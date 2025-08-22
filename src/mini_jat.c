// Prototype : fonctionnel mais minimaliste, & encore des bogues.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>

#define TEXT_SIZE       (1u << 20)
#define DATA_SIZE       (1u << 20)
#define SYM_TABLE_SIZE  (1u << 20)
#define VAR_TABLE_SIZE  16384

// Profondeur max pour piles de labels/continues/etc.
static const int kMaxCtrlDepth = 256;

// Taille max. utilisée pour le code «post» du for (tampon temporaire)
#define K_MAX_FOR_POST_BYTES 256

// IR / Flags
#define VT_CONST    0x0002
#define VT_VAR      0x0004
#define VT_LOCAL    0x0008
#define VT_LVAL     0x0010
#define VT_CMP      0x0020
#define VT_FORWARD  0x0040
#define VT_JMP      0x0080

#define VT_LVALN    (~VT_LVAL)

#define VT_BYTE     0x00001

#define VT_PTRMASK  0x00F00
#define VT_PTRINC   0x00100

#define VT_FUNC     0x01000

#define VT_TYPE     0x01F01
#define VT_TYPEN    (~VT_TYPE)
#define VT_FUNCN    (~VT_FUNC)

// Tokens | ordre == idtable_init
#define TOK_INT       256
#define TOK_VOID      257
#define TOK_CHAR      258
#define TOK_IF        259
#define TOK_ELSE      260
#define TOK_WHILE     261
#define TOK_BREAK     262
#define TOK_RETURN    263
#define TOK_DEFINE    264
#define TOK_MAIN      265
#define TOK_FOR       266
#define TOK_DO        267
#define TOK_CONTINUE  268
#define TOK_SIZEOF    269

#define TOK_EQ   0x94
#define TOK_NE   0x95
#define TOK_LT   0x9C
#define TOK_GE   0x9D
#define TOK_LE   0x9E
#define TOK_GT   0x9F
#define TOK_LAND 0xA0
#define TOK_LOR  0xA1
#define TOK_DEC  0xA2
#define TOK_MID  0xA3
#define TOK_INC  0xA4
#define TOK_SHL  0xE0
#define TOK_SHR  0xF8

static void NextToken(void);
static void ParseExpr(void);
static void Declare(int storageFlag);
static void ParseBlock(void);
static void ParseUnaryLegacy(void);
static void ParseSum(int level);
static void ParseAnd(void);
static void ParseAssignOrUnary(void);
static void GenValue(void);
static int  IsType(void);
static int  ParseType(int wantVar, int type);

static int  GetQuotedChar(int n);


static int   s_tok = 0;
static int*  s_vac = NULL;
static int*  s_vat = NULL;
static int*  s_lsym = NULL;
static int   s_rsym = 0;
static int   s_vt = 0;
static int   s_vc = 0;

static char* s_prog = NULL;
static char* s_ind = NULL;
static char* s_glo = NULL;

static int   s_loc = 0;
static FILE* s_file = NULL;

static long* s_macroStack = NULL;
static long* s_macroStackPtr = NULL;

static char* s_idTable = NULL;
static char* s_idPtr = NULL;
static char* s_idLast = NULL;

static int*  s_cchain = NULL;
static int*  s_cTarget = NULL;
static int   s_csi = -1;

static long  s_tokPos = -1;
static long  s_prevTokPos = -1;


/// Écrit un octet dans le buffer code.
static void EmitByte(char c)
{
    *s_ind++ = c;
}

/// Émet un entier en «little endian».
static void Emit(unsigned int c)
{
    while (c != 0U)
    {
        EmitByte((char)(c & 0xFFU));
        c >>= 8U;
    }
}

/// Patche une chaîne de symboles (liens d'attente) vers la position courante.
static void PatchSymChain(int t)
{
    while (t != 0)
    {
        int n = *(int*)t;
        *(int*)t = (int)(s_ind - (char*)t - 4);
        t = n;
    }
}

/// Émet un opcode suivi d'un immédiat 32 bits.
static int EmitWithImm32(unsigned int opcode, int imm32)
{
    Emit(opcode);
    *(int*)s_ind = imm32;
    imm32 = (int)(intptr_t)s_ind;
    s_ind += 4;
    return imm32;
}

#define PSYM EmitWithImm32

/// Définit le «type courant» (s_vt) et sa «valeur» (s_vc).
static void SetValue(int t, int v)
{
    s_vt = t;
    s_vc = v;
}

/// Taille du type (1 si char/byte, 4 sinon).
static int TypeSize(int t)
{
    if ((t & VT_PTRMASK) > VT_PTRINC || (t & VT_TYPE) == VT_PTRINC)
    {
        return 4;
    }
    return 1;
}

/// Si la valeur courante est une constante, push immédiat sinon génère la valeur et push EAX.
static void PushCurrentValue(void)
{
    if ((s_vt & (VT_CONST | VT_LVAL)) == VT_CONST)
    {
        PSYM(0x68U, s_vc); // push imm32
    }
    else
    {
        GenValue();
        Emit(0x50U); // push eax
    }
}


/// Recherche un symbole externe dans msvcrt.dll.
static void* FindExternalSymbol(const char* name)
{
    HMODULE hMsvcrt = GetModuleHandleA("msvcrt.dll");
    if (hMsvcrt != NULL)
    {
        FARPROC p = GetProcAddress(hMsvcrt, name);
        if (p != NULL)
        {
            return (void*)p;
        }
    }
    return NULL;
}

// Lexer
static int ReadChar(void)
{
    return fgetc(s_file);
}

static int IsIdentChar(int c)
{
    return (c >= 'a' && c <= 'z')
        || (c >= 'A' && c <= 'Z')
        || (c == '_');
}

static int IsDigit(int c)
{
    return (c >= '0' && c <= '9');
}

/// Lit le prochain token dans s_tok.
static void NextToken(void)
{
    int c, v;
    char* q;
    char* p;

again:
    while (1)
    {
        c = ReadChar();

        if (c == '\r')
        {
            v = ReadChar();
            if (v != '\n')
            {
                ungetc(v, s_file);
            }
            c = '\n';
        }

        if (c == ' ' || c == '\t' || c == '\f' || c == '\v')
        {
            continue;
        }

        if (c == '/')
        {
            v = ReadChar();
            if (v == '/')
            {
                while (c != '\n' && c != EOF)
                {
                    c = ReadChar();
                }
                continue;
            }
            if (v == '*')
            {
                int pch = 0;
                while (1)
                {
                    c = ReadChar();
                    if (c == EOF)
                    {
                        break;
                    }
                    if (pch == '*' && c == '/')
                    {
                        break;
                    }
                    pch = c;
                }
                continue;
            }
            ungetc(v, s_file);
        }

        if (c == '\n')
        {
            if (s_macroStackPtr > s_macroStack)
            {
                fseek(s_file, *--s_macroStackPtr, SEEK_SET);
            }
            continue;
        }
        break;
    }

    s_prevTokPos = s_tokPos;
    s_tokPos = ftell(s_file) - 1;

    if (c == '#')
    {
        NextToken();
        if (s_tok == TOK_DEFINE)
        {
            NextToken();
            s_vat[s_tok] = VT_FORWARD;
            s_vac[s_tok] = (int)ftell(s_file);
        }
        while (c != '\n' && c != EOF)
        {
            c = ReadChar();
        }
        goto again;
    }

    if (IsIdentChar(c))
    {
        q = s_idPtr;
        s_idLast = q;
        while (IsIdentChar(c) || IsDigit(c))
        {
            *q++ = (char)c;
            c = ReadChar();
        }
        *q++ = '\0';
        ungetc(c, s_file);

        p = s_idTable;
        s_tok = 256;
        while (p < s_idPtr)
        {
            if (strcmp(p, s_idLast) == 0)
            {
                break;
            }
            p += strlen(p) + 1;
            s_tok++;
        }
        if (p == s_idPtr)
        {
            s_idPtr = q;
        }

        if (s_vat[s_tok] == VT_FORWARD)
        {
            *s_macroStackPtr++ = ftell(s_file);
            fseek(s_file, s_vac[s_tok], SEEK_SET);
            NextToken();
        }
        return;
    }

    // Deux-char tokens : "<=" ">=" "!=" "&&" "||" "++" "--" "==" "<<" ">>"
    {
        const char* r =
            "<=\x9E>=\x9D!=\x95&&\xA0||\xA1++\xA4--\xA2==\x94<<\xE0>>\xF8";
        v = ReadChar();
        while (*r)
        {
            if (r[0] == c && r[1] == v)
            {
                s_tok = (unsigned char)r[2];
                return;
            }
            r += 3;
        }
        ungetc(v, s_file);
    }

    if (c == '<')
    {
        s_tok = TOK_LT;
    }
    else if (c == '>')
    {
        s_tok = TOK_GT;
    }
    else
    {
        s_tok = c;
    }
}

// Génération de valeur en EAX.
static void GenValue(void)
{
    if (s_vt & VT_LVAL)
    {
        // load [addr] -> EAX (byte ou dword)
        if ((s_vt & VT_TYPE) == VT_BYTE) { Emit(0xBE0FU); }
        else { Emit(0x8BU); }
        if (s_vt & VT_CONST) { PSYM(0x05U, s_vc); }
        else if (s_vt & VT_LOCAL) { PSYM(0x85U, s_vc); }
        else { EmitByte(0x00); }
    }
    else
    {
        if (s_vt & VT_CONST)
        {
            PSYM(0xB8U, s_vc); // mov eax, imm32
        }
        else if (s_vt & VT_LOCAL)
        {
            PSYM(0x858DU, s_vc); // lea eax, [ebp+disp]
        }
        else if (s_vt & VT_CMP)
        {
            PSYM(0xB8U, 0);     // mov eax, 0
            Emit(0x0FU);
            Emit((unsigned)s_vc);
            Emit(0xC0U);
        }
        else if (s_vt & VT_JMP)
        {
            int t = s_vt & 1;
            PSYM(0xB8U, t);     // mov eax, t
            PSYM(0xE9U, 5);     // jmp +5
            PatchSymChain(s_vc);
            PSYM(0xB8U, t ^ 1); // mov eax, !t
        }
    }
    s_vt = (s_vt & VT_TYPE) | VT_VAR;
}

/// Génère un test (0/≠0) et renvoie une chaîne de patchs.
static int GenTest(int invert, int chain)
{
    if (s_vt & VT_CMP)
    {
        EmitByte(0x0F);
        chain = PSYM((unsigned)((s_vc - 16) ^ invert), chain);
    }
    else if (s_vt & VT_JMP)
    {
        if ((s_vt & 1) == invert)
        {
            chain = s_vc;
        }
        else
        {
            chain = PSYM(0xE9U, chain);
            PatchSymChain(s_vc);
        }
    }
    else if ((s_vt & (VT_CONST | VT_LVAL)) == VT_CONST)
    {
        if ((s_vc != 0) != invert)
        {
            chain = PSYM(0xE9U, chain);
        }
    }
    else
    {
        GenValue();
        Emit(0xC085U); // test eax, eax
        EmitByte(0x0F);
        chain = PSYM((unsigned)(0x85 ^ invert), chain); // jnz/jz
    }
    return chain;
}

// Opérateurs

#define POST_ADD 0x1000
#define PRE_ADD  0x0000

static void IncOp(int a, int c)
{
    s_vt = s_vt & VT_LVALN;
    GenValue();
    Emit(0x018BC189U);
    Emit(0x408DU | (unsigned)a);
    EmitByte((char)((c - TOK_MID) * TypeSize(s_vt)));
    Emit(0x0189U | (unsigned)a);
}

static void GenOp(int op, int t)
{
    GenValue();
    Emit(0x59U); // pop ecx (opérande gauche)

    if (op == '+' || op == '-')
    {
        if (TypeSize(t) != 1) { Emit(0x02E0C1U); }  // shl eax, 2 si pointeurs
        if (op == '-') { Emit(0xD8F7U); }   // neg eax
        Emit(0xC801U);                             // add eax, ecx
        s_vt = t;
    }
    else if (op == '&') { Emit(0xC821U); }  // and eax, ecx
    else if (op == '^') { Emit(0xC831U); }  // xor eax, ecx
    else if (op == '|') { Emit(0xC809U); }  // or  eax, ecx
    else if (op == '*') { Emit(0xC1AF0FU); }// imul eax, ecx
    else if (op == TOK_SHL || op == TOK_SHR)
    {
        Emit(0xD391U);         // shl/shr eax, ecx
        Emit((unsigned)op);
    }
    else if (op == '/' || op == '%')
    {
        Emit(0xD231U);         // xor edx, edx
        Emit(0xF9F791U);       // idiv ecx
        if (op == '%') { Emit(0x92U); } // xchg eax, edx
    }
    else
    {
        Emit(0xC139U);         // cmp ecx, eax
        SetValue(VT_CMP, op);  // stocke l'op de comparaison
    }
}

// Types
static int IsType(void)
{
    int t;
    if (s_tok == TOK_INT || s_tok == TOK_CHAR || s_tok == TOK_VOID)
    {
        t = s_tok;
        NextToken();
        return (t != TOK_INT) | 2;
    }
    return 0;
}

static int ParseType(int wantVar, int t)
{
    int u = 0, p = 0, n = 0;
    t = t & ~2;

    while (s_tok == '*')
    {
        NextToken();
        t += VT_PTRINC;
    }

    if (s_tok == '(')
    {
        NextToken();
        u = ParseType(wantVar, 0);
        if (s_tok == ')') { NextToken(); }
    }
    else
    {
        u = 0;
        if (wantVar)
        {
            s_vc = s_tok;
            NextToken();
        }
    }

    if (s_tok == '(')
    {
        NextToken();
        p = 4;
        n = s_vc;

        while (s_tok != ')')
        {
            if ((t = IsType()) != 0)
            {
                t = ParseType(1, t);
            }
            else
            {
                s_vc = s_tok;
                t = 0;
                NextToken();
            }
            p += 4;
            s_vat[s_vc] = VT_LOCAL | VT_LVAL | t;
            s_vac[s_vc] = p;
            if (s_tok == ',') { NextToken(); }
        }

        if (s_tok == ')') { NextToken(); }
        s_vc = n;
        if (u != 0) { t = u + VT_BYTE; }
        else { t |= VT_FUNC; }
    }
    return t;
}

// Échappement
static int GetQuotedChar(int n)
{
    int c;
    if (n == '\\')
    {
        n = ReadChar();
        if (n == 'n') { n = '\n'; }
        else if (n == 't') { n = '\t'; }
        else if (n == 'r') { n = '\r'; }
        else if (IsDigit(n))
        {
            c = 0;
            while (IsDigit(n))
            {
                c = (c * 8) + (n - '0');
                n = ReadChar();
            }
            ungetc(n, s_file);
            return c;
        }
    }
    return n;
}

// AST minimaliste.
typedef enum
{
    AST_NUM,
    AST_STR,
    AST_VAR,
    AST_UN,
    AST_BIN,
    AST_CALL
} AstKind;

typedef struct AstNode AstNode;

struct AstNode
{
    AstKind  Kind;
    int      Op;            // Pour UN/BIN
    int      IntValue;      // NUM
    int      Sym;           // VAR : token identifiant
    int      Addr;          // STR : adresse dans la zone globale
    AstNode* A;             // UN (A), BIN (A,B)
    AstNode* B;
    AstNode** Args;         // CALL : tableau d’arguments
    int      ArgCount;
    int      CalleeIsConst;
    int      CalleeAddr;    // si const (ex: printf)
    AstNode* Callee;        // sinon, expr qui évalue l’adresse
};

static AstNode* AstNew(AstKind k)
{
    AstNode* n = (AstNode*)calloc(1, sizeof(AstNode));
    n->Kind = k;
    return n;
}

static AstNode* AstParseExpr(void); // fwd

static AstNode* AstParsePrimary(void)
{
    if (IsDigit(s_tok))
    {
        int n = 0;
        while (IsDigit(s_tok))
        {
            n = (n * 10) + s_tok - '0';
            NextToken();
        }
        AstNode* x = AstNew(AST_NUM);
        x->IntValue = n;
        return x;
    }
    else if (s_tok == '\'')
    {
        int ch = GetQuotedChar(ReadChar());
        NextToken();
        if (s_tok == '\'') { NextToken(); }
        AstNode* x = AstNew(AST_NUM);
        x->IntValue = ch;
        return x;
    }
    else if (s_tok == '\"')
    {
        int c;
        int base = (int)(intptr_t)s_glo;
        while ((c = ReadChar()) != '\"')
        {
            *s_glo++ = (char)GetQuotedChar(c);
        }
        *s_glo++ = 0;
        s_glo = (char*)(((intptr_t)s_glo + 3) & ~3);
        NextToken();
        AstNode* x = AstNew(AST_STR);
        x->Addr = base;
        return x;
    }
    else if (s_tok == '(')
    {
        NextToken();
        AstNode* x = AstParseExpr();
        if (s_tok == ')') { NextToken(); }
        return x;
    }
    else if (s_tok >= 256)
    {
        // ident -> var ou appel en chaîne
        int sym = s_tok;
        NextToken();
        AstNode* base = AstNew(AST_VAR);
        base->Sym = sym;

        while (s_tok == '(')
        {
            NextToken();
            AstNode** vec = NULL;
            int cap = 0, n = 0;

            if (s_tok != ')')
            {
                for (;;)
                {
                    if (n == cap)
                    {
                        cap = cap ? cap * 2 : 4;
                        vec = (AstNode**)realloc(vec, (size_t)cap * sizeof(AstNode*));
                    }
                    vec[n++] = AstParseExpr();
                    if (s_tok == ',')
                    {
                        NextToken();
                        continue;
                    }
                    break;
                }
            }
            if (s_tok == ')') { NextToken(); }

            AstNode* call = AstNew(AST_CALL);
            call->CalleeIsConst = 1;
            call->CalleeAddr = s_vac[base->Sym];
            call->Callee = NULL;
            call->Args = vec;
            call->ArgCount = n;

            base = call;
        }
        return base;
    }

    AstNode* z = AstNew(AST_NUM);
    z->IntValue = 0;
    return z;
}

static AstNode* AstParseUnary(void)
{
    if (s_tok == '+' || s_tok == '-')
    {
        int op = s_tok;
        NextToken();
        AstNode* x = AstNew(AST_UN);
        x->Op = op;
        x->A = AstParseUnary();
        return x;
    }
    return AstParsePrimary();
}

static AstNode* AstParseMul(void)
{
    AstNode* x = AstParseUnary();
    while (s_tok == '*' || s_tok == '/' || s_tok == '%')
    {
        int op = s_tok;
        NextToken();
        AstNode* y = AstParseUnary();
        AstNode* b = AstNew(AST_BIN);
        b->Op = op;
        b->A = x;
        b->B = y;
        x = b;
    }
    return x;
}

static AstNode* AstParseAdd(void)
{
    AstNode* x = AstParseMul();
    while (s_tok == '+' || s_tok == '-')
    {
        int op = s_tok;
        NextToken();
        AstNode* y = AstParseMul();
        AstNode* b = AstNew(AST_BIN);
        b->Op = op;
        b->A = x;
        b->B = y;
        x = b;
    }
    return x;
}

static AstNode* AstParseExpr(void)
{
    // Suffisant pour les arguments (addition/multiplication/unaires)
    return AstParseAdd();
}

/// Génère du code (résultat en EAX) depuis un AST
static void GenFromAst(AstNode* n)
{
    switch (n->Kind)
    {
    case AST_NUM:
        PSYM(0xB8U, n->IntValue);  // mov eax, imm32
        s_vt = VT_VAR;
        return;

    case AST_STR:
        PSYM(0xB8U, n->Addr);      // mov eax, addr
        s_vt = VT_VAR | VT_PTRINC | VT_BYTE;
        return;

    case AST_VAR:
        SetValue(s_vat[n->Sym], s_vac[n->Sym]);
        GenValue();
        return;

    case AST_UN:
        GenFromAst(n->A);
        if (n->Op == '-')
        {
            Emit(0xD8F7U); // neg eax
        }
        s_vt = VT_VAR;
        return;

    case AST_BIN:
        GenFromAst(n->A);
        Emit(0x50U);      // push eax (gauche)
        GenFromAst(n->B); // eax = droit
        GenOp(n->Op, 2);
        return;

    case AST_CALL:
    {
        int bytes = 0;

        // Args R->L
        for (int i = n->ArgCount - 1; i >= 0; --i)
        {
            GenFromAst(n->Args[i]);
            Emit(0x50U);
            bytes += 4;
        }

        if (n->CalleeIsConst)
        {
            PSYM(0xB8U, n->CalleeAddr); // mov eax, imm32
            Emit(0xD0FFU);              // call eax
        }
        else
        {
            // Pas utilisé ici pr sécurité
            GenFromAst(n->Callee);
            Emit(0x50U);
            PSYM(0x2494FFU, bytes);
            bytes += 4;
        }

        if (bytes)
        {
            PSYM(0xC481U, bytes); // add esp, bytes
        }
        s_vt = VT_VAR;
        return;
    }
    }
}

// Parse toutes les expressions d’arguments en AST, renvoie le tableau & argc
static int AstParseArgList(AstNode*** out)
{
    AstNode** vec = NULL;
    int cap = 0;
    int n = 0;

    if (s_tok != ')')
    {
        for (;;)
        {
            if (n == cap)
            {
                cap = cap ? cap * 2 : 4;
                vec = (AstNode**)realloc(vec, (size_t)cap * sizeof(AstNode*));
            }
            vec[n++] = AstParseExpr();
            if (s_tok == ',')
            {
                NextToken();
                continue;
            }
            break;
        }
    }
    if (s_tok == ')') { NextToken(); }
    *out = vec;
    return n;
}

// Parser
static void ParseUnaryLegacy(void)
{
    int n, t, ft, fc;

    if (IsDigit(s_tok))
    {
        n = 0;
        while (IsDigit(s_tok))
        {
            n = (n * 10) + s_tok - '0';
            NextToken();
        }
        SetValue(VT_CONST, n);
    }
    else if (s_tok == '\'')
    {
        SetValue(VT_CONST, GetQuotedChar(ReadChar()));
        NextToken();
        if (s_tok == '\'') { NextToken(); }
    }
    else if (s_tok == '\"')
    {
        SetValue(VT_CONST | VT_PTRINC | VT_BYTE, (int)(intptr_t)s_glo);
        while ((n = ReadChar()) != '\"')
        {
            *s_glo++ = (char)GetQuotedChar(n);
        }
        *s_glo++ = 0;
        s_glo = (char*)(((intptr_t)s_glo + 3) & ~3);
        NextToken();
    }
    else if (s_tok == TOK_SIZEOF)
    {
        NextToken();
        if (s_tok == '(')
        {
            NextToken();
            if ((t = IsType()) != 0)
            {
                t = ParseType(0, t);
                if (s_tok == ')') { NextToken(); }
                SetValue(VT_CONST, TypeSize(t));
            }
            else
            {
                ParseExpr();
                if (s_tok == ')') { NextToken(); }
                SetValue(VT_CONST, 4);
            }
        }
        else
        {
            SetValue(VT_CONST, 4);
        }
    }
    else
    {
        t = s_tok;
        NextToken();

        if (t == '(')
        {
            if ((t = IsType()) != 0)
            {
                ft = ParseType(0, t);
                if (s_tok == ')') { NextToken(); }
                ParseUnaryLegacy();
                s_vt = (s_vt & VT_TYPEN) | ft;
            }
            else
            {
                ParseExpr();
                if (s_tok == ')') { NextToken(); }
            }
        }
        else if (t == '*')
        {
            ParseUnaryLegacy();
            if (s_vt & VT_LVAL) { GenValue(); }
            s_vt = (s_vt - VT_PTRINC) | VT_LVAL;
        }
        else if (t == '&')
        {
            ParseUnaryLegacy();
            s_vt &= VT_LVALN;
            s_vt += VT_PTRINC;
        }
        else if (t == '!')
        {
            ParseUnaryLegacy();
            if (s_vt & VT_CMP) { s_vc ^= 1; }
            else { SetValue(VT_JMP, GenTest(1, 0)); }
        }
        else if (t == '~')
        {
            ParseUnaryLegacy();
            if ((s_vt & (VT_CONST | VT_LVAL)) == VT_CONST)
            {
                s_vc = ~s_vc;
            }
            else
            {
                GenValue();
                Emit(0xD0F7U); // not eax
            }
        }
        else if (t == TOK_INC || t == TOK_DEC)
        {
            ParseUnaryLegacy();
            IncOp(PRE_ADD, t);
        }
        else if (t == '-')
        {
            ParseUnaryLegacy();
            if ((s_vt & (VT_CONST | VT_LVAL)) == VT_CONST)
            {
                s_vc = -s_vc;
            }
            else
            {
                GenValue();
                Emit(0xD8F7U); // neg eax
            }
        }
        else if (t == '+')
        {
            ParseUnaryLegacy();
        }
        else
        {
            // identifiant
            SetValue(s_vat[t], s_vac[t]);
            if (s_vt == 0)
            {
                void* addr = NULL;
                if (s_idLast != NULL)
                {
                    if (strcmp(s_idLast, "printf") == 0)
                    {
                        addr = (void*)printf;
                    }
                    else
                    {
                        addr = FindExternalSymbol(s_idLast);
                    }
                }
                n = (int)(intptr_t)addr;
                if (n == 0)
                {
                    SetValue(VT_CONST | VT_LVAL | VT_FUNC, s_vac[t]); // stub si posé au prepass
                }
                else
                {
                    SetValue(VT_CONST | VT_LVAL | VT_FUNC, n);
                }
            }
        }
    }

    if (s_tok == TOK_INC || s_tok == TOK_DEC)
    {
        IncOp(POST_ADD, s_tok);
        NextToken();
    }
    else if (s_tok == '[')
    {
        GenValue();
        ft = s_vt;
        fc = s_vc;
        NextToken();
        Emit(0x50U); // push eax
        ParseExpr();
        GenOp('+', ft);
        s_vt = (ft - VT_PTRINC) | VT_LVAL;
        s_vc = fc;
        if (s_tok == ']') { NextToken(); }
    }
    else if (s_tok == '(')
    {
        s_vt &= VT_LVALN;

        int argsBytes = 0;
        int pushedFunc = 0;

        // Si callee non-const, calculer adresse en EAX et la pousser
        if ((s_vt & VT_CONST) == 0)
        {
            GenValue();
            Emit(0x50U);
            pushedFunc = 4;
        }
        ft = s_vt;
        fc = s_vc;

        NextToken(); // '('

        AstNode** av = NULL;
        int ac = AstParseArgList(&av);
        for (int i = ac - 1; i >= 0; --i)
        {
            GenFromAst(av[i]);
            Emit(0x50U);
            argsBytes += 4;
        }

        if (ft & VT_CONST)
        {
            PSYM(0xB8U, fc);  // mov eax, imm32
            Emit(0xD0FFU);    // call eax
        }
        else
        {
            PSYM(0x2494FFU, argsBytes); // call [esp+argsBytes]
            argsBytes += pushedFunc;
        }

        if (argsBytes)
        {
            PSYM(0xC481U, argsBytes); // add esp, n
        }
        s_vt = VT_VAR;
    }
}

static void ParseAssignOrUnary(void)
{
    int ft, fc, isByte;

    ParseUnaryLegacy();
    if (s_tok == '=')
    {
        NextToken();
        fc = s_vc;
        ft = s_vt;
        isByte = ((s_vt & VT_TYPE) == VT_BYTE);

        if (ft & VT_VAR) { Emit(0x50U); } // push eax (adresse)
        ParseExpr();
        GenValue();

        if (ft & VT_VAR)
        {
            Emit(0x59U); // pop ecx
            Emit(isByte ? 0x0188U : 0x0189U); // mov [ecx], al/eax
        }
        else
        {
            if (ft & VT_LOCAL)
            {
                PSYM(isByte ? 0x8588U : 0x8589U, fc); // mov [ebp+disp], al/eax
            }
            else
            {
                PSYM(isByte ? 0xA2U : 0xA3U, fc);     // mov [imm32], al/eax
            }
        }
    }
}

static void ParseSum(int level)
{
    int op, t;

    if (level == 0)
    {
        ParseAssignOrUnary();
    }
    else
    {
        level--;
        ParseSum(level);
        while (1)
        {
            op = s_tok;
            if ((level == 0 && op != '*' && op != '/' && op != '%') ||
                (level == 1 && op != '+' && op != '-') ||
                (level == 2 && op != TOK_SHL && op != TOK_SHR) ||
                (level == 3 && (op < TOK_LT || op > TOK_GT)) ||
                (level == 4 && op != TOK_EQ && op != TOK_NE) ||
                (level == 5 && op != '&') ||
                (level == 6 && op != '^') ||
                (level == 7 && op != '|'))
            {
                break;
            }

            GenValue();
            t = s_vt;
            Emit(0x50U); // push eax
            NextToken();
            ParseSum(level);
            GenOp(op, t);
        }
    }
}

static void ParseAnd(void)
{
    int chain = 0;
    ParseSum(8);
    while (1)
    {
        if (s_tok != TOK_LAND)
        {
            if (chain)
            {
                chain = GenTest(1, chain);
                SetValue(VT_JMP | 1, chain);
            }
            break;
        }
        chain = GenTest(1, chain);
        NextToken();
        ParseSum(8);
    }
}

static void ParseExpr(void)
{
    int chain = 0;
    ParseAnd();
    while (1)
    {
        if (s_tok != TOK_LOR)
        {
            if (chain)
            {
                chain = GenTest(0, chain);
                SetValue(VT_JMP, chain);
            }
            break;
        }
        chain = GenTest(0, chain);
        NextToken();
        ParseAnd();
    }
}

static void ParseBlock(void)
{
    int a, c, d, condJmp;

    if (s_tok == TOK_IF)
    {
        NextToken();
        if (s_tok == '(') { NextToken(); }
        ParseExpr();
        if (s_tok == ')') { NextToken(); }

        a = GenTest(1, 0);
        ParseBlock();
        c = s_tok;

        if (c == TOK_ELSE)
        {
            NextToken();
            {
                int d2 = PSYM(0xE9U, 0);
                PatchSymChain(a);
                (void)d2;
            }
            ParseBlock();
            PatchSymChain(0);
        }
        else
        {
            PatchSymChain(a);
        }
    }
    else if (s_tok == TOK_WHILE)
    {
        NextToken();
        d = (int)(intptr_t)s_ind;
        if (s_tok == '(') { NextToken(); }
        ParseExpr();
        if (s_tok == ')') { NextToken(); }
        *++s_lsym = GenTest(1, 0);
        s_csi++;
        s_cchain[s_csi] = 0;
        s_cTarget[s_csi] = d;

        ParseBlock();
        PSYM(0xE9U, d - (int)(intptr_t)s_ind - 5);
        PatchSymChain(*s_lsym--);
        s_csi--;
    }
    else if (s_tok == TOK_DO)
    {
        NextToken();
        d = (int)(intptr_t)s_ind;
        *++s_lsym = 0;
        s_csi++;
        s_cchain[s_csi] = 0;
        s_cTarget[s_csi] = 0;

        ParseBlock();
        PatchSymChain(s_cchain[s_csi]);

        if (s_tok == TOK_WHILE) { NextToken(); }
        if (s_tok == '(') { NextToken(); }
        ParseExpr();
        if (s_tok == ')') { NextToken(); }

        PSYM(0xE9U, d - (int)(intptr_t)s_ind - 5);
        PatchSymChain(*s_lsym--);
        if (s_tok == ';') { NextToken(); }
        s_csi--;
    }
    else if (s_tok == TOK_FOR)
    {
        NextToken();
        if (s_tok == '(') { NextToken(); }

        if (s_tok == TOK_INT || s_tok == TOK_CHAR || s_tok == TOK_VOID)
        {
            Declare(VT_LOCAL);
        }
        else
        {
            if (s_tok != ';') { ParseExpr(); GenValue(); }
            if (s_tok == ';') { NextToken(); }
        }

        int testLabel = (int)(intptr_t)s_ind;
        condJmp = 0;
        if (s_tok != ';')
        {
            ParseExpr();
            condJmp = GenTest(1, 0);
        }
        if (s_tok == ';') { NextToken(); }

        // Sauvegarde du «post» du for
        char postCode[K_MAX_FOR_POST_BYTES];
        char* saved = s_ind;
        s_ind = postCode;
        if (s_tok != ')')
        {
            ParseExpr();
            GenValue();
        }
        int postLen = (int)(s_ind - postCode);
        s_ind = saved;
        if (s_tok == ')') { NextToken(); }

        *++s_lsym = 0;
        s_csi++;
        s_cchain[s_csi] = 0;
        s_cTarget[s_csi] = 0;

        ParseBlock();
        PatchSymChain(s_cchain[s_csi]);

        if (postLen > 0)
        {
            size_t avail = TEXT_SIZE - (size_t)(s_ind - s_prog);
            (void)memcpy_s(s_ind, avail, postCode, (size_t)postLen);
            s_ind += postLen;
        }

        PSYM(0xE9U, testLabel - (int)(intptr_t)s_ind - 5);
        if (condJmp) { PatchSymChain(condJmp); }
        PatchSymChain(*s_lsym--);
        s_csi--;
    }
    else if (s_tok == '{')
    {
        NextToken();
        while (s_tok != '}')
        {
            if (s_tok == TOK_INT || s_tok == TOK_CHAR || s_tok == TOK_VOID)
            {
                Declare(VT_LOCAL);
            }
            else
            {
                ParseBlock();
            }
        }
        NextToken();
    }
    else if (s_tok == TOK_RETURN)
    {
        NextToken();
        if (s_tok != ';')
        {
            ParseExpr();
            GenValue();
        }
        if (s_tok == ';') { NextToken(); }
        s_rsym = PSYM(0xE9U, s_rsym);
    }
    else if (s_tok == TOK_BREAK)
    {
        *s_lsym = PSYM(0xE9U, *s_lsym);
        NextToken();
        if (s_tok == ';') { NextToken(); }
    }
    else if (s_tok == TOK_CONTINUE)
    {
        if (s_csi >= 0 && s_cTarget[s_csi] != 0)
        {
            PSYM(0xE9U, s_cTarget[s_csi] - (int)(intptr_t)s_ind - 5);
        }
        else if (s_csi >= 0)
        {
            s_cchain[s_csi] = PSYM(0xE9U, s_cchain[s_csi]);
        }
        NextToken();
        if (s_tok == ';') { NextToken(); }
    }
    else if (s_tok == TOK_INT || s_tok == TOK_CHAR || s_tok == TOK_VOID)
    {
        Declare(VT_LOCAL);
    }
    else
    {
        if (s_tok != ';')
        {
            ParseExpr();
        }
        if (s_tok == ';') { NextToken(); }
    }
}

// JIT paresseux : index, stubs, compilation à la volée.
enum
{
    F_NONE = 0,
    F_DECLARED = 1,
    F_COMPILED = 2,
    F_EXTERNAL = 3
};

static int* s_fstate = NULL;
static long* s_fpos = NULL;
static char** s_fstub = NULL;

static void* CompileFunctionAt(int sym);
static void* JitCompileHelper(int sym, void* stubAddr);

/// Stub paresseux :
///   push stub_addr
///   push sym
///   mov  eax, helper
///   call eax
///   add  esp, 8
///   jmp  eax      ; eax = entrée de la fonction compilée
static char* EmitLazyStub(int sym)
{
    char* s = s_ind;
    int patchStubPtr = PSYM(0x68U, 0); // push imm32 (stub addr, patché ensuite)
    PSYM(0x68U, sym);                  // push imm32 (sym)
    PSYM(0xB8U, (int)(intptr_t)&JitCompileHelper); // mov eax, imm32 (helper)
    Emit(0xD0FFU);                     // call eax
    PSYM(0xC481U, 8);                  // add esp, 8
    Emit(0xE0FFU);                     // jmp eax
    *(int*)patchStubPtr = (int)(intptr_t)s; // renseigne stub_addr dans le 1er push
    return s;
}

/// Saut d’un bloc { ... } sans le parser.
static void SkipBracedBlockRaw(void)
{
    int depth = 1, c, v;

    while (depth > 0)
    {
        c = ReadChar();
        if (c == EOF) { break; }

        if (c == '\'')
        {
            int p = 0;
            while ((v = ReadChar()) != EOF)
            {
                if (v == '\'' && p != '\\') { break; }
                p = v;
            }
            continue;
        }

        if (c == '\"')
        {
            int p = 0;
            while ((v = ReadChar()) != EOF)
            {
                if (v == '\"' && p != '\\') { break; }
                p = v;
            }
            continue;
        }

        if (c == '/')
        {
            v = ReadChar();
            if (v == '/')
            {
                while (c != '\n' && c != EOF) { c = ReadChar(); }
            }
            else if (v == '*')
            {
                int p = 0;
                while ((v = ReadChar()) != EOF)
                {
                    if (p == '*' && v == '/') { break; }
                    p = v;
                }
            }
            else
            {
                ungetc(v, s_file);
            }
            continue;
        }

        if (c == '{') { depth++; }
        else if (c == '}') { depth--; }
    }
}

/// Prépass d’indexatio, repère les définitions de fonctions et pose des stubs.
static void PrepassIndex(void)
{
    fseek(s_file, 0, SEEK_SET);
    s_macroStackPtr = s_macroStack;
    NextToken();

    while (s_tok != EOF)
    {
        int b = IsType();
        if (!b)
        {
            if (s_tok == '{')
            {
                SkipBracedBlockRaw();
                NextToken();
            }
            else
            {
                NextToken();
            }
            continue;
        }

        long typePos = s_prevTokPos;
        int t = ParseType(1, b);

        if (s_tok == '{')
        {
            int sym = s_vc;
            if (s_fstate[sym] == F_NONE)
            {
                s_fpos[sym] = typePos;
                s_fstub[sym] = EmitLazyStub(sym);
                s_vac[sym] = (int)(intptr_t)s_fstub[sym];
                s_vat[sym] = VT_CONST | VT_LVAL | t;
                s_fstate[sym] = F_DECLARED;
            }
            SkipBracedBlockRaw();
            NextToken();
        }
        else
        {
            while (s_tok != ';' && s_tok != EOF) { NextToken(); }
            if (s_tok == ';') { NextToken(); }
        }
    }
}

/// Compile une fonction à l’offset pré-indexé, renvoie son entrée.
static void* CompileFunctionAt(int sym)
{
    if (s_fstate[sym] == F_COMPILED)
    {
        return (void*)(intptr_t)s_vac[sym];
    }

    fseek(s_file, s_fpos[sym], SEEK_SET);
    s_macroStackPtr = s_macroStack;
    NextToken();

    int b = IsType();
    if (!b) { return NULL; }

    int ftype = ParseType(1, b);
    if (s_tok != '{') { return NULL; }

    if (s_vat[s_vc] == 0)
    {
        PatchSymChain(s_vac[s_vc]);
    }
    s_vat[s_vc] = VT_CONST | VT_LVAL | ftype;
    s_vac[s_vc] = (int)(intptr_t)s_ind;

    s_loc = 0;
    Emit(0xE58955U);               // push ebp ; mov ebp, esp
    int* a = (int*)PSYM(0xEC81U, 0); // sub esp, <loc> (patché)
    s_rsym = 0;

    ParseBlock();
    PatchSymChain(s_rsym);
    Emit(0xC3C9U);                 // leave ; ret
    *a = s_loc;

    s_fstate[s_vc] = F_COMPILED;
    return (void*)(intptr_t)s_vac[s_vc];
}

/// Helper appelé par le stub paresseux.
static void* JitCompileHelper(int sym, void* stubAddr)
{
    if (s_fstate[sym] == F_COMPILED)
    {
        void* entry = (void*)(intptr_t)s_vac[sym];
        unsigned char* s = (unsigned char*)stubAddr;
        s[0] = 0xB8; *(int*)(s + 1) = (int)(intptr_t)entry; *(unsigned short*)(s + 5) = 0xE0FF;
        return entry;
    }

    void* entry = CompileFunctionAt(sym);
    if (!entry)
    {
        if (s_vat[sym] & VT_FUNC)
        {
            entry = (void*)(intptr_t)s_vac[sym];
        }
    }

    unsigned char* s = (unsigned char*)stubAddr;
    s[0] = 0xB8; *(int*)(s + 1) = (int)(intptr_t)entry; *(unsigned short*)(s + 5) = 0xE0FF;
    return entry;
}

static void Declare(int storageFlag)
{
    int t, b;

    while ((b = IsType()) != 0)
    {
        while (1)
        {
            s_vt = ParseType(1, b);
            if (s_tok == '{')
            {
                SkipBracedBlockRaw();
                NextToken();
                break;
            }
            else
            {
                int sym = s_vc;
                int tdecl = s_vt;

                s_vat[sym] = storageFlag | VT_LVAL | tdecl;

                if (storageFlag == VT_LOCAL)
                {
                    s_loc += 4;
                    s_vac[sym] = -s_loc;
                }
                else
                {
                    s_vac[sym] = (int)(intptr_t)s_glo;
                    *(int*)s_glo = 0;
                    s_glo += 4;
                }

                if (s_tok == '=')
                {
                    NextToken();
                    ParseExpr();
                    GenValue();

                    int isByte = ((tdecl & VT_TYPE) == VT_BYTE);
                    if (storageFlag == VT_LOCAL)
                    {
                        PSYM(isByte ? 0x8588U : 0x8589U, s_vac[sym]);
                    }
                    else
                    {
                        PSYM(isByte ? 0xA2U : 0xA3U, s_vac[sym]);
                    }
                }

                if (s_tok != ',')
                {
                    if (s_tok == ';') { NextToken(); }
                    break;
                }
                NextToken();
            }
        }
    }
}

// Utilitaires de symboles/identifiants
static int TokenLookup(const char* name)
{
    const char* p = s_idTable;
    int t = 256;
    while (p < s_idPtr)
    {
        if (strcmp(p, name) == 0)
        {
            return t;
        }
        p += strlen(p) + 1;
        t++;
    }
    return -1;
}

int main(int argc, char** argv)
{
    int (*entry)(int, char**);

    if (argc < 2)
    {
        printf("usage: jat <source.c>\n");
        return 1;
    }

    const char* source = argv[1];

    errno_t ferr = fopen_s(&s_file, source, "r");
    if (ferr != 0 || !s_file)
    {
        printf("Could not open file: %s\n", source);
        return 1;
    }

    s_glo = (char*)VirtualAlloc(NULL, DATA_SIZE, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    s_prog = (char*)VirtualAlloc(NULL, TEXT_SIZE, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);

    if (!s_glo || !s_prog)
    {
        printf("alloc fail\n");
        if (s_glo) { VirtualFree(s_glo, 0, MEM_RELEASE); }
        if (s_prog) { VirtualFree(s_prog, 0, MEM_RELEASE); }
        fclose(s_file);
        return 1;
    }

    s_vac = (int*)calloc(VAR_TABLE_SIZE, sizeof(int));
    s_vat = (int*)calloc(VAR_TABLE_SIZE, sizeof(int));
    s_lsym = (int*)calloc((size_t)kMaxCtrlDepth, sizeof(int));
    s_cchain = (int*)calloc((size_t)kMaxCtrlDepth, sizeof(int));
    s_cTarget = (int*)calloc((size_t)kMaxCtrlDepth, sizeof(int));
    s_fstate = (int*)calloc(VAR_TABLE_SIZE, sizeof(int));
    s_fpos = (long*)calloc(VAR_TABLE_SIZE, sizeof(long));
    s_fstub = (char**)calloc(VAR_TABLE_SIZE, sizeof(char*));

    s_macroStack = (long*)malloc((size_t)kMaxCtrlDepth * sizeof(long));
    s_macroStackPtr = s_macroStack;

    if (!s_vac || !s_vat || !s_lsym || !s_cchain || !s_cTarget || !s_fstate || !s_fpos || !s_fstub || !s_macroStack)
    {
        printf("alloc fail\n");
        fclose(s_file);
        return 1;
    }

    static const char kIdTableInit[] =
        "int\0void\0char\0if\0else\0while\0break\0return\0define\0main\0for\0do\0continue\0sizeof\0printf";
    s_idTable = (char*)malloc(SYM_TABLE_SIZE);
    if (!s_idTable)
    {
        printf("alloc fail\n");
        fclose(s_file);
        return 1;
    }

    (void)memcpy_s(s_idTable, SYM_TABLE_SIZE, kIdTableInit, sizeof(kIdTableInit));
    s_idPtr = s_idTable + sizeof(kIdTableInit);

    s_ind = s_prog;

    int tokPrintf = TokenLookup("printf");
    void* printfAddr = (void*)printf;

    if (!printfAddr || tokPrintf < 0)
    {
        printf("printf not resolved\n");
        fclose(s_file);
        return 1;
    }

    s_vat[tokPrintf] = VT_CONST | VT_LVAL | VT_FUNC;
    s_vac[tokPrintf] = (int)(intptr_t)printfAddr;
    s_fstate[tokPrintf] = F_EXTERNAL;

    PrepassIndex();

    fseek(s_file, 0, SEEK_SET);
    s_macroStackPtr = s_macroStack;
    NextToken();
    Declare(VT_CONST);

    int tokMain = TokenLookup("main");
    if (tokMain < 0 || s_vac[tokMain] == 0)
    {
        printf("main non trouve\n");
        fclose(s_file);
        return 1;
    }

    entry = (int (*)(int, char**))(void*)(intptr_t)s_vac[tokMain];
    int ret = (*entry)(argc - 1, argv + 1);

    fclose(s_file);
    return ret;
}
