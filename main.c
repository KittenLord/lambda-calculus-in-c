// =================================================
// Scroll to the very bottom to see the demo :)
// =================================================

// If you want to see the memory usage of this demo (numbers represent
// the amount of malloc/free calls), uncomment the following line:
// #define MEM_STATS

// Main source:
// https://personal.utdallas.edu/~gupta/courses/apl/lambda.pdf
//
// Factorial definition (though it's not hard to derive yourself),
// Z combinator definition:
// https://en.wikipedia.org/wiki/Fixed-point_combinator

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

#ifdef MEM_STATS
int64_t finalCount;
int64_t peakCount;
int64_t mallocCount;
int64_t freeCount;

void *Malloc(size_t size) {
    mallocCount++;
    finalCount++;
    if(finalCount > peakCount) peakCount = finalCount;

    // return calloc(1, size);
    return malloc(size);
}

void *Realloc(void *ptr, size_t size) {
    return realloc(ptr, size);
}

void Free(void *ptr) {
    if(ptr == 0) return;

    freeCount++;
    finalCount--;

    free(ptr);
}
#else
#define Malloc(s) malloc(s)
#define Free(p) free(p)
#define Realloc(p, s) realloc(p, s)
#endif

// ==================
// TYPES
// ==================

typedef uint8_t byte;

// EXPR_BIND is implied to be everything not within [0; 3]
typedef uint64_t bindt;
typedef bindt exprType;
#define EXPR_FUN 0
#define EXPR_APP 1
#define EXPR_IMPURE_VAL 2
#define EXPR_IMPURE_FUN 3
bindt lastBind = 4;
#define var(b) if(lastBind < 4) { lastBind = 4; } bindt b = lastBind++;

typedef struct {
    byte *data;
    size_t len;
    bool aux;
} expr;

typedef expr (*impureFunpt)(byte *data, size_t len);

// ==================
// UTILITY
// ==================

void maybeFree(expr e) {
    if(e.aux) Free(e.data);
}

#define isBind(t) ((t) >= 4)

char *boolToStr(bool b) {
    if(b) return "true";
    else  return "false";
}

typedef struct {
    size_t *offsets;
    size_t len;
    size_t cap;
} replaceList;

void rladd(replaceList *list, size_t offset) {
    if(list->len < list->cap) {
        list->offsets[list->len] = offset;
        (list->len)++;
        return;
    }

    size_t *noffsets = Malloc((list->cap * 2 + 1) * sizeof(size_t));
    memcpy(noffsets, list->offsets, list->len * sizeof(size_t));
    Free(list->offsets);
    list->offsets = noffsets;
    list->cap = list->cap * 2 + 1;

    rladd(list, offset);
}

// replaceList rlcopy(replaceList list) {
//     size_t *offsets = Malloc(list.len);
//     memcpy(offsets, list.offsets, list.len);
//     return (replaceList){ .offsets = offsets, .len = list.len, .cap = list.cap };
// }

void rlfree(replaceList list) {
    Free(list.offsets);
}

#define rlinit (128)
#define mkrl() ((replaceList){ .offsets = Malloc(rlinit * sizeof(size_t)), .len = 0, .cap = rlinit })

// ==================
// EVALUATION
// ==================

size_t getExprLen(byte *data) {
    size_t acc = 0;
    ssize_t depth = 1;

    while(depth > 0) {
        exprType type = *(exprType *)data;

        if(false) {}
        else if(isBind(type)) {
            acc += sizeof(bindt);
            data += sizeof(bindt);

            depth--;
            continue;
        }
        else if(type == EXPR_FUN) {
            size_t fun = sizeof(exprType) + sizeof(bindt);
            data += fun;
            acc += fun;

            depth += 1;
            depth--;
            continue;
        }
        else if(type == EXPR_APP) {
            size_t app = sizeof(exprType);
            data += app;
            acc += app;

            depth += 2;
            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_VAL) {
            size_t ival = sizeof(exprType);
            data += ival;
            size_t vlen = *(size_t *)data;
            data += sizeof(size_t) + vlen;
            acc += ival + sizeof(size_t) + vlen;

            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_FUN) {
            data += sizeof(exprType) + sizeof(impureFunpt);
            acc += sizeof(exprType) + sizeof(impureFunpt);

            depth--;
            continue;
        }
        else {
            printf("This should never happen (all types should be covered by the ifs)\n");
            exit(1);
        }
    }

    return acc;
}

void searchBinds(bindt bind, byte *odata, byte **data, replaceList *list) {
    ssize_t depth = 1;

    while(depth > 0) {
        exprType type = *(exprType *)*data;

        if(false) {}
        else if(isBind(type)) {
            bindt mbind = *(bindt *)*data;

            if(mbind == bind) {
                rladd(list, *data - odata);
            }

            *data += sizeof(bindt);

            depth--;
            continue;
        }
        else if(type == EXPR_FUN) {
            *data += sizeof(exprType);
            *data += sizeof(bindt);

            depth += 1;
            depth--;
            continue;
        }
        else if(type == EXPR_APP) {
            *data += sizeof(exprType);

            depth += 2;
            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_VAL) {
            *data += sizeof(exprType);
            size_t vlen = *(size_t *)*data;
            *data += sizeof(size_t);
            *data += vlen;

            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_FUN) {
            *data += sizeof(exprType);
            *data += sizeof(impureFunpt);

            depth--;
            continue;
        }
    }
}

bool scanForSubst(byte *odata, byte **data, replaceList *list, size_t *rpos, size_t *rlen, size_t *fpos, size_t *flen, impureFunpt *imfun) {
    ssize_t depth = 1;
    bool result = false;

    while(depth > 0) {
        if(result) return result;

        exprType type = *(exprType *)*data;

        if(false) {}
        else if(isBind(type)) {
            *data += sizeof(exprType);

            result = false;
            depth--;
            continue;
        }
        else if(type == EXPR_FUN) {
            *data += sizeof(exprType);
            *data += sizeof(bindt);

            depth += 1;
            depth--;
            continue;
        }
        else if(type == EXPR_APP) {
            *fpos = *data - odata;
            *data += sizeof(exprType);
            exprType lhsType = *(exprType *)*data;
            if(lhsType == EXPR_FUN) {

                size_t funLen = getExprLen(*data);
                size_t argLen = getExprLen(*data + funLen);
                *data += sizeof(exprType);

                *flen = sizeof(exprType) + sizeof(exprType) + sizeof(bindt);

                bindt bind = *(bindt *)*data;
                *data += sizeof(bindt);

                byte *sdata = *data;
                searchBinds(bind, odata, &sdata, list);

                *rpos = *fpos + sizeof(exprType) + funLen;
                *rlen = argLen;

                result = true;
                continue;
            }
            else if(lhsType == EXPR_IMPURE_FUN) {
                *data += sizeof(exprType);
                *imfun = *(impureFunpt *)*data;
                rladd(list, *data - odata); // NOTE: assumes sizeof(bindt) == sizeof(pointer)
                *data += sizeof(impureFunpt);
                *flen = sizeof(exprType) + sizeof(exprType); // + sizeof(impureFunpt);

                *rpos = *data - odata;
                *rlen = getExprLen(*data);

                exprType argType = *(exprType *)*data;
                if(argType != EXPR_IMPURE_VAL) {
                    *imfun = NULL;
                    list->len = 0;

                    depth += 1;
                    depth--;
                    continue;
                }

                result = true;
                continue;
            }
            else {
                depth += 2;
                depth--;
                continue;
            }
        }
        else if(type == EXPR_IMPURE_VAL) {
            *data += sizeof(exprType);
            size_t vlen = *(size_t *)*data;
            *data += sizeof(size_t);
            *data += vlen;

            result = false;
            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_FUN) {
            *data += sizeof(exprType);
            *data += sizeof(impureFunpt);

            result = false;
            depth--;
            continue;
        }
    }

    return result;
}

void replaceBindings(bindt oldBind, bindt newBind, byte **data) {
    ssize_t depth = 1;
    while(depth > 0) {
        exprType type = *(exprType *)*data;

        if(false) {}
        else if(isBind(type)) {
            bindt mbind = *(bindt *)*data;

            if(mbind == oldBind) {
                *(bindt *)*data = newBind;
            }

            *data += sizeof(bindt);

            depth--;
            continue;
        }
        else if(type == EXPR_FUN) {
            *data += sizeof(exprType);
            *data += sizeof(bindt);

            depth += 1;
            depth--;
            continue;
        }
        else if(type == EXPR_APP) {
            *data += sizeof(exprType);
            
            depth += 2;
            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_VAL) {
            *data += sizeof(exprType);
            size_t vlen = *(size_t *)*data;
            *data += sizeof(size_t);
            *data += vlen;

            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_FUN) {
            *data += sizeof(exprType);
            *data += sizeof(impureFunpt);

            depth--;
            continue;
        }
    }
}

void makeUniqueBindings(byte *data) {
    ssize_t depth = 1;

    while(depth > 0) {
        exprType type = *(exprType *)data;

        if(false) {}
        else if(isBind(type)) {
            data += sizeof(bindt);

            depth--;
            continue;
        }
        else if(type == EXPR_FUN) {
            data += sizeof(exprType);
            bindt bind = *(bindt *)data;
            var(newBind);
            *(bindt *)data = newBind;
            data += sizeof(bindt);

            byte *sdata = data;
            replaceBindings(bind, newBind, &sdata);

            depth += 1;
            depth--;
            continue;
        }
        else if(type == EXPR_APP) {
            data += sizeof(exprType);

            depth += 2;
            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_VAL) {
            data += sizeof(exprType);
            size_t vlen = *(size_t *)data;
            data += sizeof(size_t);
            data += vlen;

            depth--;
            continue;
        }
        else if(type == EXPR_IMPURE_FUN) {
            data += sizeof(exprType);
            data += sizeof(impureFunpt);

            depth--;
            continue;
        }
    }
}

void evaluate(expr *e) {
    replaceList list = mkrl();

    byte *odata = e->data;
    byte *data = e->data;

    size_t rpos;
    size_t rlen;

    size_t fpos;
    size_t flen;

    impureFunpt imfun = NULL;

    while(scanForSubst(odata, &data, &list, &rpos, &rlen, &fpos, &flen, &imfun)) {
        bool useImpureFunction = imfun != NULL;
        size_t imrlen = rlen;

        byte *rdata = Malloc(rlen);
        memcpy(rdata, e->data + rpos, rlen);

        if(useImpureFunction) {
            expr impureResult = imfun(rdata, rlen);
            Free(rdata);
            rdata = impureResult.data;
            imrlen = impureResult.len;
        }

        if(!useImpureFunction) {
            byte *_rdata = rdata;
            makeUniqueBindings(_rdata);
        }

        size_t extraBytesPerBind = (imrlen - sizeof(bindt));
        size_t oldLen = e->len;
        size_t newLen = e->len + extraBytesPerBind * list.len - rlen - flen;

        memmove(e->data + rpos, e->data + rpos + rlen, e->len - (rpos + rlen)); 
        memmove(e->data + fpos, e->data + fpos + flen, e->len - (fpos + flen)); 
        e->data = Realloc(e->data, newLen);
        e->len = newLen;
        odata = e->data;

        size_t extra = 0;
        for(size_t i = 0; i < list.len; i++) {
            size_t offset = list.offsets[i] - flen + extra;
            size_t toMove = oldLen + extra - offset - flen - rlen - sizeof(bindt);
            extra += extraBytesPerBind;

            memmove(odata + offset + sizeof(bindt) + extraBytesPerBind, odata + offset + sizeof(bindt), toMove);

            memcpy(odata + offset, rdata, imrlen);
        }

        Free(rdata);
        list.len = 0;
        odata = e->data;
        data = e->data;
        imfun = NULL;
    }

    rlfree(list);
}

// ==================
// CONSTRUCTORS
// ==================

expr mkBind(bindt bind) {
    size_t len = sizeof(bindt);
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    *(bindt *)b.data = bind;
    return b;
}

expr mkFun(bindt bind, expr body) {
    size_t len = sizeof(exprType) + sizeof(bindt) + body.len;
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_FUN;
    data += sizeof(exprType);

    *(bindt *)data = bind;
    data += sizeof(bindt);

    memcpy(data, body.data, body.len);
    byte *p = data;
    makeUniqueBindings(p);

    maybeFree(body);
    return b;
}

expr mkApp(expr lhs, expr rhs) {
    size_t len = sizeof(exprType) + lhs.len + rhs.len;
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_APP;
    data += sizeof(exprType);

    memcpy(data, lhs.data, lhs.len);
    byte *p = data;
    makeUniqueBindings(p);
    data += lhs.len;

    memcpy(data, rhs.data, rhs.len);
    p = data;
    makeUniqueBindings(p);
    
    maybeFree(lhs);
    maybeFree(rhs);
    return b;
}

expr mkImpureVal(byte *value, size_t vlen) {
    size_t len = sizeof(exprType) + sizeof(size_t) + vlen;
    expr b = { .aux = false, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_IMPURE_VAL;
    data += sizeof(exprType);

    *(size_t *)data = vlen;
    data += sizeof(size_t);

    memcpy(data, value, vlen);
    return b;
}

expr mkImpureFun(impureFunpt fun) {
    size_t len = sizeof(exprType) + sizeof(impureFunpt);
    expr b = { .aux = false, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_IMPURE_FUN;
    data += sizeof(exprType);
    *(impureFunpt *)data = fun;

    return b;
}
        
// ==================
// PRINTING
// ==================

char getBindSymbol(bindt bind, bindt binds[], size_t *lastBind, char symbols[], size_t bindsAmount) {
    for(size_t i = 0; i < *lastBind; i++) {
        if(binds[i] == bind) return symbols[i];
    }

    if(*lastBind >= bindsAmount) return '?';

    binds[*lastBind] = bind;
    return symbols[(*lastBind)++];
}

void _printExpr(byte **data, bindt binds[], size_t *lastBind, char symbols[], bool isRhs, int bindsAmount) {
    exprType type = *(exprType *)*data;

    if(false) {}
    else if(isBind(type)) {
        *data += sizeof(bindt);
        printf("%c", getBindSymbol((bindt)type, binds, lastBind, symbols, bindsAmount));
    }
    else if(type == EXPR_FUN) {
        *data += sizeof(exprType);
        bindt bind = *(bindt *)*data;
        printf("( λ%c.", getBindSymbol(bind, binds, lastBind, symbols, bindsAmount));
        *data += sizeof(bindt);
        _printExpr(data, binds, lastBind, symbols, false, bindsAmount);
        printf(" )");
    }
    else if(type == EXPR_APP) {
        if(isRhs) printf("(");
        *data += sizeof(exprType);
        _printExpr(data, binds, lastBind, symbols, false, bindsAmount);
        _printExpr(data, binds, lastBind, symbols, true, bindsAmount);
        if(isRhs) printf(")");
    }
    else if(type == EXPR_IMPURE_VAL) {
        *data += sizeof(exprType);
        size_t vlen = *(size_t *)*data;
        printf("[%lu bytes]", vlen);
        *data += sizeof(size_t);
        *data += vlen;
    }
    else if(type == EXPR_IMPURE_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(impureFunpt);
        printf("<fun>");
    }
}

void printExpr(expr e) {
    bindt binds[52] = {0};
    size_t lastBind = 0;
    char symbols[52] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    byte *data = e.data;
    _printExpr(&data, binds, &lastBind, symbols, false, 52);
    printf("\n");
}

// ==================
// MACROS / EXPRESSIONS
// ==================

#define Bind(bi) mkBind(bi)

expr Church(size_t num) {
    var(s);
    var(z);
    size_t allocSize = sizeof(exprType) + sizeof(bindt) +
                       sizeof(exprType) + sizeof(bindt) +
                       num * (sizeof(exprType) + sizeof(bindt)) +
                       sizeof(bindt);

    byte *data = Malloc(allocSize);
    byte *sdata = data;

    *(exprType *)sdata = EXPR_FUN;
    sdata += sizeof(exprType);

    *(bindt *)sdata = s;
    sdata += sizeof(bindt);

    *(exprType *)sdata = EXPR_FUN;
    sdata += sizeof(exprType);

    *(bindt *)sdata = z;
    sdata += sizeof(bindt);

    for(size_t i = 0; i < num; i++) {
        *(exprType *)sdata = EXPR_APP;
        sdata += sizeof(exprType);

        *(bindt *)sdata = s;
        sdata += sizeof(bindt);
    }

    *(bindt *)sdata = z;
    sdata += sizeof(bindt);

    return (expr){ .data = data, .len = allocSize, .aux = true };
}

#define App(l, r) \
    {0}; \
    { \
        expr __lhs; \
        { \
            expr temp = l; \
            __lhs = temp; \
        } \
        expr __rhs; \
        { \
            expr temp = r; \
            __rhs = temp; \
        } \
        temp = mkApp(__lhs, __rhs); \
    } \

#define Fun(b, body) \
    {0}; \
    { \
        var(b); \
        { \
            expr __fun; \
            { \
                expr temp = body; \
                __fun = temp; \
            } \
            temp = mkFun(b, __fun); \
        } \
    }

#define Defun(fname, b, body) \
    expr fname; \
    { \
        var(b); \
        expr __fun; \
        { \
            expr temp = body; \
            __fun = temp; \
        } \
        fname = mkFun(b, __fun); \
    } \
    fname.aux = false; \
    evaluate(&fname);

#define DefunLazy(fname, b, body) \
    expr fname; \
    { \
        var(b); \
        expr __fun; \
        { \
            expr temp = body; \
            __fun = temp; \
        } \
        fname = mkFun(b, __fun); \
    } \
    fname.aux = false; \

#define Defvar(vname, body) \
    expr vname; \
    { \
        expr temp = body; \
        vname = temp; \
    } \
    vname.aux = false; \
    evaluate(&vname);

#define DefvarLazy(vname, body) \
    expr vname; \
    { \
        expr temp = body; \
        vname = temp; \
    } \
    vname.aux = false;

#define DefunImpure(fname, argty, argname, body) \
    expr __##fname(byte *__##argname, size_t len) { \
        exprType type = *(exprType *)__##argname; \
        if(type != EXPR_IMPURE_VAL) { \
            printf("Impure function expected type %d found type %lu\n", EXPR_IMPURE_VAL, type); \
            exit(1); \
        } \
        __##argname += sizeof(exprType); \
        __##argname += sizeof(size_t); \
        len -= sizeof(exprType); \
        len -= sizeof(size_t); \
        if(len != sizeof(argty)) { \
            printf("Impure function expected input length %lu, found length %lu\n", sizeof(argty), len); \
            exit(1); \
        } \
        argty argname = *(argty *)__##argname; \
 \
        body; \
 \
        argty *__result = Malloc(sizeof(argty)); \
        *__result = argname; \
        expr __expr = mkImpureVal((byte *)__result, sizeof(argty)); \
        Free(__result); \
        return __expr; \
    } \
    const uint64_t __test[] = { EXPR_IMPURE_FUN, (uint64_t)__##fname }; \
    expr fname = (expr){ .aux = false, .len = sizeof(exprType) + sizeof(impureFunpt), .data = (byte *)__test };

#define DefvarImpure(vname, vty, vval) \
    vty *__##vname = Malloc(sizeof(vty)); \
    *__##vname = vval; \
    expr vname = mkImpureVal((byte *)__##vname, sizeof(vty));

#define ReadVarImpure(var, ty) *(ty *)(var.data + sizeof(exprType) + sizeof(size_t))
        
// ==================
// USAGE
// ==================

expr __ImpureIdentity(byte *ptr, size_t len) {
    byte *nptr = Malloc(len);
    memcpy(nptr, ptr, len);
    return (expr){ .aux = false, .data = nptr, .len = len };
}

DefunImpure(ImpureIncrement, uint64_t, num, {
    num++;
});

int main() {
    // Zero and Successor
    Defun(Zero, s, Fun(z, Bind(z)));
    Defun(Succ, w, Fun(y, Fun(x, App(Bind(y), App(App(Bind(w), Bind(y)), Bind(x))))));

    // Simple numbers
    Defvar(One, App(Succ, Zero));
    Defvar(Two, App(Succ, One));
    Defvar(Three, App(Succ, App(Succ, App(Succ, Zero))));
    Defvar(Four, App(Succ, Three));

    // Sum and Multiplication
    Defun(Sum, x, Fun(y, App(App(Bind(x), Succ), Bind(y))));
    Defun(Mul, x, Fun(y, Fun(z, App(Bind(x), App(Bind(y), Bind(z))))));

    // More complicated numbers
    Defvar(Five, App(App(Two, Succ), Three));
    Defvar(Six, App(App(Sum, Three), Three));
    Defvar(Twelve, App(App(Mul, Three), Four));
    Defvar(Twenty, App(App(Mul, Five), Four));

    // Booleans
    Defun(True, x, Fun(y, Bind(x)));
    Defun(False, x, Fun(y, Bind(y)));

    // Boolean operations
    Defun(And, x, Fun(y, App(App(Bind(x), Bind(y)), False)));
    Defun(Or, x, Fun(y, App(App(Bind(x), True), Bind(y))));
    Defun(Not, x, App(App(Bind(x), False), True));

    Defun(IsZero, x, App(App(App(Bind(x), False), Not), False));

    Defvar(ZeroIsZero, App(IsZero, Zero));
    Defvar(TwoIsZero, App(IsZero, Two));

    // Boolean operations examples
    Defvar(BothZeroAndTwoAreZero, App(App(And, ZeroIsZero), TwoIsZero));
    Defvar(EitherZeroOrTwoIsZero, App(App(Or, ZeroIsZero), TwoIsZero));

    // Predecessor
    Defun(PredAux, p, Fun(z, App(App(Bind(z), App(Succ, App(Bind(p), True))), App(Bind(p), True))));
    Defun(Pred, n, App(App(App(Bind(n), PredAux), Fun(z, App(App(Bind(z), Zero), Zero))), False));

    // Predecessor example
    Defvar(Eleven, App(Pred, Twelve));

    // Comparison
    Defun(IsGreaterOrEqual, x, Fun(y, App(IsZero, App(App(Bind(x), Pred), Bind(y)))));
    Defun(IsLess, x, Fun(y, App(Not, App(App(IsGreaterOrEqual, Bind(x)), Bind(y)))));
    Defun(IsEqual, x, Fun(y, App(App(And, App(App(IsGreaterOrEqual, Bind(x)), Bind(y))), App(App(IsGreaterOrEqual, Bind(y)), Bind(x)))));
    Defun(IsLessOrEqual, x, Fun(y, App(App(Or, App(App(IsLess, Bind(x)), Bind(y))), App(App(IsEqual, Bind(x)), Bind(y)))));
    Defun(IsGreater, x, Fun(y, App(App(And, App(App(IsGreaterOrEqual, Bind(x)), Bind(y))), App(Not, App(App(IsEqual, Bind(x)), Bind(y))))));

    // Comparison examples
    Defvar(FiveGThree, App(App(IsGreater, Five), Three));
    Defvar(TwoGThree, App(App(IsGreater, Two), Three));
    Defvar(TwoLEFive, App(App(IsLessOrEqual, Two), Five));
    Defvar(FiveLEFive, App(App(IsLessOrEqual, Five), Five));

    // Recursive Y and Z combinators
    DefunLazy(YC, y, App(Fun(x, App(Bind(y), App(Bind(x), Bind(x)))), Fun(x, App(Bind(y), App(Bind(x), Bind(x))))));
    DefunLazy(ZC, f, App(Fun(x, App(Bind(f), Fun(v, App(App(Bind(x), Bind(x)), Bind(v))))), Fun(x, App(Bind(f), Fun(v, App(App(Bind(x), Bind(x)), Bind(v)))))));
    ZC = ZC;

    // Sum via Y combinator
    Defun(SumNatAux, r, Fun(n, App(App(App(IsZero, Bind(n)), Zero), App(App(Bind(n), Succ), App(Bind(r), App(Pred, Bind(n)))))));
    DefunLazy(SumNat, n, App(App(YC, SumNatAux), Bind(n)));
    Defvar(SumTwelve, App(SumNat, Twelve));

    // Factorial via Y combinator
    Defun(FactAux, f, Fun(n, App(App(App(IsZero, Bind(n)), One), App(App(Mul, Bind(n)), App(Bind(f), App(Pred, Bind(n)))))));
    DefunLazy(Fact, n, App(App(YC, FactAux), Bind(n)));
    Defvar(FactFive, App(Fact, Five));

    // Defining impure values for confirming results
    DefvarImpure(ImpureZero, uint64_t, 0);
    DefvarImpure(ImpureOne, uint64_t, 1);
    Defvar(ImpureFalse, ImpureZero);
    Defvar(ImpureTrue, ImpureOne);

    // Tests
    Defun(CheckNumber, n, App(App(Bind(n), ImpureIncrement), ImpureZero));
    Defun(CheckBool, b, App(App(Bind(b), ImpureTrue), ImpureFalse));

    Defvar(CheckTwenty, App(CheckNumber, Twenty));
    printf("Twenty evaluates to: %lu\n", ReadVarImpure(CheckTwenty, uint64_t));

    Defvar(CheckFour, App(CheckNumber, Four));
    printf("Four evaluates to: %lu\n", ReadVarImpure(CheckFour, uint64_t));

    Defvar(CheckEleven, App(CheckNumber, Eleven));
    printf("Eleven evaluates to: %lu\n", ReadVarImpure(CheckEleven, uint64_t));

    Defvar(CheckZeroIsZero, App(CheckBool, ZeroIsZero));
    printf("isZero(0) evaluates to: %s\n", boolToStr(ReadVarImpure(CheckZeroIsZero, bool)));

    Defvar(CheckTwoIsZero, App(CheckBool, TwoIsZero));
    printf("isZero(2) evaluates to: %s\n", boolToStr(ReadVarImpure(CheckTwoIsZero, bool)));

    Defvar(CheckBothZeroAndTwoAreZero, App(CheckBool, BothZeroAndTwoAreZero));
    printf("isZero(0) && isZero(2) evaluates to: %s\n", boolToStr(ReadVarImpure(CheckBothZeroAndTwoAreZero, bool)));

    Defvar(CheckEitherZeroOrTwoIsZero, App(CheckBool, EitherZeroOrTwoIsZero));
    printf("isZero(0) || isZero(2) evaluates to: %s\n", boolToStr(ReadVarImpure(CheckEitherZeroOrTwoIsZero, bool)));

    Defvar(CheckFiveGThree, App(CheckBool, FiveGThree));
    printf("5 > 3 evaluates to: %s\n", boolToStr(ReadVarImpure(CheckFiveGThree, bool)));

    Defvar(CheckTwoGThree,  App(CheckBool, TwoGThree));
    printf("2 > 3 evaluates to: %s\n", boolToStr(ReadVarImpure(CheckTwoGThree, bool)));

    Defvar(CheckTwoLEFive,  App(CheckBool, TwoLEFive));
    printf("2 <= 5 evaluates to: %s\n", boolToStr(ReadVarImpure(CheckTwoLEFive, bool)));

    Defvar(CheckFiveLEFive, App(CheckBool, FiveLEFive));
    printf("5 <= 5 evaluates to: %s\n", boolToStr(ReadVarImpure(CheckFiveLEFive, bool)));

    Defvar(CheckSumTwelve, App(CheckNumber, SumTwelve));
    printf("Sum of all numbers up to twelve evaluates to: %lu\n", ReadVarImpure(CheckSumTwelve, uint64_t));

    Defvar(CheckFactFive, App(CheckNumber, FactFive));
    printf("Five factorial evaluates to: %lu\n", ReadVarImpure(CheckFactFive, uint64_t));

    // Defvar(Large, Church(60));
    // Defvar(SumNatLarge, App(SumNat, Large));
    // Defvar(CheckSumNatLarge, App(CheckNumber, SumNatLarge));
    // printf("Large sumnat evaluates to: %lu\n", ReadVarImpure(CheckSumNatLarge, uint64_t));

#ifdef MEM_STATS
    printf("MALLOC: %ld; FREE: %ld; FINAL: %ld; PEAK: %ld\n", mallocCount, freeCount, finalCount, peakCount);
#endif

    return 0;
}
