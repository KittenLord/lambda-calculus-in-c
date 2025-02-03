// =================================================
// Scroll to the very bottom to see the demo :)
// =================================================

// If you want to see the memory usage of this demo (where numbers
// represent the amount of malloc calls), uncomment the following line:
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

    return calloc(1, size);
}

void Free(void *ptr) {
    if(ptr == 0) return;
    freeCount++;
    finalCount--;

    free(ptr);
}
#else
#define Malloc(s) calloc(1, s)
#define Free(p) free(p)
#endif

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
typedef expr impureFunt(byte *data, size_t len);

bool isBind(exprType t) { return t >= 4; }


typedef struct {
    size_t *offsets;
    size_t len;
    size_t cap;
} replaceList;

void rladd(replaceList *list, size_t offset) {
    if(list->len < list->cap) {
        list->offsets[list->len++] = offset;
        return;
    }

    size_t *noffsets = Malloc(list->cap * 2 + 1);
    memcpy(noffsets, list->offsets, list->len);
    list->offsets = noffsets;
    list->cap = list->cap * 2 + 1;

    rladd(list, offset);
}

replaceList rlcopy(replaceList list) {
    size_t *offsets = Malloc(list.len);
    memcpy(offsets, list.offsets, list.len);
    return (replaceList){ .offsets = offsets, .len = list.len, .cap = list.cap };
}

void rlfree(replaceList list) {
    free(list.offsets);
}

#define rlinit 128
#define mkrl() ((replaceList){ .offsets = Malloc(rlinit), .len = 0, .cap = rlinit })

size_t getExprLen(byte *data) {
    exprType type = *(exprType *)(data);

    if(false) {}
    else if(isBind(type)) {
        return sizeof(bindt);
    }
    else if(type == EXPR_FUN) {
        size_t fun = sizeof(exprType) + sizeof(bindt);
        data += fun;
        return fun + getExprLen(data);
    }
    else if(type == EXPR_APP) {
        size_t app = sizeof(exprType);
        data += app;
        size_t lhs = getExprLen(data);
        data += lhs;
        size_t rhs = getExprLen(data);
        return app + lhs + rhs;
    }
    else if(type == EXPR_IMPURE_VAL) {
        size_t ival = sizeof(exprType);
        data += ival;
        size_t vlen = *(size_t *)data;
        return ival + sizeof(size_t) + vlen;
    }
    else if(type == EXPR_IMPURE_VAL) {
        return sizeof(exprType) + sizeof(impureFunpt);
    }
}

void searchBinds(bindt bind, byte *odata, byte **data, replaceList *list) {
    exprType type = *(exprType *)*data;
    
    if(false) {}
    else if(isBind(type)) {
        bindt mbind = *(bindt *)*data;

        if(mbind == bind) {
            rladd(list, *data - odata);
        }

        *data += sizeof(bindt);
        return;
    }
    else if(type == EXPR_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(bindt);
        searchBinds(bind, odata, data, list);
        return;
    }
    else if(type == EXPR_APP) {
        *data += sizeof(exprType);
        searchBinds(bind, odata, data, list);
        searchBinds(bind, odata, data, list);
        return;
    }
    else if(type == EXPR_IMPURE_VAL) {
        *data += sizeof(exprType);
        size_t vlen = *(size_t *)data;
        *data += sizeof(size_t);
        *data += vlen;
        return;
    }
    else if(type == EXPR_IMPURE_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(impureFunpt);
        return;
    }
}

bool scanForSubst(byte *odata, byte **data, replaceList *list, byte **rdata, size_t *rlen) {
    exprType type = *(exprType *)*data;

    if(false) {}
    else if(isBind(type)) {
        *data += sizeof(exprType);
        return false;
    }
    else if(type == EXPR_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(bindt);
        return scanForSubst(odata, data, list, rdata, rlen);
    }
    else if(type == EXPR_APP) {
        *data += sizeof(exprType);
        exprType lhsType = *(exprType *)*data;
        if(lhsType == EXPR_FUN) {
            size_t funLen = getExprLen(*data);
            size_t argLen = getExprLen(*data + funLen);

            bindt bind = *(bindt *)*data;
            *data += sizeof(bindt);

            byte *sdata = *data;
            searchBinds(bind, odata, &sdata, list);

            *rdata = *data + funLen;
            *rlen = argLen;

            return true;
        }
        else {
            bool lhs = scanForSubst(odata, data, list, rdata, rlen);
            if(lhs) return lhs;
            return scanForSubst(odata, data, list, rdata, rlen);
        }
    }
    else if(type == EXPR_IMPURE_VAL) {
        *data += sizeof(exprType);
        size_t vlen = *(size_t *)*data;
        *data += sizeof(size_t);
        *data += vlen;
        return false;
    }
    else if(type == EXPR_IMPURE_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(impureFunpt);
        return false;
    }
}

void replaceBindings(bindt oldBind, bindt newBind, byte **data) {
    exprType type = *(exprType *)*data;

    if(false) {}
    else if(isBind(type)) {
        bindt mbind = *(bindt *)*data;

        if(mbind == oldBind) {
            *(bindt *)*data = newBind;
        }

        *data += sizeof(bindt);
        return;
    }
    else if(type == EXPR_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(bindt);
        replaceBindings(oldBind, newBind, data);
        return;
    }
    else if(type == EXPR_APP) {
        *data += sizeof(exprType);
        replaceBindings(oldBind, newBind, data);
        replaceBindings(oldBind, newBind, data);
        return;
    }
    else if(type == EXPR_IMPURE_VAL) {
        *data += sizeof(exprType);
        size_t vlen = *(size_t *)*data;
        *data += sizeof(size_t);
        *data += vlen;
        return;
    }
    else if(type == EXPR_IMPURE_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(impureFunpt);
        return;
    }
}

void makeUniqueBindings(byte **data) {
    exprType type = *(exprType *)*data;

    if(false) {}
    else if(isBind(type)) {
        *data += sizeof(bindt);
        return;
    }
    else if(type == EXPR_FUN) {
        *data += sizeof(exprType);
        bindt bind = *(bindt *)*data;
        var(newBind);

        byte *sdata = *data;
        replaceBindings(bind, newBind, &sdata);

        *data += sizeof(bindt);
        makeUniqueBindings(data);
        return;
    }
    else if(type == EXPR_APP) {
        *data += sizeof(exprType);
        makeUniqueBindings(data);
        makeUniqueBindings(data);
        return;
    }
    else if(type == EXPR_IMPURE_VAL) {
        *data += sizeof(exprType);
        size_t vlen = *(size_t *)*data;
        *data += sizeof(size_t);
        *data += vlen;
        return;
    }
    else if(type == EXPR_IMPURE_FUN) {
        *data += sizeof(exprType);
        *data += sizeof(impureFunpt);
        return;
    }
}

void evaluate(expr *e) {
    printf("evaluate\n");
    replaceList list = mkrl();

    byte *odata = e->data;
    byte *data = e->data;

    byte *rdata;
    size_t rlen;

    while(scanForSubst(odata, &data, &list, &rdata, &rlen)) {
        size_t extraBytesPerBind = (rlen - sizeof(bindt));
        size_t oldLen = e->len;
        size_t newLen = e->len + extraBytesPerBind * list.len;

        // copying before realloc
        byte *_rdata = Malloc(rlen);
        memcpy(_rdata, rdata, rlen);
        rdata = _rdata;

        e->data = realloc(e->data, newLen);
        odata = e->data;

        size_t extra = 0;
        for(int i = 0; i < list.len; i++) {
            size_t offset = list.offsets[i];
            size_t toMove = oldLen - offset;
            offset += extra;
            extra += extraBytesPerBind;

            memmove(odata + offset + sizeof(bindt), odata + offset + sizeof(bindt) + extraBytesPerBind, toMove);

            _rdata = rdata;
            makeUniqueBindings(&_rdata);
            memcpy(odata + offset, rdata, rlen);
        }

        free(rdata);
        list.len = 0;
        data = odata;
    }

    rlfree(list);
}

void maybeFree(expr e) {
    if(e.aux) Free(e.data);
}

expr mkBind(bindt bind) {
    size_t len = sizeof(bindt);
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    *(bindt *)b.data = bind;
    return b;
}

expr mkFun(bindt bind, expr body) {
    size_t len = sizeof(exprType) + body.len;
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_FUN;
    data += sizeof(exprType);

    memcpy(data, body.data, body.len);

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
    data += lhs.len;
    memcpy(data, rhs.data, rhs.len);
    
    maybeFree(lhs);
    maybeFree(rhs);
    return b;
}

expr mkImpureVal(size_t vlen, byte *value) {
    size_t len = sizeof(exprType) + vlen;
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_IMPURE_VAL;
    data += sizeof(exprType);

    memcpy(data, value, vlen);
    return b;
}

expr mkImpureFun(impureFunpt fun) {
    size_t len = sizeof(exprType) + sizeof(impureFunpt);
    expr b = { .aux = true, .data = Malloc(len), .len = len };
    byte *data = b.data;

    *(exprType *)data = EXPR_IMPURE_FUN;
    data += sizeof(exprType);
    *(impureFunpt *)data = fun;

    return b;
}

// ==================
// MACROS
// ==================

#define Bind(bi) mkBind(bi)

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

/*
#define DefunImpure(fname, argty, argname, body) \
    expr __##fname(byte *__##argname, size_t len) { \
        if(!(len == sizeof(argty))) { \
            printf("Unexpected arg length in impure function. Expected: %lu, Actual: %lu, line: %d\n", sizeof(argty), len, __LINE__); \
            exit(1); \
        } \
        argty argname = *(argty *)__##argname; \
        body; \
        __##argname = Malloc(sizeof(argty)); \
        *__##argname = argname; \
        return (expr){ .type = EXPR_IMPURE_VAL, .valp = __##argname, .vall = sizeof(argty) }; \
    } \
    expr fname = (expr){ .type = EXPR_IMPURE_FUN, .fun = __##fname }; \

#define DefvarImpure(vname, vty, vval) \
    vty *__##vname = Malloc(sizeof(vty)); \
    *__##vname = vval; \
    expr vname = (expr){ .type = EXPR_IMPURE_VAL, .valp = (byte *)__##vname, .vall = sizeof(vty) }; \

#define ReadVarImpure(var, ty) *(ty *)var.valp
*/
        
// ==================
// USAGE
// ==================

/*
expr __ImpureIdentity(byte *ptr, size_t len) {
    byte *ret = Malloc(len);
    memcpy(ret, ptr, len);
    return (expr){ .type = EXPR_IMPURE_VAL, .valp = ret, .vall = len };
}

DefunImpure(ImpureIncrement, uint64_t, num, {
    num++;
});
*/

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
    Defvar(Five, App(App(Sum, Two), Three));
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

    // Sum via Y combinator
    Defun(SumNatAux, r, Fun(n, App(App(App(IsZero, Bind(n)), Zero), App(App(Bind(n), Succ), App(Bind(r), App(Pred, Bind(n)))))));
    DefunLazy(SumNat, n, App(App(YC, SumNatAux), Bind(n)));
#if defined(SLOW) && defined(SLOW_SUMNAT)
    Defvar(SumTwelve, App(SumNat, Twelve));
#endif

    // Factorial via Y combinator
    Defun(FactAux, f, Fun(n, App(App(App(IsZero, Bind(n)), One), App(App(Mul, Bind(n)), App(Bind(f), App(Pred, Bind(n)))))));
    DefunLazy(Fact, n, App(App(YC, FactAux), Bind(n)));
#if defined(SLOW) && defined(SLOW_FACTORIAL)
    Defvar(FactFive, App(Fact, Five));
#endif

/*
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

#if defined(SLOW) && defined(SLOW_SUMNAT)
    Defvar(CheckSumTwelve, App(CheckNumber, SumTwelve));
    printf("Sum of all numbers up to twelve evaluates to: %lu\n", ReadVarImpure(CheckSumTwelve, uint64_t));
#endif

#if defined(SLOW) && defined(SLOW_FACTORIAL)
    Defvar(CheckFactFive, App(CheckNumber, FactFive));
    printf("Five factorial evaluates to: %lu\n", ReadVarImpure(CheckFactFive, uint64_t));
#endif

#ifdef MEM_STATS
    printf("MALLOC: %ld; FREE: %ld; FINAL: %ld; PEAK: %ld\n", mallocCount, freeCount, finalCount, peakCount);
#endif

*/

    return 0;
}
