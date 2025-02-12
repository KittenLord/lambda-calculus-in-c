# Lambda Calculus in C

In case you have ever wanted to use something more Lispy than C, this repo is for you

Some useful info is written at the top of the `main.c`, check it out

## Example code

```
Defun(Zero, s, Fun(z, Bind(z)));
Defun(Succ, w, Fun(y, Fun(x, App(Bind(y), App(App(Bind(w), Bind(y)), Bind(x))))));
Defvar(One, App(Succ, Zero));
Defvar(Two, App(Succ, One));
```

## TODO:

- [x] Fix memory leaks (real)
- [ ] Make some sort of a header
- [x] Memory corruption when trying to CheckNumber a sufficiently large number (around 130)
- [ ] Make `scanForSubst` and `evaluate` process more than one substitution at a time (this will probably make it five gazillion times faster)
- [ ] Try removing all `memmove`s
- [ ] Try preallocating memory in `evaluate`
