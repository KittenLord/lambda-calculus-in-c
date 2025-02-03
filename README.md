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

- [ ] Fix memory leaks (real)
- [ ] Make some sort of a header
