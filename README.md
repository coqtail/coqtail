# Coqtail

[Coqtail](https://coqtail.github.io/index.html) is a library of
mathematical theorems and tools proved inside the Coq proof assistant.
Results range mostly from arithmetic to real and complex analysis.

[Coqtail is now being developed and maintained at
coq-community](https://github.com/coq-community/coqtail-math), where
contributions are welcome! The present repository only exists for
related, older, materials, please do not use it for development.

## Requirements

`master` is developed with Coq 8.11.0, which is its only requirement,
but the following git tags point to snapshots for different versions
of Coq, which should cover most versions from 8.5 to 8.11.

- tag `v8.6.1` for Coq 8.5pl3 and Coq 8.6.1
- tag `v8.7.2` for Coq 8.7.2
- tag `v8.8.2` for Coq 8.8.2
- tag `v8.9.1` for Coq 8.9.1
- tag `v8.10.2` for Coq 8.10.2
- tag `v8.11.0` for Coq 8.11.0
- see the [new repository](https://github.com/coq-community/coqtail-math) for Coq 8.12+

Use e.g. `git checkout v8.10.2` if you want to use Coq 8.10.2. Note
that those tags are for backward compatibility only, there is no
intention of maintaining them as branches. Go to the
[new repository](https://github.com/coq-community/coqtail-math)
instead for development.

## Compiling

Running `cd src; make` should suffice. It uses a `_CoqProject` file,
which should also allow you to use coqide and proofgeneral with no
further configuration.

## Developer's todo list

Big things:

- prove linear and non-linear theory of ℂ is decidable (using Groebner
  basis)

Lemmas to prove:

- Mertens' Theorem for Complex numbers
- (expand this list to your wish)

Maintenance:

- Use -Q instead of -R and fix the resulting loadpath problems
- Opam package for `make install`
- Check for commented lemmas (and admits)
- Remove useless "Require"s
- Check for admits (run "./todos.sh").
- Check for commented results (run "./todos.sh comments")
