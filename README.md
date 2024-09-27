# Calculating minimal non-solvable Bieberbach groups

The repository contains code needed for calculations presented in the article

[R. Lutowski, A. Szczepański, *Minimal nonsolvable Bieberbach groups*](https://arxiv.org/abs/2302.11368)

## Short description of the contents of the files

- `mns.g`: calculating minimal nonsolvable subgroups of a given group, up to conjugacy
- `imf.g`: calculating minimal nonsolvable subgroups of finite irreducible subgroups of GL(n,Z)
- `qtbl.g`: dealing with rational characters and character tables of finite groups
- `perfect.g`: finding mns groups in the library of perfect groups
- `run.g`: tools to reproduce the results of the article
- `run.out`: example output of the `run` function described below

## How to reproduce the results

In the GAP shell simply invoke

```gap
Read("run.g");
```

followed by

```gap
run(10, 10^6);
```

Function `run` accepts the third argument, describing the verbosity level:

- 0: default - print nothing
- 1: print the rational character tables of minimal nonsolvable subgroups found
- 2: additionally, print some information about what is going on
- 3: print more details on what group is calculated

### More on the `run` function

#### Syntax

```gap
run(maxdim, theshold[, verbose])
```

#### Steps

1. Find conjugacy classes of minimal nonsolvable subgroups of order at least `threshold` of irreducible subgroups of GL(n,Z) for n less than or equal to `maxdim`.
1. Find minimal nonsolvable perfect groups of order up to `threshold`.
1. Find minimal nonsolvable perfect groups of order up to `threshold`, which have faithful rational representations in dimensions less than or equal to `maxdim`.
1. Calculate rational character tables of the groups found in the previous step.

### Notes

We are in fact interested in the isomorphism types of groups, hence we consider finite irreducible subgroups of GL(n,Q). In particular, we use the function `ImfNumberQQClasses` from the library of irreducible maximal finite subgroups of GL(n,Z) of GAP.