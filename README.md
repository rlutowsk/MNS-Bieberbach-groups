# Calculating minimal non-solvable Bieberbach groups

The repository contains code needed for calculations presented in the article

[R. Lutowski, A. Szczepański, *Minimal nonsolvable Bieberbach groups*](https://arxiv.org/abs/2302.11368)

## Short description of the contents of the files

- `mns.g`: calculating minimal nonsolvable subgroups of a given group, up to conjugacy
- `imf.g`: calculating minimal nonsolvable subgroups of finite irreducible subgroups of GL(n,Z)
- `qtbl.g`: dealing with rational characters and character tables of finite groups
- `perfect.g`: finding mns groups in the library of perfect groups
- `run.g`: tools to reproduce the results of the article

## How to reproduce the results

Simply invoke

```gap
gap> Read("run.g");
```

followed by

```gap
gap> run(10, 10^6);
```

Function `run` accepts the third argument, describing the verbosity level:

    - 0: default - print nothing
    - 1: print the rational character tables of minimal nonsolvable subgroups found
    - 2: additionally, print some information about what is going on
    - 3: print more details on what group is calculated
