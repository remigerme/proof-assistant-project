# Proof assistant project of CSC_51051_EP

To clone the project :

```bash
git clone git@github.com:remigerme/proof-assistant-project.git
```

This is my implementation of the [proof assistant project of CSC_51051_EP](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/4.prover.html). It contains the folders

1. [simple](simple/): the proof assistant for propositional logic (parts 1 to 4 of the project),
2. [dependent](dependent/): the proof assistant with dependent types (part 5),
3. [report](report/): the final report.

In order to run the two different provers you can type (inside their respective directories) :

```bash
dune exec ./prover.exe
```

You might need to first execute

```bash
eval $(opam config env)
```

You can also build the report from the markdown source file, using pandoc and the Makefile inside the `report` folder :

```bash
make
```
