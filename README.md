# DTS With Coq Library

## To Use the Library

Download the library to your working directory, then run the following on the directory including the library's _CoqProject

`coq_makefile -f _CoqProject -o CoqMakefile`

and compile the library with

`make -f CoqMakefile`

To use the semantic templates and tactics in the library, it suffices to load DTSTactics.v by writing, e.g.,

`Require Import DTSTactics.`

## To Customize the Library

You can add a new tactic (resp. a new semantic template) to DTSTactics.v (resp. SemanticTemplates.v).

Don't forget to recompile the library when you revised DTSTactics.v and/or SemanticTemplates.v!
