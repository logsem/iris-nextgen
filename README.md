# ⚡️ iris-nextgen

Next generation modality for Iris.

This directory contains the Coq mechanization accompanying the paper
"The Nextgen Modality: A Modality for Non-Frame-Preserving Updates in
Separation Logic".

## Development

The `main` branch is currently developed using Coq version 8.17.1. and coq-equations version 1.3+8.17

### Clone

The project uses submodules for its dependencies. To clone it and the
associated submodules use the following command:

```
git submodule update --init --recursive
```

### Updating dependencies

The following git command updates all the submodules:

```
git submodule update --remote --merge
```
### Building the proofs 

We recommend installing the dependencies using [opam](https://opam.ocaml.org/)

Once you have installed `Coq 8.17.1` and `coq-equations 1.3+8.17`, you can build the project by running:
```
make -jN  # replace N with the number of CPU cores of your machine
```

### Organization 

#### Below is a high level description of the file structure, and select files.

- `case_study`: contains files specific to StackLang (definition, program logic, and examples).

- `case_study/program_logic`: contains language generic files related to the construction of a program logics that use the nextgen modality.

- `lib`: contains the construction of invariants in the presence of the nextgen modality.

- `gmap_view_transformation.v`: provides a generic methodology to define transformations over the map resource algebra.

- `nextgen_soundness.v`: proves soundness of the nextgen modality as it occurs in the weakest precondition.

- `nextgen_independent.v`: defines the independence modality

#### Below is a lookup table for the definitions in the paper.

| Paper                                            | File or Folder                                                  | Name                                                     |
|--------------------------------------------------|-----------------------------------------------------------------|----------------------------------------------------------|
| StackLang syntax (Fig 3)                         | `case_study/stack_lang.v`                                       | `expr`                                                   |
| StackLang step relation (Page 9, Fig 4)          | `case_study/stack_lang.v`                                       | `head_step`                                              |
| Points-to predicates (Page 9)                    | `case_study/rules_unary.v`                                      | `l ↦ v`, `i @@ l ↦ v`, `[size] n`                       |
| Nextgen modality for stack (Page 10)             | `case_study/rules_unary.v`                                      | `next_state`                                             |
| Rules about stack nextgen (Page 10)              | `case_study/rules_unary.v`                                      | `Section heapG_nextgen_updates`                          |
| cut-heap-intro | `case_study/rules_unary.v` | `heap_stack_intro` |
| cut-stack-intro | `case_study/rules_unary.v` | `stack_stack_pop_intro` |
| cut-size-intro | `case_study/rules_unary.v` | `stack_size_frag_intro` |
| Weakest Precondition definition (Fig 5)          | `case_study/program_logic/weakestpre.v`                         | `wp_pre`                                                 |
| Adequacy (Theorem 4.1)                           | `case_study/program_logic/adequacy.v` and `nextgen_soundness.v` | `wp_adequacy_no_lc_single_thread`                        |
| Independence modality (Page 11)                  | `nextgen_independent.v`            | `uPred_bnextgen_ind` |
| ind-intro | `nextgen_independent.v` | `bnextgen_bounded_ind_GenIndependent_intro` |
| cut-ind-intro | `nextgen_independent.v` | `bnextgen_bounded_ind_bnextgen_intro` |
| ind-elim | `nextgen_independent.v` | `bnextgen_bounded_ind_elim` |
| ind-weaken | `nextgen_independent.v` | `bnextgen_bounded_ind_weaken` |
| ind-heap-intro | `case_study/rules_unary.v` | `heap_stack_ind_intro` |
| ind-stack-intro | `case_study/rules_unary.v` | `stack_stack_ind_intro` |
| ind-size-intro | `case_study/rules_unary.v` | `stack_size_frag_ind_intro` |
| Frame rule (Page 11)                             | `case_study/program_logic/weakestpre.v`                         | `wp_frame_l`                                             |
| Context-local Weakest Precondition (Page 11)     | `case_study/program_logic/cl_weakestpre.v`                      | `clwp`                                                   |
| ClSalloc | `case_study/program_logic/cl_weakestpre.v` | `clwp_stack_alloc` |
| Return | `case_study/rules_unary.v` | `wp_return` |
| inv-alloc              | `lib/invariants`     | `own_inv_alloc`    |
| cut-inv-intro | `case_study/rules_unary.v` | `next_state_stack_inv_intro` |
| ind-inv-intro | `case_study/rules_unary.v` | `next_state_stack_inv_ind_intro` |

