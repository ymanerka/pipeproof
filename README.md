# PipeProof

PipeProof is a methodology and automated tool for verifying that a microarchitectural
specification correctly implements its ISA-level MCM across all possible programs.

PipeProof is based on PipeCheck, CCICheck, and COATCheck, but marks a philosophical shift
by verifying across all possible programs rather than for litmus tests. This repository
is a fork of the COATCheck repository, but adds significant amounts of new code to implement
PipeProof's all-program verification (including modifying the Check suite's solver to be symbolic).
Nevertheless, a lot of the terminology and naming (as well as the uspec domain-specific language
for microarchitectural specifications) comes from the prior tools in the Check suite.
See those papers/websites for details.

http://github.com/daniellustig/pipecheck

http://github.com/ymanerka/ccicheck

http://github.com/daniellustig/coatcheck

### Citing PipeProof

If you use our tool in your work, we would appreciate it if you cite our paper(s):

Yatin A. Manerkar, Daniel Lustig, Margaret Martonosi, and Aarti Gupta.
  "PipeProof: Automated Memory Consistency Proofs for Microarchitectural Specifications",
  *51st International Symposium on Microarchitecture (MICRO)*,
  Fukuoka, Japan, October 2018.

Daniel Lustig+, Geet Sethi+, Margaret Martonosi, and Abhishek Bhattacharjee.
  "COATCheck: Verifying Memory Ordering at the Hardware-OS Interface",
  *21st International Conference on Architectural Support for Programming
  Languages and Operating Systems (ASPLOS)*, Atlanta, GA, April 2016.
  (+: joint first authors)

Yatin A. Manerkar, Daniel Lustig, Michael Pellauer, and Margaret Martonosi.
  "CCICheck: Using uhb Graphs to Verify the Coherence-Consistency Interface",
  *48th International Symposium on Microarchitecture (MICRO)*,
  Honolulu, HI, December 2015.

Daniel Lustig, Michael Pellauer, and Margaret Martonosi.  "PipeCheck:
  Specifying and Verifying Microarchitectural Enforcement of Memory Consistency
  Models", *47th International Symposium on Microarchitecture (MICRO)*,
  Cambridge UK, December 2014.

### Contacting the authors

If you have any comments, questions, or feedback, please contact Yatin Manerkar
at manerkar@princeton.edu, or visit our GitHub page,
github.com/ymanerka/pipeproof.

### Status

At this point, PipeProof is very much a research tool rather than an industry-strength
verification toolchain.  We do appreciate any suggestions or feedback either
in approach or in implementation.  If you are interested in any particular
feature, missing item, or implementation detail, please contact the authors and
we will try to help out as best we can.

## Building and Using PipeProof

### Prerequisites

PipeProof is written in Coq (Gallina) and extracted to OCaml for compilation to a native
executable. PipeProof requires OCaml (v4.0 or later) and Coq (tested on
version 8.4pl5). The authors have compiled and executed PipeProof
successfully on Linux, and have proven the simpleSC and simpleTSO microarchitectures correct
using PipeProof on a Linux machine.

- Coq
  - tested with Coq 8.4pl5 (October 2014)
- OCaml
  - tested with OCaml 4.01.0

### Building

1. `make`

## Basic Usage

To write a new uspec model for PipeProof, keep in mind the following:

1. All constraints are provided in a single uspec file (axioms, mappings, theory lemmas, and chain invariants).
2. You can generally write your microarchitectural axioms as you would when writing traditional uspec
(eg: as you would with prior tools from the Check suite).
3. Your mappings should be provided as a single axiom named `Mappings` (see `simpleSC.uarch` for an example).
4. Theory lemmas should be provided as a single axiom named `Theory_Lemmas` (see `simpleSC.uarch` for an example).
You can simply copy the theory lemmas from `simpleSC.uarch` to your new uspec model unless you're adding something
that requires new theory lemmas. For example, if you were adding a new ISA-level edge `coi` that represents coherence order
between same-core instructions, you may wish to add a theory lemma enforcing that `coi` implies a `co` edge between the
two instructions and that the `SameCore` predicate would be true for the two instructions connected by the edge.
5. Chain invariants should be written as axioms (one per invariant), with each invariant axiom's named
`Invariant_<name-of-invariant>` (see `simpleSC.uarch` for an example).
6. If you are adding new invariant ISA-level edges (like `po_plus`) for your invariants that are not present in the base PipeProof implementation,
you will need to add them to the definition of `ISAEdge` in `FOLPredicate.v`. You will also need to modify most of the functions that
deal with elements of type `ISAEdge` to handle these new ISA-level edges.
7. To enable PipeProof to search generated ISA-level chains for an ISA-level pattern that represents a new invariant edge,
you should add the pattern and its corresponding invariant edge to `InvPatterns` at line 3854 of `FOL.v` as an `(ISAPattern, ISAEdge)` tuple,
where the second element is the invariant edge. Supported patterns are single ISA-level relations or chains of ISA-level relations.

Note that delving into the Gallina code may not be necessary to get your new uspec model to work with PipeProof.

To add a new ISA-level MCM other than SC and TSO, do the following:

1. Add the definition of it as a list of ISA-level axioms after line 5516 in `FOL.v.`
See the definitions of SC and TSO in `FOL.v` for examples.
2. Add the name of your new model to the extraction list at the end of `PipeGraph.v`.
3. Modify the `isa_mcm_for` function in `Main.ml` to allow selection of your new ISA-level MCM
with a command-line parameter.

To run PipeProof, proceed as follows:

`src/pipeproof -s <memoization setting> -l <ISA-level MCM> -f <filtering/covering setting> -c <Distributing ANDs over ORs threshold> -o <output file> -m <uspec file> [-x] [-b <bounded cyclic cex search limit>]`

Note the following points:

1. To use memoization, pass `1` to `-s`, and `0` if you want to run without memoization.
2. Current valid values for the ISA-level MCM are `SC` and `TSO`.
3. The filtering/covering setting is:

- `0` to filter required edges both before and after applying chain invariants (this may help when debugging)
- `1` to filter only after applying chain invariants (the default),
- `2` to add the Covering Sets Optimization to the default,
- `3` to both filter and apply covering sets before and after applying chain invariants (again, may help when debugging)

4. Distributing small ANDs over ORs helps the performance of PipeProof's solver. A value of 5 for this threshold was empirically determined to work well.
5. The `-x` option tells PipeProof to search for a cyclic counterexample through a bounded search if the proof of TC Abstraction support fails. Note that
the proof of TC Abstraction support may fail because:

- the microarchitecture is buggy
- the microarchitecture is correct, but does not satisfy the TC Abstraction support theorem (please see the PipeProof paper for details)
- the microarchitecture is correct, but the chain invariants provided by the user are not strong enough

Thus, if the microarchitecture is correct but PipeProof cannot prove TC Abstraction support for it, the cyclic counterexample search may
never find a counterexample.

6. The `-b` option sets the max size of counterexamples searched for by a cyclic counterexample search. The default is 10.

For more options, just run `pipeproof` by itself to see the list of available
flags.

### Examples

To run PipeProof on simpleSC with no optimizations (but while distributing small ANDs over ORs):

`src/pipeproof -s 0 -l SC -f 1 -c 5 -o mp.out -m uarches/simpleSC.uarch`

To run PipeProof on simpleTSO with Covering Sets, Memoization, and distribution of ANDs over ORs:

`src/pipeproof -s 1 -l TSO -f 2 -c 5 -o mp.out -m uarches/simpleTSO.uarch`

To run PipeProof on simpleTSO with Covering Sets, Memoization, distribution, bounded cyclic counterexample search enabled, and a max bound of 4 for that search:

`src/pipeproof -s 1 -l TSO -f 2 -c 5 -o mp.out -m uarches/simpleTSO.uarch -x -b 4`

## Design Approach

PipeProof is written in Coq, a theorem prover/verification assistant.  For
example, Coq has been used to rigorously and formally verify mathematical
theorems such as the four color theorem, and it has been used to produce
C compilers which provably produce correct C code.  PipeProof itself does not
yet contain any verified theorems or processes.  Nevertheless, we chose Coq to
make for easier integration with other formal models written using Coq, and to
leave open the possibility of formally proving the correctness of our PipeProof
implementation in the future.

In practice, we are interested in using PipeProof as a practical tool.
For this reason, we auto-extract our code from Coq to OCaml (using built-in
Coq methodology for doing so), and we compile this code to run natively.  So
far, we have implemented two algorithmic optimizations (Covering Sets and
Memoization; please see the PipeProof paper for details) that have significantly improved
the runtime of the tool. To see how to enable/disable these optimizations,
please see the "Basic Usage" section above.

We intend to optimize further in future work,
particularly through a parallel implementation of PipeProof's algorithm, which is
highly parallelizable (again, please see the paper for details).
