# Verfication of digital circuit verification
## Background
This problem is originated from ICCAD 2020 Contest - Problem A.

Given two combinational circuits, a reference circuit G and a refined circuit R, we need to design a procedure to verify if G and R are equivalent (performing the same function).

If booleans are the only valid input, the miter circuit technique is a standard way to verify the circuit equivalence:
- Connect each related input of G and R together
- Connect each related output of G and R as input of a XOR gate
- Do SAT solving on every output of the newly created XOR gates:
  - If SAT, then G and R are **not** equivalent.
  - If not SAT, then G and R are equivalent.

### X-value
We can extend booleans to three values: 0 , 1 and X.
Here, value X represents the situation where the exact value is unknown.

All logic gates originally operating on booleans can be extended to this three-valued logic.
(WIP)

Compatible equivalence gate is the three-valued version of XOR gate in the miter circuit.
(WIP)

### Using SAT
By "booleanize" every three-valued wire and gates,
(WIP)

## Code Structure
All coding files are linked to each other in a line.
```
-- A >> B means A is imported into B.
Agda modules >> lib.agda >> core.agda >> enclib.agda >> encprf.agda >> encore.agda
                Add things not related to circuit
                            Definition of circuit
                                         Defintion of encodes and decodes
                                                        Properties and Proofs
                                                                       Definition of compile and Correctness proof
```
### Things to fix when
Adding new types : ```Ty``` , ```Ty⟦_⟧```, ```decode```, ```size```.

Adding new gates : ```Op``` , ```Op⟦_⟧```.

... and related proofs.

### Proof dependency in ```encprf.agda```
```lookup-dec``` and ```decs-++Vlp``` are used by ```encore.agda```.
```
lookup-dec
 |------------------------------------------┓
look-dec                                   decs-lookup                         decs-++Vlp
 |------------┓------------┓               |----------------┓------------------|
lookup-suf   lookup-ini   lookup-pre       lookup-++Vr      dec-++Vlp          ++Vlp-assoc
 |            |-------------┛                                |                  |
look-suf     lookup-mapThere                                split-bv           ++Vlp-∷
                                                              |-----------┓
                                                            split-ri     split-rc
```
### Properties
- ⟦ C ⟧ ∘ decode = decode ∘ ⟦ compile C ⟧

## Further Links
- [ ICCAD 2020 Contest - Problem A ](http://iccad-contest.org/2020/Problem_A/20200618_cad_contest_problem_a.pdf)
- [ Josh Ko's blog ](https://josh-hs-ko.github.io/blog/0009/)
