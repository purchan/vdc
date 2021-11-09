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
For example, the three-valued AND logic gate truth table is:
| AND | **0** | **X** | **1** |
|:-:|:-:|:-:|:-:|
| **0** | 0 | 0 | 0 |
| **X** | 0 | X | X |
| **1** | 0 | X | 1 |
The bold column represents input value from the golden circuit, and the bold row represents input value from the revised circuit.
This truth table is derived from the fact that AND(0, x) = 0, AND(1, x) = x.

Compatible equivalence gate is the three-valued version of XOR gate in the miter circuit.
| ≡C | **0** | **X** | **1** |
|:-:|:-:|:-:|:-:|
| **0** | 0 | 1 | 1 |
| **X** | 0 | 0 | 0 |
| **1** | 1 | 1 | 0 | 
Notice that the table matrix is not symmetric, as the revised circuit is allowed to enforce an 0 value or 1 value on each X value of the golden circuit.

### Using SAT
By "booleanize" every three-valued wire and gates,
we can use the well-developed SAT verification method to help us calculate the three-valued SAT.

We can use two two-valued wires to represent a three-valued wire. 
For example, one of the possible mapping is: {(00, 0), (01, 1), (10, X), (11, X)}.
This uses the first two-valued wire to represent whether the value is X or not X, and the second two-valued wire to represent whether the value is 0 or 1.

Using the mapping above, we can use a two-valued circuit to represent a three-valued logic gate.
For example, the two-valued circuit representing the three-valued AND logic gate has the following truth table:
| AND | **00** | **01** | **11** | **10** |
|:-:|:-:|:-:|:-:|:-:|
| **00** | 00 | 00 | 00 | 00 |
| **01** | 00 | 01 | 1X | 1X |
| **11** | 00 | 1X | 1X | 1X |
| **10** | 00 | 1X | 1X | 1X |

By using the equivalent two-valued circuit of the compatible equivalence gate as the miter circuit component, we can finally verify the compatible equivalence between two three-valued circuit.

### The Code
We verify that the "booleanize" mapping keeps the structure of the three-valued circuit.
```
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs
compile : Circ Γ Δ → Circ (toBools Γ) (toBools Δ)
Cr⟦_⟧ : Circ Γ Δ → Vals Γ → Vals Δ

correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr⟦ compile c ⟧ bvals)
```
- ⟦ C ⟧ ∘ decode = decode ∘ ⟦ compile C ⟧

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

## Further Links
- [ ICCAD 2020 Contest - Problem A ](http://iccad-contest.org/2020/Problem_A/20200618_cad_contest_problem_a.pdf)
- [ Josh Ko's blog ](https://josh-hs-ko.github.io/blog/0009/)
