# Lean

This project was a collaboration with Rose Lopez as part of the UC Berkeley Summer 2020 [Lean Seminar](https://sites.google.com/view/berkeleyleanseminar). 

Lean is a theorem proving programming language where lemmas and theorems are formalized in the header and the function code uses ```tactics``` and prior results to check the desired conclusion. To learn more check out the Lean Community page [here](https://leanprover-community.github.io/index.html) or get started on the Natural Numbers Game Tutorial [here](https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/). 

## Project Goal

The goal of this project was to implement a version of the Chinese Remainder Theorem in Lean. You can check out our slides used to present on this project in the seminar [here](https://drive.google.com/file/d/1SuDF7DOl59ERRkO-dbzAO1d8Ki3RPenC/view). 


There are several versions of the Chinese Remainder Theorem from purely arithmetic to ring theory. The version of the CRT we aimed to implement the congruences version as follows. 

>**Chinese Remainder Theorem** _Given k coprime integers n1, n2,..., nk and any k integers a1, a2, ..., ak then:_
>- _(Existence) There exists an integer x such that x is congruent to ai modulo ni for every i=1,2,...,k_
>- _(Uniqueness) The value of x above is unique modulo N, where N=n1 * n2 * ... * nk._

To prove this full version we inducted on a smaller version with only two congruences 

>**Chinese Remainder Theorem 'Lite'** _Given 2 coprime integers M1 and M2 and 2 integers a1 and a2 then:_
>- _(Existence) There exists an integer x such that x is congruent to a1 modulo M1 and congruent to a2 modulo M2_
>- _(Uniqueness) The value of x above is unique modulo M1 * M2_

While the Lean mathlib library has an implementation for the Lite version of CRT we elected to derive our own version to gain familiraity with Lean as well as provide consistency in the implementation with the full version. 


## File Overview

### **Main Files**

**```CRT2.lean```** - contains the statements and proof for existence and uniqueness of **Chinese Remainder Theorem 'Lite'** using lemmas from ```lemmas2.lean```.  

**```CRT.lean```** - contains the statements and proof for existence and uniqueness of the full **Chinese Remainder Theorem** using lemmas from ```lemmas2.lean``` and ```defs_lemmas.lean``` as well as the results from ```CRT2.lean```.

### **Supporting Files**

**```lemmas2.lean```** - derives helpful lemmas for the proof of CRT2.  **Note:** This file contains 1 ```sorry``` due to updates in the ```zmod/basics.lean``` file from the mathlib directory added after the completion of this project.

**```defs_lemmas.lean```** - develops definitions for lists of congruences and proves lemmas about these to help handle the data of arbitrary lists of congruences for the full **Chinese Remainder Theorem** 

### **Other Files**

**```CRT_isomorphism.lean```** - the beginnings of a proof for the ring theory isomorphism version of the Chinese Remainder Theorem. This file contains mostly lemma headers with few proofs (and hence many ```sorry```'s!). 






