# Lean

This project was a collaboration with Rose Lopez as part of the UC Berkeley Summer 2020 [Lean Seminar](https://sites.google.com/view/berkeleyleanseminar). 

Lean is a theorem proving programming language where lemmas and theorems are formalized in the header and the function code uses ```tactics``` and prior results to check the desired conclusion. To learn more check out the Lean Community page [here](https://leanprover-community.github.io/index.html). 

## Project Goal

The goal of this project was to implement a version of the Chinese Remainder Theorem in Lean. You can check out our slides used to present on this project in the seminar [here](https://drive.google.com/file/d/1SuDF7DOl59ERRkO-dbzAO1d8Ki3RPenC/view). 


There are several versions of the Chinese Remainder Theorem from purely arithmetic to ring theory. The version of the CRT we aimed to implement the congruences version as follows. 

>**Chinese Remainder Theorem** _Given k coprime integers n1, n2,..., nk and any k integers a1, a2, ..., ak then:_
>- _There exists an integer x such that x is congruent to ai modulo ni for every i=1,2,...,k_
>- _The value of x above is unique modulo N, where N=n1 * n2 * ... * nk._

To prove this full version we inducted on a smaller version with only two congruences 

>**Chinese Remainder Theorem Lite** _Given 2 coprime integers M1 and M2 and 2 integers a1 and a2 then:_
>- _There exists an integer x such that x is congruent to a1 modulo M1 and congruent to a2 modulo M2_
>- _The value of x above is unique modulo M1 * M2_

While the Lean mathlib library has an implementation for the Lite Version of CRT we elected to derive our own version to gain familiraity with Lean as well as provide consistency in the implementation with the full version. 



