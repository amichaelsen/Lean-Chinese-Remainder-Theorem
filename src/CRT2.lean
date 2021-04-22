import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import algebra.euclidean_domain
import data.int.basic
import data.equiv.ring
import lemmas2
noncomputable theory

open nat nat.modeq zmod euclidean_domain lemmas2
namespace CRT2

/- CHINESE REMAINDER THEOREM WITH 2 CONGRUENCE RELATIONS -/

/-- 
Given two coprime moduli M1 and M2 (nonzero) and natural numbers a1 and a1,
there is a natural number x such that x ≡ a1 [MOD M1]  and  x ≡ a2 [MOD M2]. 
-/
theorem CRTwith2exist (a1 a2 M1 M2 : ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H : coprime M1 M2) :
                         ∃ x : ℕ , modeq M1 x a1 ∧ modeq M2 x a2 :=
begin
    -- get modulo inveres from lemma above
    cases nat_inv M1 M2 M1pos M2pos H with b1 Hb1, 
    cases nat_inv M2 M1 M2pos M1pos (coprime.symm H) with b2 Hb2, 
    --solution x = a1 b1 m2 + a2 b1 m2 
    use (a1*b1*M2 + a2*b2*M1),
    split,  
    --show this is a solution mod M1
        { rw ← add_zero a1, --conv {to_rhs, skip, rw ← add_zero a1}, --applies to just what we see as RHS
        apply modeq_add,
        
        simp only [add_zero],
        rw ← mul_one a1, 
        rw mul_assoc, 
        apply modeq_mul,  
        simp only [mul_one],
        exact Hb1, 

        rw modeq_iff_dvd,
        simp only [dvd_mul_left, zero_sub, int.coe_nat_zero, dvd_neg, int.coe_nat_mul], },
     
      --show this is a solution mod M2
        { rw ← zero_add a2, 
        apply modeq_add, 
        
        rw modeq_iff_dvd,
        simp only [dvd_mul_left, zero_sub, int.coe_nat_zero, dvd_neg, int.coe_nat_mul],

        simp only [zero_add],
        rw ← mul_one a2, 
        rw mul_assoc, 
        apply modeq_mul,  
        simp only [mul_one],
        exact Hb2, }
end

/--
Given two solutions to a pair of congruence relations modulo M1 and M2, 
the two solutions will be congruent modulo M1*M2 
-/
theorem CRTwith2unique (x1 x2 a1 a2 M1 M2 : ℕ)  (M1pos : 0 < M1) (M2pos : 0 < M2)
            (H : coprime M1 M2) (H1 : modeq M1 x1 a1 ∧ modeq M2 x1 a2) 
            (H2 : modeq M1 x2 a1 ∧ modeq M2 x2 a2) : modeq (M1 * M2) x1 x2 :=
begin
    --cosntruct separate modular equations x1 = x2 mod Mi 
    have H3 := modeq.trans H1.left (modeq.symm H2.left),
    have H4 := modeq.trans H1.right (modeq.symm H2.right),
    -- combine modular equations using coprime
    rw ← modeq_and_modeq_iff_modeq_mul, 
    exact ⟨H3, H4⟩, 
    exact H, 
end


end CRT2