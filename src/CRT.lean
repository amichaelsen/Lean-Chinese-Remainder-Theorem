import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic

open nat nat.modeq zmod 


--  inverses mod n 

/- mathlib inverses in zmod n

-/

-- 2 congruence statements

lemma eq_iff_dvd_dvd {n m : ℕ } (hn: n ≠ 0) (hm: m ≠ 0): 
                     n = m  ↔ m ∣ n ∧ n ∣ m :=
begin
    split, 
    intro H, 
    rw H, 
    split; 
    refl,

    intro H, 
    have H' : n ≤ m ∧ m ≤ n,
    begin
        rcases H with ⟨H1, H2⟩, 
        split, 
        cases H2 with d Hd, 
        cases d, 

        -- zero case
        exfalso, 
        rw mul_zero at Hd,
        exact hm Hd, 

        --d+1 case
        rw Hd,
        rw succ_eq_add_one,
        sorry,
        sorry, 
    end,
    linarith, 
end

lemma nat_inv (M1 M2: ℕ ) (H: coprime M1 M2): ∃ b1 : ℕ, modeq M1 (b1*M2) 1 := 
begin
    let b1 := (M2 : zmod M1)⁻¹,
    have hb1 := mul_inv_eq_gcd (M2: zmod M1),  
    have H' := coprime.symm H,
    unfold coprime at *, 
    rw val_cast_nat M2 at hb1, 
    have H'' : (M1 % M2).gcd M2 = M1.gcd M2, 
    begin
        
    end,
    --rw [H'', H] at hb2,  
end  

theorem CRTwith2exist (a1 a2 M1 M2: ℕ ) (H: coprime M1 M2) : ∃ x : ℕ , modeq M1 x a1 ∧ modeq M2 x a2 :=
begin
    -- cast m1 and m2 into zmod m2 and zmod m1 ... then take inverses
    cases nat_inv M1 M2 H with b1 Hb1, 
    cases nat_inv M2 M1 (coprime.symm H) with b2 Hb2, 
    --solution x = a1 b1 m2 + a2 b1 m2 
    use (a1*b1*M2 + a2*b2*M1),
    split,  
    {
        rw ← add_zero a1, --can we change to just do right side? 
        apply modeq_add, 
        simp only [add_zero],
        rw ← mul_one a1, 
        rw mul_assoc, 
        apply modeq_mul,  
        simp only [mul_one],
        exact Hb1, 

        rw modeq_iff_dvd,
        simp only [dvd_mul_left, zero_sub, int.coe_nat_zero, dvd_neg, int.coe_nat_mul], 
    },
    {
        rw ← zero_add a2, --can we change to just do right side? 
        apply modeq_add, 
        rw modeq_iff_dvd,
        simp only [dvd_mul_left, zero_sub, int.coe_nat_zero, dvd_neg, int.coe_nat_mul],

        simp only [zero_add],
        rw ← mul_one a2, 
        rw mul_assoc, 
        apply modeq_mul,  
        simp only [mul_one],
        exact Hb2,         
    }
end

theorem CRTwith2unique (x1 x2 a1 a2 M1 M2: ℕ) (H: coprime M1 M2) 
    (H1: modeq M1 x1 a1 ∧ modeq M2 x1 a2) (H2: modeq M1 x2 a1 ∧ modeq M2 x2 a2): modeq (M1*M2) x1 x2:=
begin
    sorry,
end

