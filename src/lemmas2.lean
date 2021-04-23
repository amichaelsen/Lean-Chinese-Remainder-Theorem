import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import algebra.euclidean_domain
import data.int.basic
import data.equiv.ring
noncomputable theory

open nat nat.modeq zmod euclidean_domain 
namespace lemmas2

/- LEMMAS FOR CHINESE REMAINDER THEOREM WITH 2 CONGRUENCE RELATIONS -/

/--
Two natural numbers are equal if and only if they are mutual divisors
-/
lemma eq_iff_dvd_dvd {n m : ℕ } : n = m ↔ m ∣ n ∧ n ∣ m :=
begin
    split, 
    intro H, 
    rw H, 
    split; 
    refl,
 
    intro H,
    rcases H with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩, 
    rw hd,
    rw hc at hd,
    induction m with x hx,  
    rw zero_mul at hc,
    rw hc,
    ring,

    rw mul_assoc at hd,
    have hd' : x.succ * (c * d) = x.succ,
        linarith,
    rw mul_right_eq_self_iff at hd',
    have h : d = 1,
        rw nat.mul_eq_one_iff at hd',
        exact hd'.2,
    rw h,
    ring,
    exact succ_pos',
end

/-- 
Given coprime natural numbers M1 M2, find the inverse of M2 M1 
assuming that both are nonzero so avoid (1,0) case which is silly. 
-/
lemma nat_inv (M1 M2 : ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H : coprime M1 M2) :
                         ∃ b1 : ℕ, modeq M1 (b1 * M2) 1 := 
begin
    -- first cast to Z/M1 Z and get the group inverse 
    have hb1 := mul_inv_eq_gcd (M2 : zmod M1),  
    have H' := coprime.symm H,
    unfold coprime at *, 
    rw val_nat_cast M2 at hb1, 

    have H'' : (M2 % M1).gcd M1 = M2.gcd M1, 
    begin
        have qr  := div_add_mod (M2 : ℤ) (M1 : ℤ ),
        have qr' : (M1 * (M2 / M1) + M2 % M1) = M2,
            begin
                rw [← int.coe_nat_div M2 M1,
                    ← int.coe_nat_mod M2 M1,
                    ← int.coe_nat_mul _ _ ,
                    ← int.coe_nat_add _ _ ,
                      int.coe_nat_inj'] at qr,
                exact qr,
            end,
        -- want to show  M2.gcd M1 ∣ (M2 % M1).gcd M1,
        have div1 : M2.gcd M1 ∣ (M2 % M1).gcd M1, 
        begin   
            have f1 := gcd_dvd_left M2 M1,
            have f2 := gcd_dvd_right M2 M1,
            have f3 : M2.gcd M1 ∣ M1 * (M2 / M1),
                {cases f2 with c hc,
                use c * (M2 / M1),
                rw ← mul_assoc,
                rw ← hc,},
            have f4 : M2.gcd M1∣ M1 * (M2 / M1) + M2 % M1,
                {rw qr',
                exact f1,},
            rw nat.dvd_add_right f3 at f4,
            exact dvd_gcd f4 f2,
        end,
        -- want to show  (M2 % M1).gcd M1 ∣ M2.gcd M1,
        have div2 : (M2 % M1).gcd M1 ∣ M2.gcd M1, 
        begin
            have f1 := gcd_dvd_right (M2 % M1) M1,
            have f2 := gcd_dvd_left (M2 % M1) M1,
            have f3 := dvd_mul_of_dvd_left f1 (M2 / M1),
            have f4 : (M2 % M1).gcd M1 ∣ M2,
            begin    
                have k := (nat.dvd_add_right f3).2 f2,
                rw qr' at k,  
                exact k, 
            end,
            exact dvd_gcd f4 f1,         
        end,
        have div : M2.gcd M1 ∣ (M2 % M1).gcd M1 ∧ (M2 % M1).gcd M1 ∣ M2.gcd M1, 
            exact ⟨div1, div2⟩,
        rw ← eq_iff_dvd_dvd at div,
        exact div, 
    end,
    -- use coprimeness and equality of gcd's to get as an actual inverse
    rw [H'',H'] at hb1,     
    use (M2 : zmod M1)⁻¹.val,
    --translate this to zmod M1
    rw ← nat_coe_eq_nat_coe_iff _ _ _, 
    simp at *,
    rw mul_comm,

    have fact : (((M2 : zmod M1)⁻¹.val) : zmod M1) = (M2 : zmod M1)⁻¹,
    begin
        rw @nat_cast_zmod_val _ _,
        use M1pos,
    end,
    rw fact,
    exact hb1, 
end

/- LEMMAS FOR CHINESE REMAINDER THEOREM WITH K CONGRUENCE RELATIONS -/


end lemmas2


