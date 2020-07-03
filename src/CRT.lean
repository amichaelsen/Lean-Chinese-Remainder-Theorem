import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import algebra.euclidean_domain
import data.int.basic

open nat nat.modeq zmod euclidean_domain 



-- CRT with 2 congruence statements

lemma eq_iff_dvd_dvd {n m : ℕ } : n = m  ↔ m ∣ n ∧ n ∣ m :=
begin
    split, 
    intro H, 
    rw H, 
    split; 
    refl,

    intro H,
    cases H with H1 H2,
    cases H1 with c hc,
    cases H2 with d hd,
    rw hd,
    rw hc at hd,
    induction m with x hx,  
    rw zero_mul at hc,
    rw hc,
    ring,

    rw mul_assoc at hd,
    have hd': x.succ*(c*d)=x.succ,
        linarith,
    rw mul_right_eq_self_iff at hd',
    have h: d=1,
        rw mul_eq_one_iff at hd',
        exact hd'.2,
    rw h,
    ring,
    exact succ_pos',
end


lemma wrapper_for_cast_val {M1 : ℕ} (nonzero: fact (0 < M1)) (b : zmod M1) : ((b.val) : zmod M1) = b :=
begin
    exact cast_val b,
        --rw cast_val ((M2  : zmod M1)⁻¹: zmod M1),
        --rw ← cast_val ((M2  : zmod M1)⁻¹: zmod M1) at hb1,
        --rw [← cast_val     ((u * u⁻¹ : units (zmod (n+1)) ) : zmod (n+1))],
  
        --rw cast_val ((M2: zmod M1)⁻¹),
        --exact nonzero, 
end


lemma nat_inv (M1 M2: ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H: coprime M1 M2): ∃ b1 : ℕ, modeq M1 (b1*M2) 1 := 
begin
    -- first cast to Z/M1 Z and get the group inverse 
    have hb1 := mul_inv_eq_gcd (M2: zmod M1),  
    have H' := coprime.symm H,
    unfold coprime at *, 
    rw val_cast_nat M2 at hb1, 

    have H'' : (M2 % M1).gcd M1 = M2.gcd M1, 
    begin
        have qr := div_add_mod (M2:ℤ) (M1:ℤ ),
        have qr':  (M1 * (M2 / M1) + M2 % M1) = M2,
            rw ← int.coe_nat_div M2 M1 at qr,
            rw ← int.coe_nat_mod M2 M1 at qr,
            rw ← int.coe_nat_mul _ _ at qr,
            rw ← int.coe_nat_add _ _ at qr,
            rw int.coe_nat_inj' at qr,
            exact qr,
        -- want to show  M2.gcd M1 ∣ (M2 % M1).gcd M1,
        have div1 : M2.gcd M1 ∣ (M2 % M1).gcd M1, 
        begin
        have f1: M2.gcd M1 ∣ M2 ,
            exact gcd_dvd_left M2 M1,
        have f2: M2.gcd M1 ∣ (M1),
            exact gcd_dvd_right M2 M1,
        have f3: M2.gcd M1 ∣ M1 *(M2/M1),
            cases f2 with c hc,
            use c*(M2/M1),
            rw ← mul_assoc,
            rw ← hc,
       
        have f4: M2.gcd M1∣ M1 * (M2 / M1) + M2 % M1,
            rw qr',
            exact f1,
        rw nat.dvd_add_right (f3) at f4,
        exact dvd_gcd f4 f2,
        end,
        -- want to show  (M2 % M1).gcd M1 ∣ M2.gcd M1,
        have div2 : (M2 % M1).gcd M1 ∣ M2.gcd M1, 
        begin
            have f1 : (M2 % M1).gcd M1 ∣ M1,
                exact gcd_dvd_right (M2 % M1) M1,
            have f2 : (M2 % M1).gcd M1 ∣ M2 % M1,   
                exact gcd_dvd_left (M2 % M1) M1,
            have f3 : (M2 % M1).gcd M1 ∣ M1 * (M2 / M1),
                by exact dvd_mul_of_dvd_left f1 (M2 / M1),
            have f4 : (M2 % M1).gcd M1 ∣ M2,
                have k:= (nat.dvd_add_right f3).2 f2,
                rw qr' at k,  
                exact k, 
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
    have fact : (((M2: zmod M1)⁻¹.val) : zmod M1)=(M2: zmod M1)⁻¹,
    begin
        exact wrapper_for_cast_val M1pos ((M2: zmod M1)⁻¹ : zmod M1), 
        --rw ← cast_val ((M2  : zmod M1)⁻¹: zmod M1) at hb1, --WHY DOESNT THIS WORK??
    end,
    rw fact,
    exact hb1, 
end  



theorem CRTwith2exist (a1 a2 M1 M2: ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H: coprime M1 M2) : ∃ x : ℕ , modeq M1 x a1 ∧ modeq M2 x a2 :=
begin
    -- get modulo inveres from lemma above
    cases nat_inv M1 M2 M1pos M2pos H with b1 Hb1, 
    cases nat_inv M2 M1 M2pos M1pos (coprime.symm H) with b2 Hb2, 
    --solution x = a1 b1 m2 + a2 b1 m2 
    use (a1*b1*M2 + a2*b2*M1),
    split,  
    {
        rw ← add_zero a1, --conv {to_rhs, skip, rw ← add_zero a1}, --applies to just what we see as RHS
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
        rw ← zero_add a2, 
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

theorem CRTwith2unique (x1 x2 a1 a2 M1 M2: ℕ)  (M1pos : 0 < M1) (M2pos : 0 < M2) (H: coprime M1 M2) 
    (H1: modeq M1 x1 a1 ∧ modeq M2 x1 a2) (H2: modeq M1 x2 a1 ∧ modeq M2 x2 a2): modeq (M1*M2) x1 x2:=
begin
    --cosntruct separate modular equations
    have H3 : x1 ≡ x2 [MOD M1],
    begin
        exact modeq.trans H1.left (modeq.symm H2.left),
    end,
    have H4 : x1 ≡ x2 [MOD M2],
    begin
        exact modeq.trans H1.right (modeq.symm H2.right),
    end,

    -- combine modular equations using coprime
    rw ← modeq_and_modeq_iff_modeq_mul, 
    exact ⟨H3, H4⟩, 
    exact H, 
end

--PLAYING WITH DEFINING CONGRUENCES


--DEFINITIONS 

def cong := (Σ (n:ℕ), zmod (n+1))

def congruences := list cong

def pairwise_coprime  (l : congruences) : Prop := list.pairwise (λ (x y : cong), nat.coprime x.1 y.1) l

--def nonzero_cong (l : congruences) : Prop := list.all (λ (x:cong), x.1 > 0) l, --need bool form of x.1 > 0
--EXAMPLES

def x : Σ (n:ℕ), zmod n := ⟨5, ↑2⟩

def y : list (Σ (n:ℕ), zmod n) := [⟨5, ↑2⟩ , ⟨3, ↑2⟩]


--"inductive"
--DEFINE INDUCTIVE STRUCTURE ON LISTS OF CONGRUENCES (base case = 2 congruences)

 -- HOW DO BOOLEANS WORK IN LEAN? 
theorem CRT (l : congruences) (H: pairwise_coprime l) : false := 
begin
    sorry, 
end



/-
-- how to check all modulus are coprime 

--def pairwise_coprime 

#check list.pairwise (λ (x y : ct), nat.coprime x.1 y.1) y 

#check (list.pairwise (≠) [1,2]) 

example {l : list ℕ} (H: list.pairwise (≠) l) : true := 
begin
    induction l with a b, 
    sorry,
end
-/
