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
    have hd' : x.succ * (c * d) = x.succ,
        linarith,
    rw mul_right_eq_self_iff at hd',
    have h : d = 1,
        rw mul_eq_one_iff at hd',
        exact hd'.2,
    rw h,
    ring,
    exact succ_pos',
end


lemma nat_inv (M1 M2 : ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H : coprime M1 M2) :
                         ∃ b1 : ℕ, modeq M1 (b1 * M2) 1 := 
begin
    -- first cast to Z/M1 Z and get the group inverse 
    have hb1 := mul_inv_eq_gcd (M2 : zmod M1),  
    have H' := coprime.symm H,
    unfold coprime at *, 
    rw val_cast_nat M2 at hb1, 

    have H'' : (M2 % M1).gcd M1 = M2.gcd M1, 
    begin
        have qr  := div_add_mod (M2 : ℤ) (M1 : ℤ ),
        have qr' : (M1 * (M2 / M1) + M2 % M1) = M2,
            rw ← int.coe_nat_div M2 M1 at qr,
            rw ← int.coe_nat_mod M2 M1 at qr,
            rw ← int.coe_nat_mul _ _ at qr,
            rw ← int.coe_nat_add _ _ at qr,
            rw int.coe_nat_inj' at qr,
            exact qr,
        -- want to show  M2.gcd M1 ∣ (M2 % M1).gcd M1,
        have div1 : M2.gcd M1 ∣ (M2 % M1).gcd M1, 
        begin
        have f1 : M2.gcd M1 ∣ M2 ,
            exact gcd_dvd_left M2 M1,
        have f2 : M2.gcd M1 ∣ M1,
            exact gcd_dvd_right M2 M1,
        have f3 : M2.gcd M1 ∣ M1 * (M2 / M1),
            cases f2 with c hc,
            use c * (M2 / M1),
            rw ← mul_assoc,
            rw ← hc,
       
        have f4 : M2.gcd M1∣ M1 * (M2 / M1) + M2 % M1,
            rw qr',
            exact f1,
        rw nat.dvd_add_right f3 at f4,
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
                have k := (nat.dvd_add_right f3).2 f2,
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

    have fact : (((M2 : zmod M1)⁻¹.val) : zmod M1) = (M2 : zmod M1)⁻¹,
    begin
        --exact wrapper_for_cast_val M1pos ((M2: zmod M1)⁻¹ : zmod M1), 
        rw @cast_val _ M1pos ((M2  : zmod M1)⁻¹: zmod M1), --need the '@' to make fact explicity 
    end,
    rw fact,
    exact hb1, 
end  



theorem CRTwith2exist (a1 a2 M1 M2 : ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H : coprime M1 M2) :
                         ∃ x : ℕ , modeq M1 x a1 ∧ modeq M2 x a2 :=
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

theorem CRTwith2unique (x1 x2 a1 a2 M1 M2 : ℕ)  (M1pos : 0 < M1) (M2pos : 0 < M2)
            (H : coprime M1 M2) (H1 : modeq M1 x1 a1 ∧ modeq M2 x1 a2) 
            (H2 : modeq M1 x2 a1 ∧ modeq M2 x2 a2) : modeq (M1 * M2) x1 x2 :=
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

def cong := (Σ (n : ℕ), zmod n)

def congruences := list cong

--Examples 
 def x : Σ (n : ℕ), zmod n := ⟨5, ↑2⟩
 def y : list (Σ (n : ℕ), zmod n) := [⟨5, ↑2⟩ , ⟨3, ↑2⟩]
 def z : list (Σ (n : ℕ), zmod n) := []
 #reduce list.tail y
 #reduce y.tail
--end examples



/- LIST PROPERTIES -/

/- all moduli for the congruences in the list are pairwise coprime
   required for application of chinese remainder theorem -/
def pairwise_coprime  (l : congruences) : Prop := list.pairwise (λ (x y : cong), nat.coprime x.1 y.1) l

/- all moduli for the congruences in the list are nonzero,
   prevents congruences mod 0, but not mod 1  -/
def nonzero_cong ( l : congruences) : Prop := list.all l (λ (c : cong), 0 < c.1)  

/-  defines when x is a solution to the list of congruences  in l -/
def solution (x : ℕ) (l : congruences) : Prop := list.all l (λ (c : cong), modeq c.1 x c.2.val)

/- takes the product of the defining moduli of all congruences in the list -/
def cong_prod : congruences → ℕ
    | list.nil := 1
    | (h :: t) := h.1 * cong_prod t



/- LEMMAS ABOUT LIST PROPERTIES -/

/- if a list satisfies nonzero_cong, so does the tail and the head has nonzero moduli-/
lemma subset_nonzero (c : cong) (l : list cong) (H : nonzero_cong (c :: l)) : 0 < c.1 ∧ nonzero_cong l :=
begin
    unfold nonzero_cong at H, 
    rw list.all_iff_forall_prop at H, 
    split, 
    {
        exact H c (by exact list.mem_cons_self c l),
    },
    {
        unfold nonzero_cong, 
        rw list.all_iff_forall_prop,
        rintros a ha, 
        exact H a (by exact list.mem_cons_of_mem _ ha),
    }
end 

/- if a list satisfies pairwise_coprime the head is coprime to all 
    moduli in the tail and the tail satisfies pairwise_coprime -/
lemma subset_coprime (c : cong) (l : list cong) (H : pairwise_coprime (c :: l)) :
                     (∀ (a : cong), a ∈ l → coprime c.1 a.1) ∧ pairwise_coprime l :=
begin
    unfold pairwise_coprime at H,
    rw list.pairwise_cons at H, 
    exact H,
end

lemma mem_div_prod (l : list cong) (a : cong) (H : a ∈ l) : a.1 ∣ cong_prod l :=
begin
    induction l with head tail ihtail,
     --nil case
    exfalso,
    exact H,
    --induction case
    dsimp[cong_prod],
    cases H,
    rw H,
    simp only [nat.dvd_mul_right],
    specialize ihtail H,
    cases ihtail with c hc,
    rw hc,
    rw mul_comm,
    use c * head.fst,
    ring,
end
 

/-  LEMMAS ABOUT CONG_PROD OUTPUTS -/ 

/- given a list of congruences with nonzero (i.e. positive) 
   moduli, the product of those moduli will be positive -/
lemma pos_prod (l : congruences) (H : nonzero_cong l) : 0 < cong_prod l :=
begin
    induction l with head tail ihtail,
    {
        dsimp [cong_prod],
        linarith,
    },
    {
        have nonzero_parts := subset_nonzero head tail H,
        specialize ihtail nonzero_parts.right,
        dsimp [cong_prod],
        exact mul_pos nonzero_parts.left ihtail,
    }
end



/- the modulus of the first congruence is coprime to the product of the moduli of 
    the tail of the list assuming that the entire list satisfies pairwise_coprime-/
lemma coprime_prod (c : cong) (l : list cong) (H : pairwise_coprime (c :: l)) :
                             coprime c.1 (cong_prod l) :=
begin
    induction l with head tail ihtail,
    {
        dsimp[cong_prod],
        by exact c.fst.coprime_one_right,
    },
    {
        dsimp[cong_prod],
        apply nat.coprime.mul_right,
        exact (subset_coprime c (head :: tail) H).left head (by exact list.mem_cons_self head tail),
        apply ihtail,
        unfold pairwise_coprime at *, 
        rw list.pairwise_cons at *, 
        split, 
        intros a ha, 
        refine H.left a (by exact list.mem_cons_of_mem head ha), 
        exact list.pairwise_of_pairwise_cons H.right,  
    },
end 

/- CRT: (Existence) Given a list of congruences with coprime and nonzero moduli, 
        there exists a natural number x that solves every congruence simultaneously -/
theorem CRT_existence (l : congruences) (H_coprime : pairwise_coprime l) 
            (H_nonzero : nonzero_cong l) : ∃ x : ℕ, solution x l := 
begin
    induction l with cong1 other_congs ind_hyp, 
    { --null cases with empty list, use x=1 since any x is a "solution"
        unfold solution,
        use 1,
        rw list.all_nil (λ (c : cong), modeq c.1 1 c.2.val),
        simp only [bool.coe_sort_tt],        
    },
    {--inductive case
        --Want to apply CRTwith2exists by getting facts about congruences for input 
        -- obtain relevant hypothesis for applying CRTwith2exists
        have congs_nonzero := (subset_nonzero cong1 other_congs H_nonzero).right,
        have congs_pairwise_coprime := (subset_coprime cong1 other_congs H_coprime).right,
        
        have head_pos := (subset_nonzero cong1 other_congs H_nonzero).left,
        have tail_prod_pos := pos_prod other_congs (subset_nonzero cong1 other_congs H_nonzero).right,
        have head_coprime_to_tail_prod := coprime_prod cong1 other_congs H_coprime,
      
        --specialize ind_hyp congs_pairwise_coprime congs_nonzero, -- (wrapped into next line)
        rcases ind_hyp  congs_pairwise_coprime congs_nonzero with ⟨y, hy⟩, 
        have soln := CRTwith2exist cong1.2.val y cong1.1 (cong_prod other_congs) head_pos tail_prod_pos head_coprime_to_tail_prod,
        cases soln with x hx,
        use x,
        unfold solution,
        rw list.all_iff_forall_prop,
        intros a ha,
        cases ha,
        rw ha,
        exact hx.left,
        unfold solution at hy,
        rw list.all_iff_forall_prop at hy,
        specialize hy a ha,
        have cong_div := mem_div_prod other_congs a ha,
        have xymod    := modeq.modeq_of_dvd_of_modeq cong_div hx.2,
        exact modeq.trans xymod hy,
    },
end

theorem CRT_uniqueness (x1 x2 : ℕ) (l : congruences) (H_nonzero : nonzero_cong l)
                        (H_coprime : pairwise_coprime l) (H1 : solution x1 l) (H2 : solution x2 l) :
                             modeq (cong_prod l) x1 x2 :=
begin
    unfold solution at H1 H2, 
    rw list.all_iff_forall_prop at H1 H2, 
    induction l with head tail ihtail, 
    --list.nil case
    dsimp [cong_prod], 
    rw modeq.modeq_iff_dvd,
    simp only [one_dvd, int.coe_nat_zero, int.coe_nat_succ, zero_add],

    --induction case 
    dsimp [cong_prod],
    have h1 : x1 ≡ x2 [MOD head.1], 
    begin
        have k1 := H1 head (by exact list.mem_cons_self head tail), 
        have k2 := modeq.symm (H2 head (by exact list.mem_cons_self head tail)), 
        exact modeq.trans k1 k2, 
    end,
    have h2 : x1 ≡ x2 [MOD cong_prod tail], 
    begin
        apply ihtail, 
        exact (subset_nonzero head tail H_nonzero).right,
        exact (subset_coprime head tail H_coprime).right,
        intros a ha, 
        exact H2 a (by exact list.mem_cons_of_mem head ha),
        intros a ha, 
        exact H1 a (by exact list.mem_cons_of_mem head ha),        
    end,
    have coprime :=  coprime_prod head tail H_coprime,
    rw ← modeq.modeq_and_modeq_iff_modeq_mul, 
    exact ⟨h1, h2⟩, 
    exact coprime, 
end

