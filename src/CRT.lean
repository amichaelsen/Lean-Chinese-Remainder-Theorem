import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import algebra.euclidean_domain
import data.int.basic
import data.equiv.ring
import lemmas2
import defs_lemmas
import CRT2
noncomputable theory

open nat nat.modeq zmod euclidean_domain lemmas2 defs_lemmas CRT2
namespace CRT


/- THE STATEMENT & PROOFS FOR GENERAL CRT WITH CONGRUENCE -/

/-- 
CRT: (Existence) Given a list of congruences with coprime and nonzero moduli, 
there exists a natural number x that solves every congruence simultaneously 
-/
theorem CRT_existence (l : congruences) (H_coprime : pairwise_coprime l) 
            (H_nonzero : nonzero_cong l) : ∃ x : ℕ, solution x l := 
begin
    induction l with cong1 other_congs ind_hyp, 
    { --null cases with empty list, use x=1 since any x is a "solution"
        unfold solution,
        use 1,
        rw list.all_nil (λ (c : cong), modeq c.1 1 c.2.val),
        simp only [bool.coe_sort_tt], },
    {--inductive case
        --Want to apply CRTwith2exists by getting facts about congruences for input 
        -- obtain relevant hypothesis for applying CRTwith2exists
        have congs_nonzero := (subset_nonzero cong1 other_congs H_nonzero).right,
        have congs_pairwise_coprime := (subset_coprime cong1 other_congs H_coprime).right,
        have head_pos := (subset_nonzero cong1 other_congs H_nonzero).left,
        have tail_prod_pos := pos_prod other_congs (subset_nonzero cong1 other_congs H_nonzero).right,
        have head_coprime_to_tail_prod := coprime_prod cong1 other_congs H_coprime,
      
        rcases ind_hyp congs_pairwise_coprime congs_nonzero with ⟨y, hy⟩, 
        have soln := CRTwith2exist cong1.2.val y cong1.1 (cong_prod other_congs) head_pos tail_prod_pos head_coprime_to_tail_prod,
        clear ind_hyp H_coprime congs_nonzero H_nonzero congs_pairwise_coprime
                head_pos tail_prod_pos head_coprime_to_tail_prod,
        
        -- show the solution from CRTwith2exist satisfies the list of congruences
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
        exact modeq.trans xymod hy, },
end

/-- 
CRT: (Uniqueness) Given a list of congruences with coprime and nonzero moduli, 
any two solutions will be congruent modulo the cong_prod of the list  
-/
theorem CRT_uniqueness (x1 x2 : ℕ) (l : congruences) (H_nonzero : nonzero_cong l)
                            (H_coprime : pairwise_coprime l) 
                            (H1 : solution x1 l) (H2 : solution x2 l) :
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


end CRT