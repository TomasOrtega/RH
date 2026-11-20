import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem wd_apply' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem wd_anti' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w w' : σ → Module.End ℂ E) (h : ∀ i j, Commute (w i) (w' j)) (c : Finset σ → E) :
    wd w (wd w' c) + wd w' (wd w c) = 0 := by
  funext t
  have hc : ∀ f : σ → σ → E, ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = ∑ i ∈ t, ∑ j ∈ t.erase i, f j i := by
    intro f
    refine Finset.sum_comm' ?_
    intro x y
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨Ne.symm b, a⟩, c⟩, fun ⟨⟨b, a⟩, c⟩ => ⟨a, Ne.symm b, c⟩⟩
  simp only [wd_apply', map_sum, map_zsmul, Finset.smul_sum, smul_smul, Pi.add_apply, Pi.zero_apply]
  conv_lhs => rhs; rw [hc]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  have hjt : j ∈ t := (Finset.mem_erase.1 hj).2
  have hcomm : w' j (w i (c ((t.erase j).erase i))) = w i (w' j (c ((t.erase i).erase j))) := by
    rw [show (t.erase j).erase i = (t.erase i).erase j from Finset.erase_right_comm]
    exact (LinearMap.congr_fun (h i j).eq _).symm
  rw [hcomm, ← add_smul, GlobalTheory.cubeSign_mul_erase hi hjt (Ne.symm hji), neg_add_cancel, zero_smul]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem cubeSign_map' {σ σ' : Type} [LinearOrder σ] [LinearOrder σ'] (e : σ' ↪o σ)
    (s : Finset σ') (i : σ') :
    GlobalTheory.cubeSign (s.map e.toEmbedding) (e i) = GlobalTheory.cubeSign s i := by
  simp only [GlobalTheory.cubeSign, Finset.filter_map, Finset.card_map]
  congr 2
  ext x
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.productCup_of_system.wdBasic_of :
    WdBasic := by
  intro σ E _ _ _ _ A w
  have d2 : (∀ i j, Commute (w i) (w j)) → ∀ c, wd w (wd w c) = 0 := by
    intro h c
    have hx := wd_anti' w w h c
    have h2 : (2 : ℂ) • wd w (wd w c) = 0 := by rw [two_smul]; exact hx
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨d2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hw, hA⟩ n a ha
    refine ⟨?_, d2 hw a⟩
    simp only [acx, Submodule.mem_pi, Set.mem_univ, forall_const] at ha ⊢
    intro s
    rw [wd_apply']
    by_cases hs : (s.card : ℤ) = n + 1
    · rw [if_pos hs]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_
      have hcard : ((s.erase i).card : ℤ) = n := by
        have := Finset.card_erase_add_one hi
        omega
      have hmem := ha (s.erase i)
      rw [if_pos hcard] at hmem
      have := hA (s.erase i) i (by simp) _ hmem
      rwa [Finset.insert_erase hi] at this
    · rw [if_neg hs, Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hcard : ¬ ((s.erase i).card : ℤ) = n := by
        have := Finset.card_erase_add_one hi
        omega
      have hmem := ha (s.erase i)
      rw [if_neg hcard, Submodule.mem_bot] at hmem
      rw [hmem, map_zero, smul_zero]
  · intro w'
    refine LinearMap.ext fun c => funext fun t => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, wd_apply', smul_add, Finset.sum_add_distrib]
  · intro w' h _ c
    exact wd_anti' w w' h c
  · intro c
    funext t
    rw [wd_apply']
    simp only [Module.End.one_apply]
    rfl
  · intro σ' _ e c s
    rw [wd_apply', wd_apply', Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [RelEmbedding.coe_toEmbedding, cubeSign_map']
    rw [Finset.map_erase]
    rfl
