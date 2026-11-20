import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Simplify using `[wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
private theorem wd_apply' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `hc : ∀ f : σ → σ → E, ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = ∑ i ∈ t, ∑ j ∈ t.erase i, f j i`. Introduce `f`. Use `Finset.sum_comm' ?_` and prove the remaining obligations. Introduce `x y`.

Simplify using `only [Finset.mem_erase]`. Conclude with `⟨fun ⟨a, b, c⟩ => ⟨⟨Ne.symm b, a⟩, c⟩, fun ⟨⟨b, a⟩, c⟩ => ⟨a, Ne.symm b, c⟩⟩`. Simplify using `only [wd_apply', map_sum, map_zsmul, Finset.smul_sum, smul_smul, Pi.add_apply, Pi.zero_apply]`. Use `conv_lhs => rhs`. Rewrite using `[hc]`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hji : j ≠ i` using `(Finset.mem_erase.1 hj).1`.

Establish `hjt : j ∈ t` using `(Finset.mem_erase.1 hj).2`. Establish `hcomm : w' j (w i (c ((t.erase j).erase i))) = w i (w' j (c ((t.erase i).erase j)))`. Rewrite using `[show (t.erase j).erase i = (t.erase i).erase j from Finset.erase_right_comm]`. Conclude with `(LinearMap.congr_fun (h i j).eq _).symm`. Rewrite using `[hcomm, ← add_smul, GlobalTheory.cubeSign_mul_erase hi hjt (Ne.symm hji), neg_add_cancel, zero_smul]`.
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
Simplify using `only [GlobalTheory.cubeSign, Finset.filter_map, Finset.card_map]`. Use `congr 2`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
private theorem cubeSign_map' {σ σ' : Type} [LinearOrder σ] [LinearOrder σ'] (e : σ' ↪o σ)
    (s : Finset σ') (i : σ') :
    GlobalTheory.cubeSign (s.map e.toEmbedding) (e i) = GlobalTheory.cubeSign s i := by
  simp only [GlobalTheory.cubeSign, Finset.filter_map, Finset.card_map]
  congr 2
  ext x
  simp

/- English proof (translation)
Introduce `σ E _ _ _ _ A w`. Establish `d2 : (∀ i j, Commute (w i) (w j)) → ∀ c, wd w (wd w c) = 0`. Introduce `h c`. Establish `hx` using `wd_anti' w w h c`. Establish `h2 : (2 : ℂ) • wd w (wd w c) = 0` using `by rw [two_smul]; exact hx`.

Conclude with `(smul_eq_zero.1 h2).resolve_left two_ne_zero`. Use `⟨d2, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨hw, hA⟩ n a ha`. Use `⟨?_, d2 hw a⟩` and prove the remaining obligations. Simplify using `only [acx, Submodule.mem_pi, Set.mem_univ, forall_const] at ha ⊢`.

Introduce `s`. Rewrite using `[wd_apply']`. Distinguish the cases in `hs : (s.card : ℤ) = n + 1`. Rewrite using `[if_pos hs]`. Use `Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations.

Establish `hcard : ((s.erase i).card : ℤ) = n`. Use `Finset.card_erase_add_one hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmem` using `ha (s.erase i)`. Rewrite `hmem` using `[if_pos hcard]`.

Use `hA (s.erase i) i (by simp) _ hmem` as an intermediate fact. Rewrite `this` using `[Finset.insert_erase hi]`. Then use the resulting hypothesis. Rewrite using `[if_neg hs, Submodule.mem_bot]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hcard : ¬ ((s.erase i).card : ℤ) = n`.

Use `Finset.card_erase_add_one hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmem` using `ha (s.erase i)`. Rewrite `hmem` using `[if_neg hcard, Submodule.mem_bot]`. Rewrite using `[hmem, map_zero, smul_zero]`.

Introduce `w'`. Use `LinearMap.ext fun c => funext fun t => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Pi.add_apply, wd_apply', smul_add, Finset.sum_add_distrib]`. Introduce `w' h _ c`. Conclude with `wd_anti' w w' h c`.

Introduce `c`. Use function extensionality and compare the values at `t`. Rewrite using `[wd_apply']`. Simplify using `only [Module.End.one_apply]`. Both sides reduce to the same expression.

Introduce `σ' _ e c s`. Rewrite using `[wd_apply', wd_apply', Finset.sum_map]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [RelEmbedding.coe_toEmbedding, cubeSign_map']`. Rewrite using `[Finset.map_erase]`.

Both sides reduce to the same expression.
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
