import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimirStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVermaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectorsStatement
set_option maxSynthPendingDepth 1

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hbot : lowSpanW μ = ⊥`. Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, hw, rfl⟩`. Conclude with `absurd ⟨m, hm, hw⟩ hne`.

Rewrite `h` using `[hbot, bot_sup_eq]`. Conclude with `hx h`.
-/
theorem exists_exp {μ : Fin n → ℤ} {x : U n} (h : x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n))
    (hx : x ∉ vermaIdeal (rhoVec n)) : ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ := by
  by_contra hne
  have hbot : lowSpanW μ = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨m, hm, hw, rfl⟩
    exact absurd ⟨m, hm, hw⟩ hne
  rw [hbot, bot_sup_eq] at h
  exact hx h

/- English proof (translation)
Use `GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_` and prove the remaining obligations. Simplify using `[h]`.
-/
theorem lowExp_wt_zero {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) (h : wt m = 0) : m = 0 := by
  refine GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_
  simp [h]

/- English proof (translation)
Take `⟨y, hy, w, hw, rfl⟩` from `Submodule.mem_sup.1 h`. Use `clear h`. Establish `: ∃ c : ℂ, y = c • 1`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨m, hm, hw0, rfl⟩` from `hx`. Conclude with `⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, rfl⟩` from `hx`.

Take `⟨d, rfl⟩` from `hy`. Conclude with `⟨c + d, by rw [add_smul]⟩`. Consider the case `smul r x _ hx`. Take `⟨c, rfl⟩` from `hx`. Conclude with `⟨r * c, by rw [mul_smul]⟩`.

Take `⟨c, rfl⟩` from `this`. Conclude with `⟨c, by simpa using hw⟩`.
-/
theorem mem_of_adW_zero {x : U n} (h : x ∈ lowSpanW (0 : Fin n → ℤ) ⊔ vermaIdeal (rhoVec n)) :
    ∃ c : ℂ, x - c • 1 ∈ vermaIdeal (rhoVec n) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  clear h
  have : ∃ c : ℂ, y = c • 1 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, hw0, rfl⟩ := hx
      exact ⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r * c, by rw [mul_smul]⟩
  obtain ⟨c, rfl⟩ := this
  exact ⟨c, by simpa using hw⟩

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `μ x hN hx h0`. Assume the negation of the conclusion as `hJ`.

Take `⟨m, hm, rfl⟩` from `exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)`. Use `ht_wt_nonpos hm` as an intermediate fact. Move the coercions through the operations in `at hN`. Use linear arithmetic over natural numbers and integers. Consider the case `succ N ih`.

Introduce `μ x hN hx h0`. Assume the negation of the conclusion as `hJ`. Take `⟨m, hm, rfl⟩` from `exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)`. Establish `hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n`. Introduce `a ha`.

Use `ih _ _ ?_ (hx.e_mul a) (by simp [h0])` and prove the remaining obligations. Rewrite using `[ht_add_rootAt, ht_rootAt]`. Establish `h1 : (a.1 : ℕ) < a.2` using `ha`. Move the coercions through the operations in `at hN`. Use linear arithmetic over natural numbers and integers.

Establish `hm0 : m = 0` using `GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij)) (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)`. Substitute `hm0` using the available equality. Establish `hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0` using `by ext k; simp [wt]`. Rewrite `hx` using `[hw0]`. Take `⟨c, hc⟩` from `mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)`.

Establish `h1` using `act_eq_zero_of_mem φ t hd hu hc`. Rewrite `h1` using `[map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one]`. Establish `hc0 : c = 0`. Assume the negation of the conclusion as `hne`. Simplify using `[hne, ht0] at h1`.

Rewrite `hc` using `[hc0, zero_smul, sub_zero]`. Conclude with `hJ (vermaIdeal_le_Jp hc)`.
-/
theorem mem_Jp_of_adW {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (ht0 : t ≠ 0)
    (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) :
    ∀ (N : ℕ) (μ : Fin n → ℤ) (x : U n), -ht μ < N → IsAdW μ x → φ x t = 0 → x ∈ Jp n := by
  intro N
  induction N with
  | zero =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have := ht_wt_nonpos hm
    push_cast at hN
    omega
  | succ N ih =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n := by
      intro a ha
      refine ih _ _ ?_ (hx.e_mul a) (by simp [h0])
      rw [ht_add_rootAt, ht_rootAt]
      have h1 : (a.1 : ℕ) < a.2 := ha
      push_cast at hN
      omega
    have hm0 : m = 0 := GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm
      (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij))
      (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)
    subst hm0
    have hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext k; simp [wt]
    rw [hw0] at hx
    obtain ⟨c, hc⟩ := mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)
    have h1 := act_eq_zero_of_mem φ t hd hu hc
    rw [map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one] at h1
    have hc0 : c = 0 := by
      by_contra hne
      simp [hne, ht0] at h1
    rw [hc0, zero_smul, sub_zero] at hc
    exact hJ (vermaIdeal_le_Jp hc)

/- English proof (translation)
Use `(Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, -, -, rfl⟩`. Conclude with `Submodule.subset_span ⟨m, hm, rfl⟩`.
-/
theorem word_mem_lowSpan {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, p.2 < p.1) :
    word l ∈ lowSpan n := by
  refine (Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact Submodule.subset_span ⟨m, hm, rfl⟩

/- English proof (translation)
Simplify using `[rhoV, rhoVec]`.
-/
theorem rho_cast (a : Fin n) : ((rhoV n a : ℝ) : ℂ) = rhoVec n a := by
  simp [rhoV, rhoVec]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, i, j, hij, rfl⟩` from `hx`. Simplify using `only [map_mul, map_pow, hφ, Module.End.mul_apply]`. Rewrite using `[hz i j hij, map_zero]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul r x _ hx => simp [hx]`.
-/
theorem act_eq_zero_of_sqSpan {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {F : Fin n → Fin n → Module.End ℂ Z} (φ : U n →ₐ[ℂ] Module.End ℂ Z)
    (hφ : ∀ i j, φ (e (i, j)) = F i j) (z : Z)
    (hz : ∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) {x : U n}
    (hx : x ∈ sqSpan n) : φ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    simp only [map_mul, map_pow, hφ, Module.End.mul_apply]
    rw [hz i j hij, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

/- English proof (translation)
Introduce `n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum`. Take `⟨φ, hφ⟩` from `exists_act G hG`. Take `⟨ψ, hψ⟩` from `exists_act F hF`. Establish `hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t` using `fun k => by`. Rewrite using `[hφ, hd, rho_cast]`.

Establish `hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0` using `fun a ha => by`. Rewrite using `[show e a = e (a.1, a.2) from rfl, hφ]`. Conclude with `hu _ _ ha`. Use `set Y : U n := ∑ l ∈ s, coef l • word l with hY`. Establish `hYlow : Y ∈ lowSpan n` using `Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))`.

Establish `hYt : φ Y t = 0`. Rewrite using `[hY, map_sum, LinearMap.sum_apply, ← hsum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, act_word φ hφ]`. Establish `hYJ : Y ∈ Jp n`.

Use `(Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)` and prove the remaining obligations. Introduce and unpack `y ⟨μ, hy, h0⟩`. Conclude with `mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0`. Establish `hYs` using `GlobalTheory.T.low_span_inf_ideal_le_square_span Y hYlow hYJ`. Establish `h` using `act_eq_zero_of_sqSpan ψ hψ z hz hYs`.

Rewrite `h` using `[hY, map_sum, LinearMap.sum_apply]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, act_word ψ hψ]`.
-/
theorem pres_rho : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  intro n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum
  obtain ⟨φ, hφ⟩ := exists_act G hG
  obtain ⟨ψ, hψ⟩ := exists_act F hF
  have hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t := fun k => by
    rw [hφ, hd, rho_cast]
  have hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0 := fun a ha => by
    rw [show e a = e (a.1, a.2) from rfl, hφ]; exact hu _ _ ha
  set Y : U n := ∑ l ∈ s, coef l • word l with hY
  have hYlow : Y ∈ lowSpan n :=
    Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))
  have hYt : φ Y t = 0 := by
    rw [hY, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, act_word φ hφ]
  have hYJ : Y ∈ Jp n := by
    refine (Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)
    rintro y ⟨μ, hy, h0⟩
    exact mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0
  have hYs := GlobalTheory.T.low_span_inf_ideal_le_square_span Y hYlow hYJ
  have h := act_eq_zero_of_sqSpan ψ hψ z hz hYs
  rw [hY, map_sum, LinearMap.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, act_word ψ hψ]

end GlobalTheory.CompanionTheory.PresRho
