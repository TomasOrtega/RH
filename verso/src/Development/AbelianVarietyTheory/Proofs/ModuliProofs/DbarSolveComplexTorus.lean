import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvableStatement
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Use `haveI : IsZLattice ℝ Λ := ⟨hΛ⟩`. Set `b0` to `Module.finBasis ℤ Λ`. Set `b` to `b0.ofZLatticeBasis ℝ Λ`. Use `⟨_, b.equivFunL.symm, ?_, ?_⟩` and prove the remaining obligations. Introduce `ν`.

Establish `: b.equivFunL.symm (fun k => (ν k : ℝ)) = ∑ k, (ν k : ℝ) • b k` using `b.equivFun_symm_apply _`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Simplify using `[b]`. Introduce `l`. Use `⟨fun k => b0.repr l k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b0 l k` as an intermediate fact.

Simplify `this` using `[b]`.
-/
theorem exists_equiv_latticeCoords (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)),
      (∀ ν : Fin n → ℤ, T (fun k => (ν k : ℝ)) ∈ Λ) ∧
      ∀ l : Λ, ∃ ν : Fin n → ℤ, T.symm l = fun k => (ν k : ℝ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b0 := Module.finBasis ℤ Λ
  let b := b0.ofZLatticeBasis ℝ Λ
  refine ⟨_, b.equivFunL.symm, ?_, ?_⟩
  · intro ν
    have : b.equivFunL.symm (fun k => (ν k : ℝ)) = ∑ k, (ν k : ℝ) • b k :=
      b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    refine Submodule.smul_mem _ _ ?_
    simp [b]
  · intro l
    refine ⟨fun k => b0.repr l k, ?_⟩
    funext k
    have := Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b0 l k
    simpa [b] using this

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single u]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: (Pi.single k (u k) : Fin n → ℝ) = u k • (Pi.single k 1 : Fin n → ℝ)`. Rewrite using `[← Pi.single_smul]`.

Simplify using the standard rewrite rules. Rewrite using `[this, map_smul]`. Simplify using the standard rewrite rules.
-/
theorem realLinear_eq_sum_single {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℂ) (u : Fin n → ℝ) :
    L u = ∑ k, (u k : ℂ) * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (u k) : Fin n → ℝ) = u k • (Pi.single k 1 : Fin n → ℝ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul]; simp

/- English proof (translation)
Establish `e : ∀ y, fderiv ℝ h (T x) y = fderiv ℝ (h ∘ T) x (T.symm y)`. Introduce `y`. Rewrite using `[ContinuousLinearEquiv.comp_right_fderiv]`. Simplify using the standard rewrite rules. Rewrite using `[e u, e v, realLinear_eq_sum_single _ (T.symm u), realLinear_eq_sum_single _ (T.symm v), Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dbar_comp_equiv {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (h : (Fin g → ℂ) → ℂ)
    (x : Fin n → ℝ) (u v : Fin g → ℂ) :
    ∑ k, ((T.symm u k : ℂ) + I * (T.symm v k : ℂ)) * fderiv ℝ (h ∘ T) x (Pi.single k 1) =
      fderiv ℝ h (T x) u + I * fderiv ℝ h (T x) v := by
  have e : ∀ y, fderiv ℝ h (T x) y = fderiv ℝ (h ∘ T) x (T.symm y) := by
    intro y
    rw [ContinuousLinearEquiv.comp_right_fderiv]; simp
  rw [e u, e v, realLinear_eq_sum_single _ (T.symm u), realLinear_eq_sum_single _ (T.symm v),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Establish `h1 : ∀ a, T.symm (Pi.single a 1) ⬝ᵥ ξ = 0` using `fun a => by`. Use `congrArg Complex.re (h a)` as an intermediate fact. Simplify `this` using `[Complex.re_sum, dotProduct]`. Establish `h2 : ∀ a, T.symm (I • (Pi.single a 1 : Fin g → ℂ)) ⬝ᵥ ξ = 0` using `fun a => by`. Use `congrArg Complex.im (h a)` as an intermediate fact.

Simplify `this` using `[Complex.im_sum, dotProduct]`. Establish `h3 : ∀ z : Fin g → ℂ, T.symm z ⬝ᵥ ξ = 0` using `fun z => by`. Establish `hz : z = ∑ a, ((z a).re • (Pi.single a 1 : Fin g → ℂ) + (z a).im • (I • (Pi.single a 1 : Fin g → ℂ)))` using `by conv_lhs => rw [← Finset.univ_sum_single z]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `c`.

Distinguish the cases in `hc : c = a`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hc]`. Rewrite using `[hz, map_sum, sum_dotProduct]`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]`. Simplify using the standard rewrite rules. Use `h3 (T ξ)` as an intermediate fact. Rewrite `this` using `[T.symm_apply_apply]`.

Conclude with `dotProduct_self_eq_zero.mp this`.
-/
theorem dbar_symbol_elliptic {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (ξ : Fin n → ℝ)
    (h : ∀ a, ∑ k, ((T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ)) * (ξ k : ℂ) = 0) : ξ = 0 := by
  have h1 : ∀ a, T.symm (Pi.single a 1) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.re (h a)
    simpa [Complex.re_sum, dotProduct] using this
  have h2 : ∀ a, T.symm (I • (Pi.single a 1 : Fin g → ℂ)) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.im (h a)
    simpa [Complex.im_sum, dotProduct] using this
  have h3 : ∀ z : Fin g → ℂ, T.symm z ⬝ᵥ ξ = 0 := fun z => by
    have hz : z = ∑ a, ((z a).re • (Pi.single a 1 : Fin g → ℂ) +
        (z a).im • (I • (Pi.single a 1 : Fin g → ℂ))) := by
      conv_lhs => rw [← Finset.univ_sum_single z]
      refine Finset.sum_congr rfl fun a _ => ?_
      funext c
      by_cases hc : c = a
      · subst hc; simp
      · simp [hc]
    rw [hz, map_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_add, map_smul, map_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]
    simp
  have := h3 (T ξ)
  rw [T.symm_apply_apply] at this
  exact dotProduct_self_eq_zero.mp this

/- English proof (translation)
Introduce `g Λ hd hΛ w hw hc`. Take `⟨n, T, hT1, hT2⟩` from `exists_equiv_latticeCoords g Λ hΛ`. Take `⟨t, f, hf, hper, heq⟩` from `GlobalTheory.T.exists_periodic_smooth_solution_torus_system n g (fun a k => (T.symm (Pi.single a 1) k : ℂ) + I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ)) (dbar_symbol_elliptic T) (fun a => w a ∘ T) (fun a => ⟨(hw a).1.comp T.contDiff, fun ν x => by`. Simplify using `only [Function.comp, map_add]`. Conclude with `(hw a).2 ⟨_, hT1 ν⟩ _⟩)`.

Use the proof step `(fun a b x => by`. Rewrite using `[dbar_comp_equiv, dbar_comp_equiv]`. Conclude with `hc a b _)`. Use `⟨t, f ∘ T.symm, hf.comp T.symm.contDiff, fun l z => ?_, fun a z => ?_⟩` and prove the remaining obligations. Take `⟨ν, hν⟩` from `hT2 l`.

Simplify using `only [Function.comp, map_add, hν]`. Conclude with `hper ν _`. Establish `h1` using `dbar_comp_equiv T (f ∘ T.symm) (T.symm z) (Pi.single a 1) (I • (Pi.single a 1 : Fin g → ℂ))`. Establish `h2 : (f ∘ T.symm) ∘ T = f` using `by funext y; simp`. Rewrite `h1` using `[h2, T.apply_symm_apply]`.

Rewrite using `[← h1, heq a]`. Simplify using the standard rewrite rules.
-/
theorem dbar_solve_complexTorus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ w : Fin g → (Fin g → ℂ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ ∀ (l : Λ) z, w a (z + l) = w a z) → (∀ a b z, (fderiv ℝ (w b) z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ (w b) z (I • (Pi.single a 1 : Fin g → ℂ))) = (fderiv ℝ (w a) z (Pi.single b 1 : Fin g → ℂ) + I * fderiv ℝ (w a) z (I • (Pi.single b 1 : Fin g → ℂ)))) → ∃ (t : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (l : Λ) z, f (z + l) = f z) ∧ ∀ a z, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = w a z - t a := by
  intro g Λ hd hΛ w hw hc
  obtain ⟨n, T, hT1, hT2⟩ := exists_equiv_latticeCoords g Λ hΛ
  obtain ⟨t, f, hf, hper, heq⟩ := GlobalTheory.T.exists_periodic_smooth_solution_torus_system n g
    (fun a k => (T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ))
    (dbar_symbol_elliptic T) (fun a => w a ∘ T)
    (fun a => ⟨(hw a).1.comp T.contDiff, fun ν x => by
      simp only [Function.comp, map_add]
      exact (hw a).2 ⟨_, hT1 ν⟩ _⟩)
    (fun a b x => by
      rw [dbar_comp_equiv, dbar_comp_equiv]
      exact hc a b _)
  refine ⟨t, f ∘ T.symm, hf.comp T.symm.contDiff, fun l z => ?_, fun a z => ?_⟩
  · obtain ⟨ν, hν⟩ := hT2 l
    simp only [Function.comp, map_add, hν]
    exact hper ν _
  · have h1 := dbar_comp_equiv T (f ∘ T.symm) (T.symm z) (Pi.single a 1)
      (I • (Pi.single a 1 : Fin g → ℂ))
    have h2 : (f ∘ T.symm) ∘ T = f := by funext y; simp
    rw [h2, T.apply_symm_apply] at h1
    rw [← h1, heq a]
    simp

end GlobalTheory
