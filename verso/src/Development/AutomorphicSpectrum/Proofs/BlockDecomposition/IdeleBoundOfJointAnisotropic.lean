import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.FormHeight

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

section Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ}

/- English proof (translation)
Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigR_conj (R : Type) [CommRing R] [Algebra F R] :
    sigR R (conj F E).toAlgHom = conjBase F E R := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Rewrite using `[hR, sigR_conj]`. Simplify using `only [hermValue, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Both sides reduce to the same expression.
-/
theorem hermValue_eq_hR (R : Type) [CommRing R] [Algebra F R] (H : Matrix (Fin n) (Fin n) E)
    (x : Fin n → R ⊗[F] E) : hermValue F H R x = hR R (conj F E).toAlgHom H x x := by
  rw [hR, sigR_conj]
  simp only [hermValue, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  rfl

/- English proof (translation)
Establish `e : algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F` using `F) (AF F) z = s • ((1 : AF F) ⊗ₜ[F] z) := by`. Simplify using `[inclR, Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']`. Rewrite using `[e, map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `[coords, Reduction.ratVec, Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem coords_algebraMap_mul_inclR (s : AF F) (z : E) :
    coords (Module.finBasis F E) (AF F)
        (algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z) =
      s • Reduction.ratVec (fun k => (Module.finBasis F E).repr z k) := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z = s • ((1 : AF F) ⊗ₜ[F] z) := by
    simp [inclR, Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
  rw [e, map_smul]
  congr 1
  funext k
  simp [coords, Reduction.ratVec, Algebra.TensorProduct.basis_repr_tmul]

/- English proof (translation)
The claim follows from `exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos (hermPoly H (Module.finBasis F E)) (fun v t y k => by rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul] rfl) (fun w t y k => by rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul] rfl)`.
-/
theorem exists_adelicNorm_hermPoly_le (H : Matrix (Fin n) (Fin n) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2 :=
  exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos (hermPoly H (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)

/- English proof (translation)
Use `set b := Module.finBasis F E with hb`. Use `set v := (matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ with hv`. Use `set y : Fin (Bridge.dimN F E n) → AF F := resVec (ι := Fin n) b (AF F) v with hy`. Establish `ey : Reduction.ratVec (Bridge.cvec F ξ) ᵥ* (Bridge.trG (conj F E).toAlgHom J g : Matrix _ _ (AF F)) = y`. Rewrite using `[Bridge.ratVec_cvec, Bridge.trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hy, hv, map_inv]`.

Establish `hfy : Reduction.HasFiniteContent y`. Rewrite using `[← ey]`. Conclude with `Reduction.hasFiniteContent_height _ (Bridge.cvec_ne_zero hξ)`. Establish `hz' : (fun k => b.repr z k) ≠ 0`. Introduce `h0`.

Apply `hz` to reduce the goal to its premises. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Simplify using `using congrFun h0 k`. Establish `e : (fun k => MvPolynomial.aeval y (hermPoly H b k)) = (s : AF F) • Reduction.ratVec (fun k => b.repr z k)`.

Use function extensionality and compare the values at `k`. Rewrite using `[aeval_hermPoly, hermCoords, hy, ofResVec_resVec, hermValue_eq_hR, he, coords_algebraMap_mul_inclR]`. Establish `hfz : Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (hermPoly H b k))`. Rewrite using `[e]`. Conclude with `(Reduction.hasFiniteContent_ratVec hz').smul s`.

Establish `h1 : 1 ≤ Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H b k))`. Rewrite using `[e, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz')]`. Conclude with `one_le_mul_of_one_le_of_one_le hs (Reduction.one_le_adelicNorm_ratVec hz')`. Conclude with `h1.trans (hCb y hfy hfz)`.
-/
theorem one_le_mul_hgt_sq (J H : Matrix (Fin n) (Fin n) E) {C : ℝ}
    (hCb : ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2)
    (g : GAd (conj F E).toAlgHom J) {ξ : Fin n → E} (hξ : ξ ≠ 0)
    (s : GroundTheory.Global.IdeleGroup F) (hs : 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ))
    {z : E} (hz : z ≠ 0)
    (he : hR (AF F) (conj F E).toAlgHom H
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ)
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ) =
      algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) z) :
    1 ≤ C * hgt (conj F E).toAlgHom J g ξ ^ 2 := by
  set b := Module.finBasis F E with hb
  set v := (matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ with hv
  set y : Fin (Bridge.dimN F E n) → AF F := resVec (ι := Fin n) b (AF F) v with hy
  have ey : Reduction.ratVec (Bridge.cvec F ξ) ᵥ*
      (Bridge.trG (conj F E).toAlgHom J g : Matrix _ _ (AF F)) = y := by
    rw [Bridge.ratVec_cvec, Bridge.trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hy, hv, map_inv]
  have hfy : Reduction.HasFiniteContent y := by
    rw [← ey]
    exact Reduction.hasFiniteContent_height _ (Bridge.cvec_ne_zero hξ)
  have hz' : (fun k => b.repr z k) ≠ 0 := by
    intro h0
    apply hz
    apply b.repr.injective
    ext k
    simpa using congrFun h0 k
  have e : (fun k => MvPolynomial.aeval y (hermPoly H b k)) =
      (s : AF F) • Reduction.ratVec (fun k => b.repr z k) := by
    funext k
    rw [aeval_hermPoly, hermCoords, hy, ofResVec_resVec, hermValue_eq_hR, he,
      coords_algebraMap_mul_inclR]
  have hfz : Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e]
    exact (Reduction.hasFiniteContent_ratVec hz').smul s
  have h1 : 1 ≤ Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz')]
    exact one_le_mul_of_one_le_of_one_le hs (Reduction.one_le_adelicNorm_ratVec hz')
  exact h1.trans (hCb y hfy hfz)

end Forms

/- English proof (translation)
Distinguish the cases in `h1 : 1 ≤ t`. Conclude with `(min_le_left _ _).trans h1`. Use `replace h1 := not_le.1 h1`. Establish `h3 : 1 ≤ D * t`. Use `h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities. Use `(min_le_right _ _).trans ?_` and prove the remaining obligations. Rewrite using `[inv_le_iff_one_le_mul₀ hD, mul_comm]`. Conclude with `h3`.
-/
theorem min_le_of_one_le_mul_sq {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) (h : 1 ≤ D * t ^ 2) :
    min 1 D⁻¹ ≤ t := by
  by_cases h1 : 1 ≤ t
  · exact (min_le_left _ _).trans h1
  · replace h1 := not_le.1 h1
    have h3 : 1 ≤ D * t := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
      nlinarith
    refine (min_le_right _ _).trans ?_
    rw [inv_le_iff_one_le_mul₀ hD, mul_comm]
    exact h3

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J _ M _ H L hzero hL`. Take `⟨hF, hEc, h2, hc⟩` from `hCM`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Take `rfl : σ = (conj F E).toAlgHom` from `AlgHom.ext fun x => τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)`.

Consider the cases of `nonempty_fintype M`. Use `choose C hC hCb using fun j => exists_adelicNorm_hermPoly_le (F := F) (H j)`. Establish `hsum : 0 ≤ ∑ j, C j` using `Finset.sum_nonneg fun j _ => (hC j).le`. Establish `hD : 0 < 1 + ∑ j, C j` using `by linarith`. Use `⟨min 1 (1 + ∑ j, C j)⁻¹, lt_min one_pos (inv_pos.2 hD), fun g hg ξ hξ => ?_⟩` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, hE (conj F E).toAlgHom (H j) ξ ξ ≠ 0 := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hξ (hzero ξ hno)`. Take `⟨s, hs, he⟩` from `hL g hg j`.

Establish `h1` using `one_le_mul_hgt_sq J (H j) (hCb j) g hξ s hs hj (he ξ)`. Establish `ht : 0 ≤ hgt (conj F E).toAlgHom J g ξ` using `Reduction.adelicNorm_nonneg _`. Establish `hle : C j ≤ 1 + ∑ j, C j`. Use `Finset.single_le_sum (f := C) (fun i _ => (hC i).le) (Finset.mem_univ j)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `min_le_of_one_le_mul_sq hD ht (h1.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)))`.
-/
theorem exists_pos_le_hgt_of_forms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  intro F E _ _ _ _ _ σ hCM n J _ M _ H L hzero hL
  obtain ⟨hF, hEc, h2, hc⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  cases nonempty_fintype M
  choose C hC hCb using fun j => exists_adelicNorm_hermPoly_le (F := F) (H j)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hD : 0 < 1 + ∑ j, C j := by linarith
  refine ⟨min 1 (1 + ∑ j, C j)⁻¹, lt_min one_pos (inv_pos.2 hD), fun g hg ξ hξ => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, hE (conj F E).toAlgHom (H j) ξ ξ ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (hzero ξ hno)
  obtain ⟨s, hs, he⟩ := hL g hg j
  have h1 := one_le_mul_hgt_sq J (H j) (hCb j) g hξ s hs hj (he ξ)
  have ht : 0 ≤ hgt (conj F E).toAlgHom J g ξ := Reduction.adelicNorm_nonneg _
  have hle : C j ≤ 1 + ∑ j, C j := by
    have := Finset.single_le_sum (f := C) (fun i _ => (hC i).le) (Finset.mem_univ j)
    linarith
  exact min_le_of_one_le_mul_sq hD ht
    (h1.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)))

end GlobalTheory.CompanionTheory.ParCocompact.FormHeight

end
