import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.HermForm

section Ring

variable {A : Type} [CommRing A] (c : A →+* A) {n : ℕ} (M : Matrix (Fin n) (Fin n) A)

/- English proof (translation)
Use `⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Simplify using `only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Formalism.UG.hform, map_sum, map_mul, hc]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHerm_hform (hc : ∀ a, c (c a) = a) (hM : ∀ i j, c (M j i) = M i j) :
    IsHerm c (Formalism.UG.hform c M) := by
  refine ⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_⟩
  · simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [Formalism.UG.hform, map_sum, map_mul, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
    ring

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem hform_eq_dotProduct (x y : Fin n → A) :
    Formalism.UG.hform c M x y = ((fun i => c (x i)) ᵥ* M) ⬝ᵥ y := by
  simp only [Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use `⟨fun x hx => ?_, fun f => ?_⟩` and prove the remaining obligations. Establish `hv : (fun i => c (x i)) ᵥ* M = 0`. Use function extensionality and compare the values at `j`. Establish `h1` using `hx (Pi.single j 1)`. Rewrite `h1` using `[hform_eq_dotProduct]`.

Simplify using `using h1`. Establish `h0 : (fun i => c (x i)) = 0`. Establish `h2` using `congrArg (fun v => v ᵥ* M⁻¹) hv`. Simplify `h2` using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM]`. Use function extensionality and compare the values at `i`.

Establish `h3 : c (x i) = 0` using `by simpa using congrFun h0 i`. Establish `h4` using `hc (x i)`. Rewrite `h4` using `[h3, map_zero]`. Simplify using `using h4.symm`. Use `⟨fun i => c (((fun k => f (fun j => if k = j then 1 else 0)) ᵥ* M⁻¹) i), fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hform_eq_dotProduct]`. Simplify using `only [hc]`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hM, Matrix.vecMul_one]`. Use `conv_rhs => rw [pi_eq_sum_univ y]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, smul_eq_mul, dotProduct]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem isPerfect_hform (hc : ∀ a, c (c a) = a) (hM : IsUnit M.det) :
    IsPerfect (Formalism.UG.hform c M) := by
  refine ⟨fun x hx => ?_, fun f => ?_⟩
  · have hv : (fun i => c (x i)) ᵥ* M = 0 := by
      funext j
      have h1 := hx (Pi.single j 1)
      rw [hform_eq_dotProduct] at h1
      simpa using h1
    have h0 : (fun i => c (x i)) = 0 := by
      have h2 := congrArg (fun v => v ᵥ* M⁻¹) hv
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM] using h2
    funext i
    have h3 : c (x i) = 0 := by simpa using congrFun h0 i
    have h4 := hc (x i)
    rw [h3, map_zero] at h4
    simpa using h4.symm
  · refine ⟨fun i => c (((fun k => f (fun j => if k = j then 1 else 0)) ᵥ* M⁻¹) i), fun y => ?_⟩
    rw [hform_eq_dotProduct]
    simp only [hc]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hM, Matrix.vecMul_one]
    conv_rhs => rw [pi_eq_sum_univ y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Ring

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
theorem sigR_inclR (a : E) : sigR R σ (inclR (F := F) R a) = inclR (F := F) R (σ a) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem sigR_sigR_of_invol (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) : sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `h1 : (JR (F` using `F) R J).det = inclR (F := F) R J.det := by`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `(isUnit_iff_ne_zero.mpr h).map _`.
-/
theorem isUnit_det_JR (h : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by
  have h1 : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr h).map _

end Tensor

end GlobalTheory.CompanionTheory.KFin.HermForm

namespace GlobalTheory.CompanionTheory.KFin

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hCM hJ v`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hinv : ∀ x : E, σ (σ x) = x`. Introduce `x`. Apply `(w.embedding).injective` to reduce the goal to its premises.

Rewrite using `[hCM.2.2.2, hCM.2.2.2]`. Conclude with `star_star _`. Establish `hc : ∀ a, sigR (Fv F v) σ (sigR (Fv F v) σ a) = a` using `HermForm.sigR_sigR_of_invol (Fv F v) σ hinv`. Establish `hM : ∀ i j, sigR (Fv F v) σ (JR (F` using `F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by`. Introduce `i j`.

Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]`. Rewrite using `[HermForm.sigR_inclR, hJ.1]`. Conclude with `⟨HermForm.isHerm_hform _ _ hc hM, HermForm.isPerfect_hform _ _ hc (HermForm.isUnit_det_JR (F := F) (Fv F v) J hJ.2)⟩`.
-/
theorem isHerm_isPerfect_hR : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHerm (sigR (Fv F v) σ) (hR (Fv F v) σ J) ∧ IsPerfect (hR (Fv F v) σ J) := by
  intro F E _ _ _ _ _ σ n J hCM hJ v
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    apply (w.embedding).injective
    rw [hCM.2.2.2, hCM.2.2.2]
    exact star_star _
  have hc : ∀ a, sigR (Fv F v) σ (sigR (Fv F v) σ a) = a :=
    HermForm.sigR_sigR_of_invol (Fv F v) σ hinv
  have hM : ∀ i j, sigR (Fv F v) σ (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
    intro i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    rw [HermForm.sigR_inclR, hJ.1]
  exact ⟨HermForm.isHerm_hform _ _ hc hM,
    HermForm.isPerfect_hform _ _ hc (HermForm.isUnit_det_JR (F := F) (Fv F v) J hJ.2)⟩

end GlobalTheory.CompanionTheory.KFin

end
