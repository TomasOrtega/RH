import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNorm.FieldCase

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [Field K] [Algebra F K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR K e) = inclR K (σ e) := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e => simp [sigR, hσ]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (x : K ⊗[F] E) :
    sigR K σ (sigR K σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective`.
-/
theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) K) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, GlobalTheory.UTrans.hf, Matrix.transpose_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_eq_hf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → K ⊗[F] E) :
    hR K σ J x y = GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose y x := by
  simp only [hR, Formalism.UG.hform, GlobalTheory.UTrans.hf, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Alg

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm K _ _ M J hJ hunit hiso a b ha hb`. Establish `hinj` using `inclR_injective (F := F) (E := E) K`. Use `haveI : Nontrivial (K ⊗[F] E) := hinj.nontrivial`. Use `haveI : CharZero (K ⊗[F] E) := charZero_of_injective_algebraMap (algebraMap F (K ⊗[F] E)).injective`. Establish `hfield : IsField (K ⊗[F] E)` using `⟨exists_pair_ne _, mul_comm, fun {x} hx => (hunit x hx).exists_right_inv⟩`.

Use `letI : Field (K ⊗[F] E) := hfield.toField`. Establish `hG : GlobalTheory.UTrans.IsHerm (sigR K σ) (JR K J).transpose` using `{ invol := sigR_sigR K σ (GlobalTheory.HermLineZeros.conj_invol hcm) ne_id := by`. Take `⟨d, hd⟩` from `GlobalTheory.HermLineZeros.exists_conj_ne hcm`. Conclude with `⟨inclR K d, fun h => hd (hinj (by rw [← sigR_inclR]; exact h))⟩`. Use `herm := fun p q => by`.

Simplify using `only [Matrix.transpose_apply, JR, Matrix.map_apply, sigR_inclR]`. Rewrite using `[hJ.1 p q]`. Use `det_ne := by`. Rewrite using `[Matrix.det_transpose, JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Introduce `h`.

Conclude with `hJ.2 (hinj (by rw [h, map_zero])) }`. Establish `hsymm : ∀ x y, sigR K σ (hR K σ J x y) = hR K σ J y x`. Introduce `x y`. Rewrite using `[hR_eq_hf, hR_eq_hf, GlobalTheory.UTrans.IsoBasis.hf_symm hG]`. Take `⟨u, hu0, huu⟩` from `hiso`.

Establish `hz : ∃ z, z ≠ 0 ∧ GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose z z = 0` using `⟨u, hu0, by rw [← hR_eq_hf]; exact huu⟩`. Take `⟨e, he, hne⟩` from `GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid hG hz ![GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose a, GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose b] (by`. Introduce `i`. Use `fin_cases i`. Conclude with `GlobalTheory.UTrans.IsoBasis.hfL_ne hG ha`.

Conclude with `GlobalTheory.UTrans.IsoBasis.hfL_ne hG hb)`. Establish `hee : hR K σ J e e = 0` using `by rw [hR_eq_hf]; exact he`. Establish `h1 : hR K σ J a e ≠ 0`. Rewrite using `[hR_eq_hf]`. Conclude with `hne 0`.

Establish `h2 : hR K σ J e b ≠ 0`. Introduce `h`. Apply `hne 1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose e b = 0`. Rewrite using `[← hR_eq_hf, ← hsymm, h, map_zero]`.

Use `⟨e, ⟨hR K σ J a e, isUnit_iff_ne_zero.2 h1, ?_⟩, ⟨hR K σ J e b, isUnit_iff_ne_zero.2 h2, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hsymm, gram2R, hee]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsymm, gram2R, hee]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_unitNorm_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hJ hunit hiso a b ha hb
  have hinj := inclR_injective (F := F) (E := E) K
  haveI : Nontrivial (K ⊗[F] E) := hinj.nontrivial
  haveI : CharZero (K ⊗[F] E) := charZero_of_injective_algebraMap (algebraMap F (K ⊗[F] E)).injective
  have hfield : IsField (K ⊗[F] E) :=
    ⟨exists_pair_ne _, mul_comm, fun {x} hx => (hunit x hx).exists_right_inv⟩
  letI : Field (K ⊗[F] E) := hfield.toField
  have hG : GlobalTheory.UTrans.IsHerm (sigR K σ) (JR K J).transpose :=
    { invol := sigR_sigR K σ (GlobalTheory.HermLineZeros.conj_invol hcm)
      ne_id := by
        obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
        exact ⟨inclR K d, fun h => hd (hinj (by rw [← sigR_inclR]; exact h))⟩
      herm := fun p q => by
        simp only [Matrix.transpose_apply, JR, Matrix.map_apply, sigR_inclR]
        rw [hJ.1 p q]
      det_ne := by
        rw [Matrix.det_transpose, JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        intro h
        exact hJ.2 (hinj (by rw [h, map_zero])) }
  have hsymm : ∀ x y, sigR K σ (hR K σ J x y) = hR K σ J y x := by
    intro x y
    rw [hR_eq_hf, hR_eq_hf, GlobalTheory.UTrans.IsoBasis.hf_symm hG]
  obtain ⟨u, hu0, huu⟩ := hiso
  have hz : ∃ z, z ≠ 0 ∧ GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose z z = 0 := ⟨u, hu0, by rw [← hR_eq_hf]; exact huu⟩
  obtain ⟨e, he, hne⟩ := GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid hG hz
    ![GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose a, GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose b] (by
      intro i
      fin_cases i
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG ha
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG hb)
  have hee : hR K σ J e e = 0 := by rw [hR_eq_hf]; exact he
  have h1 : hR K σ J a e ≠ 0 := by
    rw [hR_eq_hf]; exact hne 0
  have h2 : hR K σ J e b ≠ 0 := by
    intro h
    apply hne 1
    change GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose e b = 0
    rw [← hR_eq_hf, ← hsymm, h, map_zero]
  refine ⟨e, ⟨hR K σ J a e, isUnit_iff_ne_zero.2 h1, ?_⟩, ⟨hR K σ J e b, isUnit_iff_ne_zero.2 h2, ?_⟩⟩
  · rw [hsymm, gram2R, hee]; ring
  · rw [hsymm, gram2R, hee]; ring

end GlobalTheory.PlaneNorm.FieldCase
