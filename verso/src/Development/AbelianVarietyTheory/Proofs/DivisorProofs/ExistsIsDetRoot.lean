import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDeterminantCongruentElement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetOnto

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y h`. Take `⟨a, ha, x, rfl⟩` from `h`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig x, (x.2 : IsIntegral ℤ (x : D.host.E)).map D.sp.cm.sig.toRingHom.toIntAlgHom⟩, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`.
-/
theorem sigR_mem_intAE (D : D7) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha,
      ⟨D.sp.cm.sig x, (x.2 : IsIntegral ℤ (x : D.host.E)).map D.sp.cm.sig.toRingHom.toIntAlgHom⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem sigR_sigR (D : D7) (a : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Apply `e.injective` to reduce the goal to its premises. Conclude with `Prod.ext ((he a).1.trans (h1.trans (he b).1.symm)) ((he a).2.trans (h2.trans (he b).2.symm))`.
-/
theorem ext_parts (D : D7) {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  exact Prod.ext ((he a).1.trans (h1.trans (he b).1.symm)) ((he a).2.trans (h2.trans (he b).2.symm))

/- English proof (translation)
Establish `h'` using `congrArg σ h`. Rewrite `h'` using `[map_mul, map_one]`. Rewrite using `[map_mul, hσ]`. Take the linear combination `(σ a * σ b) * h + h'`.
-/
theorem norm_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {a b : R} (h : a * b = 1) :
    a * σ b * σ (a * σ b) = 1 := by
  have h' := congrArg σ h
  rw [map_mul, map_one] at h'
  rw [map_mul, hσ]
  linear_combination (σ a * σ b) * h + h'

/- English proof (translation)
Establish `h : infHom V k = 1` using `hk`. Establish `h' : (infHom V k).1.det = infPart D (matHom V k).1.det` using `((infPart D).map_det _).symm`. Rewrite using `[← h', h, Units.val_one, Matrix.det_one]`.
-/
theorem infPart_det {D : D7} (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) : infPart D (matHom V k).1.det = 1 := by
  have h : infHom V k = 1 := hk
  have h' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  rw [← h', h, Units.val_one, Matrix.det_one]

/- English proof (translation)
The claim follows from `GlobalTheory.DetRootCong.map_sigR _ _ x`.
-/
theorem infPart_sigR (D : D7) (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) :=
  GlobalTheory.DetRootCong.map_sigR _ _ x

/- English proof (translation)
The claim follows from `(finPart D).map_det _`.
-/
theorem finPart_det {D : D7} (V : HSp D) (k : GA D V) : finPart D (matHom V k).1.det = (finHom V k).1.det :=
  (finPart D).map_det _

end GlobalTheory.DetOnto
