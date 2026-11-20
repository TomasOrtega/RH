import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramesFGP

/- English proof (translation)
Use `haveI : F.IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames h`. Use `choose U n e hx he using h`. Establish `hU` using `isAffineOpen_top (Sp O)`. Set `s : Set Γ(Sp O, ⊤)` to `{f | ∃ x, (Sp O).basicOpen f ≤ U x}`. Establish `hs : Ideal.span s = ⊤`.

Rewrite using `[← hU.self_le_iSup_basicOpen_iff]`. Introduce `y _`. Take `⟨f, hf, hyf⟩` from `hU.exists_basicOpen_le (V := U y) ⟨y, hx y⟩ (by simp)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, y, hf⟩, hyf⟩`. Use `haveI (g : s) := hU.isLocalization_basicOpen g.1`.

Use `haveI (g : s) := GlobalTheory.QCoh.isLocalizedModule_resBasicOpen F hU g.1`. Set `b (g : s) : Module.Basis (Fin (n g.2.choose)) Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1)` to `(he g.2.choose).basis g.2.choose_spec`. Use `haveI (g : s) : Module.Free Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) := .of_basis (b g)`. Use `haveI (g : s) : Module.Finite Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) := .of_basis (b g)`. Use `haveI (g : s) : Module.Flat Γ(Sp O, ⊤) Γ(F, (Sp O).basicOpen g.1) := by haveI : Module.Flat Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) := IsLocalization.flat _ (Submonoid.powers g.1)`.

Conclude with `Module.Flat.trans Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) _`. Use `haveI hfp : Module.FinitePresentation Γ(Sp O, ⊤) Γ(F, ⊤) := Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := fun g : s => Γ(F, (Sp O).basicOpen g.1)) (Rₚ := fun g : s => Γ(Sp O, (Sp O).basicOpen g.1)) (fun g => GlobalTheory.QCoh.resBasicOpen F g.1) fun _ => Module.finit …`. Use `haveI : Module.Flat Γ(Sp O, ⊤) Γ(F, ⊤) := Module.flat_of_isLocalized_span Γ(Sp O, ⊤) Γ(F, ⊤) s hs (fun g : s => Γ(F, (Sp O).basicOpen g.1)) (fun g => GlobalTheory.QCoh.resBasicOpen F g.1) fun _ => inferInstance`. Conclude with `⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩`.
-/
theorem finite_projective_top {O : Type} [CommRing O] (F : (Sp O).Modules)
    (h : ∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(F, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) :
    Module.Finite Γ(Sp O, ⊤) Γ(F, ⊤) ∧ Module.Projective Γ(Sp O, ⊤) Γ(F, ⊤) := by
  haveI : F.IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames h
  choose U n e hx he using h
  have hU := isAffineOpen_top (Sp O)
  let s : Set Γ(Sp O, ⊤) := {f | ∃ x, (Sp O).basicOpen f ≤ U x}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro y _
    obtain ⟨f, hf, hyf⟩ := hU.exists_basicOpen_le (V := U y) ⟨y, hx y⟩ (by simp)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, y, hf⟩, hyf⟩
  haveI (g : s) := hU.isLocalization_basicOpen g.1
  haveI (g : s) := GlobalTheory.QCoh.isLocalizedModule_resBasicOpen F hU g.1
  let b (g : s) : Module.Basis (Fin (n g.2.choose)) Γ(Sp O, (Sp O).basicOpen g.1)
      Γ(F, (Sp O).basicOpen g.1) := (he g.2.choose).basis g.2.choose_spec
  haveI (g : s) : Module.Free Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Finite Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Flat Γ(Sp O, ⊤) Γ(F, (Sp O).basicOpen g.1) := by
    haveI : Module.Flat Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) _
  haveI hfp : Module.FinitePresentation Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Mₚ := fun g : s => Γ(F, (Sp O).basicOpen g.1))
      (Rₚ := fun g : s => Γ(Sp O, (Sp O).basicOpen g.1))
      (fun g => GlobalTheory.QCoh.resBasicOpen F g.1) fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.flat_of_isLocalized_span Γ(Sp O, ⊤) Γ(F, ⊤) s hs
      (fun g : s => Γ(F, (Sp O).basicOpen g.1)) (fun g => GlobalTheory.QCoh.resBasicOpen F g.1)
      fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.FramesFGP

/- English proof (translation)
Introduce `O _ A _ h`. Take `⟨h1, h2⟩` from `GlobalTheory.FramesFGP.finite_projective_top (GlobalTheory.LieVB.omega A) h`. Use `letI : Module Γ(Sp O, ⊤) (Wmod A) := inferInstanceAs (Module Γ(Sp O, ⊤) Γ(GlobalTheory.LieVB.omega A, ⊤))`. Use `haveI : Module.Finite Γ(Sp O, ⊤) (Wmod A) := h1`. Use `haveI : Module.Projective Γ(Sp O, ⊤) (Wmod A) := h2`.

Establish `hb : Function.Bijective (GlobalTheory.LieVB.cst O)` using `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv`. Set `E : O ≃+* Γ(Sp O, ⊤)` to `RingEquiv.ofBijective (GlobalTheory.LieVB.cst O) hb`. Use `letI : Algebra O Γ(Sp O, ⊤) := (GlobalTheory.LieVB.cst O).toAlgebra`. Use `haveI : IsScalarTower O Γ(Sp O, ⊤) (Wmod A) := .of_algebraMap_smul fun _ _ => rfl`. Use `haveI : Module.Finite O Γ(Sp O, ⊤) := Module.Finite.of_surjective (Algebra.linearMap O Γ(Sp O, ⊤)) hb.2`.

Use `⟨Module.Finite.trans Γ(Sp O, ⊤) (Wmod A), ?_⟩` and prove the remaining obligations. Use `haveI : RingHomInvPair (E.symm : Γ(Sp O, ⊤) →+* O) (E : O →+* Γ(Sp O, ⊤)) := ⟨RingHom.ext E.apply_symm_apply, RingHom.ext E.symm_apply_apply⟩`. Use `haveI : RingHomInvPair (E : O →+* Γ(Sp O, ⊤)) (E.symm : Γ(Sp O, ⊤) →+* O) := .symm _ _`. Set `e : Wmod A ≃ₛₗ[(E.symm : Γ(Sp O, ⊤) →+* O)] Wmod A` to `{ toFun := id invFun := id map_add' := fun _ _ => rfl map_smul' := fun r m => by`. Express the relevant statement in the definitionally equal form `r • m = GlobalTheory.LieVB.cst O (E.symm r) • m`.

Use `congr 1`. Conclude with `(E.apply_symm_apply r).symm`. Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`. Conclude with `Module.Projective.of_equiv e`.
-/
theorem GlobalTheory.FramesFGP.finite_projective_wmod : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) → Module.Finite O (Wmod A) ∧ Module.Projective O (Wmod A) := by
  intro O _ A _ h
  obtain ⟨h1, h2⟩ := GlobalTheory.FramesFGP.finite_projective_top (GlobalTheory.LieVB.omega A) h
  letI : Module Γ(Sp O, ⊤) (Wmod A) := inferInstanceAs (Module Γ(Sp O, ⊤) Γ(GlobalTheory.LieVB.omega A, ⊤))
  haveI : Module.Finite Γ(Sp O, ⊤) (Wmod A) := h1
  haveI : Module.Projective Γ(Sp O, ⊤) (Wmod A) := h2
  have hb : Function.Bijective (GlobalTheory.LieVB.cst O) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv
  let E : O ≃+* Γ(Sp O, ⊤) := RingEquiv.ofBijective (GlobalTheory.LieVB.cst O) hb
  letI : Algebra O Γ(Sp O, ⊤) := (GlobalTheory.LieVB.cst O).toAlgebra
  haveI : IsScalarTower O Γ(Sp O, ⊤) (Wmod A) := .of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O Γ(Sp O, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap O Γ(Sp O, ⊤)) hb.2
  refine ⟨Module.Finite.trans Γ(Sp O, ⊤) (Wmod A), ?_⟩
  haveI : RingHomInvPair (E.symm : Γ(Sp O, ⊤) →+* O) (E : O →+* Γ(Sp O, ⊤)) :=
    ⟨RingHom.ext E.apply_symm_apply, RingHom.ext E.symm_apply_apply⟩
  haveI : RingHomInvPair (E : O →+* Γ(Sp O, ⊤)) (E.symm : Γ(Sp O, ⊤) →+* O) := .symm _ _
  let e : Wmod A ≃ₛₗ[(E.symm : Γ(Sp O, ⊤) →+* O)] Wmod A :=
    { toFun := id
      invFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = GlobalTheory.LieVB.cst O (E.symm r) • m
        congr 1
        exact (E.apply_symm_apply r).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Projective.of_equiv e

end
