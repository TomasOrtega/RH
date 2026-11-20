import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBase

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsExactCond

/- English proof (translation)
Introduce `hR hP hA`. Use `⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩` and prove the remaining obligations. Take `⟨δ⟩` from `nonempty_fieldDat hR hA B₀.toPre`. Take `⟨B₁, e₁, k⟩` from `(GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2`. Take `⟨B₂, e₂, k₂, l₂⟩` from `Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)`.

Take `⟨B, e, l₃⟩` from `BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)`. Establish `hk : B.KsC = B₁.KsC` using `e.KsC_eq.trans k₂`. Establish `e' : B.toPre = B₀.toPre` using `e.1.trans (e₂.trans e₁)`. Establish `hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)`. Rewrite using `[hk, Has₂, e.fixedCoefficientField_eq]`.

Conclude with `⟨l₂, l₃⟩`. Rewrite `k` using `[← hk]`. Use `clear e e₁ e₂ hO`. Generalize the expression as in `B₀.toPre = P₀ at *`. Substitute `e'` using the available equality.

Conclude with `⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩`. Establish `e'` using `e.1`. Unfold `Base.KsExact at hS ⊢`. Rewrite using `[e.KsC_eq]`. Use `clear e`.

Generalize the expression as in `B.KsC = F at *`. Generalize the expression as in `B.toPre = P at *`. Substitute `e'` using the available equality. Take `rfl` from `eq_of_heq hf`. Conclude with `hS`.
-/
theorem ksCond_exact : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt →
    V4.KsCond fun B f => ∃ δ : FieldDat B.toPre, B.KsExact δ f := by
  intro hR hP hA
  refine ⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

end GlobalTheory.Mem.KsExactCond
