import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HasseFld

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

/- English proof (translation)
Set `U : (k ⊗[maximalRealSubfield E] plus Q)ˣ` to `Units.map (Algebra.TensorProduct.includeRight : plus Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] plus Q).toMonoidHom (Units.mk0 x hx)`. Establish `hU : (U : k ⊗[maximalRealSubfield E] plus Q) = 1 ⊗ₜ x` using `rfl`. Establish `hi : inclPlus Q k (1 ⊗ₜ x) = 1 ⊗ₜ (x : Fld Q)` using `by simp [inclPlus]`. Establish `hzu : IsUnit z`. Establish `: IsUnit (z * involBase Q k z)`.

Rewrite using `[hz, ← hi, ← hU]`. Conclude with `U.isUnit.map _`. Conclude with `isUnit_of_mul_isUnit_left this`. Establish `hmem : U ∈ norms Q k` using `⟨hzu.unit, Units.ext (by`. Express the relevant statement in the definitionally equal form `z * involBase Q k z = inclPlus Q k (U : _)`.

Rewrite using `[hz, hU, hi])⟩`. Rewrite using `[← hU]`. Conclude with `(GlobalTheory.TraceClasses.mem_norms_iff Q h0 hθ k hd U).1 hmem`.
-/
theorem isValue_of_local {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Q : SelfRecip E r) {θ : E} (h0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ) {d : plus Q}
    (hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ)
    (k : Type) [Field k] [Algebra (maximalRealSubfield E) k]
    (x : plus Q) (hx : x ≠ 0) (z : k ⊗[maximalRealSubfield E] Fld Q)
    (hz : z * involBase Q k z = 1 ⊗ₜ (x : Fld Q)) :
    GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) (1 ⊗ₜ x : k ⊗[maximalRealSubfield E] plus Q) := by
  let U : (k ⊗[maximalRealSubfield E] plus Q)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight :
      plus Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] plus Q).toMonoidHom (Units.mk0 x hx)
  have hU : (U : k ⊗[maximalRealSubfield E] plus Q) = 1 ⊗ₜ x := rfl
  have hi : inclPlus Q k (1 ⊗ₜ x) = 1 ⊗ₜ (x : Fld Q) := by simp [inclPlus]
  have hzu : IsUnit z := by
    have : IsUnit (z * involBase Q k z) := by
      rw [hz, ← hi, ← hU]; exact U.isUnit.map _
    exact isUnit_of_mul_isUnit_left this
  have hmem : U ∈ norms Q k := ⟨hzu.unit, Units.ext (by
      change z * involBase Q k z = inclPlus Q k (U : _)
      rw [hz, hU, hi])⟩
  rw [← hU]
  exact (GlobalTheory.TraceClasses.mem_norms_iff Q h0 hθ k hd U).1 hmem

/- English proof (translation)
Introduce `E _ _ _ r Q x hxx hf hi`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨θ, h0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : E, IsCMField.complexConj E w ≠ w := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `IsCMField.complexConj_ne_one E (AlgEquiv.ext h)`. Conclude with `⟨w - IsCMField.complexConj E w, sub_ne_zero.mpr hw.symm, by simp⟩`. Set `x' : plus Q` to `⟨x, hxx⟩`.

Establish `hx' : x' ≠ 0` using `fun h => hx (congrArg Subtype.val h)`. Set `d : plus Q` to `⟨algebraMap E _ θ * algebraMap E _ θ, by show invol Q _ = (AlgHom.id _ _) _`. Rewrite using `[map_mul, GlobalTheory.TraceClasses.invol_theta Q hθ]`. Use the proof step `simp⟩`. Establish `hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ` using `rfl`.

Take `⟨e, e0, e1⟩` from `GlobalTheory.TraceClasses.exists_basis_theta Q h0 hθ`. Use `GlobalTheory.TraceClasses.isQuadraticExtension Q h0 hθ` as an intermediate fact. Establish `e2 : e 1 * e 1 = algebraMap _ _ d` using `by rw [e1]; exact hd.symm`. Take `⟨a, b, hab⟩` from `GlobalTheory.TraceClasses.form_of_local (F := maximalRealSubfield E) e e0 e2 (Units.mk0 x' hx') (fun v => by`. Take `⟨z, hz⟩` from `hf v`.

Conclude with `isValue_of_local Q h0 hθ hd _ x' hx' z hz)`. Use the proof step `(fun v => by`. Take `⟨z, hz⟩` from `hi v`. Conclude with `isValue_of_local Q h0 hθ hd _ x' hx' z hz)`. Use `⟨a + b * algebraMap E _ θ, ?_⟩` and prove the remaining obligations.

Establish `hx2 : x = (a : Fld Q) ^ 2 - d * b ^ 2`. Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `using this`. Rewrite using `[map_add, map_mul, GlobalTheory.TraceClasses.invol_coe, GlobalTheory.TraceClasses.invol_coe, GlobalTheory.TraceClasses.invol_theta Q hθ, hx2, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasse_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (Q : SelfRecip E r) (x : Fld Q), invol Q x = x →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] Fld Q,
        z * involBase Q _ z = 1 ⊗ₜ x) →
    (∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] Fld Q, z * involBase Q _ z = 1 ⊗ₜ x) →
    ∃ y : Fld Q, y * invol Q y = x := by
  intro E _ _ _ r Q x hxx hf hi
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨θ, h0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by
    obtain ⟨w, hw⟩ : ∃ w : E, IsCMField.complexConj E w ≠ w := by
      by_contra h
      push_neg at h
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
    exact ⟨w - IsCMField.complexConj E w, sub_ne_zero.mpr hw.symm, by simp⟩
  let x' : plus Q := ⟨x, hxx⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let d : plus Q := ⟨algebraMap E _ θ * algebraMap E _ θ, by
    show invol Q _ = (AlgHom.id _ _) _
    rw [map_mul, GlobalTheory.TraceClasses.invol_theta Q hθ]
    simp⟩
  have hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ := rfl
  obtain ⟨e, e0, e1⟩ := GlobalTheory.TraceClasses.exists_basis_theta Q h0 hθ
  have := GlobalTheory.TraceClasses.isQuadraticExtension Q h0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  obtain ⟨a, b, hab⟩ := GlobalTheory.TraceClasses.form_of_local (F := maximalRealSubfield E) e e0 e2
    (Units.mk0 x' hx')
    (fun v => by
      obtain ⟨z, hz⟩ := hf v
      exact isValue_of_local Q h0 hθ hd _ x' hx' z hz)
    (fun v => by
      obtain ⟨z, hz⟩ := hi v
      exact isValue_of_local Q h0 hθ hd _ x' hx' z hz)
  refine ⟨a + b * algebraMap E _ θ, ?_⟩
  have hx2 : x = (a : Fld Q) ^ 2 - d * b ^ 2 := by
    have := congrArg Subtype.val hab
    simpa using this
  rw [map_add, map_mul, GlobalTheory.TraceClasses.invol_coe, GlobalTheory.TraceClasses.invol_coe,
    GlobalTheory.TraceClasses.invol_theta Q hθ, hx2, hd]
  ring

end GlobalTheory.HasseFld
