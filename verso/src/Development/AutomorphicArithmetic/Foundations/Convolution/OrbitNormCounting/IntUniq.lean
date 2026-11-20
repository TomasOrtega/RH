import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.Transl
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AutomorphicArithmetic.UnitaryInvolutions.EventuallyMapMemMaximalCompactGL
import Development.AutomorphicArithmetic.UnitaryInvolutions.EventuallySeparableOfIntegralModel
import Development.AutomorphicArithmetic.UnitaryInvolutions.UnitaryInvolutionStabilizesIntegralAtNonsplit
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

/- English proof (translation)
Take `⟨g₀, rfl⟩` from `hg`. Take `⟨y₀, rfl⟩` from `hy`. Establish `e : ∀ a : GL (Fin n) (Ov E w), (Formalism.UG.bc (n` using `Fin n) (Ov E w).subtype a).val = a.val.map (Ov E w).subtype := fun a => rfl`. Establish `hinj : Function.Injective (Ov E w).subtype` using `Subtype.val_injective`. Establish `hcp : ∀ a : GL (Fin n) (Ov E w), (Formalism.UG.bc (n` using `Fin n) (Ov E w).subtype a).val.charpoly = a.val.charpoly.map (Ov E w).subtype := by`.

Introduce `a`. Rewrite using `[e, Matrix.charpoly_map]`. Establish `hs : g₀.val.charpoly.Separable` using `hsep _ (hcp g₀).symm`. Establish `hyg : y₀.val.charpoly = g₀.val.charpoly`. Apply `Polynomial.map_injective _ hinj` to reduce the goal to its premises.

Rewrite using `[← hcp, ← hcp, hp]`. Take `⟨x, hx⟩` from `(UpperTheory.ConvolutionTheory.D.conjSep (Ov E w) (Ov E w) n g₀.val hs).1 y₀.val hyg`. Use `⟨Formalism.UG.bc (n := Fin n) (Ov E w).subtype x, ⟨x, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, eq_inv_mul_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, Units.val_mul, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, hx]`.
-/
private theorem splitCase {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) (g y : GLw n w)
    (hg : g ∈ GlobalTheory.LFun.KGL w n) (hy : y ∈ GlobalTheory.LFun.KGL w n) (hp : y.val.charpoly = g.val.charpoly)
    (hsep : ∀ Q : (Ov E w)[X], Q.map (Ov E w).subtype = g.val.charpoly → Q.Separable) :
    ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * g * k := by
  obtain ⟨g₀, rfl⟩ := hg
  obtain ⟨y₀, rfl⟩ := hy
  have e : ∀ a : GL (Fin n) (Ov E w), (Formalism.UG.bc (n := Fin n) (Ov E w).subtype a).val = a.val.map (Ov E w).subtype := fun a => rfl
  have hinj : Function.Injective (Ov E w).subtype := Subtype.val_injective
  have hcp : ∀ a : GL (Fin n) (Ov E w), (Formalism.UG.bc (n := Fin n) (Ov E w).subtype a).val.charpoly = a.val.charpoly.map (Ov E w).subtype := by
    intro a
    rw [e, Matrix.charpoly_map]
  have hs : g₀.val.charpoly.Separable := hsep _ (hcp g₀).symm
  have hyg : y₀.val.charpoly = g₀.val.charpoly := by
    apply Polynomial.map_injective _ hinj
    rw [← hcp, ← hcp, hp]
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep (Ov E w) (Ov E w) n g₀.val hs).1 y₀.val hyg
  refine ⟨Formalism.UG.bc (n := Fin n) (Ov E w).subtype x, ⟨x, rfl⟩, ?_⟩
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, hx]

/- English proof (translation)
Introduce `E _ _ _ hU n δ hsep`. Take `⟨u, hth, hu, hloc⟩` from `UpperTheory.ConvolutionTheory.G3.transl E hU n`. Establish `h1` using `UpperTheory.eventually_map_mem_maximalCompactGL E n (δ * thE E n δ)`. Establish `h2` using `UpperTheory.eventually_map_mem_maximalCompactGL E n δ`. Establish `h3` using `UpperTheory.eventually_map_mem_maximalCompactGL E n u`.

Establish `h4` using `UpperTheory.eventually_separable_of_integral_model E (UpperTheory.ConvolutionTheory.G3.gpol δ) hsep`. Use `filter_upwards [h1, h2, h3, h4] with w h1 h2 h3 h4`. Distinguish the cases in `hs : IsSplitAt w`. Establish `hl : locEl n w δ = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)`. Simplify using `[locEl, hs]`.

Establish `hcp : (locEl n w δ).val.charpoly = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ)`. Rewrite using `[hl]`. Conclude with `Matrix.charpoly_map _ _`. Use `⟨hl ▸ h1, fun y hy hp => ?_⟩` and prove the remaining obligations. Establish `hy' : y.val.charpoly = (locEl n w δ).val.charpoly`.

Rewrite using `[hcp, ← hp]`. Simplify using `[UpperTheory.ConvolutionTheory.G3.lpol, nrmL, hs]`. Take `⟨k, hk, e⟩` from `splitCase w n (locEl n w δ) y (hl ▸ h1) hy hy' (fun Q hQ => h4 Q (hQ.trans hcp))`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Simplify `e` using `[thL, hs]`.

Establish `hl : locEl n w δ = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ`. Simplify using `[locEl, hs]`. Conclude with `⟨hl ▸ h2, UpperTheory.unitary_involution_stabilizes_integral_at_nonsplit E hU n u δ hth hu w hs (hloc w hs) h3 h2 h4⟩`.
-/
theorem UpperTheory.ConvolutionTheory.G3.intUniq :
    UpperTheory.ConvolutionTheory.G3.IntUniq := by
  intro E _ _ _ hU n δ hsep
  obtain ⟨u, hth, hu, hloc⟩ := UpperTheory.ConvolutionTheory.G3.transl E hU n
  have h1 := UpperTheory.eventually_map_mem_maximalCompactGL E n (δ * thE E n δ)
  have h2 := UpperTheory.eventually_map_mem_maximalCompactGL E n δ
  have h3 := UpperTheory.eventually_map_mem_maximalCompactGL E n u
  have h4 := UpperTheory.eventually_separable_of_integral_model E (UpperTheory.ConvolutionTheory.G3.gpol δ) hsep
  filter_upwards [h1, h2, h3, h4] with w h1 h2 h3 h4
  by_cases hs : IsSplitAt w
  · have hl : locEl n w δ = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
      simp [locEl, hs]
    have hcp : (locEl n w δ).val.charpoly = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) := by
      rw [hl]
      exact Matrix.charpoly_map _ _
    refine ⟨hl ▸ h1, fun y hy hp => ?_⟩
    have hy' : y.val.charpoly = (locEl n w δ).val.charpoly := by
      rw [hcp, ← hp]
      simp [UpperTheory.ConvolutionTheory.G3.lpol, nrmL, hs]
    obtain ⟨k, hk, e⟩ := splitCase w n (locEl n w δ) y (hl ▸ h1) hy hy' (fun Q hQ => h4 Q (hQ.trans hcp))
    refine ⟨k, hk, ?_⟩
    simpa [thL, hs] using e
  · have hl : locEl n w δ = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ := by
      simp [locEl, hs]
    exact ⟨hl ▸ h2, UpperTheory.unitary_involution_stabilizes_integral_at_nonsplit E hU n u δ hth hu w hs (hloc w hs) h3 h2 h4⟩
