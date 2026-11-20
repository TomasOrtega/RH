import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem ordE_neg {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    ordE w (-x) = ordE w x := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold ordE
    rw [GroundTheory.Global.count_spanSingleton w hx, GroundTheory.Global.count_spanSingleton w (neg_ne_zero.2 hx),
      Valuation.map_neg]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem ordE_mul {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) : ordE w (x * y) = ordE w x + ordE w y := by
  unfold ordE
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TP.Skew.ordLine :
    UpperTheory.Gal.TP.Skew.ConjAut → UpperTheory.Gal.TP.Skew.IdeleStep → UpperTheory.Gal.TP.Skew.OrdEmb → UpperTheory.Gal.TP.Skew.InvFun → UpperTheory.Gal.TP.Skew.OrdAut → UpperTheory.Gal.TP.Skew.OrdLine := by
  intro hCA hIS hOE hIF hOA F E _ _ _ _ _ σ hc hu
  classical
  obtain ⟨hG, s, hsσ, hs1, hss, hall, δ₀, hδ0, hδσ⟩ := hCA F E σ hc
  haveI := hG
  let m : HeightOneSpectrum (𝓞 E) → ℤ := fun w =>
    FractionalIdeal.count E w (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) - ordE w δ₀
  have hcof : ∀ᶠ w in Filter.cofinite, m w = 0 :=
    ((FractionalIdeal.finite_factors (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))).and
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 E)⁰ δ₀))).mono
      fun w h => by
        change _ - FractionalIdeal.count E w _ = 0
        rw [h.1, h.2, sub_zero]
  have hinv : ∀ (g : E ≃ₐ[F] E) w, m (g • w) = m w := by
    intro g w
    rcases hall g with hg | hg
    · rw [hg, one_smul]
    · rw [hg]
      have h1 := (hOA F E s w).1 δ₀
      have h2 := (hOA F E s w).2
      rw [hsσ, hδσ, ordE_neg] at h1
      change _ - _ = _ - _
      rw [h1, h2]
  obtain ⟨a, ha⟩ := hIF F E m hcof hinv
  obtain ⟨x, b, hxb⟩ := hIS F E σ hc a
  have hx0 : algebraMap F E (x : F) ≠ 0 :=
    (map_ne_zero (algebraMap F E)).2 x.ne_zero
  refine ⟨s, algebraMap F E (x : F) * δ₀,
    ((toFractionalIdeal b : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E),
    hsσ, hss, mul_ne_zero hx0 hδ0, ?_, Units.ne_zero _, ?_⟩
  · rw [map_mul, AlgHom.commutes, hδσ, mul_neg]
  · intro w
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
      ext g
      simpa using hall g
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have h1 : m w = ord (w.under (𝓞 F)) (diagonal F x) + ord (w.under (𝓞 F)) (ideleNorm F E b) :=
      (ha w).symm.trans (hxb _)
    rw [← hOE F E hu _ w, ← hOE F E hu _ w, ideleEmbedding_diagonal, ideleEmbedding_ideleNorm,
      huniv, Finset.prod_pair hs1.symm, ord_mul, one_smul, ord_smul, hsi, ord_diagonal,
      ← GroundTheory.Global.count_spanSingleton w (by simpa using x.ne_zero)] at h1
    have h3 : FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰
        ((Units.map (algebraMap F E).toMonoidHom x : Eˣ) : E)) = ordE w (algebraMap F E (x : F)) := rfl
    rw [h3] at h1
    rw [ordE_mul w hx0 hδ0, count_toFractionalIdeal, count_toFractionalIdeal]
    change _ - _ = _ at h1
    linarith
