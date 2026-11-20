import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Unfold `ordE`. Rewrite using `[GroundTheory.Global.count_spanSingleton w hx, GroundTheory.Global.count_spanSingleton w (neg_ne_zero.2 hx), Valuation.map_neg]`.
-/
private theorem ordE_neg {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    ordE w (-x) = ordE w x := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold ordE
    rw [GroundTheory.Global.count_spanSingleton w hx, GroundTheory.Global.count_spanSingleton w (neg_ne_zero.2 hx),
      Valuation.map_neg]

/- English proof (translation)
Unfold `ordE`. Rewrite using `[← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx) (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy)]`.
-/
private theorem ordE_mul {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) : ordE w (x * y) = ordE w x + ordE w y := by
  unfold ordE
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy)]

/- English proof (translation)
Introduce `hCA hIS hOE hIF hOA F E _ _ _ _ _ σ hc hu`. Take `⟨hG, s, hsσ, hs1, hss, hall, δ₀, hδ0, hδσ⟩` from `hCA F E σ hc`. Use `haveI := hG`. Set `m : HeightOneSpectrum (𝓞 E) → ℤ` to `fun w => FractionalIdeal.count E w (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) - ordE w δ₀`. Establish `hcof : ∀ᶠ w in Filter.cofinite, m w = 0` using `((FractionalIdeal.finite_factors (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))).and (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 E)⁰ δ₀))).mono fun w h => by`.

Express the relevant statement in the definitionally equal form `_ - FractionalIdeal.count E w _ = 0`. Rewrite using `[h.1, h.2, sub_zero]`. Establish `hinv : ∀ (g : E ≃ₐ[F] E) w, m (g • w) = m w`. Introduce `g w`. Break down `hall g with hg | hg` into its components or cases.

Rewrite using `[hg, one_smul]`. Rewrite using `[hg]`. Establish `h1` using `(hOA F E s w).1 δ₀`. Establish `h2` using `(hOA F E s w).2`. Rewrite `h1` using `[hsσ, hδσ, ordE_neg]`.

Express the relevant statement in the definitionally equal form `_ - _ = _ - _`. Rewrite using `[h1, h2]`. Take `⟨a, ha⟩` from `hIF F E m hcof hinv`. Take `⟨x, b, hxb⟩` from `hIS F E σ hc a`. Establish `hx0 : algebraMap F E (x : F) ≠ 0` using `(map_ne_zero (algebraMap F E)).2 x.ne_zero`.

Use `⟨s, algebraMap F E (x : F) * δ₀, ((toFractionalIdeal b : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E), hsσ, hss, mul_ne_zero hx0 hδ0, ?_, Units.ne_zero _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes, hδσ, mul_neg]`. Introduce `w`. Establish `huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s}`. Use extensionality with `g`.

Simplify using `using hall g`. Establish `hsi : s⁻¹ = s` using `inv_eq_of_mul_eq_one_right hss`. Establish `h1 : m w = ord (w.under (𝓞 F)) (diagonal F x) + ord (w.under (𝓞 F)) (ideleNorm F E b)` using `(ha w).symm.trans (hxb _)`. Rewrite `h1` using `[← hOE F E hu _ w, ← hOE F E hu _ w, ideleEmbedding_diagonal, ideleEmbedding_ideleNorm, huniv, Finset.prod_pair hs1.symm, ord_mul, one_smul, ord_smul, hsi, ord_diagonal, ← GroundTheory.Global.count_spanSingleton w (by simpa using x.ne_zero)]`. Establish `h3 : FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((Units.map (algebraMap F E).toMonoidHom x : Eˣ) : E)) = ordE w (algebraMap F E (x : F))` using `rfl`.

Rewrite `h1` using `[h3]`. Rewrite using `[ordE_mul w hx0 hδ0, count_toFractionalIdeal, count_toFractionalIdeal]`. Express the relevant statement in the definitionally equal form `_ - _ = _ at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
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
