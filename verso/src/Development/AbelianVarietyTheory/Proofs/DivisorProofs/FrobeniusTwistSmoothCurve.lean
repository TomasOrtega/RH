import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobTwistCurve

/- English proof (translation)
Take `⟨N, i, hi, e⟩` from `h`. Establish `H` using `ProjSpace.isPullback_baseChange N φ`. Establish `: IsIso (ProjSpace.baseChange N φ)` using `H.isIso_fst_of_isIso`. Conclude with `⟨N, i ≫ ProjSpace.baseChange N φ, inferInstance, by rw [Category.assoc, H.w, ← Category.assoc, e]⟩`.
-/
theorem isProjOver_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') [IsIso (spMap φ)]
    {X : Scheme.{0}} {f : X ⟶ Sp R'} (h : IsProjOver f) : IsProjOver (f ≫ spMap φ) := by
  obtain ⟨N, i, hi, e⟩ := h
  have H := ProjSpace.isPullback_baseChange N φ
  have : IsIso (ProjSpace.baseChange N φ) := H.isIso_fst_of_isIso
  exact ⟨N, i ≫ ProjSpace.baseChange N φ, inferInstance, by rw [Category.assoc, H.w, ← Category.assoc, e]⟩

/- English proof (translation)
Introduce `q _ k _ _ _ C a hC`. Establish `h₁` using `hC.isIntegral`. Establish `h₂` using `hC.dim_eq`. Establish `h₃` using `hC.isProjOver`. Establish `h₄` using `hC.smooth`.

Establish `h₅` using `natCast_eq_zero C q k`. Set `a' : Algebra k Γ(C, ⊤)` to `((algebraMap k Γ(C, ⊤)).comp (frobenius k q)).toAlgebra`. Establish `e : @strHom k _ C a' = @strHom k _ C a ≫ spMap (frobenius k q)`. Simplify using `only [strHom, Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `hiso : IsIso (spMap (frobenius k q))`. Establish `: IsIso (CommRingCat.ofHom (frobenius k q))` using `(frobeniusEquiv k q).toCommRingCatIso.isIso_hom`. Use `infer_instance`. Establish `h0 : (q : Γ(Sp k, ⊤)) = 0`. Rewrite using `[← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom, CharP.cast_eq_zero, map_zero]`.

Use `⟨a', @IsSmoothProjCurve.mk k _ C a' (@IsProjCurve.mk k _ C a' h₁ h₂ ?_) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `isProjOver_comp_spMap _ h₃`. Rewrite using `[e]`. Use `infer_instance`.

Rewrite using `[e, frob_naturality q h0 _ h₅]`. Use `congr 1`. Conclude with `SS.FrobField.absFrob_spec k q 1 Fact.out h0 _ fun c => by rw [pow_one, frobenius_def]`.
-/
theorem exists_twist : ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [CharP k q] (C : Scheme.{0}) [a : Algebra k Γ(C, ⊤)], IsSmoothProjCurve k C → ∃ a' : Algebra k Γ(C, ⊤), @IsSmoothProjCurve k _ C a' ∧ frob C q (natCast_eq_zero C q k) ≫ @strHom k _ C a = @strHom k _ C a' := by
  intro q _ k _ _ _ C a hC
  have h₁ := hC.isIntegral
  have h₂ := hC.dim_eq
  have h₃ := hC.isProjOver
  have h₄ := hC.smooth
  have h₅ := natCast_eq_zero C q k
  let a' : Algebra k Γ(C, ⊤) := ((algebraMap k Γ(C, ⊤)).comp (frobenius k q)).toAlgebra
  have e : @strHom k _ C a' = @strHom k _ C a ≫ spMap (frobenius k q) := by
    simp only [strHom, Category.assoc, ← Spec.map_comp]
    rfl
  have hiso : IsIso (spMap (frobenius k q)) := by
    have : IsIso (CommRingCat.ofHom (frobenius k q)) := (frobeniusEquiv k q).toCommRingCatIso.isIso_hom
    infer_instance
  have h0 : (q : Γ(Sp k, ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom, CharP.cast_eq_zero, map_zero]
  refine ⟨a', @IsSmoothProjCurve.mk k _ C a' (@IsProjCurve.mk k _ C a' h₁ h₂ ?_) ?_, ?_⟩
  · rw [e]; exact isProjOver_comp_spMap _ h₃
  · rw [e]; infer_instance
  · rw [e, frob_naturality q h0 _ h₅]
    congr 1
    exact SS.FrobField.absFrob_spec k q 1 Fact.out h0 _ fun c => by rw [pow_one, frobenius_def]

end GlobalTheory.FrobTwistCurve
