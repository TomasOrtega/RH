import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformationStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h1]`. Unfold `sOf`. Establish `e : (GlobalTheory.FlagTan.dir c M).toRingHom.comp (algebraMap c.F (TrivSqZeroExt K (ι → K))) = algebraMap c.F (DualNumber K)` using `(GlobalTheory.FlagTan.dir c M).comp_algebraMap`. Rewrite using `[spMap_comp_spMap, ← RingHom.comp_assoc, e]`.

Rewrite using `[← Category.assoc, spMap_comp_spMap, ← h2]`. Use `congr 2`. Apply the tactic sequence `ext z <;> simp`.
-/
theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (h1 : X ≫ Xo.s = sOf c _) (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x)
    (M : ι → K) : GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1]
    unfold sOf
    have e : (GlobalTheory.FlagTan.dir c M).toRingHom.comp (algebraMap c.F (TrivSqZeroExt K (ι → K))) =
        algebraMap c.F (DualNumber K) := (GlobalTheory.FlagTan.dir c M).comp_algebraMap
    rw [spMap_comp_spMap, ← RingHom.comp_assoc, e]
  · rw [← Category.assoc, spMap_comp_spMap, ← h2]
    congr 2
    ext z <;> simp

/- English proof (translation)
Introduce `hP hG E _ _ _ H Dw l Xo c K _ _ y hpq`. Take `⟨X, h1, h2, hks⟩` from `GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq`. Use `⟨X, h1, h2, fun x' hx => ?_⟩` and prove the remaining obligations. Establish `key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X` using `fun M => ⟨fun k => GlobalTheory.T.kodaira_spencer_tangent_difference hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M), fun e => e ▸ hks M⟩`. Take `⟨M, hM⟩` from `GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y x' hpq hx`.

Conclude with `⟨⟨M, (key M).1 hM, fun M' e => GlobalTheory.T.kodaira_spencer_matrix_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩`.
-/
theorem ksIso_psiSet : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  obtain ⟨X, h1, h2, hks⟩ := GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq
  refine ⟨X, h1, h2, fun x' hx => ?_⟩
  have key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X := fun M =>
    ⟨fun k => GlobalTheory.T.kodaira_spencer_tangent_difference hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M),
      fun e => e ▸ hks M⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y x' hpq hx
  exact ⟨⟨M, (key M).1 hM, fun M' e => GlobalTheory.T.kodaira_spencer_matrix_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩

end GlobalTheory.FlagTan
