import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.MatchingNotVacuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint

set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

noncomputable section

namespace GlobalTheory.FactorDepth.Extension

attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `h` using `m.cart`. Establish `hid : spMap (algebraMap V V) = 𝟙 _` using `Spec.map_id _`. Take `⟨B, hB⟩` from `GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V))) (spMap (algebraMap V (DualNumber V)) ≫ x) rfl`. Take `⟨A, hA⟩` from `GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (spMap (algebraMap V V)) x (by rw [hid, Category.id_comp])`. Establish `hw : ∀ v : epsOver V V ⟶ G.G, v.left ≫ G.G.hom = spMap (algebraMap V (DualNumber V))` using `fun v => Over.w v`.

Establish `sc : ∀ (a : V) (u v : epsOver V V ⟶ G.G), (B u).left = spMap (epsMul a) ≫ (B v).left ↔ u.left = spMap (epsMul a) ≫ v.left`. Introduce `a u v`. Rewrite using `[hB, hB]`. Use `⟨fun e => h.1.hom_ext (by rw [e, Category.assoc]) ?_, fun e => by rw [e, Category.assoc]⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hw, hw, GlobalTheory.Exist.FlagBaseChange.epsMul_over]`.

Establish `prod : ∀ (n : ℕ) (u : Fin n → (epsOver V V ⟶ G.G)), B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod`. Introduce `n u`. Rewrite using `[map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Use `⟨B, hB, fun v => ?_, fun v a r => ?_, fun n v a w => ?_⟩` and prove the remaining obligations.

Unfold `IsTanAtG IsTan`. Use `(and_iff_right (Over.w (B v))).trans ?_` and prove the remaining obligations. Rewrite using `[← map_one A, hA, hB]`. Use `⟨fun e => h.1.hom_ext (by rw [← e, Category.assoc]) ?_, fun e => by rw [← e, Category.assoc]⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hw, GlobalTheory.Exist.FlagBaseChange.fst_over]`.

Conclude with `((Over.w (1 : ptOver V V ⟶ G.G)).trans hid).symm`. Establish `e : (B v).left ≫ (t.act.act a).left = (B (v ≫ G.act.act a)).left`. Rewrite using `[hB, hB, Over.comp_left, Category.assoc, Category.assoc, m.act]`. Rewrite using `[e]`. Conclude with `sc _ _ _`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, e⟩`. Use `⟨fun i => B.symm (u i), fun i => (sc _ _ _).1 (by rw [B.apply_symm_apply]; exact hu i), B.injective ?_⟩` and prove the remaining obligations. Rewrite using `[prod, ← Over.OverMorphism.ext e]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨u, hu, e⟩`. Conclude with `⟨fun i => B (u i), fun i => (sc _ _ _).2 (hu i), by rw [e, prod]⟩`.
-/
theorem exists_tanEquiv {V : Type} [CommRing V] {X0 : Scheme.{0}} {t : SAB H X0} {x : Sp V ⟶ X0} {G : SAB H (Sp V)}
    (m : SABMap G t x) :
    ∃ B : (epsOver V V ⟶ G.G) ≃* (tEpsG x ⟶ t.G), (∀ v, (B v).left = v.left ≫ m.φ) ∧
      (∀ v, IsTanAtG t x (B v).left ↔ IsTan v) ∧
      (∀ v (a : 𝓞 E) (r : V), (B v).left ≫ (t.act.act a).left = spMap (epsMul r) ≫ (B v).left ↔
        (v ≫ G.act.act a).left = spMap (epsMul r) ≫ v.left) ∧
      ∀ (n : ℕ) (v : Fin n → (epsOver V V ⟶ G.G)) a w,
        IsCombAtG t x (fun i => (B (v i)).left) a (B w).left ↔ IsComb v a w := by
  have h := m.cart
  have hid : spMap (algebraMap V V) = 𝟙 _ := Spec.map_id _
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h
    (spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)))
    (spMap (algebraMap V (DualNumber V)) ≫ x) rfl
  obtain ⟨A, hA⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (spMap (algebraMap V V)) x
    (by rw [hid, Category.id_comp])
  have hw : ∀ v : epsOver V V ⟶ G.G, v.left ≫ G.G.hom = spMap (algebraMap V (DualNumber V)) := fun v => Over.w v
  have sc : ∀ (a : V) (u v : epsOver V V ⟶ G.G),
      (B u).left = spMap (epsMul a) ≫ (B v).left ↔ u.left = spMap (epsMul a) ≫ v.left := by
    intro a u v
    rw [hB, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [e, Category.assoc]) ?_, fun e => by rw [e, Category.assoc]⟩
    rw [Category.assoc, hw, hw, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
  have prod : ∀ (n : ℕ) (u : Fin n → (epsOver V V ⟶ G.G)),
      B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
    intro n u
    rw [map_list_prod, List.map_ofFn]
    rfl
  refine ⟨B, hB, fun v => ?_, fun v a r => ?_, fun n v a w => ?_⟩
  · unfold IsTanAtG IsTan
    refine (and_iff_right (Over.w (B v))).trans ?_
    rw [← map_one A, hA, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [← e, Category.assoc]) ?_, fun e => by rw [← e, Category.assoc]⟩
    rw [Category.assoc, hw, GlobalTheory.Exist.FlagBaseChange.fst_over]
    exact ((Over.w (1 : ptOver V V ⟶ G.G)).trans hid).symm
  · have e : (B v).left ≫ (t.act.act a).left = (B (v ≫ G.act.act a)).left := by
      rw [hB, hB, Over.comp_left, Category.assoc, Category.assoc, m.act]
    rw [e]
    exact sc _ _ _
  · constructor
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => B.symm (u i), fun i => (sc _ _ _).1 (by rw [B.apply_symm_apply]; exact hu i), B.injective ?_⟩
      rw [prod, ← Over.OverMorphism.ext e]
      simp
    · rintro ⟨u, hu, e⟩
      exact ⟨fun i => B (u i), fun i => (sc _ _ _).2 (hu i), by rw [e, prod]⟩

end GlobalTheory.FactorDepth.Extension
