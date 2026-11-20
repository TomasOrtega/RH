import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped Classical

namespace GlobalTheory.PureFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `hx : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F`. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Conclude with `(x i).2.2`. Use `Set.Finite.subset (Filter.eventually_cofinite.1 (hφ.and hx)) ?_` and prove the remaining obligations.

Introduce `v hv hv'`. Apply `hv` to reduce the goal to its premises. Take `⟨h1, h2⟩` from `hv'`. Simplify using `only [h1]`. Rewrite using `[Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]`.

Both sides reduce to the same expression.
-/
theorem mulSupport_finite (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) : (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro i
    exact (x i).2.2
  refine Set.Finite.subset (Filter.eventually_cofinite.1 (hφ.and hx)) ?_
  intro v hv hv'
  apply hv
  obtain ⟨h1, h2⟩ := hv'
  simp only [h1]
  rw [Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
  rfl

/- English proof (translation)
Use `filter_upwards [hφ, Filter.eventually_cofinite_ne v₁] with v hv hne`. Rewrite using `[Function.update_of_ne hne]`. Conclude with `hv`.
-/
theorem update_eventually (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∀ᶠ v in Filter.cofinite, Function.update φ v₁ g v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hφ, Filter.eventually_cofinite_ne v₁] with v hv hne
  rw [Function.update_of_ne hne]; exact hv

/- English proof (translation)
Rewrite using `[← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ g hφ) x), ← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ (fun _ => 1) hφ) x)]`. Simplify using `only [Function.update_self, one_mul]`. Use `congr 1`. Use `finprod_congr fun v => finprod_congr fun hv => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne hv, Function.update_of_ne hv]`.
-/
theorem finprod_update (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) :
    (∏ᶠ v, Function.update φ v₁ g v fun i => evFin F v (x i)) =
      g (fun i => evFin F v₁ (x i)) * ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i) := by
  rw [← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ g hφ) x),
    ← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ (fun _ => 1) hφ) x)]
  simp only [Function.update_self, one_mul]
  congr 1
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  rw [Function.update_of_ne hv, Function.update_of_ne hv]

/- English proof (translation)
Use `set u : AF F := 1 - GlobalTheory.EmbChart.atPlace v₁ 1 with hu`. Establish `h0 : evFin F v₁ u = 0`. Rewrite using `[hu, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]`. Establish `hzi : u * z i = 0`. Use `congrFun (hz u h0) i` as an intermediate fact.

Simplify using `using this`. Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1 : (u * z i).1 = (z i).1`. Establish `: u.1 = 1`. Rewrite using `[hu]`.

Use `show (1 : Ainf F) - (0 : Ainf F) = 1`. Conclude with `sub_zero 1`. Use `show u.1 * (z i).1 = (z i).1`. Rewrite using `[this, one_mul]`. Rewrite using `[← h1, hzi]`.

Both sides reduce to the same expression. Establish `h2 : evFin F v u = 1`. Rewrite using `[hu, map_sub, map_one]`. Establish `: evFin F v (GlobalTheory.EmbChart.atPlace v₁ 1) = 0` using `evalV_singleFin_ne hv 1`. Rewrite using `[this, sub_zero]`.

Use `congrArg (evFin F v) hzi` as an intermediate fact. Rewrite `this` using `[map_mul, h2, one_mul, map_zero]`. Then use the resulting hypothesis.
-/
theorem comp_add_of_at (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z) (i : κ) :
    (z i).1 = 0 ∧ ∀ v, v ≠ v₁ → evFin F v (z i) = 0 := by
  set u : AF F := 1 - GlobalTheory.EmbChart.atPlace v₁ 1 with hu
  have h0 : evFin F v₁ u = 0 := by
    rw [hu, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 : (u * z i).1 = (z i).1 := by
      have : u.1 = 1 := by
        rw [hu]
        show (1 : Ainf F) - (0 : Ainf F) = 1
        exact sub_zero 1
      show u.1 * (z i).1 = (z i).1
      rw [this, one_mul]
    rw [← h1, hzi]; rfl
  · have h2 : evFin F v u = 1 := by
      rw [hu, map_sub, map_one]
      have : evFin F v (GlobalTheory.EmbChart.atPlace v₁ 1) = 0 := evalV_singleFin_ne hv 1
      rw [this, sub_zero]
    have := congrArg (evFin F v) hzi
    rwa [map_mul, h2, one_mul, map_zero] at this

end GlobalTheory.PureFactor

open GlobalTheory.PureFactor in

/- English proof (translation)
Introduce `F _ _ κ _ v₁ f φ hφ`. Use `⟨fun x => f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i), ?_, ?_⟩` and prove the remaining obligations. Introduce `x z hz`. Establish `hI : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)`. Use function extensionality and compare the values at `i`.

Establish `h` using `(comp_add_of_at v₁ z hz i).1`. Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + (z i).1) = (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1`. Rewrite using `[h, add_zero]`. Simplify using `only`. Rewrite using `[hI]`.

Use `congr 1`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v = v₁`. Substitute `hv` using the available equality. Simplify using `only [Function.update_self]`.

Rewrite using `[Function.update_of_ne hv]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, map_add, (comp_add_of_at v₁ z hz i).2 v hv, add_zero]`. Introduce `ψ₀`.

Use function extensionality and compare the values at `x`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure`. Rewrite using `[finprod_update φ v₁ ψ₀ hφ x]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.PureFactor.exists_rest_factor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∃ r : (κ → AF F) → ℂ, (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x) ∧
      ∀ ψ₀ : (κ → Fv F v₁) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀) := by
  intro F _ _ κ _ v₁ f φ hφ
  refine ⟨fun x => f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) *
    ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i), ?_, ?_⟩
  · intro x z hz
    have hI : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i) := by
      funext i
      have h := (comp_add_of_at v₁ z hz i).1
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + (z i).1) = (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
      rw [h, add_zero]
    simp only
    rw [hI]
    congr 1
    refine finprod_congr fun v => ?_
    by_cases hv : v = v₁
    · subst hv; simp only [Function.update_self]
    · rw [Function.update_of_ne hv]
      congr 1
      funext i
      rw [Pi.add_apply, map_add, (comp_add_of_at v₁ z hz i).2 v hv, add_zero]
  · intro ψ₀
    funext x
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [finprod_update φ v₁ ψ₀ hφ x]
    ring
