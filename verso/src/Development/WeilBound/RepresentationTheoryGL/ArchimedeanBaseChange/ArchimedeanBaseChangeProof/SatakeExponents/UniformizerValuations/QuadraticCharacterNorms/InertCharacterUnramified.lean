import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace PositivityTheory.Rg.BcB.F.Fok.Mu3Aux1

/- English proof (translation)
Use `haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Establish `he` using `ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[ValuativeRel.le_uniformizer_iff, he.lt_one_iff_lt_one, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Take `⟨y, hy⟩` from `ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))`. Rewrite using `[← hy]`. Establish `h1 : Valued.v y < 1`. Rewrite using `[← he.lt_one_iff_lt_one, hy]`. Conclude with `ValuativeRel.uniformizer_lt_one`.

Rewrite using `[he.le_iff_le, hx]`. Distinguish the cases in `hy0 : Valued.v y = 0`. Rewrite using `[hy0]`. Conclude with `zero_le'`. Rewrite `h1`, the goal using `[← WithZero.exp_log hy0]`.

Rewrite `h1` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_eq_uniformizer {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : Valued.v x = WithZero.exp (-1 : ℤ)) :
    ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff, he.lt_one_iff_lt_one, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
    rw [← hy]
    have h1 : Valued.v y < 1 := by
      rw [← he.lt_one_iff_lt_one, hy]; exact ValuativeRel.uniformizer_lt_one
    rw [he.le_iff_le, hx]
    by_cases hy0 : Valued.v y = 0
    · rw [hy0]; exact zero_le'
    · rw [← WithZero.exp_log hy0] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega

/- English proof (translation)
Use `haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hx`.
-/
theorem valued_eq_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : ValuativeRel.valuation (w.adicCompletion E) x = 1) : Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hx

/- English proof (translation)
Conclude with `Pi.mulSingle_eq_same v _`.
-/
theorem loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (Neutral.B1.localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

/- English proof (translation)
Conclude with `Pi.mulSingle_eq_of_ne h _`.
-/
theorem loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : (Neutral.B1.localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ideleMap_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : Neutral.B1.Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L a).val.2 w = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap ideleMap)

/- English proof (translation)
Introduce `E _ _ _ hU μ hres hunit w hw`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E` using `E) (w.under (𝓞 (maximalRealSubfield E))) := by`. Introduce `hs`. Take `⟨a, b, hab, ha, hb⟩` from `GlobalTheory.LFun.isSplit_iff.1 hs`.

Apply `hw` to reduce the goal to its premises. Break down `eq_or_ne a w with rfl | haw` into its components or cases. Conclude with `⟨b, hab.symm, hb⟩`. Conclude with `⟨a, haw, ha⟩`. Establish `hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E` using `E) (w.under (𝓞 (maximalRealSubfield E))) := by`.

Use `GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_` and prove the remaining obligations. Take `rfl` from `GlobalTheory.LFun.eq_of_not_isSplit hns hu rfl`. Use `u.isPrime` as an intermediate fact. Conclude with `Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (hU u)`. Establish `he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1` using `GlobalTheory.LFun.isUnram_iff.1 hun w rfl`.

Take `⟨ϖ, hϖ⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (w.under (𝓞 (maximalRealSubfield E)))`. Use `set ϖE : (w.adicCompletion E)ˣ := Units.map (finiteCompletionMap (maximalRealSubfield E) E w).toMonoidHom ϖ with hϖE`. Establish `hvE : Valued.v (ϖE : w.adicCompletion E) = WithZero.exp (-1 : ℤ)`. Express the relevant statement in the definitionally equal form `Valued.v (finiteCompletionMap (maximalRealSubfield E) E w ϖ) = _`. Rewrite using `[← GlobalTheory.CharTransport.locMap_eq, ← GlobalTheory.LFun.complMap_rfl, GlobalTheory.LFun.valued_complMap rfl ϖ.ne_zero, he, pow_one]`.

Conclude with `hϖ`. Establish `hid : ideleMap (maximalRealSubfield E) E (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) = Neutral.B1.localIdele E w ϖE`. Use `Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))` and prove the remaining obligations. Conclude with `map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E)`. Rewrite using `[ideleMap_apply]`.

Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Rewrite using `[loc_same, loc_same]`. Both sides reduce to the same expression. Establish `hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))` using `fun e => hu (GlobalTheory.LFun.eq_of_not_isSplit hns e rfl)`.

Rewrite using `[loc_ne hu', loc_ne hu, map_one]`. Establish `hq : (GlobalTheory.GalOfCusp.quadChar E).1 (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) = -1`. Express the relevant statement in the definitionally equal form `Units.map _ (GlobalTheory.IdeleNormChar.normSign E (Neutral.B1.localIdele _ _ ϖ)) = -1`. Rewrite using `[GlobalTheory.LFun.normSign_localIdele]`. Establish `hne` using `fun h => GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hns hun hϖ (GlobalTheory.QuadSymbol.eta_eq_one_iff.1 h)`.

Break down `Int.units_eq_one_or (GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E _ ϖ) with h | h` into its components or cases. Conclude with `absurd h hne`. Rewrite using `[h]`. Use `ext`. Simplify using the standard rewrite rules.

Establish `hval : μ.loc w ϖE = -1`. Express the relevant statement in the definitionally equal form `μ.1 (Neutral.B1.localIdele E w ϖE) = -1`. Rewrite using `[← hid, hres, hq]`. Establish `hunr : GlobalTheory.SplitWeil.IsUnram (μ.loc w)` using `fun x hx => hunit w x hw (valued_eq_one w hx)`. Rewrite using `[GlobalTheory.SmGL.eq_unrChar hunr (valuation_eq_uniformizer w hvE), hval]`.
-/
theorem inert_character_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  intro E _ _ _ hU μ hres hunit w hw
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    intro hs
    obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    apply hw
    rcases eq_or_ne a w with rfl | haw
    · exact ⟨b, hab.symm, hb⟩
    · exact ⟨a, haw, ha⟩
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
    obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hns hu rfl
    have := u.isPrime
    exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (hU u)
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := GlobalTheory.LFun.isUnram_iff.1 hun w rfl
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (w.under (𝓞 (maximalRealSubfield E)))
  set ϖE : (w.adicCompletion E)ˣ := Units.map (finiteCompletionMap (maximalRealSubfield E) E w).toMonoidHom ϖ with hϖE
  have hvE : Valued.v (ϖE : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (finiteCompletionMap (maximalRealSubfield E) E w ϖ) = _
    rw [← GlobalTheory.CharTransport.locMap_eq, ← GlobalTheory.LFun.complMap_rfl, GlobalTheory.LFun.valued_complMap rfl ϖ.ne_zero, he, pow_one]
    exact hϖ
  have hid : ideleMap (maximalRealSubfield E) E (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) =
      Neutral.B1.localIdele E w ϖE := by
    refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
    · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E)
    · rw [ideleMap_apply]
      by_cases hu : u = w
      · subst hu
        rw [loc_same, loc_same]
        rfl
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hu (GlobalTheory.LFun.eq_of_not_isSplit hns e rfl)
        rw [loc_ne hu', loc_ne hu, map_one]
  have hq : (GlobalTheory.GalOfCusp.quadChar E).1 (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) = -1 := by
    change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (Neutral.B1.localIdele _ _ ϖ)) = -1
    rw [GlobalTheory.LFun.normSign_localIdele]
    have hne := fun h => GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hns hun hϖ (GlobalTheory.QuadSymbol.eta_eq_one_iff.1 h)
    rcases Int.units_eq_one_or (GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E _ ϖ) with h | h
    · exact absurd h hne
    · rw [h]; ext; simp
  have hval : μ.loc w ϖE = -1 := by
    change μ.1 (Neutral.B1.localIdele E w ϖE) = -1
    rw [← hid, hres, hq]
  have hunr : GlobalTheory.SplitWeil.IsUnram (μ.loc w) := fun x hx => hunit w x hw (valued_eq_one w hx)
  rw [GlobalTheory.SmGL.eq_unrChar hunr (valuation_eq_uniformizer w hvE), hval]

end PositivityTheory.Rg.BcB.F.Fok.Mu3Aux1
