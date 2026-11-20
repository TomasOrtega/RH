import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTermFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMaximalIdealOfTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTermTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndIsPrincipalPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanValueLimitDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolySumPowFibrePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterNumRedCloPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualEigOfHasDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamBaseGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermSumLocalEqGlobalStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.VdmCore

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hS hX h2 hH hA hV r hr D O hc hf A T H h`. Establish `hcut` using `@GlobalTheory.VdmCut.val_recursion`. Establish `hdeg` using `@GlobalTheory.DegRec.degAt_recursion`. Establish `hsect` using `@GlobalTheory.VdmRec.CutSec.exists_cuts`. Establish `hvert` using `@GlobalTheory.VertVanish.vertical_val_eq_zero`.

Establish `key : ∀ c (M : DRBase O c) (I : M.Emb) (e : ℕ) (z : M.B), I.Good z e → Tendsto (fun R => M.val R z e) atTop (𝓝 (r * (M.deg z (e + 1) : ℝ)))`. Introduce `c M I e`. Proceed by induction on `e with`. Consider the case `zero`. Introduce `z hz`.

Distinguish the cases in `hz0 : CharZero (M.B.residueField z)`. Conclude with `GlobalTheory.T.archimedean_value_limit_degree hX h2 hH hA r hr D O hc hf A T H h c M I z hz hz0`. Establish `e₁ : M.deg z (0 + 1) = 0` using `(hdeg _ _ M.q _ M.ar (M.lam 2)).1 z _ hz0`. Simplify using `only [hvert hX h2 hH hA hV D O hc hf A T H h c M I z hz hz0, e₁]`. Simplify using the standard rewrite rules.

Consider the case `succ e ih`. Introduce `z hz`. Take `⟨m, hm, s, hs⟩` from `hsect D O c M I z e hz`. Establish `hm' : (m : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `c₁` using `fun R => hcut h2.p4 _ _ M.q _ M.ar _ _ _ ((M.H R).pull M.b rfl) M.F (M.lam R) m s z e hz.1 hs.1`.

Establish `fin : (Function.support (cutMult (M.isLB_pow m) s z)).Finite` using `(c₁ 2).1`. Establish `d₁ : (m : ℤ) * M.deg z (e + 1 + 1) = ∑ᶠ w, cutMult (M.isLB_pow m) s z w * M.deg w (e + 1)` using `(hdeg _ _ M.q _ M.ar (M.lam 2)).2 m s z (e + 1) hz.1 hs.1`. Rewrite using `[finsum_eq_sum_of_support_subset (s := fin.toFinset) _ (fun w hw => by`. Simplify using `using left_ne_zero_of_mul hw)] at d₁`. Establish `v₁ (R : ℝ) : M.val R z (e + 1) = (∑ w ∈ fin.toFinset, (cutMult (M.isLB_pow m) s z w : ℝ) * M.val R w e - M.arch R m s z e) / m`.

Rewrite using `[eq_div_iff hm', mul_comm]`. Use `(c₁ R).2.trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `finsum_eq_sum_of_support_subset _ (fun w hw => by`. Use `left_ne_zero_of_mul hw` as an intermediate fact.

Conclude with `(Set.Finite.mem_toFinset fin).2 (Int.cast_ne_zero.1 this))`. Simplify using `only [v₁]`. Establish `t` using `((tendsto_finset_sum fin.toFinset fun w hw => (ih w (hs.2 w (by simpa using hw))).const_mul (cutMult (M.isLB_pow m) s z w : ℝ)).sub (GlobalTheory.T.archimedean_term_tendsto_zero hX h2 hH hA D O hc hf A T H h c M I z e m s hz hs)).div_const (m : ℝ)`. Use `t using 2` and compare the differences between its conclusion and the goal. Rewrite using `[eq_div_iff hm', sub_zero]`.

Establish `d₂` using `congrArg (Int.cast : ℤ → ℝ) d₁`. Move the coercions through the operations in `at d₂`. Simplify using `only [mul_left_comm _ r, ← Finset.mul_sum, ← d₂]`. Expand and normalize the polynomial expressions, which then agree. Establish `M : ∀ c, DRBase O c` using `fun c => (GlobalTheory.DRBaseEx.main hX h2 hH hA D O hc hf A T H h c).some`.

Take `⟨h1, hI⟩` from `GlobalTheory.T.de_rham_base_good_embedding hX h2 hH hA D O hc hf A T H h`. Rewrite using `[← GlobalTheory.HodgeDegSum.main hX h2 hH hA D O hc hf A T H h M, Finset.mul_sum]`. Establish `e₀ (R : ℝ) : vdmVal O.Y R = ∑ c, termL O c R`. Express the relevant statement in the definitionally equal form `(arIn O.s O.Φ O.met.hm).arMix ∅ R 1 _ = _`. Conclude with `LinearMap.sum_apply _ _ _`.

Use `(tendsto_finset_sum _ fun c _ => ?_ : Tendsto (fun R => ∑ c, termW O c R) _ _).congr' ((eventually_ge_atTop 2).mono fun R hR => ((e₀ R).trans (GlobalTheory.T.term_sum_local_eq_global hS hX h2 hH hA D O hc hf A T H h R hR)).symm)` and prove the remaining obligations. Take `⟨I, hg⟩` from `hI c (M c)`. Establish `t` using `(key c (M c) I _ _ hg).div_const (Module.finrank ℚ D.what₂.LL : ℝ)`. Rewrite `t` using `[Nat.sub_add_cancel h1, mul_div_assoc]`. Use `t.congr' ((eventually_ge_atTop 2).mono fun R hR => ?_)` and prove the remaining obligations.

Conclude with `(GlobalTheory.T.archimedean_term_formula hX h2 hH hA D O hc hf A T H h c (M c) R hR).symm`.
-/
theorem tendsto_vdmVal : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH →
    RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes → ∀ r : ℝ, Ch2Const r →
    OnObj fun D O _ _ _ _ => Tendsto (vdmVal O.Y) atTop
      (𝓝 (r * O.Y.chern (lamA D.what₂.Tau O.Y.N O.Y.j ^ dimGr D.what₂.Tau O.Y.N O.Y.j *
        vdmCl D.what₂.Tau O.Y.N O.Y.j))) := by
  intro hS hX h2 hH hA hV r hr D O hc hf A T H h
  have hcut := @GlobalTheory.VdmCut.val_recursion
  have hdeg := @GlobalTheory.DegRec.degAt_recursion
  have hsect := @GlobalTheory.VdmRec.CutSec.exists_cuts
  have hvert := @GlobalTheory.VertVanish.vertical_val_eq_zero
  have key : ∀ c (M : DRBase O c) (I : M.Emb) (e : ℕ) (z : M.B), I.Good z e →
      Tendsto (fun R => M.val R z e) atTop (𝓝 (r * (M.deg z (e + 1) : ℝ))) := by
    intro c M I e
    induction e with
    | zero =>
      intro z hz
      by_cases hz0 : CharZero (M.B.residueField z)
      · exact GlobalTheory.T.archimedean_value_limit_degree hX h2 hH hA r hr D O hc hf A T H h c M I z hz hz0
      · have e₁ : M.deg z (0 + 1) = 0 := (hdeg _ _ M.q _ M.ar (M.lam 2)).1 z _ hz0
        simp only [hvert hX h2 hH hA hV D O hc hf A T H h c M I z hz hz0, e₁]
        simp
    | succ e ih =>
      intro z hz
      obtain ⟨m, hm, s, hs⟩ := hsect D O c M I z e hz
      have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      have c₁ := fun R => hcut h2.p4 _ _ M.q _ M.ar _ _ _ ((M.H R).pull M.b rfl) M.F (M.lam R) m s z e hz.1 hs.1
      have fin : (Function.support (cutMult (M.isLB_pow m) s z)).Finite := (c₁ 2).1
      have d₁ : (m : ℤ) * M.deg z (e + 1 + 1) =
          ∑ᶠ w, cutMult (M.isLB_pow m) s z w * M.deg w (e + 1) :=
        (hdeg _ _ M.q _ M.ar (M.lam 2)).2 m s z (e + 1) hz.1 hs.1
      rw [finsum_eq_sum_of_support_subset (s := fin.toFinset) _ (fun w hw => by
        simpa using left_ne_zero_of_mul hw)] at d₁
      have v₁ (R : ℝ) : M.val R z (e + 1) =
          (∑ w ∈ fin.toFinset, (cutMult (M.isLB_pow m) s z w : ℝ) * M.val R w e -
            M.arch R m s z e) / m := by
        rw [eq_div_iff hm', mul_comm]
        refine (c₁ R).2.trans ?_
        congr 1
        exact finsum_eq_sum_of_support_subset _ (fun w hw => by
          have := left_ne_zero_of_mul hw
          exact (Set.Finite.mem_toFinset fin).2 (Int.cast_ne_zero.1 this))
      simp only [v₁]
      have t := ((tendsto_finset_sum fin.toFinset fun w hw =>
        (ih w (hs.2 w (by simpa using hw))).const_mul (cutMult (M.isLB_pow m) s z w : ℝ)).sub
          (GlobalTheory.T.archimedean_term_tendsto_zero hX h2 hH hA D O hc hf A T H h c M I z e m s hz hs)).div_const (m : ℝ)
      convert t using 2
      rw [eq_div_iff hm', sub_zero]
      have d₂ := congrArg (Int.cast : ℤ → ℝ) d₁
      push_cast at d₂
      simp only [mul_left_comm _ r, ← Finset.mul_sum, ← d₂]
      ring
  have M : ∀ c, DRBase O c := fun c => (GlobalTheory.DRBaseEx.main hX h2 hH hA D O hc hf A T H h c).some
  obtain ⟨h1, hI⟩ := GlobalTheory.T.de_rham_base_good_embedding hX h2 hH hA D O hc hf A T H h
  rw [← GlobalTheory.HodgeDegSum.main hX h2 hH hA D O hc hf A T H h M, Finset.mul_sum]
  have e₀ (R : ℝ) : vdmVal O.Y R = ∑ c, termL O c R := by
    change (arIn O.s O.Φ O.met.hm).arMix ∅ R 1 _ = _
    exact LinearMap.sum_apply _ _ _
  refine (tendsto_finset_sum _ fun c _ => ?_ :
    Tendsto (fun R => ∑ c, termW O c R) _ _).congr' ((eventually_ge_atTop 2).mono fun R hR =>
      ((e₀ R).trans (GlobalTheory.T.term_sum_local_eq_global hS hX h2 hH hA D O hc hf A T H h R hR)).symm)
  obtain ⟨I, hg⟩ := hI c (M c)
  have t := (key c (M c) I _ _ hg).div_const (Module.finrank ℚ D.what₂.LL : ℝ)
  rw [Nat.sub_add_cancel h1, mul_div_assoc] at t
  refine t.congr' ((eventually_ge_atTop 2).mono fun R hR => ?_)
  exact (GlobalTheory.T.archimedean_term_formula hX h2 hH hA D O hc hf A T H h c (M c) R hR).symm

end GlobalTheory.VdmCore
