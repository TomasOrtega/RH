import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PlainTorOfPs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open private ex_emb from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HodgeTateWeightsOfLocalGlobal
namespace UpperTheory.V.Z.Ord.AtLOrdinary
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
/- English proof (translation)
Establish `hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2))` using `fun i => (hs i).mul (isSmoothChar_absPow _)`. Establish `hsup` using `hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩ (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)`. Use `⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hy`. Both sides reduce to the same expression.

Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hy`. Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 hz`. Rewrite `e'` using `[IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Establish `h1 : absPow k ((1 : ℝ) : ℂ) = 1`. Use `mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')` as an intermediate fact. Simplify using `using this.symm`. Conclude with `one_ne_zero (absPow_ofReal_eq_one.1 h1)`. Take `⟨y, hy⟩` from `hd i j hij`.

Establish `h1` using `DFunLike.congr_fun e' (y : kˣ)`. Simplify using `only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1`. Conclude with `hy h1`.
-/
private theorem plainTor_of_ps [CharZero k] {n : ℕ} (σ : SmIrr (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo k, ω i y ≠ ω j y) (e : σ.ρ.Equiv (PS ω)) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2)) := fun i => (hs i).mul (isSmoothChar_absPow _)
  have hsup := hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)
  refine ⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e'
    by_cases hij : i = j
    · subst hij
      have h1 : absPow k ((1 : ℝ) : ℂ) = 1 := by
        have := mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')
        simpa using this.symm
      exact one_ne_zero (absPow_ofReal_eq_one.1 h1)
    · obtain ⟨y, hy⟩ := hd i j hij
      have h1 := DFunLike.congr_fun e' (y : kˣ)
      simp only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1
      exact hy h1
end UpperTheory.V.Z.Ord.AtLOrdinary
open UpperTheory.V.Z.Ord.AtLOrdinary in
/- English proof (translation)
Introduce `_ l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw ω hs hd ⟨e⟩ rc hrc _ O _ _ _ Bw hj`. Use `haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective`. Establish `hP` using `plainTor_of_ps τ ω hs hd e`. Establish `hG : Win.Gd (rc (algNorm τ))` using `UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP`. Take `⟨h1, h2⟩` from `hHT hP A h O Bw hj`.

Use `⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩` from `ex_emb h Bw hj t LL' τ' hτ`. Establish `e : HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _))`. Use `Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_` and prove the remaining obligations. Rewrite using `[hw j]`.

Simplify using `only [infOfWeight, Multiset.map_map]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [htW, lowW, Function.comp_apply, DomWeight.dual]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3` using `h2 _ LL' τ' hτ`. Rewrite `h3` using `[e]`. Conclude with `h3`. Rewrite using `[((hLG A h rc hrc).2 O Bw hj hG).2]`.
-/
theorem UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → AtLOf := by
  intro _ l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw ω hs hd ⟨e⟩ rc hrc _ O _ _ _ Bw hj
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  have hP := plainTor_of_ps τ ω hs hd e
  have hG : Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  obtain ⟨h1, h2⟩ := hHT hP A h O Bw hj
  refine ⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨j, rfl⟩ := ex_emb h Bw hj t LL' τ' hτ
    have e : HT (j.1.comp (algebraMap L _)) =
        Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
      refine Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_
      rw [hw j]
      simp only [infOfWeight, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [htW, lowW, Function.comp_apply, DomWeight.dual]
      push_cast
      ring
    have h3 := h2 _ LL' τ' hτ
    rw [e] at h3
    exact h3
  · rw [((hLG A h rc hrc).2 O Bw hj hG).2]
end
