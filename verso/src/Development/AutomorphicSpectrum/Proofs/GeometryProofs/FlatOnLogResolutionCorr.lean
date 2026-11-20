import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

/- English proof (translation)
Introduce `K _ J _ P Jd D R Ψ N T hT a x _`. Consider the cases of `a with`. Consider the case `none`. Use `⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => ?_⟩` and prove the remaining obligations. Simplify using `[potOf, corr, Top.trivLine, LocPot.ofFun]`.

Consider the case `some r => choose V hVo hxV G hG hE using fun k : Fin N => hT (r.1, k) x (Set.mem_univ x)`. Use `⟨R.U x ∩ ⋂ k, V k, (R.isOpen_U x).inter (isOpen_iInter_of_finite hVo), ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => -∑ k ∈ Finset.Iic r.2, G k y, fun j w hw => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hs : ∀ k ∈ Finset.Iic r.2, AnalyticAt ℂ (G k ∘ (R.A.chart j).symm) w` using `fun k _ => hG k j w ⟨hw.1, Set.mem_iInter.1 hw.2.2 k⟩`. Conclude with `(Finset.analyticAt_fun_sum _ hs).neg`. Establish `hm` using `(R.mem x y hy.1).1`.

Establish `e : (potOf R (corr T (some r))).φ x y = -∑ k ∈ Finset.Iic r.2, Real.log ((T (r.1, k)).h (R.lift x y))` using `log_stepLine (fun k => T (r.1, k)) r.2 hm`. Establish `e' : ∀ k, Real.log ((T (r.1, k)).h (R.lift x y)) = (G k y).re` using `fun k => by`. Simplify `hE k y (Set.mem_iInter.1 hy.2 k)` using `[potOf, LocPot.ofFun]`. Simplify using `[e, e', LocPot.ofFun]`.
-/
theorem isFlatOn_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  intro K _ J _ P Jd D R Ψ N T hT a x _
  cases a with
  | none =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => ?_⟩
    simp [potOf, corr, Top.trivLine, LocPot.ofFun]
  | some r =>
    choose V hVo hxV G hG hE using fun k : Fin N => hT (r.1, k) x (Set.mem_univ x)
    refine ⟨R.U x ∩ ⋂ k, V k, (R.isOpen_U x).inter (isOpen_iInter_of_finite hVo),
      ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => -∑ k ∈ Finset.Iic r.2, G k y, fun j w hw => ?_, fun y hy => ?_⟩
    · have hs : ∀ k ∈ Finset.Iic r.2, AnalyticAt ℂ (G k ∘ (R.A.chart j).symm) w := fun k _ =>
        hG k j w ⟨hw.1, Set.mem_iInter.1 hw.2.2 k⟩
      exact (Finset.analyticAt_fun_sum _ hs).neg
    · have hm := (R.mem x y hy.1).1
      have e : (potOf R (corr T (some r))).φ x y = -∑ k ∈ Finset.Iic r.2, Real.log ((T (r.1, k)).h (R.lift x y)) :=
        log_stepLine (fun k => T (r.1, k)) r.2 hm
      have e' : ∀ k, Real.log ((T (r.1, k)).h (R.lift x y)) = (G k y).re := fun k => by
        simpa [potOf, LocPot.ofFun] using hE k y (Set.mem_iInter.1 hy.2 k)
      simp [e, e', LocPot.ofFun]

end GlobalTheory.CompanionTheory.Ar.Chg
