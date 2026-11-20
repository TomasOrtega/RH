import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DirSeries
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopSeries

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FarP

/- English proof (translation)
Introduce `m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD hS _ _ μ _ _ Q N ρ ψ a b D M hρ hψ hab hDd hM hid`. Use `⟨⟨t, ?_⟩, FarP.klaw hS hD⟩` and prove the remaining obligations. Introduce `z hz g y`. Establish `key : ∀ (F : M2 n → ℂ) (x : M2 n), rC (lowQ Q) F x = deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 + Complex.I * deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir …`. Introduce `F x`.

Simplify using `only [rC, dir1, dir2, if_true]`. Both sides reduce to the same expression. Use `choose y₀ C hyC using fun q : GlobalTheory.Eis.Cosets Pp Γ => FarP.termSplit hS hD z (↑(Quotient.out q) * g)`. Establish `d1` using `FarP.dirSeries hC hF hD hz (lowQ Q) true g y y₀ C hyC`. Establish `d2` using `FarP.dirSeries hC hF hD hz (lowQ Q) false g y y₀ C hyC`.

Establish `tp` using `fun l : Fin N => FarP.topSeries hS hD μ hz (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y y₀ C hyC`. Establish `hq : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 + Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp …`. Introduce `q`. Establish `h` using `hid (z - s₀) (mR (y₀ q * y)) (y₀ q * y).2`. Rewrite `h` using `[key]`.

Conclude with `h`. Rewrite using `[key, d1.2, d2.2, Finset.sum_congr rfl (fun l _ => by rw [(tp l).2])]`. Establish `e1 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 + Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = t …`. Rewrite using `[← tsum_mul_left, ← tsum_mul_left, ← (d1.1.mul_left _).tsum_add (d2.1.mul_left _)]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 + Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = t …`. Establish `hq2 : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 + Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSp …`. Introduce `q`.

Rewrite using `[hq q, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun l _ => by ring)`. Rewrite using `[tsum_congr hq2]`. Rewrite using `[Summable.tsum_finsetSum (fun l _ => ((tp l).1.mul_left (M l (z - s₀))))]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Rewrite using `[← tsum_mul_left]`. Establish `e3` using `e1.symm.trans e2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e3, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem farId_of (hC : CurveGR) (hF : FzDer) : FarId := by
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD hS _ _ μ _ _ Q N ρ ψ a b D M hρ hψ hab hDd hM hid
  refine ⟨⟨t, ?_⟩, FarP.klaw hS hD⟩
  intro z hz g y
  have key : ∀ (F : M2 n → ℂ) (x : M2 n), rC (lowQ Q) F x =
      deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 := by
    intro F x
    simp only [rC, dir1, dir2, if_true]
    rfl
  choose y₀ C hyC using fun q : GlobalTheory.Eis.Cosets Pp Γ => FarP.termSplit hS hD z (↑(Quotient.out q) * g)
  have d1 := FarP.dirSeries hC hF hD hz (lowQ Q) true g y y₀ C hyC
  have d2 := FarP.dirSeries hC hF hD hz (lowQ Q) false g y y₀ C hyC
  have tp := fun l : Fin N => FarP.topSeries hS hD μ hz (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1
    (hab l).1 (hab l).2 g y y₀ C hyC
  have hq : ∀ q : GlobalTheory.Eis.Cosets Pp Γ,
      D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0) =
      ∑ l : Fin N, M l (z - s₀) * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y)) := by
    intro q
    have h := hid (z - s₀) (mR (y₀ q * y)) (y₀ q * y).2
    rw [key] at h
    exact h
  rw [key, d1.2, d2.2, Finset.sum_congr rfl (fun l _ => by rw [(tp l).2])]
  have e1 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
      D (z - s₀) * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        D (z - s₀) * Complex.I * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (d1.1.mul_left _).tsum_add (d2.1.mul_left _)]
    congr 1
    funext q
    ring
  have e2 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
      ∑ l : Fin N, M l (z - s₀) * ∑' q, C q * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y)) := by
    have hq2 : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
        ∑ l : Fin N, M l (z - s₀) * (C q * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y))) := by
      intro q
      rw [hq q, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [tsum_congr hq2]
    rw [Summable.tsum_finsetSum (fun l _ => ((tp l).1.mul_left (M l (z - s₀))))]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← tsum_mul_left]
  have e3 := e1.symm.trans e2
  calc D (z - s₀) * (Polynomial.eval z d * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * (Polynomial.eval z d * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0))
        = Polynomial.eval z d * (D (z - s₀) * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        D (z - s₀) * Complex.I * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0) := by ring
    _ = _ := by
      rw [e3, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring

end PositivityTheory.Rg.Sw.HSt
