import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie

/- English proof (translation)
Take `⟨n, u, v, rfl⟩` from `Submodule.mem_span_set'.1 hg`. Use `choose f hf hv using fun i => (v i).2`. Use `⟨_, GlobalTheory.UpperModel.isBddSec_sum X (fun i => (hf i).1) u, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [← hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Apply the tactic sequence `by_cases hx : x ∈ X.dom <;> simp [hx]`.
-/
theorem exists_bddSec_of_mem_domSpan {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : Wt X.Ψ r) {g : Frame X.Ψ r → ℂ} (hg : g ∈ domSpan X (X.SS la)) :
    ∃ f, X.IsBddSec la f ∧ g = X.dom.indicator f := by
  obtain ⟨n, u, v, rfl⟩ := Submodule.mem_span_set'.1 hg
  choose f hf hv using fun i => (v i).2
  refine ⟨_, GlobalTheory.UpperModel.isBddSec_sum X (fun i => (hf i).1) u, ?_⟩
  funext x
  simp only [← hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ X.dom <;> simp [hx]

/- English proof (translation)
Introduce `E _ _ _ r X Xa Fl`. Establish `hr : Module.rank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ≤ ((Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) : ℕ) : Cardinal)`. Use `rank_le fun s hs => ?_` and prove the remaining obligations. Establish `hs'` using `(hs.map' _ (Submodule.ker_subtype _)).comp s.equivFin.symm s.equivFin.symm.injective`. Use `choose f hf hfe using fun q : Fin s.card => exists_bddSec_of_mem_domSpan X _ (s.equivFin.symm q).1.2`.

Use `GlobalTheory.UpperModel.upper E r X Xa Fl s.card f hf fun u hu => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Use `Fintype.linearIndependent_iff.1 hs' u ?_ q` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, Submodule.subtype_apply, hfe, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`.

Distinguish the cases in `hx : x ∈ X.dom`. Simplify `hu x hx` using `[hx]`. Simplify using `[hx]`. Conclude with `⟨Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0)), Module.finrank_le_of_rank_le hr⟩`.
-/
theorem finrank_domSpan_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), FiniteDimensional ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ∧ Module.finrank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) := by
  intro E _ _ _ r X Xa Fl
  have hr : Module.rank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ≤
      ((Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) : ℕ) : Cardinal) := by
    refine rank_le fun s hs => ?_
    have hs' := (hs.map' _ (Submodule.ker_subtype _)).comp s.equivFin.symm s.equivFin.symm.injective
    choose f hf hfe using fun q : Fin s.card =>
      exists_bddSec_of_mem_domSpan X _ (s.equivFin.symm q).1.2
    refine GlobalTheory.UpperModel.upper E r X Xa Fl s.card f hf fun u hu => ?_
    funext q
    refine Fintype.linearIndependent_iff.1 hs' u ?_ q
    funext x
    simp only [Function.comp, Submodule.subtype_apply, hfe, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    by_cases hx : x ∈ X.dom
    · simpa [hx] using hu x hx
    · simp [hx]
  exact ⟨Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0)), Module.finrank_le_of_rank_le hr⟩

end GlobalTheory.UpTie
