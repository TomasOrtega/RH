import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DomCongr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish `e : ∀ s : X.Ψ → ℝ, P (X.flow ξ (fun τ => (s τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x)` using `fun s => h _ (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)`. Unfold `Data.fj`. Simplify using `only [e]`.
-/
theorem fj_eq_of_eqOn (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {P Q : Frame X.Ψ r → ℂ} (h : ∀ x ∈ X.dom, P x = Q x) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ ν P x = X.fj la ξ ν Q x := by
  have e : ∀ s : X.Ψ → ℝ, P (X.flow ξ (fun τ => (s τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    fun s => h _ (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)
  unfold Data.fj
  simp only [e]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP ⊢`. Take `⟨hd, hb, hg⟩` from `hP`. Use `⟨hd.congr fun x hx => (hPQ x hx).symm, fun x hx b hb' => ?_, fun γ hγ x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb'), ← hPQ x hx, hb x hx b hb']`. Rewrite using `[← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← hPQ x hx, hg γ hγ x hx]`.
-/
private lemma isSec_of_eqOn_dom {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) (hP : X.IsSec la P) : X.IsSec la Q := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP ⊢
  obtain ⟨hd, hb, hg⟩ := hP
  refine ⟨hd.congr fun x hx => (hPQ x hx).symm, fun x hx b hb' => ?_, fun γ hγ x hx => ?_⟩
  · rw [← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb'), ← hPQ x hx, hb x hx b hb']
  · rw [← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← hPQ x hx, hg γ hγ x hx]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPQ x hx]`.
-/
private lemma pnorm_eq_of_eqOn_dom (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x = X.pnorm la Q x := by
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPQ x hx]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Establish `key : ∀ s : ↥X.Ψ → ℝ, P (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) = Q (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x)` using `fun s => hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx)`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj`. Simplify using `only [key]`.
-/
private lemma fj_eq_of_eqOn_dom (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) {ξ : Fin r → E} (hξ : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0)
    (ν : ↥X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ ν P x = X.fj la ξ ν Q x := by
  have key : ∀ s : ↥X.Ψ → ℝ, P (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) =
      Q (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) :=
    fun s => hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj
  simp only [key]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

/- English proof (translation)
Introduce `E _ _ _ r X la P Q hPQ`. Establish `hB : X.IsBddSec la P → X.IsBddSec la Q`. Introduce `hP`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsBddSec at hP ⊢`. Take `⟨hs, C, hC⟩` from `hP`.

Conclude with `⟨isSec_of_eqOn_dom X hPQ hs, C, fun x hx => (pnorm_eq_of_eqOn_dom X la hPQ hx) ▸ hC x hx⟩`. Use `⟨hB, fun hP => ?_⟩` and prove the remaining obligations. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP ⊢`. Take `⟨hb, hc⟩` from `hP`. Use `⟨hB hb, fun ξ hξ x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[← fj_eq_of_eqOn_dom X la hPQ (by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIso at hξ; exact hξ.2.1) 0 hx]`. Conclude with `hc ξ hξ x hx`.
-/
theorem _root_.GlobalTheory.DomCongr.bddSec_cusp_congr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∀ (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ),
    (∀ x ∈ X.dom, P x = Q x) → (X.IsBddSec la P → X.IsBddSec la Q) ∧
      (P ∈ X.SS la → Q ∈ X.SS la) := by
  intro E _ _ _ r X la P Q hPQ
  have hB : X.IsBddSec la P → X.IsBddSec la Q := by
    intro hP
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsBddSec at hP ⊢
    obtain ⟨hs, C, hC⟩ := hP
    exact ⟨isSec_of_eqOn_dom X hPQ hs, C,
      fun x hx => (pnorm_eq_of_eqOn_dom X la hPQ hx) ▸ hC x hx⟩
  refine ⟨hB, fun hP => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP ⊢
  obtain ⟨hb, hc⟩ := hP
  refine ⟨hB hb, fun ξ hξ x hx => ?_⟩
  rw [← fj_eq_of_eqOn_dom X la hPQ (by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIso at hξ; exact hξ.2.1) 0 hx]
  exact hc ξ hξ x hx

end GlobalTheory.DomCongr
