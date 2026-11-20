import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSixthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamilyStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => c (some k), fun k => hc _, ?_⟩
  funext p
  show z (v₀ k₀ p) = c (some p.1) * z' (v₀ k₀ p)
  rw [e]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · by_cases hk : k = k₀
    · simpa [hk] using hc none
    · simpa [hk] using hc (some k)
  · funext p
    show z (v₁ k₀ p) = (if p.1 = k₀ then c none else c (some p.1)) * z' (v₁ k₀ p)
    rw [e]
    by_cases hk : p.1 = k₀
    · obtain ⟨k, m⟩ := p
      obtain rfl : k = k₀ := hk
      simp [v₁_self]
    · rw [if_neg hk, v₁_ne hk]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Prove the first alternative. Prove the first alternative.

Prove the second alternative.
-/
theorem null_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ l : Fin BM.q, IsNull RW.A {x | FA.pr (q 0 x) ∈ BM.O l ∧ (FA.pr (q 0 x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p = 0 ∨ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hpr : HoloMap RW.A BM.Rb.A (FA.pr ∘ q 0) := Pr.holoMap_comp' (hq 0) FA.pr_holo
  have hdens := GlobalTheory.T.flag_adjacent_twisted_resolution_sixth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hn0 := GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => fstPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₀ k₀ p))
    (fun x y' hy => sameOrbit_fstPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).1⟩)
  have hn1 := GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => sndPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₁ k₀ p))
    (fun x y' hy => sameOrbit_sndPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).2⟩)
  intro i
  refine measure_mono_null ?_ (measure_union_null (hn0 i) (hn1 i))
  rintro w ⟨hw, hw'⟩
  obtain ⟨hO, hs | ⟨p, hp | hp⟩⟩ := hw'
  · exact Or.inl ⟨hw, hO, Or.inl hs⟩
  · exact Or.inl ⟨hw, hO, Or.inr ⟨p, hp⟩⟩
  · exact Or.inr ⟨hw, hO, Or.inr ⟨p, hp⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
