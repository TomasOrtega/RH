import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentres
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
open GlobalTheory.PolFan.StarGap

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap

/- English proof (translation)
Introduce `O _ _ _ _ bar _ q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp`. Establish `hfan` using `hψ X hX`. Take `⟨-, hge, heq⟩` from `hsw`. Establish `hmem : toReal β ∈ psdCone bar X`. Use `ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ) (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)` as an intermediate fact.

Simplify using `using this`. Take `⟨S, -, hS⟩` from `hfan.finite`. Take `⟨e, m', δ₀, c, hδ₀, -, hc, he⟩` from `hS _ hmem`. Use `set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef`. Establish `hδ : IsCell bar ψ δ` using `CarDim.isCell_pull_equiv hδ₀ e.symm`.

Establish `hβc : toReal β = ∑ i, c i • toReal (δ i)` using `LinearMap.ext₂ fun a b => by`. Use `LinearMap.congr_fun₂ he (e.symm a) (e.symm b)` as an intermediate fact. Simplify `this` using `[hδdef, LinearMap.sum_apply]`. Rewrite using `[← evalR_toReal]`. Use `evalR_starDepth_le _ bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_` and prove the remaining obligations.

Introduce and unpack `v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩`. Establish `hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v`. Take `⟨n, hn⟩` from `hfan.integral v hv hvp`. Establish `h0` using `hge v hv hvp`. Establish `hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v` using `fun h => by`.

Take `⟨k, a, hk, hka⟩` from `heq v hv hvp h`. Take `⟨g, hg, hgs⟩` from `StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num) (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)`. Use `hno v hv hvp ⟨g, hg, by simpa using hgs⟩` as an intermediate fact. Rewrite `this` using `[hwv]`. Conclude with `one_ne_zero this`.

Establish `hlt` using `lt_of_le_of_ne h0 hne`. Rewrite `hlt`, the goal using `[hn]`. Establish `h1 : (N : ℤ) * n < ℓ v` using `by exact_mod_cast hlt`. Establish `h2 : (1 : ℤ) ≤ ℓ v - N * n` using `by omega`. Conclude with `h2` after adjusting the coercions.

Establish `hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i)`. Establish `: toReal β = t • toReal v + (toReal β - t • toReal v)` using `by abel`. Rewrite using `[this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]`. Establish `e1` using `gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'`.

Establish `e2` using `gap_eq_sum N ℓ hδ.linear hb hvb`. Establish `e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i))` using `Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))`. Establish `e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) + ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i))`. Rewrite using `[e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Rewrite using `[e4]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hv1 ht.le]`.
-/
theorem starDepth_le_gap : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith bar ψ N ℓ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (starDepth bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  intro O _ _ _ _ bar _ q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp
  have hfan := hψ X hX
  obtain ⟨-, hge, heq⟩ := hsw

  have hmem : toReal β ∈ psdCone bar X := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m', δ₀, c, hδ₀, -, hc, he⟩ := hS _ hmem
  set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef
  have hδ : IsCell bar ψ δ := CarDim.isCell_pull_equiv hδ₀ e.symm
  have hβc : toReal β = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [hδdef, LinearMap.sum_apply] using this
  rw [← evalR_toReal]
  refine evalR_starDepth_le _ bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_
  rintro v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩

  have hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v := by
    obtain ⟨n, hn⟩ := hfan.integral v hv hvp
    have h0 := hge v hv hvp
    have hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v := fun h => by
      obtain ⟨k, a, hk, hka⟩ := heq v hv hvp h
      obtain ⟨g, hg, hgs⟩ := StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num)
        (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)
      have := hno v hv hvp ⟨g, hg, by simpa using hgs⟩
      rw [hwv] at this
      exact one_ne_zero this
    have hlt := lt_of_le_of_ne h0 hne
    rw [hn] at hlt ⊢
    have h1 : (N : ℤ) * n < ℓ v := by exact_mod_cast hlt
    have h2 : (1 : ℤ) ≤ ℓ v - N * n := by omega
    exact_mod_cast h2
  have hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i) := by
    have : toReal β = t • toReal v + (toReal β - t • toReal v) := by abel
    rw [this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]
  have e1 := gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'
  have e2 := gap_eq_sum N ℓ hδ.linear hb hvb
  have e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))
  have e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) +
      ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left hv1 ht.le]

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap
