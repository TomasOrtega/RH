import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y e J h p hp t ht`. Take `⟨m, f, a, hf, ha, hsum, hcl⟩` from `h p hp`. Rewrite `hf`, `ha` using `[Algebra.adjoin_range_eq_range_aeval]`. Use `choose F hF using fun l => AlgHom.mem_range _ |>.1 (hf l)`. Use `choose A hA using fun l => AlgHom.mem_range _ |>.1 (ha l)`.

Choose the witnesses or unpack the hypotheses as in `rfl : f = fun l => aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) :=`. Use function extensionality and compare the values at `fun l => (hF l).symm`. Establish `hker : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (∑ l, A l * F l - 1) = 0`. Simplify using `only [map_sub, map_sum, map_mul, map_one, hA]`. Conclude with `sub_eq_zero.2 hsum`.

Establish `h1` using `ht _ hker`. Simplify using `only [map_sub, map_sum, map_mul, map_one] at h1`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, eval t (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Simplify using `[hc] at h1`. Establish `hfl : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) ≠ 0` using `fun h0 => hl (ht _ h0)`. Take `⟨-, z, n, -, -, hspan, hq⟩` from `hcl l hfl _ rfl`. Conclude with `⟨F l, _, z, n, hfl, hl, rfl, hspan, hq⟩`.
-/
theorem exists_basicOpen_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), IsSncModel y e J → ∀ p : (k : K) → ι k, (∀ k, y ⟨k, p k⟩ ≠ 0) → ∀ t : (Σ k, ι k) → ℂ, (∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → ∃ (F : MvPolynomial (Σ k, ι k) ℚ) (S : Subalgebra ℚ Ω) (z : Fin e → S) (n : ℕ), aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F ≠ 0 ∧ eval t (map (algebraMap ℚ ℂ) F) ≠ 0 ∧ S = Algebra.adjoin ℚ (insert (aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F)⁻¹ (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩))) ∧ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧ ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  intro K _ ι _ Ω _ _ y e J h p hp t ht
  obtain ⟨m, f, a, hf, ha, hsum, hcl⟩ := h p hp
  rw [Algebra.adjoin_range_eq_range_aeval] at hf ha
  choose F hF using fun l => AlgHom.mem_range _ |>.1 (hf l)
  choose A hA using fun l => AlgHom.mem_range _ |>.1 (ha l)
  obtain rfl : f = fun l => aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) :=
    funext fun l => (hF l).symm
  have hker : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (∑ l, A l * F l - 1) = 0 := by
    simp only [map_sub, map_sum, map_mul, map_one, hA]
    exact sub_eq_zero.2 hsum
  have h1 := ht _ hker
  simp only [map_sub, map_sum, map_mul, map_one] at h1
  obtain ⟨l, hl⟩ : ∃ l, eval t (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h1
  have hfl : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) ≠ 0 := fun h0 => hl (ht _ h0)
  obtain ⟨-, z, n, -, -, hspan, hq⟩ := hcl l hfl _ rfl
  exact ⟨F l, _, z, n, hfl, hl, rfl, hspan, hq⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
