import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

/- English proof (translation)
Establish `h1 : p * m = p * (m % r) + r * (p * (m / r))` using `by conv_lhs => rw [← Nat.mod_add_div m r]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : p * m / r = p * (m % r) / r + p * (m / r)`. Rewrite using `[h1, Nat.add_mul_div_left _ _ hr]`. Establish `h4 : p * (m % r) < p * r` using `Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m hr) hp`.

Establish `h3 : p * (m % r) / r < p` using `(Nat.div_lt_iff_lt_mul hr).2 h4`. Rewrite using `[h2]`. Generalize the expression as in `p * (m % r) / r = q at h3 ⊢`. Generalize the expression as in `p * (m / r) = s`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem GlobalTheory.nat_mul_div_bounds_rounded_multiples (p r m : ℕ) (hp : 0 < p) (hr : 0 < r) :
    p * (m / r) ≤ p * m / r ∧ p * m / r + 1 ≤ p * (m / r) + p := by
  have h1 : p * m = p * (m % r) + r * (p * (m / r)) := by
    conv_lhs => rw [← Nat.mod_add_div m r]
    ring
  have h2 : p * m / r = p * (m % r) / r + p * (m / r) := by
    rw [h1, Nat.add_mul_div_left _ _ hr]
  have h4 : p * (m % r) < p * r := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m hr) hp
  have h3 : p * (m % r) / r < p := (Nat.div_lt_iff_lt_mul hr).2 h4
  rw [h2]
  generalize p * (m % r) / r = q at h3 ⊢
  generalize p * (m / r) = s
  constructor <;> omega

/- English proof (translation)
Introduce `X _ p C _ E M Kc r b hp hr e`. Establish `hm : ∀ c, p ^ (e + 1) * b c = p * (p ^ e * b c)` using `fun c => by ring`. Use `⟨fun c => p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`. Use `GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr` as an intermediate fact.

Use `show p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r < p`. Rewrite using `[hm c]`. Use linear arithmetic over natural numbers and integers. Establish `hc : ∀ c, p • ((p ^ e * b c / r) • E c + E c) = (p ^ (e + 1) * b c / r) • E c + E c + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c`. Introduce `c`.

Use `GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr` as an intermediate fact. Establish `hk : p * (p ^ e * b c / r) + p = p ^ (e + 1) * b c / r + 1 + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r)`. Rewrite using `[hm c]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[smul_add, ← mul_smul, ← add_smul]`.

Use `conv_lhs => rw [hk]`. Rewrite using `[add_smul, add_smul, one_smul]`. Establish `hs : p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c) = ∑ c, (p ^ (e + 1) * b c / r) • E c + ∑ c, E c + ∑ c, (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c`. Rewrite using `[← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun c _ => hc c)`.

Establish `hs' : p • (p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) = p ^ (e + 1) • (M - Kc) - p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c)`. Rewrite using `[pow_succ', mul_smul, smul_sub, smul_sub, smul_add]`. Normalize the expressions using the abelian group laws. Use `beta_reduce`. Rewrite using `[hs', hs]`.

Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.rounded_multiples_step : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) {C : Type} [Fintype C] (E : C → CartierDiv X) (M Kc : CartierDiv X) (r : ℕ) (b : C → ℕ), 0 < p → 0 < r → ∀ e : ℕ, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) (e + 1) = p • (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) e + ∑ c, ρ c • E c := by
  intro X _ p C _ E M Kc r b hp hr e
  have hm : ∀ c, p ^ (e + 1) * b c = p * (p ^ e * b c) := fun c => by ring
  refine ⟨fun c => p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r, ?_, ?_⟩
  · intro c
    have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
    show p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r < p
    rw [hm c]
    omega
  · have hc : ∀ c, p • ((p ^ e * b c / r) • E c + E c)
        = (p ^ (e + 1) * b c / r) • E c + E c
          + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      intro c
      have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
      have hk : p * (p ^ e * b c / r) + p
          = p ^ (e + 1) * b c / r + 1 + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) := by
        rw [hm c]; omega
      rw [smul_add, ← mul_smul, ← add_smul]
      conv_lhs => rw [hk]
      rw [add_smul, add_smul, one_smul]
    have hs : p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c)
        = ∑ c, (p ^ (e + 1) * b c / r) • E c + ∑ c, E c
          + ∑ c, (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => hc c)
    have hs' : p • (p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c)
        = p ^ (e + 1) • (M - Kc) - p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c) := by
      rw [pow_succ', mul_smul, smul_sub, smul_sub, smul_add]; abel
    beta_reduce
    rw [hs', hs]
    abel
