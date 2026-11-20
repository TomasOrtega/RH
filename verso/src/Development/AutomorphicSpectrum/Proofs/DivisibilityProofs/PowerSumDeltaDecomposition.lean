import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalPowerSumStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

def lieRank {Ψ : Type} (N j : ℕ) (s : Ψ ⊕ Ψ) : ℝ := if s.isLeft then (j : ℝ) else ((N - j : ℕ) : ℝ)

/- English proof (translation)
Establish `h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).map Fin.valEmbedding = Finset.range j`. Use extensionality with `a`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `hi`. Introduce `ha`. Conclude with `⟨⟨a, lt_of_lt_of_le ha hj⟩, ha, rfl⟩`. Rewrite using `[← Finset.card_map Fin.valEmbedding, h, Finset.card_range]`.
-/
theorem delta_card_filter_lt {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := by
  have h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).map Fin.valEmbedding = Finset.range j := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro ha
      exact ⟨⟨a, lt_of_lt_of_le ha hj⟩, ha, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_range]

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)`. Simplify using `only [not_lt, Finset.card_univ, Fintype.card_fin] at h`. Rewrite `h` using `[delta_card_filter_lt hj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem delta_card_filter_ge {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  rw [delta_card_filter_lt hj] at h
  omega

/- English proof (translation)
Consider the cases of `s with`. Consider the case `inl τ`. Simplify using `only [pLie, pkLow, pow_zero, Finset.sum_const, delta_card_filter_lt hj, lieRank, Sum.isLeft_inl, if_true, nsmul_eq_mul, mul_one, map_natCast]`. Consider the case `inr τ`. Simplify using `only [pLie, pow_zero, Finset.sum_const, delta_card_filter_ge hj, lieRank, Sum.isLeft_inr, Bool.false_eq_true, if_false, nsmul_eq_mul, mul_one, map_natCast]`.
-/
theorem pLie_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (s : Ψ ⊕ Ψ) :
    (pLie j 0 s : RP Ψ N) = C (lieRank N j s) := by
  cases s with
  | inl τ =>
    simp only [pLie, pkLow, pow_zero, Finset.sum_const, delta_card_filter_lt hj, lieRank, Sum.isLeft_inl, if_true,
      nsmul_eq_mul, mul_one, map_natCast]
  | inr τ =>
    simp only [pLie, pow_zero, Finset.sum_const, delta_card_filter_ge hj, lieRank, Sum.isLeft_inr,
      Bool.false_eq_true, if_false, nsmul_eq_mul, mul_one, map_natCast]

/- English proof (translation)
Simplify using `only [degFl, coeff_C_mul]`. Establish `h : ∀ f g : (Ψ → Equiv.Perm (Fin N)) → ℝ, ∑ σ, f σ * (c * g σ) = c * ∑ σ, f σ * g σ`. Introduce `f g`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun _ _ => by ring)`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degFl_C_mul {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (c : ℝ) (Q : RP Ψ N) :
    degFl (C c * Q) = c * degFl Q := by
  simp only [degFl, coeff_C_mul]
  have h : ∀ f g : (Ψ → Equiv.Perm (Fin N)) → ℝ, ∑ σ, f σ * (c * g σ) = c * ∑ σ, f σ * g σ := by
    intro f g
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h]
  ring

/- English proof (translation)
Introduce `Ψ _ _ N j frob hj hN hF`. Break down `isEmpty_or_nonempty Ψ with hE | ⟨⟨τ₀⟩⟩` into its components or cases. Conclude with `⟨0, fun _ τ => isEmptyElim τ⟩`. Use `⟨fun p => Real.log p / N * ∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n), ?_⟩` and prove the remaining obligations. Introduce `p τ k Q hp hk`.

Establish `hN' : (N : ℝ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hSh : ∑ σ, Sh j σ (pk τ k * Q) = k * degFl (pkLow j τ (k - 1) * Q)`. Rewrite using `[Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).1)]`. Simplify using the standard rewrite rules. Establish `hTot : ∑ σ, Tot σ (pk τ k * Q) = if k = 1 then N * degFl Q else 0`.

Rewrite using `[Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).2)]`. Apply the tactic sequence `by_cases h1 : k = 1 <;> simp [h1]`. Rewrite using `[hSh, hTot]`. Distinguish the cases in `h1 : k = 1`. Substitute `h1` using the available equality.

Establish `hrank : ∀ n, degFl (pLie j (1 - 1) (frob p τ n) * Q) = lieRank N j (frob p τ₀ n) * degFl Q`. Introduce `n`. Establish `: lieRank N j (frob p τ n) = lieRank N j (frob p τ₀ n)`. Simplify using `only [lieRank, hF p n τ τ₀]`. Rewrite using `[Nat.sub_self, pLie_zero hj, degFl_C_mul, this]`.

Establish `hsum : (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * degFl (pLie j (1 - 1) (frob p τ n) * Q)) = (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n)) * degFl Q`. Rewrite using `[← tsum_mul_right]`. Conclude with `tsum_congr (fun n => by rw [hrank]; ring)`. Simplify using `only [deltaTerm, restTerm, hsum]`. Simplify using `only [if_true, Nat.one_lt_ofNat, Nat.not_ofNat_le_one, if_false]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : 2 ≤ k` using `by omega`. Simplify using `only [deltaTerm, restTerm, h1, if_false, h2, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaTerm_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), j ≤ N → 0 < N → FrobShape frob → ∃ κ : ℕ → ℝ, ∀ (p : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), 2 ≤ p → 1 ≤ k → deltaTerm j p τ (frob p τ) k Q = -(Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh j σ (pk τ k * Q) + κ p * ∑ σ, Tot σ (pk τ k * Q) + restTerm j p (frob p τ) k Q := by
  intro Ψ _ _ N j frob hj hN hF
  rcases isEmpty_or_nonempty Ψ with hE | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun _ τ => isEmptyElim τ⟩
  refine ⟨fun p => Real.log p / N * ∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n), ?_⟩
  intro p τ k Q hp hk
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hSh : ∑ σ, Sh j σ (pk τ k * Q) = k * degFl (pkLow j τ (k - 1) * Q) := by
    rw [Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).1)]
    simp
  have hTot : ∑ σ, Tot σ (pk τ k * Q) = if k = 1 then N * degFl Q else 0 := by
    rw [Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).2)]
    by_cases h1 : k = 1 <;> simp [h1]
  rw [hSh, hTot]
  by_cases h1 : k = 1
  · subst h1
    have hrank : ∀ n, degFl (pLie j (1 - 1) (frob p τ n) * Q) =
        lieRank N j (frob p τ₀ n) * degFl Q := by
      intro n
      have : lieRank N j (frob p τ n) = lieRank N j (frob p τ₀ n) := by
        simp only [lieRank, hF p n τ τ₀]
      rw [Nat.sub_self, pLie_zero hj, degFl_C_mul, this]
    have hsum : (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * degFl (pLie j (1 - 1) (frob p τ n) * Q)) =
        (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n)) * degFl Q := by
      rw [← tsum_mul_right]
      exact tsum_congr (fun n => by rw [hrank]; ring)
    simp only [deltaTerm, restTerm, hsum]
    simp only [if_true, Nat.one_lt_ofNat, Nat.not_ofNat_le_one, if_false]
    field_simp
    ring
  · have h2 : 2 ≤ k := by omega
    simp only [deltaTerm, restTerm, h1, if_false, h2, if_true]
    ring

end GlobalTheory.CompanionTheory.Ar.Top
