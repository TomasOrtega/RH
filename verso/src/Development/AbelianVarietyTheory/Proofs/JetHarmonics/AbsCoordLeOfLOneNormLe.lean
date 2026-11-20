import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapSubsetOfSetBoundIntegral
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FamilyDegreeRatio

/- English proof (translation)
Take `⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hh, -, hq1, hq2, -⟩` from `H`. Distinguish the cases in `hc : c.val + 1 < k`. Combine the linear relations using `[hga a c hac hc]`. Distinguish the cases in `ha : a.val + 1 < k`. Establish `hp : k - 1 < 2 * r + k + 1` using `by omega`.

Establish `hq : k < 2 * r + k + 1` using `by omega`. Establish `hpq : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, hp⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, hq⟩`. Establish `h1 : ¬ (k < k - 1)` using `by omega`. Establish `h2 : (k - (k - 1)) % 2 = 1` using `by omega`. Simplify using `[PI.BesselPeriodGGP.eps48, h1, h2]`.

Establish `hgpq` using `hh _ _ hpq`. Establish `⟨p1, p2⟩` using `hnd ⟨k - 1, hp⟩ (by show k ≤ k - 1 + 1; omega)`. Establish `⟨q1, q2⟩` using `hnd ⟨k, hq⟩ (by show k ≤ k + 1; omega)`. Establish `habs : |lam ⟨k - 1, hp⟩ - lam ⟨k, hq⟩| ≤ bv` using `abs_le.mpr ⟨by linarith, by linarith⟩`. Establish `h1` using `(hcl a ha).1`.

Establish `h2` using `(hnd c (by omega)).2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hac' : a.val < c.val` using `hac`. Establish `hd : a.val + 1 < 2 * r + k + 1` using `by have := c.isLt; omega`. Establish `had : a < ⟨a.val + 1, hd⟩` using `by rw [Fin.lt_def]; simp`.

Establish `hdc : (⟨a.val + 1, hd⟩ : Fin (2 * r + k + 1)) ≤ c` using `by rw [Fin.le_iff_val_le_val]; simp; omega`. Establish `hne : PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r ⟨a.val + 1, hd⟩`. Establish `h1 : ¬ (a.val < k - 1)` using `by omega`. Establish `h2 : ¬ (a.val + 1 < k - 1)` using `by omega`. Break down `Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3` into its components or cases.

Establish `h4 : (a.val + 1 - (k - 1)) % 2 = 1` using `by omega`. Simplify using `[PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]`. Establish `h4 : (a.val + 1 - (k - 1)) % 2 = 0` using `by omega`. Simplify using `[PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]`. Establish `hg` using `hh _ _ hne`.

Establish `hlt` using `hanti had`. Establish `hle` using `hanti.antitone hdc`. Rewrite `hg` using `[abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_lam {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    (H : Num k r lam u b bv ga h q0) (a c : Fin (2 * r + k + 1)) (hac : a < c) :
    100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hh, -, hq1, hq2, -⟩ := H
  by_cases hc : c.val + 1 < k
  · linarith [hga a c hac hc]
  by_cases ha : a.val + 1 < k
  ·
    have hp : k - 1 < 2 * r + k + 1 := by omega
    have hq : k < 2 * r + k + 1 := by omega
    have hpq : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, hp⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, hq⟩ := by
      have h1 : ¬ (k < k - 1) := by omega
      have h2 : (k - (k - 1)) % 2 = 1 := by omega
      simp [PI.BesselPeriodGGP.eps48, h1, h2]
    have hgpq := hh _ _ hpq
    have ⟨p1, p2⟩ := hnd ⟨k - 1, hp⟩ (by show k ≤ k - 1 + 1; omega)
    have ⟨q1, q2⟩ := hnd ⟨k, hq⟩ (by show k ≤ k + 1; omega)
    have habs : |lam ⟨k - 1, hp⟩ - lam ⟨k, hq⟩| ≤ bv := abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 := (hcl a ha).1
    have h2 := (hnd c (by omega)).2
    linarith
  ·
    have hac' : a.val < c.val := hac
    have hd : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have had : a < ⟨a.val + 1, hd⟩ := by rw [Fin.lt_def]; simp
    have hdc : (⟨a.val + 1, hd⟩ : Fin (2 * r + k + 1)) ≤ c := by rw [Fin.le_iff_val_le_val]; simp; omega
    have hne : PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r ⟨a.val + 1, hd⟩ := by
      have h1 : ¬ (a.val < k - 1) := by omega
      have h2 : ¬ (a.val + 1 < k - 1) := by omega
      rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
    have hg := hh _ _ hne
    have hlt := hanti had
    have hle := hanti.antitone hdc
    rw [abs_of_pos (by linarith)] at hg
    linarith

/- English proof (translation)
Establish `h1 : (ν a).natAbs ≤ n1 ν` using `Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)`. Establish `h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ)`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[h2]`. Conclude with `h1.trans hν` after adjusting the coercions.
-/
theorem abs_coord_le_of_lOneNorm_le {n : ℕ} {ν : Fin n → ℤ} {q : ℕ} (hν : n1 ν ≤ q) (a : Fin n) : |(ν a : ℝ)| ≤ q := by
  have h1 : (ν a).natAbs ≤ n1 ν :=
    Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h2]
  exact_mod_cast h1.trans hν

/- English proof (translation)
Introduce `k r lam u b bv ga h q0 H ν hν`. Establish `hgl` using `fun a c (hac : a < c) => gap_lam H a c hac`. Establish `hνb` using `fun a => abs_le.mp (abs_coord_le_of_lOneNorm_le hν a)`. Establish `hint` using `H.2.1.2`. Establish `hq : (0 : ℝ) ≤ q0` using `Nat.cast_nonneg _`.

Establish `hgap : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))`. Introduce `a c hac`. Use `hgl a c hac` as an intermediate fact. Use `hνb a` as an intermediate fact. Use `hνb c` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hanti : StrictAnti (fun a => lam a + (ν a : ℝ))` using `fun a c hac => by`. Use `hgap a c hac` as an intermediate fact. Simplify using `only`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hinj` using `hanti.injective`. Establish `hZ : ∀ a c, ∃ m : ℤ, (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) = (m : ℝ)`. Introduce `a c`. Take `⟨m1, hm1⟩` from `hint a`. Take `⟨m2, hm2⟩` from `hint c`.

Conclude with `⟨m1 - m2 + ν a - ν c, by push_cast; linarith⟩`. Establish `hpos : 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ))` using `Formalism.QuantumDeterminants.formal_degree_pos_holds _ _ hinj`. Use `⟨hpos, ?_, ?_⟩` and prove the remaining obligations. Introduce `I`. Establish `hb` using `(Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound (2 * r + k + 1) (fun a => lam a + (ν a : ℝ)) I hanti hZ hgap).2`.

Establish `hfun : (fun a => lam a + (((ν + eZ I) a : ℤ) : ℝ)) = (fun a => (lam a + (ν a : ℝ)) + if a ∈ I then 1 else 0)`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply, eZ]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Rewrite using `[hfun]`.

Rewrite `hb` using `[div_le_iff₀ hpos]`. Move the coercions through the operations in `at hb`. Conclude with `hb`. Introduce `s`. Establish `hfun : (fun a => lam a + (((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) = (fun a => lam a + (ν a : ℝ)) + Pi.single s (-1 : ℝ)`.

Use function extensionality and compare the values at `a`. Distinguish the cases in `has : a = s`. Substitute `has` using the available equality. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne has, sub_zero, add_zero]`. Rewrite using `[hfun, GlobalTheory.CompareIterDegree.fdeg_ratio_abs _ s (-1) hinj]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[abs_div]`. Use `congr 2`.
-/
theorem degree_ratios : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) ∧ (∀ I : Finset (Fin (2 * r + k + 1)), Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν + eZ I) a : ℝ)) ≤ ((2 * r + k + 1) : ℝ) ^ I.card * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ))) ∧ ∀ s, Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) / Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) = ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| / |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))| := by
  intro k r lam u b bv ga h q0 H ν hν
  have hgl := fun a c (hac : a < c) => gap_lam H a c hac
  have hνb := fun a => abs_le.mp (abs_coord_le_of_lOneNorm_le hν a)
  have hint := H.2.1.2
  have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hgap : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    have := hgl a c hac
    have := hνb a
    have := hνb c
    linarith
  have hanti : StrictAnti (fun a => lam a + (ν a : ℝ)) := fun a c hac => by
    have := hgap a c hac
    simp only
    linarith
  have hinj := hanti.injective
  have hZ : ∀ a c, ∃ m : ℤ, (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) = (m : ℝ) := by
    intro a c
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨m2, hm2⟩ := hint c
    exact ⟨m1 - m2 + ν a - ν c, by push_cast; linarith⟩
  have hpos : 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := Formalism.QuantumDeterminants.formal_degree_pos_holds _ _ hinj
  refine ⟨hpos, ?_, ?_⟩
  · intro I
    have hb := (Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound (2 * r + k + 1) (fun a => lam a + (ν a : ℝ)) I hanti hZ hgap).2
    have hfun : (fun a => lam a + (((ν + eZ I) a : ℤ) : ℝ)) =
        (fun a => (lam a + (ν a : ℝ)) + if a ∈ I then 1 else 0) := by
      funext a
      simp only [Pi.add_apply, eZ]
      split_ifs <;> push_cast <;> ring
    rw [hfun]
    rw [div_le_iff₀ hpos] at hb
    push_cast at hb
    exact hb
  · intro s
    have hfun : (fun a => lam a + (((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) + Pi.single s (-1 : ℝ) := by
      funext a
      by_cases has : a = s
      · subst has
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
        ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne has, sub_zero, add_zero]
    rw [hfun, GlobalTheory.CompareIterDegree.fdeg_ratio_abs _ s (-1) hinj]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [abs_div]
    congr 2

end GlobalTheory.FamilyDegreeRatio
