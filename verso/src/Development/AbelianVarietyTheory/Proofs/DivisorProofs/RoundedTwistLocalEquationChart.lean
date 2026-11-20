import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RoundEqn

open GlobalTheory.Cartier.CartierDiv

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem eff_of_atlas {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    (𝒜 : SncAtlas E n ι) (c : C) : (E c).Eff := by
  intro y
  have hy : y ∈ ⨆ i, 𝒜.U i := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
  obtain ⟨e, -, -, heq⟩ := 𝒜.snc i
  refine ⟨_, heq c y hi, ?_⟩
  rw [one_mul]
  cases h : e c with
  | none => exact (unitAt_one y).regAt
  | some j => exact ((𝒜.chart i).chart y hi).mem j

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem Eff.nsmul' {D : CartierDiv X} (h : D.Eff) (m : ℕ) : (m • D).Eff := by
  induction m with
  | zero => rw [zero_nsmul]; exact eff_zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isEqn_sum {C : Type} (s : Finset C) (D : C → CartierDiv X) (g : C → X.functionFieldˣ)
    (y : X) (h : ∀ c ∈ s, (D c).IsEqn y (g c)) : (∑ c ∈ s, D c).IsEqn y (∏ c ∈ s, g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem prod_elim_pow {C : Type} [Fintype C] {n : ℕ} {M : Type} [CommMonoid M] (x : Fin n → M)
    (J : Finset (Fin n)) (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j)
    (r : C → ℕ) :
    ∏ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (∑ c, if e c = some j then r c else 0) := by
  have step : ∀ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (if e c = some j then r c else 0) := by
    intro c
    cases h : e c with
    | none => simp
    | some j₀ =>
      have hj₀ : j₀ ∈ J := (hJ j₀).2 ⟨c, h⟩
      rw [Finset.prod_eq_single j₀]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro hn; exact (hn hj₀).elim
  simp_rw [step]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_pow_eq_pow_sum _ _ _

end GlobalTheory.RoundEqn

open GlobalTheory.RoundEqn GlobalTheory.Cartier.CartierDiv in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem GlobalTheory.roundedTwist_isEqn :
  ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  intro p hp X _ _ C _ E n ι _ 𝒜 G r hr
  classical
  refine ⟨?_, fun i => ?_⟩
  · rw [add_sub_cancel_left]
    refine Finset.sum_induction _ (fun D : CartierDiv X => D.Eff) (fun _ _ h h' => h.add h') eff_zero ?_
    intro c _
    exact Eff.nsmul' (eff_of_atlas 𝒜 c) (r c)
  · obtain ⟨e, huniq, hJ, heq⟩ := 𝒜.snc i
    refine ⟨fun j => ∑ c, if e c = some j then r c else 0, fun j => ?_, fun y hy t ht => ?_⟩
    · show (∑ c, if e c = some j then r c else 0) < p
      by_cases h : ∃ c, e c = some j
      · obtain ⟨c₀, hc₀⟩ := h
        rw [Finset.sum_eq_single c₀]
        · rw [if_pos hc₀]; exact hr c₀
        · intro c _ hc; rw [if_neg]; exact fun h' => hc (huniq c c₀ j h' hc₀)
        · intro hn; exact (hn (Finset.mem_univ _)).elim
      · push_neg at h
        rw [Finset.sum_eq_zero fun c _ => if_neg (h c)]
        exact hp.out.pos
    · rw [← prod_elim_pow (𝒜.x i) (𝒜.J i) e hJ r]
      refine (ht.nsmul p).add (isEqn_sum _ _ _ y fun c _ => ?_)
      exact (heq c y hy).nsmul (r c)
