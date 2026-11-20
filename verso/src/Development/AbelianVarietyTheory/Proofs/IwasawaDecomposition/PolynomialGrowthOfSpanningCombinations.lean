import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `n g r J _ R x u hspan hb`. Use `choose C k hC using hb`. Establish `hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1`. Introduce `m`. Establish `hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u)`.

Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `(Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem`. Use `choose a ha using hsingle`. Use `⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩` and prove the remaining obligations.

Introduce `s hs`. Establish `h1 : (1:ℝ) ≤ 1 + ‖s‖` using `by linarith [norm_nonneg s]`. Establish `hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j)` using `fun i => pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))`. Establish `hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j)`. Introduce `m`.

Establish `hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'`. Establish `e` using `congrFun (ha m)`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m' = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m'`.

Introduce `m'`. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Establish `h2` using `e m'`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2`.

Rewrite using `[← h2]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl (fun m' _ => hc m')]`. Rewrite using `[Finset.sum_eq_single m]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ m) h`.

Rewrite using `[hid]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs]`.

Apply `mul_le_mul_of_nonneg_left _ (abs_nonneg _)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm`.

Establish `hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0` using `fun m => Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)`. Use `(pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Conclude with `Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0) (fun j _ => hnn j) (Finset.mem_univ m)`.
-/
theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
