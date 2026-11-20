import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `f hf`. Establish `hf0 : f = fun _ => 0` using `funext fun q => hf q (Nat.zero_le q)`. Substitute `hf0` using the available equality.

Rewrite using `[Cardinal.sum_const', mul_zero, Finset.sum_range_zero]`. Consider the case `succ N ih`. Introduce `f hf`. Rewrite using `[Cardinal.sum_nat_eq_add_sum_succ, ih (fun i => f (i+1)) (fun q hq => hf (q+1) (by omega)), Finset.sum_range_succ', add_comm]`.
-/
private theorem UpperTheory.cardinal_sum_eq_finite_sum_range (N : ℕ) : ∀ f : ℕ → Cardinal.{0}, (∀ q, N ≤ q → f q = 0) →
    Cardinal.sum f = ∑ q ∈ Finset.range N, f q := by
  induction N with
  | zero =>
    intro f hf
    have hf0 : f = fun _ => 0 := funext fun q => hf q (Nat.zero_le q)
    subst hf0
    rw [Cardinal.sum_const', mul_zero, Finset.sum_range_zero]
  | succ N ih =>
    intro f hf
    rw [Cardinal.sum_nat_eq_add_sum_succ, ih (fun i => f (i+1)) (fun q hq => hf (q+1) (by omega)),
      Finset.sum_range_succ', add_comm]

/- English proof (translation)
Unfold `UpperTheory.V.Af.BA.BddOfDeg`. Introduce `Γ _ hc hD`. Use `choose c hc using hc`. Take `⟨D, hD⟩` from `hD`. Unfold `UpperTheory.V.Af.CohB.Bdd`.

Use `⟨∑ q ∈ Finset.range D, c q, fun A => ?_⟩` and prove the remaining obligations. Unfold `UpperTheory.V.Af.CohB.totCoh`. Rewrite using `[UpperTheory.cardinal_sum_eq_finite_sum_range D _ (fun q hq => hD q hq A), Nat.cast_sum, Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun q _ => hc q A`.
-/
theorem UpperTheory.adelic_rep_bounded_of_degree_bounded :
    UpperTheory.V.Af.BA.BddOfDeg := by
  unfold UpperTheory.V.Af.BA.BddOfDeg
  intro Γ _ hc hD
  choose c hc using hc
  obtain ⟨D, hD⟩ := hD
  unfold UpperTheory.V.Af.CohB.Bdd
  refine ⟨∑ q ∈ Finset.range D, c q, fun A => ?_⟩
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [UpperTheory.cardinal_sum_eq_finite_sum_range D _ (fun q hq => hD q hq A), Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun q _ => hc q A
