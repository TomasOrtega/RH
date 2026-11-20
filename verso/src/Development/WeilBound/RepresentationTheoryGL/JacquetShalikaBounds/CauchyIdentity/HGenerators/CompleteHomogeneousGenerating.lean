import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset

namespace PositivityTheory.RgJS

namespace completeHomogeneousGenerating

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr fun x => ?_` and prove the remaining obligations. Conclude with `(norm_mul _ _).symm`. Rewrite using `[tsum_mul_tsum_of_summable_norm ha hb]`. Conclude with `(summable_mul_of_summable_norm ha hb).hasSum`.
-/
private theorem summable_norm_mul_and_hasSum_mul_tsum {ι : Type} (a : ℕ → ℂ) (b : ι → ℂ) (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖) :
    Summable (fun x : ℕ × ι => ‖a x.1 * b x.2‖) ∧
      HasSum (fun x : ℕ × ι => a x.1 * b x.2) ((∑' k, a k) * ∑' k, b k) := by
  refine ⟨?_, ?_⟩
  · refine (Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun x => ?_
    exact (norm_mul _ _).symm
  · rw [tsum_mul_tsum_of_summable_norm ha hb]
    exact (summable_mul_of_summable_norm ha hb).hasSum

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `f _`. Use `⟨Summable.of_finite, ?_⟩` and prove the remaining obligations. Simplify using `using (hasSum_fintype (fun k : Fin 0 → ℕ => ∏ i, f i (k i)))`.

Consider the case `succ n ih`. Introduce `f hf`. Take `⟨hs1, hh1⟩` from `ih (fun i => f i.succ) (fun i => hf i.succ)`. Take `⟨hN2, hH2⟩` from `summable_norm_mul_and_hasSum_mul_tsum (f 0) (fun k : Fin n → ℕ => ∏ i, f i.succ (k i)) (hf 0) (hs1.congr fun _ => rfl)`. Rewrite `hH2` using `[hh1.tsum_eq]`.

Set `e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ)` to `Fin.consEquiv (fun _ => ℕ)`. Establish `hcomp : ∀ x : ℕ × (Fin n → ℕ), ∏ i, f i (e x i) = f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)`. Introduce `x`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[e, Fin.consEquiv]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← e.summable_iff]`. Use `hN2.congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[hcomp]`.

Rewrite using `[← e.hasSum_iff]`. Establish `hfun : ((fun k : Fin (n + 1) → ℕ => ∏ i, f i (k i)) ∘ e) = fun x => f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)` using `funext hcomp`. Rewrite using `[hfun, Fin.prod_univ_succ]`. Conclude with `hH2`.
-/
theorem pi_hasSum (m : ℕ) : ∀ (f : Fin m → ℕ → ℂ), (∀ i, Summable (fun n => ‖f i n‖)) →
    Summable (fun k : Fin m → ℕ => ‖∏ i, f i (k i)‖) ∧ HasSum (fun k : Fin m → ℕ => ∏ i, f i (k i)) (∏ i, ∑' n, f i n) := by
  induction m with
  | zero =>
    intro f _
    refine ⟨Summable.of_finite, ?_⟩
    simpa using (hasSum_fintype (fun k : Fin 0 → ℕ => ∏ i, f i (k i)))
  | succ n ih =>
    intro f hf
    obtain ⟨hs1, hh1⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    obtain ⟨hN2, hH2⟩ := summable_norm_mul_and_hasSum_mul_tsum (f 0) (fun k : Fin n → ℕ => ∏ i, f i.succ (k i)) (hf 0)
      (hs1.congr fun _ => rfl)
    rw [hh1.tsum_eq] at hH2
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv (fun _ => ℕ)
    have hcomp : ∀ x : ℕ × (Fin n → ℕ),
        ∏ i, f i (e x i) = f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := by
      intro x
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    constructor
    · rw [← e.summable_iff]
      refine hN2.congr fun x => ?_
      simp only [Function.comp_apply]
      rw [hcomp]
    · rw [← e.hasSum_iff]
      have hfun : ((fun k : Fin (n + 1) → ℕ => ∏ i, f i (k i)) ∘ e) =
          fun x => f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := funext hcomp
      rw [hfun, Fin.prod_univ_succ]
      exact hH2

/- English proof (translation)
Establish `hsub : Finset.Nat.antidiagonalTuple m p ⊆ Fintype.piFinset (fun _ : Fin m => Finset.range (p + 1))`. Introduce `k hk`. Rewrite `hk` using `[Finset.Nat.mem_antidiagonalTuple]`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`.

Rewrite using `[Finset.mem_range, Nat.lt_succ_iff, ← hk]`. Conclude with `Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)`. Establish `h` using `Finset.card_le_card hsub`. Rewrite `h` using `[Fintype.card_piFinset]`. Simplify using `only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h`.

Conclude with `h` after adjusting the coercions.
-/
theorem card_le (m p : ℕ) : ((Finset.Nat.antidiagonalTuple m p).card : ℝ) ≤ ((p + 1 : ℕ) : ℝ) ^ m := by
  have hsub : Finset.Nat.antidiagonalTuple m p ⊆ Fintype.piFinset (fun _ : Fin m => Finset.range (p + 1)) := by
    intro k hk
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff, ← hk]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  have h := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

/- English proof (translation)
Unfold `hN`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[Finset.Nat.mem_antidiagonalTuple]`. Repeatedly rewrite using `[mul_pow]`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]`.
-/
theorem term_eq (m : ℕ) (α : Fin m → ℂ) (u : ℂ) (p : ℕ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple m p, ∏ i, (α i * u) ^ k i = hN p α * u ^ p := by
  unfold hN
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hk
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]

end completeHomogeneousGenerating

open completeHomogeneousGenerating in
/- English proof (translation)
Introduce `m α u A hA hα hAu`. Establish `hr : ∀ i, ‖α i * u‖ < 1` using `fun i => by`. Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hα i) (norm_nonneg u)) hAu`. Use `⟨?_, fun p => ?_⟩` and prove the remaining obligations.

Take `⟨-, hH⟩` from `pi_hasSum m (fun i n => (α i * u) ^ n) (fun i => by`. Simplify `summable_geometric_of_lt_one (norm_nonneg _) (hr i))` using `only [norm_pow]`. Establish `hprod : (∏ i, ∑' n, (α i * u) ^ n) = ∏ i, (1 - α i * u)⁻¹` using `Finset.prod_congr rfl fun i _ => tsum_geometric_of_norm_lt_one (hr i)`. Rewrite `hH` using `[hprod]`. Establish `hF` using `hH.tsum_fiberwise (fun k : Fin m → ℕ => ∑ i, k i)`.

Establish `hset : ∀ c : ℕ, ((fun k : Fin m → ℕ => ∑ i, k i) ⁻¹' {c}) = ↑(Finset.Nat.antidiagonalTuple m c)`. Introduce `c`. Use extensionality with `k`. Simplify using `[Finset.Nat.mem_antidiagonalTuple]`. Establish `hfun : (fun c : ℕ => hN c α * u ^ c) = fun c => ∑' b : ↑((fun k : Fin m → ℕ => ∑ i, k i) ⁻¹' {c}), ∏ i, (α i * u) ^ (b : Fin m → ℕ) i`.

Use function extensionality and compare the values at `c`. Rewrite using `[hset c]`. Conclude with `((Finset.tsum_subtype' _ (fun k : Fin m → ℕ => ∏ i, (α i * u) ^ k i)).trans (term_eq m α u c)).symm`. Rewrite using `[hfun]`. Conclude with `hF`.

Establish `hterm : ∀ k ∈ Finset.Nat.antidiagonalTuple m p, ‖∏ i, α i ^ k i‖ ≤ A ^ p`. Introduce `k hk`. Rewrite `hk` using `[Finset.Nat.mem_antidiagonalTuple]`. Rewrite using `[norm_prod, ← hk, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hα i) _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ ((p + 1 : ℕ) : ℝ) ^ m * A ^ p := mul_le_mul_of_nonneg_right (card_le m p) (pow_nonneg hA _)`.
-/
theorem complete_homogeneous_generating : HGen := by
  intro m α u A hA hα hAu
  have hr : ∀ i, ‖α i * u‖ < 1 := fun i => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hα i) (norm_nonneg u)) hAu
  refine ⟨?_, fun p => ?_⟩
  · obtain ⟨-, hH⟩ := pi_hasSum m (fun i n => (α i * u) ^ n) (fun i => by
      simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hr i))
    have hprod : (∏ i, ∑' n, (α i * u) ^ n) = ∏ i, (1 - α i * u)⁻¹ :=
      Finset.prod_congr rfl fun i _ => tsum_geometric_of_norm_lt_one (hr i)
    rw [hprod] at hH
    have hF := hH.tsum_fiberwise (fun k : Fin m → ℕ => ∑ i, k i)
    have hset : ∀ c : ℕ, ((fun k : Fin m → ℕ => ∑ i, k i) ⁻¹' {c}) =
        ↑(Finset.Nat.antidiagonalTuple m c) := by
      intro c
      ext k
      simp [Finset.Nat.mem_antidiagonalTuple]
    have hfun : (fun c : ℕ => hN c α * u ^ c) = fun c =>
        ∑' b : ↑((fun k : Fin m → ℕ => ∑ i, k i) ⁻¹' {c}), ∏ i, (α i * u) ^ (b : Fin m → ℕ) i := by
      funext c
      rw [hset c]
      exact ((Finset.tsum_subtype' _ (fun k : Fin m → ℕ => ∏ i, (α i * u) ^ k i)).trans
        (term_eq m α u c)).symm
    rw [hfun]
    exact hF
  · have hterm : ∀ k ∈ Finset.Nat.antidiagonalTuple m p, ‖∏ i, α i ^ k i‖ ≤ A ^ p := by
      intro k hk
      rw [Finset.Nat.mem_antidiagonalTuple] at hk
      rw [norm_prod, ← hk, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hα i) _
    calc ‖hN p α‖ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple m p, ‖∏ i, α i ^ k i‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple m p, A ^ p := Finset.sum_le_sum hterm
      _ = ((Finset.Nat.antidiagonalTuple m p).card : ℝ) * A ^ p := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((p + 1 : ℕ) : ℝ) ^ m * A ^ p :=
        mul_le_mul_of_nonneg_right (card_le m p) (pow_nonneg hA _)

end PositivityTheory.RgJS
