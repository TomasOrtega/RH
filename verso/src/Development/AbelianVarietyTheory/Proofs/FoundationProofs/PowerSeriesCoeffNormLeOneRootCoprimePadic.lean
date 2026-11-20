import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open scoped BigOperators

noncomputable section
namespace GlobalTheory.RootInt

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Introduce `n`. Rewrite using `[PowerSeries.coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hf _) (norm_nonneg _) (hg _)`.
-/
theorem intSer_mul {f g : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (hg : GlobalTheory.EvenTheta.IntSer g) :
    GlobalTheory.EvenTheta.IntSer (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `n`. Rewrite using `[pow_zero, PowerSeries.coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ N ih => rw [pow_succ]`. Conclude with `intSer_mul ih hf`.
-/
theorem intSer_pow {f : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (N : ℕ) :
    GlobalTheory.EvenTheta.IntSer (f ^ N) := by
  induction N with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih => rw [pow_succ]; exact intSer_mul ih hf

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, norm_one]`.

Use `set a : PowerSeries K := PowerSeries.mk fun k => if k < n then PowerSeries.coeff k s else 0 with ha`. Establish `hca : ∀ k, PowerSeries.coeff k a = if k < n then PowerSeries.coeff k s else 0` using `fun k => by`. Rewrite using `[ha, PowerSeries.coeff_mk]`. Establish `hai : GlobalTheory.EvenTheta.IntSer a` using `fun k => by`. Rewrite using `[hca]`.

Use `split_ifs with h`. Conclude with `ih k h`. Simplify using the standard rewrite rules. Establish `hcb : ∀ k, PowerSeries.coeff k (s - a) = if k < n then 0 else PowerSeries.coeff k s` using `fun k => by`. Apply the tactic sequence `rw [map_sub, hca]; split_ifs <;> simp`.

Use `set G : PowerSeries K := ∑ i ∈ Finset.range N, s ^ i * a ^ (N - 1 - i) with hG`. Establish `hGN : G * (s - a) = s ^ N - a ^ N` using `geom_sum₂_mul s a N`. Establish `ha0 : PowerSeries.constantCoeff a = 1`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hca, if_pos hn, PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]`. Establish `hG0 : PowerSeries.coeff 0 G = N`.

Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, map_sum]`. Simplify using `[hs0, ha0]`. Establish `key : PowerSeries.coeff n (G * (s - a)) = (N : K) * PowerSeries.coeff n s`. Rewrite using `[PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]`. Rewrite using `[hG0, hcb, if_neg (lt_irrefl n)]`.

Introduce and unpack `⟨i, j⟩ hij hne`. Rewrite `hij` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hj : j < n`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Conclude with `absurd (by simp at hij; simp [hij]) hne`.

Use linear arithmetic over natural numbers and integers. Simplify using `only`. Rewrite using `[hcb, if_pos hj, mul_zero]`. Introduce `h; exact absurd (by simp) h`. Establish `h1 : ‖(N : K) * PowerSeries.coeff n s‖ ≤ 1`.

Rewrite using `[← key, hGN, map_sub]`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsN n) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `intSer_pow hai N n`.

Rewrite `h1` using `[norm_mul, hN, one_mul]`. Then use the resulting hypothesis.
-/
theorem intSer_of_pow {N : ℕ} (hN : ‖(N : K)‖ = 1) {s : PowerSeries K}
    (hs0 : PowerSeries.constantCoeff s = 1) (hsN : GlobalTheory.EvenTheta.IntSer (s ^ N)) :
    GlobalTheory.EvenTheta.IntSer s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, norm_one]
  set a : PowerSeries K := PowerSeries.mk fun k => if k < n then PowerSeries.coeff k s else 0 with ha
  have hca : ∀ k, PowerSeries.coeff k a = if k < n then PowerSeries.coeff k s else 0 := fun k => by
    rw [ha, PowerSeries.coeff_mk]
  have hai : GlobalTheory.EvenTheta.IntSer a := fun k => by
    rw [hca]; split_ifs with h
    · exact ih k h
    · simp
  have hcb : ∀ k, PowerSeries.coeff k (s - a) = if k < n then 0 else PowerSeries.coeff k s := fun k => by
    rw [map_sub, hca]; split_ifs <;> simp
  set G : PowerSeries K := ∑ i ∈ Finset.range N, s ^ i * a ^ (N - 1 - i) with hG
  have hGN : G * (s - a) = s ^ N - a ^ N := geom_sum₂_mul s a N
  have ha0 : PowerSeries.constantCoeff a = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hca, if_pos hn,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]
  have hG0 : PowerSeries.coeff 0 G = N := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, map_sum]
    simp [hs0, ha0]
  have key : PowerSeries.coeff n (G * (s - a)) = (N : K) * PowerSeries.coeff n s := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hG0, hcb, if_neg (lt_irrefl n)]
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact absurd (by simp at hij; simp [hij]) hne
        · omega
      simp only
      rw [hcb, if_pos hj, mul_zero]
    · intro h; exact absurd (by simp) h
  have h1 : ‖(N : K) * PowerSeries.coeff n s‖ ≤ 1 := by
    rw [← key, hGN, map_sub]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsN n) ?_)
    rw [norm_neg]; exact intSer_pow hai N n
  rwa [norm_mul, hN, one_mul] at h1

end GlobalTheory.RootInt

/- English proof (translation)
Introduce `p _ N _ hcop s hs0 hsN`. Use `GlobalTheory.RootInt.intSer_of_pow ?_ hs0 hsN` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `hcop.symm`.
-/
theorem GlobalTheory.RootInt.intSer_root : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  intro p _ N _ hcop s hs0 hsN
  refine GlobalTheory.RootInt.intSer_of_pow ?_ hs0 hsN
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact hcop.symm
