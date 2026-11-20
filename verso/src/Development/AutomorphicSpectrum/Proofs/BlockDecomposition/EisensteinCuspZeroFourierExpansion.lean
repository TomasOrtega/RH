import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S
open Complex

namespace GlobalTheory.CompanionTheory.EisensteinPoissonSummation

/- English proof (translation)
Simplify using `only [ee, mul_add, Complex.exp_add]`.
-/
theorem ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  simp only [ee, mul_add, Complex.exp_add]

/- English proof (translation)
Unfold `ee`. Rewrite using `[Complex.exp_eq_one_iff]`. Conclude with `⟨n, by ring⟩`.
-/
theorem ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by ring⟩

/- English proof (translation)
Unfold `ee`. Establish `: (2 * (Real.pi : ℂ) * I * t) = ((2 * Real.pi * t : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_ee_real (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * (Real.pi : ℂ) * I * t) = ((2 * Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Unfold `GS`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `: (r : ℂ) * (x : ℂ) ^ 2 / d = (((r : ℝ) * (x : ℝ) ^ 2 / d : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, norm_ee_real]`.

Use `_ = d := by simp`.
-/
theorem GS_norm_le (r : ℤ) (d : ℕ) : ‖GS r d‖ ≤ d := by
  unfold GS
  calc ‖∑ x ∈ Finset.range d, ee (r * (x : ℂ) ^ 2 / d)‖
      ≤ ∑ x ∈ Finset.range d, ‖ee (r * (x : ℂ) ^ 2 / d)‖ := norm_sum_le _ _
    _ = ∑ x ∈ Finset.range d, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have : (r : ℂ) * (x : ℂ) ^ 2 / d = (((r : ℝ) * (x : ℝ) ^ 2 / d : ℝ) : ℂ) := by push_cast; rfl
        rw [this, norm_ee_real]
    _ = d := by simp

/- English proof (translation)
Unfold `GS`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `: (((r + j * d : ℤ)) : ℂ) * (x : ℂ) ^ 2 / d = (r : ℂ) * (x : ℂ) ^ 2 / d + ((j * (x : ℤ) ^ 2 : ℤ) : ℂ)` using `by push_cast; field_simp`. Rewrite using `[this, ee_add, ee_int, mul_one]`.
-/
theorem GS_add (r j : ℤ) (d : ℕ) (hd : 0 < d) : GS (r + j * d) d = GS r d := by
  unfold GS
  refine Finset.sum_congr rfl fun x _ => ?_
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (((r + j * d : ℤ)) : ℂ) * (x : ℂ) ^ 2 / d = (r : ℂ) * (x : ℂ) ^ 2 / d + ((j * (x : ℤ) ^ 2 : ℤ) : ℂ) := by
    push_cast; field_simp
  rw [this, ee_add, ee_int, mul_one]

/- English proof (translation)
Unfold `RR`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun r _ => ?_` and prove the remaining obligations. Establish `: (-((n : ℂ) * r / d)) = ((-((n : ℝ) * r / d) : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[norm_mul, this, norm_ee_real, mul_one]`.

Conclude with `GS_norm_le _ _`. Use `_ = ((Finset.range d).filter (fun r => Nat.Coprime r d)).card * (d : ℝ) := by simp`. Use `_ ≤ (d : ℝ) * d := by`. Use `mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)` and prove the remaining obligations. Conclude with `(Finset.card_filter_le _ _).trans (by simp)` after adjusting the coercions.

Use `_ = (d : ℝ) ^ 2 := by ring`.
-/
theorem RR_norm_le (n : ℤ) (d : ℕ) : ‖RR n d‖ ≤ (d : ℝ) ^ 2 := by
  unfold RR
  calc ‖∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), GS r d * ee (-(n * r / d))‖
      ≤ ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), ‖GS r d * ee (-(n * r / d))‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), (d : ℝ) := by
        refine Finset.sum_le_sum fun r _ => ?_
        have : (-((n : ℂ) * r / d)) = ((-((n : ℝ) * r / d) : ℝ) : ℂ) := by push_cast; rfl
        rw [norm_mul, this, norm_ee_real, mul_one]
        exact GS_norm_le _ _
    _ = ((Finset.range d).filter (fun r => Nat.Coprime r d)).card * (d : ℝ) := by simp
    _ ≤ (d : ℝ) * d := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    _ = (d : ℝ) ^ 2 := by ring

/- English proof (translation)
Establish `hS : Summable (Function.uncurry fun (d : ℕ) (n : ℤ) => b d * (RR n d * Q n))`. Use `Summable.of_norm_bounded (hb.mul_of_nonneg hQ (fun _ => by positivity) (fun _ => norm_nonneg _)) ?_` and prove the remaining obligations. Introduce and unpack `⟨d, n⟩`. Simplify using `only [Function.uncurry, norm_mul]`. Rewrite using `[mul_assoc]`.

Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (RR_norm_le n d) (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[← tsum_mul_right]`.

Conclude with `tsum_congr fun d => by ring`.
-/
theorem swap (b : ℕ → ℂ) (Q : ℤ → ℂ) (hb : Summable fun d : ℕ => ‖b d‖ * (d : ℝ) ^ 2)
    (hQ : Summable fun n : ℤ => ‖Q n‖) :
    ∑' d : ℕ, b d * ∑' n : ℤ, RR n d * Q n = ∑' n : ℤ, (∑' d : ℕ, b d * RR n d) * Q n := by
  have hS : Summable (Function.uncurry fun (d : ℕ) (n : ℤ) => b d * (RR n d * Q n)) := by
    refine Summable.of_norm_bounded (hb.mul_of_nonneg hQ (fun _ => by positivity) (fun _ => norm_nonneg _)) ?_
    rintro ⟨d, n⟩
    simp only [Function.uncurry, norm_mul]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (RR_norm_le n d) (norm_nonneg _)
  calc ∑' d : ℕ, b d * ∑' n : ℤ, RR n d * Q n
      = ∑' d : ℕ, ∑' n : ℤ, b d * (RR n d * Q n) := tsum_congr fun d => tsum_mul_left.symm
    _ = ∑' n : ℤ, ∑' d : ℕ, b d * (RR n d * Q n) := hS.tsum_comm.symm
    _ = ∑' n : ℤ, (∑' d : ℕ, b d * RR n d) * Q n := by
        refine tsum_congr fun n => ?_
        rw [← tsum_mul_right]
        exact tsum_congr fun d => by ring

/- English proof (translation)
Establish `h0 : Summable fun d : ℕ => (d : ℝ) ^ (1 - s.re)` using `Real.summable_nat_rpow.2 (by linarith)`. Use `Summable.of_nonneg_of_le (fun _ => by positivity) (fun d => ?_) h0` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Simplify using `only [Nat.cast_zero]`. Rewrite using `[zero_pow two_ne_zero, mul_zero]`.

Conclude with `Real.rpow_nonneg le_rfl _`. Establish `hd' : (0 : ℝ) < d` using `by exact_mod_cast hd`. Rewrite using `[norm_mul, Complex.norm_natCast_cpow_of_pos hd]`. Establish `h1 : ‖c (d : ZMod M)‖ ≤ 1` using `DirichletCharacter.norm_le_one c _`. Establish `h2 : (d : ℝ) ^ (1 - s.re) = (d : ℝ) ^ (-(s + 1)).re * (d : ℝ) ^ 2`.

Rewrite using `[← Real.rpow_natCast (d : ℝ) 2, ← Real.rpow_add hd']`. Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coef_summable (M : ℕ) [NeZero M] (c : DirichletCharacter ℂ M) (s : ℂ) (hs : 2 < s.re) :
    Summable fun d : ℕ => ‖c (d : ZMod M) * (d : ℂ) ^ (-(s + 1))‖ * (d : ℝ) ^ 2 := by
  have h0 : Summable fun d : ℕ => (d : ℝ) ^ (1 - s.re) := Real.summable_nat_rpow.2 (by linarith)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun d => ?_) h0
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero]
    rw [zero_pow two_ne_zero, mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hd]
    have h1 : ‖c (d : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one c _
    have h2 : (d : ℝ) ^ (1 - s.re) = (d : ℝ) ^ (-(s + 1)).re * (d : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast (d : ℝ) 2, ← Real.rpow_add hd']
      congr 1
      simp; ring
    rw [h2]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ‖c (d : ZMod M)‖ * (d : ℝ) ^ (-(s + 1)).re ≤ 1 * (d : ℝ) ^ (-(s + 1)).re :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := one_mul _

/- English proof (translation)
Establish `hM1 : ¬ Nat.Coprime 0 M`. Introduce `h`. Establish `h1 : M = 1` using `by simpa using h`. Substitute `h1` using the available equality. Evaluate the numerical expressions using `at hM`.

Establish `hb00 : b 0 = 0` using `hb0 0 hM1`. Set `A : ℕ → ℤ → ℂ` to `fun d c' => if IsCoprime c' (d : ℤ) then G d c' else 0`. Set `F : ℕ × ℤ → ℂ` to `fun p => b p.1 * A p.1 p.2`. Establish `hnorm : ∀ p, ‖F p‖ = ‖b p.1‖ * ‖A p.1 p.2‖` using `fun p => norm_mul _ _`. Establish `hsF : Summable fun p => ‖F p‖`.

Use `(summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun d => ?_, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Simplify using `only [hnorm, hb00, norm_zero, zero_mul]`. Conclude with `summable_zero`. Simplify using `only [hnorm]`.

Conclude with `(hG d hd).1.mul_left _`. Use `Summable.of_nonneg_of_le (fun d => tsum_nonneg fun _ => norm_nonneg _) (fun d => ?_) (hbs.mul_right B)` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Simplify using `[hnorm, hb00]`. Simplify using `only [hnorm]`.

Rewrite using `[tsum_mul_left, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hG d hd).2 (norm_nonneg _)`. Establish `hsupp : Function.support F ⊆ {p : ℕ × ℤ | 0 < p.1 ∧ IsCoprime (((4 * M ^ 2 : ℕ) : ℤ) * p.2) (p.1 : ℤ)}`. Introduce and unpack `⟨d, c'⟩ hp`. Establish `h1 : b d ≠ 0` using `left_ne_zero_of_mul hp`.

Establish `h2 : IsCoprime c' (d : ℤ)`. Assume the negation of the conclusion as `h`. Apply `hp` to reduce the goal to its premises. Simplify using `[F, A, h]`. Establish `hc : Nat.Coprime d M`.

Assume the negation of the conclusion as `h`. Conclude with `h1 (hb0 d h)`. Establish `hpos : 0 < d`. Break down `Nat.eq_zero_or_pos d with rfl | h` into its components or cases. Conclude with `absurd hc hM1`.

Conclude with `h`. Establish `hodd : Nat.Coprime d 2` using `Nat.Coprime.coprime_dvd_right hM hc`. Establish `h4 : Nat.Coprime 4 d`. Use `(hodd.pow_right 2).symm` as an intermediate fact. Simplify using `using this`.

Establish `hc4 : Nat.Coprime (4 * M ^ 2) d` using `Nat.Coprime.mul_left h4 (hc.symm.pow_left 2)`. Conclude with `⟨hpos, IsCoprime.mul_left (Nat.isCoprime_iff_coprime.2 hc4) h2⟩`. Establish `hback : ∀ p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2 = F p.1`. Introduce `p`. Establish `: IsCoprime p.1.2 (p.1.1 : ℤ)` using `IsCoprime.of_mul_left_right p.2.2`.

Simplify using `[F, A, this]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [F, A]`. Conclude with `tsum_mul_left`.
-/
theorem idx_tsum (M : ℕ) (hM : 2 ∣ M) (hM0 : M ≠ 0) (b : ℕ → ℂ) (G : ℕ → ℤ → ℂ) (B : ℝ)
    (hb0 : ∀ d : ℕ, ¬ Nat.Coprime d M → b d = 0)
    (hbs : Summable fun d : ℕ => ‖b d‖ * (d : ℝ) ^ 2)
    (hG : ∀ d : ℕ, 0 < d →
      (Summable fun c' : ℤ => ‖if IsCoprime c' (d : ℤ) then G d c' else 0‖) ∧
      ∑' c' : ℤ, ‖if IsCoprime c' (d : ℤ) then G d c' else 0‖ ≤ (d : ℝ) ^ 2 * B) :
    ∑' p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2 =
      ∑' d : ℕ, b d * ∑' c' : ℤ, if IsCoprime c' (d : ℤ) then G d c' else 0 := by
  classical
  have hM1 : ¬ Nat.Coprime 0 M := by
    intro h
    have h1 : M = 1 := by simpa using h
    subst h1
    norm_num at hM
  have hb00 : b 0 = 0 := hb0 0 hM1
  let A : ℕ → ℤ → ℂ := fun d c' => if IsCoprime c' (d : ℤ) then G d c' else 0
  let F : ℕ × ℤ → ℂ := fun p => b p.1 * A p.1 p.2
  have hnorm : ∀ p, ‖F p‖ = ‖b p.1‖ * ‖A p.1 p.2‖ := fun p => norm_mul _ _
  have hsF : Summable fun p => ‖F p‖ := by
    refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun d => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp only [hnorm, hb00, norm_zero, zero_mul]
        exact summable_zero
      · simp only [hnorm]
        exact (hG d hd).1.mul_left _
    · refine Summable.of_nonneg_of_le (fun d => tsum_nonneg fun _ => norm_nonneg _) (fun d => ?_)
        (hbs.mul_right B)
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [hnorm, hb00]
      · simp only [hnorm]
        rw [tsum_mul_left, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hG d hd).2 (norm_nonneg _)
  have hsupp : Function.support F ⊆
      {p : ℕ × ℤ | 0 < p.1 ∧ IsCoprime (((4 * M ^ 2 : ℕ) : ℤ) * p.2) (p.1 : ℤ)} := by
    rintro ⟨d, c'⟩ hp
    have h1 : b d ≠ 0 := left_ne_zero_of_mul hp
    have h2 : IsCoprime c' (d : ℤ) := by
      by_contra h
      apply hp
      simp [F, A, h]
    have hc : Nat.Coprime d M := by
      by_contra h
      exact h1 (hb0 d h)
    have hpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd hc hM1
      · exact h
    have hodd : Nat.Coprime d 2 := Nat.Coprime.coprime_dvd_right hM hc
    have h4 : Nat.Coprime 4 d := by
      have := (hodd.pow_right 2).symm
      simpa using this
    have hc4 : Nat.Coprime (4 * M ^ 2) d := Nat.Coprime.mul_left h4 (hc.symm.pow_left 2)
    exact ⟨hpos, IsCoprime.mul_left (Nat.isCoprime_iff_coprime.2 hc4) h2⟩
  have hback : ∀ p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2 = F p.1 := by
    intro p
    have : IsCoprime p.1.2 (p.1.1 : ℤ) := IsCoprime.of_mul_left_right p.2.2
    simp [F, A, this]
  calc ∑' p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2
      = ∑' p : Idx (4 * M ^ 2), F p.1 := tsum_congr hback
    _ = ∑' p : ℕ × ℤ, F p := tsum_subtype_eq_of_support_subset hsupp
    _ = ∑' d : ℕ, ∑' c' : ℤ, F (d, c') := hsF.of_norm.tsum_prod
    _ = ∑' d : ℕ, b d * ∑' c' : ℤ, if IsCoprime c' (d : ℤ) then G d c' else 0 :=
        tsum_congr fun d => by
          simp only [F, A]
          exact tsum_mul_left

/- English proof (translation)
Establish `: NeZero d` using `⟨hd.ne'⟩`. Establish `hdR : (d : ℝ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hdC : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hC0 : 0 ≤ C` using `le_trans (tsum_nonneg fun _ => norm_nonneg _) (h1 0).2`. Set `A : ℤ → ℂ` to `fun c' => if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0`.

Set `e : Fin d × ℤ ≃ ℤ` to `(Equiv.prodComm _ _).trans (Int.divModEquiv d).symm`. Establish `he : ∀ p : Fin d × ℤ, e p = p.2 * d + ((p.1 : ℕ) : ℤ)` using `fun p => by`. Simplify using `[e, Int.divModEquiv_symm_apply]`. Set `t : Fin d → ℝ` to `fun r => x - ((r : ℕ) : ℝ) / d`. Set `g : Fin d → ℂ` to `fun r => if Nat.Coprime r d then GS ((r : ℕ) : ℤ) d else 0`.

Establish `hAe : ∀ (r : Fin d) (j : ℤ), A (e (r, j)) = g r * K (t r - j)`. Introduce `r j`. Establish `hcop : IsCoprime (j * d + ((r : ℕ) : ℤ)) (d : ℤ) ↔ Nat.Coprime r d`. Rewrite using `[add_comm, IsCoprime.add_mul_right_left_iff, Nat.isCoprime_iff_coprime]`. Simplify using `only [A, he, g, t]`.

Distinguish the cases in `h : Nat.Coprime r d`. Rewrite using `[if_pos (hcop.2 h), if_pos h, add_comm (j * (d : ℤ)), GS_add _ _ _ hd]`. Use `congr 2`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h' => h (hcop.1 h')), if_neg h, zero_mul]`. Establish `hg : ∀ r, ‖g r‖ ≤ d`. Introduce `r`. Simplify using `only [g]`.

Use `split_ifs`. Conclude with `GS_norm_le _ _`. Simplify using the standard rewrite rules. Establish `hfib : ∀ r : Fin d, Summable fun j : ℤ => ‖A (e (r, j))‖`. Introduce `r`.

Simplify using `only [hAe, norm_mul]`. Conclude with `(h1 (t r)).1.mul_left _`. Establish `hfibs : ∀ r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ ≤ d * C`. Introduce `r`. Simplify using `only [hAe, norm_mul]`.

Rewrite using `[tsum_mul_left]`. Conclude with `mul_le_mul (hg r) (h1 (t r)).2 (tsum_nonneg fun _ => norm_nonneg _) (Nat.cast_nonneg _)`. Establish `hsum : Summable fun p : Fin d × ℤ => ‖A (e p)‖` using `(summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨hfib, (hasSum_fintype _).summable⟩`. Establish `hs1 : Summable fun c' => ‖A c'‖` using `e.summable_iff.1 hsum`. Use `⟨hs1, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hsumA : Summable fun p : Fin d × ℤ => A (e p)` using `hsum.of_norm`. Establish `hee : ∀ (n : ℤ) (r : Fin d), ee (n * (t r : ℝ)) = ee (-(n * ((r : ℕ) : ℂ) / d)) * ee (n * x)`. Introduce `n r`. Rewrite using `[← ee_add]`.

Use `congr 1`. Simplify using `only [t]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hQs : ∀ r : Fin d, Summable fun n : ℤ => g r * (Y * Ph n * ee (n * (t r : ℝ)))`.

Introduce `r`. Use `Summable.mul_left _ (Summable.of_norm ?_)` and prove the remaining obligations. Establish `hn : ∀ n : ℤ, ‖ee (n * (t r : ℝ))‖ = 1`. Introduce `n`. Establish `: (n : ℂ) * (t r : ℝ) = (((n : ℝ) * t r : ℝ) : ℂ)` using `by push_cast; rfl`.

Rewrite using `[this, norm_ee_real]`. Simplify using `only [norm_mul, hn, mul_one]`. Conclude with `h2.mul_left _`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Simplify using `only [hAe]`. Rewrite using `[tsum_mul_left, tsum_mul_left, h3]`. Use `_ = ∑' n : ℤ, ∑ r : Fin d, g r * (Y * Ph n * ee (n * (t r : ℝ))) := (Summable.tsum_finsetSum fun r _ => hQs r).symm`. Use `_ = ∑' n : ℤ, RR n d * (Y * Ph n * ee (n * x)) := by`. Use `tsum_congr fun n => ?_` and prove the remaining obligations.

Unfold `RR`. Rewrite using `[Finset.sum_filter, Finset.sum_range, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [g]`. Distinguish the cases in `h : Nat.Coprime r d`.

Rewrite using `[if_pos h, if_pos h, hee]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg h, zero_mul, zero_mul]`.
-/
theorem inner (K : ℝ → ℂ) (Ph : ℤ → ℂ) (Y : ℂ) (C x : ℝ)
    (h1 : ∀ t : ℝ, (Summable fun j : ℤ => ‖K (t - j)‖) ∧ ∑' j : ℤ, ‖K (t - j)‖ ≤ C)
    (h2 : Summable fun n : ℤ => ‖Ph n‖)
    (h3 : ∀ t : ℝ, ∑' j : ℤ, K (t - j) = ∑' n : ℤ, Y * Ph n * ee (n * t))
    (d : ℕ) (hd : 0 < d) :
    (Summable fun c' : ℤ => ‖if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0‖) ∧
    (∑' c' : ℤ, ‖if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0‖ ≤ (d : ℝ) ^ 2 * C) ∧
    ∑' c' : ℤ, (if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0) =
      ∑' n : ℤ, RR n d * (Y * Ph n * ee (n * x)) := by
  classical
  have : NeZero d := ⟨hd.ne'⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hC0 : 0 ≤ C := le_trans (tsum_nonneg fun _ => norm_nonneg _) (h1 0).2
  let A : ℤ → ℂ := fun c' => if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0
  let e : Fin d × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv d).symm
  have he : ∀ p : Fin d × ℤ, e p = p.2 * d + ((p.1 : ℕ) : ℤ) := fun p => by
    simp [e, Int.divModEquiv_symm_apply]
  let t : Fin d → ℝ := fun r => x - ((r : ℕ) : ℝ) / d
  let g : Fin d → ℂ := fun r => if Nat.Coprime r d then GS ((r : ℕ) : ℤ) d else 0
  have hAe : ∀ (r : Fin d) (j : ℤ), A (e (r, j)) = g r * K (t r - j) := by
    intro r j
    have hcop : IsCoprime (j * d + ((r : ℕ) : ℤ)) (d : ℤ) ↔ Nat.Coprime r d := by
      rw [add_comm, IsCoprime.add_mul_right_left_iff, Nat.isCoprime_iff_coprime]
    simp only [A, he, g, t]
    by_cases h : Nat.Coprime r d
    · rw [if_pos (hcop.2 h), if_pos h, add_comm (j * (d : ℤ)), GS_add _ _ _ hd]
      congr 2
      push_cast
      field_simp
      ring
    · rw [if_neg (fun h' => h (hcop.1 h')), if_neg h, zero_mul]
  have hg : ∀ r, ‖g r‖ ≤ d := by
    intro r
    simp only [g]
    split_ifs
    · exact GS_norm_le _ _
    · simp
  have hfib : ∀ r : Fin d, Summable fun j : ℤ => ‖A (e (r, j))‖ := by
    intro r
    simp only [hAe, norm_mul]
    exact (h1 (t r)).1.mul_left _
  have hfibs : ∀ r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ ≤ d * C := by
    intro r
    simp only [hAe, norm_mul]
    rw [tsum_mul_left]
    exact mul_le_mul (hg r) (h1 (t r)).2 (tsum_nonneg fun _ => norm_nonneg _) (Nat.cast_nonneg _)
  have hsum : Summable fun p : Fin d × ℤ => ‖A (e p)‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨hfib, (hasSum_fintype _).summable⟩
  have hs1 : Summable fun c' => ‖A c'‖ := e.summable_iff.1 hsum
  refine ⟨hs1, ?_, ?_⟩
  · calc ∑' c' : ℤ, ‖A c'‖ = ∑' p : Fin d × ℤ, ‖A (e p)‖ := (e.tsum_eq fun c' => ‖A c'‖).symm
      _ = ∑' r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ := hsum.tsum_prod
      _ = ∑ r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ := tsum_fintype _
      _ ≤ ∑ _r : Fin d, (d : ℝ) * C := Finset.sum_le_sum fun r _ => hfibs r
      _ = (d : ℝ) ^ 2 * C := by simp; ring
  · have hsumA : Summable fun p : Fin d × ℤ => A (e p) := hsum.of_norm
    have hee : ∀ (n : ℤ) (r : Fin d), ee (n * (t r : ℝ)) = ee (-(n * ((r : ℕ) : ℂ) / d)) * ee (n * x) := by
      intro n r
      rw [← ee_add]
      congr 1
      simp only [t]
      push_cast
      ring
    have hQs : ∀ r : Fin d, Summable fun n : ℤ => g r * (Y * Ph n * ee (n * (t r : ℝ))) := by
      intro r
      refine Summable.mul_left _ (Summable.of_norm ?_)
      have hn : ∀ n : ℤ, ‖ee (n * (t r : ℝ))‖ = 1 := by
        intro n
        have : (n : ℂ) * (t r : ℝ) = (((n : ℝ) * t r : ℝ) : ℂ) := by push_cast; rfl
        rw [this, norm_ee_real]
      simp only [norm_mul, hn, mul_one]
      exact h2.mul_left _
    calc ∑' c' : ℤ, A c' = ∑' p : Fin d × ℤ, A (e p) := (e.tsum_eq A).symm
      _ = ∑' r : Fin d, ∑' j : ℤ, A (e (r, j)) := hsumA.tsum_prod
      _ = ∑ r : Fin d, ∑' j : ℤ, A (e (r, j)) := tsum_fintype _
      _ = ∑ r : Fin d, ∑' n : ℤ, g r * (Y * Ph n * ee (n * (t r : ℝ))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [hAe]
          rw [tsum_mul_left, tsum_mul_left, h3]
      _ = ∑' n : ℤ, ∑ r : Fin d, g r * (Y * Ph n * ee (n * (t r : ℝ))) :=
          (Summable.tsum_finsetSum fun r _ => hQs r).symm
      _ = ∑' n : ℤ, RR n d * (Y * Ph n * ee (n * x)) := by
          refine tsum_congr fun n => ?_
          unfold RR
          rw [Finset.sum_filter, Finset.sum_range, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [g]
          by_cases h : Nat.Coprime r d
          · rw [if_pos h, if_pos h, hee]
            ring
          · rw [if_neg h, if_neg h, zero_mul, zero_mul]

/- English proof (translation)
Introduce `hP1 M k ν _ h2 c s v hs hv`. Establish `hM0 : M ≠ 0` using `NeZero.ne M`. Use `set y := v.im with hy`. Use `set x := v.re with hx`. Use `set α := al k ν s with hα`.

Use `set β := be k ν s with hβ`. Establish `ha : α = s / 2 + (((ν : ℝ) + 1 - k) / 2 : ℝ)`. Simplify using `only [hα, al]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hb : β = s / 2 + (((k : ℝ) - ν) / 2 : ℝ)`. Simplify using `only [hβ, be]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : α + β = s + 1 / 2` using `by rw [ha, hb]; push_cast; ring`.

Establish `hre : 1 < (α + β).re`. Rewrite using `[hsum]`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨⟨C, hC⟩, hPh, hPo⟩` from `hP1 s α β _ _ y ha hb hre hv`.

Establish `hY : (y : ℂ) ^ (1 - α - β) = (y : ℂ) ^ (1 / 2 - s)`. Use `congr 1`. Take the linear combination `-hsum`. Use `set Y : ℂ := (y : ℂ) ^ (1 / 2 - s) with hYd`. Establish `hPo' : ∀ t : ℝ, ∑' j : ℤ, KK α β y (t - j) = ∑' n : ℤ, Y * Phi α β (n * y) * ee (n * t)`.

Introduce `t`. Rewrite using `[hPo t, hY]`. Establish `hin` using `inner (KK α β y) (fun n => Phi α β (n * y)) Y C x hC hPh hPo'`. Establish `hcs` using `coef_summable M c s hs`. Establish `hb0 : ∀ d : ℕ, ¬ Nat.Coprime d M → c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) = 0`.

Introduce `d hd`. Rewrite using `[MulChar.map_nonunit c (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]`. Establish `hidx` using `idx_tsum M h2 hM0 (fun d => c (d : ZMod M) * (d : ℂ) ^ (-(s + 1))) (fun d c' => GS c' d * KK α β y (x - c' / d)) C hb0 hcs (fun d hd => ⟨(hin d hd).1, (hin d hd).2.1⟩)`. Establish `hQ : Summable fun n : ℤ => ‖Y * Phi α β (n * y) * ee (n * x)‖`. Establish `hn : ∀ n : ℤ, ‖ee (n * x)‖ = 1`.

Introduce `n`. Simplify using `only [ee]`. Establish `: (2 * (Real.pi : ℂ) * I * (n * x)) = ((2 * Real.pi * n * x : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`. Simplify using `only [norm_mul, hn, mul_one]`.

Conclude with `hPh.mul_left _`. Establish `hsw` using `swap (fun d => c (d : ZMod M) * (d : ℂ) ^ (-(s + 1))) (fun n => Y * Phi α β (n * y) * ee (n * x)) hcs hQ`. Establish `hE : Ep c k ν s v = ∑' p : Idx (4 * M ^ 2), (c (p.1.1 : ZMod M) * (p.1.1 : ℂ) ^ (-(s + 1))) * (GS p.1.2 p.1.1 * KK α β y (x - p.1.2 / p.1.1))`. Unfold `Ep tm`. Use `tsum_congr fun p => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE, hidx]`. Establish `h1 : ∀ d : ℕ, c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * (∑' c' : ℤ, if IsCoprime c' (d : ℤ) then GS c' d * KK α β y (x - c' / d) else 0) = c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * ∑' n : ℤ, RR n d * (Y * Phi α β (n * y) * ee (n * x))`. Introduce `d`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases.

Establish `: ¬ Nat.Coprime 0 M`. Introduce `h`. Establish `: M = 1` using `by simpa using h`. Substitute `this` using the available equality. Simplify using `at h2`.

Rewrite using `[hb0 0 this, zero_mul, zero_mul]`. Rewrite using `[(hin d hd).2.2]`. Rewrite using `[tsum_congr h1, hsw]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Unfold `Dn`.

Establish `: ∀ d : ℕ, c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * RR n d = c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1))`. Introduce `d`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tsum_congr this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisenstein_cusp_zero_fourier_expansion : P1 → P2 := by
  intro hP1 M k ν _ h2 c s v hs hv
  have hM0 : M ≠ 0 := NeZero.ne M
  set y := v.im with hy
  set x := v.re with hx
  set α := al k ν s with hα
  set β := be k ν s with hβ
  have ha : α = s / 2 + (((ν : ℝ) + 1 - k) / 2 : ℝ) := by
    simp only [hα, al]; push_cast; ring
  have hb : β = s / 2 + (((k : ℝ) - ν) / 2 : ℝ) := by
    simp only [hβ, be]; push_cast; ring
  have hsum : α + β = s + 1 / 2 := by rw [ha, hb]; push_cast; ring
  have hre : 1 < (α + β).re := by
    rw [hsum]; simp; linarith
  obtain ⟨⟨C, hC⟩, hPh, hPo⟩ := hP1 s α β _ _ y ha hb hre hv
  have hY : (y : ℂ) ^ (1 - α - β) = (y : ℂ) ^ (1 / 2 - s) := by
    congr 1; linear_combination -hsum
  set Y : ℂ := (y : ℂ) ^ (1 / 2 - s) with hYd
  have hPo' : ∀ t : ℝ, ∑' j : ℤ, KK α β y (t - j) = ∑' n : ℤ, Y * Phi α β (n * y) * ee (n * t) := by
    intro t; rw [hPo t, hY]
  have hin := inner (KK α β y) (fun n => Phi α β (n * y)) Y C x hC hPh hPo'
  have hcs := coef_summable M c s hs
  have hb0 : ∀ d : ℕ, ¬ Nat.Coprime d M → c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) = 0 := by
    intro d hd
    rw [MulChar.map_nonunit c (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
  have hidx := idx_tsum M h2 hM0 (fun d => c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)))
    (fun d c' => GS c' d * KK α β y (x - c' / d)) C hb0 hcs
    (fun d hd => ⟨(hin d hd).1, (hin d hd).2.1⟩)
  have hQ : Summable fun n : ℤ => ‖Y * Phi α β (n * y) * ee (n * x)‖ := by
    have hn : ∀ n : ℤ, ‖ee (n * x)‖ = 1 := by
      intro n
      simp only [ee]
      have : (2 * (Real.pi : ℂ) * I * (n * x)) = ((2 * Real.pi * n * x : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    simp only [norm_mul, hn, mul_one]
    exact hPh.mul_left _
  have hsw := swap (fun d => c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)))
    (fun n => Y * Phi α β (n * y) * ee (n * x)) hcs hQ
  have hE : Ep c k ν s v = ∑' p : Idx (4 * M ^ 2), (c (p.1.1 : ZMod M) * (p.1.1 : ℂ) ^ (-(s + 1))) *
      (GS p.1.2 p.1.1 * KK α β y (x - p.1.2 / p.1.1)) := by
    unfold Ep tm
    refine tsum_congr fun p => ?_
    ring
  rw [hE, hidx]
  have h1 : ∀ d : ℕ, c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) *
      (∑' c' : ℤ, if IsCoprime c' (d : ℤ) then GS c' d * KK α β y (x - c' / d) else 0) =
      c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * ∑' n : ℤ, RR n d * (Y * Phi α β (n * y) * ee (n * x)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : ¬ Nat.Coprime 0 M := by
        intro h
        have : M = 1 := by simpa using h
        subst this
        simp at h2
      rw [hb0 0 this, zero_mul, zero_mul]
    · rw [(hin d hd).2.2]
  rw [tsum_congr h1, hsw]
  refine tsum_congr fun n => ?_
  unfold Dn
  have : ∀ d : ℕ, c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * RR n d = c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1)) := by
    intro d; ring
  rw [tsum_congr this]
  ring

end GlobalTheory.CompanionTheory.EisensteinPoissonSummation
