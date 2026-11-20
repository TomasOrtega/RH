import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section Closed

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a]

/- English proof (translation)
Introduce `_` and use `Eventually.of_forall fun _ => dvd_zero _`.
-/
theorem LTo0_zero {ι : Type} : LTo0 l (0 : ι → Wq l a) :=
  fun _ => Eventually.of_forall fun _ => dvd_zero _

/- English proof (translation)
Introduce `r` and use `((h r).and (h' r)).mono fun _ hp => dvd_add hp.1 hp.2`.
-/
theorem LTo0_add {ι : Type} {w w' : ι → Wq l a} (h : LTo0 l w) (h' : LTo0 l w') : LTo0 l (w + w') :=
  fun r => ((h r).and (h' r)).mono fun _ hp => dvd_add hp.1 hp.2

/- English proof (translation)
Introduce `r` and use `(h r).mono fun _ hp => (dvd_neg).2 hp`.
-/
theorem LTo0_neg {ι : Type} {w : ι → Wq l a} (h : LTo0 l w) : LTo0 l (-w) :=
  fun r => (h r).mono fun _ hp => (dvd_neg).2 hp

/- English proof (translation)
Introduce `_` and use `(eventually_cofinite_ne ((0 : ℕ), (0 : ℕ))).mono fun _ hp => by simp [hp]`.
-/
theorem LTo0_single : LTo0 l (fun p : ℕ × ℕ => if p = (0, 0) then (1 : Wq l a) else 0) :=
  fun _ => (eventually_cofinite_ne ((0 : ℕ), (0 : ℕ))).mono fun _ hp => by simp [hp]

/- English proof (translation)
Introduce `r`. Establish `hB` using `h r`. Establish `hB'` using `h' r`. Rewrite `hB`, `hB'`, the goal using `[Filter.eventually_cofinite]`. Use `((hB.prod hB').image fun pq : (ℕ × ℕ) × (ℕ × ℕ) => pq.1 + pq.2).subset ?_` and prove the remaining obligations.

Introduce and unpack `⟨i, n⟩ hp`. Assume the negation of the conclusion as `hni`. Apply `hp` to reduce the goal to its premises. Use `Finset.dvd_sum fun x hx => Finset.dvd_sum fun y hy => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : (l : Wq l a) ^ r ∣ w (x.1, y.1)`.

Conclude with `dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _`. Distinguish the cases in `h2 : (l : Wq l a) ^ r ∣ w' (x.2, y.2)`. Conclude with `dvd_mul_of_dvd_right h2 _`. Rewrite `hx`, `hy` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Conclude with `(hni ⟨((x.1, y.1), (x.2, y.2)), ⟨h1, h2⟩, by simp [Prod.mk_add_mk, hx, hy]⟩).elim`.
-/
theorem LTo0_conv {w w' : ℕ × ℕ → Wq l a} (h : LTo0 l w) (h' : LTo0 l w')
    (c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ) :
    LTo0 l (fun p : ℕ × ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      (c p.1 p.2 x y : Wq l a) * w (x.1, y.1) * w' (x.2, y.2)) := by
  intro r
  have hB := h r
  have hB' := h' r
  rw [Filter.eventually_cofinite] at hB hB' ⊢
  refine ((hB.prod hB').image fun pq : (ℕ × ℕ) × (ℕ × ℕ) => pq.1 + pq.2).subset ?_
  rintro ⟨i, n⟩ hp
  by_contra hni
  apply hp
  refine Finset.dvd_sum fun x hx => Finset.dvd_sum fun y hy => ?_
  by_cases h1 : (l : Wq l a) ^ r ∣ w (x.1, y.1)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _
  by_cases h2 : (l : Wq l a) ^ r ∣ w' (x.2, y.2)
  · exact dvd_mul_of_dvd_right h2 _
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  exact (hni ⟨((x.1, y.1), (x.2, y.2)), ⟨h1, h2⟩, by simp [Prod.mk_add_mk, hx, hy]⟩).elim

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, LTo0_zero, fun τ i n => by simp⟩`.
-/
theorem PPSet_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e :=
  ⟨0, LTo0_zero, fun τ i n => by simp⟩

/- English proof (translation)
Use `⟨_, LTo0_single, fun τ i n => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.one_apply, coeff_one]`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hn]`. Simplify using `[hi]`.
-/
theorem PPSet_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e := by
  refine ⟨_, LTo0_single, fun τ i n => ?_⟩
  simp only [Pi.one_apply, coeff_one]
  by_cases hi : i = 0
  · subst hi
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · simp [hi]

/- English proof (translation)
Take `⟨w, hw, hF⟩` from `hF`. Take `⟨w', hw', hG⟩` from `hG`. Use `⟨w + w', LTo0_add hw hw', fun τ i n => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, map_add, mul_add, hF, hG]`.
-/
theorem PPSet_add {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F + G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', LTo0_add hw hw', fun τ i n => ?_⟩
  simp only [Pi.add_apply, map_add, mul_add, hF, hG]

/- English proof (translation)
Take `⟨w, hw, hF⟩` from `hF`. Use `⟨-w, LTo0_neg hw, fun τ i n => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.neg_apply, map_neg, mul_neg, hF]`.
-/
theorem PPSet_neg {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : -F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, LTo0_neg hw, fun τ i n => ?_⟩
  simp only [Pi.neg_apply, map_neg, mul_neg, hF]

/- English proof (translation)
Take `⟨w, hw, hF⟩` from `hF`. Take `⟨w', hw', hG⟩` from `hG`. Set `c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ` to `fun i n x y => (i.factorial * (n / e).factorial) / ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))`. Use `⟨_, LTo0_conv hw hw' c, fun τ i n => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n, i.factorial * (n / e).factorial = c i n x y * ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))`.

Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use `(Nat.div_mul_cancel ?_).symm` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm]`. Apply `mul_dvd_mul` to reduce the goal to its premises.

Rewrite using `[← hx]`. Conclude with `Nat.factorial_mul_factorial_dvd_factorial_add _ _`. Conclude with `(Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (by rw [← hy]; exact Nat.add_div_le_add_div _ _ _))`. Simplify using `only [Pi.mul_apply, coeff_mul, map_sum, Finset.mul_sum, map_mul, map_natCast]`. Use `Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[hc x hx y hy, ← hF τ x.1 y.1, ← hG τ x.2 y.2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PPSet_mul {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F * G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ := fun i n x y =>
    (i.factorial * (n / e).factorial) /
      ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))
  refine ⟨_, LTo0_conv hw hw' c, fun τ i n => ?_⟩
  have hc : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      i.factorial * (n / e).factorial =
        c i n x y * ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial)) := by
    intro x hx y hy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    refine (Nat.div_mul_cancel ?_).symm
    rw [mul_mul_mul_comm]
    apply mul_dvd_mul
    · rw [← hx]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    · exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
        (Nat.factorial_dvd_factorial (by rw [← hy]; exact Nat.add_div_le_add_div _ _ _))
  simp only [Pi.mul_apply, coeff_mul, map_sum, Finset.mul_sum, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [hc x hx y hy, ← hF τ x.1 y.1, ← hG τ x.2 y.2]
  push_cast
  ring

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF`. Set `S : Subring (ZMod a → K⟦X⟧⟦X⟧)` to `{ carrier := PPSet t K e mul_mem' := PPSet_mul t e one_mem' := PPSet_one t e add_mem' := PPSet_add t e zero_mem' := PPSet_zero t e neg_mem' := PPSet_neg t e }`. Conclude with `(Subring.closure_le (t := S)).2 le_rfl hF`.
-/
theorem PPd_subset_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  let S : Subring (ZMod a → K⟦X⟧⟦X⟧) :=
    { carrier := PPSet t K e
      mul_mem' := PPSet_mul t e
      one_mem' := PPSet_one t e
      add_mem' := PPSet_add t e
      zero_mem' := PPSet_zero t e
      neg_mem' := PPSet_neg t e }
  exact (Subring.closure_le (t := S)).2 le_rfl hF

end Closed

end GlobalTheory.CrysPrism
