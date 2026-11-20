import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section SdClosed

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

/- English proof (translation)
Simplify using `only [LTo0, Nat.cofinite_eq_atTop, eventually_atTop]`.
-/
theorem lTo0_atTop {w : ℕ → Wq l a} : LTo0 l w ↔ ∀ r : ℕ, ∃ N, ∀ n ≥ N, (l : Wq l a) ^ r ∣ w n := by
  simp only [LTo0, Nat.cofinite_eq_atTop, eventually_atTop]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun r => Eventually.of_forall fun _ => dvd_zero _, fun τ n => by simp⟩`.
-/
theorem sdSet_zero : (0 : ZMod a → K⟦X⟧) ∈ SdSet t K e :=
  ⟨0, fun r => Eventually.of_forall fun _ => dvd_zero _, fun τ n => by simp⟩

/- English proof (translation)
Use `⟨fun n => if n = 0 then 1 else 0, lTo0_atTop.2 fun r => ⟨1, fun n hn => ?_⟩, fun τ n => ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg (by omega)]; exact dvd_zero _`. Rewrite using `[Pi.one_apply, coeff_one]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hn]`.
-/
theorem sdSet_one : (1 : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun n => if n = 0 then 1 else 0, lTo0_atTop.2 fun r => ⟨1, fun n hn => ?_⟩, fun τ n => ?_⟩
  · rw [if_neg (by omega)]; exact dvd_zero _
  · rw [Pi.one_apply, coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

/- English proof (translation)
Take `⟨w, hw, hF⟩` from `hF`. Use `⟨-w, fun r => (hw r).mono fun n hn => ?_, fun τ n => ?_⟩` and prove the remaining obligations. Simplify using `using hn`. Simplify using `[hF τ n]`.
-/
theorem sdSet_neg {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : -F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, fun r => (hw r).mono fun n hn => ?_, fun τ n => ?_⟩
  · simpa using hn
  · simp [hF τ n]

/- English proof (translation)
Take `⟨w, hw, hF⟩` from `hF`. Take `⟨w', hw', hG⟩` from `hG`. Use `⟨w + w', fun r => ((hw r).and (hw' r)).mono fun n hn => ?_, fun τ n => ?_⟩` and prove the remaining obligations. Conclude with `dvd_add hn.1 hn.2`. Simplify using `[mul_add, hF τ n, hG τ n]`.
-/
theorem sdSet_add {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F + G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', fun r => ((hw r).and (hw' r)).mono fun n hn => ?_, fun τ n => ?_⟩
  · exact dvd_add hn.1 hn.2
  · simp [mul_add, hF τ n, hG τ n]

/- English proof (translation)
The claim follows from `(Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div i j e))`.
-/
theorem fact_div_dvd (e i j : ℕ) : (i / e).factorial * (j / e).factorial ∣ ((i + j) / e).factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div i j e))

/- English proof (translation)
Take `⟨w, hw, hF⟩` from `hF`. Take `⟨w', hw', hG⟩` from `hG`. Set `q : ℕ → ℕ → ℕ` to `fun i j => ((i + j) / e).factorial / ((i / e).factorial * (j / e).factorial)`. Establish `hq : ∀ i j, ((i + j) / e).factorial = q i j * ((i / e).factorial * (j / e).factorial)` using `fun i j => (Nat.div_mul_cancel (fact_div_dvd e i j)).symm`. Use `⟨fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, q p.1 p.2 • (w p.1 * w' p.2), ?_, fun τ n => ?_⟩` and prove the remaining obligations.

Rewrite `hw`, `hw'`, the goal using `[lTo0_atTop]`. Introduce `r`. Take `⟨N, hN⟩` from `hw r`. Take `⟨N', hN'⟩` from `hw' r`. Use `⟨N + N', fun n hn => Finset.dvd_sum fun p hp => ?_⟩` and prove the remaining obligations.

Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[nsmul_eq_mul]`. Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Distinguish the cases in `h1 : N ≤ p.1`. Conclude with `(hN _ h1).mul_right _`.

Conclude with `(hN' _ (by omega)).mul_left _`. Rewrite using `[Pi.mul_apply, coeff_mul, Finset.mul_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[map_nsmul, map_nsmul, nsmul_eq_mul, map_mul, map_mul, ← hF τ p.1, ← hG τ p.2, ← hp, hq p.1 p.2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sdSet_mul {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F * G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let q : ℕ → ℕ → ℕ := fun i j => ((i + j) / e).factorial / ((i / e).factorial * (j / e).factorial)
  have hq : ∀ i j, ((i + j) / e).factorial = q i j * ((i / e).factorial * (j / e).factorial) := fun i j =>
    (Nat.div_mul_cancel (fact_div_dvd e i j)).symm
  refine ⟨fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, q p.1 p.2 • (w p.1 * w' p.2), ?_, fun τ n => ?_⟩
  · rw [lTo0_atTop] at hw hw' ⊢
    intro r
    obtain ⟨N, hN⟩ := hw r
    obtain ⟨N', hN'⟩ := hw' r
    refine ⟨N + N', fun n hn => Finset.dvd_sum fun p hp => ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [nsmul_eq_mul]
    apply Dvd.dvd.mul_left
    by_cases h1 : N ≤ p.1
    · exact (hN _ h1).mul_right _
    · exact (hN' _ (by omega)).mul_left _
  · rw [Pi.mul_apply, coeff_mul, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, map_mul, map_mul, ← hF τ p.1, ← hG τ p.2, ← hp, hq p.1 p.2]
    push_cast
    ring

/- English proof (translation)
Set `S : Subring (ZMod a → K⟦X⟧)` to `{ carrier := SdSet t K e zero_mem' := sdSet_zero t e one_mem' := sdSet_one t e add_mem' := fun hF hG => sdSet_add t e hF hG mul_mem' := fun hF hG => sdSet_mul t e hF hG neg_mem' := fun hF => sdSet_neg t e hF }`. Introduce `F hF`. Conclude with `(Subring.closure_le.2 (fun x hx => hx) : Sd t K e ≤ S) hF`.
-/
theorem sd_sub_sdSet : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  let S : Subring (ZMod a → K⟦X⟧) :=
    { carrier := SdSet t K e
      zero_mem' := sdSet_zero t e
      one_mem' := sdSet_one t e
      add_mem' := fun hF hG => sdSet_add t e hF hG
      mul_mem' := fun hF hG => sdSet_mul t e hF hG
      neg_mem' := fun hF => sdSet_neg t e hF }
  intro F hF
  exact (Subring.closure_le.2 (fun x hx => hx) : Sd t K e ≤ S) hF

end SdClosed

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t`. Conclude with `sd_sub_sdSet t e`.
-/
theorem sdSet_closed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact sd_sub_sdSet t e

end GlobalTheory.CrysPrism
