import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Take `⟨n, rfl⟩` from `h`. Use `⟨n * M, ?_⟩` and prove the remaining obligations. Establish `: (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Use `push_cast`. Rewrite using `[mul_div_mul_right _ _ this]`.
-/
theorem den_scale_left {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((N * M : ℕ) : ℚ) := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * M, ?_⟩
  have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  rw [mul_div_mul_right _ _ this]

/- English proof (translation)
Rewrite using `[Nat.mul_comm]`. Conclude with `den_scale_left hM h`.
-/
theorem den_scale_right {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((M * N : ℕ) : ℚ) := by
  rw [Nat.mul_comm]; exact den_scale_left hM h

/- English proof (translation)
Take `⟨N, hN, H⟩` from `hh`. Take `⟨N', hN', H'⟩` from `hh'`. Use `⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩` and prove the remaining obligations. Break down `hx hr with h1 | h1` into its components or cases. Use `den_scale_left (M := N') hN' (H r h1)` as an intermediate fact.

Simplify using `using this`. Use `den_scale_right (M := N) hN (H' r h1)` as an intermediate fact. Simplify using `using this`.
-/
theorem den_union {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h')
    (x : HahnSeries ℚ Ω) (hx : x.support ⊆ h.support ∪ h'.support) : Den x := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  rcases hx hr with h1 | h1
  · have := den_scale_left (M := N') hN' (H r h1)
    simpa using this
  · have := den_scale_right (M := N) hN (H' r h1)
    simpa using this

/- English proof (translation)
Take `⟨N, hN, H⟩` from `hh`. Take `⟨N', hN', H'⟩` from `hh'`. Use `⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩` and prove the remaining obligations. Establish `hs` using `HahnSeries.support_mul_subset (x := h) (y := h') hr`. Take `⟨a, ha, b, hb, rfl⟩` from `Set.mem_add.mp hs`.

Take `⟨n, rfl⟩` from `H a ha`. Take `⟨m, rfl⟩` from `H' b hb`. Use `⟨n * N' + m * N, ?_⟩` and prove the remaining obligations. Establish `h1 : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `h2 : (N' : ℚ) ≠ 0` using `by exact_mod_cast hN'.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem den_mul {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h') :
    Den (h * h') := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  have hs := HahnSeries.support_mul_subset (x := h) (y := h') hr
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
  obtain ⟨n, rfl⟩ := H a ha
  obtain ⟨m, rfl⟩ := H' b hb
  refine ⟨n * N' + m * N, ?_⟩
  have h1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (N' : ℚ) ≠ 0 := by exact_mod_cast hN'.ne'
  push_cast
  field_simp

/- English proof (translation)
Use `⟨r.den, r.den_pos, fun s hs => ⟨r.num, ?_⟩⟩` and prove the remaining obligations. Rewrite `hs` using `[HahnSeries.coeff_single]`. Use `split_ifs at hs with hsr`. Rewrite using `[hsr]`. Conclude with `(Rat.num_div_den r).symm`.

Conclude with `(hs rfl).elim`.
-/
theorem den_single {Ω : Type} [Field Ω] (r : ℚ) (c : Ω) : Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  refine ⟨r.den, r.den_pos, fun s hs => ⟨r.num, ?_⟩⟩
  rw [HahnSeries.coeff_single] at hs
  split_ifs at hs with hsr
  · rw [hsr]; exact (Rat.num_div_den r).symm
  · exact (hs rfl).elim

/- English proof (translation)
Introduce `Ω _`. Use `⟨fun h h' hh hh' => ⟨den_union hh hh' _ (HahnSeries.support_add_subset h h'), den_union hh hh' _ (HahnSeries.support_sub_subset h h'), den_mul hh hh'⟩, fun r c => den_single r c⟩` and prove the remaining obligations.
-/
theorem den_ring : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  intro Ω _
  refine ⟨fun h h' hh hh' => ⟨den_union hh hh' _ (HahnSeries.support_add_subset h h'),
    den_union hh hh' _ (HahnSeries.support_sub_subset h h'), den_mul hh hh'⟩, fun r c => den_single r c⟩

end GlobalTheory.FN
