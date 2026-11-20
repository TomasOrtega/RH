import Formalism.PeriodIntegrals.WfRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf

/- English proof (translation)
Take `⟨i, hi⟩` from `ha`. Take `⟨j, hj⟩` from `hb`. Use `⟨i + j, ?_⟩` and prove the remaining obligations. Establish `e : q ^ (i + j) * (a + b) = q ^ j * (q ^ i * a) + q ^ i * (q ^ j * b)` using `by ring`. Rewrite using `[e]`.

Conclude with `S.add_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)`.
-/
private theorem exists_pow_mul_add_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a + b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a + b) = q ^ j * (q ^ i * a) + q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.add_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

/- English proof (translation)
Take `⟨i, hi⟩` from `ha`. Take `⟨j, hj⟩` from `hb`. Use `⟨i + j, ?_⟩` and prove the remaining obligations. Establish `e : q ^ (i + j) * (a - b) = q ^ j * (q ^ i * a) - q ^ i * (q ^ j * b)` using `by ring`. Rewrite using `[e]`.

Conclude with `S.sub_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)`.
-/
private theorem exists_pow_mul_sub_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a - b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a - b) = q ^ j * (q ^ i * a) - q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.sub_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

/- English proof (translation)
Take `⟨i, hi⟩` from `ha`. Take `⟨j, hj⟩` from `hb`. Use `⟨i + j, ?_⟩` and prove the remaining obligations. Establish `e : q ^ (i + j) * (a * b) = (q ^ i * a) * (q ^ j * b)` using `by ring`. Rewrite using `[e]`.

Conclude with `S.mul_mem hi hj`.
-/
private theorem exists_pow_mul_mul_mem_subring {R : Type*} [CommRing R] (S : Subring R) {q a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a * b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a * b) = (q ^ i * a) * (q ^ j * b) := by ring
  rw [e]
  exact S.mul_mem hi hj

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_` and prove the remaining obligations. Introduce `a s ha ih h`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `exists_pow_mul_add_mem_subring S q hq (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
private theorem exists_pow_mul_finset_sum_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {ι : Type*}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, ∃ k : ℕ, q ^ k * f i ∈ S) :
    ∃ k : ℕ, q ^ k * ∑ i ∈ s, f i ∈ S := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact exists_pow_mul_add_mem_subring S q hq (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `p _ σ f g hf hg`. Use `delta PI.CoefWf PI.InWf at hf hg ⊢`. Establish `hq : (p : ℂ_[p]) ∈ PI.Wp p` using `natCast_mem (PI.Wp p) p`. Use `⟨fun n => ?_, fun n => ?_, fun n => ?_, fun c hc n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`.

Conclude with `exists_pow_mul_add_mem_subring _ _ hq (hf n) (hg n)`. Rewrite using `[map_sub]`. Conclude with `exists_pow_mul_sub_mem_subring _ _ hq (hf n) (hg n)`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `exists_pow_mul_finset_sum_mem_subring _ _ hq _ _ fun x _ => exists_pow_mul_mul_mem_subring _ (hf x.1) (hg x.2)`.

Rewrite using `[MvPowerSeries.coeff_C_mul]`. Conclude with `exists_pow_mul_mul_mem_subring _ hc (hf n)`.
-/
theorem witt_ring_structure : PI.WfRing := by
  classical
  intro p _ σ f g hf hg
  delta PI.CoefWf PI.InWf at hf hg ⊢
  have hq : (p : ℂ_[p]) ∈ PI.Wp p := natCast_mem (PI.Wp p) p
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun c hc n => ?_⟩
  · rw [map_add]
    exact exists_pow_mul_add_mem_subring _ _ hq (hf n) (hg n)
  · rw [map_sub]
    exact exists_pow_mul_sub_mem_subring _ _ hq (hf n) (hg n)
  · rw [MvPowerSeries.coeff_mul]
    exact exists_pow_mul_finset_sum_mem_subring _ _ hq _ _ fun x _ => exists_pow_mul_mul_mem_subring _ (hf x.1) (hg x.2)
  · rw [MvPowerSeries.coeff_C_mul]
    exact exists_pow_mul_mul_mem_subring _ hc (hf n)
