import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar

variable {r : ℕ}

/- English proof (translation)
Simplify using `[Pi.single_eq_of_ne h.symm]`.
-/
lemma add_single_apply_ne {i k : Fin r} (h : k ≠ i) (m : Fin r → ℕ) (e : ℕ) :
    (m + (Pi.single k e : Fin r → ℕ)) i = m i := by
  simp [Pi.single_eq_of_ne h.symm]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[Pi.single_eq_of_ne h.symm]`. Simplify using `[Function.update_of_ne hj]`.
-/
lemma update_add_single {i k : Fin r} (h : k ≠ i) (m : Fin r → ℕ) (e t : ℕ) :
    Function.update (m + (Pi.single k e : Fin r → ℕ)) i t = Function.update m i t + (Pi.single k e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Pi.single_eq_of_ne h.symm]
  · simp [Function.update_of_ne hj]

/- English proof (translation)
Unfold `partialSum`. Rewrite using `[add_single_apply_ne h]`. Conclude with `Finset.sum_congr rfl fun t _ => by rw [update_add_single h]`.
-/
lemma partialSum_shift {i k : Fin r} (h : k ≠ i) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (e : ℕ) :
    partialSum i v (m + (Pi.single k e : Fin r → ℕ)) =
      ∑ t ∈ Finset.range (m i), v (Function.update m i t + (Pi.single k e : Fin r → ℕ)) := by
  unfold partialSum
  rw [add_single_apply_ne h]
  exact Finset.sum_congr rfl fun t _ => by rw [update_add_single h]

/- English proof (translation)
Unfold `meanP`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun t _ => by rw [update_add_single h]`.
-/
lemma meanP_shift (l : ℕ) {i k : Fin r} (h : k ≠ i) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (e : ℕ) :
    meanP l i v (m + (Pi.single k e : Fin r → ℕ)) =
      (∑ t ∈ Finset.range l, partialSum i v (Function.update m i t + (Pi.single k e : Fin r → ℕ))) / l := by
  unfold meanP
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [update_add_single h]

/- English proof (translation)
Rewrite using `[partialSum_shift h]`. Unfold `partialSum`. Conclude with `Finset.sum_congr rfl fun t _ => hp _`.
-/
lemma partialSum_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    partialSum i v (m + (Pi.single k l : Fin r → ℕ)) = partialSum i v m := by
  rw [partialSum_shift h]
  unfold partialSum
  exact Finset.sum_congr rfl fun t _ => hp _

/- English proof (translation)
Rewrite using `[meanP_shift l h]`. Unfold `meanP`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun t _ => partialSum_period h hp _`.
-/
lemma meanP_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    meanP l i v (m + (Pi.single k l : Fin r → ℕ)) = meanP l i v m := by
  rw [meanP_shift l h]
  unfold meanP
  congr 1
  exact Finset.sum_congr rfl fun t _ => partialSum_period h hp _

/- English proof (translation)
Repeatedly rewrite using `[partialSum_shift h]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_eq_zero fun t _ => hz _`.
-/
lemma partialSum_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, partialSum i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  simp_rw [partialSum_shift h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t _ => hz _

/- English proof (translation)
Repeatedly rewrite using `[meanP_shift l h]`. Rewrite using `[← Finset.sum_div, Finset.sum_comm]`. Rewrite using `[Finset.sum_eq_zero fun t _ => partialSum_zero h hz _, zero_div]`.
-/
lemma meanP_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, meanP l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  simp_rw [meanP_shift l h]
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_eq_zero fun t _ => partialSum_zero h hz _, zero_div]

/- English proof (translation)
Unfold `Aop`. Rewrite using `[add_right_comm, partialSum_period h hp, meanP_period h hp]`.
-/
lemma Aop_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    Aop l i v (m + (Pi.single k l : Fin r → ℕ)) = Aop l i v m := by
  unfold Aop
  rw [add_right_comm, partialSum_period h hp, meanP_period h hp]

/- English proof (translation)
Unfold `Bop`. Rewrite using `[add_single_apply_ne h, meanP_period h hp]`.
-/
lemma Bop_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    Bop l i v (m + (Pi.single k l : Fin r → ℕ)) = Bop l i v m := by
  unfold Bop
  rw [add_single_apply_ne h, meanP_period h hp]

/- English proof (translation)
Unfold `Aop`. Rewrite using `[Finset.sum_sub_distrib, meanP_zero h hz, sub_zero]`. Repeatedly rewrite using `[add_right_comm m]`. Conclude with `partialSum_zero h hz _`.
-/
lemma Aop_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, Aop l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  unfold Aop
  rw [Finset.sum_sub_distrib, meanP_zero h hz, sub_zero]
  simp_rw [add_right_comm m]
  exact partialSum_zero h hz _

/- English proof (translation)
Unfold `Bop`. Repeatedly rewrite using `[add_single_apply_ne h]`. Distinguish the cases in `h0 : m i = 0`. Simplify using `only [h0, if_true]`. Conclude with `meanP_zero h hz m`.

Simplify using `[h0]`.
-/
lemma Bop_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, Bop l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  unfold Bop
  simp_rw [add_single_apply_ne h]
  by_cases h0 : m i = 0
  · simp only [h0, if_true]
    exact meanP_zero h hz m
  · simp [h0]

/- English proof (translation)
Unfold `partialSum`. Use `Finset.sum_eq_zero fun t _ => hs _ ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne h]` and apply the resulting hypothesis.
-/
lemma partialSum_support {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hs : ∀ m, m k ≠ 0 → v m = 0) (m : Fin r → ℕ) (hm : m k ≠ 0) : partialSum i v m = 0 := by
  unfold partialSum
  refine Finset.sum_eq_zero fun t _ => hs _ ?_
  rwa [Function.update_of_ne h]

/- English proof (translation)
Unfold `meanP`. Rewrite using `[Finset.sum_eq_zero fun t _ => partialSum_support h hs _ (by rwa [Function.update_of_ne h]), zero_div]`.
-/
lemma meanP_support (l : ℕ) {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hs : ∀ m, m k ≠ 0 → v m = 0) (m : Fin r → ℕ) (hm : m k ≠ 0) : meanP l i v m = 0 := by
  unfold meanP
  rw [Finset.sum_eq_zero fun t _ => partialSum_support h hs _ (by rwa [Function.update_of_ne h]), zero_div]

/- English proof (translation)
Use `⟨fun hg => ⟨⟨Aop_period h hg.1, Aop_zero h hg.2⟩, ⟨Bop_period h hg.1, Bop_zero h hg.2⟩⟩, fun hs => ⟨fun m hm => ?_, fun m hm => ?_⟩⟩` and prove the remaining obligations. Unfold `Aop`. Rewrite using `[partialSum_support h hs _ (by simpa [Pi.single_eq_of_ne h] using hm), meanP_support l h hs m hm, sub_zero]`. Unfold `Bop`. Rewrite using `[meanP_support l h hs m hm, ite_self]`.
-/
theorem good_support_other (r l : ℕ) (i k : Fin r) (v : (Fin r → ℕ) → ℚ) (h : k ≠ i) :
    (GoodAt l k v → GoodAt l k (Aop l i v) ∧ GoodAt l k (Bop l i v)) ∧
    ((∀ m, m k ≠ 0 → v m = 0) → (∀ m, m k ≠ 0 → Aop l i v m = 0) ∧ (∀ m, m k ≠ 0 → Bop l i v m = 0)) := by
  refine ⟨fun hg => ⟨⟨Aop_period h hg.1, Aop_zero h hg.2⟩, ⟨Bop_period h hg.1, Bop_zero h hg.2⟩⟩, fun hs => ⟨fun m hm => ?_, fun m hm => ?_⟩⟩
  · unfold Aop
    rw [partialSum_support h hs _ (by simpa [Pi.single_eq_of_ne h] using hm), meanP_support l h hs m hm, sub_zero]
  · unfold Bop
    rw [meanP_support l h hs m hm, ite_self]

/- English proof (translation)
Introduce `r l i k v h` and use `good_support_other r l i k v h`.
-/
theorem otherVar_main : ∀ (r l : ℕ) (i k : Fin r) (v : (Fin r → ℕ) → ℚ), k ≠ i →
    (GoodAt l k v → GoodAt l k (Aop l i v) ∧ GoodAt l k (Bop l i v)) ∧
    ((∀ m, m k ≠ 0 → v m = 0) → (∀ m, m k ≠ 0 → Aop l i v m = 0) ∧ (∀ m, m k ≠ 0 → Bop l i v m = 0)) :=
  fun r l i k v h => good_support_other r l i k v h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar
