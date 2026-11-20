import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `I E F R _ _ _ _ e hid hort hsum p r hsurj hker`. Use `choose s hs using hsurj`. Establish `key : ∀ i x y, p i x = p i y → r (e i) * r x = r (e i) * r y`. Introduce `i x y h`. Use `hker i (x - y) (by rw [map_sub, h, sub_self])` as an intermediate fact.

Rewrite `this` using `[map_sub, mul_sub]`. Conclude with `sub_eq_zero.mp this`. Establish `hext : ∀ a b : R, (∀ i, r (e i) * a = r (e i) * b) → a = b`. Introduce `a b h`. Establish `h1 : ∑ i, r (e i) = 1` using `by rw [← map_sum, hsum, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => h i`. Use `_ = b := by rw [h1, one_mul]`. Establish `hidR : ∀ i, r (e i) * r (e i) = r (e i)` using `fun i => by rw [← map_mul, hid]`.

Set `k : F → R` to `fun c => ∑ i, r (e i) * r (s i c)`. Establish `hk0 : ∀ i c, r (e i) * k c = r (e i) * r (s i c)`. Introduce `i c`. Use `show r (e i) * ∑ j, r (e j) * r (s j c) = _`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single i]`.

Rewrite using `[← mul_assoc, hidR]`. Introduce `j _ hj`. Rewrite using `[← mul_assoc, ← map_mul, hort i j (Ne.symm hj), map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hk : ∀ i x, r (e i) * k (p i x) = r (e i) * r x`. Introduce `i x`. Rewrite using `[hk0]`. Conclude with `key i _ _ (hs i _)`. Use `⟨{ toFun := k, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hk⟩` and prove the remaining obligations.

Apply `hext` to reduce the goal to its premises. Introduce `i`. Use `hk i 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Then use the resulting hypothesis. Introduce `a b`.

Apply `hext` to reduce the goal to its premises. Introduce `i`. Establish `h` using `hk i (s i a * s i b)`. Rewrite `h` using `[map_mul, hs, hs, map_mul]`. Establish `ha` using `hk0 i a`.

Establish `hb` using `hk0 i b`. Establish `hi` using `hidR i`. Rewrite using `[h]`. Take the linear combination `(-(k b)) * ha - (r (s i a)) * hb`. Apply `hext` to reduce the goal to its premises.

Introduce `i`. Use `hk i 0` as an intermediate fact. Rewrite `this` using `[map_zero, map_zero]`. Then use the resulting hypothesis. Introduce `a b`. Apply `hext` to reduce the goal to its premises.

Introduce `i`. Establish `h` using `hk i (s i a + s i b)`. Rewrite `h` using `[map_add, hs, hs, map_add]`. Rewrite using `[h, mul_add, mul_add, hk0, hk0]`.
-/
theorem exists_diagonal_ringHom_of_letterwise_reductions :
    ∀ (I E F R : Type) [Fintype I] [CommRing E] [CommRing F] [CommRing R] (e : I → E), (∀ i, e i * e i = e i) → (∀ i j, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 → ∀ (p : I → (E →+* F)) (r : E →+* R), (∀ i, Function.Surjective (p i)) → (∀ i x, p i x = 0 → r (e i) * r x = 0) → ∃ κ : F →+* R, ∀ i x, r (e i) * κ (p i x) = r (e i) * r x := by
  intro I E F R _ _ _ _ e hid hort hsum p r hsurj hker
  classical
  choose s hs using hsurj
  have key : ∀ i x y, p i x = p i y → r (e i) * r x = r (e i) * r y := by
    intro i x y h
    have := hker i (x - y) (by rw [map_sub, h, sub_self])
    rw [map_sub, mul_sub] at this
    exact sub_eq_zero.mp this
  have hext : ∀ a b : R, (∀ i, r (e i) * a = r (e i) * b) → a = b := by
    intro a b h
    have h1 : ∑ i, r (e i) = 1 := by rw [← map_sum, hsum, map_one]
    calc a = (∑ i, r (e i)) * a := by rw [h1, one_mul]
      _ = (∑ i, r (e i)) * b := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => h i
      _ = b := by rw [h1, one_mul]
  have hidR : ∀ i, r (e i) * r (e i) = r (e i) := fun i => by rw [← map_mul, hid]
  let k : F → R := fun c => ∑ i, r (e i) * r (s i c)
  have hk0 : ∀ i c, r (e i) * k c = r (e i) * r (s i c) := by
    intro i c
    show r (e i) * ∑ j, r (e j) * r (s j c) = _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [← mul_assoc, hidR]
    · intro j _ hj
      rw [← mul_assoc, ← map_mul, hort i j (Ne.symm hj), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : ∀ i x, r (e i) * k (p i x) = r (e i) * r x := by
    intro i x
    rw [hk0]
    exact key i _ _ (hs i _)
  refine ⟨{ toFun := k, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hk⟩
  · apply hext
    intro i
    have := hk i 1
    rwa [map_one, map_one] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a * s i b)
    rw [map_mul, hs, hs, map_mul] at h
    have ha := hk0 i a
    have hb := hk0 i b
    have hi := hidR i
    rw [h]
    linear_combination (-(k b)) * ha - (r (s i a)) * hb
  · apply hext
    intro i
    have := hk i 0
    rwa [map_zero, map_zero] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a + s i b)
    rw [map_add, hs, hs, map_add] at h
    rw [h, mul_add, mul_add, hk0, hk0]

end GlobalTheory
