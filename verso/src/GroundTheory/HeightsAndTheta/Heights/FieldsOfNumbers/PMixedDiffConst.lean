import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace MixedDiffConst

variable {K : Type}

def shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  aeval (fun k => X k - C ((b k : ℤ) : ℚ)) p

def polyStep (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  p - shiftPoly b p

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [shiftPoly]`. Consider the case `add p q hp hq => simp only [shiftPoly, map_add] at hp hq ⊢`. Rewrite using `[hp, hq]`. Consider the case `mul_X p k hp => simp only [shiftPoly, map_mul] at hp ⊢`.

Rewrite using `[hp]`. Simplify using the standard rewrite rules.
-/
theorem eval_shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) (x : K → ℚ) :
    eval x (shiftPoly b p) = eval (fun k => x k - b k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shiftPoly]
  | add p q hp hq => simp only [shiftPoly, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p k hp => simp only [shiftPoly, map_mul] at hp ⊢; rw [hp]; simp

/- English proof (translation)
Use `MvPolynomial.induction_on_monomial (motive := fun q => (shiftPoly b q).totalDegree ≤ q.totalDegree ∧ (polyStep b q = 0 ∨ (polyStep b q).totalDegree + 1 ≤ q.totalDegree)) ?_ ?_ s a` and prove the remaining obligations. Introduce `a`. Simplify using `[shiftPoly, polyStep]`. Introduce `p k hp`. Take `⟨h1, h2⟩` from `hp`.

Distinguish the cases in `hp0 : p = 0`. Substitute `hp0` using the available equality. Simplify using `[shiftPoly, polyStep]`. Establish `hdeg : (p * X k).totalDegree = p.totalDegree + 1`. Rewrite using `[totalDegree_mul_of_isDomain hp0 (X_ne_zero k), totalDegree_X]`.

Establish `hXC : (X k - C ((b k : ℤ) : ℚ) : MvPolynomial K ℚ).totalDegree ≤ 1` using `(totalDegree_sub _ _).trans (max_le (totalDegree_X k).le (by rw [totalDegree_C]; omega))`. Establish `hsh : shiftPoly b (p * X k) = shiftPoly b p * (X k - C ((b k : ℤ) : ℚ))`. Simplify using `[shiftPoly]`. Establish `hst : polyStep b (p * X k) = polyStep b p * X k + C ((b k : ℤ) : ℚ) * shiftPoly b p`. Rewrite using `[polyStep, polyStep, hsh]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[hsh, hdeg]`. Conclude with `(totalDegree_mul _ _).trans (add_le_add h1 hXC)`. Rewrite using `[hst, hdeg, add_le_add_iff_right]`.

Use `(totalDegree_add _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Break down `h2 with h2 | h2` into its components or cases. Rewrite using `[h2, zero_mul, totalDegree_zero]`. Conclude with `zero_le`. Conclude with `(totalDegree_mul _ _).trans (by rw [totalDegree_X]; exact h2)`.

Conclude with `(totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact h1)`.
-/
theorem monomial_good (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    (shiftPoly b (monomial s a)).totalDegree ≤ (monomial s a).totalDegree ∧
      (polyStep b (monomial s a) = 0 ∨
        (polyStep b (monomial s a)).totalDegree + 1 ≤ (monomial s a).totalDegree) := by
  refine MvPolynomial.induction_on_monomial (motive := fun q =>
    (shiftPoly b q).totalDegree ≤ q.totalDegree ∧
      (polyStep b q = 0 ∨ (polyStep b q).totalDegree + 1 ≤ q.totalDegree)) ?_ ?_ s a
  · intro a; simp [shiftPoly, polyStep]
  · intro p k hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hp0 : p = 0
    · subst hp0; simp [shiftPoly, polyStep]
    have hdeg : (p * X k).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero k), totalDegree_X]
    have hXC : (X k - C ((b k : ℤ) : ℚ) : MvPolynomial K ℚ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X k).le (by rw [totalDegree_C]; omega))
    have hsh : shiftPoly b (p * X k) = shiftPoly b p * (X k - C ((b k : ℤ) : ℚ)) := by
      simp [shiftPoly]
    have hst : polyStep b (p * X k) = polyStep b p * X k + C ((b k : ℤ) : ℚ) * shiftPoly b p := by
      rw [polyStep, polyStep, hsh]; ring
    refine ⟨?_, Or.inr ?_⟩
    · rw [hsh, hdeg]
      exact (totalDegree_mul _ _).trans (add_le_add h1 hXC)
    · rw [hst, hdeg, add_le_add_iff_right]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rcases h2 with h2 | h2
        · rw [h2, zero_mul, totalDegree_zero]; exact zero_le
        · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; exact h2)
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact h1)

/- English proof (translation)
Establish `hs : shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p))` using `by conv_lhs => rw [p.as_sum]`. Simplify using `only [shiftPoly, map_sum]`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Simplify using `only [polyStep, Finset.sum_sub_distrib]`. Rewrite using `[← hs, ← p.as_sum]`.
-/
theorem sum_eq (b : K → ℤ) (p : MvPolynomial K ℚ) :
    shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) ∧
      polyStep b p = ∑ v ∈ p.support, polyStep b (monomial v (coeff v p)) := by
  have hs : shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    simp only [shiftPoly, map_sum]
  refine ⟨hs, ?_⟩
  simp only [polyStep, Finset.sum_sub_distrib]
  rw [← hs, ← p.as_sum]

/- English proof (translation)
The claim follows from `(totalDegree_monomial_le _ _).trans (le_totalDegree hv)`.
-/
theorem monomial_le (p : MvPolynomial K ℚ) {v : K →₀ ℕ} (hv : v ∈ p.support) :
    (monomial v (coeff v p)).totalDegree ≤ p.totalDegree :=
  (totalDegree_monomial_le _ _).trans (le_totalDegree hv)

/- English proof (translation)
Distinguish the cases in `h0 : p.totalDegree = 0`. Use `left`. Rewrite `h0` using `[totalDegree_eq_zero_iff_eq_C]`. Rewrite using `[h0]`. Simplify using `[polyStep, shiftPoly]`.

Use `right`. Establish `: (polyStep b p).totalDegree ≤ p.totalDegree - 1`. Rewrite using `[(sum_eq b p).2]`. Use `totalDegree_finsetSum_le fun v hv => ?_` and prove the remaining obligations. Break down `(monomial_good b v (coeff v p)).2 with h | h` into its components or cases.

Rewrite using `[h, totalDegree_zero]`. Conclude with `zero_le`. Use `monomial_le p hv` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem polyStep_deg (b : K → ℤ) (p : MvPolynomial K ℚ) :
    polyStep b p = 0 ∨ (polyStep b p).totalDegree + 1 ≤ p.totalDegree := by
  by_cases h0 : p.totalDegree = 0
  · left
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0]; simp [polyStep, shiftPoly]
  · right
    have : (polyStep b p).totalDegree ≤ p.totalDegree - 1 := by
      rw [(sum_eq b p).2]
      refine totalDegree_finsetSum_le fun v hv => ?_
      rcases (monomial_good b v (coeff v p)).2 with h | h
      · rw [h, totalDegree_zero]; exact zero_le
      · have := monomial_le p hv; omega
    omega

section Eventual

/- English proof (translation)
Establish `ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop`. Simplify `tendsto_atTop_add_const_right atTop (-b) tendsto_id` using `[sub_eq_add_neg]`. Use `filter_upwards [hq, ht.eventually hq] with m h1 h2`. Simplify using `only [diffStep, polyStep, map_sub, eval_shiftPoly]`. Rewrite using `[Int.cast_sub, h1, h2]`.

Simplify using `[Pi.sub_apply]`.
-/
theorem eventuallyPoly_diffStep (b : K → ℤ) {g : (K → ℤ) → ℤ} {q : MvPolynomial K ℚ}
    (hq : EventuallyPoly g q) : EventuallyPoly (diffStep b g) (polyStep b q) := by
  have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-b) tendsto_id
  filter_upwards [hq, ht.eventually hq] with m h1 h2
  simp only [diffStep, polyStep, map_sub, eval_shiftPoly]
  rw [Int.cast_sub, h1, h2]
  simp [Pi.sub_apply]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simpa using hp`. Consider the case `cons b L ih => simpa using eventuallyPoly_diffStep b ih`.
-/
theorem eventuallyPoly_foldr (L : List (K → ℤ)) {h : (K → ℤ) → ℤ} {p : MvPolynomial K ℚ}
    (hp : EventuallyPoly h p) : EventuallyPoly (L.foldr diffStep h) (L.foldr polyStep p) := by
  induction L with
  | nil => simpa using hp
  | cons b L ih => simpa using eventuallyPoly_diffStep b ih

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons b L ih`. Simplify using `only [List.foldr_cons, List.length_cons]`. Break down `ih with h0 | hd` into its components or cases.

Use `left`. Rewrite using `[h0]`. Simplify using `[polyStep, shiftPoly]`. Break down `polyStep_deg b (L.foldr polyStep p) with h | h` into its components or cases. Conclude with `Or.inl h`.

Use `right`. Use linear arithmetic over natural numbers and integers.
-/
theorem foldr_polyStep_deg (L : List (K → ℤ)) (p : MvPolynomial K ℚ) :
    L.foldr polyStep p = 0 ∨ (L.foldr polyStep p).totalDegree + L.length ≤ p.totalDegree := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rcases ih with h0 | hd
    · left; rw [h0]; simp [polyStep, shiftPoly]
    · rcases polyStep_deg b (L.foldr polyStep p) with h | h
      · exact Or.inl h
      · right; omega

end Eventual

end MixedDiffConst

open MixedDiffConst in

/- English proof (translation)
Introduce `F _ K _ _ ι _ I hI hrel n hn`. Take `⟨p, hp⟩` from `h2 F K ι I hI`. Establish `hdeg : p.totalDegree ≤ n`. Distinguish the cases in `hp0 : p = 0`. Simplify using `[hp0]`.

Use `(h1 F K ι I hI).1 hrel p hp hp0` as an intermediate fact. Rewrite `this` using `[hn]`. Conclude with `this` after adjusting the coercions. Establish `key : ∀ (r : ℕ) (bs : Fin r → K → ℤ), n ≤ r → ∃ c : ℚ, (n < r → c = 0) ∧ ∀ᶠ m in atTop, (mixedDiff bs (hilbFn I) m : ℚ) = c`. Introduce `r bs hr`.

Establish `hE` using `eventuallyPoly_foldr (List.ofFn bs) hp`. Break down `foldr_polyStep_deg (List.ofFn bs) p with h0 | hd` into its components or cases. Use `⟨0, fun _ => rfl, ?_⟩ filter_upwards [hE] with m hm` and prove the remaining obligations. Rewrite using `[mixedDiff, hm, h0, map_zero]`. Rewrite `hd` using `[List.length_ofFn]`.

Establish `hq0 : ((List.ofFn bs).foldr polyStep p).totalDegree = 0` using `by omega`. Use `⟨coeff 0 ((List.ofFn bs).foldr polyStep p), fun hlt => by omega, ?_⟩` and prove the remaining obligations. Rewrite `hq0` using `[totalDegree_eq_zero_iff_eq_C]`. Use `filter_upwards [hE] with m hm`. Rewrite using `[mixedDiff, hm, hq0, eval_C, coeff_C, if_pos rfl]`.

Prove the components needed by the constructor for the conclusion. Introduce `bs`. Take `⟨c, -, hc⟩` from `key n bs le_rfl`. Take `⟨m0, hm0⟩` from `hc.exists`. Establish `hc' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = mixedDiff bs (hilbFn I) m0` using `hc.mono fun m hm => by exact_mod_cast hm.trans hm0.symm`.

Establish `hex : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = c` using `⟨_, hc'⟩`. Establish `hval : intNum F I bs = mixedDiff bs (hilbFn I) m0`. Unfold `intNum eventualValue`. Rewrite using `[dif_pos hex]`. Take `⟨m, hm1, hm2⟩` from `(hex.choose_spec.and hc').exists`.

Rewrite using `[← hm1, hm2]`. Use `filter_upwards [hc'] with m hm`. Rewrite using `[hm, hval]`. Introduce `r hr bs`. Take `⟨c, hc0, hc⟩` from `key r bs hr.le`.

Use `filter_upwards [hc] with m hm`. Rewrite `hm` using `[hc0 hr]`. Conclude with `hm` after adjusting the coercions.
-/
theorem MixedDiffConst.proof (h1 : HilbDegreeBound.Statement.{u})
    (h2 : HilbEventuallyPoly.Statement.{u}) : MixedDiffConst.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn
  obtain ⟨p, hp⟩ := h2 F K ι I hI
  have hdeg : p.totalDegree ≤ n := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (h1 F K ι I hI).1 hrel p hp hp0
      rw [hn] at this
      exact_mod_cast this
  have key : ∀ (r : ℕ) (bs : Fin r → K → ℤ), n ≤ r → ∃ c : ℚ, (n < r → c = 0) ∧
      ∀ᶠ m in atTop, (mixedDiff bs (hilbFn I) m : ℚ) = c := by
    intro r bs hr
    have hE := eventuallyPoly_foldr (List.ofFn bs) hp
    rcases foldr_polyStep_deg (List.ofFn bs) p with h0 | hd
    · refine ⟨0, fun _ => rfl, ?_⟩
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, h0, map_zero]
    · rw [List.length_ofFn] at hd
      have hq0 : ((List.ofFn bs).foldr polyStep p).totalDegree = 0 := by omega
      refine ⟨coeff 0 ((List.ofFn bs).foldr polyStep p), fun hlt => by omega, ?_⟩
      rw [totalDegree_eq_zero_iff_eq_C] at hq0
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, hq0, eval_C, coeff_C, if_pos rfl]
  constructor
  · intro bs
    obtain ⟨c, -, hc⟩ := key n bs le_rfl
    obtain ⟨m0, hm0⟩ := hc.exists
    have hc' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = mixedDiff bs (hilbFn I) m0 :=
      hc.mono fun m hm => by exact_mod_cast hm.trans hm0.symm
    have hex : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = c := ⟨_, hc'⟩
    have hval : intNum F I bs = mixedDiff bs (hilbFn I) m0 := by
      unfold intNum eventualValue
      rw [dif_pos hex]
      obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and hc').exists
      rw [← hm1, hm2]
    filter_upwards [hc'] with m hm
    rw [hm, hval]
  · intro r hr bs
    obtain ⟨c, hc0, hc⟩ := key r bs hr.le
    filter_upwards [hc] with m hm
    rw [hc0 hr] at hm
    exact_mod_cast hm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
