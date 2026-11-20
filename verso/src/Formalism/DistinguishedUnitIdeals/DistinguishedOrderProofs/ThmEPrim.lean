import Mathlib
import Formalism.DistinguishedUnitIdeals.FrobeniusCoboundedArc
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEFull
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LemmaCFull
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LemmaC
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Descent

namespace Formalism.ExponentWindows.E.Prim

open PowerSeries

/- English proof (translation)
Unfold `parM`. Establish `hm : 0 < ℓ - 1` using `by omega`. Use `first`. Consider the case `exact Nat.lt_mul_div_succ _ hm`. Consider the case `(have h1 := Nat.div_add_mod (hh + 2 * g) (ℓ - 1)`.

Establish `h2` using `Nat.mod_lt (hh + 2 * g) hm`. Use the proof step `nlinarith)`.
-/
theorem lt_parM (ℓ hh g : ℕ) (hℓ : 2 ≤ ℓ) : hh + 2 * g < (ℓ - 1) * parM ℓ hh g := by
  unfold parM
  have hm : 0 < ℓ - 1 := by omega
  first
    | exact Nat.lt_mul_div_succ _ hm
    | (have h1 := Nat.div_add_mod (hh + 2 * g) (ℓ - 1)
       have h2 := Nat.mod_lt (hh + 2 * g) hm
       nlinarith)

section shape
variable {O : Type} [CommRing O]

def QQ (l : O) (x : PowerSeries O) (d : ℕ) : Prop :=
  ∃ v a : PowerSeries O, IsUnit v ∧ x = v * X ^ d + C l * a

/- English proof (translation)
Take `⟨v, a, hv, rfl⟩` from `hx`. Take `⟨w, b, hw, rfl⟩` from `hy`. Use `⟨v * w, v * X ^ d * b + a * (w * X ^ d') + C l * a * b, hv.mul hw, ?_⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem QQ.mul {l : O} {x y : PowerSeries O} {d d' : ℕ} (hx : QQ l x d) (hy : QQ l y d') :
    QQ l (x * y) (d + d') := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  obtain ⟨w, b, hw, rfl⟩ := hy
  refine ⟨v * w, v * X ^ d * b + a * (w * X ^ d') + C l * a * b, hv.mul hw, ?_⟩
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨1, 0, isUnit_one, by simp⟩`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Establish `h` using `ih.mul hx`.

Rewrite `h` using `[show d * m + d = d * (m + 1) by ring]`. Then use the resulting hypothesis.
-/
theorem QQ.pow {l : O} {x : PowerSeries O} {d : ℕ} (hx : QQ l x d) (m : ℕ) :
    QQ l (x ^ m) (d * m) := by
  induction m with
  | zero => exact ⟨1, 0, isUnit_one, by simp⟩
  | succ m ih =>
    rw [pow_succ]
    have h := ih.mul hx
    rwa [show d * m + d = d * (m + 1) by ring] at h

/- English proof (translation)
Take `⟨v, a, hv, rfl⟩` from `hx`. Conclude with `⟨u * v, u * a, hu.mul hv, by ring⟩`.
-/
theorem QQ.unit_mul {l : O} {x u : PowerSeries O} {d : ℕ} (hu : IsUnit u) (hx : QQ l x d) :
    QQ l (u * x) d := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  exact ⟨u * v, u * a, hu.mul hv, by ring⟩

/- English proof (translation)
Take `⟨v, a, hv, rfl⟩` from `hx`. Take `⟨w, b, hw, hwb⟩` from `QQ.unit_mul (hv.map f) (hf.pow d)`. Establish `hC : f (C l) = C l` using `by first`. Consider the case `exact f.commutes l`. Consider the case `simpa [PowerSeries.algebraMap_eq] using f.commutes l`.

Use `⟨w, b + f a, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_pow, hC, hwb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem QQ.map {l : O} (f : PowerSeries O →ₐ[O] PowerSeries O) {x : PowerSeries O} {e d : ℕ}
    (hf : QQ l (f X) e) (hx : QQ l x d) : QQ l (f x) (e * d) := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  obtain ⟨w, b, hw, hwb⟩ := QQ.unit_mul (hv.map f) (hf.pow d)
  have hC : f (C l) = C l := by
    first
      | exact f.commutes l
      | simpa [PowerSeries.algebraMap_eq] using f.commutes l
  refine ⟨w, b + f a, hw, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, hC, hwb]
  ring

/- English proof (translation)
Take `⟨u, hu⟩` from `h3`. Establish `hq : QQ (B.ℓ : O) B.q 1` using `⟨1, 1, isUnit_one, by simp [Base.q]⟩`. Establish `hX : QQ (B.ℓ : O) (X : PowerSeries O) 1` using `⟨1, 0, isUnit_one, by simp⟩`. Establish `h` using `QQ.unit_mul u.isUnit (hX.mul (hq.pow (B.ℓ - 1)))`. Establish `he : 1 + 1 * (B.ℓ - 1) = B.ℓ` using `by omega`.

Rewrite `h` using `[he]`. Rewrite using `[hu, mul_assoc]`. Conclude with `h`.
-/
theorem QQ_φX {B : Base O} (h3 : B.E3) (h1 : 1 ≤ B.ℓ) : QQ (B.ℓ : O) (B.φ X) B.ℓ := by
  obtain ⟨u, hu⟩ := h3
  have hq : QQ (B.ℓ : O) B.q 1 := ⟨1, 1, isUnit_one, by simp [Base.q]⟩
  have hX : QQ (B.ℓ : O) (X : PowerSeries O) 1 := ⟨1, 0, isUnit_one, by simp⟩
  have h := QQ.unit_mul u.isUnit (hX.mul (hq.pow (B.ℓ - 1)))
  have he : 1 + 1 * (B.ℓ - 1) = B.ℓ := by omega
  rw [he] at h
  rw [hu, mul_assoc]
  exact h

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => exact ⟨1, 0, isUnit_one, by simp⟩`. Consider the case `succ s ih`. Rewrite using `[Function.iterate_succ_apply']`. Establish `h` using `QQ.map B.φ (QQ_φX h3 h1) ih`.

Rewrite `h` using `[show B.ℓ * B.ℓ ^ s = B.ℓ ^ (s + 1) by ring]`. Then use the resulting hypothesis.
-/
theorem QQ_it {B : Base O} (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (s : ℕ) :
    QQ (B.ℓ : O) ((⇑B.φ)^[s] X) (B.ℓ ^ s) := by
  induction s with
  | zero => exact ⟨1, 0, isUnit_one, by simp⟩
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    have h := QQ.map B.φ (QQ_φX h3 h1) ih
    rwa [show B.ℓ * B.ℓ ^ s = B.ℓ ^ (s + 1) by ring] at h

/- English proof (translation)
Establish `hC : ∀ c : O, B.φ (C c) = C c` using `fun c => by first`. Consider the case `exact B.φ.commutes c`. Consider the case `simpa [PowerSeries.algebraMap_eq] using B.φ.commutes c`. Unfold `Base.p Base.q`. Proceed by induction on `s with`.

Consider the case `zero => simp`. Consider the case `succ s ih`. Rewrite using `[Function.iterate_succ_apply', ih, Function.iterate_succ_apply', map_add, hC]`.
-/
theorem p_eq (B : Base O) (s : ℕ) : B.p s = (⇑B.φ)^[s] X + C (B.ℓ : O) := by
  have hC : ∀ c : O, B.φ (C c) = C c := fun c => by
    first
      | exact B.φ.commutes c
      | simpa [PowerSeries.algebraMap_eq] using B.φ.commutes c
  unfold Base.p Base.q
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', map_add, hC]

/- English proof (translation)
Take `⟨v, a, hv, ha⟩` from `QQ_it h3 h1 s`. Conclude with `⟨v, a + 1, hv, by rw [p_eq, ha]; ring⟩`.
-/
theorem QQ_p {B : Base O} (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (s : ℕ) :
    QQ (B.ℓ : O) (B.p s) (B.ℓ ^ s) := by
  obtain ⟨v, a, hv, ha⟩ := QQ_it h3 h1 s
  exact ⟨v, a + 1, hv, by rw [p_eq, ha]; ring⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1 : ¬ IsUnit (l * c)` using `fun hu => hl (isUnit_of_mul_isUnit_left hu)`. Establish `h2 : ¬ IsUnit (-(l * c))` using `by rwa [IsUnit.neg_iff]`. Conclude with `IsLocalRing.nonunits_add h h2 (by simp)`.
-/
theorem isUnit_one_add [IsLocalRing O] {l : O} (hl : ¬ IsUnit l) (c : O) : IsUnit (1 + l * c) := by
  by_contra h
  have h1 : ¬ IsUnit (l * c) := fun hu => hl (isUnit_of_mul_isUnit_left hu)
  have h2 : ¬ IsUnit (-(l * c)) := by rwa [IsUnit.neg_iff]
  exact IsLocalRing.nonunits_add h h2 (by simp)

/- English proof (translation)
Take `⟨v, a, hv, rfl⟩` from `hx`. Take `⟨vi, hvi⟩` from `hv.exists_right_inv`. Establish `hI : Ideal.span {l} ≠ ⊤` using `Ideal.span_singleton_ne_top hl`. Establish `: Nontrivial (O ⧸ Ideal.span {l})` using `Ideal.Quotient.nontrivial_iff.2 hI`. Use `set g : PowerSeries O := X ^ d + C l * (vi * a) with hg`.

Establish `hl0 : Ideal.Quotient.mk (Ideal.span {l}) l = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self l)`. Establish `hmap : g.map (Ideal.Quotient.mk (Ideal.span {l})) = X ^ d`. Rewrite using `[hg, map_add, map_mul, map_pow, map_X, map_C, hl0, map_zero, zero_mul, add_zero]`. Establish `hord : (g.map (Ideal.Quotient.mk (Ideal.span {l}))).order.toNat = d`. Rewrite using `[hmap, order_X_pow]`.

Both sides reduce to the same expression. Establish `H : g.IsWeierstrassDivisorAt (Ideal.span {l})`. Unfold `IsWeierstrassDivisorAt`. Rewrite using `[hord, hg, map_add, coeff_X_pow_self, coeff_C_mul]`. Conclude with `isUnit_one_add hl _`.

Establish `hdv` using `H.isWeierstrassDivisionAt_div_mod (X ^ d)`. Use `set q := H.div (X ^ d)`. Use `set r := H.mod (X ^ d)`. Establish `h1 : r.degree < d`. Use `hdv.degree_lt` as an intermediate fact.

Rewrite `this` using `[hord]`. Then use the resulting hypothesis. Establish `h2 : (X : PowerSeries O) ^ d = g * q + r` using `hdv.eq_mul_add`. Establish `hm : (Polynomial.X ^ d - r).Monic` using `Polynomial.monic_X_pow_sub h1`. Establish `hnd : (Polynomial.X ^ d - r).natDegree = d`. Apply `Polynomial.natDegree_eq_of_degree_eq_some` to reduce the goal to its premises.

Rewrite using `[Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]), Polynomial.degree_X_pow]`. Establish `hE : ((Polynomial.X ^ d - r : Polynomial O) : PowerSeries O) = g * q`. Rewrite using `[Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : IsUnit q`.

Rewrite using `[isUnit_iff_constantCoeff]`. Establish `hcd : (Polynomial.X ^ d - r : Polynomial O).coeff d = 1`. Use `hm.coeff_natDegree` as an intermediate fact. Rewrite `this` using `[hnd]`. Then use the resulting hypothesis. Establish `h3` using `congrArg (coeff d) hE`.

Rewrite `h3` using `[Polynomial.coeff_coe, hcd, hg, add_mul, map_add, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, mul_assoc, coeff_C_mul, coeff_zero_eq_constantCoeff_apply]`. Establish `h4 : constantCoeff q = 1 + l * (-(coeff d (vi * a * q)))`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`.

Conclude with `isUnit_one_add hl _`. Take `⟨qi, hqi⟩` from `hq.exists_right_inv`. Use `⟨Polynomial.X ^ d - r, v * qi, hm, hnd, fun i hi => ?_, hv.mul (IsUnit.of_mul_eq_one q (by rw [mul_comm]; exact hqi)), ?_⟩` and prove the remaining obligations. Use `hdv.coeff_f_sub_r_mem (i := i) (by rwa [hord])` as an intermediate fact. Rewrite `this` using `[Ideal.mem_span_singleton]`.

Establish `e : coeff i ((X : PowerSeries O) ^ d - (r : PowerSeries O)) = (Polynomial.X ^ d - r : Polynomial O).coeff i`. Rewrite using `[← Polynomial.coeff_coe, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[hE, hg]`. Take the linear combination `(-(C l * a)) * hvi - (v * (X ^ d + C l * (vi * a))) * hqi`.
-/
theorem prep [IsLocalRing O] {l : O} (hl : ¬ IsUnit l) [IsAdicComplete (Ideal.span {l}) O]
    {x : PowerSeries O} {d : ℕ} (hx : QQ l x d) :
    ∃ (E : Polynomial O) (u : PowerSeries O), E.Monic ∧ E.natDegree = d ∧
      (∀ i < d, l ∣ E.coeff i) ∧ IsUnit u ∧ x = u * (E : PowerSeries O) := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  obtain ⟨vi, hvi⟩ := hv.exists_right_inv
  have hI : Ideal.span {l} ≠ ⊤ := Ideal.span_singleton_ne_top hl
  have : Nontrivial (O ⧸ Ideal.span {l}) := Ideal.Quotient.nontrivial_iff.2 hI
  set g : PowerSeries O := X ^ d + C l * (vi * a) with hg
  have hl0 : Ideal.Quotient.mk (Ideal.span {l}) l = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self l)
  have hmap : g.map (Ideal.Quotient.mk (Ideal.span {l})) = X ^ d := by
    rw [hg, map_add, map_mul, map_pow, map_X, map_C, hl0, map_zero, zero_mul, add_zero]
  have hord : (g.map (Ideal.Quotient.mk (Ideal.span {l}))).order.toNat = d := by
    rw [hmap, order_X_pow]
    rfl
  have H : g.IsWeierstrassDivisorAt (Ideal.span {l}) := by
    unfold IsWeierstrassDivisorAt
    rw [hord, hg, map_add, coeff_X_pow_self, coeff_C_mul]
    exact isUnit_one_add hl _
  have hdv := H.isWeierstrassDivisionAt_div_mod (X ^ d)
  set q := H.div (X ^ d)
  set r := H.mod (X ^ d)
  have h1 : r.degree < d := by
    have := hdv.degree_lt
    rwa [hord] at this
  have h2 : (X : PowerSeries O) ^ d = g * q + r := hdv.eq_mul_add
  have hm : (Polynomial.X ^ d - r).Monic := Polynomial.monic_X_pow_sub h1
  have hnd : (Polynomial.X ^ d - r).natDegree = d := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  have hE : ((Polynomial.X ^ d - r : Polynomial O) : PowerSeries O) = g * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, h2]
    ring
  have hq : IsUnit q := by
    rw [isUnit_iff_constantCoeff]
    have hcd : (Polynomial.X ^ d - r : Polynomial O).coeff d = 1 := by
      have := hm.coeff_natDegree
      rwa [hnd] at this
    have h3 := congrArg (coeff d) hE
    rw [Polynomial.coeff_coe, hcd, hg, add_mul, map_add,
      coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, mul_assoc, coeff_C_mul,
      coeff_zero_eq_constantCoeff_apply] at h3
    have h4 : constantCoeff q = 1 + l * (-(coeff d (vi * a * q))) := by
      rw [h3]; ring
    rw [h4]
    exact isUnit_one_add hl _
  obtain ⟨qi, hqi⟩ := hq.exists_right_inv
  refine ⟨Polynomial.X ^ d - r, v * qi, hm, hnd, fun i hi => ?_,
    hv.mul (IsUnit.of_mul_eq_one q (by rw [mul_comm]; exact hqi)), ?_⟩
  · have := hdv.coeff_f_sub_r_mem (i := i) (by rwa [hord])
    rw [Ideal.mem_span_singleton] at this
    have e : coeff i ((X : PowerSeries O) ^ d - (r : PowerSeries O)) =
        (Polynomial.X ^ d - r : Polynomial O).coeff i := by
      rw [← Polynomial.coeff_coe, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X]
    rwa [e] at this
  · rw [hE, hg]
    linear_combination (-(C l * a)) * hvi - (v * (X ^ d + C l * (vi * a))) * hqi

end shape

section dvr
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Introduce `s _`. Take `⟨E, u, hm, hd, hc, hu, hp⟩` from `prep hl (QQ_p h3 h1 s)`. Use `⟨E, u, hm, hd, hc, ?_, hu, hp⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `iterated_third_estimate_holds O B h3 s`. Establish `h0 : constantCoeff (B.p s) = (B.ℓ : O)`.

Rewrite using `[p_eq, hw]`. Simplify using the standard rewrite rules. Rewrite `h0` using `[hp, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O), Polynomial.coeff_coe]`. Establish `hu0 : IsUnit (constantCoeff u)` using `isUnit_iff_constantCoeff.1 hu`. Conclude with `⟨hu0.unit, by rw [IsUnit.unit_spec, mul_comm]; exact h0⟩`.
-/
theorem pshape {B : Base O} (hl : ¬ IsUnit (B.ℓ : O)) [IsAdicComplete (Ideal.span {(B.ℓ : O)}) O]
    (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (ell : ℕ) : B.PShape ell := by
  intro s _
  obtain ⟨E, u, hm, hd, hc, hu, hp⟩ := prep hl (QQ_p h3 h1 s)
  refine ⟨E, u, hm, hd, hc, ?_, hu, hp⟩
  obtain ⟨w, hw⟩ := iterated_third_estimate_holds O B h3 s
  have h0 : constantCoeff (B.p s) = (B.ℓ : O) := by
    rw [p_eq, hw]
    simp
  rw [hp, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O),
    Polynomial.coeff_coe] at h0
  have hu0 : IsUnit (constantCoeff u) := isUnit_iff_constantCoeff.1 hu
  exact ⟨hu0.unit, by rw [IsUnit.unit_spec, mul_comm]; exact h0⟩

noncomputable def itAlg (f : PowerSeries O →ₐ[O] PowerSeries O) :
    ℕ → (PowerSeries O →ₐ[O] PowerSeries O)
  | 0 => AlgHom.id O _
  | k + 1 => f.comp (itAlg f k)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', ← ih]`. Both sides reduce to the same expression.
-/
theorem itAlg_apply (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) (a : PowerSeries O) :
    itAlg f k a = (⇑f)^[k] a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

/- English proof (translation)
Take `⟨E, u, hm, hdeg, hc, hu, hPe'⟩` from `prep hl (QQ_it h3 h1 k)`. Use `set d := B.ℓ ^ k with hd`. Establish `hd1 : 1 ≤ d` using `Nat.one_le_pow _ _ h1`. Use `set φ := itAlg B.φ k with hφ`. Establish `hPe : φ X = u * (E : PowerSeries O)` using `by rw [hφ, itAlg_apply]; exact hPe'`.

Establish `hI : Ideal.span {(B.ℓ : O)} ≠ ⊤` using `Ideal.span_singleton_ne_top hl`. Establish `hE : E.IsDistinguishedAt (Ideal.span {(B.ℓ : O)})` using `⟨⟨fun {i} hi => Ideal.mem_span_singleton.2 (hc i (hdeg ▸ hi))⟩, hm⟩`. Establish `hPnu : ¬ IsUnit (φ X)`. Introduce `hunit`. Establish `h1` using `isUnit_constantCoeff _ hunit`.

Establish `hmem0 : constantCoeff (φ X) ∈ Ideal.span {(B.ℓ : O)}`. Rewrite using `[hPe, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O), Polynomial.coeff_coe]`. Conclude with `Ideal.mul_mem_left _ _ (hE.mem (by omega))`. Conclude with `hI (Ideal.eq_top_of_isUnit_mem _ hmem0 h1)`. Establish `hP0 : φ X ≠ 0`.

Introduce `h0`. Rewrite `h0` using `[hPe]`. Establish `hE0 : (E : PowerSeries O) = 0` using `(hu.mul_right_eq_zero).mp h0`. Rewrite `hE0` using `[Polynomial.coe_eq_zero_iff]`. Conclude with `hE.monic.ne_zero hE0`.

Establish `hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < d ∧ F = φ X * q + r`. Introduce `F`. Take `⟨q, r, hr, hF⟩` from `exists_div_of_isDistinguishedAt hI hE F`. Use `⟨↑hu.unit⁻¹ * q, r, by rwa [hdeg] at hr, ?_⟩` and prove the remaining obligations. Establish `hinv : u * ↑hu.unit⁻¹ = 1` using `hu.mul_val_inv`.

Rewrite using `[hPe]`. Take the linear combination `hF - ((E : PowerSeries O) * q) * hinv`. Establish `huniq : ∀ (a : Fin d → O) (q : PowerSeries O), ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0`. Introduce `a q hq j`. Establish `hr : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).degree < E.natDegree` using `by rw [hdeg]; exact Polynomial.degree_sum_fin_lt a`.

Establish `h0` using `eq_zero_of_isDistinguishedAt_mul hI hE (q := u * q) hr (by`. Rewrite using `[coe_sum_fin, hq, hPe]`. Use the proof step `ring)`. Use `coeff_sum_fin a j` as an intermediate fact. Rewrite `this` using `[h0, Polynomial.coeff_zero]`.

Conclude with `this.symm`. Establish `hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0` using `fun x hx => eq_zero_of_forall_pow_dvd hPnu hx`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Take `⟨α, hα⟩` from `exists_sum_algHom_mul_X_pow φ d hdiv hkrull a`.

Use `⟨α, hα.trans (Finset.sum_congr rfl fun t _ => ?_)⟩` and prove the remaining obligations. Rewrite using `[hφ, itAlg_apply, mul_comm]`. Introduce `a' h t`. Establish `h' : ∑ i, φ (a' i) * X ^ (i : ℕ) = 0`. Rewrite using `[← h]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hφ, itAlg_apply, mul_comm]`. Use extensionality with `m`. Rewrite using `[map_zero]`. Conclude with `eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0 m a' h' t`.
-/
theorem basePhiFree {B : Base O} (hl : ¬ IsUnit (B.ℓ : O))
    [IsAdicComplete (Ideal.span {(B.ℓ : O)}) O] (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (k : ℕ) :
    (∀ a : PowerSeries O, ∃ a' : Fin (B.ℓ ^ k) → PowerSeries O,
      a = ∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t)) ∧
    ∀ a' : Fin (B.ℓ ^ k) → PowerSeries O,
      ∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t) = 0 →
      ∀ t, a' t = 0 := by
  obtain ⟨E, u, hm, hdeg, hc, hu, hPe'⟩ := prep hl (QQ_it h3 h1 k)
  set d := B.ℓ ^ k with hd
  have hd1 : 1 ≤ d := Nat.one_le_pow _ _ h1
  set φ := itAlg B.φ k with hφ
  have hPe : φ X = u * (E : PowerSeries O) := by rw [hφ, itAlg_apply]; exact hPe'
  have hI : Ideal.span {(B.ℓ : O)} ≠ ⊤ := Ideal.span_singleton_ne_top hl
  have hE : E.IsDistinguishedAt (Ideal.span {(B.ℓ : O)}) :=
    ⟨⟨fun {i} hi => Ideal.mem_span_singleton.2 (hc i (hdeg ▸ hi))⟩, hm⟩
  have hPnu : ¬ IsUnit (φ X) := by
    intro hunit
    have h1 := isUnit_constantCoeff _ hunit
    have hmem0 : constantCoeff (φ X) ∈ Ideal.span {(B.ℓ : O)} := by
      rw [hPe, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O),
        Polynomial.coeff_coe]
      exact Ideal.mul_mem_left _ _ (hE.mem (by omega))
    exact hI (Ideal.eq_top_of_isUnit_mem _ hmem0 h1)
  have hP0 : φ X ≠ 0 := by
    intro h0
    rw [hPe] at h0
    have hE0 : (E : PowerSeries O) = 0 := (hu.mul_right_eq_zero).mp h0
    rw [Polynomial.coe_eq_zero_iff] at hE0
    exact hE.monic.ne_zero hE0
  have hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r := by
    intro F
    obtain ⟨q, r, hr, hF⟩ := exists_div_of_isDistinguishedAt hI hE F
    refine ⟨↑hu.unit⁻¹ * q, r, by rwa [hdeg] at hr, ?_⟩
    have hinv : u * ↑hu.unit⁻¹ = 1 := hu.mul_val_inv
    rw [hPe]
    linear_combination hF - ((E : PowerSeries O) * q) * hinv
  have huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0 := by
    intro a q hq j
    have hr : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).degree
        < E.natDegree := by rw [hdeg]; exact Polynomial.degree_sum_fin_lt a
    have h0 := eq_zero_of_isDistinguishedAt_mul hI hE (q := u * q) hr (by
      rw [coe_sum_fin, hq, hPe]
      ring)
    have := coeff_sum_fin a j
    rw [h0, Polynomial.coeff_zero] at this
    exact this.symm
  have hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0 :=
    fun x hx => eq_zero_of_forall_pow_dvd hPnu hx
  constructor
  · intro a
    obtain ⟨α, hα⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull a
    refine ⟨α, hα.trans (Finset.sum_congr rfl fun t _ => ?_)⟩
    rw [hφ, itAlg_apply, mul_comm]
  · intro a' h t
    have h' : ∑ i, φ (a' i) * X ^ (i : ℕ) = 0 := by
      rw [← h]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hφ, itAlg_apply, mul_comm]
    ext m
    rw [map_zero]
    exact eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0 m a' h' t

end dvr

section ring
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Conclude with `(dvd_pow_self ϖ (by omega)).trans h.symm.dvd`.
-/
theorem dvd_ell {ϖ : O} {ℓ e : ℕ} (he : 1 ≤ e) (h : Associated (ℓ : O) (ϖ ^ e)) : ϖ ∣ (ℓ : O) := by
  exact (dvd_pow_self ϖ (by omega)).trans h.symm.dvd

/- English proof (translation)
Conclude with `h.ne_zero_iff.mpr (pow_ne_zero _ hϖ.ne_zero)`.
-/
theorem ell_ne {ϖ : O} (hϖ : Irreducible ϖ) {ℓ e : ℕ} (h : Associated (ℓ : O) (ϖ ^ e)) :
    (ℓ : O) ≠ 0 := by
  exact h.ne_zero_iff.mpr (pow_ne_zero _ hϖ.ne_zero)

/- English proof (translation)
Conclude with `fun hu => hϖ.not_isUnit (isUnit_of_dvd_unit (dvd_ell he h) hu)`.
-/
theorem ell_nonunit {ϖ : O} (hϖ : Irreducible ϖ) {ℓ e : ℕ} (he : 1 ≤ e)
    (h : Associated (ℓ : O) (ϖ ^ e)) : ¬ IsUnit (ℓ : O) := by
  exact fun hu => hϖ.not_isUnit (isUnit_of_dvd_unit (dvd_ell he h) hu)

/- English proof (translation)
Use `haveI := hB.complete`. Conclude with `pshape (ell_nonunit hϖ hB.one_le_e hB.assoc) hB.e3 (by have := hB.three_le; omega) ell`.
-/
theorem pshape' {B : Base O} {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e) (ell : ℕ) :
    B.PShape ell := by
  haveI := hB.complete
  exact pshape (ell_nonunit hϖ hB.one_le_e hB.assoc) hB.e3 (by have := hB.three_le; omega) ell

/- English proof (translation)
Take `⟨E, u, hm, hdeg, hdvd, -, hu, hp⟩` from `hP s hs`. Use `⟨u, E, hu, { mem := fun {n} hn => ?_, monic := hm }, hdeg, hp⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `hd.trans (hdvd n (hdeg ▸ hn))`.
-/
theorem unitDist {B : Base O} {ϖ : O} (hd : ϖ ∣ (B.ℓ : O)) {ell : ℕ} (hP : B.PShape ell) (s : ℕ)
    (hs : s < ell) : UnitDist ϖ (B.ℓ ^ s) (B.p s) := by
  obtain ⟨E, u, hm, hdeg, hdvd, -, hu, hp⟩ := hP s hs
  refine ⟨u, E, hu, { mem := fun {n} hn => ?_, monic := hm }, hdeg, hp⟩
  rw [Ideal.mem_span_singleton]
  exact hd.trans (hdvd n (hdeg ▸ hn))

/- English proof (translation)
Take `⟨u, hu⟩` from `h3`. Establish `hit : ∀ k, (⇑B.φ)^[k + 1] X = (⇑B.φ)^[k] (u : PowerSeries O) * (⇑B.φ)^[k] X * (⇑B.φ)^[k] B.q ^ (B.ℓ - 1)`. Introduce `k`. Rewrite using `[Function.iterate_succ_apply, hu, ← itAlg_apply, map_mul, map_mul, map_pow, itAlg_apply, itAlg_apply, itAlg_apply]`. Establish `hdiv : ∀ t, s + 1 ≤ t → B.p s ∣ (⇑B.φ)^[t] X`.

Introduce `t ht`. Proceed by induction on `t, ht using Nat.le_induction with`. Consider the case `base`. Rewrite using `[hit s]`. Conclude with `Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _`.

Consider the case `succ t _ ih`. Rewrite using `[hit t]`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_left ih _) _`. Take `⟨d, hd⟩` from `hdiv s' hs`. Use `⟨d, ?_⟩` and prove the remaining obligations.

Rewrite using `[p_eq B s', hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem p_sub_mem {B : Base O} (h3 : B.E3) (hℓ : 2 ≤ B.ℓ) {s s' : ℕ} (hs : s < s') :
    ∃ d : PowerSeries O, B.p s' = d * B.p s + C (B.ℓ : O) := by
  obtain ⟨u, hu⟩ := h3
  have hit : ∀ k, (⇑B.φ)^[k + 1] X =
      (⇑B.φ)^[k] (u : PowerSeries O) * (⇑B.φ)^[k] X * (⇑B.φ)^[k] B.q ^ (B.ℓ - 1) := by
    intro k
    rw [Function.iterate_succ_apply, hu, ← itAlg_apply, map_mul, map_mul, map_pow, itAlg_apply,
      itAlg_apply, itAlg_apply]
  have hdiv : ∀ t, s + 1 ≤ t → B.p s ∣ (⇑B.φ)^[t] X := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      rw [hit s]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    | succ t _ ih =>
      rw [hit t]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ih _) _
  obtain ⟨d, hd⟩ := hdiv s' hs
  refine ⟨d, ?_⟩
  rw [p_eq B s', hd]
  ring

/- English proof (translation)
Take `⟨d, hd⟩` from `p_sub_mem h3 hℓ hs`. Take `⟨u, hu⟩` from `ha`. Use `⟨-(C (u : O) * d), C (u : O), ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, map_mul, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coprimeRat_lt {B : Base O} {ϖ : O} {e : ℕ} (ha : Associated (B.ℓ : O) (ϖ ^ e)) (h3 : B.E3)
    (hℓ : 2 ≤ B.ℓ) {s s' : ℕ} (hs : s < s') :
    ∃ a a' : PowerSeries O, a * B.p s + a' * B.p s' = C (ϖ ^ e) := by
  obtain ⟨d, hd⟩ := p_sub_mem h3 hℓ hs
  obtain ⟨u, hu⟩ := ha
  refine ⟨-(C (u : O) * d), C (u : O), ?_⟩
  rw [← hu, map_mul, hd]
  ring

/- English proof (translation)
Use `⟨fun s hs => unitDist (dvd_ell he ha) hP s hs, fun s _ s' _ hne => ?_⟩` and prove the remaining obligations. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Take `⟨a, a', h'⟩` from `coprimeRat_lt ha h3 hℓ h`. Conclude with `⟨e, a, a', h'⟩`. Take `⟨a, a', h'⟩` from `coprimeRat_lt ha h3 hℓ h`.

Conclude with `⟨e, a', a, by rw [add_comm]; exact h'⟩`.
-/
theorem constant_model_setting {B : Base O} {ϖ : O} {e : ℕ} (he : 1 ≤ e) (ha : Associated (B.ℓ : O) (ϖ ^ e))
    (h3 : B.E3) (hℓ : 2 ≤ B.ℓ) {ell : ℕ} (hP : B.PShape ell) : DistinguishedFamily ϖ B.ℓ ell B.p := by
  refine ⟨fun s hs => unitDist (dvd_ell he ha) hP s hs, fun s _ s' _ hne => ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨a, a', h'⟩ := coprimeRat_lt ha h3 hℓ h
    exact ⟨e, a, a', h'⟩
  · obtain ⟨a, a', h'⟩ := coprimeRat_lt ha h3 hℓ h
    exact ⟨e, a', a, by rw [add_comm]; exact h'⟩

/- English proof (translation)
Establish `hM` using `lt_parM B.ℓ hh g (by have := hB.three_le; omega)`. Conclude with `base_ring_good_holds O B j _ g hB.e3 hB.e4 (le_of_lt (lt_of_le_of_lt (by omega) hM))`.
-/
theorem baseGood {B : Base O} {ϖ : O} {e : ℕ} (hB : PrimBase B ϖ e) {g hh : ℕ}
    (hg : g ≤ hh) (j : ℕ) : B.Good j (parM B.ℓ hh g) g := by
  have hM := lt_parM B.ℓ hh g (by have := hB.three_le; omega)
  exact base_ring_good_holds O B j _ g hB.e3 hB.e4 (le_of_lt (lt_of_le_of_lt (by omega) hM))

end ring

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  [NeZero n]

/- English proof (translation)
Establish `hd` using `dvd_ell hB.one_le_e hB.assoc`. Take `⟨u₁, hu₁⟩` from `one_add_unit_pow_formula O ϖ B hϖ hd hB.prime hB.three_le hB.e4`. Establish `hM` using `lt_parM B.ℓ hh g (by have := hB.three_le; omega)`. Set `Mi : ZMod n → ℕ` to `fun i => if ∃ c ∈ Cu.cuts, ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i = c + (k : ZMod n) then G else hh`. Use `good_lattice_holds O ϖ B u₁ n Cu j (parM B.ℓ hh g) g G sig Mi V L hϖ hd (ell_ne hϖ hB.assoc) hB.prime hB.three_le hN.one_le_j hB.e3 hu₁ hN.G_le_g hN.sigOK hL.p9 (fun i => ?_) (fun i => ?_) (fun c hc k hk1 hk2 => ?_) hL.pullFree (completion_holds O B n V L hB.complete hL.free) (X_ …` and prove the remaining obligations.

Distinguish the cases in `h : ∃ c ∈ Cu.cuts, ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i = c + (k : ZMod n)`. Simplify using `only [Mi]`. Rewrite using `[if_pos h]`. Take `⟨c, hc, k, hk1, hk2, rfl⟩` from `h`. Conclude with `hL.frobeniusBounded_after c hc k hk1 hk2`.

Simplify using `only [Mi]`. Rewrite using `[if_neg h]`. Conclude with `hL.p5M i`. Establish `hGh : G ≤ hh` using `le_trans hN.G_le_g hN.g_le_h`. Establish `hle : Mi i ≤ hh`.

Simplify using `only [Mi]`. Apply the tactic sequence `split_ifs <;> omega`. Conclude with `lt_of_le_of_lt hle (lt_of_le_of_lt (by omega) hM)`. Establish `h : ∃ c' ∈ Cu.cuts, ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ j ∧ c + (k : ZMod n) = c' + (k' : ZMod n)` using `⟨c, hc, k, hk1, hk2, rfl⟩`. Simplify using `only [Mi]`.

Rewrite using `[if_pos h]`.
-/
theorem latGood {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {Cu : Cuts n} {j g G hh sig ellmax : ℕ} (hN : PrimNum B.ℓ Cu j g G hh sig ellmax)
    {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] {L : Lat B n V}
    (hL : PrimLat L Cu j G hh) : L.Good Cu j (parM B.ℓ hh g) g sig := by
  classical
  have hd := dvd_ell hB.one_le_e hB.assoc
  obtain ⟨u₁, hu₁⟩ := one_add_unit_pow_formula O ϖ B hϖ hd hB.prime hB.three_le hB.e4
  have hM := lt_parM B.ℓ hh g (by have := hB.three_le; omega)
  let Mi : ZMod n → ℕ := fun i =>
    if ∃ c ∈ Cu.cuts, ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i = c + (k : ZMod n) then G else hh
  refine good_lattice_holds O ϖ B u₁ n Cu j (parM B.ℓ hh g) g G sig Mi V L hϖ hd
    (ell_ne hϖ hB.assoc) hB.prime hB.three_le hN.one_le_j hB.e3 hu₁ hN.G_le_g hN.sigOK hL.p9
    (fun i => ?_) (fun i => ?_) (fun c hc k hk1 hk2 => ?_) hL.pullFree
    (completion_holds O B n V L hB.complete hL.free) (X_regular_on_lattice O B n V L hL.free) hL.ltors
  · by_cases h : ∃ c ∈ Cu.cuts, ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i = c + (k : ZMod n)
    · simp only [Mi]
      rw [if_pos h]
      obtain ⟨c, hc, k, hk1, hk2, rfl⟩ := h
      exact hL.frobeniusBounded_after c hc k hk1 hk2
    · simp only [Mi]
      rw [if_neg h]
      exact hL.p5M i
  · have hGh : G ≤ hh := le_trans hN.G_le_g hN.g_le_h
    have hle : Mi i ≤ hh := by
      simp only [Mi]
      split_ifs <;> omega
    exact lt_of_le_of_lt hle (lt_of_le_of_lt (by omega) hM)
  · have h : ∃ c' ∈ Cu.cuts, ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ j ∧ c + (k : ZMod n) = c' + (k' : ZMod n) :=
      ⟨c, hc, k, hk1, hk2, rfl⟩
    simp only [Mi]
    rw [if_pos h]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => first`. Consider the case `rw [Lat.phiIt, ih, L₀.φ_semi, h, Function.iterate_succ_apply']`. Consider the case `(simp only [Lat.phiIt]`.

Rewrite using `[ih, L₀.φ_semi, h, Function.iterate_succ_apply'])`.
-/
theorem unit_phiIt {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀] {L₀ : Lat B n V₀}
    {e₀ : V₀} (h : ∀ i, L₀.φ i e₀ = e₀) (i : ZMod n) (k : ℕ) (a : PowerSeries O) :
    L₀.phiIt i k (a • e₀) = (⇑B.φ)^[k] a • e₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    first
      | rw [Lat.phiIt, ih, L₀.φ_semi, h, Function.iterate_succ_apply']
      | (simp only [Lat.phiIt]
         rw [ih, L₀.φ_semi, h, Function.iterate_succ_apply'])

/- English proof (translation)
Use `haveI := hB.complete`. Establish `hl` using `ell_nonunit hϖ hB.one_le_e hB.assoc`. Establish `h1 : 1 ≤ B.ℓ` using `by have := hB.three_le; omega`. Take `⟨hspan, hfree⟩` from `basePhiFree hl hB.e3 h1 k`. Use `⟨B.ℓ ^ k, fun t => X ^ (t : ℕ), hspan, ?_⟩` and prove the remaining obligations.

Introduce `m hm hsum t`. Establish `hm' : ∀ t, ∃ a : PowerSeries O, a • e₀ = m t` using `fun t => by`. Use `hm t` as an intermediate fact. Rewrite `this` using `[hU.N_eq i, Submodule.mem_span_singleton]`. Then use the resulting hypothesis. Use `choose a' ha' using hm'`.

Establish `hz : (∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t)) • e₀ = 0`. Rewrite using `[Finset.sum_smul, ← hsum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← ha' t, unit_phiIt hU.φ_fix, mul_smul]`. Use `hfree a' (hU.tors _ hz) t` as an intermediate fact.

Rewrite using `[← ha' t, this, zero_smul]`.
-/
theorem unit_phiFree {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀] {L₀ : Lat B n V₀} {e₀ : V₀}
    (hU : PrimUnit L₀ e₀) (i : ZMod n) (k : ℕ) : L₀.PhiFree i k := by
  haveI := hB.complete
  have hl := ell_nonunit hϖ hB.one_le_e hB.assoc
  have h1 : 1 ≤ B.ℓ := by have := hB.three_le; omega
  obtain ⟨hspan, hfree⟩ := basePhiFree hl hB.e3 h1 k
  refine ⟨B.ℓ ^ k, fun t => X ^ (t : ℕ), hspan, ?_⟩
  intro m hm hsum t
  have hm' : ∀ t, ∃ a : PowerSeries O, a • e₀ = m t := fun t => by
    have := hm t
    rwa [hU.N_eq i, Submodule.mem_span_singleton] at this
  choose a' ha' using hm'
  have hz : (∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t)) • e₀ = 0 := by
    rw [Finset.sum_smul, ← hsum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← ha' t, unit_phiIt hU.φ_fix, mul_smul]
  have := hfree a' (hU.tors _ hz) t
  rw [← ha' t, this, zero_smul]

/- English proof (translation)
Introduce `i v hv hXv`. Rewrite `hv` using `[hU.N_eq i, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hv`. Rewrite `hXv` using `[smul_smul]`. Break down `mul_eq_zero.mp (hU.tors _ hXv) with h | h` into its components or cases.

Conclude with `absurd h PowerSeries.X_ne_zero`. Rewrite using `[h, zero_smul]`.
-/
theorem unit_xReg {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀] {L₀ : Lat B n V₀}
    {e₀ : V₀} (hU : PrimUnit L₀ e₀) : L₀.XReg := by
  intro i v hv hXv
  rw [hU.N_eq i, Submodule.mem_span_singleton] at hv
  obtain ⟨a, rfl⟩ := hv
  rw [smul_smul] at hXv
  rcases mul_eq_zero.mp (hU.tors _ hXv) with h | h
  · exact absurd h PowerSeries.X_ne_zero
  · rw [h, zero_smul]

/- English proof (translation)
Establish `hsat` using `saturation_first_form_holds O ϖ B j M g hϖ (dvd_ell hB.one_le_e hB.assoc) (ell_ne hϖ hB.assoc) hB.e3`. Conclude with `⟨hY.lift, hY.p9, extension_complete_holds O B n V₂ V₀ L₂ L₀ Y hY.p6 (unit_xReg hU), fun c hc => lattice_induction_lemma_holds O B n j M g G Y.VY Y.LY c (by omega) (hY.frobeniusBounded_after c hc), fun c hc => saturation_holds_alt O B n j _ Y.VY Y.LY c hsat (hY.pullFree c hc), fun …`.
-/
theorem extGood {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {Cu : Cuts n} {j g G rr : ℕ} (hG : G ≤ g) (M : ℕ) {H : ZMod n → ℕ → ℕ}
    {V₂ V₀ : Type} [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] {L₂ : Lat B n V₂} {L₀ : Lat B n V₀} {e₀ : V₀}
    (hU : PrimUnit L₀ e₀) {Y : Ext L₂ L₀} (hY : PrimExt Y e₀ Cu j G rr H) :
    Y.Good e₀ Cu (LamOf B Cu H) j M g rr := by
  have hsat := saturation_first_form_holds O ϖ B j M g hϖ (dvd_ell hB.one_le_e hB.assoc) (ell_ne hϖ hB.assoc)
    hB.e3
  exact ⟨hY.lift, hY.p9, extension_complete_holds O B n V₂ V₀ L₂ L₀ Y hY.p6 (unit_xReg hU),
    fun c hc => lattice_induction_lemma_holds O B n j M g G Y.VY Y.LY c (by omega) (hY.frobeniusBounded_after c hc),
    fun c hc => saturation_holds_alt O B n j _ Y.VY Y.LY c hsat (hY.pullFree c hc),
    fun c hc => pullback_lemma_holds O B n Y.VY Y.LY c (Cu.ell c) (H c) (H c) (hY.frobeniusCobounded_arc c hc)
      (fun _ _ => le_rfl),
    fun c _ => extension_generated_holds O B n V₂ V₀ L₂ L₀ Y _ _ _ hY.p6 (unit_phiFree hϖ hB hU _ _)⟩

end lat

section arc
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

/- English proof (translation)
Take `⟨r₁, r₂, S₁, S₂, m, b, kind, U₁, U₂, PP, PP', hP⟩` from `hA`. Establish `hℓ : 2 ≤ B.ℓ` using `by have := hB.three_le; omega`. Establish `hsh : B.PShape ell` using `pshape' hϖ hB ell`. Establish `hMS : LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂` using `⟨hℓ, constant_model_setting hB.one_le_e hB.assoc hB.e3 hℓ hsh, hP.sat₁, hP.sat₂, hP.b_le_H⟩`. Use `⟨r₁, r₂, S₁, S₂, m, H, b, kind, U₁, U₂, PP, PP', rfl, hP.p4c₁, hP.p4c₂, hP.equiv₁, hP.equiv₂, hP.k2iii, hP.rd₁, hP.rd₂, hP.k3a2, hP.k3a4, hP.dcFix, hP.partner₁, hP.partner₂, hP.p3₁, hP.p3₂, hP.p4a₁, hP.p4a₂, hP.p4b₁, hP.p4b₂, hP.bridge₁, hP.bridge₂, hP.mapFl, hP.p4d, hP.ppval, hM …` and prove the remaining obligations.

Break down `hP.word with hW | hW | hW | hW | hW` into its components or cases. Conclude with `Or.inl hW`. Conclude with `Or.inr (Or.inl hW)`. Conclude with `Or.inr (Or.inr (Or.inl hW))`. Take `⟨s₀, s₁, h0, h1, h2, h3, h4⟩` from `hW`.

Conclude with `Or.inr (Or.inr (Or.inr (Or.inl ⟨s₀, s₁, h0, h1, h2, h3, h4, (word_constants_holds O ϖ hϖ B.ℓ ell B.p b hℓ hMS.2.1 s₀ s₁ h0 h1).1⟩)))`. Take `⟨s₀, s₁, h0, h1, h2, h3, h4, h5, h6⟩` from `hW`. Establish `hb : 1 ≤ b s₀`. Use `hP.g_lt_b s₀ (by omega) (by rw [h3]; decide)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hle : 2 * sig + rr + 2 * g * ell ≤ parA sig rr g ellmax`. Use `Nat.mul_le_mul_left (2 * g) hell` as an intermediate fact. Unfold `parA`. Use linear arithmetic over natural numbers and integers. Establish `hC : CLift B.ℓ (parA sig rr g ellmax) (U₁ s₁) (U₂ s₁) m.prL` using `lemma_C_full_holds lemma_C_valuation_real O ϖ hϖ B e hB.one_le_e hB.assoc n V₁ V₂ L₁ L₂ h c ell _ r₁ r₂ S₁ S₂ m H b kind U₁ U₂ g sig rr _ rfl hsh hMS hP.rd₁ hP.rd₂ hP.partner₁ hP.partner₂ hP.p3₁ hP.p3₂ hP.p4a₁ hP.p4a₂ hP.bridge₁ hP.bridge₂ hP.flReg hP.mapFl hP.p4d s₀ s₁ h0 h1 h2 …`.

Conclude with `Or.inr (Or.inr (Or.inr (Or.inr ⟨s₀, s₁, h0, h1, h2, h3, h4, hC, (word_constants_holds O ϖ hϖ B.ℓ ell B.p b hℓ hMS.2.1 s₀ s₁ h0 h1).2 hb⟩)))`.
-/
theorem arcHyp {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {h : LatHom L₁ L₂} {c : ZMod n} {ell ellmax : ℕ} (hell : ell ≤ ellmax) {H : ℕ → ℕ}
    {g sig rr kap : ℕ}
    (hA : PrimArc h c ell H g sig rr (parA sig rr g ellmax) kap ϖ) :
    ArcHyp h c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) g sig rr (parA sig rr g ellmax) kap ϖ := by
  obtain ⟨r₁, r₂, S₁, S₂, m, b, kind, U₁, U₂, PP, PP', hP⟩ := hA
  have hℓ : 2 ≤ B.ℓ := by have := hB.three_le; omega
  have hsh : B.PShape ell := pshape' hϖ hB ell
  have hMS : LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂ :=
    ⟨hℓ, constant_model_setting hB.one_le_e hB.assoc hB.e3 hℓ hsh, hP.sat₁, hP.sat₂, hP.b_le_H⟩
  refine ⟨r₁, r₂, S₁, S₂, m, H, b, kind, U₁, U₂, PP, PP', rfl, hP.p4c₁, hP.p4c₂, hP.equiv₁,
    hP.equiv₂, hP.k2iii, hP.rd₁, hP.rd₂, hP.k3a2, hP.k3a4, hP.dcFix, hP.partner₁, hP.partner₂,
    hP.p3₁, hP.p3₂, hP.p4a₁, hP.p4a₂, hP.p4b₁, hP.p4b₂, hP.bridge₁, hP.bridge₂, hP.mapFl, hP.p4d,
    hP.ppval, hMS, hP.lLift, ?_⟩
  rcases hP.word with hW | hW | hW | hW | hW
  · exact Or.inl hW
  · exact Or.inr (Or.inl hW)
  · exact Or.inr (Or.inr (Or.inl hW))
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4⟩ := hW
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s₀, s₁, h0, h1, h2, h3, h4,
      (word_constants_holds O ϖ hϖ B.ℓ ell B.p b hℓ hMS.2.1 s₀ s₁ h0 h1).1⟩)))
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, h5, h6⟩ := hW
    have hb : 1 ≤ b s₀ := by
      have := hP.g_lt_b s₀ (by omega) (by rw [h3]; decide)
      omega
    have hle : 2 * sig + rr + 2 * g * ell ≤ parA sig rr g ellmax := by
      have := Nat.mul_le_mul_left (2 * g) hell
      unfold parA
      omega
    have hC : CLift B.ℓ (parA sig rr g ellmax) (U₁ s₁) (U₂ s₁) m.prL :=
      lemma_C_full_holds lemma_C_valuation_real O ϖ hϖ B e hB.one_le_e hB.assoc n V₁ V₂ L₁ L₂ h c ell _
        r₁ r₂ S₁ S₂ m H b kind U₁ U₂ g sig rr _ rfl hsh hMS hP.rd₁ hP.rd₂ hP.partner₁ hP.partner₂
        hP.p3₁ hP.p3₂ hP.p4a₁ hP.p4a₂ hP.bridge₁ hP.bridge₂ hP.flReg hP.mapFl hP.p4d s₀ s₁ h0 h1
        h2 h3 h4 (hP.cMap s₁ h1 h2) hle h6 h5
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s₀, s₁, h0, h1, h2, h3, h4, hC,
      (word_constants_holds O ϖ hϖ B.ℓ ell B.p b hℓ hMS.2.1 s₀ s₁ h0 h1).2 hb⟩)))

end arc

end Formalism.ExponentWindows.E.Prim

namespace Formalism.ExponentWindows.E

open PowerSeries

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ B e n _ Cu H j g G hh sig rr kap ellmax V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hB hN hL₁ hL₂ hU hBK hA κ hκ`. Establish `hM1 : 1 ≤ parM B.ℓ hh g`. Unfold `parM`. Conclude with `Nat.le_add_left 1 _`. Use `theorem_E_full_form O ϖ hϖ B n Cu (LamOf B Cu H) j (parM B.ℓ hh g) g sig rr (parA sig rr g ellmax) kap V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hM1 (Prim.baseGood hB hN.g_le_h j) (Prim.latGood hϖ hB hN hL₁) (Prim.latGood hϖ hB hN hL₂) hN.j_le_ell hU.φ_fix hU.γ_fix hBK.smul hBK.rho (fun κ h …` and prove the remaining obligations.

Take `⟨Y, hrep, hY⟩` from `hBK.ext κ hκ`. Conclude with `⟨Y, hrep, Prim.extGood hϖ hB hN.G_le_g _ hU hY⟩`. Unfold `parA first`. Consider the case `omega`. Consider the case `nlinarith [Nat.zero_le (2 * g * ellmax)]`.

Conclude with `Prim.arcHyp hϖ hB (hN.ell_le c hc) (hA c hc)`.
-/
theorem theorem_E_primitive_form : ThmEPrim := by
  intro O _ _ _ ϖ hϖ B e n _ Cu H j g G hh sig rr kap ellmax V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h
    Zf₁ Zf₂ hB hN hL₁ hL₂ hU hBK hA κ hκ
  have hM1 : 1 ≤ parM B.ℓ hh g := by
    unfold parM
    exact Nat.le_add_left 1 _
  refine theorem_E_full_form O ϖ hϖ B n Cu (LamOf B Cu H) j (parM B.ℓ hh g) g sig rr
    (parA sig rr g ellmax) kap V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hM1 (Prim.baseGood hB hN.g_le_h j)
    (Prim.latGood hϖ hB hN hL₁) (Prim.latGood hϖ hB hN hL₂) hN.j_le_ell hU.φ_fix hU.γ_fix
    hBK.smul hBK.rho (fun κ hκ => ?_) ?_ (fun c hc => ?_) κ hκ
  · obtain ⟨Y, hrep, hY⟩ := hBK.ext κ hκ
    exact ⟨Y, hrep, Prim.extGood hϖ hB hN.G_le_g _ hU hY⟩
  · unfold parA
    first
      | omega
      | nlinarith [Nat.zero_le (2 * g * ellmax)]
  · exact Prim.arcHyp hϖ hB (hN.ell_le c hc) (hA c hc)

end Formalism.ExponentWindows.E

namespace Formalism.ExponentWindows.E.Prim

open PowerSeries IdempotentNormalFormsRhoFacts GoodPlacesAlt

section p4
variable {O : Type} [CommRing O] {B : Base O}

/- English proof (translation)
Take `⟨e, he⟩` from `h4`. Choose the witnesses or unpack the hypotheses as in `⟨a', ha'⟩ : (X : PowerSeries O) ∣ a - C (PowerSeries.constantCoeff a) := by`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules. Establish `ha : a = C (PowerSeries.constantCoeff a) + X * a'`.

Rewrite using `[← ha']`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : B.γ (C (PowerSeries.constantCoeff a)) = C (PowerSeries.constantCoeff a)` using `by first`. Consider the case `exact B.γ.commutes _`. Consider the case `simpa [PowerSeries.algebraMap_eq] using B.γ.commutes (PowerSeries.constantCoeff a)`.

Use `⟨(1 + (e : PowerSeries O) * B.q) * B.γ a' - a', ?_⟩` and prove the remaining obligations. Establish `key : B.γ a - a = B.γ (C (PowerSeries.constantCoeff a) + X * a') - (C (PowerSeries.constantCoeff a) + X * a')`. Rewrite using `[← ha]`. Rewrite using `[key, map_add, map_mul, hC, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem γ_sub_X (h4 : B.E4) (a : PowerSeries O) : ∃ c : PowerSeries O, B.γ a - a = X * c := by
  obtain ⟨e, he⟩ := h4
  obtain ⟨a', ha'⟩ : (X : PowerSeries O) ∣ a - C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have ha : a = C (PowerSeries.constantCoeff a) + X * a' := by
    rw [← ha']
    ring
  have hC : B.γ (C (PowerSeries.constantCoeff a)) = C (PowerSeries.constantCoeff a) := by
    first
      | exact B.γ.commutes _
      | simpa [PowerSeries.algebraMap_eq] using B.γ.commutes (PowerSeries.constantCoeff a)
  refine ⟨(1 + (e : PowerSeries O) * B.q) * B.γ a' - a', ?_⟩
  have key : B.γ a - a = B.γ (C (PowerSeries.constantCoeff a) + X * a') -
      (C (PowerSeries.constantCoeff a) + X * a') := by
    rw [← ha]
  rw [key, map_add, map_mul, hC, he]
  ring

def GU (B : Base O) (x : PowerSeries O) : Prop := ∃ t : PowerSeries O, B.γ x = x * (1 + X * t)

/- English proof (translation)
Conclude with `⟨0, by simp⟩`.
-/
theorem GU.one : GU B 1 := by
  exact ⟨0, by simp⟩

/- English proof (translation)
Take `⟨t, ht⟩` from `hx`. Take `⟨t', ht'⟩` from `hy`. Conclude with `⟨t + t' + X * t * t', by rw [map_mul, ht, ht']; ring⟩`.
-/
theorem GU.mul {x y : PowerSeries O} (hx : GU B x) (hy : GU B y) : GU B (x * y) := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨t', ht'⟩ := hy
  exact ⟨t + t' + X * t * t', by rw [map_mul, ht, ht']; ring⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Conclude with `GU.one`. Consider the case `succ m ih`.

Rewrite using `[pow_succ]`. Conclude with `ih.mul hx`.
-/
theorem GU.pow {x : PowerSeries O} (hx : GU B x) (m : ℕ) : GU B (x ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact GU.one
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul hx

variable {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (PowerSeries O) V]

/- English proof (translation)
Establish `hcommK : ∀ (k : ℕ) (v : V), L.γ (i + (k : ZMod n)) (L.phiIt i k v) = L.phiIt i k (L.γ i v)`. Introduce `k v`. Proceed by induction on `k with`. Consider the case `zero => simp [Lat.phiIt]`. Consider the case `succ k ih => show L.γ (i + ((k + 1 : ℕ) : ZMod n)) (L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v)) = L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k (L.γ i v))`.

Rewrite using `[← L.comm]`. Establish `e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ih]`.

Establish `hsub : ∀ (k : ℕ) (v w : V), L.phiIt i k (v - w) = L.phiIt i k v - L.phiIt i k w`. Introduce `k v w`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => show L.φ _ (L.phiIt i k (v - w)) = L.φ _ (L.phiIt i k v) - L.φ _ (L.phiIt i k w)`.

Rewrite using `[ih, map_sub]`. Establish `hsmul : ∀ (k : ℕ) (a : PowerSeries O) (v : V), L.phiIt i k (a • v) = (⇑B.φ)^[k] a • L.phiIt i k v`. Introduce `k a v`. Proceed by induction on `k with`. Consider the case `zero => rfl`.

Consider the case `succ k ih => show L.φ _ (L.phiIt i k (a • v)) = _ • L.φ _ (L.phiIt i k v)`. Rewrite using `[ih, L.φ_semi, Function.iterate_succ_apply']`. Establish `hXdiv : ∀ k : ℕ, ∃ d : PowerSeries O, (⇑B.φ)^[k] X = X * d`. Take `⟨u, hu⟩` from `h3`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, by simp⟩`. Consider the case `succ k ih`. Take `⟨d, hd⟩` from `ih`. Use `⟨(u : PowerSeries O) * B.q ^ (B.ℓ - 1) * B.φ d, ?_⟩` and prove the remaining obligations.

Rewrite using `[Function.iterate_succ_apply', hd, map_mul, hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsmX : ∀ z ∈ L.pull i k, X • z ∈ sm X (L.pull i k)` using `fun z hz => by`. Unfold `sm`. Conclude with `Submodule.mem_map.2 ⟨z, hz, LinearMap.lsmul_apply _ _⟩`.

Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Take `⟨w, hw, hwe⟩` from `Submodule.mem_map.1 (h9 i v hv)`. Rewrite using `[hcommK, ← hsub, ← hwe, LinearMap.lsmul_apply, hsmul]`.

Take `⟨d, hd⟩` from `hXdiv k`. Rewrite using `[hd, mul_smul]`. Conclude with `hsmX _ ((L.pull i k).smul_mem d (Submodule.subset_span ⟨w, hw, rfl⟩))`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[map_add, show L.γ (i + (k : ZMod n)) x + L.γ (i + (k : ZMod n)) y - (x + y) = (L.γ (i + (k : ZMod n)) x - x) + (L.γ (i + (k : ZMod n)) y - y) by abel]`. Conclude with `(sm X (L.pull i k)).add_mem hx hy`. Consider the case `smul a x hxs hx`. Rewrite using `[L.γ_semi]`. Take `⟨c, hc⟩` from `γ_sub_X h4 a`.

Establish `e : B.γ a • L.γ (i + (k : ZMod n)) x - a • x = B.γ a • (L.γ (i + (k : ZMod n)) x - x) + (X : PowerSeries O) • (c • x)`. Rewrite using `[smul_sub, smul_smul, ← hc, sub_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `(sm X (L.pull i k)).add_mem ((sm X (L.pull i k)).smul_mem (B.γ a) hx) (hsmX _ ((L.pull i k).smul_mem c hxs))`.
-/
theorem γ_pull_sub (L : Lat B n V) (h3 : B.E3) (h4 : B.E4) (h9 : L.P9) (i : ZMod n) (k : ℕ)
    {p : V} (hp : p ∈ L.pull i k) : L.γ (i + (k : ZMod n)) p - p ∈ sm X (L.pull i k) := by
  have hcommK : ∀ (k : ℕ) (v : V), L.γ (i + (k : ZMod n)) (L.phiIt i k v) = L.phiIt i k (L.γ i v) := by
    intro k v
    induction k with
    | zero => simp [Lat.phiIt]
    | succ k ih =>
      show L.γ (i + ((k + 1 : ℕ) : ZMod n)) (L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v)) =
        L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k (L.γ i v))
      rw [← L.comm]
      have e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by
        push_cast
        ring
      rw [e, ih]
  have hsub : ∀ (k : ℕ) (v w : V), L.phiIt i k (v - w) = L.phiIt i k v - L.phiIt i k w := by
    intro k v w
    induction k with
    | zero => rfl
    | succ k ih =>
      show L.φ _ (L.phiIt i k (v - w)) = L.φ _ (L.phiIt i k v) - L.φ _ (L.phiIt i k w)
      rw [ih, map_sub]
  have hsmul : ∀ (k : ℕ) (a : PowerSeries O) (v : V), L.phiIt i k (a • v) = (⇑B.φ)^[k] a • L.phiIt i k v := by
    intro k a v
    induction k with
    | zero => rfl
    | succ k ih =>
      show L.φ _ (L.phiIt i k (a • v)) = _ • L.φ _ (L.phiIt i k v)
      rw [ih, L.φ_semi, Function.iterate_succ_apply']
  have hXdiv : ∀ k : ℕ, ∃ d : PowerSeries O, (⇑B.φ)^[k] X = X * d := by
    obtain ⟨u, hu⟩ := h3
    intro k
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨(u : PowerSeries O) * B.q ^ (B.ℓ - 1) * B.φ d, ?_⟩
      rw [Function.iterate_succ_apply', hd, map_mul, hu]
      ring
  have hsmX : ∀ z ∈ L.pull i k, X • z ∈ sm X (L.pull i k) := fun z hz => by
    unfold sm
    exact Submodule.mem_map.2 ⟨z, hz, LinearMap.lsmul_apply _ _⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 (h9 i v hv)
    rw [hcommK, ← hsub, ← hwe, LinearMap.lsmul_apply, hsmul]
    obtain ⟨d, hd⟩ := hXdiv k
    rw [hd, mul_smul]
    exact hsmX _ ((L.pull i k).smul_mem d (Submodule.subset_span ⟨w, hw, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, show L.γ (i + (k : ZMod n)) x + L.γ (i + (k : ZMod n)) y - (x + y) =
      (L.γ (i + (k : ZMod n)) x - x) + (L.γ (i + (k : ZMod n)) y - y) by abel]
    exact (sm X (L.pull i k)).add_mem hx hy
  | smul a x hxs hx =>
    rw [L.γ_semi]
    obtain ⟨c, hc⟩ := γ_sub_X h4 a
    have e : B.γ a • L.γ (i + (k : ZMod n)) x - a • x =
        B.γ a • (L.γ (i + (k : ZMod n)) x - x) + (X : PowerSeries O) • (c • x) := by
      rw [smul_sub, smul_smul, ← hc, sub_smul]
      abel
    rw [e]
    exact (sm X (L.pull i k)).add_mem ((sm X (L.pull i k)).smul_mem (B.γ a) hx)
      (hsmX _ ((L.pull i k).smul_mem c hxs))

end p4

end Formalism.ExponentWindows.E.Prim

namespace Formalism.ExponentWindows.E

open PowerSeries IdempotentNormalFormsRhoFacts

/- English proof (translation)
Introduce `O _ B n V₁ V₂ _ _ _ _ L₁ L₂ h c ell g rr hI₁ hI₂ hW x hx`. Use `set T := B.Th ell g with hT`. Establish `hx' : T • x ∈ L₂.N c` using `hx`. Take `⟨y, hy, hfy⟩` from `hW _ hx'`. Take `⟨x₁, hx₁⟩` from `hI₁.2 y`.

Establish `hx₁' : T • x₁ = y` using `hx₁`. Substitute `hx₁'` using the available equality. Use `⟨x₁, hy, ?_⟩` and prove the remaining obligations. Apply `hI₂.1` to reduce the goal to its premises. Use `show T • h.f x₁ = T • (B.lc ^ rr • x)`.

Rewrite using `[← map_smul, hfy, smul_comm]`.
-/
theorem partner_fourth_fourth_form : LiftsDivisibleOf := by
  intro O _ B n V₁ V₂ _ _ _ _ L₁ L₂ h c ell g rr hI₁ hI₂ hW x hx
  set T := B.Th ell g with hT
  have hx' : T • x ∈ L₂.N c := hx
  obtain ⟨y, hy, hfy⟩ := hW _ hx'
  obtain ⟨x₁, hx₁⟩ := hI₁.2 y
  have hx₁' : T • x₁ = y := hx₁
  subst hx₁'
  refine ⟨x₁, hy, ?_⟩
  apply hI₂.1
  show T • h.f x₁ = T • (B.lc ^ rr • x)
  rw [← map_smul, hfy, smul_comm]

end Formalism.ExponentWindows.E
