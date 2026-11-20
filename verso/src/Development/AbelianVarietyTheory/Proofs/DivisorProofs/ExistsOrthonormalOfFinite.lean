import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi

open Matrix

namespace GlobalTheory.FiniteHermitian

/- English proof (translation)
Establish `key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m)`. Introduce `i d hd h`. Establish `h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k)`. Introduce `t k`. Proceed by induction on `t with`.

Consider the case `zero => simp`. Consider the case `succ t ih`. Establish `: i + k + (t + 1) * d = (i + d) + (k + t * d)` using `by ring`. Rewrite using `[this, pow_add, h, ← pow_add, ← add_assoc, ih]`. Establish `hle : i ≤ (i + 1) * d` using `by nlinarith`.

Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`. Use `⟨(i + 1) * d, by positivity, ?_⟩` and prove the remaining obligations. Unfold `IsIdempotentElem`. Rewrite using `[← pow_add]`. Use `h1 (i + 1) k` as an intermediate fact.

Rewrite `this` using `[← hk]`. Conclude with `this`. Take `⟨i, j, hij, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Conclude with `key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)`.

Conclude with `key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)`.
-/
theorem exists_pow_isIdempotentElem {R : Type} [Monoid R] [Finite R] (x : R) :
    ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
  have key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
    intro i d hd h
    have h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k) := by
      intro t k
      induction t with
      | zero => simp
      | succ t ih =>
        have : i + k + (t + 1) * d = (i + d) + (k + t * d) := by ring
        rw [this, pow_add, h, ← pow_add, ← add_assoc, ih]
    have hle : i ≤ (i + 1) * d := by nlinarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    have := h1 (i + 1) k
    rw [← hk] at this
    exact this
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
  · exact key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

/- English proof (translation)
Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Take `⟨m, hm, he⟩` from `exists_pow_isIdempotentElem x`. Break down `h _ he with h0 | h1` into its components or cases. Conclude with `Or.inr (IsNilpotent.isUnit_one_sub ⟨m, h0⟩)`. Conclude with `Or.inl (IsUnit.of_pow_eq_one h1 hm.ne')`.
-/
theorem isLocalRing_of_idempotent {R : Type} [CommRing R] [Finite R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing R := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨m, hm, he⟩ := exists_pow_isIdempotentElem x
  rcases h _ he with h0 | h1
  · exact Or.inr (IsNilpotent.isUnit_one_sub ⟨m, h0⟩)
  · exact Or.inl (IsUnit.of_pow_eq_one h1 hm.ne')

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem cT_comb {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (c d : R)
    (A B : Matrix (Fin n) (Fin n) R) :
    ((c • A + d • B).map s).transpose = s c • (A.map s).transpose + s d • (B.map s).transpose := by
  ext i j
  simp

/- English proof (translation)
Take `⟨P, hP⟩` from `hu.exists_right_inv`. Establish `hP' : (P.map s).transpose * Q = 1` using `by conv_lhs => rw [← hQ]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, hP]`. Simplify using the standard rewrite rules. Establish `h1 : ((1 : Matrix (Fin n) (Fin n) R).map s).transpose = 1` using `by simp`.

Establish `hs1 : s (1 - e) = e` using `by rw [map_sub, map_one, hse]; ring`. Establish `h01 : (1 - e) * e = 0` using `by rw [sub_mul, one_mul, he.eq, sub_self]`. Establish `h10 : e * (1 - e) = 0` using `by rw [mul_comm, h01]`. Establish `h11 : (1 - e) * (1 - e) = 1 - e` using `he.one_sub.eq`. Use `⟨e • P + (1 - e) • 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[cT_comb, hs1, hse, h1]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hP', hP, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, h01, h10, h11, he.eq, zero_smul]`. Rewrite using `[zero_add, add_zero, ← add_smul]`. Simplify using the standard rewrite rules.
-/
theorem exists_of_split {R : Type} [CommRing R] (s : R →+* R) (e : R)
    (he : IsIdempotentElem e) (hse : s e = 1 - e) {n : ℕ} (Q : Matrix (Fin n) (Fin n) R)
    (hQ : (Q.map s).transpose = Q) (hu : IsUnit Q) :
    ∃ a : Matrix (Fin n) (Fin n) R, (a.map s).transpose * Q * a = 1 := by
  obtain ⟨P, hP⟩ := hu.exists_right_inv
  have hP' : (P.map s).transpose * Q = 1 := by
    conv_lhs => rw [← hQ]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hP]
    simp
  have h1 : ((1 : Matrix (Fin n) (Fin n) R).map s).transpose = 1 := by simp
  have hs1 : s (1 - e) = e := by rw [map_sub, map_one, hse]; ring
  have h01 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have h10 : e * (1 - e) = 0 := by rw [mul_comm, h01]
  have h11 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  refine ⟨e • P + (1 - e) • 1, ?_⟩
  rw [cT_comb, hs1, hse, h1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hP', hP,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, h01, h10, h11, he.eq, zero_smul]
  rw [zero_add, add_zero, ← add_smul]
  simp

/- English proof (translation)
Establish `hs1 : s (1 - e) = 1 - e` using `by rw [map_sub, map_one, hse]`. Establish `h01 : (1 - e) * e = 0` using `by rw [sub_mul, one_mul, he.eq, sub_self]`. Establish `h10 : e * (1 - e) = 0` using `by rw [mul_comm, h01]`. Establish `h11 : (1 - e) * (1 - e) = 1 - e` using `he.one_sub.eq`. Use `⟨(1 - e) • A + e • B, ?_⟩` and prove the remaining obligations.

Rewrite using `[cT_comb, hs1, hse]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h01, h10, h11, he.eq, zero_smul]`. Rewrite using `[zero_add, add_zero, hA, hB, ← add_smul]`. Simplify using the standard rewrite rules.
-/
theorem exists_of_glue {R : Type} [CommRing R] (s : R →+* R) (e : R)
    (he : IsIdempotentElem e) (hse : s e = e) {n : ℕ} (Q A B : Matrix (Fin n) (Fin n) R)
    (hA : (1 - e) • ((A.map s).transpose * Q * A) = (1 - e) • (1 : Matrix (Fin n) (Fin n) R))
    (hB : e • ((B.map s).transpose * Q * B) = e • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ a : Matrix (Fin n) (Fin n) R, (a.map s).transpose * Q * a = 1 := by
  have hs1 : s (1 - e) = 1 - e := by rw [map_sub, map_one, hse]
  have h01 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have h10 : e * (1 - e) = 0 := by rw [mul_comm, h01]
  have h11 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  refine ⟨(1 - e) • A + e • B, ?_⟩
  rw [cT_comb, hs1, hse]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, smul_smul, h01, h10, h11, he.eq, zero_smul]
  rw [zero_add, add_zero, hA, hB, ← add_smul]
  simp

def HasOrthonormal (R : Type) [CommRing R] : Prop :=
  ∀ s : R →+* R, (∀ x, s (s x) = x) → (∃ τ : R, τ + s τ = 1) →
    (∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u) →
    ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) R), (Q.map s).transpose = Q → IsUnit Q →
      ∃ a : Matrix (Fin n) (Fin n) R, (a.map s).transpose * Q * a = 1

/- English proof (translation)
Use `set I : Ideal R := Ideal.span {e} with hI`. Set `π : R →+* R ⧸ I` to `Ideal.Quotient.mk I`. Establish `h01 : (1 - e) * e = 0` using `by rw [sub_mul, one_mul, he.eq, sub_self]`. Establish `hπe : π e = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)`. Establish `hker : ∀ x y : R, π x = π y → (1 - e) * x = (1 - e) * y`.

Introduce `x y h`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)`. Rewrite using `[← sub_eq_zero, ← mul_sub, ← hc, mul_left_comm, h01, mul_zero]`. Set `t : R ⧸ I →+* R ⧸ I` to `Ideal.Quotient.lift I (π.comp s) (by`. Introduce `a ha`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[RingHom.comp_apply, map_mul, hse, map_mul, hπe, mul_zero])`. Establish `ht : ∀ x, t (π x) = π (s x)` using `fun x => rfl`. Establish `hsurj : Function.Surjective π` using `Ideal.Quotient.mk_surjective`. Take `⟨a, ha⟩` from `ih t (by intro x; obtain ⟨y, rfl⟩ := hsurj x; rw [ht, ht, hs]) (by obtain ⟨τ, hτ⟩ := hτ; exact ⟨π τ, by rw [ht, ← map_add, hτ, map_one]⟩) (by`.

Introduce `u hu1 hu2`. Take `⟨w, hw⟩` from `hu1.exists_right_inv`. Take `⟨u, rfl⟩` from `hsurj u`. Take `⟨w, rfl⟩` from `hsurj w`. Establish `e1` using `hker (u * w) 1 (by rw [map_mul, hw, map_one])`.

Establish `e2` using `hker (s u) u (by rw [← ht, hu2])`. Establish `h11 : (1 - e) * (1 - e) = 1 - e` using `he.one_sub.eq`. Establish `hee : e * e = e` using `he.eq`. Take `⟨x, hx⟩` from `hn ((1 - e) * u + e) (IsUnit.of_mul_eq_one ((1 - e) * w + e) (by`. Take the linear combination `(u * w) * h11 + e1 + (u + w) * h01 + hee))`.

Use the proof step `(by rw [map_add, map_mul, map_sub, map_one, hse, e2])`. Use `⟨π x, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, ← map_mul, hx, map_add, map_mul, map_sub, map_one, hπe]`. Use the proof step `ring)`. Use `n (Q.map π)`.

Use the proof step `(by`. Use extensionality with `i j`. Use `congrFun (congrFun hQ i) j` as an intermediate fact. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢`. Rewrite using `[ht, this])`.

Use the proof step `(hu.map π.mapMatrix)`. Use `choose σ hσ using hsurj`. Establish `hA : (a.map σ).map π = a` using `by ext i j; simp [hσ]`. Use `⟨a.map σ, ?_⟩` and prove the remaining obligations. Establish `hB : (((a.map σ).map s).transpose * Q * (a.map σ)).map π = (1 : Matrix (Fin n) (Fin n) R).map π`.

Establish `: (((a.map σ).map s).transpose).map π = (a.map t).transpose`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[← ht, hσ]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hA, this, ha, Matrix.map_one _ (map_zero π) (map_one π)]`.

Use extensionality with `i j`. Conclude with `hker _ _ (congrFun (congrFun hB i) j)`.
-/
theorem exists_mod_idempotent {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x)
    (hτ : ∃ τ : R, τ + s τ = 1) (hn : ∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u)
    (e : R) (he : IsIdempotentElem e) (hse : s e = e)
    (ih : HasOrthonormal (R ⧸ Ideal.span {e}))
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) R) (hQ : (Q.map s).transpose = Q) (hu : IsUnit Q) :
    ∃ A : Matrix (Fin n) (Fin n) R,
      (1 - e) • ((A.map s).transpose * Q * A) = (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
  set I : Ideal R := Ideal.span {e} with hI
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  have h01 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have hπe : π e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
  have hker : ∀ x y : R, π x = π y → (1 - e) * x = (1 - e) * y := by
    intro x y h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
    rw [← sub_eq_zero, ← mul_sub, ← hc, mul_left_comm, h01, mul_zero]
  let t : R ⧸ I →+* R ⧸ I := Ideal.Quotient.lift I (π.comp s) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, hse, map_mul, hπe, mul_zero])
  have ht : ∀ x, t (π x) = π (s x) := fun x => rfl
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  obtain ⟨a, ha⟩ := ih t
    (by intro x; obtain ⟨y, rfl⟩ := hsurj x; rw [ht, ht, hs])
    (by obtain ⟨τ, hτ⟩ := hτ; exact ⟨π τ, by rw [ht, ← map_add, hτ, map_one]⟩)
    (by
      intro u hu1 hu2
      obtain ⟨w, hw⟩ := hu1.exists_right_inv
      obtain ⟨u, rfl⟩ := hsurj u
      obtain ⟨w, rfl⟩ := hsurj w
      have e1 := hker (u * w) 1 (by rw [map_mul, hw, map_one])
      have e2 := hker (s u) u (by rw [← ht, hu2])
      have h11 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
      have hee : e * e = e := he.eq
      obtain ⟨x, hx⟩ := hn ((1 - e) * u + e)
        (IsUnit.of_mul_eq_one ((1 - e) * w + e) (by
          linear_combination (u * w) * h11 + e1 + (u + w) * h01 + hee))
        (by rw [map_add, map_mul, map_sub, map_one, hse, e2])
      refine ⟨π x, ?_⟩
      rw [ht, ← map_mul, hx, map_add, map_mul, map_sub, map_one, hπe]
      ring)
    n (Q.map π)
    (by
      ext i j
      have := congrFun (congrFun hQ i) j
      simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
      rw [ht, this])
    (hu.map π.mapMatrix)
  choose σ hσ using hsurj
  have hA : (a.map σ).map π = a := by ext i j; simp [hσ]
  refine ⟨a.map σ, ?_⟩
  have hB : (((a.map σ).map s).transpose * Q * (a.map σ)).map π
      = (1 : Matrix (Fin n) (Fin n) R).map π := by
    have : (((a.map σ).map s).transpose).map π = (a.map t).transpose := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      rw [← ht, hσ]
    rw [Matrix.map_mul, Matrix.map_mul, hA, this, ha, Matrix.map_one _ (map_zero π) (map_one π)]
  ext i j
  exact hker _ _ (congrFun (congrFun hB i) j)

/- English proof (translation)
Establish `hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {e}))` using `Ideal.Quotient.mk_surjective`. Use `lt_of_le_of_ne (Nat.card_le_card_of_surjective _ hsurj) fun h => he ?_` and prove the remaining obligations. Establish `hb` using `(Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, h.symm⟩`. Apply `hb.1` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)`.
-/
theorem card_quot_lt {R : Type} [CommRing R] [Finite R] (e : R) (he : e ≠ 0) :
    Nat.card (R ⧸ Ideal.span {e}) < Nat.card R := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {e})) :=
    Ideal.Quotient.mk_surjective
  refine lt_of_le_of_ne (Nat.card_le_card_of_surjective _ hsurj) fun h => he ?_
  have hb := (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, h.symm⟩
  apply hb.1
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `R _ _ hk s hs hτ hn n Q hQ hu`. Use `haveI hfin : ∀ I : Ideal R, Finite (R ⧸ I) := fun I => Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))`. Distinguish the cases in `h1 : ∃ e : R, IsIdempotentElem e ∧ s e = e ∧ e ≠ 0 ∧ e ≠ 1`.

Take `⟨e, he, hse, h0, h1⟩` from `h1`. Take `⟨A, hA⟩` from `exists_mod_idempotent s hs hτ hn e he hse (ih _ (hk ▸ card_quot_lt e h0) _ rfl) Q hQ hu`. Take `⟨B, hB⟩` from `exists_mod_idempotent s hs hτ hn (1 - e) he.one_sub (by rw [map_sub, map_one, hse]) (ih _ (hk ▸ card_quot_lt (1 - e) (sub_ne_zero.2 h1.symm)) _ rfl) Q hQ hu`. Rewrite `hB` using `[sub_sub_cancel]`. Conclude with `exists_of_glue s e he hse Q A B hA hB`.

Establish `hfix : ∀ e : R, IsIdempotentElem e → s e = e → e = 0 ∨ e = 1`. Introduce `e he hse`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `h1 ⟨e, he, hse, hc.1, hc.2⟩`.

Distinguish the cases in `h2 : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1`. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Conclude with `⟨1, Subsingleton.elim _ _⟩`. Use `haveI := isLocalRing_of_idempotent h2`. Take `⟨a, ha⟩` from `GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing R s hs hτ hn n Q hQ hu`.

Conclude with `⟨a.1, ha⟩`. Use `push Not at h2`. Take `⟨e, he, h0, h1⟩` from `h2`. Establish `hee : e * e = e` using `he.eq`. Establish `hff : s e * s e = s e` using `by rw [← map_mul, hee]`.

Establish `hz : e * s e = 0`. Break down `hfix (e * s e) (he.mul (he.map s)) (by rw [map_mul, hs, mul_comm]) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (by linear_combination (1 - e) * h + s e * hee) h1`. Establish `ho : e + s e = 1`.

Break down `hfix (e + s e) (show (e + s e) * (e + s e) = e + s e by` into its components or cases. Take the linear combination `hee + hff + 2 * hz) (by rw [map_add, hs, add_comm]) with h | h`. Conclude with `absurd (by linear_combination e * h - hee - hz) h0`. Conclude with `h`. Conclude with `exists_of_split s e he (by linear_combination ho) Q hQ hu`.
-/
theorem hasOrthonormal_of_finite (k : ℕ) :
    ∀ (R : Type) [CommRing R] [Finite R], Nat.card R = k → HasOrthonormal R := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro R _ _ hk s hs hτ hn n Q hQ hu
    haveI hfin : ∀ I : Ideal R, Finite (R ⧸ I) := fun I =>
      Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
    by_cases h1 : ∃ e : R, IsIdempotentElem e ∧ s e = e ∧ e ≠ 0 ∧ e ≠ 1
    · obtain ⟨e, he, hse, h0, h1⟩ := h1
      obtain ⟨A, hA⟩ := exists_mod_idempotent s hs hτ hn e he hse
        (ih _ (hk ▸ card_quot_lt e h0) _ rfl) Q hQ hu
      obtain ⟨B, hB⟩ := exists_mod_idempotent s hs hτ hn (1 - e) he.one_sub
        (by rw [map_sub, map_one, hse])
        (ih _ (hk ▸ card_quot_lt (1 - e) (sub_ne_zero.2 h1.symm)) _ rfl) Q hQ hu
      rw [sub_sub_cancel] at hB
      exact exists_of_glue s e he hse Q A B hA hB
    · have hfix : ∀ e : R, IsIdempotentElem e → s e = e → e = 0 ∨ e = 1 := by
        intro e he hse
        by_contra hc
        push Not at hc
        exact h1 ⟨e, he, hse, hc.1, hc.2⟩
      by_cases h2 : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1
      · rcases subsingleton_or_nontrivial R with hR | hR
        · exact ⟨1, Subsingleton.elim _ _⟩
        · haveI := isLocalRing_of_idempotent h2
          obtain ⟨a, ha⟩ :=
            GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing R s hs hτ hn n Q hQ hu
          exact ⟨a.1, ha⟩
      · push Not at h2
        obtain ⟨e, he, h0, h1⟩ := h2
        have hee : e * e = e := he.eq
        have hff : s e * s e = s e := by rw [← map_mul, hee]
        have hz : e * s e = 0 := by
          rcases hfix (e * s e) (he.mul (he.map s)) (by rw [map_mul, hs, mul_comm]) with h | h
          · exact h
          · exact absurd (by linear_combination (1 - e) * h + s e * hee) h1
        have ho : e + s e = 1 := by
          rcases hfix (e + s e) (show (e + s e) * (e + s e) = e + s e by
            linear_combination hee + hff + 2 * hz) (by rw [map_add, hs, add_comm]) with h | h
          · exact absurd (by linear_combination e * h - hee - hz) h0
          · exact h
        exact exists_of_split s e he (by linear_combination ho) Q hQ hu

/- English proof (translation)
Introduce `R _ _ s hs hτ hn n Q hQ hu`. Take `⟨a, ha⟩` from `hasOrthonormal_of_finite _ R rfl s hs hτ hn n Q hQ hu`. Establish `: IsUnit a` using `IsUnit.of_mul_eq_one_right _ ha`. Conclude with `⟨this.unit, by rw [IsUnit.unit_spec]; exact ha⟩`.
-/
theorem exists_orthonormal_of_finite :
    ∀ (R : Type) [CommRing R] [Finite R] (s : R →+* R), (∀ x, s (s x) = x) → (∃ τ : R, τ + s τ = 1) → (∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u) → ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) R), (Q.map s).transpose = Q → IsUnit Q → ∃ a : GL (Fin n) R, (a.1.map s).transpose * Q * a.1 = 1 := by
  intro R _ _ s hs hτ hn n Q hQ hu
  obtain ⟨a, ha⟩ := hasOrthonormal_of_finite _ R rfl s hs hτ hn n Q hQ hu
  have : IsUnit a := IsUnit.of_mul_eq_one_right _ ha
  exact ⟨this.unit, by rw [IsUnit.unit_spec]; exact ha⟩

end GlobalTheory.FiniteHermitian
