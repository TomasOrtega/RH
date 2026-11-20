import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SumLeSqrtCardMul

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}

noncomputable def evW (w : Fin (N + 1) → B) :
    MvPolynomial (UXVar D N) R →ₐ[R] MvPolynomial (Fin (D + 2) × Fin (N + 1)) B :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (w j))

def CoeffIn (W : Submodule R B) (m : ℕ) (p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) : Prop :=
  ∀ β, coeff β p ∈ W ^ m

variable (W : Submodule R B)

/- English proof (translation)
Introduce `β` and use `by rw [coeff_add] exact Submodule.add_mem _ (hp β) (hq β)`.
-/
theorem coeffIn_add {m : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m q) : CoeffIn W m (p + q) := fun β => by
  rw [coeff_add]
  exact Submodule.add_mem _ (hp β) (hq β)

/- English proof (translation)
Introduce `β` and use `by rw [coeff_mul, pow_add] exact Submodule.sum_mem _ fun x _ => Submodule.mul_mem_mul (hp _) (hq _)`.
-/
theorem coeffIn_mul {m m' : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m' q) : CoeffIn W (m + m') (p * q) := fun β => by
  rw [coeff_mul, pow_add]
  exact Submodule.sum_mem _ fun x _ => Submodule.mul_mem_mul (hp _) (hq _)

/- English proof (translation)
Introduce `β` and use `by rw [pow_zero, coeff_one] split_ifs · exact Submodule.mem_one.2 ⟨1, map_one _⟩ · exact zero_mem _`.
-/
theorem coeffIn_one : CoeffIn W 0 (1 : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [pow_zero, coeff_one]
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using coeffIn_one W`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Nat.mul_succ]`. Conclude with `coeffIn_mul W ih hp`.
-/
theorem coeffIn_pow {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (k : ℕ) : CoeffIn W (m * k) (p ^ k) := by
  induction k with
  | zero => simpa using coeffIn_one W
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact coeffIn_mul W ih hp

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s (fun _ => by simpa using coeffIn_one W) ?_` and prove the remaining obligations. Introduce `a s ha ih h`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `coeffIn_mul W (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem coeffIn_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin (D + 2) × Fin (N + 1)) B)
    (m : ι → ℕ) (h : ∀ i ∈ s, CoeffIn W (m i) (p i)) : CoeffIn W (∑ i ∈ s, m i) (∏ i ∈ s, p i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using coeffIn_one W) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact coeffIn_mul W (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `β` and use `by rw [coeff_C_mul, ← Algebra.smul_def] exact Submodule.smul_mem _ r (hp β)`.
-/
theorem coeffIn_smul {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (r : R) : CoeffIn W m (C (algebraMap R B r) * p) := fun β => by
  rw [coeff_C_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hp β)

/- English proof (translation)
Introduce `β` and use `by rw [pow_zero, coeff_X'] split_ifs · exact Submodule.mem_one.2 ⟨1, map_one _⟩ · exact zero_mem _`.
-/
theorem coeffIn_X (u : Fin (D + 2) × Fin (N + 1)) : CoeffIn W 0 (X u : MvPolynomial _ B) := fun β => by
  rw [pow_zero, coeff_X']
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

/- English proof (translation)
Introduce `β` and use `by rw [coeff_sum, pow_one] refine Submodule.sum_mem _ fun j _ => ?_ rw [mul_comm, coeff_C_mul, coeff_X'] split_ifs · rw [mul_one] exact hw j · rw [mul_zero] exact zero_mem _`.
-/
theorem coeffIn_lin (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) (i : Fin (D + 2)) :
    CoeffIn W 1 (∑ j, X (i, j) * C (w j) : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [coeff_sum, pow_one]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mul_comm, coeff_C_mul, coeff_X']
  split_ifs
  · rw [mul_one]
    exact hw j
  · rw [mul_zero]
    exact zero_mem _

/- English proof (translation)
Rewrite using `[xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]`. Simplify using the standard rewrite rules. Introduce `x _ hx`. Consider the cases of `x with`. Consider the case `inl p => rfl`.

Consider the case `inr i => simpa using hx`.
-/
private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx

/- English proof (translation)
Introduce `β`. Rewrite using `[Q.as_sum, map_sum, coeff_sum]`. Use `Submodule.sum_mem _ fun s hs => ?_` and prove the remaining obligations. Establish `hterm : CoeffIn W n (evW w (monomial s (coeff s Q)))`. Rewrite using `[evW, aeval_monomial, MvPolynomial.algebraMap_apply]`.

Apply `coeffIn_smul` to reduce the goal to its premises. Rewrite using `[Finsupp.prod, ← hx s hs, ← sum_support_inr_eq_xDeg s]`. Use `coeffIn_prod W s.support _ _ fun x _ => ?_` and prove the remaining obligations. Consider the cases of `x with`. Consider the case `inl p => simpa using coeffIn_pow W (coeffIn_X W p) (s (Sum.inl p))`.

Consider the case `inr i => simpa using coeffIn_pow W (coeffIn_lin W w hw i) (s (Sum.inr i))`. Conclude with `hterm β`.
-/
theorem coeffIn_evW (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) {n : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) : CoeffIn W n (evW w Q) := by
  intro β
  rw [Q.as_sum, map_sum, coeff_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hterm : CoeffIn W n (evW w (monomial s (coeff s Q))) := by
    rw [evW, aeval_monomial, MvPolynomial.algebraMap_apply]
    apply coeffIn_smul
    rw [Finsupp.prod, ← hx s hs, ← sum_support_inr_eq_xDeg s]
    refine coeffIn_prod W s.support _ _ fun x _ => ?_
    cases x with
    | inl p => simpa using coeffIn_pow W (coeffIn_X W p) (s (Sum.inl p))
    | inr i => simpa using coeffIn_pow W (coeffIn_lin W w hw i) (s (Sum.inr i))
  exact hterm β

/- English proof (translation)
Establish `h` using `coeffIn_evW (Submodule.span R (Set.range w)) w (fun j => Submodule.subset_span ⟨j, rfl⟩) Q hx β`. Rewrite `h` using `[Submodule.span_pow]`. Use `Submodule.span_mono ?_ h` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha` using `[Set.mem_pow]`.

Take `⟨f, rfl⟩` from `ha`. Use `choose s hs using fun k => (f k).2`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `show ∏ k, w (s k) = _`. Rewrite using `[List.prod_ofFn]`.

Conclude with `Finset.prod_congr rfl fun k _ => hs k`.
-/
theorem coeff_evW_mem (w : Fin (N + 1) → B) {n : ℕ} (Q : MvPolynomial (UXVar D N) R)
    (hx : XHom n Q) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    coeff β (evW w Q) ∈
      Submodule.span R (Set.range fun s : Fin n → Fin (N + 1) => ∏ k, w (s k)) := by
  have h := coeffIn_evW (Submodule.span R (Set.range w)) w (fun j => Submodule.subset_span ⟨j, rfl⟩) Q hx β
  rw [Submodule.span_pow] at h
  refine Submodule.span_mono ?_ h
  intro a ha
  rw [Set.mem_pow] at ha
  obtain ⟨f, rfl⟩ := ha
  choose s hs using fun k => (f k).2
  refine ⟨s, ?_⟩
  show ∏ k, w (s k) = _
  rw [List.prod_ofFn]
  exact Finset.prod_congr rfl fun k _ => hs k

end

/- English proof (translation)
Rewrite using `[Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Simplify using `only [evW, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul, map_C, Finsupp.prod, map_prod, map_pow]`. Rewrite using `[← IsScalarTower.algebraMap_apply, mul_assoc]`. Use `congr 1`.

Rewrite using `[← hx s hs, ← sum_support_inr_eq_xDeg s]`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Consider the cases of `x with`. Consider the case `inl p => simp`.

Consider the case `inr i`. Simplify using `only [Sum.elim_inr, map_sum, map_mul, map_X, map_C]`. Rewrite using `[← mul_pow, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem evW_factor {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] [Algebra S B] [IsScalarTower R S B] {D N n : ℕ} (y : Fin (N + 1) → S) (w0 : B)
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) :
    evW (fun j => algebraMap S B (y j) * w0) Q =
      MvPolynomial.map (algebraMap S B) (evW y Q) * C (w0 ^ n) := by
  rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [evW, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul, map_C, Finsupp.prod,
    map_prod, map_pow]
  rw [← IsScalarTower.algebraMap_apply, mul_assoc]
  congr 1
  rw [← hx s hs, ← sum_support_inr_eq_xDeg s]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  cases x with
  | inl p => simp
  | inr i =>
    simp only [Sum.elim_inr, map_sum, map_mul, map_X, map_C]
    rw [← mul_pow, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Establish `h : (MvPolynomial.map P).comp (evW (R` using `K) (D := D) y).toRingHom = (Ey (D := D) (fun j => P (y j))).toRingHom.comp (MvPolynomial.map sg) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[evW, Ey, ← hP]`. Introduce `i`.

Apply the tactic sequence `cases i <;> simp [evW, Ey]`. Conclude with `RingHom.congr_fun h R`.
-/
theorem map_evW_eq {K S : Type*} [Field K] [CommRing S] [Algebra K S] {D N : ℕ} (P : S →+* ℂ)
    (sg : K →+* ℂ) (hP : P.comp (algebraMap K S) = sg) (y : Fin (N + 1) → S)
    (R : MvPolynomial (UXVar D N) K) :
    MvPolynomial.map P (evW (R := K) y R) = Ey (fun j => P (y j)) (MvPolynomial.map sg R) := by
  have h : (MvPolynomial.map P).comp (evW (R := K) (D := D) y).toRingHom =
      (Ey (D := D) (fun j => P (y j))).toRingHom.comp (MvPolynomial.map sg) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evW, Ey, ← hP]
    · intro i
      cases i <;> simp [evW, Ey]
  exact RingHom.congr_fun h R

end ReciprocityTheory.ChartRestriction.G.T0
