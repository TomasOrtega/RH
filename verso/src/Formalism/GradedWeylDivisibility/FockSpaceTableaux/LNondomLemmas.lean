import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

set_option linter.unusedSimpArgs false

section NonDom

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEul (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => (colW r n v s) • X v

def ndE (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = j then X (v.1, l) else 0

def ndF (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = l then X (v.1, j) else 0

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]`.
-/
lemma nd_weight_apply (s : Fin n) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (fun v => colW r n v s) m = Finsupp.weight (colW r n) m s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on generalizing m with`. Consider the case `C a`. Rewrite using `[derivation_C, coeff_zero, coeff_C]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]`. Consider the case `mul_X p v hp`. Establish `hX : ndEul R r n s (X v) = colW r n v s • X v` using `mkDerivation_X _ _ _`.

Rewrite using `[Derivation.leibniz, hX, coeff_add, smul_eq_mul, smul_eq_mul, mul_smul_comm, coeff_smul, coeff_mul_X', coeff_X_mul']`. Use `split_ifs with h`. Rewrite using `[hp]`. Establish `hle : Finsupp.single v 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Conclude with `Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)`. Establish `hm : m = (m - Finsupp.single v 1) + Finsupp.single v 1` using `(tsub_add_cancel_of_le hle).symm`. Establish `hw : Finsupp.weight (fun v => colW r n v s) m = Finsupp.weight (fun v => colW r n v s) (m - Finsupp.single v 1) + colW r n v s` using `by conv_lhs => rw [hm]`. Rewrite using `[map_add, Finsupp.weight_single, one_smul]`. Rewrite using `[hw, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
lemma ndEul_coeff (s : Fin n) (g : MvPolynomial (Fin r × Fin n) R) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (ndEul R r n s g) =
      (Finsupp.weight (fun v => colW r n v s) m : R) * coeff m g := by
  classical
  induction g using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [derivation_C, coeff_zero, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
  | mul_X p v hp =>
    have hX : ndEul R r n s (X v) = colW r n v s • X v := mkDerivation_X _ _ _
    rw [Derivation.leibniz, hX, coeff_add, smul_eq_mul, smul_eq_mul,
      mul_smul_comm, coeff_smul, coeff_mul_X', coeff_X_mul']
    split_ifs with h
    · rw [hp]
      have hle : Finsupp.single v 1 ≤ m := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
      have hm : m = (m - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight (fun v => colW r n v s) m =
          Finsupp.weight (fun v => colW r n v s) (m - Finsupp.single v 1) + colW r n v s := by
        conv_lhs => rw [hm]
        rw [map_add, Finsupp.weight_single, one_smul]
      rw [hw, nsmul_eq_mul]; push_cast; ring
    · simp

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[ndEul_coeff, coeff_smul, smul_eq_mul]`. Distinguish the cases in `h : coeff m g = 0`. Simplify using `[h]`. Rewrite using `[nd_weight_apply, hg h]`.
-/
lemma ndEul_homog {g : MvPolynomial (Fin r × Fin n) R} {μ : Fin n → ℕ}
    (hg : IsWeightedHomogeneous (colW r n) g μ) (s : Fin n) :
    ndEul R r n s g = (μ s : R) • g := by
  ext m
  rw [ndEul_coeff, coeff_smul, smul_eq_mul]
  by_cases h : coeff m g = 0
  · simp [h]
  · rw [nd_weight_apply, hg h]

/- English proof (translation)
Use extensionality with `m`. Establish `h1` using `congrArg (coeff m) h`. Rewrite `h1` using `[ndEul_coeff, coeff_neg]`. Establish `h2 : ((Finsupp.weight (fun v => colW r n v s) m : R) + 1) * coeff m g = 0`. Take the linear combination `h1`.

Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 (Nat.cast_add_one_ne_zero _)`. Simplify using `using h3`.
-/
lemma ndEul_neg_eq_zero [IsDomain R] [CharZero R] {g : MvPolynomial (Fin r × Fin n) R}
    (s : Fin n) (h : ndEul R r n s g = -g) : g = 0 := by
  ext m
  have h1 := congrArg (coeff m) h
  rw [ndEul_coeff, coeff_neg] at h1
  have h2 : ((Finsupp.weight (fun v => colW r n v s) m : R) + 1) * coeff m g = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.cast_add_one_ne_zero _)
  · simpa using h3

/- English proof (translation)
Establish `key : ⁅ndE R r n l j, ndF R r n l j⁆ = ndEul R r n l - ndEul R r n j`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Rewrite using `[Derivation.commutator_apply, Derivation.sub_apply]`. Distinguish the cases in `h1 : s = l`.

Substitute `h1` using the available equality. Simplify using `[ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]`. Distinguish the cases in `h2 : s = j`. Substitute `h2` using the available equality. Simplify using `[ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]`.

Simplify using `[ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]`. Use `congrArg (fun D => D g) key` as an intermediate fact. Simplify using `only [Derivation.commutator_apply, Derivation.sub_apply] at this`. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws.
-/
lemma nd_comm_EF {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndE R r n l j (ndF R r n l j g) =
      ndF R r n l j (ndE R r n l j g) + (ndEul R r n l g - ndEul R r n j g) := by
  have key : ⁅ndE R r n l j, ndF R r n l j⁆ = ndEul R r n l - ndEul R r n j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at this
  rw [← this]; abel

/- English proof (translation)
Establish `key : ⁅ndEul R r n l, ndF R r n l j⁆ = -ndF R r n l j`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Rewrite using `[Derivation.commutator_apply, Derivation.neg_apply]`. Distinguish the cases in `h1 : s = l`.

Substitute `h1` using the available equality. Simplify using `[ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]`. Distinguish the cases in `h2 : s = j`. Substitute `h2` using the available equality. Simplify using `[ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]`.

Simplify using `[ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]`. Use `congrArg (fun D => D g) key` as an intermediate fact. Simplify using `only [Derivation.commutator_apply, Derivation.neg_apply] at this`. Rewrite using `[sub_eq_iff_eq_add.1 this]`. Normalize the expressions using the abelian group laws.
-/
lemma nd_comm_EulF_l {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n l (ndF R r n l j g) = ndF R r n l j (ndEul R r n l g) - ndF R r n l j g := by
  have key : ⁅ndEul R r n l, ndF R r n l j⁆ = -ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.neg_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.neg_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

/- English proof (translation)
Establish `key : ⁅ndEul R r n j, ndF R r n l j⁆ = ndF R r n l j`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Rewrite using `[Derivation.commutator_apply]`. Distinguish the cases in `h1 : s = l`.

Substitute `h1` using the available equality. Simplify using `[ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]`. Distinguish the cases in `h2 : s = j`. Substitute `h2` using the available equality. Simplify using `[ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]`.

Simplify using `[ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]`. Use `congrArg (fun D => D g) key` as an intermediate fact. Simplify using `only [Derivation.commutator_apply] at this`. Rewrite using `[sub_eq_iff_eq_add.1 this]`. Normalize the expressions using the abelian group laws.
-/
lemma nd_comm_EulF_j {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n j (ndF R r n l j g) = ndF R r n l j (ndEul R r n j g) + ndF R r n l j g := by
  have key : ⁅ndEul R r n j, ndF R r n l j⁆ = ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

end NonDom

end Formalism.GradedWeylDivisibility
