import Formalism.RealPlaceAnalysis.Complexify

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace Formalism.REAL

variable {n : ℕ}

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma Jm_mul_Jm_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Jm ε, Jm ε, Jm_mul_Jm_eq_one ε, Jm_mul_Jm_eq_one ε⟩, rfl⟩`.
-/
lemma isUnit_signature_matrix (ε : Fin n → Bool) : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_Jm_eq_one ε, Jm_mul_Jm_eq_one ε⟩, rfl⟩

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (Jm_mul_Jm_eq_one ε)`.
-/
lemma signature_matrix_inv_self (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_Jm_eq_one ε)

/- English proof (translation)
Establish `h` using `Matrix.exp_conj (Jm ε) A (isUnit_signature_matrix ε)`. Rewrite `h` using `[signature_matrix_inv_self]`. Then use the resulting hypothesis.
-/
lemma exp_signature_conj (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε := by
  have h := Matrix.exp_conj (Jm ε) A (isUnit_signature_matrix ε)
  rwa [signature_matrix_inv_self] at h

/- English proof (translation)
Conclude with `hA`.
-/
lemma isSelfAdjoint_of_conjTranspose_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) : IsSelfAdjoint A := by
  exact hA

/- English proof (translation)
Establish `h1` using `congrArg CFC.log h`. Use `first`. Consider the case `rwa [CFC.log_exp A (isSelfAdjoint_of_conjTranspose_eq hA), CFC.log_exp B (isSelfAdjoint_of_conjTranspose_eq hB)] at h1`. Consider the case `rwa [CFC.log_exp A, CFC.log_exp B] at h1`.
-/
lemma exp_injective_hermitian {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  have h1 := congrArg CFC.log h
  first
  | rwa [CFC.log_exp A (isSelfAdjoint_of_conjTranspose_eq hA), CFC.log_exp B (isSelfAdjoint_of_conjTranspose_eq hB)] at h1
  | rwa [CFC.log_exp A, CFC.log_exp B] at h1

/- English proof (translation)
Rewrite using `[← Matrix.exp_conjTranspose, hA]`.
-/
lemma exp_conjTranspose_of_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) :
    (NormedSpace.exp A)ᴴ = NormedSpace.exp A := by
  rw [← Matrix.exp_conjTranspose, hA]

/- English proof (translation)
Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl A)), neg_add_cancel]`. Apply the tactic sequence `first | exact Matrix.exp_zero | exact NormedSpace.exp_zero`.
-/
lemma matrix_exp_neg_mul_exp (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl A)), neg_add_cancel]
  first | exact Matrix.exp_zero | exact NormedSpace.exp_zero

/- English proof (translation)
Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel]`. Apply the tactic sequence `first | exact Matrix.exp_zero | exact NormedSpace.exp_zero`.
-/
lemma matrix_exp_mul_exp_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel]
  first | exact Matrix.exp_zero | exact NormedSpace.exp_zero

/- English proof (translation)
The claim follows from `Matrix.exp_add_of_commute _ _ (Commute.refl A)`.
-/
lemma exp_add_self (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (A + A) = NormedSpace.exp A * NormedSpace.exp A := Matrix.exp_add_of_commute _ _ (Commute.refl A)

/- English proof (translation)
Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.add_apply] at h1`. Take the linear combination `(1 / 2 : ℂ) * h1`.
-/
lemma eq_of_add_self_eq_add_self {A B : Matrix (Fin n) (Fin n) ℂ} (h : A + A = B + B) : A = B := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.add_apply] at h1
  linear_combination (1 / 2 : ℂ) * h1

/- English proof (translation)
Introduce `x hx`. Establish `h0 : 0 ≤ x` using `by open scoped MatrixOrder in first`. Consider the case `exact spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx`. Consider the case `exact spectrum_nonneg_of_nonneg hP.nonneg hx`. Establish `hne : x ≠ 0`.

Introduce and unpack `rfl`. Use `first`. Consider the case `exact (spectrum.zero_notMem_iff ℝ).mpr hu hx`. Consider the case `exact (spectrum.zero_not_mem_iff ℝ).mpr hu hx`. Conclude with `lt_of_le_of_ne h0 (Ne.symm hne)`.
-/
lemma spectrum_pos_of_posSemidef_unit {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) (hu : IsUnit P) :
    ∀ x ∈ spectrum ℝ P, 0 < x := by
  intro x hx
  have h0 : 0 ≤ x := by
    open scoped MatrixOrder in
    first
    | exact spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
    | exact spectrum_nonneg_of_nonneg hP.nonneg hx
  have hne : x ≠ 0 := by
    rintro rfl
    first
    | exact (spectrum.zero_notMem_iff ℝ).mpr hu hx
    | exact (spectrum.zero_not_mem_iff ℝ).mpr hu hx
  exact lt_of_le_of_ne h0 (Ne.symm hne)

/- English proof (translation)
Establish `hl : IsSelfAdjoint (CFC.log P)` using `cfc_predicate Real.log P`. Use `Eq.trans (CFC.real_exp_eq_normedSpace_exp hl).symm ?_` and prove the remaining obligations. Unfold `CFC.log`. Rewrite using `[← cfc_comp Real.exp Real.log P hP Real.continuous_exp.continuousOn (Real.continuousOn_log.mono fun x hx => (hs x hx).ne')]`. Use `conv_rhs => rw [← cfc_id ℝ P hP]`.

Conclude with `cfc_congr fun x hx => Real.exp_log (hs x hx)`.
-/
lemma exp_log_of_pos_spectrum {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsSelfAdjoint P)
    (hs : ∀ x ∈ spectrum ℝ P, 0 < x) : NormedSpace.exp (CFC.log P) = P := by
  have hl : IsSelfAdjoint (CFC.log P) := cfc_predicate Real.log P
  refine Eq.trans (CFC.real_exp_eq_normedSpace_exp hl).symm ?_
  unfold CFC.log
  rw [← cfc_comp Real.exp Real.log P hP Real.continuous_exp.continuousOn
    (Real.continuousOn_log.mono fun x hx => (hs x hx).ne')]
  conv_rhs => rw [← cfc_id ℝ P hP]
  exact cfc_congr fun x hx => Real.exp_log (hs x hx)

/- English proof (translation)
Unfold `inUJ at hg`. Establish `h1 : (Jm ε * gᴴ * Jm ε) * g = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : g * (Jm ε * gᴴ * Jm ε) = 1` using `by first`. Consider the case `exact mul_eq_one_comm.mp h1`.

Consider the case `exact (Matrix.mul_eq_one_comm).mp h1`. Consider the case `exact Matrix.mul_eq_one_comm.1 h1`. Use `⟨?_, ⟨⟨g, _, h2, h1⟩, rfl⟩⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]`.

Use `_ = Jm ε := by rw [h2, one_mul]`.
-/
lemma indefinite_unitary_preserves_form {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * Jm ε * gᴴ = Jm ε ∧ IsUnit g := by
  unfold inUJ at hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [mul_assoc]
      _ = 1 := by rw [hg, Jm_mul_Jm_eq_one]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp h1
    | exact (Matrix.mul_eq_one_comm).mp h1
    | exact Matrix.mul_eq_one_comm.1 h1
  refine ⟨?_, ⟨⟨g, _, h2, h1⟩, rfl⟩⟩
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
    _ = Jm ε := by rw [h2, one_mul]

def polarLog (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • CFC.log (gᴴ * g)

/- English proof (translation)
Establish `h1 : IsSelfAdjoint (CFC.log (gᴴ * g))` using `by first`. Consider the case `exact cfc_predicate Real.log (gᴴ * g)`. Consider the case `exact CFC.log_isSelfAdjoint`. Establish `h2 : IsSelfAdjoint ((1 / 2 : ℝ) • CFC.log (gᴴ * g))` using `IsSelfAdjoint.smul (IsSelfAdjoint.all _) h1`. Conclude with `h2`.
-/
lemma polar_log_hermitian (g : Matrix (Fin n) (Fin n) ℂ) : (polarLog g)ᴴ = polarLog g := by
  have h1 : IsSelfAdjoint (CFC.log (gᴴ * g)) := by
    first
    | exact cfc_predicate Real.log (gᴴ * g)
    | exact CFC.log_isSelfAdjoint
  have h2 : IsSelfAdjoint ((1 / 2 : ℝ) • CFC.log (gᴴ * g)) := IsSelfAdjoint.smul (IsSelfAdjoint.all _) h1
  exact h2

/- English proof (translation)
Unfold `polarLog`. Rewrite using `[← add_smul]`. Evaluate the numerical expressions.
-/
lemma polarLog_add_self_eq_log (g : Matrix (Fin n) (Fin n) ℂ) :
    polarLog g + polarLog g = CFC.log (gᴴ * g) := by
  unfold polarLog
  rw [← add_smul]
  norm_num

/- English proof (translation)
Establish `hu : IsUnit g` using `(indefinite_unitary_preserves_form hg).2`. Use `⟨Matrix.isHermitian_conjTranspose_mul_self g, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsUnit.star hu).mul hu`. Conclude with `spectrum_pos_of_posSemidef_unit (Matrix.posSemidef_conjTranspose_mul_self g) ((IsUnit.star hu).mul hu)`.
-/
lemma conjTranspose_mul_self_pos_facts {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g) ∧ ∀ x ∈ spectrum ℝ (gᴴ * g), 0 < x := by
  have hu : IsUnit g := (indefinite_unitary_preserves_form hg).2
  refine ⟨Matrix.isHermitian_conjTranspose_mul_self g, ?_, ?_⟩
  · exact (IsUnit.star hu).mul hu
  · exact spectrum_pos_of_posSemidef_unit (Matrix.posSemidef_conjTranspose_mul_self g) ((IsUnit.star hu).mul hu)

/- English proof (translation)
Rewrite using `[polarLog_add_self_eq_log]`. Take `⟨h1, -, h3⟩` from `conjTranspose_mul_self_pos_facts hg`. Conclude with `exp_log_of_pos_spectrum h1 h3`.
-/
lemma exp_polarLog_double {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    NormedSpace.exp (polarLog g + polarLog g) = gᴴ * g := by
  rw [polarLog_add_self_eq_log]
  obtain ⟨h1, -, h3⟩ := conjTranspose_mul_self_pos_facts hg
  exact exp_log_of_pos_spectrum h1 h3

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma Jm_conjTranspose_eq_self (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `set L := polarLog g with hL`. Establish `hH : Lᴴ = L` using `polar_log_hermitian g`. Establish `hP : NormedSpace.exp (L + L) = gᴴ * g` using `exp_polarLog_double hg`. Establish `hgJ : g * Jm ε * gᴴ = Jm ε` using `(indefinite_unitary_preserves_form hg).1`. Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`.

Establish `hX : (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = Jm ε * (gᴴ * Jm ε * g) := by rw [hgJ]; simp only [mul_assoc]`. Use `_ = 1 := by rw [hg', Jm_mul_Jm_eq_one]`.

Establish `hE : NormedSpace.exp (-(L + L)) = Jm ε * (gᴴ * g) * Jm ε`. Establish `h0 : NormedSpace.exp (-(L + L)) * (gᴴ * g) = 1`. Rewrite using `[← hP]`. Conclude with `matrix_exp_neg_mul_exp _`. Establish `h2 : (gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε) = 1`.

Establish `h1` using `hX`. Use `first`. Consider the case `exact mul_eq_one_comm.mp h1`. Consider the case `exact (Matrix.mul_eq_one_comm).mp h1`. Consider the case `exact Matrix.mul_eq_one_comm.1 h1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hA : (Jm ε * (L + L) * Jm ε)ᴴ = Jm ε * (L + L) * Jm ε`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self, Matrix.conjTranspose_add, hH, mul_assoc]`. Establish `hB : (-(L + L))ᴴ = -(L + L)`. Rewrite using `[Matrix.conjTranspose_neg, Matrix.conjTranspose_add, hH]`.

Establish `hEq : Jm ε * (L + L) * Jm ε = -(L + L)` using `exp_injective_hermitian hA hB (by rw [exp_signature_conj, hP, hE])`. Apply `eq_of_add_self_eq_add_self` to reduce the goal to its premises. Rewrite using `[← neg_add, ← hEq]`. Simplify using `only [mul_add, add_mul]`.
-/
lemma polar_log_anticommutes_signature {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Jm ε * polarLog g * Jm ε = -polarLog g := by
  set L := polarLog g with hL
  have hH : Lᴴ = L := polar_log_hermitian g
  have hP : NormedSpace.exp (L + L) = gᴴ * g := exp_polarLog_double hg
  have hgJ : g * Jm ε * gᴴ = Jm ε := (indefinite_unitary_preserves_form hg).1
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hX : (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = 1 := by
    calc (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = Jm ε * gᴴ * (g * Jm ε * gᴴ) * g := by
          simp only [mul_assoc]
      _ = Jm ε * (gᴴ * Jm ε * g) := by rw [hgJ]; simp only [mul_assoc]
      _ = 1 := by rw [hg', Jm_mul_Jm_eq_one]
  have hE : NormedSpace.exp (-(L + L)) = Jm ε * (gᴴ * g) * Jm ε := by
    have h0 : NormedSpace.exp (-(L + L)) * (gᴴ * g) = 1 := by
      rw [← hP]
      exact matrix_exp_neg_mul_exp _
    have h2 : (gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε) = 1 := by
      have h1 := hX
      first
      | exact mul_eq_one_comm.mp h1
      | exact (Matrix.mul_eq_one_comm).mp h1
      | exact Matrix.mul_eq_one_comm.1 h1
    calc NormedSpace.exp (-(L + L))
        = NormedSpace.exp (-(L + L)) * ((gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε)) := by rw [h2, mul_one]
      _ = Jm ε * (gᴴ * g) * Jm ε := by rw [← mul_assoc, h0, one_mul]
  have hA : (Jm ε * (L + L) * Jm ε)ᴴ = Jm ε * (L + L) * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self, Matrix.conjTranspose_add, hH,
      mul_assoc]
  have hB : (-(L + L))ᴴ = -(L + L) := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_add, hH]
  have hEq : Jm ε * (L + L) * Jm ε = -(L + L) :=
    exp_injective_hermitian hA hB (by rw [exp_signature_conj, hP, hE])
  apply eq_of_add_self_eq_add_self
  rw [← neg_add, ← hEq]
  simp only [mul_add, add_mul]

/- English proof (translation)
Establish `hJ` using `polar_log_anticommutes_signature hg`. Establish `h2 : polarLog g * Jm ε = -(Jm ε * polarLog g)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, Jm_mul_Jm_eq_one, one_mul]`. Use `_ = -(Jm ε * polarLog g) := by rw [hJ, mul_neg]`.

Use `⟨?_, h2⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[polar_log_hermitian, h2, neg_add_cancel]`.
-/
lemma polarLog_mem_hermitian_part {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inP ε (polarLog g) := by
  have hJ := polar_log_anticommutes_signature hg
  have h2 : polarLog g * Jm ε = -(Jm ε * polarLog g) := by
    calc polarLog g * Jm ε = Jm ε * (Jm ε * polarLog g * Jm ε) := by
          rw [← mul_assoc, ← mul_assoc, Jm_mul_Jm_eq_one, one_mul]
      _ = -(Jm ε * polarLog g) := by rw [hJ, mul_neg]
  refine ⟨?_, h2⟩
  unfold inG
  rw [polar_log_hermitian, h2, neg_add_cancel]

/- English proof (translation)
Use `set L := polarLog g with hL`. Establish `hH : Lᴴ = L` using `polar_log_hermitian g`. Establish `hFF : NormedSpace.exp L * NormedSpace.exp L = gᴴ * g`. Rewrite using `[← exp_add_self]`. Conclude with `exp_polarLog_double hg`.

Establish `hEF : NormedSpace.exp (-L) * NormedSpace.exp L = 1` using `matrix_exp_neg_mul_exp L`. Establish `hFE : NormedSpace.exp L * NormedSpace.exp (-L) = 1` using `matrix_exp_mul_exp_neg L`. Establish `hEH : (NormedSpace.exp (-L))ᴴ = NormedSpace.exp (-L)` using `exp_conjTranspose_of_hermitian (by rw [Matrix.conjTranspose_neg, hH])`. Establish `hJE : NormedSpace.exp (-L) = Jm ε * NormedSpace.exp L * Jm ε`. Rewrite using `[← exp_signature_conj, polar_log_anticommutes_signature hg]`.

Establish `hgJ : g * Jm ε * gᴴ = Jm ε` using `(indefinite_unitary_preserves_form hg).1`. Unfold `Kset`. Rewrite using `[Set.mem_setOf_eq]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hEH]`. Simplify using `only [mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[← hFF]`.

Simplify using `only [← mul_assoc]`. Rewrite using `[hEF, one_mul, hFE]`. Establish `h4 : g * Jm ε * (NormedSpace.exp L * NormedSpace.exp L) = Jm ε * g`. Rewrite using `[hFF, ← mul_assoc, hgJ]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hJE]`. Simplify using `only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]`. Use `_ = Jm ε * (g * NormedSpace.exp (-L)) := by`. Rewrite using `[← mul_assoc, ← h4]`. Simplify using `only [mul_assoc]`.

Rewrite using `[hFE, mul_one]`.
-/
lemma mul_exp_neg_polarLog_mem_compact {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * NormedSpace.exp (-polarLog g) ∈ Kset ε := by
  set L := polarLog g with hL
  have hH : Lᴴ = L := polar_log_hermitian g
  have hFF : NormedSpace.exp L * NormedSpace.exp L = gᴴ * g := by
    rw [← exp_add_self]
    exact exp_polarLog_double hg
  have hEF : NormedSpace.exp (-L) * NormedSpace.exp L = 1 := matrix_exp_neg_mul_exp L
  have hFE : NormedSpace.exp L * NormedSpace.exp (-L) = 1 := matrix_exp_mul_exp_neg L
  have hEH : (NormedSpace.exp (-L))ᴴ = NormedSpace.exp (-L) :=
    exp_conjTranspose_of_hermitian (by rw [Matrix.conjTranspose_neg, hH])
  have hJE : NormedSpace.exp (-L) = Jm ε * NormedSpace.exp L * Jm ε := by
    rw [← exp_signature_conj, polar_log_anticommutes_signature hg]
  have hgJ : g * Jm ε * gᴴ = Jm ε := (indefinite_unitary_preserves_form hg).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    calc star (g * NormedSpace.exp (-L)) * (g * NormedSpace.exp (-L))
        = NormedSpace.exp (-L) * (gᴴ * g) * NormedSpace.exp (-L) := by
          rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hEH]
          simp only [mul_assoc]
      _ = 1 := by
          rw [← hFF]
          simp only [← mul_assoc]
          rw [hEF, one_mul, hFE]
  · have h4 : g * Jm ε * (NormedSpace.exp L * NormedSpace.exp L) = Jm ε * g := by
      rw [hFF, ← mul_assoc, hgJ]
    calc g * NormedSpace.exp (-L) * Jm ε = g * Jm ε * NormedSpace.exp L := by
          rw [hJE]
          simp only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
      _ = Jm ε * (g * NormedSpace.exp (-L)) := by
          rw [← mul_assoc, ← h4]
          simp only [mul_assoc]
          rw [hFE, mul_one]

/- English proof (translation)
Rewrite using `[mul_assoc, matrix_exp_neg_mul_exp, mul_one]`.
-/
lemma polar_decomposition_eq {g : Matrix (Fin n) (Fin n) ℂ} :
    g = g * NormedSpace.exp (-polarLog g) * NormedSpace.exp (polarLog g) := by
  rw [mul_assoc, matrix_exp_neg_mul_exp, mul_one]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hX`. Unfold `inG at h1`. Establish `h3 : Xᴴ * Jm ε = X * Jm ε`. Rewrite using `[h2]`. Conclude with `eq_neg_of_add_eq_zero_left h1`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma hermitian_of_mem_hermitian_part {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨h1, h2⟩ := hX
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]
    exact eq_neg_of_add_eq_zero_left h1
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h3]
    _ = X := by rw [mul_assoc, Jm_mul_Jm_eq_one, mul_one]

/- English proof (translation)
Establish `hXh` using `hermitian_of_mem_hermitian_part hX`. Establish `hX'h` using `hermitian_of_mem_hermitian_part hX'`. Establish `hk1 : k ∈ unitaryGroup (Fin n) ℂ`. Unfold `Kset at hk`. Conclude with `hk.1`.

Establish `hk1' : k' ∈ unitaryGroup (Fin n) ℂ`. Unfold `Kset at hk'`. Conclude with `hk'.1`. Establish `hu : star k * k = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk1`. Establish `hu' : star k' * k' = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk1'`.

Establish `key : ∀ (c Y : Matrix (Fin n) (Fin n) ℂ), star c * c = 1 → (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y → (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y)`. Introduce `c Y hc hY`. Rewrite using `[Matrix.conjTranspose_mul, hY, exp_add_self]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.star_eq_conjTranspose]`.

Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [hc, mul_one]`. Establish `h2 : NormedSpace.exp (X + X) = NormedSpace.exp (X' + X')`. Rewrite using `[← key k X hu (exp_conjTranspose_of_hermitian hXh), ← key k' X' hu' (exp_conjTranspose_of_hermitian hX'h), h]`. Establish `hXX : X = X'` using `eq_of_add_self_eq_add_self (exp_injective_hermitian (by rw [Matrix.conjTranspose_add, hXh]) (by rw [Matrix.conjTranspose_add, hX'h]) h2)`.

Substitute `hXX` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, matrix_exp_mul_exp_neg, mul_one]`. Use `_ = k' * NormedSpace.exp X * NormedSpace.exp (-X) := by rw [h]`.

Use `_ = k' := by rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]`.
-/
lemma polar_decomposition_unique {ε : Fin n → Bool} (k k' X X' : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) (hX : inP ε X) (hX' : inP ε X')
    (h : k * NormedSpace.exp X = k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hXh := hermitian_of_mem_hermitian_part hX
  have hX'h := hermitian_of_mem_hermitian_part hX'
  have hk1 : k ∈ unitaryGroup (Fin n) ℂ := by
    unfold Kset at hk
    exact hk.1
  have hk1' : k' ∈ unitaryGroup (Fin n) ℂ := by
    unfold Kset at hk'
    exact hk'.1
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk1
  have hu' : star k' * k' = 1 := Matrix.mem_unitaryGroup_iff'.mp hk1'
  have key : ∀ (c Y : Matrix (Fin n) (Fin n) ℂ), star c * c = 1 →
      (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y →
      (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    intro c Y hc hY
    rw [Matrix.conjTranspose_mul, hY, exp_add_self]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (star c * c) * NormedSpace.exp Y := by
          rw [Matrix.star_eq_conjTranspose]
          simp only [mul_assoc]
      _ = _ := by rw [hc, mul_one]
  have h2 : NormedSpace.exp (X + X) = NormedSpace.exp (X' + X') := by
    rw [← key k X hu (exp_conjTranspose_of_hermitian hXh), ← key k' X' hu' (exp_conjTranspose_of_hermitian hX'h), h]
  have hXX : X = X' := eq_of_add_self_eq_add_self (exp_injective_hermitian (by rw [Matrix.conjTranspose_add, hXh])
    (by rw [Matrix.conjTranspose_add, hX'h]) h2)
  subst hXX
  refine ⟨?_, rfl⟩
  calc k = k * NormedSpace.exp X * NormedSpace.exp (-X) := by
        rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]
    _ = k' * NormedSpace.exp X * NormedSpace.exp (-X) := by rw [h]
    _ = k' := by rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]

/- English proof (translation)
Establish `hc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * g) {g | inUJ ε g}` using `(continuous_star.mul continuous_id).continuousOn`. Establish `hlog : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g}` using `CFC.continuousOn_log.comp hc (fun g hg => by show IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g)`. Conclude with `⟨(conjTranspose_mul_self_pos_facts hg).1, (conjTranspose_mul_self_pos_facts hg).2.1⟩)`. Conclude with `hlog.const_smul (1 / 2 : ℝ)`.
-/
lemma continuousOn_polarLog (ε : Fin n → Bool) : ContinuousOn (polarLog (n := n)) {g | inUJ ε g} := by
  have hc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * g) {g | inUJ ε g} :=
    (continuous_star.mul continuous_id).continuousOn
  have hlog : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} :=
    CFC.continuousOn_log.comp hc (fun g hg => by
      show IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g)
      exact ⟨(conjTranspose_mul_self_pos_facts hg).1, (conjTranspose_mul_self_pos_facts hg).2.1⟩)
  exact hlog.const_smul (1 / 2 : ℝ)

/- English proof (translation)
Introduce `n ε`. Use `⟨fun g hg => ⟨g * NormedSpace.exp (-polarLog g), polarLog g, mul_exp_neg_polarLog_mem_compact hg, polarLog_mem_hermitian_part hg, polar_decomposition_eq⟩, fun k k' X X' hk hk' hX hX' h => polar_decomposition_unique k k' X X' hk hk' hX hX' h, ⟨polarLog, continuousOn_polarLog ε, fu …` and prove the remaining obligations.
-/
theorem polar_decomposition_holds : Polar := by
  intro n ε
  refine ⟨fun g hg => ⟨g * NormedSpace.exp (-polarLog g), polarLog g, mul_exp_neg_polarLog_mem_compact hg,
      polarLog_mem_hermitian_part hg, polar_decomposition_eq⟩,
    fun k k' X X' hk hk' hX hX' h => polar_decomposition_unique k k' X X' hk hk' hX hX' h,
    ⟨polarLog, continuousOn_polarLog ε, fun g hg => ⟨polarLog_mem_hermitian_part hg, mul_exp_neg_polarLog_mem_compact hg⟩⟩⟩

end Formalism.REAL
