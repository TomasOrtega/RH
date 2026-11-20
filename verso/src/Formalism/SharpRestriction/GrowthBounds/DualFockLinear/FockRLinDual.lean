import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockSumRight
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
import Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol)
open Formalism.L2.G.Model.TS

section Contra

variable {S : Type} [Fintype S] [DecidableEq S] {R : Type} [CommRing R] {k : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fock_eq_fockR {τ : Type} (F G : MvPolynomial τ R) : fock F G = fockR F G := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Lin_X (N : S → Matrix (Fin k) (Fin k) R) (v : S × Fin k) :
    Lin N (X v) = ∑ b : Fin k, C (N v.1 v.2 b) * X (v.1, b) := by
  simp [Lin]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Lin_coeff_zero (N : S → Matrix (Fin k) (Fin k) R) (h : MvPolynomial (S × Fin k) R) :
    coeff 0 (Lin N h) = coeff 0 h := by
  have h1 : (MvPolynomial.constantCoeff : MvPolynomial (S × Fin k) R →+* R).comp (Lin N).toRingHom =
      MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro v
      simp [Lin]
  exact congrArg (fun φ : MvPolynomial (S × Fin k) R →+* R => φ h) h1

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Proceed by induction. Treat this case separately.

Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Lin_chain (N : S → Matrix (Fin k) (Fin k) R) (s : S) (b : Fin k) (h : MvPolynomial (S × Fin k) R) :
    pderiv (s, b) (Lin N h) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) h) := by
  have hX : ∀ v : S × Fin k, pderiv (s, b) (Lin N (X v)) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) (X v)) := by
    rintro ⟨t, c⟩
    rw [Lin_X]
    simp only [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, smul_zero, add_zero,
      Pi.single_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases ht : t = s
    · subst ht
      simp [Finset.sum_ite_eq', Finset.sum_ite_eq, MvPolynomial.smul_eq_C_mul]
    · simp [ht]
  induction h using MvPolynomial.induction_on with
  | C r =>
    have h1 : Lin N (C r) = C r := (Lin N).commutes r
    simp [h1]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, hp, hX v]
    simp only [Derivation.leibniz, map_add, map_mul, smul_add, Finset.sum_add_distrib, smul_eq_mul,
      Finset.mul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [MvPolynomial.smul_eq_C_mul]
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [MvPolynomial.smul_eq_C_mul]
      ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities.
-/
theorem fockR_Lin (N : S → Matrix (Fin k) (Fin k) R) (P : MvPolynomial (S × Fin k) R) :
    ∀ Q : MvPolynomial (S × Fin k) R, fockR (Lin N P) Q = fockR P (Lin (fun s => (N s).transpose) Q) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : Lin N (C a : MvPolynomial (S × Fin k) R) = C a := by simp [Lin]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, Lin_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add, tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, Lin_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, Lin_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : Lin N p * (C (N v.1 v.2 b) * X (v.1, b)) = N v.1 v.2 b • (Lin N p * X (v.1, b)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem fockR_Lin_dual (A B : S → Matrix (Fin k) (Fin k) R) (h : ∀ s, B s * (A s).transpose = 1)
    (P Q : MvPolynomial (S × Fin k) R) : fockR (Lin A P) (Lin B Q) = fockR P Q := by
  rw [fockR_Lin, Lin_comp]
  simp only [h]
  rw [Lin_one]

end Contra

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Aa_dual {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose)⁻¹ * (Aa vec M⁻¹).transpose = 1 := by
  have h1 : IsUnit (M⁻¹).det := Matrix.isUnit_nonsing_inv_det M hM
  have h2 : IsUnit ((M⁻¹).transpose).det := by rwa [Matrix.det_transpose]
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [Matrix.nonsing_inv_nonsing_inv _ h2, Matrix.transpose_transpose, Matrix.transpose_transpose,
      Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.nonsing_inv_mul _ hM]
  · simp only [Aa, if_true]
    exact Matrix.nonsing_inv_mul _ h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem multDiv_kapFl (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) {n' k : ℕ} (d : Fin n' → ℕ) :
    MultDiv O p (kapFl p k d) (k := k) d := by
  intro α hα

  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  set Mn : ℕ := ∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) with hMn
  have h3 : (∏ s, (d s).factorial) = Mn * expFact α := by
    rw [h2, hMn, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : Mn ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have h4 : padicValNat p Mn ≤ kapFl p k d := by
    rw [hMn, Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    unfold kapFl
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin k => α (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin k, α (s, c) = d s := hα s
    rw [e] at this
    exact this

  have hdv : p ^ padicValNat p Mn ∣ Mn := pow_padicValNat_dvd
  have hnd : ¬ p ^ (padicValNat p Mn + 1) ∣ Mn := pow_succ_padicValNat_not_dvd hMn0
  generalize padicValNat p Mn = v at h4 hdv hnd
  obtain ⟨u, hu⟩ := hdv
  have hpu : ¬ p ∣ u := by
    intro hd
    apply hnd
    rw [hu, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have huO : IsUnit ((u : ℕ) : O) := by
    have hco : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpu).symm
    by_contra hnu
    have hm : ((u : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hb := Nat.gcd_eq_gcd_ab u p
    rw [hco] at hb
    have h5 : (1 : O) = (u : O) * ((Nat.gcdA u p : ℤ) : O) + (p : O) * ((Nat.gcdB u p : ℤ) : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hb
      push_cast at this
      exact this
    have h6 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hpO)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h6)
  obtain ⟨uu, huu⟩ := huO
  refine ⟨(p : O) ^ (kapFl p k d - v) * (↑uu⁻¹ : O), ?_⟩
  rw [h3, hu]
  push_cast
  rw [← huu]
  have e1 : (p : O) ^ kapFl p k d = (p : O) ^ v * (p : O) ^ (kapFl p k d - v) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1]
  have e2 : (uu : O) * (↑uu⁻¹ : O) = 1 := Units.mul_inv uu
  linear_combination (-(p : O) ^ v * (p : O) ^ (kapFl p k d - v) * (expFact α : O)) * e2

end Formalism.MainNotions.TestSideCounting
