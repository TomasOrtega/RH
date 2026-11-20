import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ExpandKer

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

/- English proof (translation)
Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = ((i + j).choose i : A.Acr 1) * A.dxi 1 (i + j) := by
  obtain ⟨-, hmul, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  change A.mkAcr 1 (A.dxi0 i) * A.mkAcr 1 (A.dxi0 j)
    = ((i + j).choose i : A.Acr 1) * A.mkAcr 1 (A.dxi0 (i + j))
  rw [← map_mul, hmul, map_mul, map_natCast]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  obtain ⟨-, -, hfac, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  have h1 : A.dxi0 1 = algebraMap A.W A.Acr0 A.xi := by
    simpa using hfac 1
  have h2 : A.dxi 1 1 = A.toAcr 1 A.xi := by
    change A.mkAcr 1 (A.dxi0 1) = A.mkAcr 1 (algebraMap A.W A.Acr0 A.xi)
    rw [h1]
  rw [h2, ← A.aTo1_coeff, A.xi_coeff_zero, map_neg, neg_neg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem toAcr_teichmuller (b : A.A) : A.toAcr 1 (WittVector.teichmuller l b) = A.aTo1 b := by
  rw [← A.aTo1_coeff, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_coprime {m : ℕ} (hm : l ∣ m) {j : ℕ} (hj : j < l) :
    ∃ c : ℕ, c.Coprime l ∧ A.dxi 1 1 ^ j * A.dxi 1 m = (c : A.Acr 1) * A.dxi 1 (m + j) := by
  have hp : l.Prime := Fact.out
  induction j with
  | zero => exact ⟨1, Nat.coprime_one_left l, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc, hcj⟩ := ih (Nat.lt_of_succ_lt hj)
    have hnd : ¬ l ∣ m + j + 1 := by
      intro h
      have h2 : l ∣ j + 1 := by
        rw [Nat.add_assoc] at h
        exact (Nat.dvd_add_right hm).mp h
      have := Nat.le_of_dvd (Nat.succ_pos j) h2
      omega
    refine ⟨c * (m + j + 1), Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm, ?_⟩
    rw [pow_succ', mul_assoc, hcj, mul_left_comm, dxi_mul A 1 (m + j), Nat.choose_one_right]
    have e : 1 + (m + j) = m + (j + 1) := by omega
    rw [e]
    push_cast
    ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_of_coprime_mul {I : Ideal (A.Acr 1)} {c : ℕ} (hc : c.Coprime l) {x : A.Acr 1}
    (h : (c : A.Acr 1) * x ∈ I) : x ∈ I := by
  have hl : ((l : ℕ) : A.Acr 1) = 0 := by
    have e : ((l : ℕ) : A.Acr 1) = A.toAcr 1 (l : A.W) := by rw [map_natCast]
    rw [e]
    change Ideal.Quotient.mk _ (algebraMap A.W A.Acr0 (l : A.W)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.subset_span (by simp)
  have h1 : (1 : A.Acr 1) = (c : A.Acr 1) * (Nat.gcdA c l : A.Acr 1)
      + (l : A.Acr 1) * (Nat.gcdB c l : A.Acr 1) := by
    have h' := Nat.gcd_eq_gcd_ab c l
    rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at h'
    have h'' := congrArg (fun z : ℤ => (z : A.Acr 1)) h'
    push_cast at h''
    exact h''
  have hx : x = (Nat.gcdA c l : A.Acr 1) * ((c : A.Acr 1) * x) := by
    calc x = (1 : A.Acr 1) * x := (one_mul x).symm
      _ = _ := by rw [h1, hl]; ring
  rw [hx]
  exact I.mul_mem_left _ h

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem inner_step (k : ℕ) {j : ℕ} (hj : j < l) (b : A.A)
    (h : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1)) :
    b ∈ Ideal.span {A.pi} := by
  obtain ⟨c, hc, hcj⟩ := exists_coprime A (dvd_mul_right l k) hj
  have hx : A.aTo1 b * A.dxi 1 (l * k + j) ∈ A.Fil 1 (l * k + j + 1) := by
    have e : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k)
        = (c : A.Acr 1) * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j))) := by
      rw [map_mul, map_pow, aTo1_pi A]
      calc (-A.dxi 1 1) ^ j * A.aTo1 b * A.dxi 1 (l * k)
          = (-1) ^ j * A.aTo1 b * (A.dxi 1 1 ^ j * A.dxi 1 (l * k)) := by ring
        _ = _ := by rw [hcj]; ring
    rw [e] at h
    have h2 := mem_of_coprime_mul A hc h
    have h3 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        ∈ A.Fil 1 (l * k + j + 1) := Ideal.mul_mem_left _ _ h2
    have h4 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        = A.aTo1 b * A.dxi 1 (l * k + j) := by
      rw [← mul_assoc, ← mul_pow]
      simp
    rwa [h4] at h3
  rw [← toAcr_teichmuller A b] at hx
  have hth := ((GlobalTheory.T.graded_filtration_generated_by_dividedXi A 1 (l * k + j)).2 (WittVector.teichmuller l b)).mp hx
  have hz : A.aToU1 b = 0 := by
    have e := A.sharpMap_coeff (WittVector.teichmuller l b)
    rw [WittVector.teichmuller_coeff_zero] at e
    rw [e, Ideal.Quotient.eq_zero_iff_mem]
    exact hth
  obtain ⟨-, hker⟩ := GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A
  rw [← hker]
  exact RingHom.mem_ker.mpr hz

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem term_eq_zero {a : A.A} (h : a ∈ Ideal.span {A.pi ^ l}) (m : ℕ) :
    A.aTo1 a * A.dxi 1 m = 0 := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.expansion_surjective_additive_linear A
  rw [map_mul, mul_assoc, h4, mul_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem term_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) :
    A.aTo1 (c k) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + l) := by
  obtain ⟨-, hadd, -, -⟩ := GlobalTheory.T.expansion_surjective_additive_linear A
  obtain ⟨-, -, -, -, hmap, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  have hdx : ∀ m, A.dxi 1 m ∈ A.Fil 1 m := fun m => by
    rw [hmap]
    change A.mkAcr 1 (A.dxi0 m) ∈ _
    apply Ideal.mem_map_of_mem
    unfold CrystallineSemistableComparison.PAlg.Fil0
    exact Ideal.subset_span ⟨m, le_rfl, rfl⟩
  have hanti : ∀ r s : ℕ, r ≤ s → A.Fil 1 s ≤ A.Fil 1 r := by
    intro r s hrs
    rw [hmap, hmap]
    apply Ideal.map_mono
    unfold CrystallineSemistableComparison.PAlg.Fil0
    apply Ideal.span_mono
    rintro z ⟨i, hi, rfl⟩
    exact ⟨i, le_trans hrs hi, rfl⟩
  have hsingle : A.expand (Finsupp.single k (c k)) = A.aTo1 (c k) * A.dxi 1 (l * k) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum_single_index]
    simp
  have herase : A.expand (c.erase k) ∈ A.Fil 1 (l * k + l) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Ideal.sum_mem
    intro i hi
    have hik : i ≠ k := by
      rintro rfl
      simp at hi
    rw [Finsupp.erase_ne hik]
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · rw [term_eq_zero A (hk i hlt)]
      exact Ideal.zero_mem _
    · apply Ideal.mul_mem_left
      refine hanti _ _ ?_ (hdx (l * i))
      calc l * k + l = l * (k + 1) := by ring
        _ ≤ l * i := Nat.mul_le_mul (le_refl l) hgt
  have hsplit := hadd (Finsupp.single k (c k)) (c.erase k)
  rw [Finsupp.single_add_erase, h0, hsingle] at hsplit
  have e : A.aTo1 (c k) * A.dxi 1 (l * k) = -A.expand (c.erase k) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hsplit.symm
  rw [e]
  exact (Ideal.neg_mem_iff _).mpr herase

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem fil_anti {r s : ℕ} (h : r ≤ s) : A.Fil 1 s ≤ A.Fil 1 r := by
  obtain ⟨-, -, -, -, hmap, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  rw [hmap, hmap]
  apply Ideal.map_mono
  unfold CrystallineSemistableComparison.PAlg.Fil0
  apply Ideal.span_mono
  rintro z ⟨i, hi, rfl⟩
  exact ⟨i, le_trans h hi, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) : c k ∈ Ideal.span {A.pi ^ l} := by
  have hT := term_mem A c h0 k hk
  have key : ∀ j, j ≤ l → c k ∈ Ideal.span {A.pi ^ j} := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ih (Nat.le_of_succ_le hj))
      have h1 : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1) := by
        rw [mul_comm (A.pi ^ j) b, hb]
        exact fil_anti A (by omega) hT
      obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp (inner_step A k (Nat.lt_of_succ_le hj) b h1)
      rw [← hb, ← hb', pow_succ]
      exact Ideal.mem_span_singleton'.mpr ⟨b', by ring⟩
  exact key l le_rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem expand_eq_zero_iff : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A),
    A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  intro l _ A c
  constructor
  · intro h0 k
    refine Nat.strong_induction_on k ?_
    intro k ih
    exact coeff_mem A c h0 k ih
  · intro h
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro i _
    exact term_eq_zero A (h i) _

end GlobalTheory.CompanionTheory.ExpandKer
