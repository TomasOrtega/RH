import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodRing

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hc : ∀ n : ℕ, 0 < n → n < 5 → (n : k) ≠ 0`. Introduce `n h0 h5`. Use `interval_cases n`.

Simplify using the standard rewrite rules. Simplify using `using h2`. Simplify using `using h3`. Establish `: ((4 : ℕ) : k) = 2 * 2` using `by norm_num`. Rewrite using `[this]`.

Conclude with `mul_ne_zero h2 h2`. Establish `hinj : Function.Injective (fun i : Fin 5 => ((i : ℕ) : k))`. Establish `key : ∀ i j : ℕ, i < j → j < 5 → (i : k) ≠ j`. Introduce `i j hij hj h`. Apply `hc (j - i) (by omega) (by omega)` to reduce the goal to its premises.

Rewrite using `[Nat.cast_sub hij.le, h, sub_self]`. Introduce `i j h`. Simplify using `only at h`. Break down `lt_trichotomy (i : ℕ) (j : ℕ) with hl | hl | hl` into its components or cases. Conclude with `absurd h (key _ _ hl j.2)`.

Conclude with `Fin.ext hl`. Conclude with `absurd h.symm (key _ _ hl i.2)`. Set `Q1 : Polynomial k` to `1 - Polynomial.C D * Polynomial.X ^ 2`. Set `Q2 : Polynomial k` to `Polynomial.C A + Polynomial.C B * Polynomial.X + Polynomial.C C * Polynomial.X ^ 2`. Establish `hQ1 : Q1 ≠ 0`.

Introduce `h`. Use `congrArg (fun p => Polynomial.coeff p 0) h` as an intermediate fact. Simplify using `[Q1, Polynomial.coeff_one, Polynomial.coeff_X_pow] at this`. Establish `hQ2 : Q2 ≠ 0`. Introduce `h`.

Establish `e0` using `congrArg (fun p => Polynomial.coeff p 0) h`. Establish `e1` using `congrArg (fun p => Polynomial.coeff p 1) h`. Establish `e2` using `congrArg (fun p => Polynomial.coeff p 2) h`. Simplify using `[Q2, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at e0 e1 e2`. Break down `hne with h' | h' | h'` into its components or cases.

Conclude with `h' e0`. Conclude with `h' e1`. Conclude with `h' e2`. Establish `hdeg : (Q1 * Q2).natDegree ≤ 4`. Simplify using `only [Q1, Q2]`.

Use `compute_degree`. Establish `hz : Q1 * Q2 = 0`. Apply `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj` to reduce the goal to its premises. Introduce `i`. Simplify using `only [Polynomial.eval_mul]`.

Distinguish the cases in `h : 1 - D * (((i : ℕ) : k)) ^ 2 = 0`. Establish `: Polynomial.eval (((i : ℕ) : k)) Q1 = 0` using `by simpa [Q1] using h`. Rewrite using `[this, zero_mul]`. Use `hcon i h` as an intermediate fact. Establish `h' : Polynomial.eval (((i : ℕ) : k)) Q2 = 0` using `by simpa [Q2] using this`.

Rewrite using `[h', mul_zero]`. Simplify using `using Nat.lt_succ_of_le hdeg`. Conclude with `(mul_ne_zero hQ1 hQ2) hz`.
-/
theorem exists_good_nat {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (D A B C : k)
    (hne : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ a : ℕ, 1 - D * (a : k) ^ 2 ≠ 0 ∧ A + B * (a : k) + C * (a : k) ^ 2 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hc : ∀ n : ℕ, 0 < n → n < 5 → (n : k) ≠ 0 := by
    intro n h0 h5
    interval_cases n
    · simp
    · simpa using h2
    · simpa using h3
    · have : ((4 : ℕ) : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
  have hinj : Function.Injective (fun i : Fin 5 => ((i : ℕ) : k)) := by
    have key : ∀ i j : ℕ, i < j → j < 5 → (i : k) ≠ j := by
      intro i j hij hj h
      apply hc (j - i) (by omega) (by omega)
      rw [Nat.cast_sub hij.le, h, sub_self]
    intro i j h
    simp only at h
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hl | hl | hl
    · exact absurd h (key _ _ hl j.2)
    · exact Fin.ext hl
    · exact absurd h.symm (key _ _ hl i.2)
  let Q1 : Polynomial k := 1 - Polynomial.C D * Polynomial.X ^ 2
  let Q2 : Polynomial k :=
    Polynomial.C A + Polynomial.C B * Polynomial.X + Polynomial.C C * Polynomial.X ^ 2
  have hQ1 : Q1 ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simp [Q1, Polynomial.coeff_one, Polynomial.coeff_X_pow] at this
  have hQ2 : Q2 ≠ 0 := by
    intro h
    have e0 := congrArg (fun p => Polynomial.coeff p 0) h
    have e1 := congrArg (fun p => Polynomial.coeff p 1) h
    have e2 := congrArg (fun p => Polynomial.coeff p 2) h
    simp [Q2, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at e0 e1 e2
    rcases hne with h' | h' | h'
    · exact h' e0
    · exact h' e1
    · exact h' e2
  have hdeg : (Q1 * Q2).natDegree ≤ 4 := by
    simp only [Q1, Q2]
    compute_degree
  have hz : Q1 * Q2 = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
    · intro i
      simp only [Polynomial.eval_mul]
      by_cases h : 1 - D * (((i : ℕ) : k)) ^ 2 = 0
      · have : Polynomial.eval (((i : ℕ) : k)) Q1 = 0 := by simpa [Q1] using h
        rw [this, zero_mul]
      · have := hcon i h
        have h' : Polynomial.eval (((i : ℕ) : k)) Q2 = 0 := by simpa [Q2] using this
        rw [h', mul_zero]
    · simpa using Nat.lt_succ_of_le hdeg
  exact (mul_ne_zero hQ1 hQ2) hz

section Quad

variable {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) (τ : O →+* O) (δ : O) (D : R)

include ι in

/- English proof (translation)
Use `letI : Algebra R O := ι.toAlgebra`. Use `haveI : Module.Finite R O := by`. Use `⟨⟨{1, δ}, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.eq_top_iff']`. Introduce `y`.

Take `⟨p, q, rfl⟩` from `hsp y`. Establish `e1 : ι p = p • (1 : O)`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Establish `e2 : ι q * δ = q • δ`.

Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))`. Conclude with `finite_maximalSpectrum_of_finite R O`.
-/
theorem finite_maxSpec [IsLocalRing R] (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) :
    Finite (MaximalSpectrum O) := by
  classical
  letI : Algebra R O := ι.toAlgebra
  haveI : Module.Finite R O := by
    refine ⟨⟨{1, δ}, ?_⟩⟩
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨p, q, rfl⟩ := hsp y
    have e1 : ι p = p • (1 : O) := by
      rw [Algebra.smul_def, mul_one]; rfl
    have e2 : ι q * δ = q • δ := by
      rw [Algebra.smul_def]; rfl
    rw [e1, e2]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  exact finite_maximalSpectrum_of_finite R O

/- English proof (translation)
Simplify using `only [map_add, map_mul, hτι, hτδ, map_sub, map_pow]`. Take the linear combination `(-(ι q) ^ 2) * hδ`.
-/
theorem norm_eq (hδ : δ * δ = ι D) (hτι : ∀ r, τ (ι r) = ι r) (hτδ : τ δ = -δ) (p q : R) :
    (ι p + ι q * δ) * τ (ι p + ι q * δ) = ι (p ^ 2 - D * q ^ 2) := by
  simp only [map_add, map_mul, hτι, hτδ, map_sub, map_pow]
  linear_combination (-(ι q) ^ 2) * hδ

/- English proof (translation)
Take `⟨p, q, rfl⟩` from `hsp β`. Establish `hq : q = 0`. Establish `h` using `hinj 0 (2 * q) (by`. Use `hτβ` as an intermediate fact. Simplify using `only [map_add, map_mul, hτι, hτδ] at this`.

Simplify using `only [map_zero, map_mul, map_ofNat]`. Take the linear combination `-this)`. Conclude with `(h2.mul_right_eq_zero).1 h.2`. Substitute `hq` using the available equality. Simplify using `only [map_zero, zero_mul, add_zero] at hβ ⊢`.

Use `⟨p, ?_, rfl⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hβ.exists_right_inv`. Take `⟨c, e, rfl⟩` from `hsp w`. Establish `h` using `hinj (p * c - 1) (p * e) (by`. Simplify using `only [map_sub, map_mul, map_one]`.

Take the linear combination `hw)`. Conclude with `IsUnit.of_mul_eq_one c (sub_eq_zero.1 h.1)`.
-/
theorem fixed_unit (hτι : ∀ r, τ (ι r) = ι r) (hτδ : τ δ = -δ)
    (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hinj : ∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) (h2 : IsUnit (2 : R))
    (β : O) (hβ : IsUnit β) (hτβ : τ β = β) : ∃ b : R, IsUnit b ∧ β = ι b := by
  obtain ⟨p, q, rfl⟩ := hsp β
  have hq : q = 0 := by
    have h := hinj 0 (2 * q) (by
      have := hτβ
      simp only [map_add, map_mul, hτι, hτδ] at this
      simp only [map_zero, map_mul, map_ofNat]
      linear_combination -this)
    exact (h2.mul_right_eq_zero).1 h.2
  subst hq
  simp only [map_zero, zero_mul, add_zero] at hβ ⊢
  refine ⟨p, ?_, rfl⟩
  obtain ⟨w, hw⟩ := hβ.exists_right_inv
  obtain ⟨c, e, rfl⟩ := hsp w
  have h := hinj (p * c - 1) (p * e) (by
    simp only [map_sub, map_mul, map_one]
    linear_combination hw)
  exact IsUnit.of_mul_eq_one c (sub_eq_zero.1 h.1)

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `fixed_unit ι τ δ hτι hτδ hsp hinj h2 β hβ hτβ`. Take `⟨s0, s1, rfl⟩` from `hsp s`. Set `φ` to `IsLocalRing.residue R`. Establish `nz : ∀ {x : R}, IsUnit x → φ x ≠ 0` using `fun hx => (hx.map φ).ne_zero`. Establish `un : ∀ {x : R}, φ x ≠ 0 → IsUnit x` using `fun {x} hx => by`.

Assume the negation of the conclusion as `h`. Conclude with `hx ((IsLocalRing.residue_eq_zero_iff x).2 h)`. Establish `h2k : (2 : IsLocalRing.ResidueField R) ≠ 0`. Use `nz h2` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `h3k : (3 : IsLocalRing.ResidueField R) ≠ 0`. Use `nz h3` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `hDk` using `nz hD`. Establish `hbk` using `nz hb`.

Take `⟨a, ha1, ha2⟩` from `exists_good_nat h2k h3k (φ D) ((φ b - φ s0) ^ 2 - φ D * φ s1 ^ 2) (4 * φ D * φ b * φ s1) (φ D ^ 2 * φ s1 ^ 2 - φ D * (φ b + φ s0) ^ 2) (by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨hA, hB, hC⟩` from `hcon`. Establish `h4 : (4 : IsLocalRing.ResidueField R) ≠ 0`.

Establish `: (4 : IsLocalRing.ResidueField R) = 2 * 2` using `by norm_num`. Rewrite using `[this]`. Conclude with `mul_ne_zero h2k h2k`. Establish `hs1 : φ s1 = 0`. Use `mul_ne_zero (mul_ne_zero h4 hDk) hbk` as an intermediate fact.

Conclude with `(mul_eq_zero.1 hB).resolve_left this`. Rewrite `hA`, `hC` using `[hs1]`. Establish `e1 : φ b - φ s0 = 0`. Establish `: (φ b - φ s0) ^ 2 = 0` using `by simpa using hA`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 this`.

Establish `e2 : φ b + φ s0 = 0`. Establish `: φ D * (φ b + φ s0) ^ 2 = 0` using `by simpa using hC`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 this).resolve_left hDk)`. Establish `: 2 * φ b = 0` using `by linear_combination e1 + e2`. Conclude with `(mul_ne_zero h2k hbk) this)`.

Use `set c : R := (a : R) with hc`. Establish `hφc : φ c = (a : IsLocalRing.ResidueField R)` using `by simp [hc]`. Set `P : R` to `b - s0 + c * s1 * D`. Set `Q : R` to `b * c - s1 + c * s0`. Establish `hn1 : IsUnit (1 - D * c ^ 2)` using `un (by`.

Simplify using `only [map_sub, map_one, map_mul, map_pow, hφc]`. Conclude with `ha1)`. Establish `hn2 : IsUnit (P ^ 2 - D * Q ^ 2)` using `un (by`. Establish `: φ (P ^ 2 - D * Q ^ 2) = (φ b - φ s0) ^ 2 - φ D * φ s1 ^ 2 + 4 * φ D * φ b * φ s1 * (a : IsLocalRing.ResidueField R) + (φ D ^ 2 * φ s1 ^ 2 - φ D * (φ b + φ s0) ^ 2) * (a : IsLocalRing.ResidueField R) ^ 2`. Simplify using `only [P, Q, map_sub, map_add, map_mul, map_pow, hφc]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `ha2)`. Take `⟨e1, he1⟩` from `hn1.exists_right_inv`. Take `⟨e2, he2⟩` from `hn2.exists_right_inv`.

Establish `he1' : ι (1 - D * c ^ 2) * ι e1 = 1` using `by rw [← map_mul, he1, map_one]`. Establish `he2' : ι (P ^ 2 - D * Q ^ 2) * ι e2 = 1` using `by rw [← map_mul, he2, map_one]`. Set `u : O` to `ι 1 + ι c * δ`. Establish `hτu : τ u = 1 - ι c * δ`. Simplify using `only [u, map_add, map_mul, hτι, hτδ, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Establish `huu : u * τ u = ι (1 - D * c ^ 2)`. Use `norm_eq ι τ δ D hδ hτι hτδ 1 c` as an intermediate fact. Simplify `this` using `[u, one_pow]`. Set `t : O` to `ι P + ι Q * δ`.

Establish `htt : t * τ t = ι (P ^ 2 - D * Q ^ 2)` using `norm_eq ι τ δ D hδ hτι hτδ P Q`. Establish `ht : ι b * u - τ u * (ι s0 + ι s1 * δ) = t`. Rewrite using `[hτu]`. Simplify using `only [t, u, P, Q, map_add, map_sub, map_mul, map_one]`. Take the linear combination `(ι c * ι s1) * hδ`.

Use `⟨u * u * ι e1, u * τ t * ι e2, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, hτι]`. Combine the equalities or inequalities in the displayed calculation. Establish `hτε : τ (u * u * ι e1) * u = τ u`. Simplify using `only [map_mul, hτι]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_eps [IsLocalRing R] (hδ : δ * δ = ι D) (hτι : ∀ r, τ (ι r) = ι r) (hτδ : τ δ = -δ)
    (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hinj : ∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0)
    (hD : IsUnit D) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (s β : O) (hβ : IsUnit β) (hτβ : τ β = β) :
    ∃ ε z : O, ε * τ ε = 1 ∧ (β - τ ε * s) * z = 1 := by
  obtain ⟨b, hb, rfl⟩ := fixed_unit ι τ δ hτι hτδ hsp hinj h2 β hβ hτβ
  obtain ⟨s0, s1, rfl⟩ := hsp s
  let φ := IsLocalRing.residue R
  have nz : ∀ {x : R}, IsUnit x → φ x ≠ 0 := fun hx => (hx.map φ).ne_zero
  have un : ∀ {x : R}, φ x ≠ 0 → IsUnit x := fun {x} hx => by
    by_contra h
    exact hx ((IsLocalRing.residue_eq_zero_iff x).2 h)
  have h2k : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := nz h2
    rwa [map_ofNat] at this
  have h3k : (3 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := nz h3
    rwa [map_ofNat] at this
  have hDk := nz hD
  have hbk := nz hb
  obtain ⟨a, ha1, ha2⟩ := exists_good_nat h2k h3k (φ D) ((φ b - φ s0) ^ 2 - φ D * φ s1 ^ 2)
    (4 * φ D * φ b * φ s1) (φ D ^ 2 * φ s1 ^ 2 - φ D * (φ b + φ s0) ^ 2) (by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hA, hB, hC⟩ := hcon
      have h4 : (4 : IsLocalRing.ResidueField R) ≠ 0 := by
        have : (4 : IsLocalRing.ResidueField R) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2k h2k
      have hs1 : φ s1 = 0 := by
        have := mul_ne_zero (mul_ne_zero h4 hDk) hbk
        exact (mul_eq_zero.1 hB).resolve_left this
      rw [hs1] at hA hC
      have e1 : φ b - φ s0 = 0 := by
        have : (φ b - φ s0) ^ 2 = 0 := by simpa using hA
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have e2 : φ b + φ s0 = 0 := by
        have : φ D * (φ b + φ s0) ^ 2 = 0 := by simpa using hC
        exact pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 this).resolve_left hDk)
      have : 2 * φ b = 0 := by linear_combination e1 + e2
      exact (mul_ne_zero h2k hbk) this)
  set c : R := (a : R) with hc
  have hφc : φ c = (a : IsLocalRing.ResidueField R) := by simp [hc]
  let P : R := b - s0 + c * s1 * D
  let Q : R := b * c - s1 + c * s0
  have hn1 : IsUnit (1 - D * c ^ 2) := un (by
    simp only [map_sub, map_one, map_mul, map_pow, hφc]; exact ha1)
  have hn2 : IsUnit (P ^ 2 - D * Q ^ 2) := un (by
    have : φ (P ^ 2 - D * Q ^ 2) = (φ b - φ s0) ^ 2 - φ D * φ s1 ^ 2 +
        4 * φ D * φ b * φ s1 * (a : IsLocalRing.ResidueField R) +
        (φ D ^ 2 * φ s1 ^ 2 - φ D * (φ b + φ s0) ^ 2) * (a : IsLocalRing.ResidueField R) ^ 2 := by
      simp only [P, Q, map_sub, map_add, map_mul, map_pow, hφc]
      ring
    rw [this]; exact ha2)
  obtain ⟨e1, he1⟩ := hn1.exists_right_inv
  obtain ⟨e2, he2⟩ := hn2.exists_right_inv
  have he1' : ι (1 - D * c ^ 2) * ι e1 = 1 := by rw [← map_mul, he1, map_one]
  have he2' : ι (P ^ 2 - D * Q ^ 2) * ι e2 = 1 := by rw [← map_mul, he2, map_one]
  let u : O := ι 1 + ι c * δ
  have hτu : τ u = 1 - ι c * δ := by
    simp only [u, map_add, map_mul, hτι, hτδ, map_one]; ring
  have huu : u * τ u = ι (1 - D * c ^ 2) := by
    have := norm_eq ι τ δ D hδ hτι hτδ 1 c
    simpa [u, one_pow] using this
  let t : O := ι P + ι Q * δ
  have htt : t * τ t = ι (P ^ 2 - D * Q ^ 2) := norm_eq ι τ δ D hδ hτι hτδ P Q
  have ht : ι b * u - τ u * (ι s0 + ι s1 * δ) = t := by
    rw [hτu]
    simp only [t, u, P, Q, map_add, map_sub, map_mul, map_one]
    linear_combination (ι c * ι s1) * hδ
  refine ⟨u * u * ι e1, u * τ t * ι e2, ?_, ?_⟩
  · simp only [map_mul, hτι]
    calc u * u * ι e1 * (τ u * τ u * ι e1) = (u * τ u * ι e1) ^ 2 := by ring
      _ = 1 := by rw [huu, he1', one_pow]
  · have hτε : τ (u * u * ι e1) * u = τ u := by
      simp only [map_mul, hτι]
      calc τ u * τ u * ι e1 * u = τ u * (u * τ u * ι e1) := by ring
        _ = τ u := by rw [huu, he1', mul_one]
    calc (ι b - τ (u * u * ι e1) * (ι s0 + ι s1 * δ)) * (u * τ t * ι e2)
        = (ι b * u - (τ (u * u * ι e1) * u) * (ι s0 + ι s1 * δ)) * τ t * ι e2 := by ring
      _ = t * τ t * ι e2 := by rw [hτε, ht]
      _ = 1 := by rw [htt, he2']

end Quad

section Lattice

variable {K A : Type} [Field K] [CommRing A] [Algebra K A] (R : Subring K)

/- English proof (translation)
Rewrite using `[← P.sum_repr y, map_sum, Finsupp.finset_sum_apply]`. Use `R.sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `R.mul_mem (hy i) (hPQ i l)`.
-/
theorem coord_mem {ι₁ ι₂ : Type} [Fintype ι₁] (P : Module.Basis ι₁ K A) (Q : Module.Basis ι₂ K A)
    (hPQ : ∀ i l, Q.repr (P i) l ∈ R) (y : A) (hy : ∀ i, P.repr y i ∈ R) (l : ι₂) :
    Q.repr y l ∈ R := by
  rw [← P.sum_repr y, map_sum, Finsupp.finset_sum_apply]
  refine R.sum_mem fun i _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact R.mul_mem (hy i) (hPQ i l)

/- English proof (translation)
Establish `e : algebraMap K A p + algebraMap K A q * B 1 = p • B 0 + q • B 1`. Rewrite using `[hB0, Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem coord_two (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (p q : K) :
    B.repr (algebraMap K A p + algebraMap K A q * B 1) 0 = p ∧
      B.repr (algebraMap K A p + algebraMap K A q * B 1) 1 = q := by
  have e : algebraMap K A p + algebraMap K A q * B 1 = p • B 0 + q • B 1 := by
    rw [hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [e]
  simp

/- English proof (translation)
Use `conv_lhs => rw [← B.sum_repr y]`. Rewrite using `[Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]`.
-/
theorem eq_coord (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (y : A) :
    y = algebraMap K A (B.repr y 0) + algebraMap K A (B.repr y 1) * B 1 := by
  conv_lhs => rw [← B.sum_repr y]
  rw [Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]

/- English proof (translation)
Set `O : Subring A` to `{ carrier := {y | ∀ j, B.repr y j ∈ R} zero_mem' := by intro j; simp [R.zero_mem] one_mem' := by`. Establish `h` using `coord_two B hB0 1 0`. Simplify using `only [map_one, map_zero, zero_mul, add_zero] at h`. Use `show ∀ j, B.repr 1 j ∈ R`. Use `Fin.forall_fin_two.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h.1]`. Conclude with `R.one_mem`. Rewrite using `[h.2]`. Conclude with `R.zero_mem`. Use the proof step `add_mem' := by`.

Introduce `a b ha hb j`. Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `R.add_mem (ha j) (hb j)`. Use the proof step `neg_mem' := by`. Introduce `a ha j`.

Rewrite using `[map_neg, Finsupp.neg_apply]`. Conclude with `R.neg_mem (ha j)`. Use the proof step `mul_mem' := by`. Introduce `a b ha hb j`. Establish `e : a * b = algebraMap K A (B.repr a 0 * B.repr b 0 + B.repr a 1 * B.repr b 1 * D) + algebraMap K A (B.repr a 0 * B.repr b 1 + B.repr a 1 * B.repr b 0) * B 1` using `by conv_lhs => rw [eq_coord B hB0 a, eq_coord B hB0 b]`.

Simplify using `only [map_add, map_mul]`. Take the linear combination `(algebraMap K A (B.repr a 1) * algebraMap K A (B.repr b 1)) * hD`. Establish `h` using `coord_two B hB0 (B.repr a 0 * B.repr b 0 + B.repr a 1 * B.repr b 1 * D) (B.repr a 0 * B.repr b 1 + B.repr a 1 * B.repr b 0)`. Rewrite `h` using `[← e]`. Use `fin_cases j`.

Use `show B.repr (a * b) 0 ∈ R`. Rewrite using `[h.1]`. Conclude with `R.add_mem (R.mul_mem (ha 0) (hb 0)) (R.mul_mem (R.mul_mem (ha 1) (hb 1)) hDR)`. Use `show B.repr (a * b) 1 ∈ R`. Rewrite using `[h.2]`.

Conclude with `R.add_mem (R.mul_mem (ha 0) (hb 1)) (R.mul_mem (ha 1) (hb 0)) }`. Use `⟨O, fun y => ⟨fun hy k => coord_mem R B C hCB y hy k, fun hy j => coord_mem R C B hBC y hy j⟩, fun y => Iff.rfl⟩` and prove the remaining obligations.
-/
theorem exists_subring {d : ℕ} (B : Module.Basis (Fin 2) K A) (C : Module.Basis (Fin d) K A)
    (D : K) (hB0 : B 0 = 1) (hD : B 1 * B 1 = algebraMap K A D) (hDR : D ∈ R)
    (hBC : ∀ k j, B.repr (C k) j ∈ R) (hCB : ∀ j k, C.repr (B j) k ∈ R) :
    ∃ O : Subring A, (∀ y, y ∈ O ↔ ∀ k, C.repr y k ∈ R) ∧ (∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ R) := by
  let O : Subring A :=
    { carrier := {y | ∀ j, B.repr y j ∈ R}
      zero_mem' := by intro j; simp [R.zero_mem]
      one_mem' := by
        have h := coord_two B hB0 1 0
        simp only [map_one, map_zero, zero_mul, add_zero] at h
        show ∀ j, B.repr 1 j ∈ R
        refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
        · rw [h.1]; exact R.one_mem
        · rw [h.2]; exact R.zero_mem
      add_mem' := by
        intro a b ha hb j
        rw [map_add, Finsupp.add_apply]
        exact R.add_mem (ha j) (hb j)
      neg_mem' := by
        intro a ha j
        rw [map_neg, Finsupp.neg_apply]
        exact R.neg_mem (ha j)
      mul_mem' := by
        intro a b ha hb j
        have e : a * b = algebraMap K A (B.repr a 0 * B.repr b 0 + B.repr a 1 * B.repr b 1 * D) +
            algebraMap K A (B.repr a 0 * B.repr b 1 + B.repr a 1 * B.repr b 0) * B 1 := by
          conv_lhs => rw [eq_coord B hB0 a, eq_coord B hB0 b]
          simp only [map_add, map_mul]
          linear_combination (algebraMap K A (B.repr a 1) * algebraMap K A (B.repr b 1)) * hD
        have h := coord_two B hB0
          (B.repr a 0 * B.repr b 0 + B.repr a 1 * B.repr b 1 * D)
          (B.repr a 0 * B.repr b 1 + B.repr a 1 * B.repr b 0)
        rw [← e] at h
        fin_cases j
        · show B.repr (a * b) 0 ∈ R
          rw [h.1]
          exact R.add_mem (R.mul_mem (ha 0) (hb 0)) (R.mul_mem (R.mul_mem (ha 1) (hb 1)) hDR)
        · show B.repr (a * b) 1 ∈ R
          rw [h.2]
          exact R.add_mem (R.mul_mem (ha 0) (hb 1)) (R.mul_mem (ha 1) (hb 0)) }
  refine ⟨O, fun y => ⟨fun hy k => coord_mem R B C hCB y hy k,
    fun hy j => coord_mem R C B hBC y hy j⟩, fun y => Iff.rfl⟩

end Lattice

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigR_algebraMap (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Use `set K := Fv F v with hK`. Use `set B := Algebra.TensorProduct.basis K b₂ with hB`. Use `set C := Algebra.TensorProduct.basis K b with hC`. Set `Rs : Subring K` to `(v.adicCompletionIntegers F).toSubring`. Establish `hB0 : B 0 = 1`.

Rewrite using `[hB, Algebra.TensorProduct.basis_apply, hb0]`. Both sides reduce to the same expression. Establish `hB1 : B 1 = inclR K (b₂ 1)`. Rewrite using `[hB, Algebra.TensorProduct.basis_apply]`. Both sides reduce to the same expression.

Establish `hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D)`. Rewrite using `[hB1, ← map_mul, hD]`. Use `show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Establish `hDR : algebraMap F K D ∈ Rs` using `hD1.le`.

Take `⟨O, hOC, hOB⟩` from `exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR (fun k j => by`. Use `hBC k j` as an intermediate fact. Rewrite using `[show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)` and apply the resulting hypothesis. Use the proof step `(fun j k => by`. Use `hCB j k` as an intermediate fact.

Rewrite using `[show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)` and apply the resulting hypothesis. Establish `hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs → algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O`. Introduce `p q hp hq`. Establish `h` using `coord_two B hB0 p q`. Use `(hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)` and prove the remaining obligations.

Rewrite using `[h.1]`. Conclude with `hp`. Rewrite using `[h.2]`. Conclude with `hq`. Establish `hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O`.

Introduce `c hc`. Simplify using `using hpq c 0 hc Rs.zero_mem`. Establish `hδO : B 1 ∈ O`. Use `hpq 0 1 Rs.zero_mem Rs.one_mem` as an intermediate fact. Rewrite `this` using `[map_zero, map_one, zero_add, one_mul]`. Then use the resulting hypothesis.

Set `ι : (v.adicCompletionIntegers F) →+* O` to `((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O (fun x => hRmem x x.2)`. Set `δ : O` to `⟨B 1, hδO⟩`. Establish `hσB : sigR K σ (B 1) = -B 1`. Rewrite using `[hB1]`. Use `show (1 : Fv F v) ⊗ₜ[F] σ (b₂ 1) = -((1 : Fv F v) ⊗ₜ[F] b₂ 1)`.

Rewrite using `[hσ1, TensorProduct.tmul_neg]`. Establish `hstab : ∀ y ∈ O, sigR K σ y ∈ O`. Introduce `y hy`. Establish `hy'` using `(hOB y).1 hy`. Rewrite using `[eq_coord B hB0 y, map_add, map_mul, sigR_algebraMap σ v, sigR_algebraMap σ v, hσB]`.

Use `hpq (B.repr y 0) (-(B.repr y 1)) (hy' 0) (Rs.neg_mem (hy' 1))` as an intermediate fact. Simplify `this` using `[map_neg]`. Set `τ : O →+* O` to `(sigR K σ).restrict O O hstab`. Set `D' : v.adicCompletionIntegers F` to `⟨algebraMap F K D, hDR⟩`. Establish `hτι : ∀ r, τ (ι r) = ι r` using `fun r => Subtype.ext (sigR_algebraMap σ v _)`.

Establish `hτδ : τ δ = -δ` using `Subtype.ext hσB`. Establish `hδ : δ * δ = ι D'` using `Subtype.ext hBD`. Establish `hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ` using `fun y => by`. Establish `hy` using `(hOB y).1 y.2`. Conclude with `⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩`.

Establish `hinj : ∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0`. Introduce `p q h`. Establish `h' : algebraMap K (K ⊗[F] E) (p : K) + algebraMap K (K ⊗[F] E) (q : K) * B 1 = 0` using `congrArg Subtype.val h`. Establish `hc` using `coord_two B hB0 (p : K) (q : K)`. Rewrite `hc` using `[h']`.

Simplify using `only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hc`. Conclude with `⟨Subtype.ext hc.1.symm, Subtype.ext hc.2.symm⟩`. Establish `hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1` using `fun r => HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one`. Establish `hv2 : Valued.v (2 : K) = 1` using `by simpa [map_ofNat] using h21`. Establish `hv3 : Valued.v (3 : K) = 1` using `by simpa [map_ofNat] using h31`.

Establish `hDu : IsUnit D'` using `(hunit D').2 hD1`. Establish `h2u : IsUnit (2 : v.adicCompletionIntegers F)` using `(hunit 2).2 (by`. Rewrite using `[show ((2 : v.adicCompletionIntegers F) : K) = 2 from map_ofNat (v.adicCompletionIntegers F).subtype 2]`. Conclude with `hv2)`. Establish `h3u : IsUnit (3 : v.adicCompletionIntegers F)` using `(hunit 3).2 (by`.

Rewrite using `[show ((3 : v.adicCompletionIntegers F) : K) = 3 from map_ofNat (v.adicCompletionIntegers F).subtype 3]`. Conclude with `hv3)`. Use `⟨O, hOC, hstab, finite_maxSpec ι δ hsp, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `h2u.map ι` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Use `⟨δ, ?_, hσB⟩` and prove the remaining obligations. Establish `h : IsUnit (δ * δ)` using `by rw [hδ]; exact hDu.map ι`. Conclude with `isUnit_of_mul_isUnit_left h`. Introduce `s β hβ hτβ`. Take `⟨ε, z, h1, h2⟩` from `exists_eps ι τ δ D' hδ hτι hτδ hsp hinj hDu h2u h3u s β hβ (Subtype.ext hτβ)`.

Conclude with `⟨ε, z, congrArg Subtype.val h1, congrArg Subtype.val h2⟩`. Introduce `β hβ hτβ`. Take `⟨c, hc, rfl⟩` from `fixed_unit ι τ δ hτι hτδ hsp hinj h2u β hβ (Subtype.ext hτβ)`. Take `⟨x, hx, y, hy, e⟩` from `GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v (algebraMap F K D) (c : K) hv2 hD1 ((hunit c).1 hc)`. Use `⟨ι ⟨x, hx⟩ + ι ⟨y, hy⟩ * δ, ?_⟩` and prove the remaining obligations.

Establish `h` using `norm_eq ι τ δ D' hδ hτι hτδ ⟨x, hx⟩ ⟨y, hy⟩`. Establish `e' : (⟨x, hx⟩ : v.adicCompletionIntegers F) ^ 2 - D' * ⟨y, hy⟩ ^ 2 = c` using `Subtype.ext e.symm`. Rewrite `h` using `[e']`. Conclude with `congrArg Subtype.val h`.
-/
theorem good_at (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1) (hσ1 : σ (b₂ 1) = -b₂ 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (h31 : Valued.v (algebraMap F (Fv F v) 3) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F) :
    ∃ O : Subring (Fv F v ⊗[F] E),
      (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F) ∧
      (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧
      (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧
      (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O,
        (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧
        ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧
      ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β →
        ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  obtain ⟨O, hOC, hOB⟩ := exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR
    (fun k j => by
      have := hBC k j
      rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)
    (fun j k => by
      have := hCB j k
      rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  have hσB : sigR K σ (B 1) = -B 1 := by
    rw [hB1]
    show (1 : Fv F v) ⊗ₜ[F] σ (b₂ 1) = -((1 : Fv F v) ⊗ₜ[F] b₂ 1)
    rw [hσ1, TensorProduct.tmul_neg]
  have hstab : ∀ y ∈ O, sigR K σ y ∈ O := by
    intro y hy
    have hy' := (hOB y).1 hy
    rw [eq_coord B hB0 y, map_add, map_mul, sigR_algebraMap σ v, sigR_algebraMap σ v, hσB]
    have := hpq (B.repr y 0) (-(B.repr y 1)) (hy' 0) (Rs.neg_mem (hy' 1))
    simpa [map_neg] using this
  let τ : O →+* O := (sigR K σ).restrict O O hstab
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hτι : ∀ r, τ (ι r) = ι r := fun r => Subtype.ext (sigR_algebraMap σ v _)
  have hτδ : τ δ = -δ := Subtype.ext hσB
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hinj : ∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' : algebraMap K (K ⊗[F] E) (p : K) + algebraMap K (K ⊗[F] E) (q : K) * B 1 = 0 :=
      congrArg Subtype.val h
    have hc := coord_two B hB0 (p : K) (q : K)
    rw [h'] at hc
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
    exact ⟨Subtype.ext hc.1.symm, Subtype.ext hc.2.symm⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hv3 : Valued.v (3 : K) = 1 := by simpa [map_ofNat] using h31
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  have h3u : IsUnit (3 : v.adicCompletionIntegers F) := (hunit 3).2 (by
    rw [show ((3 : v.adicCompletionIntegers F) : K) = 3 from
      map_ofNat (v.adicCompletionIntegers F).subtype 3]
    exact hv3)
  refine ⟨O, hOC, hstab, finite_maxSpec ι δ hsp, ?_, ?_, ?_, ?_⟩
  · have := h2u.map ι
    rwa [map_ofNat] at this
  · refine ⟨δ, ?_, hσB⟩
    have h : IsUnit (δ * δ) := by rw [hδ]; exact hDu.map ι
    exact isUnit_of_mul_isUnit_left h
  · intro s β hβ hτβ
    obtain ⟨ε, z, h1, h2⟩ := exists_eps ι τ δ D' hδ hτι hτδ hsp hinj hDu h2u h3u s β hβ
      (Subtype.ext hτβ)
    exact ⟨ε, z, congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  · intro β hβ hτβ
    obtain ⟨c, hc, rfl⟩ := fixed_unit ι τ δ hτι hτδ hsp hinj h2u β hβ (Subtype.ext hτβ)
    obtain ⟨x, hx, y, hy, e⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v
      (algebraMap F K D) (c : K) hv2 hD1 ((hunit c).1 hc)
    refine ⟨ι ⟨x, hx⟩ + ι ⟨y, hy⟩ * δ, ?_⟩
    have h := norm_eq ι τ δ D' hδ hτι hτδ ⟨x, hx⟩ ⟨y, hy⟩
    have e' : (⟨x, hx⟩ : v.adicCompletionIntegers F) ^ 2 - D' * ⟨y, hy⟩ ^ 2 = c :=
      Subtype.ext e.symm
    rw [e'] at h
    exact congrArg Subtype.val h

end Place

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h d b`. Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.

Establish `hne : ∃ x, σ x ≠ x`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨w⟩` from `(inferInstance : Nonempty (NumberField.InfinitePlace E))`. Establish `hreal : w.IsReal`.

Rewrite using `[← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]`. Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Express the relevant statement in the definitionally equal form `star (w.embedding x) = w.embedding x`. Rewrite using `[← h.2.2.2, hc]`.

Conclude with `NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal`. Take `⟨D, b₂, hsq, hb0, hσ1, hD⟩` from `GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne`. Establish `hD0 : D ≠ 0` using `fun h0 => hsq (h0 ▸ IsSquare.zero)`. Establish `I` using `GlobalTheory.T.integral_almost_all_places F E σ h`. Use `filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero, (I d b).2 3 three_ne_zero, Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k), Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 h31 hBC hCB`.

Conclude with `good_at σ b b₂ D hb0 hσ1 hD v hD1 h21 h31 hBC hCB`.
-/
theorem good_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) ∧ (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧ (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧ (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O, (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧ ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧ ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero, (I d b).2 3 three_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 h31 hBC hCB
  exact good_at σ b b₂ D hb0 hσ1 hD v hD1 h21 h31 hBC hCB

end GlobalTheory.CompanionTheory.SW.GoodRing
