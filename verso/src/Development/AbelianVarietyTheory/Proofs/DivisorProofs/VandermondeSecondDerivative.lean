import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeLaplacianVanishesStatement
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

noncomputable section

namespace GlobalTheory.VdmApolarPair

open MvPolynomial

section General

variable {ν : Type} [Fintype ν]

/- English proof (translation)
Proceed by induction on `D using MvPolynomial.induction_on' with`. Consider the case `monomial u a => simp only [GlobalTheory.FlagFormDeg.apolar_monomial, coeff_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem apolar_add_left' (P Q D : MvPolynomial ν ℝ) : apolar (P + Q) D = apolar P D + apolar Q D := by
  induction D using MvPolynomial.induction_on' with
  | monomial u a => simp only [GlobalTheory.FlagFormDeg.apolar_monomial, coeff_add]; ring
  | add p q hp hq => simp only [map_add, hp, hq]; ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' generalizing Q with`. Consider the case `monomial u a`. Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Rewrite using `[GlobalTheory.FlagFormDeg.apolar_monomial, GlobalTheory.FlagFormDeg.apolar_monomial, coeff_monomial, coeff_monomial]`.

Distinguish the cases in `h : u = m`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h, Ne.symm h]`.

Consider the case `add p q hp hq => rw [map_add, apolar_add_left', hp, hq]`. Consider the case `add p q hp hq => rw [apolar_add_left', hp, hq, map_add]`.
-/
theorem apolar_comm' (P Q : MvPolynomial ν ℝ) : apolar P Q = apolar Q P := by
  induction P using MvPolynomial.induction_on' generalizing Q with
  | monomial u a =>
    induction Q using MvPolynomial.induction_on' with
    | monomial m c =>
      rw [GlobalTheory.FlagFormDeg.apolar_monomial, GlobalTheory.FlagFormDeg.apolar_monomial, coeff_monomial, coeff_monomial]
      by_cases h : u = m
      · subst h; simp only [if_true]; ring
      · simp [h, Ne.symm h]
    | add p q hp hq => rw [map_add, apolar_add_left', hp, hq]
  | add p q hp hq => rw [apolar_add_left', hp, hq, map_add]

/- English proof (translation)
Rewrite using `[apolar_comm', map_smul, apolar_comm', smul_eq_mul]`.
-/
theorem apolar_smul_left' (c : ℝ) (P D : MvPolynomial ν ℝ) : apolar (c • P) D = c * apolar P D := by
  rw [apolar_comm', map_smul, apolar_comm', smul_eq_mul]

/- English proof (translation)
Rewrite using `[apolar_comm', map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => apolar_comm' _ _`.
-/
theorem apolar_sum_left' {α : Type} (s : Finset α) (F : α → MvPolynomial ν ℝ) (D : MvPolynomial ν ℝ) :
    apolar (∑ a ∈ s, F a) D = ∑ a ∈ s, apolar (F a) D := by
  rw [apolar_comm', map_sum]
  exact Finset.sum_congr rfl fun a _ => apolar_comm' _ _

/- English proof (translation)
Proceed by induction on `D using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Rewrite using `[rename_monomial, GlobalTheory.FlagFormDeg.apolar_monomial, GlobalTheory.FlagFormDeg.apolar_monomial, coeff_rename_mapDomain _ e.injective]`. Use `congr 2`. Rewrite using `[← Equiv.prod_comp e]`.

Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_apply e.injective]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem apolar_rename_equiv (e : ν ≃ ν) (P D : MvPolynomial ν ℝ) :
    apolar (rename e P) (rename e D) = apolar P D := by
  induction D using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [rename_monomial, GlobalTheory.FlagFormDeg.apolar_monomial, GlobalTheory.FlagFormDeg.apolar_monomial,
      coeff_rename_mapDomain _ e.injective]
    congr 2
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finsupp.mapDomain_apply e.injective]
  | add p q hp hq => simp only [map_add, hp, hq]

end General

end GlobalTheory.VdmApolarPair

namespace GlobalTheory.VdmApolarPair

open MvPolynomial

section Vdm

variable (r : ℕ)

def vdm : MvPolynomial (Option (Fin r)) ℝ :=
  ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i))

def psq : MvPolynomial (Option (Fin r)) ℝ := ∑ i : Fin r, X (some i) ^ 2

def pone : MvPolynomial (Option (Fin r)) ℝ := ∑ i : Fin r, X (some i)

def bb (a c : Fin r) : ℝ := apolar (psq r * vdm r) (X (some a) * (X (some c) * vdm r))

/- English proof (translation)
Rewrite using `[Matrix.det_vandermonde]`. Both sides reduce to the same expression.
-/
theorem vdm_eq_det :
    vdm r = (Matrix.vandermonde fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)).det := by
  rw [Matrix.det_vandermonde]; rfl

/- English proof (translation)
Rewrite using `[vdm_eq_det, AlgHom.map_det]`. Establish `h : (rename (Equiv.optionCongr σ) : MvPolynomial (Option (Fin r)) ℝ →ₐ[ℝ] _).mapMatrix (Matrix.vandermonde fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)) = (Matrix.vandermonde fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)).submatrix σ id`. Use extensionality with `i j`. Simplify using `[Matrix.vandermonde_apply]`. Rewrite using `[h, Matrix.det_permute]`.

Simplify using the standard rewrite rules.
-/
theorem rename_vdm (σ : Equiv.Perm (Fin r)) :
    rename (Equiv.optionCongr σ) (vdm r) = C ((Equiv.Perm.sign σ : ℤ) : ℝ) * vdm r := by
  rw [vdm_eq_det, AlgHom.map_det]
  have h : (rename (Equiv.optionCongr σ) : MvPolynomial (Option (Fin r)) ℝ →ₐ[ℝ] _).mapMatrix
      (Matrix.vandermonde fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)) =
      (Matrix.vandermonde fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]
  simp

/- English proof (translation)
Simplify using `only [psq, map_sum, map_pow, rename_X, Equiv.optionCongr_apply, Option.map_some]`. Conclude with `Equiv.sum_comp σ (fun i => (X (some i) : MvPolynomial (Option (Fin r)) ℝ) ^ 2)`.
-/
theorem rename_psq (σ : Equiv.Perm (Fin r)) : rename (Equiv.optionCongr σ) (psq r) = psq r := by
  simp only [psq, map_sum, map_pow, rename_X, Equiv.optionCongr_apply, Option.map_some]
  exact Equiv.sum_comp σ (fun i => (X (some i) : MvPolynomial (Option (Fin r)) ℝ) ^ 2)

/- English proof (translation)
Unfold `bb`. Use `conv_rhs => rw [← apolar_rename_equiv (Equiv.optionCongr σ)]`. Simplify using `only [map_mul, rename_X, rename_vdm, rename_psq, Equiv.optionCongr_apply, Option.map_some]`. Use `set ε : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)`. Establish `hε : ε * ε = 1`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [ε, h]`. Establish `h1 : psq r * (C ε * vdm r) = ε • (psq r * vdm r)` using `by rw [smul_eq_C_mul]; ring`. Establish `h2 : (X (some (σ a)) * (X (some (σ c)) * (C ε * vdm r)) : MvPolynomial (Option (Fin r)) ℝ) = ε • (X (some (σ a)) * (X (some (σ c)) * vdm r))` using `by rw [smul_eq_C_mul]; ring`. Rewrite using `[h1, h2, map_smul, apolar_smul_left', smul_eq_mul, ← mul_assoc ε ε, hε, one_mul]`.
-/
theorem bb_perm (σ : Equiv.Perm (Fin r)) (a c : Fin r) : bb r (σ a) (σ c) = bb r a c := by
  unfold bb
  conv_rhs => rw [← apolar_rename_equiv (Equiv.optionCongr σ)]
  simp only [map_mul, rename_X, rename_vdm, rename_psq, Equiv.optionCongr_apply, Option.map_some]
  set ε : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)
  have hε : ε * ε = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [ε, h]
  have h1 : psq r * (C ε * vdm r) = ε • (psq r * vdm r) := by rw [smul_eq_C_mul]; ring
  have h2 : (X (some (σ a)) * (X (some (σ c)) * (C ε * vdm r)) : MvPolynomial (Option (Fin r)) ℝ) =
      ε • (X (some (σ a)) * (X (some (σ c)) * vdm r)) := by rw [smul_eq_C_mul]; ring
  rw [h1, h2, map_smul, apolar_smul_left', smul_eq_mul, ← mul_assoc ε ε, hε, one_mul]

/- English proof (translation)
Use `bb_perm r (Equiv.swap a a') a a` as an intermediate fact. Rewrite `this` using `[Equiv.swap_apply_left]`. Conclude with `this.symm`.
-/
theorem bb_diag (a a' : Fin r) : bb r a a = bb r a' a' := by
  have := bb_perm r (Equiv.swap a a') a a
  rw [Equiv.swap_apply_left] at this
  exact this.symm

/- English proof (translation)
Establish `e1` using `bb_perm r (Equiv.swap a a') a c`. Rewrite `e1` using `[Equiv.swap_apply_left]`. Establish `hne : Equiv.swap a a' c ≠ a'`. Introduce `hc`. Apply `h` to reduce the goal to its premises.

Establish `: Equiv.swap a a' c = Equiv.swap a a' a` using `by rw [hc, Equiv.swap_apply_left]`. Conclude with `((Equiv.swap a a').injective this).symm`. Establish `e2` using `bb_perm r (Equiv.swap (Equiv.swap a a' c) c') a' (Equiv.swap a a' c)`. Rewrite `e2` using `[Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hne.symm h']`. Rewrite using `[← e1, ← e2]`.
-/
theorem bb_off (a c a' c' : Fin r) (h : a ≠ c) (h' : a' ≠ c') : bb r a c = bb r a' c' := by
  have e1 := bb_perm r (Equiv.swap a a') a c
  rw [Equiv.swap_apply_left] at e1
  have hne : Equiv.swap a a' c ≠ a' := by
    intro hc
    apply h
    have : Equiv.swap a a' c = Equiv.swap a a' a := by rw [hc, Equiv.swap_apply_left]
    exact ((Equiv.swap a a').injective this).symm
  have e2 := bb_perm r (Equiv.swap (Equiv.swap a a' c) c') a' (Equiv.swap a a' c)
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hne.symm h'] at e2
  rw [← e1, ← e2]

end Vdm

end GlobalTheory.VdmApolarPair

namespace GlobalTheory.VdmApolarPair

open MvPolynomial

section Sums

variable (r : ℕ)

/- English proof (translation)
Rewrite using `[psq, map_sum, Finset.sum_eq_single a]`. Simplify using `[Derivation.leibniz_pow]`. Introduce `i _ hi`. Establish `: (some a : Option (Fin r)) ≠ some i` using `fun h => hi (Option.some_injective _ h).symm`. Simplify using `[Derivation.leibniz_pow, pderiv_X_of_ne this.symm]`.

Simplify using the standard rewrite rules.
-/
theorem pderiv_psq (a : Fin r) : pderiv (some a) (psq r) = 2 * X (some a) := by
  rw [psq, map_sum, Finset.sum_eq_single a]
  · simp [Derivation.leibniz_pow]
  · intro i _ hi
    have : (some a : Option (Fin r)) ≠ some i := fun h => hi (Option.some_injective _ h).symm
    simp [Derivation.leibniz_pow, pderiv_X_of_ne this.symm]
  · simp

/- English proof (translation)
Rewrite using `[pone, map_sum, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Establish `: (some a : Option (Fin r)) ≠ some i` using `fun h => hi (Option.some_injective _ h).symm`. Simplify using `[pderiv_X_of_ne this.symm]`.

Simplify using the standard rewrite rules.
-/
theorem pderiv_pone (a : Fin r) : pderiv (some a) (pone r) = 1 := by
  rw [pone, map_sum, Finset.sum_eq_single a]
  · simp
  · intro i _ hi
    have : (some a : Option (Fin r)) ≠ some i := fun h => hi (Option.some_injective _ h).symm
    simp [pderiv_X_of_ne this.symm]
  · simp

/- English proof (translation)
Unfold `vdm`. Use `Finset.prod_induction _ (fun q => pderiv (none : Option (Fin r)) q = 0) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p q hp hq`. Simplify using `[Derivation.leibniz, hp, hq]`. Conclude with `Derivation.map_one_eq_zero _`.

Introduce `i _`. Use `Finset.prod_induction _ (fun q => pderiv (none : Option (Fin r)) q = 0) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p q hp hq`. Simplify using `[Derivation.leibniz, hp, hq]`. Conclude with `Derivation.map_one_eq_zero _`.

Introduce `i' _`. Simplify using `[pderiv_X_of_ne (show (some i' : Option (Fin r)) ≠ none by simp), pderiv_X_of_ne (show (some i : Option (Fin r)) ≠ none by simp)]`.
-/
theorem pderiv_none_vdm : pderiv none (vdm r) = 0 := by
  unfold vdm
  refine Finset.prod_induction _ (fun q => pderiv (none : Option (Fin r)) q = 0) ?_ ?_ ?_
  · intro p q hp hq; simp [Derivation.leibniz, hp, hq]
  · exact Derivation.map_one_eq_zero _
  · intro i _
    refine Finset.prod_induction _ (fun q => pderiv (none : Option (Fin r)) q = 0) ?_ ?_ ?_
    · intro p q hp hq; simp [Derivation.leibniz, hp, hq]
    · exact Derivation.map_one_eq_zero _
    · intro i' _
      simp [pderiv_X_of_ne (show (some i' : Option (Fin r)) ≠ none by simp),
        pderiv_X_of_ne (show (some i : Option (Fin r)) ≠ none by simp)]

/- English proof (translation)
Unfold `vdm`. Use `IsHomogeneous.prod _ _ _ fun i _ => IsHomogeneous.prod _ _ _ fun i' _ => ?_` and prove the remaining obligations. Conclude with `(isHomogeneous_X _ _).sub (isHomogeneous_X _ _)`.
-/
theorem vdm_homog : (vdm r).IsHomogeneous (∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1) := by
  unfold vdm
  refine IsHomogeneous.prod _ _ _ fun i _ => IsHomogeneous.prod _ _ _ fun i' _ => ?_
  exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)

/- English proof (translation)
Establish `h1 : (∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1 : ℕ) = r * (r - 1) / 2`. Rewrite using `[← GlobalTheory.FlagFormDeg.sum_card_Ioi]`. Simplify using the standard rewrite rules. Establish `h2 : 2 * (r * (r - 1) / 2) = r * (r - 1)` using `Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self r))`. Rewrite using `[h1]`.

Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h3 : ((2 * (r * (r - 1) / 2) : ℕ) : ℝ) = ((r * (r - 1) : ℕ) : ℝ)` using `by rw [h2]`. Move the coercions through the operations in `[Nat.cast_sub (show 1 ≤ r from h)] at h3`.

Rewrite using `[← h3]`.
-/
theorem two_mul_deg : 2 * ((∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1 : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
  have h1 : (∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1 : ℕ) = r * (r - 1) / 2 := by
    rw [← GlobalTheory.FlagFormDeg.sum_card_Ioi]
    simp
  have h2 : 2 * (r * (r - 1) / 2) = r * (r - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self r))
  rw [h1]
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · have h3 : ((2 * (r * (r - 1) / 2) : ℕ) : ℝ) = ((r * (r - 1) : ℕ) : ℝ) := by rw [h2]
    push_cast [Nat.cast_sub (show 1 ≤ r from h)] at h3
    rw [← h3]

/- English proof (translation)
Rewrite using `[← (vdm_homog r).sum_X_mul_pderiv, Fintype.sum_option, pderiv_none_vdm, mul_zero, zero_add]`.
-/
theorem euler_vdm :
    ∑ a : Fin r, X (some a) * pderiv (some a) (vdm r) =
      (∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1 : ℕ) • vdm r := by
  rw [← (vdm_homog r).sum_X_mul_pderiv, Fintype.sum_option, pderiv_none_vdm, mul_zero, zero_add]

/- English proof (translation)
Simplify using `only [Derivation.leibniz, smul_eq_mul, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv2_mul (D : Derivation ℝ (MvPolynomial (Option (Fin r)) ℝ) (MvPolynomial (Option (Fin r)) ℝ))
    (p w : MvPolynomial (Option (Fin r)) ℝ) : D (D (p * w)) = D (D p) * w + 2 * (D p * D w) + p * D (D w) := by
  simp only [Derivation.leibniz, smul_eq_mul, map_add]; ring

/- English proof (translation)
Rewrite using `[bb, GlobalTheory.FlagFormDeg.apolar_X_mul, GlobalTheory.FlagFormDeg.apolar_X_mul]`.
-/
theorem bb_eq (a c : Fin r) : bb r a c = apolar (pderiv (some c) (pderiv (some a) (psq r * vdm r))) (vdm r) := by
  rw [bb, GlobalTheory.FlagFormDeg.apolar_X_mul, GlobalTheory.FlagFormDeg.apolar_X_mul]

/- English proof (translation)
Rewrite using `[apolar_comm', map_zero]`.
-/
theorem apolar_zero_left' (Q : MvPolynomial (Option (Fin r)) ℝ) : apolar 0 Q = 0 := by
  rw [apolar_comm', map_zero]

/- English proof (translation)
Repeatedly rewrite using `[bb_eq]`. Rewrite using `[← apolar_sum_left', ← map_sum]`. Establish `h1 : ∑ a : Fin r, pderiv (some a) (psq r * vdm r) = (2 : ℝ) • (pone r * vdm r) + psq r * 0`. Rewrite using `[← hW1, Finset.mul_sum, pone, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Derivation.leibniz, pderiv_psq, smul_eq_mul, smul_eq_mul, smul_eq_C_mul]`. Simplify using `only [show (C 2 : MvPolynomial (Option (Fin r)) ℝ) = 2 from rfl]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : apolar (pone r * pderiv (some c) (vdm r)) (vdm r) = 0`. Rewrite using `[apolar_comm', pone, Finset.sum_mul, map_sum]`.

Repeatedly rewrite using `[GlobalTheory.FlagFormDeg.apolar_X_mul]`. Rewrite using `[← apolar_sum_left', hW1, apolar_zero_left']`. Rewrite using `[h1, mul_zero, add_zero, Derivation.map_smul, Derivation.leibniz, pderiv_pone, smul_eq_mul, smul_eq_mul, mul_one, smul_add, apolar_add_left', apolar_smul_left', apolar_smul_left', h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_sum (hW1 : ∑ a : Fin r, pderiv (some a) (vdm r) = 0) (c : Fin r) :
    ∑ a : Fin r, bb r a c = 2 * apolar (vdm r) (vdm r) := by
  simp_rw [bb_eq]
  rw [← apolar_sum_left', ← map_sum]
  have h1 : ∑ a : Fin r, pderiv (some a) (psq r * vdm r) = (2 : ℝ) • (pone r * vdm r) + psq r * 0 := by
    rw [← hW1, Finset.mul_sum, pone, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Derivation.leibniz, pderiv_psq, smul_eq_mul, smul_eq_mul, smul_eq_C_mul]
    simp only [show (C 2 : MvPolynomial (Option (Fin r)) ℝ) = 2 from rfl]
    ring
  have h0 : apolar (pone r * pderiv (some c) (vdm r)) (vdm r) = 0 := by
    rw [apolar_comm', pone, Finset.sum_mul, map_sum]
    simp_rw [GlobalTheory.FlagFormDeg.apolar_X_mul]
    rw [← apolar_sum_left', hW1, apolar_zero_left']
  rw [h1, mul_zero, add_zero, Derivation.map_smul, Derivation.leibniz, pderiv_pone, smul_eq_mul, smul_eq_mul, mul_one,
    smul_add, apolar_add_left', apolar_smul_left', apolar_smul_left', h0]
  ring

/- English proof (translation)
Repeatedly rewrite using `[bb_eq]`. Rewrite using `[← apolar_sum_left']`. Establish `hX : ∀ a : Fin r, pderiv (some a) (2 * X (some a) : MvPolynomial (Option (Fin r)) ℝ) = 2`. Introduce `a`. Establish `h2 : (2 * X (some a) : MvPolynomial (Option (Fin r)) ℝ) = (2 : ℝ) • X (some a)`.

Rewrite using `[smul_eq_C_mul]`. Both sides reduce to the same expression. Rewrite using `[h2, Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]`. Both sides reduce to the same expression. Establish `h1 : ∑ a : Fin r, pderiv (some a) (pderiv (some a) (psq r * vdm r)) = (2 * (r : ℝ) + 4 * ((∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1 : ℕ) : ℝ)) • vdm r`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[deriv2_mul, pderiv_psq, hX]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 2 * ∑ _a : Fin r, vdm r + 4 * ∑ a : Fin r, X (some a) * pderiv (some a) (vdm r) + psq r * ∑ a : Fin r, pderiv (some a) (pderiv (some a) (vdm r)) := by`.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `_ = _ := by`. Rewrite using `[hW2, euler_vdm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_zero, add_zero, smul_eq_C_mul]`. Simplify using `only [nsmul_eq_mul, map_add, map_mul, map_natCast, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, apolar_smul_left']`. Use `two_mul_deg r` as an intermediate fact. Take the linear combination `(2 * apolar (vdm r) (vdm r)) * this`.
-/
theorem trace_sum (hW2 : ∑ a : Fin r, pderiv (some a) (pderiv (some a) (vdm r)) = 0) :
    ∑ a : Fin r, bb r a a = 2 * (r : ℝ) ^ 2 * apolar (vdm r) (vdm r) := by
  simp_rw [bb_eq]
  rw [← apolar_sum_left']
  have hX : ∀ a : Fin r, pderiv (some a) (2 * X (some a) : MvPolynomial (Option (Fin r)) ℝ) = 2 := by
    intro a
    have h2 : (2 * X (some a) : MvPolynomial (Option (Fin r)) ℝ) = (2 : ℝ) • X (some a) := by
      rw [smul_eq_C_mul]; rfl
    rw [h2, Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]; rfl
  have h1 : ∑ a : Fin r, pderiv (some a) (pderiv (some a) (psq r * vdm r)) =
      (2 * (r : ℝ) + 4 * ((∑ i : Fin r, ∑ _i' ∈ Finset.Ioi i, 1 : ℕ) : ℝ)) • vdm r := by
    calc ∑ a : Fin r, pderiv (some a) (pderiv (some a) (psq r * vdm r))
        = ∑ a : Fin r, (2 * vdm r + 4 * (X (some a) * pderiv (some a) (vdm r)) +
            psq r * pderiv (some a) (pderiv (some a) (vdm r))) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [deriv2_mul, pderiv_psq, hX]; ring
      _ = 2 * ∑ _a : Fin r, vdm r + 4 * ∑ a : Fin r, X (some a) * pderiv (some a) (vdm r) +
            psq r * ∑ a : Fin r, pderiv (some a) (pderiv (some a) (vdm r)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = _ := by
          rw [hW2, euler_vdm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_zero, add_zero,
            smul_eq_C_mul]
          simp only [nsmul_eq_mul, map_add, map_mul, map_natCast, map_ofNat]
          ring
  rw [h1, apolar_smul_left']
  have := two_mul_deg r
  linear_combination (2 * apolar (vdm r) (vdm r)) * this

end Sums

end GlobalTheory.VdmApolarPair

namespace GlobalTheory.VdmApolarPair

open MvPolynomial

/- English proof (translation)
Introduce `r`. Take `⟨hW1, hW2⟩` from `GlobalTheory.T.vandermonde_laplacian_vanishes r`. Establish `hW1' : ∑ a : Fin r, pderiv (some a) (vdm r) = 0` using `hW1`. Establish `hW2' : ∑ a : Fin r, pderiv (some a) (pderiv (some a) (vdm r)) = 0` using `hW2`. Use `⟨2 * apolar (vdm r) (vdm r), fun a b => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `bb r a b = _`. Establish `hdiag : ∀ c : Fin r, bb r c c = 2 * (r : ℝ) * apolar (vdm r) (vdm r)`. Introduce `c`. Establish `ht` using `trace_sum r hW2'`. Establish `hc : ∑ x : Fin r, bb r x x = (r : ℝ) * bb r c c`.

Rewrite using `[Finset.sum_congr rfl fun x _ => bb_diag r x c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hr : (r : ℝ) ≠ 0`. Use `c.pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Rewrite `ht` using `[hc]`.

Apply `mul_left_cancel₀ hr` to reduce the goal to its premises. Take the linear combination `ht`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, hdiag]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hab]`. Establish `h2 : 2 ≤ r`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact.

Establish `: a.val ≠ b.val` using `fun h => hab (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Establish `hrow` using `row_sum r hW1' b`. Rewrite `hrow` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ b), hdiag, Finset.sum_congr rfl fun x hx => bb_off r x b a b (Finset.ne_of_mem_erase hx) hab, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 …`. Establish `hr : (r : ℝ) - 1 ≠ 0`.

Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `mul_left_cancel₀ hr` to reduce the goal to its premises. Take the linear combination `hrow`.
-/
theorem apolar_psq_vdm : ∀ r : ℕ, ∃ κ : ℝ, ∀ a b : Fin r,
    apolar ((∑ i : Fin r, MvPolynomial.X (some i) ^ 2) *
      ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) :
        MvPolynomial (Option (Fin r)) ℝ)
      (MvPolynomial.X (some a) * (MvPolynomial.X (some b) *
        ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)))) =
      κ * ((if a = b then (r : ℝ) + 1 else 0) - 1) := by
  intro r
  obtain ⟨hW1, hW2⟩ := GlobalTheory.T.vandermonde_laplacian_vanishes r
  have hW1' : ∑ a : Fin r, pderiv (some a) (vdm r) = 0 := hW1
  have hW2' : ∑ a : Fin r, pderiv (some a) (pderiv (some a) (vdm r)) = 0 := hW2
  refine ⟨2 * apolar (vdm r) (vdm r), fun a b => ?_⟩
  change bb r a b = _
  have hdiag : ∀ c : Fin r, bb r c c = 2 * (r : ℝ) * apolar (vdm r) (vdm r) := by
    intro c
    have ht := trace_sum r hW2'
    have hc : ∑ x : Fin r, bb r x x = (r : ℝ) * bb r c c := by
      rw [Finset.sum_congr rfl fun x _ => bb_diag r x c, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hr : (r : ℝ) ≠ 0 := by
      have := c.pos; exact_mod_cast this.ne'
    rw [hc] at ht
    apply mul_left_cancel₀ hr
    linear_combination ht
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, hdiag]
    ring
  · rw [if_neg hab]
    have h2 : 2 ≤ r := by
      have := a.isLt; have := b.isLt
      have : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    have hrow := row_sum r hW1' b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hdiag,
      Finset.sum_congr rfl fun x hx => bb_off r x b a b (Finset.ne_of_mem_erase hx) hab,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hrow
    have hr : (r : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast h2
      linarith
    apply mul_left_cancel₀ hr
    linear_combination hrow

end GlobalTheory.VdmApolarPair
