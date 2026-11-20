import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoeffFunctional

open MvPolynomial

variable {σ K L : Type} [Field K] [Field L] [Algebra K L]

def coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ μ ∈ P.support, monomial μ (φ (P.coeff μ))

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) (μ : σ →₀ ℕ) :
    (coeffMap φ P).coeff μ = φ (P.coeff μ) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem coeffMap_add (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffMap φ (P + Q) = coeffMap φ P + coeffMap φ Q := by
  ext μ
  simp [coeff_coeffMap]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem coeffMap_zero (φ : L →ₗ[K] K) : coeffMap φ (0 : MvPolynomial σ L) = 0 := by
  ext μ
  simp [coeff_coeffMap]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem coeffMap_map_mul_C (φ : L →ₗ[K] K) (A : MvPolynomial σ K) (c : L) :
    coeffMap φ (MvPolynomial.C c * MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.C (φ c) * A := by
  ext μ
  rw [coeff_coeffMap, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm c, ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem coeffMap_comm (φ : L →ₗ[K] K) (f : MvPolynomial σ L →ₗ[L] MvPolynomial σ L)
    (g : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (h : ∀ A, f (MvPolynomial.map (algebraMap K L) A) = MvPolynomial.map (algebraMap K L) (g A))
    (P : MvPolynomial σ L) : coeffMap φ (f P) = g (coeffMap φ P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeffMap_add, coeffMap_add, map_add, hp, hq]
  | monomial μ c =>
    have e : (monomial μ c : MvPolynomial σ L) =
        MvPolynomial.C c * MvPolynomial.map (algebraMap K L) (monomial μ 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, coeffMap_map_mul_C, C_mul', map_smul, h, ← C_mul', coeffMap_map_mul_C, C_mul', C_mul',
      map_smul]

variable {T : Type} (r : T → ℕ) (n : ℕ)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem lap_one_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (A : MvPolynomial (Letter T r n) K) :
    lap r n L 1 τ τ' a a' (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (lap r n K 1 τ τ' a a' A) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    simp [pderiv_map]
  · simp [Matrix.one_apply_ne hb]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rowShift_map (s : T) (i i' : Fin (r s)) (t : K) (A : MvPolynomial (Letter T r n) K) :
    rowShift r n L s i i' (algebraMap K L t) (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (rowShift r n K s i i' t A) := by
  induction A using MvPolynomial.induction_on with
  | C c => simp [rowShift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p l hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mem_HHa_of_coeff_functional :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (K C : Type) [Field K] [Field C] [Algebra K C] (φ : C →ₗ[K] K) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C) (Q : MvPolynomial (Letter T r n) K), (∀ μ, Q.coeff μ = φ (P.coeff μ)) → P ∈ HHa r n C cc isX a → Q ∈ HHa r n K cc isX a := by
  intro T r n K L _ _ _ φ cc isX a P Q hQ hP
  have hQ' : Q = coeffMap φ P := by
    ext μ
    rw [hQ, coeff_coeffMap]
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [hQ', ← coeffMap_comm φ _ _ (lap_one_map r n τ (cc τ) b b') P, h1 τ hτ b b', coeffMap_zero]
  · intro s i i' hi t
    have := coeffMap_comm φ (rowShift r n L s i i' (algebraMap K L t)).toLinearMap
      (rowShift r n K s i i' t).toLinearMap (rowShift_map r n s i i' t) P
    simp only [AlgHom.toLinearMap_apply] at this
    rw [hQ', ← this, h2 s i i' hi]
  · intro m hm
    refine h3 m ?_
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hQ, h0, map_zero])

end GlobalTheory.CoeffFunctional
