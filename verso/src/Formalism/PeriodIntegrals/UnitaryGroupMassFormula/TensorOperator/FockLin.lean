import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development

open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

section Fock

variable {σ R : Type*} [CommRing R]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem fockR_eq_sum (f g : MvPolynomial σ R) (T : Finset (σ →₀ ℕ)) (hT : f.support ⊆ T) :
    fockR f g = ∑ m ∈ T, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  unfold fockR
  refine Finset.sum_subset hT fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm, zero_mul, zero_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockR_add_left (f₁ f₂ g : MvPolynomial σ R) : fockR (f₁ + f₂) g = fockR f₁ g + fockR f₂ g := by
  classical
  rw [fockR_eq_sum (f₁ + f₂) g (f₁.support ∪ f₂.support) MvPolynomial.support_add,
    fockR_eq_sum f₁ g _ Finset.subset_union_left, fockR_eq_sum f₂ g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockR_smul_left (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g := by
  rw [fockR_eq_sum (a • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockR_add_right (f g₁ g₂ : MvPolynomial σ R) : fockR f (g₁ + g₂) = fockR f g₁ + fockR f g₂ := by
  unfold fockR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockR_smul_right (a : R) (f g : MvPolynomial σ R) : fockR f (a • g) = a * fockR f g := by
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

def fockB (σ R : Type*) [CommRing R] : MvPolynomial σ R →ₗ[R] MvPolynomial σ R →ₗ[R] R :=
  LinearMap.mk₂ R fockR fockR_add_left (fun a f g => by rw [fockR_smul_left, smul_eq_mul])
    fockR_add_right (fun a f g => by rw [fockR_smul_right, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockB_apply (f g : MvPolynomial σ R) : fockB σ R f g = fockR f g := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fockR_zero_left (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  simp [fockR]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fockR_zero_right (f : MvPolynomial σ R) : fockR f 0 = 0 := by
  simp [fockR]

end Fock

section Words

variable {K : Type} [CommRing K] {n' k : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem opWord_cons (y : Fin n' × (Fin k × Fin k)) (l : List (Fin n' × (Fin k × Fin k)))
    (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (y :: l) f = X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f) := rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem opWord_add (l : List (Fin n' × (Fin k × Fin k))) (f g : MvPolynomial (Fin n' × Fin k) K) :
    opWord l (f + g) = opWord l f + opWord l g := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [opWord_cons, opWord_cons, opWord_cons, ih, map_add, mul_add]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem opWord_smul (l : List (Fin n' × (Fin k × Fin k))) (a : K) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord l (a • f) = a • opWord l f := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [opWord_cons, opWord_cons, ih, Derivation.map_smul, mul_smul_comm]

def opWordL (l : List (Fin n' × (Fin k × Fin k))) :
    MvPolynomial (Fin n' × Fin k) K →ₗ[K] MvPolynomial (Fin n' × Fin k) K where
  toFun := opWord l
  map_add' := opWord_add l
  map_smul' a f := opWord_smul l a f

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem combo_add_fun (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G₁ G₂ : MvPolynomial (Fin n' × Fin k) K) :
    combo f (G₁ + G₂) = combo f G₁ + combo f G₂ := by
  unfold combo
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr fun l _ => by rw [opWord_add, smul_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem combo_smul_fun (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (a : K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo f (a • G) = a • combo f G := by
  unfold combo
  rw [Finsupp.smul_sum]
  exact Finsupp.sum_congr fun l _ => by rw [opWord_smul, smul_comm]

def comboL (f : List (Fin n' × (Fin k × Fin k)) →₀ K) :
    MvPolynomial (Fin n' × Fin k) K →ₗ[K] MvPolynomial (Fin n' × Fin k) K where
  toFun := combo f
  map_add' := combo_add_fun f
  map_smul' a G := combo_smul_fun f a G

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem combo_add (f₁ f₂ : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (f₁ + f₂) G = combo f₁ G + combo f₂ G := by
  unfold combo
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem combo_smul (a : K) (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (a • f) G = a • combo f G := by
  unfold combo
  rw [Finsupp.sum_smul_index' (h := fun (l : List (Fin n' × (Fin k × Fin k))) (c : K) => c • opWord l G)
    (fun _ => zero_smul _ _), Finsupp.smul_sum]
  exact Finsupp.sum_congr fun l _ => by rw [smul_eq_mul, mul_smul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem combo_zero (G : MvPolynomial (Fin n' × Fin k) K) : combo (0 : List (Fin n' × (Fin k × Fin k)) →₀ K) G = 0 := by
  simp [combo]

end Words

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem bilin_ext_restrict {K : Type} [CommRing K] {σ : Type*} (T : Set (σ →₀ ℕ))
    (Φ Ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K)
    (h : ∀ μ ∈ T, ∀ ν ∈ T, Φ (monomial μ 1) (monomial ν 1) = Ψ (monomial μ 1) (monomial ν 1)) :
    ∀ G ∈ restrictSupport K T, ∀ H ∈ restrictSupport K T, Φ G H = Ψ G H := by
  have e : ∀ (ρ : σ →₀ ℕ) (c : K), (monomial ρ c : MvPolynomial σ K) = c • monomial ρ 1 := fun ρ c => by
    rw [smul_monomial, smul_eq_mul, mul_one]
  intro G hG H hH
  rw [MvPolynomial.mem_restrictSupport_iff] at hG hH
  rw [G.as_sum, H.as_sum]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun ν hν => ?_
  rw [e μ, e ν]
  simp only [map_smul, LinearMap.smul_apply]
  rw [h ν (hG hν) μ (hH hμ)]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem blockSubstitution_blockInclusion {K : Type} [CommRing K] {n' m : ℕ} (vec : Fin n' → Bool) (t : Fin n')
    (P : MvPolynomial (Fin (m + 1)) K) :
    Th0 K m vec (embS K t P) = blockEmb K t (theta K m (vec t) P) := by
  have hc : (Th0 K m vec).comp (embS K t) = (blockEmb K t).comp (theta K m (vec t)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Th0, embS, theta, blockEmb]
  exact AlgHom.congr_fun hc P

end PI.TOW
