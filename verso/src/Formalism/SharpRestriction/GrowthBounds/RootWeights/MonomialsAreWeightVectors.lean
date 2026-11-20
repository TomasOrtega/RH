import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialOperatorsGlRelations

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Rewrite using `[pderiv_monomial, show (X v : MvPolynomial σ R) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul, one_mul, add_comm (Finsupp.single v 1)]`.
-/
theorem v2con_X_pderiv {R : Type*} [CommRing R] {σ : Type*} (v w : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : R)) := by
  rw [pderiv_monomial, show (X v : MvPolynomial σ R) = monomial (Finsupp.single v 1) 1 from rfl,
    monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

/- English proof (translation)
Rewrite using `[v2con_X_pderiv]`. Distinguish the cases in `h : m v = 0`. Simplify using `[h]`. Establish `hle : Finsupp.single v 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[tsub_add_cancel_of_le hle]`.
-/
theorem v2con_X_pderiv_self {R : Type*} [CommRing R] {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv v (monomial m c) = monomial m (c * (m v : R)) := by
  rw [v2con_X_pderiv]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [tsub_add_cancel_of_le hle]

/- English proof (translation)
Unfold `glAct wtS`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [Int.cast_sum, Finset.sum_mul]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Apply the tactic sequence `by_cases h1 : l ∈ S <;> by_cases h2 : LL.vec l = true <;>`. Simplify using `[h1, h2, -pderiv_monomial, v2con_X_pderiv_self, mul_comm]`.
-/
theorem v2con_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : R) * c) := by
  classical
  unfold glAct wtS
  rw [LinearMap.sum_apply]
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases h1 : l ∈ S <;> by_cases h2 : LL.vec l = true <;>
    simp [h1, h2, -pderiv_monomial, v2con_X_pderiv_self, mul_comm]

/- English proof (translation)
Proceed by induction on `x using MvPolynomial.induction_on' with`. Consider the case `monomial m' c`. Rewrite using `[v2con_diag, coeff_monomial, coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`. Rewrite using `[map_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
theorem v2con_coeff_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (glAct R LL S a a x) = ((wtS LL S m a : ℤ) : R) * coeff m x := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [v2con_diag, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Introduce `R _ _ ι _ LL n S`. Prove the components needed by the constructor for the conclusion. Introduce `m c`. Rewrite using `[weightSp, Submodule.mem_iInf]`. Introduce `a`.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Express the relevant statement in the definitionally equal form `glAct R LL S a a (monomial m c) - _ = 0`. Rewrite using `[v2con_diag, smul_monomial, smul_eq_mul, sub_self]`. Introduce `ν x hx m hm`. Rewrite `hx` using `[weightSp, Submodule.mem_iInf]`.

Use function extensionality and compare the values at `a`. Establish `h` using `hx a`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Establish `h2` using `congrArg (coeff m) h`. Express the relevant statement in the definitionally equal form `coeff m (glAct R LL S a a x) = _ at h2`.

Rewrite `h2` using `[v2con_coeff_diag, coeff_smul, smul_eq_mul]`. Establish `hc : coeff m x ≠ 0` using `mem_support_iff.mp hm`. Establish `h3` using `mul_right_cancel₀ hc h2`. Conclude with `h3` after adjusting the coercions.
-/
theorem monomials_are_weight_vectors : MonomialsAreWeightVectors := by
  intro R _ _ ι _ LL n S
  constructor
  · intro m c
    rw [weightSp, Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    change glAct R LL S a a (monomial m c) - _ = 0
    rw [v2con_diag, smul_monomial, smul_eq_mul, sub_self]
  · intro ν x hx m hm
    rw [weightSp, Submodule.mem_iInf] at hx
    funext a
    have h := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    have h2 := congrArg (coeff m) h
    change coeff m (glAct R LL S a a x) = _ at h2
    rw [v2con_coeff_diag, coeff_smul, smul_eq_mul] at h2
    have hc : coeff m x ≠ 0 := mem_support_iff.mp hm
    have h3 := mul_right_cancel₀ hc h2
    exact_mod_cast h3

/- English proof (translation)
Rewrite `hx` using `[mem_restrictSupport_iff]`. Establish `hmono : ∀ (m' : ι × Fin n →₀ ℕ) (c' : R), m'.degree ≤ N → monomial m' c' ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}`. Introduce `m' c' hm'`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `y hy`.

Use `Finset.mem_singleton.mp (support_monomial_subset hy)` as an intermediate fact. Substitute `this` using the available equality. Conclude with `hm'`. Establish `hterm : ∀ (m : ι × Fin n →₀ ℕ) (c : R) (u w : ι × Fin n), m.degree ≤ N → (X u : MvPolynomial (ι × Fin n) R) * pderiv w (monomial m c) ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}`. Introduce `m c u w hm`.

Rewrite using `[v2con_X_pderiv]`. Distinguish the cases in `h0 : m w = 0`. Simplify using `[h0]`. Apply `hmono` to reduce the goal to its premises. Establish `hle : Finsupp.single w 1 ≤ m`.

Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e1 : (m - Finsupp.single w 1).degree + 1 = m.degree`. Use `congrArg Finsupp.degree (tsub_add_cancel_of_le hle)` as an intermediate fact. Rewrite `this` using `[map_add, Finsupp.degree_single]`.

Conclude with `this`. Rewrite using `[map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[x.as_sum, map_sum]`. Use `Submodule.sum_mem _ (fun m hm => ?_)` and prove the remaining obligations.

Establish `hdeg : m.degree ≤ N` using `hx hm`. Unfold `glAct`. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ (fun l _ => ?_)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `hterm m _ _ _ hdeg`. Rewrite using `[LinearMap.neg_apply]`. Conclude with `Submodule.neg_mem _ (hterm m _ _ _ hdeg)`. Conclude with `Submodule.zero_mem _`.
-/
theorem v2con_stable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (N : ℕ) (a b : Fin n) (x : MvPolynomial (ι × Fin n) R)
    (hx : x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}) :
    glAct R LL S a b x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
  classical
  rw [mem_restrictSupport_iff] at hx
  have hmono : ∀ (m' : ι × Fin n →₀ ℕ) (c' : R), m'.degree ≤ N →
      monomial m' c' ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m' c' hm'
    rw [mem_restrictSupport_iff]
    intro y hy
    have := Finset.mem_singleton.mp (support_monomial_subset hy)
    subst this
    exact hm'
  have hterm : ∀ (m : ι × Fin n →₀ ℕ) (c : R) (u w : ι × Fin n), m.degree ≤ N →
      (X u : MvPolynomial (ι × Fin n) R) * pderiv w (monomial m c) ∈
        restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m c u w hm
    rw [v2con_X_pderiv]
    by_cases h0 : m w = 0
    · simp [h0]
    · apply hmono
      have hle : Finsupp.single w 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have e1 : (m - Finsupp.single w 1).degree + 1 = m.degree := by
        have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, Finsupp.degree_single] at this
        exact this
      rw [map_add, Finsupp.degree_single]
      omega
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hdeg : m.degree ≤ N := hx hm
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  split_ifs
  · exact hterm m _ _ _ hdeg
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hterm m _ _ _ hdeg)
  · exact Submodule.zero_mem _

/- English proof (translation)
Introduce `R _ ι _ LL n S x`. Use `⟨restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree}, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : Finite {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree} := (Finsupp.finite_of_degree_le x.totalDegree).to_subtype`. Conclude with `Module.Finite.of_basis (basisRestrictSupport R _)`. Rewrite using `[mem_restrictSupport_iff]`.

Introduce `m hm`. Use `show m.degree ≤ x.totalDegree`. Rewrite using `[Finsupp.degree_apply]`. Conclude with `le_totalDegree hm`. Introduce `a b y hy`.

Conclude with `v2con_stable LL S _ a b y hy`.
-/
theorem polynomial_locally_finite : PolynomialLocallyFinite := by
  intro R _ ι _ LL n S x
  classical
  refine ⟨restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree}, ?_, ?_, ?_⟩
  · haveI : Finite {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree} :=
      (Finsupp.finite_of_degree_le x.totalDegree).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport R _)
  · rw [mem_restrictSupport_iff]
    intro m hm
    show m.degree ≤ x.totalDegree
    rw [Finsupp.degree_apply]
    exact le_totalDegree hm
  · intro a b y hy
    exact v2con_stable LL S _ a b y hy

end Formalism.MainNotions.G.GLWeightTheory
