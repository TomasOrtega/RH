import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module Filter Topology GlobalTheory.ChowHt
open scoped ENNReal

section Cone

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ}

def coneMap (K : Type) [Field K] [Algebra K Ω] (y : Fin N → Ω) : MvPolynomial (Fin N) K →ₐ[K] Polynomial Ω :=
  aeval fun j => Polynomial.X * Polynomial.C (y j)

def coneIdeal (K : Type) [Field K] [Algebra K Ω] (y : Fin N → Ω) : Ideal (MvPolynomial (Fin N) K) :=
  RingHom.ker (coneMap K y)

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Simplify using `only [coneMap, map_sum, aeval_monomial, Finset.mul_sum, map_mul]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `: a.degree = d` using `by rw [Finsupp.degree_eq_weight_one]; exact hg (mem_support_iff.1 ha)`.

Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]`. Rewrite using `[← this, Finsupp.degree_apply, mul_left_comm, Polynomial.algebraMap_apply]`.
-/
theorem coneMap_of_isHomogeneous (y : Fin N → Ω) {d : ℕ} {g : MvPolynomial (Fin N) K} (hg : g.IsHomogeneous d) :
    coneMap K y g = Polynomial.X ^ d * Polynomial.C (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [coneMap, map_sum, aeval_monomial, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hg (mem_support_iff.1 ha)
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
  rw [← this, Finsupp.degree_apply, mul_left_comm, Polynomial.algebraMap_apply]

/- English proof (translation)
Rewrite using `[coneIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous y hg, (Polynomial.monic_X_pow d).mul_right_eq_zero_iff, Polynomial.C_eq_zero]`.
-/
theorem mem_coneIdeal_of_isHomogeneous (y : Fin N → Ω) {d : ℕ} {g : MvPolynomial (Fin N) K}
    (hg : g.IsHomogeneous d) : g ∈ coneIdeal K y ↔ aeval y g = 0 := by
  rw [coneIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous y hg, (Polynomial.monic_X_pow d).mul_right_eq_zero_iff,
    Polynomial.C_eq_zero]

/- English proof (translation)
Use `conv_lhs => rw [← g.sum_homogeneousComponent, map_sum]`. Simplify using `only [coneMap_of_isHomogeneous y (homogeneousComponent_isHomogeneous _ g), Polynomial.finsetSum_coeff, Polynomial.X_pow_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[homogeneousComponent_eq_zero _ _ (by omega), map_zero]`.
-/
theorem coeff_coneMap (y : Fin N → Ω) (g : MvPolynomial (Fin N) K) (d : ℕ) :
    (coneMap K y g).coeff d = aeval y (homogeneousComponent d g) := by
  conv_lhs => rw [← g.sum_homogeneousComponent, map_sum]
  simp only [coneMap_of_isHomogeneous y (homogeneousComponent_isHomogeneous _ g), Polynomial.finsetSum_coeff,
    Polynomial.X_pow_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

/- English proof (translation)
Rewrite using `[coneIdeal, RingHom.mem_ker, Polynomial.ext_iff]`. Simplify using `only [coeff_coneMap, Polynomial.coeff_zero]`.
-/
theorem mem_coneIdeal_iff (y : Fin N → Ω) (g : MvPolynomial (Fin N) K) :
    g ∈ coneIdeal K y ↔ ∀ d, aeval y (homogeneousComponent d g) = 0 := by
  rw [coneIdeal, RingHom.mem_ker, Polynomial.ext_iff]
  simp only [coeff_coneMap, Polynomial.coeff_zero]

/- English proof (translation)
The claim follows from `RingHom.ker_isPrime _`.
-/
theorem isPrime_coneIdeal (y : Fin N → Ω) : (coneIdeal K y).IsPrime := RingHom.ker_isPrime _

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Introduce `d g hg` and use `by have e : ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g d : _) : MvPolynomial (Fin N) K) = homogeneousComponent d g := MvPolynomial.decomposition.decompose'_apply g d rw [e, mem_coneIdeal_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g)] exact (mem_coneIde …`.
-/
theorem isHomogeneous_coneIdeal (y : Fin N → Ω) :
    (coneIdeal K y).IsHomogeneous (homogeneousSubmodule (Fin N) K) := fun d g hg => by
  have e : ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g d : _) : MvPolynomial (Fin N) K) =
      homogeneousComponent d g := MvPolynomial.decomposition.decompose'_apply g d
  rw [e, mem_coneIdeal_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g)]
  exact (mem_coneIdeal_iff y g).1 hg d

/- English proof (translation)
Rewrite using `[← g.sum_homogeneousComponent, map_sum]`. Conclude with `Finset.sum_eq_zero fun d _ => (mem_coneIdeal_iff y g).1 hg d`.
-/
theorem aeval_eq_zero_of_mem_coneIdeal {y : Fin N → Ω} {g : MvPolynomial (Fin N) K} (hg : g ∈ coneIdeal K y) :
    aeval y g = 0 := by
  rw [← g.sum_homogeneousComponent, map_sum]
  exact Finset.sum_eq_zero fun d _ => (mem_coneIdeal_iff y g).1 hg d

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [mem_coneIdeal_iff]`. Use `forall_congr' fun d => ?_` and prove the remaining obligations. Establish `h` using `congrArg (Polynomial.eval a) (coneMap_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g))`. Establish `e : ((Polynomial.aeval a : Polynomial Ω →ₐ[Ω] Ω).restrictScalars K).comp (coneMap K y) = aeval (a • y)`.

Use extensionality with `j`. Simplify using `[coneMap, mul_comm a]`. Establish `h2` using `congrArg (fun φ => φ (homogeneousComponent d g)) e`. Simplify using `only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Polynomial.coe_aeval_eq_eval] at h2`. Rewrite using `[← h2, h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_eq_zero, or_iff_right (pow_ne_zero _ ha)]`.
-/
theorem coneIdeal_smul {a : Ω} (ha : a ≠ 0) (y : Fin N → Ω) : coneIdeal K (a • y) = coneIdeal K y := by
  ext g
  simp only [mem_coneIdeal_iff]
  refine forall_congr' fun d => ?_
  have h := congrArg (Polynomial.eval a) (coneMap_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g))
  have e : ((Polynomial.aeval a : Polynomial Ω →ₐ[Ω] Ω).restrictScalars K).comp (coneMap K y) = aeval (a • y) := by
    ext j; simp [coneMap, mul_comm a]
  have h2 := congrArg (fun φ => φ (homogeneousComponent d g)) e
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Polynomial.coe_aeval_eq_eval] at h2
  rw [← h2, h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_eq_zero,
    or_iff_right (pow_ne_zero _ ha)]

/- English proof (translation)
The claim follows from `le_bot_iff.1 fun g hg => h.eq_zero_of_aeval_eq_zero g (aeval_eq_zero_of_mem_coneIdeal hg)`.
-/
theorem coneIdeal_eq_bot {y : Fin N → Ω} (h : AlgebraicIndependent K y) : coneIdeal K y = ⊥ :=
  le_bot_iff.1 fun g hg => h.eq_zero_of_aeval_eq_zero g (aeval_eq_zero_of_mem_coneIdeal hg)

def coordSubst {N' : ℕ} (M : Matrix (Fin N) (Fin N') K) : MvPolynomial (Fin N') K →ₐ[K] MvPolynomial (Fin N) K :=
  aeval fun k => ∑ j, C (M j k) * X j

/- English proof (translation)
Establish `e : coneMap K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) = (coneMap K y).comp (coordSubst M)`. Use `MvPolynomial.algHom_ext fun k => ?_` and prove the remaining obligations. Simplify using `only [coneMap, coordSubst, aeval_X, AlgHom.comp_apply, map_sum, map_mul, aeval_C, Finset.mul_sum, Polynomial.algebraMap_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _`. Rewrite using `[coneIdeal, coneIdeal, RingHom.mem_ker, RingHom.mem_ker, e, AlgHom.comp_apply]`.
-/
theorem mem_coneIdeal_coord {N' : ℕ} (M : Matrix (Fin N) (Fin N') K) (y : Fin N → Ω) (g : MvPolynomial (Fin N') K) :
    g ∈ coneIdeal K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) ↔ coordSubst M g ∈ coneIdeal K y := by
  have e : coneMap K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) = (coneMap K y).comp (coordSubst M) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [coneMap, coordSubst, aeval_X, AlgHom.comp_apply, map_sum, map_mul, aeval_C, Finset.mul_sum,
      Polynomial.algebraMap_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
  rw [coneIdeal, coneIdeal, RingHom.mem_ker, RingHom.mem_ker, e, AlgHom.comp_apply]

end Cone

section Change

variable {K : Type} [Field K] {N N' : ℕ}

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply]`. Use `congr 1`. Conclude with `MvPolynomial.algHom_ext fun k => by simp [coordSubst]`.
-/
theorem aeval_coordSubst {Ω : Type} [CommRing Ω] [Algebra K Ω] (M : Matrix (Fin N) (Fin N') K) (y : Fin N → Ω)
    (g : MvPolynomial (Fin N') K) :
    aeval y (coordSubst M g) = aeval (fun k => ∑ j, algebraMap K Ω (M j k) * y j) g := by
  rw [← AlgHom.comp_apply]
  congr 1
  exact MvPolynomial.algHom_ext fun k => by simp [coordSubst]

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply]`. Establish `e : (coordSubst M).comp (coordSubst P) = AlgHom.id K _` using `MvPolynomial.algHom_ext fun j => by`. Simplify using `only [coordSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum, AlgHom.id_apply]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ i, ∑ k, C (P k j) * (C (M i k) * X i) = (C ((M * P) i j) * X i : MvPolynomial (Fin N) K)` using `fun i => by`.

Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `[this, h, Matrix.one_apply, apply_ite C]`. Rewrite using `[e, AlgHom.id_apply]`.
-/
theorem coordSubst_coordSubst {M : Matrix (Fin N) (Fin N') K} {P : Matrix (Fin N') (Fin N) K} (h : M * P = 1)
    (g : MvPolynomial (Fin N) K) : coordSubst M (coordSubst P g) = g := by
  rw [← AlgHom.comp_apply]
  have e : (coordSubst M).comp (coordSubst P) = AlgHom.id K _ := MvPolynomial.algHom_ext fun j => by
    simp only [coordSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum,
      AlgHom.id_apply]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ k, C (P k j) * (C (M i k) * X i) = (C ((M * P) i j) * X i : MvPolynomial (Fin N) K) := fun i => by
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp [this, h, Matrix.one_apply, apply_ite C]
  rw [e, AlgHom.id_apply]

/- English proof (translation)
Use `aeval_coordSubst M y (coordSubst P (X j))` as an intermediate fact. Rewrite `this` using `[coordSubst_coordSubst h, aeval_X, aeval_coordSubst, aeval_X]`. Conclude with `this.symm`.
-/
theorem sum_sum_eq {Ω : Type} [CommRing Ω] [Algebra K Ω] {M : Matrix (Fin N) (Fin N') K}
    {P : Matrix (Fin N') (Fin N) K} (h : M * P = 1) (y : Fin N → Ω) (j : Fin N) :
    ∑ k, algebraMap K Ω (P k j) * ∑ i, algebraMap K Ω (M i k) * y i = y j := by
  have := aeval_coordSubst M y (coordSubst P (X j))
  rw [coordSubst_coordSubst h, aeval_X, aeval_coordSubst, aeval_X] at this
  exact this.symm

/- English proof (translation)
Use `⟨HeightUnique.linSubst_homog M hf.homog, ?_, fun u => ?_⟩` and prove the remaining obligations. Set `e : MvPolynomial (Fin (D + 1) × Fin N) K ≃* MvPolynomial (Fin (D + 1) × Fin N') K` to `{ toFun := linSubst M, invFun := linSubst P left_inv := fun g => by rw [HeightUnique.linSubst_linSubst, h, HeightUnique.linSubst_one] right_inv := fun g => by rw [HeightUnique.linSubst_linSubst, h', HeightUnique.linSubst_one] map_mul' := fun a b => map_mul _ a b }`. Conclude with `(MulEquiv.irreducible_iff e).2 hf.irred`. Establish `e : aeval u (linSubst M f) = aeval (fun p : Fin (D + 1) × Fin N => ∑ k, algebraMap K _ (M p.2 k) * u (p.1, k)) f`. Rewrite using `[linSubst, ← AlgHom.comp_apply]`.

Use `congr 1`. Conclude with `MvPolynomial.algHom_ext fun k => by simp`. Establish `pair : ∀ (y : Fin N → AlgebraicClosure K) (i : Fin (D + 1)), ∑ j, (∑ k, algebraMap K _ (M j k) * u (i, k)) * y j = ∑ k, u (i, k) * ∑ j, algebraMap K _ (M j k) * y j` using `fun y i => by`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e, hf.zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h1, h2⟩`. Use `⟨fun k => ∑ j, algebraMap K _ (M j k) * y j, fun h0 => hy (funext fun j => ?_), fun g hg => ?_, fun i => (pair y i).symm.trans (h2 i)⟩` and prove the remaining obligations.

Rewrite using `[← sum_sum_eq h y j]`. Conclude with `Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ (congrFun h0 k)`. Rewrite using `[← aeval_coordSubst]`. Conclude with `h1 _ ((hI g).1 hg)`. Introduce and unpack `⟨y, hy, h1, h2⟩`.

Use `⟨fun j => ∑ k, algebraMap K _ (P k j) * y k, fun h0 => hy (funext fun k => ?_), fun g hg => ?_, fun i => (pair _ i).trans ?_⟩` and prove the remaining obligations. Rewrite using `[← sum_sum_eq h' y k]`. Conclude with `Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ (congrFun h0 j)`. Rewrite using `[← aeval_coordSubst]`. Conclude with `h1 _ ((hI _).2 (by rwa [coordSubst_coordSubst h]))`.

Simplify using `only [sum_sum_eq h' y]`. Conclude with `h2 i`.
-/
theorem isChowFormInt_linSubst {M : Matrix (Fin N) (Fin N') K} {P : Matrix (Fin N') (Fin N) K} (h : M * P = 1)
    (h' : P * M = 1) {I : Ideal (MvPolynomial (Fin N) K)} {I' : Ideal (MvPolynomial (Fin N') K)}
    (hI : ∀ g, g ∈ I' ↔ coordSubst M g ∈ I) {D δ : ℕ} {f : MvPolynomial (Fin (D + 1) × Fin N) K}
    (hf : IsChowFormInt I D δ f) : IsChowFormInt I' D δ (linSubst M f) := by
  refine ⟨HeightUnique.linSubst_homog M hf.homog, ?_, fun u => ?_⟩
  · let e : MvPolynomial (Fin (D + 1) × Fin N) K ≃* MvPolynomial (Fin (D + 1) × Fin N') K :=
      { toFun := linSubst M, invFun := linSubst P
        left_inv := fun g => by rw [HeightUnique.linSubst_linSubst, h, HeightUnique.linSubst_one]
        right_inv := fun g => by rw [HeightUnique.linSubst_linSubst, h', HeightUnique.linSubst_one]
        map_mul' := fun a b => map_mul _ a b }
    exact (MulEquiv.irreducible_iff e).2 hf.irred
  · have e : aeval u (linSubst M f) =
        aeval (fun p : Fin (D + 1) × Fin N => ∑ k, algebraMap K _ (M p.2 k) * u (p.1, k)) f := by
      rw [linSubst, ← AlgHom.comp_apply]
      congr 1
      exact MvPolynomial.algHom_ext fun k => by simp
    have pair : ∀ (y : Fin N → AlgebraicClosure K) (i : Fin (D + 1)),
        ∑ j, (∑ k, algebraMap K _ (M j k) * u (i, k)) * y j = ∑ k, u (i, k) * ∑ j, algebraMap K _ (M j k) * y j :=
      fun y i => by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e, hf.zero_iff]
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨fun k => ∑ j, algebraMap K _ (M j k) * y j, fun h0 => hy (funext fun j => ?_), fun g hg => ?_,
        fun i => (pair y i).symm.trans (h2 i)⟩
      · rw [← sum_sum_eq h y j]
        exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ (congrFun h0 k)
      · rw [← aeval_coordSubst]; exact h1 _ ((hI g).1 hg)
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨fun j => ∑ k, algebraMap K _ (P k j) * y k, fun h0 => hy (funext fun k => ?_), fun g hg => ?_,
        fun i => (pair _ i).trans ?_⟩
      · rw [← sum_sum_eq h' y k]
        exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ (congrFun h0 j)
      · rw [← aeval_coordSubst]
        exact h1 _ ((hI _).2 (by rwa [coordSubst_coordSubst h]))
      · simp only [sum_sum_eq h' y]; exact h2 i

end Change

section Image

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def imageIdeal (ev : V →ₗ[K] Ω) {N : ℕ} (b : Basis (Fin N) K V) : Ideal (MvPolynomial (Fin N) K) :=
  coneIdeal K fun j => ev (b j)

/- English proof (translation)
Use `isChowFormInt_linSubst (b.toMatrix_mul_toMatrix_flip b') (b'.toMatrix_mul_toMatrix_flip b) (fun g => ?_) hf` and prove the remaining obligations. Rewrite using `[imageIdeal, imageIdeal, ← mem_coneIdeal_coord]`. Use `congr! with k`. Rewrite using `[← congrArg ev (b.sum_toMatrix_smul_self b' k), map_sum]`. Simplify using `only [map_smul, Algebra.smul_def]`.
-/
theorem isChowFormInt_basis (ev : V →ₗ[K] Ω) {N N' : ℕ} (b : Basis (Fin N) K V) (b' : Basis (Fin N') K V) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (hf : IsChowFormInt (imageIdeal ev b) D δ f) :
    IsChowFormInt (imageIdeal ev b') D δ (linSubst (b.toMatrix b') f) := by
  refine isChowFormInt_linSubst (b.toMatrix_mul_toMatrix_flip b') (b'.toMatrix_mul_toMatrix_flip b) (fun g => ?_) hf
  rw [imageIdeal, imageIdeal, ← mem_coneIdeal_coord]
  congr! with k
  rw [← congrArg ev (b.sum_toMatrix_smul_self b' k), map_sum]
  simp only [map_smul, Algebra.smul_def]

def IsImageDeg (ev : V →ₗ[K] Ω) (D δ : ℕ) : Prop :=
  ∃ (N : ℕ) (b : Basis (Fin N) K V) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt (imageIdeal ev b) D δ f

/- English proof (translation)
Take `⟨N, b, f, hf⟩` from `h`. Take `⟨N', b', f', hf'⟩` from `h'`. Conclude with `((isChowFormInt_basis ev b b' hf).unique hf').1`.
-/
theorem IsImageDeg.unique {ev : V →ₗ[K] Ω} {D δ δ' : ℕ} (h : IsImageDeg ev D δ) (h' : IsImageDeg ev D δ') : δ = δ' := by
  obtain ⟨N, b, f, hf⟩ := h
  obtain ⟨N', b', f', hf'⟩ := h'
  exact ((isChowFormInt_basis ev b b' hf).unique hf').1

/- English proof (translation)
Take `⟨N, b, f, hf⟩` from `h`. Conclude with `hf.pos`.
-/
theorem IsImageDeg.pos {ev : V →ₗ[K] Ω} {D δ : ℕ} (h : IsImageDeg ev D δ) : 0 < δ := by
  obtain ⟨N, b, f, hf⟩ := h
  exact hf.pos

open Classical in

def imageDeg (ev : V →ₗ[K] Ω) (D : ℕ) : ℕ := if h : ∃ δ, IsImageDeg ev D δ then h.choose else 0

/- English proof (translation)
Establish `h' : ∃ δ, IsImageDeg ev D δ` using `⟨δ, h⟩`. Rewrite using `[imageDeg, dif_pos h']`. Conclude with `h'.choose_spec.unique h`.
-/
theorem IsImageDeg.imageDeg_eq {ev : V →ₗ[K] Ω} {D δ : ℕ} (h : IsImageDeg ev D δ) : imageDeg ev D = δ := by
  have h' : ∃ δ, IsImageDeg ev D δ := ⟨δ, h⟩
  rw [imageDeg, dif_pos h']
  exact h'.choose_spec.unique h

/- English proof (translation)
Use `⟨fun h => ?_, IsImageDeg.pos⟩` and prove the remaining obligations. Distinguish the cases in `h' : ∃ δ, IsImageDeg ev D δ`. Take `⟨δ, hδ⟩` from `h'`. Rewrite using `[hδ.imageDeg_eq]` and apply the resulting hypothesis. Rewrite `h` using `[imageDeg, dif_neg h']`.

Conclude with `absurd h (lt_irrefl 0)`.
-/
theorem imageDeg_pos_iff (ev : V →ₗ[K] Ω) (D : ℕ) : 0 < imageDeg ev D ↔ IsImageDeg ev D (imageDeg ev D) := by
  refine ⟨fun h => ?_, IsImageDeg.pos⟩
  by_cases h' : ∃ δ, IsImageDeg ev D δ
  · obtain ⟨δ, hδ⟩ := h'
    rwa [hδ.imageDeg_eq]
  · rw [imageDeg, dif_neg h'] at h
    exact absurd h (lt_irrefl 0)

variable [NumberField K] [Module (𝓞 K) V]

structure IsFrame (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) {N n : ℕ} (b : Basis (Fin N) K V)
    (w : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop where

  span : Submodule.span (𝓞 K) (Set.range fun k => ∑ j, w j k • b j) = L

  full : Submodule.span K (Set.range w.col) = ⊤

  herm : ∀ σ, (A σ).det ≠ 0

  conj : ConjCompat A

  norm : ∀ (σ : K →+* ℂ) (x : V), frameNorm (A σ) (fun j => σ (b.repr x j)) = Nm σ x

def IsImageHeight (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (h : ℝ) : Prop :=
  ∃ (N n : ℕ) (b : Basis (Fin N) K V) (w : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsFrame Nm L b w A ∧ IsChowFormInt (imageIdeal ev b) D δ f ∧
      ((D : ℝ) + 1) * δ * h = formHeight δ w A f

open Classical in

def imageHeight (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) : ℝ :=
  if h : ∃ x, IsImageHeight Nm L ev D x then h.choose else 0

variable {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V} {ev : V →ₗ[K] Ω} {D : ℕ}

/- English proof (translation)
Rewrite using `[imageHeight, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem isImageHeight_imageHeight (h : ∃ x, IsImageHeight Nm L ev D x) :
    IsImageHeight Nm L ev D (imageHeight Nm L ev D) := by
  rw [imageHeight, dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, N, n, b, w, A, δ, f, hF, hf, -⟩`. Conclude with `⟨⟨N, n, b, w, A, hF⟩, IsImageDeg.imageDeg_eq ⟨N, b, f, hf⟩ ▸ hf.pos⟩`. Introduce and unpack `⟨⟨N, n, b, w, A, hF⟩, hd⟩`. Take `⟨N', b', f, hf⟩` from `(imageDeg_pos_iff ev D).1 hd`.

Use `⟨formHeight (imageDeg ev D) w A (linSubst (b'.toMatrix b) f) / (((D : ℝ) + 1) * imageDeg ev D), N, n, b, w, A, _, _, hF, isChowFormInt_basis ev b' b hf, ?_⟩` and prove the remaining obligations. Conclude with `mul_div_cancel₀ _ (mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hd.ne'))`.
-/
theorem exists_isImageHeight_iff : (∃ x, IsImageHeight Nm L ev D x) ↔
    (∃ (N n : ℕ) (b : Basis (Fin N) K V) (w : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
      IsFrame Nm L b w A) ∧ 0 < imageDeg ev D := by
  constructor
  · rintro ⟨x, N, n, b, w, A, δ, f, hF, hf, -⟩
    exact ⟨⟨N, n, b, w, A, hF⟩, IsImageDeg.imageDeg_eq ⟨N, b, f, hf⟩ ▸ hf.pos⟩
  · rintro ⟨⟨N, n, b, w, A, hF⟩, hd⟩
    obtain ⟨N', b', f, hf⟩ := (imageDeg_pos_iff ev D).1 hd
    refine ⟨formHeight (imageDeg ev D) w A (linSubst (b'.toMatrix b) f) / (((D : ℝ) + 1) * imageDeg ev D), N, n, b, w, A,
      _, _, hF, isChowFormInt_basis ev b' b hf, ?_⟩
    exact mul_div_cancel₀ _ (mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hd.ne'))

def Presents (T : Adelic.HermSys K) (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) : Prop :=
  ∃ b : Basis (Fin T.N) K V, IsFrame Nm L b T.w T.A ∧ T.imageIdeal = imageIdeal ev b

/- English proof (translation)
Take `⟨b, hF, hI⟩` from `hT`. Take `⟨δ, f, -, hf, e⟩` from `hh`. Conclude with `⟨_, _, b, T.w, T.A, δ, f, hF, hI ▸ hf.isChowFormInt, e⟩`.
-/
theorem Presents.isImageHeight {T : Adelic.HermSys K} (hT : Presents T Nm L ev) {h : ℝ} (hh : T.IsHeight h) :
    IsImageHeight Nm L ev T.D h := by
  obtain ⟨b, hF, hI⟩ := hT
  obtain ⟨δ, f, -, hf, e⟩ := hh
  exact ⟨_, _, b, T.w, T.A, δ, f, hF, hI ▸ hf.isChowFormInt, e⟩

/- English proof (translation)
Take `⟨b, -, hI⟩` from `hT`. Conclude with `IsImageDeg.imageDeg_eq ⟨_, b, f, hI ▸ hf⟩`.
-/
theorem Presents.imageDeg_eq {T : Adelic.HermSys K} (hT : Presents T Nm L ev) {δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin T.N) K} (hf : IsChowFormInt T.imageIdeal D δ f) : imageDeg ev D = δ := by
  obtain ⟨b, -, hI⟩ := hT
  exact IsImageDeg.imageDeg_eq ⟨_, b, f, hI ▸ hf⟩

end Image

section Model

abbrev StdField (N : ℕ) : Type := FractionRing (MvPolynomial (Fin N) ℚ)

def pointOf (K : Type) [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {N : ℕ} (y : Fin N → Ω) : (Fin N → K) →ₗ[K] Ω :=
  (Pi.basisFun K (Fin N)).constr K y

/- English proof (translation)
Simplify using `only [imageIdeal, pointOf, Basis.constr_basis]`.
-/
theorem imageIdeal_pointOf (K : Type) [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {N : ℕ} (y : Fin N → Ω) :
    imageIdeal (pointOf K y) (Pi.basisFun K (Fin N)) = coneIdeal K y := by
  simp only [imageIdeal, pointOf, Basis.constr_basis]

abbrev stdPoint (N : ℕ) := pointOf ℚ fun j : Fin N => algebraMap (MvPolynomial (Fin N) ℚ) (StdField N) (X j)

def stdNorm (N : ℕ) (σ : ℚ →+* ℂ) (x : Fin N → ℚ) : ℝ := Real.sqrt (∑ j, ‖σ (x j)‖ ^ 2)

def stdLat (N : ℕ) : Submodule (𝓞 ℚ) (Fin N → ℚ) := Submodule.span (𝓞 ℚ) (Set.range (Pi.basisFun ℚ (Fin N)))

/- English proof (translation)
Rewrite using `[imageIdeal_pointOf]`. Conclude with `coneIdeal_eq_bot <| (MvPolynomial.algebraicIndependent_X (Fin N) ℚ).map' (f := (algebraMap (MvPolynomial (Fin N) ℚ) (StdField N)).toRatAlgHom) (IsFractionRing.injective _ _)`.
-/
theorem imageIdeal_std (N : ℕ) : imageIdeal (stdPoint N) (Pi.basisFun ℚ (Fin N)) = ⊥ := by
  rw [imageIdeal_pointOf]
  exact coneIdeal_eq_bot <| (MvPolynomial.algebraicIndependent_X (Fin N) ℚ).map'
    (f := (algebraMap (MvPolynomial (Fin N) ℚ) (StdField N)).toRatAlgHom) (IsFractionRing.injective _ _)

end Model

section Weights

variable {ι : Type} [Fintype ι] {N : ℕ}

def vdm {R : Type} [CommRing R] (la : ι → Fin N → R) : R := ∏ τ, ∏ i, ∏ l ∈ Finset.Ioi i, (la τ i - la τ l)

/- English proof (translation)
Simplify using `[vdm, map_prod]`.
-/
theorem map_vdm {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (la : ι → Fin N → R) :
    φ (vdm la) = vdm fun τ i => φ (la τ i) := by
  simp [vdm, map_prod]

/- English proof (translation)
The claim follows from `Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hl => sub_pos.2 (h τ (Finset.mem_Ioi.1 hl))`.
-/
theorem vdm_pos {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {la : ι → Fin N → R}
    (h : ∀ τ, StrictAnti (la τ)) : 0 < vdm la :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hl =>
    sub_pos.2 (h τ (Finset.mem_Ioi.1 hl))

/- English proof (translation)
Establish `h : ∑ i : Fin N, (Finset.Ioi i).card = N * (N - 1) / 2`. Simplify using `only [Fin.card_Ioi]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]`. Simplify using `only [vdm, Pi.smul_apply, smul_eq_mul, ← mul_sub, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, h, ← pow_mul, Finset.card_univ, Formalism.DegreeFormula.dimFl, mul_comm]`.
-/
theorem vdm_smul {R : Type} [CommRing R] (t : R) (la : ι → Fin N → R) :
    vdm (t • la) = t ^ Formalism.DegreeFormula.dimFl ι N * vdm la := by
  have h : ∑ i : Fin N, (Finset.Ioi i).card = N * (N - 1) / 2 := by
    simp only [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
      Finset.sum_range_id]
  simp only [vdm, Pi.smul_apply, smul_eq_mul, ← mul_sub, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, h, ← pow_mul, Finset.card_univ, Formalism.DegreeFormula.dimFl, mul_comm]

def stdWt (ι : Type) (N : ℕ) : ι → Fin N → ℤ := fun _ i => (N : ℤ) - 1 - (i : ℕ)

omit [Fintype ι] in

/- English proof (translation)
Introduce `i l h` and use `by have : (i : ℕ) < l := h simp only [stdWt]; omega`.
-/
theorem strictAnti_stdWt (τ : ι) : StrictAnti (stdWt ι N τ) := fun i l h => by
  have : (i : ℕ) < l := h
  simp only [stdWt]; omega

/- English proof (translation)
Rewrite using `[show ((vdm (stdWt ι N) : ℤ) : ℝ) = _ from map_vdm (Int.castRingHom ℝ) _]`. Simplify using `only [Formalism.DegreeFormula.weylProd, vdm, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `Finset.prod_congr (by ext; simp) fun k _ => ?_` and prove the remaining obligations.

Simplify using `[stdWt]`.
-/
theorem weylProd_eq (la : ι → Fin N → ℝ) : Formalism.DegreeFormula.weylProd la = vdm la / (vdm (stdWt ι N) : ℤ) := by
  rw [show ((vdm (stdWt ι N) : ℤ) : ℝ) = _ from map_vdm (Int.castRingHom ℝ) _]
  simp only [Formalism.DegreeFormula.weylProd, vdm, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr (by ext; simp) fun k _ => ?_
  simp [stdWt]

def barWt (ι : Type) (N p : ℕ) : ι → Fin N → ℤ := fun _ i => if (i : ℕ) < p then 0 else -1

def rhoOf (u' u : ι → Fin N → ℤ) : ℝ := 1 - (vdm u' : ℤ) / (vdm u : ℤ)

/- English proof (translation)
Rewrite using `[rhoOf, sub_sub_cancel, div_mul_cancel₀ _ (Int.cast_ne_zero.2 h)]`.
-/
theorem one_sub_rhoOf_mul {u' u : ι → Fin N → ℤ} (h : vdm u ≠ 0) :
    (1 - rhoOf u' u) * (vdm u : ℤ) = (vdm u' : ℤ) := by
  rw [rhoOf, sub_sub_cancel, div_mul_cancel₀ _ (Int.cast_ne_zero.2 h)]

/- English proof (translation)
The claim follows from `sub_lt_self _ (div_pos (Int.cast_pos.2 (vdm_pos h')) (Int.cast_pos.2 (vdm_pos h)))`.
-/
theorem rhoOf_lt_one {u' u : ι → Fin N → ℤ} (h' : ∀ τ, StrictAnti (u' τ)) (h : ∀ τ, StrictAnti (u τ)) :
    rhoOf u' u < 1 :=
  sub_lt_self _ (div_pos (Int.cast_pos.2 (vdm_pos h')) (Int.cast_pos.2 (vdm_pos h)))

/- English proof (translation)
Evaluate the decidable proposition.
-/
example : vdm (fun _ : Unit => ![(5 : ℤ), 2, 0]) = 30 := by decide

/- English proof (translation)
Establish `h1 : vdm ((fun _ : Unit => ![(0 : ℤ), -8]) - (6 : ℤ) • barWt Unit 2 1) = 2` using `by decide`. Establish `h2 : vdm (fun _ : Unit => ![(0 : ℤ), -8]) = 8` using `by decide`. Rewrite using `[rhoOf, h1, h2]`. Evaluate the numerical expressions.
-/
example : rhoOf ((fun _ : Unit => ![(0 : ℤ), -8]) - (6 : ℤ) • barWt Unit 2 1) (fun _ => ![0, -8]) = 3 / 4 := by
  have h1 : vdm ((fun _ : Unit => ![(0 : ℤ), -8]) - (6 : ℤ) • barWt Unit 2 1) = 2 := by decide
  have h2 : vdm (fun _ : Unit => ![(0 : ℤ), -8]) = 8 := by decide
  rw [rhoOf, h1, h2]; norm_num

end Weights

def cStar (n : ℕ) (abelian₂ : ℝ) : ℝ := Real.log (Real.sqrt n * abelian₂)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Real.log_nonneg hL, Real.log_le_log (by linarith) (le_mul_of_one_le_left (by linarith) (Real.one_le_sqrt.2 (by exact_mod_cast hn)))⟩`.
-/
theorem log_le_cStar {n : ℕ} {abelian₂ : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ abelian₂) : 0 ≤ Real.log abelian₂ ∧ Real.log abelian₂ ≤ cStar n abelian₂ :=
  ⟨Real.log_nonneg hL, Real.log_le_log (by linarith)
    (le_mul_of_one_le_left (by linarith) (Real.one_le_sqrt.2 (by exact_mod_cast hn)))⟩

section Growth

def growth (D : ℕ) (r : ℕ → ℕ∞) : ℝ≥0∞ :=
  limsup (fun τ : ℕ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D) atTop

def logCard (m : ℕ∞) : ℝ≥0∞ := (ENNReal.log (m : ℝ≥0∞)).toENNReal

/- English proof (translation)
Break down `m.eq_zero_or_pos with rfl | hm` into its components or cases. Simplify using `[logCard]`. Rewrite using `[logCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos (Nat.cast_pos.2 hm)]`. Simplify using the standard rewrite rules.
-/
theorem logCard_coe (m : ℕ) : logCard m = ENNReal.ofReal (Real.log m) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [logCard]
  · rw [logCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos (Nat.cast_pos.2 hm)]
    simp

/- English proof (translation)
Simplify using `[logCard]`.
-/
theorem logCard_top : logCard ⊤ = ⊤ := by simp [logCard]

def countVol (D d a : ℕ) (m : ℕ → ℕ∞) : ℝ≥0∞ :=
  limsup (fun k : ℕ => (D.factorial : ℝ≥0∞) * logCard (m (a * k)) / ((d : ℝ≥0∞) * ((a * k : ℕ) : ℝ≥0∞) ^ (D + 1))) atTop

/- English proof (translation)
The claim follows from `limsup_le_limsup (Eventually.of_forall fun k => ENNReal.div_le_div_right (mul_le_mul_right (EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (h _)))) _) _)`.
-/
theorem countVol_mono (D d a : ℕ) {m m' : ℕ → ℕ∞} (h : ∀ τ, m τ ≤ m' τ) : countVol D d a m ≤ countVol D d a m' :=
  limsup_le_limsup (Eventually.of_forall fun k => ENNReal.div_le_div_right (mul_le_mul_right
    (EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (h _)))) _) _)

def volSlope (δ : ℝ) (vol : ℝ → ℝ≥0∞) : EReal := ⨅ t : ℝ, ((vol t / ENNReal.ofReal δ : ℝ≥0∞) : EReal) - (t : EReal)

/- English proof (translation)
Rewrite using `[volSlope, le_iInf_iff]`. Use `forall_congr' fun t => ?_` and prove the remaining obligations. Rewrite using `[EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t)), ← EReal.coe_add, ENNReal.ofReal_mul hδ.le, mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hδ).ne') (Or.inl ENNReal.ofReal_ne_top), ← EReal.coe_ennreal_le_coe_ennreal_iff, ER …`. Conclude with `⟨fun h => by`. Break down `le_total (a + t) 0 with h0 | h0` into its components or cases.

Rewrite using `[max_eq_right h0]`. Conclude with `EReal.coe_ennreal_nonneg _`. Rewrite using `[max_eq_left h0], fun h => (EReal.coe_le_coe_iff.2 (le_max_left _ _)).trans h⟩` and apply the resulting hypothesis.
-/
theorem le_volSlope_iff {δ : ℝ} (hδ : 0 < δ) (vol : ℝ → ℝ≥0∞) (a : ℝ) :
    (a : EReal) ≤ volSlope δ vol ↔ ∀ t : ℝ, ENNReal.ofReal (δ * (a + t)) ≤ vol t := by
  rw [volSlope, le_iInf_iff]
  refine forall_congr' fun t => ?_
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t)), ← EReal.coe_add,
    ENNReal.ofReal_mul hδ.le, mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hδ).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_ofReal]
  exact ⟨fun h => by
    rcases le_total (a + t) 0 with h0 | h0
    · rw [max_eq_right h0]; exact EReal.coe_ennreal_nonneg _
    · rwa [max_eq_left h0], fun h => (EReal.coe_le_coe_iff.2 (le_max_left _ _)).trans h⟩

def degSlope (a : ℕ) (dg : ℕ → ℝ) (r : ℕ → ℕ) : EReal :=
  liminf (fun k : ℕ => ((dg (a * k) / (((a * k : ℕ) : ℝ) * r (a * k)) : ℝ) : EReal)) atTop

def IsLimSlope (D : ℕ) (ar geo : ℚ → ℝ) (a : ℝ) : Prop :=
  (∀ᶠ s : ℚ in 𝓝[>] 0, 0 < geo s) ∧ Tendsto (fun s : ℚ => ar s / (((D : ℝ) + 1) * geo s)) (𝓝[>] 0) (𝓝 a)

/- English proof (translation)
The claim follows from `tendsto_nhds_unique ha.2 hb.2`.
-/
theorem IsLimSlope.unique {D : ℕ} {ar geo : ℚ → ℝ} {a b : ℝ} (ha : IsLimSlope D ar geo a)
    (hb : IsLimSlope D ar geo b) : a = b :=
  tendsto_nhds_unique ha.2 hb.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨Eventually.of_forall fun _ => one_pos, by norm_num⟩`.
-/
example : IsLimSlope 1 (fun _ => 6) (fun _ => 1) 3 :=
  ⟨Eventually.of_forall fun _ => one_pos, by norm_num⟩

/- English proof (translation)
Rewrite using `[growth, ← limsup_const (f := (atTop : Filter ℕ)) (1 : ℝ≥0∞)]`. Use `limsup_congr ((eventually_ne_atTop 0).mono fun k hk => ?_)` and prove the remaining obligations. Simplify using `using ENNReal.div_self (Nat.cast_ne_zero.2 hk) (ENNReal.natCast_ne_top k)`.
-/
example : growth 1 (fun τ => τ) = 1 := by
  rw [growth, ← limsup_const (f := (atTop : Filter ℕ)) (1 : ℝ≥0∞)]
  refine limsup_congr ((eventually_ne_atTop 0).mono fun k hk => ?_)
  simpa using ENNReal.div_self (Nat.cast_ne_zero.2 hk) (ENNReal.natCast_ne_top k)

end Growth

end GlobalTheory.CompHt
