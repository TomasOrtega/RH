import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per

namespace GlobalTheory.ConjNorm

/- English proof (translation)
Establish `e : M = (1 + W * ((Y - 1) * V)) * ((1 - W * V) * M + W * V)`. Establish `h3 : ∀ X : Matrix m n D, V * (W * X) = X` using `fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc, h3, h2]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.det_mul, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one, add_sub_cancel]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem det_dvd_det {D : Type*} [CommRing D] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n D) (W : Matrix n m D) (M : Matrix n n D) (Y : Matrix m m D) (h1 : V * W = 1)
    (h2 : V * M = Y * V) : Y.det ∣ M.det := by
  have e : M = (1 + W * ((Y - 1) * V)) * ((1 - W * V) * M + W * V) := by
    have h3 : ∀ X : Matrix m n D, V * (W * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc,
      h3, h2]
    abel
  rw [e, Matrix.det_mul, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one, add_sub_cancel]
  exact dvd_mul_right _ _

section Norm

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/- English proof (translation)
Establish `hr : ∀ y i, b'.repr (F y) i = f (b.repr y i)` using `fun y i => by conv_lhs => rw [← b.sum_repr y]`. Simplify using `only [map_sum, Algebra.smul_def, map_mul, hf, hb]`. Simplify using `[← Algebra.smul_def, Finsupp.single_apply]`. Rewrite using `[Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]`.
-/
theorem norm_map {A' S' ι : Type*} [CommRing A'] [CommRing S'] [Algebra A' S'] [Fintype ι]
    (b : Module.Basis ι A S) (b' : Module.Basis ι A' S') (f : A →+* A') (F : S →+* S')
    (hf : ∀ a, F (algebraMap A S a) = algebraMap A' S' (f a)) (hb : ∀ i, F (b i) = b' i) (x : S) :
    Algebra.norm A' (F x) = f (Algebra.norm A x) := by
  classical
  have hr : ∀ y i, b'.repr (F y) i = f (b.repr y i) := fun y i => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, hf, hb]
    simp [← Algebra.smul_def, Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis A S`. Establish `hr : ∀ i y, ∑ k, φ i (b k) * ψ (b.repr y k) = φ i y` using `fun i y => by conv_rhs => rw [← b.sum_repr y]`. Simplify using `only [map_sum, Algebra.smul_def, map_mul, h, mul_comm]`. Rewrite using `[Algebra.norm_eq_matrix_det b, RingHom.map_det, ← Matrix.det_diagonal]`. Use `det_dvd_det (Matrix.of fun i k => φ i (b k)) ((Matrix.of fun k j => ψ (b.repr (c j) k)) * (Matrix.of fun i k => φ i (c k))⁻¹) _ _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_nonsing_inv _ hc]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `hr i (c j)`. Use extensionality with `i k`.

Rewrite using `[Matrix.diagonal_mul, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← hr]`. Simplify using `only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]`.
-/
theorem prod_dvd_norm [Module.Free A S] [Module.Finite A S] {D m : Type*} [CommRing D] [Fintype m] [DecidableEq m]
    (φ : m → S →+* D) (ψ : A →+* D) (h : ∀ i a, φ i (algebraMap A S a) = ψ a) (c : m → S)
    (hc : IsUnit (Matrix.of fun i k => φ i (c k)).det) (x : S) : ∏ i, φ i x ∣ ψ (Algebra.norm A x) := by
  classical
  let b := Module.Free.chooseBasis A S
  have hr : ∀ i y, ∑ k, φ i (b k) * ψ (b.repr y k) = φ i y := fun i y => by
    conv_rhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, h, mul_comm]
  rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ← Matrix.det_diagonal]
  refine det_dvd_det (Matrix.of fun i k => φ i (b k))
    ((Matrix.of fun k j => ψ (b.repr (c j) k)) * (Matrix.of fun i k => φ i (c k))⁻¹) _ _ ?_ ?_
  · rw [← Matrix.mul_assoc, ← Matrix.mul_nonsing_inv _ hc]
    congr 1
    ext i j
    exact hr i (c j)
  · ext i k
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← hr]
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]

/- English proof (translation)
Simplify using `using prod_dvd_norm (fun _ : Unit => RingHom.id S) (algebraMap A S) (fun _ _ => rfl) (fun _ => 1) (by simp) x`.
-/
theorem dvd_norm [Module.Free A S] [Module.Finite A S] (x : S) : x ∣ algebraMap A S (Algebra.norm A x) := by
  simpa using prod_dvd_norm (fun _ : Unit => RingHom.id S) (algebraMap A S) (fun _ _ => rfl) (fun _ => 1)
    (by simp) x

/- English proof (translation)
Apply the tactic sequence `simpa using prod_dvd_norm ![φ₁, φ₂] (φ₁.comp (algebraMap A S)) (fun i a => by fin_cases i <;> simp [h]) ![1, c] (by simpa [Matrix.det_fin_two] using hc) x`.
-/
theorem mul_dvd_norm [Module.Free A S] [Module.Finite A S] {D : Type*} [CommRing D] (φ₁ φ₂ : S →+* D)
    (h : ∀ a, φ₂ (algebraMap A S a) = φ₁ (algebraMap A S a)) (c : S) (hc : IsUnit (φ₂ c - φ₁ c)) (x : S) :
    φ₁ x * φ₂ x ∣ φ₁ (algebraMap A S (Algebra.norm A x)) := by
  simpa using prod_dvd_norm ![φ₁, φ₂] (φ₁.comp (algebraMap A S)) (fun i a => by fin_cases i <;> simp [h])
    ![1, c] (by simpa [Matrix.det_fin_two] using hc) x

end Norm

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

/- English proof (translation)
Use `haveI : FaithfulSMul (W0 K) ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (thetaW_injective K)`. Use `haveI : CharZero (W0 K) := (algebraMap (W0 K) ↥(OL K)).charZero`. Set `P` to `IsLocalRing.maximalIdeal ↥(OL K)`. Set `p` to `IsLocalRing.maximalIdeal (W0 K)`. Use `haveI hlo : P.LiesOver p := by`.

Prove the components needed by the constructor for the conclusion. Establish `: (P.under (W0 K)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Conclude with `(IsLocalRing.eq_maximalIdeal this).symm`. Establish `hrel` using `Ideal.relNorm_eq_pow_of_isMaximal P p`. Establish `hf : P.inertiaDeg (W0 K) = 1`.

Rewrite using `[Ideal.inertiaDeg_eq_of_isMaximal p P]`. Use `letI := Ideal.Quotient.field p`. Use `letI := Ideal.Quotient.field P`. Use `Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨RingHom.injective _, fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Take `⟨w, hw⟩` from `exists_thetaW (card_res K) x`. Conclude with `⟨Ideal.Quotient.mk _ w, hw⟩`. Establish `hP : P = Ideal.span {π}` using `hπ.maximalIdeal_eq`. Establish `hp : p = Ideal.span {(l : W0 K)}` using `(WittVector.irreducible l).maximalIdeal_eq`. Rewrite `hrel` using `[hf, pow_one, hP, Ideal.relNorm_singleton, hp, Algebra.intNorm_eq_norm]`.

Take `⟨u, hu⟩` from `Ideal.span_singleton_eq_span_singleton.mp hrel.symm`. Conclude with `⟨u, u.isUnit, hu.symm⟩`.
-/
theorem norm_unif {π : ↥(OL K)} (hπ : Irreducible π) :
    ∃ u : W0 K, IsUnit u ∧ Algebra.norm (W0 K) π = (l : W0 K) * u := by
  haveI : FaithfulSMul (W0 K) ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (thetaW_injective K)
  haveI : CharZero (W0 K) := (algebraMap (W0 K) ↥(OL K)).charZero
  let P := IsLocalRing.maximalIdeal ↥(OL K)
  let p := IsLocalRing.maximalIdeal (W0 K)
  haveI hlo : P.LiesOver p := by
    constructor
    have : (P.under (W0 K)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hrel := Ideal.relNorm_eq_pow_of_isMaximal P p
  have hf : P.inertiaDeg (W0 K) = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
    letI := Ideal.Quotient.field p
    letI := Ideal.Quotient.field P
    refine Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, hw⟩ := exists_thetaW (card_res K) x
    exact ⟨Ideal.Quotient.mk _ w, hw⟩
  have hP : P = Ideal.span {π} := hπ.maximalIdeal_eq
  have hp : p = Ideal.span {(l : W0 K)} := (WittVector.irreducible l).maximalIdeal_eq
  rw [hf, pow_one, hP, Ideal.relNorm_singleton, hp, Algebra.intNorm_eq_norm] at hrel
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hrel.symm
  exact ⟨u, u.isUnit, hu.symm⟩

/- English proof (translation)
Take `⟨f⟩` from `GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt l`. Establish `hr : ∀ x : Fq l (fK K), ∃ y, f y = Fq.val l (fK K) x` using `fun x => by`. Establish `h1` using `one_lt_pow_l l (fK K)`. Establish `hm : (Polynomial.X ^ l ^ fK K - Polynomial.X : Polynomial (AlgebraicClosure (ZMod l))).Monic` using `Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)`. Establish `h2` using `congrArg (Polynomial.eval₂ f (Fq.val l (fK K) x)) ((IsAlgClosed.splits _).eq_prod_roots_of_monic hm)`.

Rewrite `h2` using `[Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, ← map_pow, Fq.pow_card, sub_self, Polynomial.eval₂_multiset_prod, eq_comm, Multiset.prod_eq_zero_iff, Multiset.map_map]`. Take `⟨y, -, hy⟩` from `Multiset.mem_map.1 h2`. Use `⟨y, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy`. Conclude with `(sub_eq_zero.1 hy).symm`.

Use `choose r hr using hr`. Set `u' : WittVector l (AlgebraicClosure (ZMod l))` to `WittVector.mk l fun n => r (u.coeff n)`. Establish `hfu : WittVector.map f u' = wA l (fK K) u` using `WittVector.ext fun n => hr (u.coeff n)`. Establish `hu' : IsUnit u'` using `WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => by`. Establish `h0 : u.coeff 0 ≠ 0` using `(hu.map (WittVector.constantCoeff (p := l) (R := Fq l (fK K)))).ne_zero`.

Establish `h1` using `hr (u.coeff 0)`. Rewrite `h1` using `[show r (u.coeff 0) = 0 from h, map_zero, eq_comm, map_eq_zero]`. Conclude with `h0 h1`. Take `⟨w, hw, hφ⟩` from `GlobalTheory.MemLoc.exists_unit_frobenius_eq_mul l _ u' hu'`. Use `⟨WittVector.map f w, hw.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hfu, ← map_mul, ← hφ]`. Use `WittVector.ext fun n => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.AinfK.coeff_iter 1 (WittVector.map f w) n`. Rewrite `h` using `[Function.iterate_one, pow_one]`. Rewrite using `[h, WittVector.map_coeff, WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]`.
-/
theorem exists_lang (u : W0 K) (hu : IsUnit u) :
    ∃ a : Per.Ainf l, IsUnit a ∧ Per.φA l a = wA l (fK K) u * a := by
  obtain ⟨f⟩ := GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt l
  have hr : ∀ x : Fq l (fK K), ∃ y, f y = Fq.val l (fK K) x := fun x => by
    have h1 := one_lt_pow_l l (fK K)
    have hm : (Polynomial.X ^ l ^ fK K - Polynomial.X : Polynomial (AlgebraicClosure (ZMod l))).Monic :=
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)
    have h2 := congrArg (Polynomial.eval₂ f (Fq.val l (fK K) x))
      ((IsAlgClosed.splits _).eq_prod_roots_of_monic hm)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, ← map_pow, Fq.pow_card, sub_self,
      Polynomial.eval₂_multiset_prod, eq_comm, Multiset.prod_eq_zero_iff, Multiset.map_map] at h2
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 h2
    refine ⟨y, ?_⟩
    simp only [Function.comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy
    exact (sub_eq_zero.1 hy).symm
  choose r hr using hr
  let u' : WittVector l (AlgebraicClosure (ZMod l)) := WittVector.mk l fun n => r (u.coeff n)
  have hfu : WittVector.map f u' = wA l (fK K) u := WittVector.ext fun n => hr (u.coeff n)
  have hu' : IsUnit u' := WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => by
    have h0 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := Fq l (fK K)))).ne_zero
    have h1 := hr (u.coeff 0)
    rw [show r (u.coeff 0) = 0 from h, map_zero, eq_comm, map_eq_zero] at h1
    exact h0 h1
  obtain ⟨w, hw, hφ⟩ := GlobalTheory.MemLoc.exists_unit_frobenius_eq_mul l _ u' hu'
  refine ⟨WittVector.map f w, hw.map _, ?_⟩
  rw [← hfu, ← map_mul, ← hφ]
  refine WittVector.ext fun n => ?_
  have h := GlobalTheory.AinfK.coeff_iter 1 (WittVector.map f w) n
  rw [Function.iterate_one, pow_one] at h
  rw [h, WittVector.map_coeff, WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

end GlobalTheory.ConjNorm

end
