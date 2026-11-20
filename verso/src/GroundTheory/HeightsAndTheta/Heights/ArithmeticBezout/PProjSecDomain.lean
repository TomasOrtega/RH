import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjSecDomain

abbrev Kf (e : ℕ) : Type := FractionRing (MvPolynomial (Fin (e + 1)) ℂ)

variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)

abbrev S : Type :=
  Vertical.SecAlg (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)

/- English proof (translation)
Simplify using `[ComplexSets.linPoly, linForm, map_sum]`.
-/
theorem map_linPoly (k : Fin (e + 1)) :
    MvPolynomial.map (algebraMap ℂ (Kf e)) (ComplexSets.linPoly A k) =
      linForm fun j => algebraMap ℂ (Kf e) (A k j) := by
  simp [ComplexSets.linPoly, linForm, map_sum]

/- English proof (translation)
Rewrite using `[projVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `X_ne_zero k`.
-/
theorem projVar_ne_zero (k : Fin (e + 1)) : projVar e k ≠ 0 := by
  rw [projVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact X_ne_zero k

/- English proof (translation)
Simplify using `[Vertical.chartForm, linForm, projPar, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm]`.
-/
theorem chartForm_eq : Vertical.chartForm (projPar A) =
    C (projVar e 0)⁻¹ * linForm fun j => algebraMap ℂ (Kf e) (A 0 j) := by
  simp [Vertical.chartForm, linForm, projPar, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm]

/- English proof (translation)
Simplify using `[Vertical.secForm, linForm, projPar, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]`.
-/
theorem secForm_eq (i : Fin e) : Vertical.secForm (projPar A) i =
    C (projVar e i.succ) * (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) -
      C (projVar e 0) * linForm fun j => algebraMap ℂ (Kf e) (A i.succ j) := by
  simp [Vertical.secForm, linForm, projPar, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]

variable {W A}

/- English proof (translation)
Use `set q := Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))`. Establish `hC : ∀ c, q (C c) = algebraMap (Kf e) (S W A) c` using `fun _ => rfl`. Establish `hu : q (C (projVar e 0)) * q (C ((projVar e 0)⁻¹)) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero 0), map_one, map_one]`. Establish `hch : q (Vertical.chartForm (projPar A) - 1) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`.

Rewrite `hch` using `[map_sub, map_one, chartForm_eq, map_mul]`. Establish `ha0 : q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) = q (C (projVar e 0))`. Take the linear combination `q (C (projVar e 0)) * hch - q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) * hu`. Proceed by induction on `k using Fin.cases with`. Consider the case `zero => rw [ha0, hC]`.

Consider the case `succ i`. Establish `hs : q (Vertical.secForm (projPar A) i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))`. Rewrite `hs` using `[secForm_eq, map_sub, map_mul, map_mul, ha0]`. Rewrite using `[← hC]`. Take the linear combination `(-q (C ((projVar e 0)⁻¹))) * hs + (q (C (projVar e i.succ)) - q (linForm fun j => algebraMap ℂ (Kf e) (A i.succ j))) * hu`.
-/
theorem mk_row (k : Fin (e + 1)) :
    Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
        (linForm fun j => algebraMap ℂ (Kf e) (A k j)) =
      algebraMap (Kf e) (S W A) (projVar e k) := by
  set q := Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
  have hC : ∀ c, q (C c) = algebraMap (Kf e) (S W A) c := fun _ => rfl
  have hu : q (C (projVar e 0)) * q (C ((projVar e 0)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero 0), map_one, map_one]
  have hch : q (Vertical.chartForm (projPar A) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [map_sub, map_one, chartForm_eq, map_mul] at hch
  have ha0 : q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) = q (C (projVar e 0)) := by
    linear_combination q (C (projVar e 0)) * hch - q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) * hu
  induction k using Fin.cases with
  | zero => rw [ha0, hC]
  | succ i =>
    have hs : q (Vertical.secForm (projPar A) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_eq, map_sub, map_mul, map_mul, ha0] at hs
    rw [← hC]
    linear_combination (-q (C ((projVar e 0)⁻¹))) * hs +
      (q (C (projVar e i.succ)) - q (linForm fun j => algebraMap ℂ (Kf e) (A i.succ j))) * hu

variable (W A)

def psi : MvPolynomial (Fin n) ℂ ⧸ W →+* S W A :=
  Ideal.Quotient.lift W
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap ℂ (Kf e))))
    fun _ hf => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)))

def M : Submonoid (MvPolynomial (Fin n) ℂ ⧸ W) :=
  (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)).map (ComplexSets.projHom W A)

abbrev T : Type := Localization (M W A)

def kappa : Kf e →+* T W A :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) (S := Kf e) (P := T W A)
    (g := (algebraMap _ (T W A)).comp (ComplexSets.projHom W A).toRingHom)
    fun y => IsLocalization.map_units (T W A) (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : M W A)

def phi : MvPolynomial (Fin n) (Kf e) →+* T W A :=
  eval₂Hom (kappa W A) fun j => algebraMap _ (T W A) (Ideal.Quotient.mk W (X j))

variable {W A}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psi_mk (f : MvPolynomial (Fin n) ℂ) : psi W A (Ideal.Quotient.mk W f) =
    Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℂ (Kf e)) f) := rfl

/- English proof (translation)
Rewrite using `[ComplexSets.projHom, AlgHom.comp_apply, ComplexSets.pullback, aeval_X]`. Both sides reduce to the same expression.
-/
theorem projHom_X (k : Fin (e + 1)) :
    ComplexSets.projHom W A (X k) = Ideal.Quotient.mk W (ComplexSets.linPoly A k) := by
  rw [ComplexSets.projHom, AlgHom.comp_apply, ComplexSets.pullback, aeval_X]; rfl

/- English proof (translation)
Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)` and prove the remaining obligations. Establish `h1 : algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e) (C r) = algebraMap ℂ (Kf e) r` using `(IsScalarTower.algebraMap_apply ℂ _ (Kf e) r).symm`. Establish `h2 : ComplexSets.projHom W A (C r) = Ideal.Quotient.mk W (C r)` using `(ComplexSets.projHom W A).commutes r`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, psi_mk, map_C]`. Both sides reduce to the same expression.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projHom_X, psi_mk, map_linPoly, mk_row]`. Both sides reduce to the same expression.
-/
theorem psi_comp_projHom :
    (psi W A).comp (ComplexSets.projHom W A).toRingHom =
      (algebraMap (Kf e) (S W A)).comp (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · have h1 : algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e) (C r) = algebraMap ℂ (Kf e) r :=
      (IsScalarTower.algebraMap_apply ℂ _ (Kf e) r).symm
    have h2 : ComplexSets.projHom W A (C r) = Ideal.Quotient.mk W (C r) := (ComplexSets.projHom W A).commutes r
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, psi_mk,
      map_C]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projHom_X,
      psi_mk, map_linPoly, mk_row]
    rfl

/- English proof (translation)
Unfold `kappa`. Conclude with `IsLocalization.lift_eq _ p`.
-/
theorem kappa_alg (p : MvPolynomial (Fin (e + 1)) ℂ) :
    kappa W A (algebraMap _ (Kf e) p) = algebraMap _ (T W A) (ComplexSets.projHom W A p) := by
  unfold kappa; exact IsLocalization.lift_eq _ p

/- English proof (translation)
The claim follows from `eval₂Hom_C _ _ _`.
-/
theorem phi_C (c : Kf e) : phi W A (C c) = kappa W A c := eval₂Hom_C _ _ _

/- English proof (translation)
Establish `: (phi W A).comp (MvPolynomial.map (algebraMap ℂ (Kf e))) = (algebraMap _ (T W A)).comp (Ideal.Quotient.mk W)`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, map_C, phi_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Kf e), kappa_alg, AlgHom.commutes]`. Both sides reduce to the same expression. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, map_X, phi, eval₂Hom_X']`.

Conclude with `RingHom.congr_fun this f`.
-/
theorem phi_map (f : MvPolynomial (Fin n) ℂ) :
    phi W A (MvPolynomial.map (algebraMap ℂ (Kf e)) f) = algebraMap _ (T W A) (Ideal.Quotient.mk W f) := by
  have : (phi W A).comp (MvPolynomial.map (algebraMap ℂ (Kf e))) =
      (algebraMap _ (T W A)).comp (Ideal.Quotient.mk W) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_C, phi_C,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Kf e), kappa_alg, AlgHom.commutes]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_X, phi, eval₂Hom_X']
  exact RingHom.congr_fun this f

/- English proof (translation)
Rewrite using `[← map_linPoly, phi_map, projVar, kappa_alg, projHom_X]`.
-/
theorem phi_row (k : Fin (e + 1)) :
    phi W A (linForm fun j => algebraMap ℂ (Kf e) (A k j)) = kappa W A (projVar e k) := by
  rw [← map_linPoly, phi_map, projVar, kappa_alg, projHom_X]

/- English proof (translation)
Establish `hu : kappa W A (projVar e 0)⁻¹ * kappa W A (projVar e 0) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ (projVar_ne_zero 0), map_one]`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, phi_map, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, secForm_eq, map_sub, map_mul, map_mul, phi_C, phi_C, phi_row, phi_row]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, chartForm_eq, map_mul, phi_C, phi_row, hu, sub_self]`.
-/
theorem secIdeal_le_ker :
    Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A) ≤
      RingHom.ker (phi W A) := by
  have hu : kappa W A (projVar e 0)⁻¹ * kappa W A (projVar e 0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (projVar_ne_zero 0), map_one]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]; intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, phi_map, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm_eq, map_sub, map_mul, map_mul, phi_C, phi_C, phi_row,
      phi_row]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      chartForm_eq, map_mul, phi_C, phi_row, hu, sub_self]

variable (W A)

def g : S W A →+* T W A := Ideal.Quotient.lift _ (phi W A) fun _ hf => RingHom.mem_ker.1 (secIdeal_le_ker hf)

/- English proof (translation)
Take `⟨_, p, hp, rfl⟩` from `y`. Establish `h` using `RingHom.congr_fun (psi_comp_projHom (W := W) (A := A)) p`. Rewrite `h` using `[RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[h]`. Conclude with `(IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map _`.
-/
theorem psi_unit (y : M W A) : IsUnit (psi W A y) := by
  obtain ⟨_, p, hp, rfl⟩ := y
  have h := RingHom.congr_fun (psi_comp_projHom (W := W) (A := A)) p
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  exact (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map _

def chi : T W A →+* S W A :=
  IsLocalization.lift (M := M W A) (S := T W A) (P := S W A) (g := psi W A) (psi_unit W A)

variable {W A}

/- English proof (translation)
Use `IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, kappa, IsLocalization.lift_comp, ← RingHom.comp_assoc, chi, IsLocalization.lift_comp, psi_comp_projHom]`.
-/
theorem chi_kappa : (chi W A).comp (kappa W A) = algebraMap (Kf e) (S W A) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) ?_
  rw [RingHom.comp_assoc, kappa, IsLocalization.lift_comp, ← RingHom.comp_assoc, chi,
    IsLocalization.lift_comp, psi_comp_projHom]

/- English proof (translation)
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective s`. Establish `: (chi W A).comp (phi W A) = Ideal.Quotient.mk _`. Use `MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, phi_C, ← RingHom.comp_apply, chi_kappa]`. Both sides reduce to the same expression.

Rewrite using `[RingHom.comp_apply, phi, eval₂Hom_X', chi, IsLocalization.lift_eq, psi_mk, map_X]`. Use `show chi W A (phi W A f) = _`. Conclude with `RingHom.congr_fun this f`.
-/
theorem chi_g (s : S W A) : chi W A (g W A s) = s := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  have : (chi W A).comp (phi W A) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, phi_C, ← RingHom.comp_apply, chi_kappa]; rfl
    · rw [RingHom.comp_apply, phi, eval₂Hom_X', chi, IsLocalization.lift_eq, psi_mk, map_X]
  show chi W A (phi W A f) = _
  exact RingHom.congr_fun this f

/- English proof (translation)
Introduce `n e W A hW hA`. Establish `hM : M W A ≤ nonZeroDivisors _`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp (hA.injective (by rw [map_zero]; exact h))`. Establish `: IsDomain (T W A)` using `IsLocalization.isDomain_localization hM`.

Use `⟨Function.Injective.isDomain (g W A) (Function.LeftInverse.injective chi_g), ?_⟩` and prove the remaining obligations. Set `_ : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W)` to `(ComplexSets.projHom W A).toRingHom.toAlgebra`. Establish `hint (j : Fin n) : IsIntegral (Kf e) (Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)) (X j))`. Use `IsIntegral.map_of_comp_eq (algebraMap _ (Kf e)) (psi W A) psi_comp_projHom.symm (hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j)))` as an intermediate fact. Rewrite `this` using `[psi_mk, map_X]`. Then use the resulting hypothesis.

Establish `: Algebra.IsIntegral (Kf e) (S W A)` using `⟨fun s => by`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective s`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => exact isIntegral_algebraMap`. Consider the case `add p q hp hq => rw [map_add]`.

Conclude with `hp.add hq`. Consider the case `mul_X p j hp => rw [map_mul]`. Conclude with `hp.mul (hint j)⟩`. Establish `: Algebra.FiniteType (Kf e) (S W A)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (Kf e) _) (Ideal.Quotient.mkₐ_surjective _ _)`. Conclude with `Algebra.IsIntegral.finite`.
-/
theorem proof : ProjSecDomain.Statement := by
  intro n e W A hW hA
  have hM : M W A ≤ nonZeroDivisors _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero hp (hA.injective (by rw [map_zero]; exact h))
  have : IsDomain (T W A) := IsLocalization.isDomain_localization hM
  refine ⟨Function.Injective.isDomain (g W A) (Function.LeftInverse.injective chi_g), ?_⟩
  let _ : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have hint (j : Fin n) : IsIntegral (Kf e) (Ideal.Quotient.mk
      (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)) (X j)) := by
    have := IsIntegral.map_of_comp_eq (algebraMap _ (Kf e)) (psi W A) psi_comp_projHom.symm
      (hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j)))
    rwa [psi_mk, map_X] at this
  have : Algebra.IsIntegral (Kf e) (S W A) := ⟨fun s => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p j hp => rw [map_mul]; exact hp.mul (hint j)⟩
  have : Algebra.FiniteType (Kf e) (S W A) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (Kf e) _)
      (Ideal.Quotient.mkₐ_surjective _ _)
  exact Algebra.IsIntegral.finite

end ProjSecDomain

end

end GroundTheory.Heights₂.Heights
