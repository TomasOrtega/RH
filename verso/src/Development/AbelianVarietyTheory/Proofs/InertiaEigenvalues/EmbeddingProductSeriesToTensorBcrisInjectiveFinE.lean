import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLastMaxOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.IBInj

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
  [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
  [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]

omit [NeZero a] [NeZero e] [Module.Finite ℤ_[l] O] [CompleteSpace K] in

/- English proof (translation)
The claim follows from `Module.Flat.lTensor_preserves_injective_linearMap (M := O) (acrisToBcris l).toLinearMap (GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l)`.
-/
theorem toOB_injective : Function.Injective (toOB l O) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := O) (acrisToBcris l).toLinearMap
    (GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l)

omit [NeZero a] in

/- English proof (translation)
Take `⟨n, hn⟩` from `hf`. Establish `hlu : IsUnit ((l : OD l O) ^ n)` using `isUnit_l_OD.pow n`. Establish `hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e` using `A_le_S l e hn`. Establish `e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩` using `Subtype.ext (by simp)`. Establish `e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) = ofA O K l e ⟨_, hn⟩` using `toHat_eq_ofAl l e rfl`.

Use `hlu.mul_left_cancel ?_` and prove the remaining obligations. Establish `h3` using `congrArg (ϖ.iSD O K) e1`. Establish `h4` using `congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1`. Simplify using `only [map_mul, map_pow, map_natCast] at h3 h4`. Rewrite using `[h3, h4, e2, ϖ.iHat_ofA O K]`.

Use `(ϖ.iSD_of_mem O K hg _).trans ?_` and prove the remaining obligations. Rewrite using `[ϖ.iS_of_mem O K hn, crisToOD_toOCr]`.
-/
theorem iSD_eq_of_mem_invL_A (ϖ : PiSys l e) (f : invL l (S O K e)) (hf : (f : K⟦X⟧) ∈ invL l (A O K)) :
    ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]

omit [NeZero a] in

/- English proof (translation)
Establish `hlu : IsUnit (l : OD l O)` using `isUnit_l_OD`. Use `set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ`. Establish `hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s)` using `fun s => ϖ.iSD_of_mem O K s.2 _`. Rewrite using `[← sub_eq_zero]`. Use `set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) - ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD`.

Establish `hDadd : ∀ p q : S O K e, D (p + q) = D p + D q` using `fun p q => by`. Simplify using `only [hD, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q` using `fun k q => by`. Simplify using `only [hD, map_mul, map_pow, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdiv : ∀ m : ℕ, ξ ^ m ∣ D s`. Introduce `m`. Take `⟨N, hN⟩` from `GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m`. Establish `hw : ∀ k : ℕ, ∃ y : OA l O, ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y`.

Introduce `k`. Take `⟨N0, hN0⟩` from `exists_sum_monomial_add l e s.2 k`. Take `⟨h, hh, hs⟩` from `hN0 N0 le_rfl`. Use `set hS' : S O K e := ⟨h, hh⟩`. Establish `hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e` using `sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)`.

Use `set P : S O K e := ⟨_, hP⟩`. Establish `hsP : s = P + (l : S O K e) ^ k * hS'` using `Subtype.ext (by simp [P, hS'])`. Establish `hPA : (P : K⟦X⟧) ∈ invL l (A O K)`. Establish `: (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧))`. Simplify using `only [P]`.

Take the linear combination `hs`. Rewrite using `[this]`. Conclude with `sum_mem fun n _ => monomial_mem_invL l n _`. Establish `hDP : D P = 0`. Simplify using `only [hD, sub_eq_zero]`.

Rewrite using `[← hS]`. Conclude with `iSD_eq_of_mem_invL_A ϖ _ hPA`. Take `⟨y1, hy1⟩` from `hN (ϖ.iS O K hS')`. Take `⟨y2, hy2⟩` from `GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'`. Use `⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩` and prove the remaining obligations.

Establish `e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) = (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') - toOD l O y1) - (l : OD l O) ^ N * ((l : OD l O) ^ m * ϖ.iHat O K (toHatS O K …`. Rewrite using `[hsP, hDadd, hDP, zero_add, hDmul]`. Simplify using `only [hD, map_sub, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Conclude with `dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _`. Establish `h1` using `GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw`. Rewrite `h1` using `[pow_add, mul_assoc]`. Conclude with `(((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)`. Establish `hc` using `ϖ.complete_OD O K`.

Conclude with `hc.toIsHausdorff.haus' _ fun n => by`. Simplify using `only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]`. Conclude with `Ideal.mem_span_singleton.2 (hdiv n)`.
-/
theorem crisToOD_iS (ϖ : PiSys l e) (s : S O K e) : crisToOD l O (ϖ.iS O K s) =
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ
  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) =
      crisToOD l O (ϖ.iS O K s) := fun s => ϖ.iSD_of_mem O K s.2 _
  rw [← sub_eq_zero]
  set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
  have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
    simp only [hD, map_add]; ring
  have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
    simp only [hD, map_mul, map_pow, map_natCast]; ring
  have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
    intro m
    obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m
    have hw : ∀ k : ℕ, ∃ y : OA l O,
        ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
      intro k
      obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
      obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
      set hS' : S O K e := ⟨h, hh⟩
      have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
        sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
      set P : S O K e := ⟨_, hP⟩
      have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
      have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
        have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
          simp only [P]; linear_combination hs
        rw [this]
        exact sum_mem fun n _ => monomial_mem_invL l n _
      have hDP : D P = 0 := by
        simp only [hD, sub_eq_zero]
        rw [← hS]
        exact iSD_eq_of_mem_invL_A ϖ _ hPA
      obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
      obtain ⟨y2, hy2⟩ := GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'
      refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
      have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k *
            toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
          (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') -
            toOD l O y1) - (l : OD l O) ^ N * ((l : OD l O) ^ m *
              ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
        rw [hsP, hDadd, hDP, zero_add, hDmul]
        simp only [hD, map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e1]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
    have h1 := GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw
    rw [pow_add, mul_assoc] at h1
    exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
  have hc := ϖ.complete_OD O K
  exact hc.toIsHausdorff.haus' _ fun n => by
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
    exact Ideal.mem_span_singleton.2 (hdiv n)

omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NeZero e] [CompleteSpace K] in

/- English proof (translation)
Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `h n`. Establish `hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) = Ideal.Quotient.mk _ (EIn l e _)` using `AlgHom.commutes _ _`. Rewrite using `[map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul]`. Conclude with `(map_zero _).symm`.
-/
theorem eq_zero_of_forall_dvd (x : Ahat O K l e) (h : ∀ n : ℕ, ∃ y, x = Ehat O K l e ^ n * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, rfl⟩ := h n
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) = Ideal.Quotient.mk _ (EIn l e _) :=
    AlgHom.commutes _ _
  rw [map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul]
  exact (map_zero _).symm

/- English proof (translation)
Use `set x := toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s) with hx`. Establish `h1 : idem (constD t) τ * ϖ.iHat O K x = 0`. Establish `h2` using `congrArg (crisToOD l O) h`. Rewrite `h2` using `[map_mul, map_zero, crisToOD_iS ϖ s]`. Establish `h3 : crisToOD l O (idem (constC t) τ) = idem (constD t) τ` using `crisToOD_toOCr (constA t (Pi.single τ 1))`.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Establish `h4 : ϖ.iD t K (Pi.single τ x) = 0`. Rewrite using `[PiSys.iD, glue_apply, Finset.sum_eq_single τ (fun σ _ hσ => by`. Rewrite using `[Pi.single_eq_of_ne hσ, map_zero, mul_zero]) (by simp), Pi.single_eq_same, h1]`. Establish `h5 : x = 0` using `eq_zero_of_forall_dvd x fun n => by`.

Take `⟨y, hy⟩` from `GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ n (Pi.single τ x) (by rw [h4]; exact zero_mem _)`. Conclude with `⟨y τ, by simpa using congrFun hy τ⟩`. Establish `h6 : toHat O K l e ⟨(s : K⟦X⟧), invL_S_le_Rpi l e (le_away _ _ s.2)⟩ = 0` using `h5`. Establish `h7` using `GlobalTheory.BK.toHat_injective O K l e (h6.trans (map_zero _).symm)`. Establish `h8 : (s : K⟦X⟧) = 0` using `congrArg (fun z : Rpi O K l e => (z : K⟦X⟧)) h7`.

Conclude with `Subtype.ext h8`.
-/
theorem eq_zero_of_idem_mul_iS (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (τ : ZMod a) (s : S O K e)
    (h : idem (constC t) τ * ϖ.iS O K s = 0) : s = 0 := by
  set x := toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s) with hx
  have h1 : idem (constD t) τ * ϖ.iHat O K x = 0 := by
    have h2 := congrArg (crisToOD l O) h
    rw [map_mul, map_zero, crisToOD_iS ϖ s] at h2
    have h3 : crisToOD l O (idem (constC t) τ) = idem (constD t) τ :=
      crisToOD_toOCr (constA t (Pi.single τ 1))
    rwa [h3] at h2
  have h4 : ϖ.iD t K (Pi.single τ x) = 0 := by
    rw [PiSys.iD, glue_apply, Finset.sum_eq_single τ (fun σ _ hσ => by
      rw [Pi.single_eq_of_ne hσ, map_zero, mul_zero]) (by simp), Pi.single_eq_same, h1]
  have h5 : x = 0 := eq_zero_of_forall_dvd x fun n => by
    obtain ⟨y, hy⟩ := GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ n (Pi.single τ x)
      (by rw [h4]; exact zero_mem _)
    exact ⟨y τ, by simpa using congrFun hy τ⟩
  have h6 : toHat O K l e ⟨(s : K⟦X⟧), invL_S_le_Rpi l e (le_away _ _ s.2)⟩ = 0 := h5
  have h7 := GlobalTheory.BK.toHat_injective O K l e (h6.trans (map_zero _).symm)
  have h8 : (s : K⟦X⟧) = 0 := congrArg (fun z : Rpi O K l e => (z : K⟦X⟧)) h7
  exact Subtype.ext h8

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun x hx => funext fun τ => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `(x τ).2`. Use `set s : S O K e := ⟨_, hk⟩`. Establish `hs : algebraMap (S O K e) (invL l (S O K e)) s = (l : invL l (S O K e)) ^ k * x τ` using `Subtype.ext (by simp [s])`. Establish `h1` using `idem_mul_glue (constB t) (ϖ.iSl O K) x τ`.

Rewrite `h1` using `[show glue (constB t) (ϖ.iSl O K) x = 0 from hx, mul_zero]`. Establish `h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s)` using `ϖ.iSl_of_mem O K s.2 _`. Establish `h2 : toOB l O (idem (constC t) τ * ϖ.iS O K s) = 0`. Rewrite using `[map_mul, ← h3, hs, map_mul, map_pow, map_natCast]`. Express the relevant statement in the definitionally equal form `idem (constB t) τ * (_ * _) = 0`.

Rewrite using `[mul_left_comm, ← h1, mul_zero]`. Establish `h4 : idem (constC t) τ * ϖ.iS O K s = 0` using `toOB_injective (h2.trans (map_zero _).symm)`. Establish `h5` using `eq_zero_of_idem_mul_iS t ϖ τ s h4`. Establish `h6 : (l : invL l (S O K e)) ^ k * x τ = 0` using `by rw [← hs, h5, map_zero]`. Establish `h7 : (l : K⟦X⟧) ^ k * (x τ : K⟦X⟧) = 0` using `by simpa using congrArg Subtype.val h6`.

Establish `hl0 : (l : K⟦X⟧) ≠ 0` using `fun h0 => BK.l_ne_zero (K := K) l (by`. Simplify using `using congrArg PowerSeries.constantCoeff h0)`. Conclude with `Subtype.ext ((mul_eq_zero.1 h7).resolve_left (pow_ne_zero _ hl0))`.
-/
theorem iB_injective (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) : Function.Injective (ϖ.iB t K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => funext fun τ => ?_
  obtain ⟨k, hk⟩ := (x τ).2
  set s : S O K e := ⟨_, hk⟩
  have hs : algebraMap (S O K e) (invL l (S O K e)) s = (l : invL l (S O K e)) ^ k * x τ :=
    Subtype.ext (by simp [s])
  have h1 := idem_mul_glue (constB t) (ϖ.iSl O K) x τ
  rw [show glue (constB t) (ϖ.iSl O K) x = 0 from hx, mul_zero] at h1
  have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
    ϖ.iSl_of_mem O K s.2 _
  have h2 : toOB l O (idem (constC t) τ * ϖ.iS O K s) = 0 := by
    rw [map_mul, ← h3, hs, map_mul, map_pow, map_natCast]
    change idem (constB t) τ * (_ * _) = 0
    rw [mul_left_comm, ← h1, mul_zero]
  have h4 : idem (constC t) τ * ϖ.iS O K s = 0 := toOB_injective (h2.trans (map_zero _).symm)
  have h5 := eq_zero_of_idem_mul_iS t ϖ τ s h4
  have h6 : (l : invL l (S O K e)) ^ k * x τ = 0 := by rw [← hs, h5, map_zero]
  have h7 : (l : K⟦X⟧) ^ k * (x τ : K⟦X⟧) = 0 := by simpa using congrArg Subtype.val h6
  have hl0 : (l : K⟦X⟧) ≠ 0 := fun h0 => BK.l_ne_zero (K := K) l (by
    simpa using congrArg PowerSeries.constantCoeff h0)
  exact Subtype.ext ((mul_eq_zero.1 h7).resolve_left (pow_ne_zero _ hl0))

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ t ϖ` and use `iB_injective t ϖ`.
-/
theorem iB_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l)
    (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) :=
  fun _ _ _ _ _ _ _ t ϖ => iB_injective t ϖ

end GlobalTheory.BKReal.IBInj
