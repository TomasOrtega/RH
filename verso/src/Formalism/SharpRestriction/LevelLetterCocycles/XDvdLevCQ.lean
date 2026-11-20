import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfPowDvd

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LevW

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def levC (i : ZMod n) (ζ : LL) : PowerSeries O →ₐ[O] PowerSeries LL :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) (PowerSeries O))

/- English proof (translation)
Establish `h` using `W.lev_letter i ζ (a - Pi.constAlgHom O (ZMod n) (PowerSeries O) (a i)) (by simp)`. Rewrite `h` using `[map_sub, sub_eq_zero]`. Conclude with `h`.
-/
theorem lev_eq_levC (i : ZMod n) (ζ : LL) (a : LetA O n) : W.lev i ζ a = levC W i ζ (a i) := by
  have h := W.lev_letter i ζ (a - Pi.constAlgHom O (ZMod n) (PowerSeries O) (a i)) (by simp)
  rw [map_sub, sub_eq_zero] at h
  exact h

/- English proof (translation)
Take `⟨E, h0, h1, h2⟩` from `W.lev_π i ζ ⟨1, by rwa [pow_one]⟩`. Use `⟨E, h0, h1, ?_⟩` and prove the remaining obligations. Establish `h3 : levC W i ζ PowerSeries.X = W.lev i ζ letπ` using `by first`. Consider the case `rfl`. Consider the case `exact (lev_eq_levC W i ζ letπ).symm`.

Rewrite using `[h3]`. Take the linear combination `h2`.
-/
theorem levC_X (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ E : PowerSeries LL, PowerSeries.constantCoeff E = 1 ∧ PowerSeries.derivative LL E = E ∧
      levC W i ζ PowerSeries.X = PowerSeries.C ζ * E - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ ⟨1, by rwa [pow_one]⟩
  refine ⟨E, h0, h1, ?_⟩
  have h3 : levC W i ζ PowerSeries.X = W.lev i ζ letπ := by
    first
    | rfl
    | exact (lev_eq_levC W i ζ letπ).symm
  rw [h3]
  linear_combination h2

/- English proof (translation)
Use `first`. Consider the case `(rw [show PowerSeries.derivative R f = f.derivativeFun from rfl, PowerSeries.coeff_derivativeFun]; simp)`. Consider the case `simp [PowerSeries.coeff_derivativeFun]`. Consider the case `simp [PowerSeries.derivative, PowerSeries.coeff_derivativeFun]`.
-/
private theorem coeff_zero_derivative_eq_coeff_one {R : Type} [CommRing R] (f : PowerSeries R) :
    PowerSeries.coeff 0 (PowerSeries.derivative R f) = PowerSeries.coeff 1 f := by
  first
  | (rw [show PowerSeries.derivative R f = f.derivativeFun from rfl, PowerSeries.coeff_derivativeFun]; simp)
  | simp [PowerSeries.coeff_derivativeFun]
  | simp [PowerSeries.derivative, PowerSeries.coeff_derivativeFun]

/- English proof (translation)
Take `⟨E, hE0, _, hX⟩` from `levC_X W i ζ hζ`. Establish `h` using `congrArg (levC W i ζ) W.q₀_def`. Simplify using `only [map_mul, map_sub, map_pow, map_add, map_one, hX] at h`. Establish `h2` using `congrArg PowerSeries.constantCoeff h`. Simplify using `only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.constantCoeff_C, hE0] at h2`.

Rewrite using `[PowerSeries.X_dvd_iff]`. Establish `h3 : (ζ - 1) * PowerSeries.constantCoeff (levC W i ζ W.q₀) = 0`. Take the linear combination `h2 + hζ.pow_eq_one`. Establish `hne : ζ - 1 ≠ 0` using `sub_ne_zero.mpr (hζ.ne_one (by omega))`. Conclude with `(mul_eq_zero.mp h3).resolve_left hne`.
-/
theorem X_dvd_levC_q (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (hp : 2 ≤ PD.p) :
    PowerSeries.X ∣ levC W i ζ W.q₀ := by
  obtain ⟨E, hE0, _, hX⟩ := levC_X W i ζ hζ
  have h := congrArg (levC W i ζ) W.q₀_def
  simp only [map_mul, map_sub, map_pow, map_add, map_one, hX] at h
  have h2 := congrArg PowerSeries.constantCoeff h
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.constantCoeff_C, hE0] at h2
  rw [PowerSeries.X_dvd_iff]
  have h3 : (ζ - 1) * PowerSeries.constantCoeff (levC W i ζ W.q₀) = 0 := by
    linear_combination h2 + hζ.pow_eq_one
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by omega))
  exact (mul_eq_zero.mp h3).resolve_left hne

end

section Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hk : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O)]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).mpr hpm`. Establish `hK : ((PD.p : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0`.

Rewrite using `[← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), hk, map_zero]`. Use `haveI : CharP (PowerSeries (IsLocalRing.ResidueField O)) PD.p := by first`. Consider the case `exact (CharP.charP_iff_prime_eq_zero hp).mpr hK`. Consider the case `exact (charP_iff_prime_eq_zero hp).mpr hK`. Establish `h` using `congrArg (PowerSeries.map (IsLocalRing.residue O)) W.q₀_def`.

Simplify using `only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X] at h`. Rewrite `h` using `[add_pow_char, one_pow, add_sub_cancel_left]`. Establish `h2 : PowerSeries.X * PowerSeries.map (IsLocalRing.residue O) W.q₀ = PowerSeries.X * PowerSeries.X ^ (PD.p - 1)`. Rewrite using `[h, ← pow_succ', Nat.sub_add_cancel hp.one_le]`. Conclude with `mul_left_cancel₀ PowerSeries.X_ne_zero h2`.
-/
theorem residue_q₀ [IsLocalRing O] (hp : PD.p.Prime) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (IsLocalRing.residue O) W.q₀ = PowerSeries.X ^ (PD.p - 1) := by
  haveI := Fact.mk hp
  have hk : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpm
  have hK : ((PD.p : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), hk, map_zero]
  haveI : CharP (PowerSeries (IsLocalRing.ResidueField O)) PD.p := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hp).mpr hK
    | exact (charP_iff_prime_eq_zero hp).mpr hK
  have h := congrArg (PowerSeries.map (IsLocalRing.residue O)) W.q₀_def
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X] at h
  rw [add_pow_char, one_pow, add_sub_cancel_left] at h
  have h2 : PowerSeries.X * PowerSeries.map (IsLocalRing.residue O) W.q₀ =
      PowerSeries.X * PowerSeries.X ^ (PD.p - 1) := by
    rw [h, ← pow_succ', Nat.sub_add_cancel hp.one_le]
  exact mul_left_cancel₀ PowerSeries.X_ne_zero h2

/- English proof (translation)
Take `⟨E, hE0, hE1, hX⟩` from `levC_X W i ζ hζ`. Take `⟨w, hw⟩` from `X_dvd_levC_q W i ζ hζ hp`. Establish `h1` using `congrArg (levC W i ζ) W.q₀_def`. Simplify using `only [map_mul, map_sub, map_pow, map_add, map_one, hX, hw] at h1`. Establish `e : (PowerSeries.C ζ * E) ^ PD.p = E ^ PD.p` using `by first`.

Consider the case `rw [mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul]`. Consider the case `simp [mul_pow, ← map_pow, hζ.pow_eq_one]`. Establish `h1' : (PowerSeries.C ζ * E - 1) * w * PowerSeries.X = E ^ PD.p - 1`. Rewrite using `[← e]`. Take the linear combination `h1`.

Establish `hc : PowerSeries.coeff 0 ((PowerSeries.C ζ * E - 1) * w) = PowerSeries.coeff 1 (E ^ PD.p - 1)`. Rewrite using `[← h1', PowerSeries.coeff_succ_mul_X]`. Establish `hD : PowerSeries.coeff 1 (E ^ PD.p) = ((PD.p : ℕ) : LL)`. Rewrite using `[← coeff_zero_derivative_eq_coeff_one, Derivation.leibniz_pow, hE1]`. Simplify using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0]`.

Establish `hcw : PowerSeries.constantCoeff w ≠ 0`. Introduce `h0`. Apply `hpL` to reduce the goal to its premises. Establish `e2 : PowerSeries.coeff 1 (E ^ PD.p - 1) = PowerSeries.coeff 1 (E ^ PD.p)` using `by first`. Consider the case `simp`.

Consider the case `simp [PowerSeries.coeff_one]`. Rewrite using `[← hD, ← e2, ← hc, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, h0, mul_zero]`. Establish `hwU : IsUnit w`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Conclude with `isUnit_iff_ne_zero.mpr hcw`.

Rewrite `h` using `[map_mul, hw, pow_succ', mul_assoc]`. Establish `h2` using `(mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp h`. Use `first`. Consider the case `exact hwU.dvd_mul_left.mp h2`. Consider the case `exact (IsUnit.dvd_mul_left hwU).mp h2`.

Consider the case `exact (Units.dvd_mul_left (u := hwU.unit)).mp h2`.
-/
private theorem eq_of_mul_mul_eq_of_det_ne_zero (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (hp : 2 ≤ PD.p)
    (hpL : ((PD.p : ℕ) : LL) ≠ 0) (b : ℕ) (c : PowerSeries O)
    (h : PowerSeries.X ^ (b + 1) ∣ levC W i ζ (W.q₀ * c)) : PowerSeries.X ^ b ∣ levC W i ζ c := by
  obtain ⟨E, hE0, hE1, hX⟩ := levC_X W i ζ hζ
  obtain ⟨w, hw⟩ := X_dvd_levC_q W i ζ hζ hp
  have h1 := congrArg (levC W i ζ) W.q₀_def
  simp only [map_mul, map_sub, map_pow, map_add, map_one, hX, hw] at h1
  have e : (PowerSeries.C ζ * E) ^ PD.p = E ^ PD.p := by
    first
    | rw [mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul]
    | simp [mul_pow, ← map_pow, hζ.pow_eq_one]
  have h1' : (PowerSeries.C ζ * E - 1) * w * PowerSeries.X = E ^ PD.p - 1 := by
    rw [← e]
    linear_combination h1
  have hc : PowerSeries.coeff 0 ((PowerSeries.C ζ * E - 1) * w) =
      PowerSeries.coeff 1 (E ^ PD.p - 1) := by
    rw [← h1', PowerSeries.coeff_succ_mul_X]
  have hD : PowerSeries.coeff 1 (E ^ PD.p) = ((PD.p : ℕ) : LL) := by
    rw [← coeff_zero_derivative_eq_coeff_one, Derivation.leibniz_pow, hE1]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0]
  have hcw : PowerSeries.constantCoeff w ≠ 0 := by
    intro h0
    apply hpL
    have e2 : PowerSeries.coeff 1 (E ^ PD.p - 1) = PowerSeries.coeff 1 (E ^ PD.p) := by
      first
      | simp
      | simp [PowerSeries.coeff_one]
    rw [← hD, ← e2, ← hc, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, h0, mul_zero]
  have hwU : IsUnit w := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hcw
  rw [map_mul, hw, pow_succ', mul_assoc] at h
  have h2 := (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp h
  first
  | exact hwU.dvd_mul_left.mp h2
  | exact (IsUnit.dvd_mul_left hwU).mp h2
  | exact (Units.dvd_mul_left (u := hwU.unit)).mp h2

/- English proof (translation)
Establish `hres` using `residue_q₀ W hp hpm`. Establish `hne : PowerSeries.map (IsLocalRing.residue O) W.q₀ ≠ 0`. Rewrite using `[hres]`. Conclude with `pow_ne_zero _ PowerSeries.X_ne_zero`. Take `⟨q, r, hdeg0, heq⟩ : ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < ((PowerSeries.map (IsLocalRing.residue O) W.q₀).order.toNat : WithBot ℕ) ∧ a = W.q₀ * q + (r : PowerSeries O)` from `by first`.

Consider the case `(obtain ⟨q, r, hr⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hne`. Conclude with `⟨q, r, hr.degree_lt, hr.eq_mul_add⟩)`. Consider the case `(obtain ⟨q, r, hr⟩ := PowerSeries.exists_isWeierstrassDivision a hne`. Conclude with `⟨q, r, hr.degree_lt, hr.eq_mul_add⟩)`. Consider the case `exact ⟨_, _, (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod a hne).degree_lt, (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod a hne).eq_mul_add⟩`.

Rewrite `hdeg0` using `[hres, PowerSeries.order_X_pow]`. Establish `hdeg : r.degree < ((PD.p - 1 : ℕ) : WithBot ℕ)` using `by first`. Consider the case `(rw [ENat.toNat_coe] at hdeg0; exact hdeg0)`. Consider the case `exact hdeg0`. Consider the case `simpa only [ENat.toNat_coe] using hdeg0`.

Establish `hroots : ∀ ζ ∈ primitiveRoots PD.p LL, (r.map (algebraMap O LL)).eval (ζ - 1) = 0`. Introduce `ζ hζm`. Establish `hζ : IsPrimitiveRoot ζ PD.p` using `(mem_primitiveRoots hp.pos).mp hζm`. Take `⟨E, hE0, _, hX⟩` from `levC_X W i ζ hζ`. Establish `hC : ∀ c : O, levC W i ζ (PowerSeries.C c) = PowerSeries.C (algebraMap O LL c)`.

Introduce `c`. Establish `hc` using `(levC W i ζ).commutes c`. Use `first`. Consider the case `simpa [PowerSeries.algebraMap_apply] using hc`. Consider the case `simpa [PowerSeries.algebraMap_apply'] using hc`.

Establish `key : ∀ s : Polynomial O, PowerSeries.constantCoeff (levC W i ζ (s : PowerSeries O)) = (s.map (algebraMap O LL)).eval (ζ - 1)`. Introduce `s`. Use `Polynomial.induction_on s ?_ ?_ ?_` and prove the remaining obligations. Introduce `c`. Simplify using `[hC]`.

Introduce `p1 p2 h1 h2`. Simplify using `[h1, h2]`. Introduce `k c _`. Simplify using `[hC, hX, hE0]`. Establish `h1` using `hv ζ hζ`.

Rewrite `h1` using `[heq, map_add, map_mul]`. Establish `h3` using `dvd_mul_of_dvd_left (X_dvd_levC_q W i ζ hζ hp.two_le) (levC W i ζ q)`. Establish `h2` using `(dvd_add_right h3).mp h1`. Rewrite `h2` using `[PowerSeries.X_dvd_iff, key]`. Conclude with `h2`.

Establish `hR0 : r.map (algebraMap O LL) = 0`. Assume the negation of the conclusion as `hR`. Establish `hRdeg : (r.map (algebraMap O LL)).degree < ((PD.p - 1 : ℕ) : WithBot ℕ)` using `by first`. Consider the case `exact lt_of_le_of_lt Polynomial.degree_map_le hdeg`. Consider the case `exact lt_of_le_of_lt (Polynomial.degree_map_le _ _) hdeg`.

Establish `hnd : (r.map (algebraMap O LL)).natDegree < PD.p - 1` using `(Polynomial.natDegree_lt_iff_degree_lt hR).mpr hRdeg`. Apply `hR` to reduce the goal to its premises. Apply `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ ((primitiveRoots PD.p LL).image (fun z => z - 1))` to reduce the goal to its premises. Introduce `x hx`. Take `⟨z, hz, rfl⟩` from `Finset.mem_image.mp hx`.

Conclude with `hroots z hz`. Rewrite using `[Finset.card_image_of_injective _ (sub_left_injective), hζ₀.card_primitiveRoots, Nat.totient_prime hp]`. Conclude with `hnd`. Establish `hr0 : r = 0`. Apply `Polynomial.map_injective (algebraMap O LL) hinj` to reduce the goal to its premises.

Rewrite using `[hR0, Polynomial.map_zero]`. Conclude with `⟨q, by rw [heq, hr0, Polynomial.coe_zero, add_zero]⟩`.
-/
private theorem q0_dvd_of_X_dvd_levC_primitive_roots [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hp : PD.p.Prime) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hinj : Function.Injective (algebraMap O LL)) {ζ₀ : LL} (hζ₀ : IsPrimitiveRoot ζ₀ PD.p)
    (i : ZMod n) (a : PowerSeries O)
    (hv : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → PowerSeries.X ∣ levC W i ζ a) : W.q₀ ∣ a := by
  classical
  have hres := residue_q₀ W hp hpm
  have hne : PowerSeries.map (IsLocalRing.residue O) W.q₀ ≠ 0 := by
    rw [hres]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hdeg0, heq⟩ : ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < ((PowerSeries.map (IsLocalRing.residue O) W.q₀).order.toNat : WithBot ℕ) ∧
      a = W.q₀ * q + (r : PowerSeries O) := by
    first
    | (obtain ⟨q, r, hr⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hne
       exact ⟨q, r, hr.degree_lt, hr.eq_mul_add⟩)
    | (obtain ⟨q, r, hr⟩ := PowerSeries.exists_isWeierstrassDivision a hne
       exact ⟨q, r, hr.degree_lt, hr.eq_mul_add⟩)
    | exact ⟨_, _, (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod a hne).degree_lt,
        (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod a hne).eq_mul_add⟩
  rw [hres, PowerSeries.order_X_pow] at hdeg0
  have hdeg : r.degree < ((PD.p - 1 : ℕ) : WithBot ℕ) := by
    first
    | (rw [ENat.toNat_coe] at hdeg0; exact hdeg0)
    | exact hdeg0
    | simpa only [ENat.toNat_coe] using hdeg0
  have hroots : ∀ ζ ∈ primitiveRoots PD.p LL, (r.map (algebraMap O LL)).eval (ζ - 1) = 0 := by
    intro ζ hζm
    have hζ : IsPrimitiveRoot ζ PD.p := (mem_primitiveRoots hp.pos).mp hζm
    obtain ⟨E, hE0, _, hX⟩ := levC_X W i ζ hζ
    have hC : ∀ c : O, levC W i ζ (PowerSeries.C c) = PowerSeries.C (algebraMap O LL c) := by
      intro c
      have hc := (levC W i ζ).commutes c
      first
      | simpa [PowerSeries.algebraMap_apply] using hc
      | simpa [PowerSeries.algebraMap_apply'] using hc
    have key : ∀ s : Polynomial O, PowerSeries.constantCoeff (levC W i ζ (s : PowerSeries O)) =
        (s.map (algebraMap O LL)).eval (ζ - 1) := by
      intro s
      refine Polynomial.induction_on s ?_ ?_ ?_
      · intro c
        simp [hC]
      · intro p1 p2 h1 h2
        simp [h1, h2]
      · intro k c _
        simp [hC, hX, hE0]
    have h1 := hv ζ hζ
    rw [heq, map_add, map_mul] at h1
    have h3 := dvd_mul_of_dvd_left (X_dvd_levC_q W i ζ hζ hp.two_le) (levC W i ζ q)
    have h2 := (dvd_add_right h3).mp h1
    rw [PowerSeries.X_dvd_iff, key] at h2
    exact h2
  have hR0 : r.map (algebraMap O LL) = 0 := by
    by_contra hR
    have hRdeg : (r.map (algebraMap O LL)).degree < ((PD.p - 1 : ℕ) : WithBot ℕ) := by
      first
      | exact lt_of_le_of_lt Polynomial.degree_map_le hdeg
      | exact lt_of_le_of_lt (Polynomial.degree_map_le _ _) hdeg
    have hnd : (r.map (algebraMap O LL)).natDegree < PD.p - 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hR).mpr hRdeg
    apply hR
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
      ((primitiveRoots PD.p LL).image (fun z => z - 1))
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hroots z hz
    · rw [Finset.card_image_of_injective _ (sub_left_injective), hζ₀.card_primitiveRoots,
        Nat.totient_prime hp]
      exact hnd
  have hr0 : r = 0 := by
    apply Polynomial.map_injective (algebraMap O LL) hinj
    rw [hR0, Polynomial.map_zero]
  exact ⟨q, by rw [heq, hr0, Polynomial.coe_zero, add_zero]⟩

/- English proof (translation)
Establish `hp2 : 2 ≤ PD.p` using `hp.two_le`. Establish `hpL : ((PD.p : ℕ) : LL) ≠ 0`. Introduce `h0`. Establish `h1` using `W.v_l`. Rewrite `h1` using `[h0, AddValuation.map_zero]`.

Use `first`. Consider the case `exact WithTop.top_ne_one h1`. Consider the case `exact absurd h1 (by simp)`. Consider the case `simp at h1`. Proceed by induction on `b generalizing a with`.

Consider the case `zero => exact ⟨a, by simp⟩`. Consider the case `succ b ih`. Take `⟨c, rfl⟩` from `q0_dvd_of_X_dvd_levC_primitive_roots W hp hpm hinj hζ₀ i a (fun ζ hζ => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero b)) (hv ζ hζ))`. Take `⟨h, hh⟩` from `ih c (fun ζ hζ => eq_of_mul_mul_eq_of_det_ne_zero W i ζ hζ hp2 hpL b c (hv ζ hζ))`. Conclude with `⟨h, by rw [hh]; ring⟩`.
-/
theorem q_pow_dvd [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hp : PD.p.Prime) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hinj : Function.Injective (algebraMap O LL)) {ζ₀ : LL} (hζ₀ : IsPrimitiveRoot ζ₀ PD.p)
    (i : ZMod n) (b : ℕ) (a : PowerSeries O)
    (hv : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → PowerSeries.X ^ b ∣ levC W i ζ a) :
    ∃ h : PowerSeries O, a = W.q₀ ^ b * h := by
  have hp2 : 2 ≤ PD.p := hp.two_le
  have hpL : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := W.v_l
    rw [h0, AddValuation.map_zero] at h1
    first
    | exact WithTop.top_ne_one h1
    | exact absurd h1 (by simp)
    | simp at h1
  induction b generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ b ih =>
    obtain ⟨c, rfl⟩ := q0_dvd_of_X_dvd_levC_primitive_roots W hp hpm hinj hζ₀ i a
      (fun ζ hζ => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero b)) (hv ζ hζ))
    obtain ⟨h, hh⟩ := ih c (fun ζ hζ => eq_of_mul_mul_eq_of_det_ne_zero W i ζ hζ hp2 hpL b c (hv ζ hζ))
    exact ⟨h, by rw [hh]; ring⟩

end Div

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LevW
