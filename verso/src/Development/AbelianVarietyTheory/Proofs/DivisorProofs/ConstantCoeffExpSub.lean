import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

namespace GlobalTheory.WachExp

open PowerSeries

/- English proof (translation)
Set `f : O⟦X⟧ →ₐ[O] L⟦X⟧` to `{ toRingHom := φ commutes' := fun a => (congrArg φ (PowerSeries.algebraMap_apply (R := O) (A := O))).trans ((hφ a).trans (PowerSeries.algebraMap_apply (R := O) (A := L)).symm) }`. Establish `h` using `GlobalTheory.HWL.Ser.map_gam_X f z hX 1 1 (by rw [pow_one]; exact hz) c (by simpa using hc)`. Rewrite `h` using `[pow_one]`. Conclude with `h`.
-/
theorem ringHom_gam_X {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L]
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] (φ : O⟦X⟧ →+* L⟦X⟧)
    (hφ : ∀ a : O, φ (C a) = C (algebraMap O L a)) (z : L) (hX : φ X = C z * exp L - 1) (hz : z ^ l = 1)
    (c : ℤ_[l]) (hc : (l : ℤ_[l]) ∣ c - 1) :
    φ (GlobalTheory.Fon.gam O c X) = C z * rescale (algebraMap ℤ_[l] L c) (exp L) - 1 := by
  let f : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
    { toRingHom := φ
      commutes' := fun a => (congrArg φ (PowerSeries.algebraMap_apply (R := O) (A := O))).trans
        ((hφ a).trans (PowerSeries.algebraMap_apply (R := O) (A := L)).symm) }
  have h := GlobalTheory.HWL.Ser.map_gam_X f z hX 1 1 (by rw [pow_one]; exact hz) c (by simpa using hc)
  rw [pow_one] at h
  exact h

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

/- English proof (translation)
Establish `h : ((z : Om l)) ^ l ^ 1 = 1`. Rewrite using `[pow_one]`. Conclude with `congrArg (fun y : ↥LL.1 => (y : Om l)) hz` after adjusting the coercions. Use `GlobalTheory.HWL.Ser.norm_sub_one_lt h` as an intermediate fact. Use `push_cast`.

Conclude with `this`.
-/
theorem norm_root_sub_one_lt {z : ↥LL.1} (hz : z ^ l = 1) : ‖(((z - 1 : ↥LL.1)) : Om l)‖ < 1 := by
  have h : ((z : Om l)) ^ l ^ 1 = 1 := by
    rw [pow_one]; exact_mod_cast congrArg (fun y : ↥LL.1 => (y : Om l)) hz
  have := GlobalTheory.HWL.Ser.norm_sub_one_lt h
  push_cast
  exact this

/- English proof (translation)
Rewrite using `[map_sub, map_mul, GlobalTheory.HWL.Ser.constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one]`.
-/
theorem constantCoeff_exp_sub (z a : ↥LL.1) :
    constantCoeff (C z * rescale a (exp ↥LL.1) - 1) = z - 1 := by
  rw [map_sub, map_mul, GlobalTheory.HWL.Ser.constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one]

/- English proof (translation)
Set `φ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1` to `{ toRingHom := φ, commutes' := fun a => by change φ (C a) = C (a : ↥LL.1); exact hφ a }`. Set `ψ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1` to `{ toRingHom := ψ, commutes' := fun a => by change ψ (C a) = C (a : ↥LL.1); exact hψ a }`. Establish `h` using `(GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x hx).1.unique (y₁ := φ') (y₂ := ψ') hφX hψX`. Conclude with `RingHom.ext fun f => AlgHom.congr_fun h f`.
-/
theorem ev_unique (x : PowerSeries ↥LL.1) (hx : ‖((constantCoeff x : ↥LL.1) : Om l)‖ < 1)
    (φ ψ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1)
    (hφ : ∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) (hψ : ∀ a : ↥(OL LL), ψ (C a) = C (a : ↥LL.1))
    (hφX : φ X = x) (hψX : ψ X = x) : φ = ψ := by
  let φ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := φ, commutes' := fun a => by change φ (C a) = C (a : ↥LL.1); exact hφ a }
  let ψ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := ψ, commutes' := fun a => by change ψ (C a) = C (a : ↥LL.1); exact hψ a }
  have h := (GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x hx).1.unique (y₁ := φ') (y₂ := ψ') hφX hψX
  exact RingHom.ext fun f => AlgHom.congr_fun h f

/- English proof (translation)
Establish `h` using `GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL (C z * rescale 1 (exp ↥LL.1) - 1) (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL hz)`. Take `⟨ev, hev, -⟩` from `h.1`. Use `⟨ev.toRingHom, fun a => ?_, by` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ev X = _`. Rewrite using `[hev, rescale_one, RingHom.id_apply]⟩`.

Use `ev.commutes a` as an intermediate fact. Conclude with `this`.
-/
theorem exists_ev (z : ↥LL.1) (hz : z ^ l = 1) :
    ∃ φ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1,
      (∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) ∧ φ X = C z * exp ↥LL.1 - 1 := by
  have h := GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL (C z * rescale 1 (exp ↥LL.1) - 1)
    (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL hz)
  obtain ⟨ev, hev, -⟩ := h.1
  refine ⟨ev.toRingHom, fun a => ?_, by
    change ev X = _
    rw [hev, rescale_one, RingHom.id_apply]⟩
  have := ev.commutes a
  exact this

/- English proof (translation)
Use extensionality with `n`. Apply the tactic sequence `by_cases h : n = 0 <;> simp [coeff_rescale, coeff_C, h]`.
-/
theorem rescale_C' (r z : ↥LL.1) : rescale r (C z) = C z := by
  ext n
  by_cases h : n = 0 <;> simp [coeff_rescale, coeff_C, h]

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

/- English proof (translation)
Introduce `l _ LL _ hex`. Take `⟨ζL, hζL⟩` from `hex`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `hfin` using `LL.2`. Establish `hint : IsIntegral ℤ_[l] ζL` using `IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)`.

Set `ζ : ↥(OL LL)` to `⟨ζL, hint⟩`. Establish `hζ : IsPrimitiveRoot ζ l` using `IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective`. Establish `hu : IsUnit (1 + (l : ℤ_[l]) * 1)`. Establish `h` using `IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))`. Break down `h with h | h` into its components or cases.

Conclude with `absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit`. Simplify `h` using `[sub_eq_add_neg]`. Set `u : ℤ_[l]ˣ` to `hu.unit`. Establish `hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1` using `hu.unit_spec`. Establish `hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL)`.

Use `(GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_` and prove the remaining obligations. Use `lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_` and prove the remaining obligations. Rewrite using `[PadicComplex.norm_extends]`. Conclude with `norm_root_sub_one_lt LL hζL.pow_eq_one`. Establish `hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1` using `fun b => by`.

Rewrite using `[← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]`. Use `choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)`. Use `⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨fun a => hC b a, ?_, fun f => ?_⟩⟩` and prove the remaining obligations. Take `⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1` from `X_dvd_iff.2 (by simp)`. Establish `hg0 : constantCoeff g = 1`.

Establish `h` using `congrArg (coeff 1) hg`. Rewrite `h` using `[coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[← h]`. Simplify using `[coeff_exp]`. Establish `hzb : ζL ^ b ≠ 0` using `pow_ne_zero _ (hζL.ne_zero (by omega))`.

Establish `hunit : IsUnit (C (ζL ^ b) * g)`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Simplify using `[hg0, hzb]`. Establish `hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g)`. Rewrite using `[map_sub, hev, hC]`.

Establish `hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1` using `rfl`. Rewrite using `[hco, map_sub (C : ↥LL.1 →+* _), map_one]`. Take the linear combination `(C (ζL ^ b)) * hg`. Rewrite using `[hcalc]`. Conclude with `associated_mul_unit_left X _ hunit`.

Use `set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def`. Establish `hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f`. Simplify using `only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]`. Conclude with `(congrFun (coe_substAlgHom _) f).symm`. Establish `hxz` using `ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b) (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩`.

Establish `huniq` using `ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1) (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b)) ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL))) ((rescale r).comp (ev b)) (fun a => by`. Express the relevant statement in the definitionally equal form `ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _`. Rewrite using `[GlobalTheory.Fon.gam_C, hC])`. Use the proof step `(fun a => by`. Express the relevant statement in the definitionally equal form `rescale r (ev b (C a)) = _`.

Rewrite using `[hC, rescale_C'])`. Use `hxz`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `rescale r (ev b X) = _`. Rewrite using `[hev, map_sub, map_mul, map_one, rescale_C'])`.

Rewrite using `[hact]`. Conclude with `RingHom.congr_fun huniq f`.
-/
theorem exists_locExp : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) →
    ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1),
      (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧
      ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1)
        (u : ℤ_[l]) (jj b) := by
  intro l _ LL _ hex
  obtain ⟨ζL, hζL⟩ := hex
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin := LL.2
  have hint : IsIntegral ℤ_[l] ζL := IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)
  let ζ : ↥(OL LL) := ⟨ζL, hint⟩
  have hζ : IsPrimitiveRoot ζ l :=
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective

  have hu : IsUnit (1 + (l : ℤ_[l]) * 1) := by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
    rcases h with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit
    · simpa [sub_eq_add_neg] using h
  let u : ℤ_[l]ˣ := hu.unit
  have hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1 := hu.unit_spec

  have hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL) := by
    refine (GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_
    refine lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_
    rw [PadicComplex.norm_extends]
    exact norm_root_sub_one_lt LL hζL.pow_eq_one
  have hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1 := fun b => by
    rw [← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]
  choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)
  refine ⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨fun a => hC b a, ?_, fun f => ?_⟩⟩
  · obtain ⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1 := X_dvd_iff.2 (by simp)
    have hg0 : constantCoeff g = 1 := by
      have h := congrArg (coeff 1) hg
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h
      rw [← h]; simp [coeff_exp]
    have hzb : ζL ^ b ≠ 0 := pow_ne_zero _ (hζL.ne_zero (by omega))
    have hunit : IsUnit (C (ζL ^ b) * g) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hg0, hzb]
    have hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g) := by
      rw [map_sub, hev, hC]
      have hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1 := rfl
      rw [hco, map_sub (C : ↥LL.1 →+* _), map_one]
      linear_combination (C (ζL ^ b)) * hg
    rw [hcalc]
    exact associated_mul_unit_left X _ hunit
  · set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def
    have hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f := by
      simp only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]
      exact (congrFun (coe_substAlgHom _) f).symm
    have hxz := ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b)
      (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩
    have huniq := ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1)
      (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b))
      ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL)))
      ((rescale r).comp (ev b))
      (fun a => by
        change ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _
        rw [GlobalTheory.Fon.gam_C, hC])
      (fun a => by
        change rescale r (ev b (C a)) = _
        rw [hC, rescale_C'])
      hxz
      (by
        change rescale r (ev b X) = _
        rw [hev, map_sub, map_mul, map_one, rescale_C'])
    rw [hact]
    exact RingHom.congr_fun huniq f

end GlobalTheory.WachExp
