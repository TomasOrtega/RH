import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EpsMeasFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVZpowDegEq

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.MeasModel

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ}

/- English proof (translation)
Conclude with `(Nat.card_pos (α := 𝓀[k]))` after adjusting the coercions.
-/
theorem q_pos : (0 : ℝ) < resCard k := by exact_mod_cast (Nat.card_pos (α := 𝓀[k]))

/- English proof (translation)
Rewrite using `[LGrp.nabs_eq_zpow]`. Conclude with `zpow_pos q_pos _`.
-/
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  rw [LGrp.nabs_eq_zpow]; exact zpow_pos q_pos _

/- English proof (translation)
Establish `h1 : valuation k (c' : k) = valuation k (c : k)` using `le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))`. Rewrite using `[LGrp.nabs_eq_zpow, LGrp.nabs_eq_zpow, valuation_eq_iff_ord.1 h1]`.
-/
theorem cond_eq {c c' : kˣ} (hc : HasConductor ψ c) (hc' : HasConductor ψ c') : nabs k c = nabs k c' := by
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [LGrp.nabs_eq_zpow, LGrp.nabs_eq_zpow, valuation_eq_iff_ord.1 h1]

/- English proof (translation)
Establish `key : ∀ b, ∀ x ∈ unitFilt k b, (χ * absPow k s) x = χ x` using `fun b x hx => by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, val_absPow, LGrp.nabs_eq_zpow, ord_eq_zero_iff.2 hx.1]`. Simplify using the standard rewrite rules. Use `and_congr (forall₂_congr fun x hx => by rw [key _ x hx]) (forall₂_congr fun b _ => ?_)` and prove the remaining obligations.

Conclude with `exists_congr fun x => and_congr_right fun hx => by rw [key _ x hx]`.
-/
theorem hasExponent_mul_absPow (s : ℝ) {a : ℕ} : HasExponent (χ * absPow k s) a ↔ HasExponent χ a := by
  have key : ∀ b, ∀ x ∈ unitFilt k b, (χ * absPow k s) x = χ x := fun b x hx => by
    apply Units.ext
    rw [MonoidHom.mul_apply, Units.val_mul, val_absPow, LGrp.nabs_eq_zpow, ord_eq_zero_iff.2 hx.1]
    simp
  refine and_congr (forall₂_congr fun x hx => by rw [key _ x hx]) (forall₂_congr fun b _ => ?_)
  exact exists_congr fun x => and_congr_right fun hx => by rw [key _ x hx]

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Establish `hq` using `q_pos (k := k)`. Establish `h1 : (resCard k : ℝ) ^ (-(a : ℝ) / 2) * (nabs k r ^ (-(1 / 2) : ℝ))⁻¹ = Real.sqrt (nabs k c)`. Rewrite using `[LGrp.nabs_eq_zpow, LGrp.nabs_eq_zpow, hR.1 r hr, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_neg hq.le, ← Real.rpow_add hq]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h1, MonoidHom.mul_apply, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val (absPow k _ r), val_absPow, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_cpow hq.le, Complex.ofReal_cpow (nabs_pos' r).le]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_shift {c : kˣ} {a : ℕ} {R : Finset kˣ} (hR : IsShellReps c a R) :
    (resCard k : ℂ) ^ (-(a : ℂ) / 2) *
      ∑ r ∈ R, ((((χ * absPow k ((-(1 / 2) : ℝ) : ℂ)) r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) =
    (Real.sqrt (nabs k c) : ℂ) * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hq := q_pos (k := k)
  have h1 : (resCard k : ℝ) ^ (-(a : ℝ) / 2) * (nabs k r ^ (-(1 / 2) : ℝ))⁻¹ = Real.sqrt (nabs k c) := by
    rw [LGrp.nabs_eq_zpow, LGrp.nabs_eq_zpow, hR.1 r hr, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
      ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_neg hq.le, ← Real.rpow_add hq]
    congr 1
    push_cast
    ring
  rw [← h1, MonoidHom.mul_apply, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val (absPow k _ r), val_absPow,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_cpow hq.le, Complex.ofReal_cpow (nabs_pos' r).le]
  push_cast
  ring

/- English proof (translation)
Establish `hs : (0 : ℝ) < t * Real.sqrt (nabs k c)` using `mul_pos ht (Real.sqrt_pos.2 (nabs_pos' c))`. Establish `key : ∀ S : ℂ, ((t * nabs k c : ℝ) : ℂ) * S = ((t * Real.sqrt (nabs k c) : ℝ) : ℂ) * ((Real.sqrt (nabs k c) : ℂ) * S)` using `fun S => by`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, mul_assoc t, Real.mul_self_sqrt (nabs_pos' c).le]`. Use `exists_congr fun c' => exists_congr fun a => exists_congr fun R => and_congr_right fun hc' => and_congr (hasExponent_mul_absPow _).symm (and_congr_right fun hR => ?_)` and prove the remaining obligations. Rewrite using `[sum_shift hR, ← cond_eq hc hc', key, mul_right_inj' (Complex.ofReal_ne_zero.2 hs.ne')]`.
-/
theorem isTateMeas_iff {c : kˣ} (hc : HasConductor ψ c) {t : ℝ} (ht : 0 < t) {e : ℂ} :
    IsTateMeas ψ t χ (((t * Real.sqrt (nabs k c) : ℝ) : ℂ) * e) ↔
      IsTateEps ψ (χ * absPow k ((-(1 / 2) : ℝ) : ℂ)) e := by
  have hs : (0 : ℝ) < t * Real.sqrt (nabs k c) := mul_pos ht (Real.sqrt_pos.2 (nabs_pos' c))
  have key : ∀ S : ℂ, ((t * nabs k c : ℝ) : ℂ) * S =
      ((t * Real.sqrt (nabs k c) : ℝ) : ℂ) * ((Real.sqrt (nabs k c) : ℂ) * S) := fun S => by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_assoc t, Real.mul_self_sqrt (nabs_pos' c).le]
  refine exists_congr fun c' => exists_congr fun a => exists_congr fun R => and_congr_right fun hc' =>
    and_congr (hasExponent_mul_absPow _).symm (and_congr_right fun hR => ?_)
  rw [sum_shift hR, ← cond_eq hc hc', key, mul_right_inj' (Complex.ofReal_ne_zero.2 hs.ne')]

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_hasConductor_of_continuous ψ hψ h1`. Establish `hs : ((t * Real.sqrt (nabs k c) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (mul_pos ht (Real.sqrt_pos.2 (nabs_pos' c))).ne'`. Establish `key : ∀ e, IsTateMeas ψ t χ e → IsTateEps ψ (χ * absPow k ((-(1 / 2) : ℝ) : ℂ)) (((t * Real.sqrt (nabs k c) : ℝ) : ℂ)⁻¹ * e)` using `fun e he => (isTateMeas_iff hc ht).1 (by rwa [mul_inv_cancel_left₀ hs])`. Take `⟨a, ha⟩` from `exists_hasExponent hχ`. Take `⟨R, hR⟩` from `exists_isShellReps c a`.

Use `⟨existsUnique_of_exists_of_unique ⟨_, c, a, R, hc, ha, hR, rfl⟩ fun e e' he he' => ?_, fun e he h0 => ?_⟩` and prove the remaining obligations. Conclude with `mul_left_cancel₀ (inv_ne_zero hs) ((key e he).unique (key e' he'))`. Conclude with `(key e he).ne_zero (by rw [h0, mul_zero])`.
-/
theorem existsUnique_isTateMeas (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hχ : IsSmoothChar χ) {t : ℝ} (ht : 0 < t) :
    (∃! e : ℂ, IsTateMeas ψ t χ e) ∧ ∀ e, IsTateMeas ψ t χ e → e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hs : ((t * Real.sqrt (nabs k c) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos ht (Real.sqrt_pos.2 (nabs_pos' c))).ne'
  have key : ∀ e, IsTateMeas ψ t χ e →
      IsTateEps ψ (χ * absPow k ((-(1 / 2) : ℝ) : ℂ)) (((t * Real.sqrt (nabs k c) : ℝ) : ℂ)⁻¹ * e) := fun e he =>
    (isTateMeas_iff hc ht).1 (by rwa [mul_inv_cancel_left₀ hs])
  obtain ⟨a, ha⟩ := exists_hasExponent hχ
  obtain ⟨R, hR⟩ := exists_isShellReps c a
  refine ⟨existsUnique_of_exists_of_unique ⟨_, c, a, R, hc, ha, hR, rfl⟩ fun e e' he he' => ?_, fun e he h0 => ?_⟩
  · exact mul_left_cancel₀ (inv_ne_zero hs) ((key e he).unique (key e' he'))
  · exact (key e he).ne_zero (by rw [h0, mul_zero])

/- English proof (translation)
Take `⟨c', a, R, hc', ha, hR, he⟩` from `isTateEps_of_isUnram hc hχ`. Take `rfl` from `ha.unique (hasExponent_zero_iff.2 hχ)`. Use `⟨c', 0, R, hc', ha, hR, ?_⟩` and prove the remaining obligations. Rewrite using `[he, cond_eq hc hc']`. Simplify using the standard rewrite rules.
-/
theorem isTateMeas_of_isUnram {c : kˣ} (hc : HasConductor ψ c) (hχ : IsUnram χ) (t : ℝ) :
    IsTateMeas ψ t χ (((t * nabs k c : ℝ) : ℂ) * ((χ c)⁻¹ : ℂˣ)) := by
  obtain ⟨c', a, R, hc', ha, hR, he⟩ := isTateEps_of_isUnram hc hχ
  obtain rfl := ha.unique (hasExponent_zero_iff.2 hχ)
  refine ⟨c', 0, R, hc', ha, hR, ?_⟩
  rw [he, cond_eq hc hc']
  simp

open Classical in

def condAbs (ψ : AddChar k Circle) : ℝ := if h : ∃ c, HasConductor ψ c then nabs k h.choose else 1

/- English proof (translation)
Establish `h : ∃ c, HasConductor ψ c` using `⟨c, hc⟩`. Rewrite using `[condAbs, dif_pos h, cond_eq h.choose_spec hc]`.
-/
theorem condAbs_eq {c : kˣ} (hc : HasConductor ψ c) : condAbs ψ = nabs k c := by
  have h : ∃ c, HasConductor ψ c := ⟨c, hc⟩
  rw [condAbs, dif_pos h, cond_eq h.choose_spec hc]

/- English proof (translation)
Unfold `condAbs`. Use `split_ifs`. Conclude with `nabs_pos' _`. Conclude with `one_pos`.
-/
theorem condAbs_pos (ψ : AddChar k Circle) : 0 < condAbs ψ := by
  unfold condAbs; split_ifs
  · exact nabs_pos' _
  · exact one_pos

end Tate

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

section

variable {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}

/- English proof (translation)
Rewrite using `[WD.lpOfChar, WD.lpOfChar, WD.lpTw_mk]`. Use `WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩` and prove the remaining obligations. Use `DFunLike.congr_fun (ha.absPow_comp s) σ` as an intermediate fact. Use function extensionality and compare the values at `i`. Simplify using `only [MonoidHom.comp_apply] at this`.

Simplify using `[WDRep.tw, this, mul_comm, mul_left_comm]`.
-/
theorem lpTw_lpOfChar {a : Weil h →* (v.adicCompletion K)ˣ} (ha : IsLocalArtin h a)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) (s : ℝ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).lpTw s =
      WD.lpOfChar h ((χ * absPow _ s).comp a) (ha.smooth (hχ.mul (isSmoothChar_absPow _))) := by
  rw [WD.lpOfChar, WD.lpOfChar, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩
  have := DFunLike.congr_fun (ha.absPow_comp s) σ
  funext i
  simp only [MonoidHom.comp_apply] at this
  simp [WDRep.tw, this, mul_comm, mul_left_comm]

variable [Algebra K L]

/- English proof (translation)
Take `⟨m, n, a, b, j, rfl, rfl, hn, -⟩` from `H`. Simplify using `using hn`.
-/
theorem induces_dim {x : WD h'} {y : WD h} (H : Induces x y) : y.lpDim = Module.finrank K L * x.lpDim := by
  obtain ⟨m, n, a, b, j, rfl, rfl, hn, -⟩ := H
  simpa using hn

/- English proof (translation)
Take `⟨m, n, a, b, j, rfl, rfl, hn, h1, h2⟩` from `H`. Use `⟨m, n, a.tw s, b.tw s, j, (WD.lpTw_mk _ _).symm, (WD.lpTw_mk _ _).symm, hn, fun σ' σ hσ u => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[WDRep.tw_ρ, WDRep.tw_ρ, GlobalTheory.EpsInduction.normV_cpow_deg_eq _ hσ]`. Simplify using `[h1 σ' σ hσ]`. Rewrite using `[eq_top_iff, ← h2, Submodule.span_le]`.

Introduce and unpack `_ ⟨⟨σ, u⟩, rfl⟩`. Establish `hne : (((normV v : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ ≠ 0` using `zpow_ne_zero _ (qPow v s).ne_zero`. Use `Submodule.subset_span ⟨(σ, ((((normV v : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ)⁻¹ • u), ?_⟩` and prove the remaining obligations. Use `show (b.tw s).ρ σ (j _) = _`. Rewrite using `[WDRep.tw_ρ, map_smul, map_smul, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]`.
-/
theorem induces_tw {x : WD h'} {y : WD h} (H : Induces x y) (s : ℝ) : Induces (x.lpTw s) (y.lpTw s) := by
  obtain ⟨m, n, a, b, j, rfl, rfl, hn, h1, h2⟩ := H
  refine ⟨m, n, a.tw s, b.tw s, j, (WD.lpTw_mk _ _).symm, (WD.lpTw_mk _ _).symm, hn, fun σ' σ hσ u => ?_, ?_⟩
  · rw [WDRep.tw_ρ, WDRep.tw_ρ, GlobalTheory.EpsInduction.normV_cpow_deg_eq _ hσ]
    simp [h1 σ' σ hσ]
  · rw [eq_top_iff, ← h2, Submodule.span_le]
    rintro _ ⟨⟨σ, u⟩, rfl⟩
    have hne : (((normV v : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ ≠ 0 := zpow_ne_zero _ (qPow v s).ne_zero
    refine Submodule.subset_span ⟨(σ, ((((normV v : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ)⁻¹ • u), ?_⟩
    show (b.tw s).ρ σ (j _) = _
    rw [WDRep.tw_ρ, map_smul, map_smul, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]

end

def measOf (ε : EpsFamily A) : EpsMeasFamily A := fun L _ _ _ _ v h ψ t x =>
  WD.unitOf ((t * Real.sqrt (condAbs ψ) : ℝ) : ℂ) ^ x.lpDim * ε L v h ψ (x.lpTw (-(1 / 2)))

def centreOf (ε : EpsMeasFamily A) : EpsFamily A := fun L _ _ _ _ v h ψ x =>
  ε L v h ψ (Real.sqrt (condAbs ψ))⁻¹ (x.lpTw (1 / 2))

/- English proof (translation)
Establish `hne : ∀ {t c : ℝ}, 0 < t → 0 < c → ((t * Real.sqrt c : ℝ) : ℂ) ≠ 0` using `fun ht hc => Complex.ofReal_ne_zero.2 (mul_pos ht (Real.sqrt_pos.2 hc)).ne'`. Use `⟨fun L _ _ _ _ v h ψ hψ h1 t ht x y => ?_, fun L _ _ _ _ v h ψ hψ h1 t ht a ha x => ?_, fun K L _ _ _ _ _ _ _ _ _ _ v v' h h' hL ψ ψ' hψ h1 hψ' htr t t' ht ht' x₁ x₂ y₁ y₂ H₁ H₂ hd => ?_, fun L _ _ _ _ v h ψ hψ h1 t ht a ha χ hχ => ?_⟩` and prove the remaining obligations. Simplify using `only [measOf]`. Rewrite using `[WD.lpTw_sum, H.add L v h ψ hψ h1, WD.lpDim_sum, pow_add, mul_mul_mul_comm]`. Simplify using `only [measOf, Units.val_mul, Units.val_pow_eq_pow_val]`.

Rewrite using `[WD.coe_unitOf (hne (mul_pos ha ht) (condAbs_pos ψ)), WD.coe_unitOf (hne ht (condAbs_pos ψ))]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `H.ind K L v v' h h' hL ψ ψ' hψ h1 hψ' htr _ _ _ _ (induces_tw H₁ (-(1 / 2))) (induces_tw H₂ (-(1 / 2))) (by rw [WD.lpDim_tw, WD.lpDim_tw, hd])` as an intermediate fact. Simplify using `only [measOf]`.

Rewrite using `[mul_mul_mul_comm, this, induces_dim H₁, induces_dim H₂, hd, mul_mul_mul_comm]`. Take `⟨c, hc⟩` from `exists_hasConductor_of_continuous ψ hψ h1`. Simplify using `only [measOf, Units.val_mul, Units.val_pow_eq_pow_val]`. Rewrite using `[WD.coe_unitOf (hne ht (condAbs_pos ψ)), lpTw_lpOfChar ha hχ, condAbs_eq hc, WD.lpOfChar, WD.lpDim_mk, Module.finrank_fin_fun, pow_one, isTateMeas_iff hc ht]`. Conclude with `H.char L v h ψ hψ h1 a ha _ (hχ.mul (isSmoothChar_absPow _))`.
-/
theorem isDeligneMeas_measOf {ε : EpsFamily A} (H : IsDeligneEps ε) : IsDeligneMeas (measOf ε) := by
  have hne : ∀ {t c : ℝ}, 0 < t → 0 < c → ((t * Real.sqrt c : ℝ) : ℂ) ≠ 0 := fun ht hc =>
    Complex.ofReal_ne_zero.2 (mul_pos ht (Real.sqrt_pos.2 hc)).ne'
  refine ⟨fun L _ _ _ _ v h ψ hψ h1 t ht x y => ?_, fun L _ _ _ _ v h ψ hψ h1 t ht a ha x => ?_,
    fun K L _ _ _ _ _ _ _ _ _ _ v v' h h' hL ψ ψ' hψ h1 hψ' htr t t' ht ht' x₁ x₂ y₁ y₂ H₁ H₂ hd => ?_,
    fun L _ _ _ _ v h ψ hψ h1 t ht a ha χ hχ => ?_⟩
  · simp only [measOf]
    rw [WD.lpTw_sum, H.add L v h ψ hψ h1, WD.lpDim_sum, pow_add, mul_mul_mul_comm]
  · simp only [measOf, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [WD.coe_unitOf (hne (mul_pos ha ht) (condAbs_pos ψ)), WD.coe_unitOf (hne ht (condAbs_pos ψ))]
    push_cast
    ring
  · have := H.ind K L v v' h h' hL ψ ψ' hψ h1 hψ' htr _ _ _ _ (induces_tw H₁ (-(1 / 2))) (induces_tw H₂ (-(1 / 2)))
      (by rw [WD.lpDim_tw, WD.lpDim_tw, hd])
    simp only [measOf]
    rw [mul_mul_mul_comm, this, induces_dim H₁, induces_dim H₂, hd, mul_mul_mul_comm]
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    simp only [measOf, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [WD.coe_unitOf (hne ht (condAbs_pos ψ)), lpTw_lpOfChar ha hχ, condAbs_eq hc, WD.lpOfChar, WD.lpDim_mk,
      Module.finrank_fin_fun, pow_one, isTateMeas_iff hc ht]
    exact H.char L v h ψ hψ h1 a ha _ (hχ.mul (isSmoothChar_absPow _))

/- English proof (translation)
Establish `hp : ∀ {c : ℝ}, 0 < c → 0 < (Real.sqrt c)⁻¹` using `fun hc => inv_pos.2 (Real.sqrt_pos.2 hc)`. Use `⟨fun L _ _ _ _ v h ψ hψ h1 x y => ?_, fun L _ _ _ _ v h ψ hψ h1 a ha χ hχ => ?_, fun K L _ _ _ _ _ _ _ _ _ _ v v' h h' hL ψ ψ' hψ h1 hψ' htr x₁ x₂ y₁ y₂ H₁ H₂ hd => ?_⟩` and prove the remaining obligations. Simplify using `only [centreOf]`. Rewrite using `[WD.lpTw_sum, H.add L v h ψ hψ h1 _ (hp (condAbs_pos ψ))]`. Take `⟨c, hc⟩` from `exists_hasConductor_of_continuous ψ hψ h1`.

Simplify using `only [centreOf]`. Rewrite using `[lpTw_lpOfChar ha hχ]`. Establish `h2` using `H.char L v h ψ hψ h1 _ (hp (condAbs_pos ψ)) a ha _ (hχ.mul (isSmoothChar_absPow ((1 / 2 : ℝ) : ℂ)))`. Establish `h3 : χ * absPow _ ((1 / 2 : ℝ) : ℂ) * absPow _ ((-(1 / 2) : ℝ) : ℂ) = χ`. Use extensionality with `x`.

Rewrite using `[MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, val_absPow, val_absPow, mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (nabs_pos' x).ne')]`. Simplify using the standard rewrite rules. Establish `h4` using `(isTateMeas_iff hc (hp (condAbs_pos ψ))).1 (by`. Rewrite using `[← condAbs_eq hc, inv_mul_cancel₀ (Real.sqrt_pos.2 (condAbs_pos ψ)).ne', Complex.ofReal_one, one_mul]`. Conclude with `h2)`.

Rewrite `h4` using `[h3]`. Then use the resulting hypothesis. Conclude with `H.ind K L v v' h h' hL ψ ψ' hψ h1 hψ' htr _ _ (hp (condAbs_pos ψ)) (hp (condAbs_pos ψ')) _ _ _ _ (induces_tw H₁ _) (induces_tw H₂ _) (by rw [WD.lpDim_tw, WD.lpDim_tw, hd])`.
-/
theorem isDeligneEps_centreOf {ε : EpsMeasFamily A} (H : IsDeligneMeas ε) : IsDeligneEps (centreOf ε) := by
  have hp : ∀ {c : ℝ}, 0 < c → 0 < (Real.sqrt c)⁻¹ := fun hc => inv_pos.2 (Real.sqrt_pos.2 hc)
  refine ⟨fun L _ _ _ _ v h ψ hψ h1 x y => ?_, fun L _ _ _ _ v h ψ hψ h1 a ha χ hχ => ?_,
    fun K L _ _ _ _ _ _ _ _ _ _ v v' h h' hL ψ ψ' hψ h1 hψ' htr x₁ x₂ y₁ y₂ H₁ H₂ hd => ?_⟩
  · simp only [centreOf]
    rw [WD.lpTw_sum, H.add L v h ψ hψ h1 _ (hp (condAbs_pos ψ))]
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    simp only [centreOf]
    rw [lpTw_lpOfChar ha hχ]
    have h2 := H.char L v h ψ hψ h1 _ (hp (condAbs_pos ψ)) a ha _ (hχ.mul (isSmoothChar_absPow ((1 / 2 : ℝ) : ℂ)))
    have h3 : χ * absPow _ ((1 / 2 : ℝ) : ℂ) * absPow _ ((-(1 / 2) : ℝ) : ℂ) = χ := by
      ext x
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, val_absPow, val_absPow, mul_assoc,
        ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (nabs_pos' x).ne')]
      simp
    have h4 := (isTateMeas_iff hc (hp (condAbs_pos ψ))).1 (by
      rw [← condAbs_eq hc, inv_mul_cancel₀ (Real.sqrt_pos.2 (condAbs_pos ψ)).ne', Complex.ofReal_one, one_mul]
      exact h2)
    rwa [h3] at h4
  · exact H.ind K L v v' h h' hL ψ ψ' hψ h1 hψ' htr _ _ (hp (condAbs_pos ψ)) (hp (condAbs_pos ψ')) _ _ _ _
      (induces_tw H₁ _) (induces_tw H₂ _) (by rw [WD.lpDim_tw, WD.lpDim_tw, hd])

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨_, H⟩ => ⟨_, isDeligneEps_centreOf H⟩, fun ⟨_, H⟩ => ⟨_, isDeligneMeas_measOf H⟩⟩`.
-/
theorem exists_iff : (∃ ε : EpsMeasFamily A, IsDeligneMeas ε) ↔ ∃ ε : EpsFamily A, IsDeligneEps ε :=
  ⟨fun ⟨_, H⟩ => ⟨_, isDeligneEps_centreOf H⟩, fun ⟨_, H⟩ => ⟨_, isDeligneMeas_measOf H⟩⟩

/- English proof (translation)
Take `⟨rc, ⟨a, ha, ε, hε, -⟩, -⟩` from `hL.1 E Ω A w h`. Conclude with `⟨⟨a, ha⟩, _, isDeligneMeas_measOf hε⟩`.
-/
theorem exists_of_localLanglands (hL : GlobalTheory.Published.LocalLanglandsGL) (E : Type) [Field E] [NumberField E] [Algebra E Ω]
    [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) :
    (∃ a, IsLocalArtin h a) ∧ ∃ ε : EpsMeasFamily A, IsDeligneMeas ε := by
  obtain ⟨rc, ⟨a, ha, ε, hε, -⟩, -⟩ := hL.1 E Ω A w h
  exact ⟨⟨a, ha⟩, _, isDeligneMeas_measOf hε⟩

end GlobalTheory.LocLanglands.MeasModel

end
