import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.CycRing

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih]`. Use function extensionality and compare the values at `i`.

Simplify using `[letφ]`.
-/
theorem letφ_pow_const {O : Type} [CommRing O] {n : ℕ} (f : PowerSeries O →ₐ[O] PowerSeries O)
    (k : ℕ) (c : PowerSeries O) :
    (letφ (n := n) f ^ k) (fun _ => c) = fun _ => (f ^ k) c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih]
    funext i
    simp [letφ]

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg (PowerSeries.coeff 1) h`. Rewrite `h1` using `[GlobalTheory.Cyc.XX, map_sub, PowerSeries.coeff_one_pow]`. Simplify using `[PowerSeries.coeff_one] at h1`. Conclude with `hl h1.1`.
-/
theorem XX_ne_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (hl : (l : O) ≠ 0) (s : ℕ) : GlobalTheory.Cyc.XX l O s ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [GlobalTheory.Cyc.XX, map_sub, PowerSeries.coeff_one_pow] at h1
  simp [PowerSeries.coeff_one] at h1
  exact hl h1.1

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW l _ K s LL h W`. Take `⟨χ₀, hχ₀, -, honto⟩` from `GlobalTheory.Cyc.exists_integral_cyclotomicChar l (D.loc l)`. Take `⟨hdvr, hcomp, hl0, hlu, -⟩` from `GlobalTheory.Per.integers_completeDVR l LL`. Establish `hWs : W.s = s` using `(HW l).W_s K s LL h`. Use `clear_value W`.

Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Establish `hcoe : ∀ z : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l])`. Introduce `z`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]`. Both sides reduce to the same expression.

Establish `hinjO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1)` using `Subtype.val_injective`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL))`. Introduce `a b hab`. Use `congrArg (algebraMap ↥(OL LL) ↥LL.1) hab` as an intermediate fact. Rewrite `this` using `[hcoe, hcoe]`.

Conclude with `Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective this)`. Establish `hres : ∀ g : ↥(GK K), algebraMap ℤ_[l] ↥(OL LL) (χ₀ (g : GQ l) : ℤ_[l]) = (W.χΓ (W.resΓ g) : ↥(OL LL))`. Introduce `g`. Apply `hinjO` to reduce the goal to its premises. Rewrite using `[hcoe, W.χΓ_res, hχ₀, (D.loc l).PD_χ]`.

Use `choose sec hsec using W.resΓ_onto`. Establish `hsec' : ∀ g : W.Gam, algebraMap ℤ_[l] ↥(OL LL) (χ₀ (sec g : GQ l) : ℤ_[l]) = (W.χΓ g : ↥(OL LL))` using `fun g => by rw [hres, hsec]`. Set `χ : W.Gam →* ℤ_[l]ˣ` to `MonoidHom.mk' (fun g => χ₀ (sec g : GQ l)) (fun a b => by`. Apply `Units.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, map_mul, hsec', hsec', hsec', map_mul, Units.val_mul])`. Establish `hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))` using `hsec'`. Establish `hφX : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1`. Rewrite using `[W.φ₀_X, W.q₀_def, hp]`. Establish `hact : ∀ g, W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l])` using `fun g => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l]) hφX (W.γ₀_comm g) (W.γ₀_X g).1 (by rw [(W.γ₀_X g).2, hχ])`.

Establish `hφ` using `(hact 1).1`. Establish `hX : W.X = fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s`. Rewrite using `[← GlobalTheory.Cyc.Series.phi_pow_X, ← hφ, ← letφ_pow_const, LocWach.X, hWs]`. Both sides reduce to the same expression. Use `⟨χ, hχ, hφ, fun g => (hact g).2, fun i => by rw [hX], fun i => ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrFun W.φA_X i`. Rewrite `h1` using `[hX, Pi.mul_apply]`. Establish `h2 : W.φA (fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s) i = W.φ₀ (GlobalTheory.Cyc.XX l ↥(OL LL) s)`. Simplify using `[LocWach.φA, letφ]`. Rewrite `h1` using `[h2, hφ, GlobalTheory.Cyc.Series.phi_XX]`.

Conclude with `(mul_left_cancel₀ (XX_ne_zero l _ hl0 s) h1).symm`. Establish `h1` using `W.gam_gen`. Rewrite `h1` using `[hWs, ← hχ, hcoe]`. Establish `h2` using `((GlobalTheory.HWL.NormVal.locPrime_v_normalised l (D.loc l) LL).1 _ (s : ℚ)).1 (by exact_mod_cast h1)`. Establish `h3 : ((algebraMap ℚ_[l] ↥LL.1 ((χ W.gam : ℤ_[l]) : ℚ_[l]) - 1 : ↥LL.1) : Om l) = algebraMap ℚ_[l] (Om l) (((χ W.gam : ℤ_[l]) - 1 : ℤ_[l]) : ℚ_[l])`.

Rewrite using `[PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]`. Both sides reduce to the same expression. Rewrite `h2` using `[h3, norm_algebraMap']`. Rewrite using `[PadicInt.norm_def, h2, ← Real.rpow_intCast]`. Use `push_cast`.

Both sides reduce to the same expression. Introduce `u hu`. Establish `hd : (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1` using `Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ s).1 hu)`. Take `⟨g, hg, hgu⟩` from `honto K s h.2.2.1 u hd`. Use `⟨W.resΓ ⟨g, hg⟩, Units.ext (hinj ?_)⟩` and prove the remaining obligations.

Rewrite using `[hχ, ← hres, hgu]`.
-/
theorem rings_cyclotomic : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ (∀ g, W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l])) ∧ (∀ i, W.X i = GlobalTheory.Cyc.XX l ↥(OL LL) s) ∧ (∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s) ∧ ‖(χ W.gam : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ ∀ u : ℤ_[l]ˣ, ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) → ∃ g, χ g = u := by
  intro D HW l _ K s LL h W
  obtain ⟨χ₀, hχ₀, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l (D.loc l)
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hWs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hcoe : ∀ z : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z)
      = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
    intro z
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  have hinjO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hab
    rw [hcoe, hcoe] at this
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective this)
  have hres : ∀ g : ↥(GK K), algebraMap ℤ_[l] ↥(OL LL) (χ₀ (g : GQ l) : ℤ_[l])
      = (W.χΓ (W.resΓ g) : ↥(OL LL)) := by
    intro g
    apply hinjO
    rw [hcoe, W.χΓ_res, hχ₀, (D.loc l).PD_χ]
  choose sec hsec using W.resΓ_onto
  have hsec' : ∀ g : W.Gam, algebraMap ℤ_[l] ↥(OL LL) (χ₀ (sec g : GQ l) : ℤ_[l])
      = (W.χΓ g : ↥(OL LL)) := fun g => by rw [hres, hsec]
  let χ : W.Gam →* ℤ_[l]ˣ := MonoidHom.mk' (fun g => χ₀ (sec g : GQ l)) (fun a b => by
    apply Units.ext
    apply hinj
    rw [Units.val_mul, map_mul, hsec', hsec', hsec', map_mul, Units.val_mul])
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL)) := hsec'
  have hφX : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 := by
    rw [W.φ₀_X, W.q₀_def, hp]
  have hact : ∀ g, W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l]) :=
    fun g => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l]) hφX (W.γ₀_comm g)
      (W.γ₀_X g).1 (by rw [(W.γ₀_X g).2, hχ])
  have hφ := (hact 1).1
  have hX : W.X = fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s := by
    rw [← GlobalTheory.Cyc.Series.phi_pow_X, ← hφ, ← letφ_pow_const, LocWach.X, hWs]
    rfl
  refine ⟨χ, hχ, hφ, fun g => (hact g).2, fun i => by rw [hX], fun i => ?_, ?_, ?_⟩
  · have h1 := congrFun W.φA_X i
    rw [hX, Pi.mul_apply] at h1
    have h2 : W.φA (fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s) i = W.φ₀ (GlobalTheory.Cyc.XX l ↥(OL LL) s) := by
      simp [LocWach.φA, letφ]
    rw [h2, hφ, GlobalTheory.Cyc.Series.phi_XX] at h1
    exact (mul_left_cancel₀ (XX_ne_zero l _ hl0 s) h1).symm
  · have h1 := W.gam_gen
    rw [hWs, ← hχ, hcoe] at h1
    have h2 := ((GlobalTheory.HWL.NormVal.locPrime_v_normalised l (D.loc l) LL).1 _ (s : ℚ)).1 (by exact_mod_cast h1)
    have h3 : ((algebraMap ℚ_[l] ↥LL.1 ((χ W.gam : ℤ_[l]) : ℚ_[l]) - 1 : ↥LL.1) : Om l)
        = algebraMap ℚ_[l] (Om l) (((χ W.gam : ℤ_[l]) - 1 : ℤ_[l]) : ℚ_[l]) := by
      rw [PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]
      rfl
    rw [h3, norm_algebraMap'] at h2
    rw [PadicInt.norm_def, h2, ← Real.rpow_intCast]
    push_cast
    rfl
  · intro u hu
    have hd : (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 :=
      Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ s).1 hu)
    obtain ⟨g, hg, hgu⟩ := honto K s h.2.2.1 u hd
    refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (hinj ?_)⟩
    rw [hχ, ← hres, hgu]

end GlobalTheory.NL.CycRing
