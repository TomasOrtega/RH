import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSchrodingerLinePureTensorZeroStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaDeriv

/- English proof (translation)
Take `⟨-, ⟨K, hK, hKz⟩, hdec⟩` from `hΦ`. Take `⟨k, hk⟩` from `GlobalTheory.SumMaj.summable_majorant F N hF K hK`. Take `⟨C, hC⟩` from `hdec k`. Establish `hC0 : 0 ≤ C` using `le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k)) (hC 0)`. Take `⟨c, hcs, hc0, hcb⟩` from `hk ω hω`.

Use `⟨C, c, hcs, hc0, fun ξ y hy => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hmem : fin (rat ξ + y) ∈ K`. Establish `h1` using `hcb ξ y hy hmem`. Establish `h2` using `hC (rat ξ + y)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hKz _ hmem, norm_zero]`. Conclude with `mul_nonneg hC0 (hc0 ξ)`.
-/
theorem decay_majorant {F : Type} [Field F] [NumberField F] {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ C : ℝ, ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
      ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨C, c, hcs, hc0, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]

/- English proof (translation)
Rewrite using `[schr_schr, GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero F N hF M hM t h, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add]`.
-/
theorem schr_line_add (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (t h : ℝ) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (M (t + h)) Φ = GlobalTheory.WeilM.schr ψ (M t) (GlobalTheory.WeilM.schr ψ (M h) Φ) := by
  rw [schr_schr, GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero F N hF M hM t h, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Take `⟨f', hf'⟩` from `GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero F N ψ hF hψ M hM f g hg`. Conclude with `⟨_, Submodule.subset_span ⟨f', g, hg, rfl⟩, hf'⟩`.

Consider the case `zero`. Use `⟨0, zero_mem _, fun z => ?_⟩` and prove the remaining obligations. Establish `e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (0 : (Fin N → AF F) → ℂ) z) = fun _ => 0`. Use function extensionality and compare the values at `s`. Simplify using `[GlobalTheory.WeilM.schr]`.

Rewrite using `[e]`. Conclude with `hasDerivAt_const 0 0`. Consider the case `add Φ Ψ _ _ h1 h2`. Take `⟨Φ', h1m, h1d⟩` from `h1`. Take `⟨Ψ', h2m, h2d⟩` from `h2`.

Use `⟨Φ' + Ψ', add_mem h1m h2m, fun z => ?_⟩` and prove the remaining obligations. Establish `e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (Φ + Ψ) z) = fun s => GlobalTheory.WeilM.schr ψ (M s) Φ z + GlobalTheory.WeilM.schr ψ (M s) Ψ z`. Use function extensionality and compare the values at `s`. Simplify using `[GlobalTheory.WeilM.schr, mul_add]`. Rewrite using `[e]`.

Conclude with `(h1d z).add (h2d z)`. Consider the case `smul c Φ _ h`. Take `⟨Φ', hm, hd⟩` from `h`. Use `⟨c • Φ', Submodule.smul_mem _ c hm, fun z => ?_⟩` and prove the remaining obligations. Establish `e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (c • Φ) z) = fun s => c * GlobalTheory.WeilM.schr ψ (M s) Φ z`.

Use function extensionality and compare the values at `s`. Simplify using `[GlobalTheory.WeilM.schr]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(hd z).const_mul c`.
-/
theorem exists_deriv_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {M : ℝ →+ VA F N} (hM : IsRealLine M) {Φ : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) :
    ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N), ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨f', hf'⟩ := GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero F N ψ hF hψ M hM f g hg
    exact ⟨_, Submodule.subset_span ⟨f', g, hg, rfl⟩, hf'⟩
  | zero =>
    refine ⟨0, zero_mem _, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (0 : (Fin N → AF F) → ℂ) z) = fun _ => 0 := by
      funext s; simp [GlobalTheory.WeilM.schr]
    rw [e]
    exact hasDerivAt_const 0 0
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨Φ', h1m, h1d⟩ := h1
    obtain ⟨Ψ', h2m, h2d⟩ := h2
    refine ⟨Φ' + Ψ', add_mem h1m h2m, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (Φ + Ψ) z) =
        fun s => GlobalTheory.WeilM.schr ψ (M s) Φ z + GlobalTheory.WeilM.schr ψ (M s) Ψ z := by
      funext s; simp [GlobalTheory.WeilM.schr, mul_add]
    rw [e]
    exact (h1d z).add (h2d z)
  | smul c Φ _ h =>
    obtain ⟨Φ', hm, hd⟩ := h
    refine ⟨c • Φ', Submodule.smul_mem _ c hm, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (c • Φ) z) = fun s => c * GlobalTheory.WeilM.schr ψ (M s) Φ z := by
      funext s; simp [GlobalTheory.WeilM.schr]; ring
    rw [e]
    exact (hd z).const_mul c

/- English proof (translation)
Establish `h1 : HasDerivAt (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) (t - t)`. Establish `e : (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) = fun h => ψ (z ⬝ᵥ (M t).2 + ⅟(2 : AF F) * ((M t).1 ⬝ᵥ (M t).2)) * GlobalTheory.WeilM.schr ψ (M h) Φ (z + (M t).1)`. Use function extensionality and compare the values at `h`. Rewrite using `[schr_line_add hF ψ hM]`. Both sides reduce to the same expression.

Rewrite using `[e, sub_self]`. Conclude with `(hd (z + (M t).1)).const_mul _`. Establish `h2` using `h1.comp_sub_const t t`. Simplify `h2` using `only [add_sub_cancel]`.
-/
theorem hasDerivAt_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    {Φ Φ' : (Fin N → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0)
    (z : Fin N → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) (t - t) := by
    have e : (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) = fun h =>
        ψ (z ⬝ᵥ (M t).2 + ⅟(2 : AF F) * ((M t).1 ⬝ᵥ (M t).2)) * GlobalTheory.WeilM.schr ψ (M h) Φ (z + (M t).1) := by
      funext h
      rw [schr_line_add hF ψ hM]
      rfl
    rw [e, sub_self]
    exact (hd (z + (M t).1)).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

end GlobalTheory.ThetaDeriv

open GlobalTheory.ThetaDeriv in

/- English proof (translation)
Introduce `F _ _ N _ ψ hF hψ Φ hΦ M hM`. Take `⟨Φ', hΦ'm, hΦ'd⟩` from `exists_deriv_schr hF ψ hψ hM hΦ`. Use `⟨Φ', hΦ'm, fun w => ?_⟩` and prove the remaining obligations. Establish `hnorm : ∀ x, ‖ψ x‖ = 1` using `hψ.2.1`. Establish `hM0 : M 0 = 0` using `map_zero M`.

Use `set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω`. Establish `hωc : IsCompact ω` using `isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))`. Take `⟨C, c, hcs, hc0, hcb⟩` from `decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc`. Take `⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩` from `decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton`. Use `set ph : (Fin N → F) → ℂ := fun ξ => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph`.

Establish `e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) = fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (rat ξ + w.1)`. Use function extensionality and compare the values at `t`. Rewrite using `[← thV_schr]`. Both sides reduce to the same expression. Establish `hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (rat ξ + w.1)`.

Rewrite using `[hM0]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Simplify using `[ph, GlobalTheory.WeilM.schr]`. Both sides reduce to the same expression. Rewrite using `[e, hv]`.

Establish `hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1` using `⟨by norm_num, by norm_num⟩`. Use `hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo (fun ξ t _ => (hasDerivAt_schr hF ψ hM hΦ'd (rat ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem` and prove the remaining obligations. Establish `hy : w.1 + (M t).1 ∈ ω` using `⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩`. Use `hcb ξ _ hy` as an intermediate fact. Simplify using `only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]`.

Simplify `this` using `[add_assoc]`. Use `Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_` and prove the remaining obligations. Use `hcb₀ ξ w.1 rfl` as an intermediate fact. Simplify `this` using `[hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm]`.
-/
theorem GlobalTheory.ThetaTransform.hasDerivAt_heisV_line : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N),
      ∀ w, HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  intro F _ _ N _ ψ hF hψ Φ hΦ M hM
  obtain ⟨Φ', hΦ'm, hΦ'd⟩ := exists_deriv_schr hF ψ hψ hM hΦ
  refine ⟨Φ', hΦ'm, fun w => ?_⟩
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr hF ψ hM hΦ'd (rat ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this
