import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConjDiEqSelf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[cj_apply]`. Distinguish the cases in `h0 : h i j = 0`. Rewrite using `[h0, mul_zero]`. Establish `e` using `fix_gen (fun i => ((tV k r κ τ i : ℝ) : ℂ)) 1 (fun i h1 h2 => by simp [tV_wb i h1 h2]) hh.1 hh.2.1 i j h0`.

Establish `e' : tV k r κ τ i = tV k r κ τ j` using `by exact_mod_cast e`. Rewrite using `[e', inv_mul_cancel₀ (tV_pos hκ hτ j).ne']`. Simplify using the standard rewrite rules.
-/
theorem cj_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) :
    cj k r κ τ h = h := by
  ext i j
  rw [cj_apply]
  by_cases h0 : h i j = 0
  · rw [h0, mul_zero]
  · have e := fix_gen (fun i => ((tV k r κ τ i : ℝ) : ℂ)) 1 (fun i h1 h2 => by simp [tV_wb i h1 h2]) hh.1 hh.2.1 i j h0
    have e' : tV k r κ τ i = tV k r κ τ j := by exact_mod_cast e
    rw [e', inv_mul_cancel₀ (tV_pos hκ hτ j).ne']
    simp

/- English proof (translation)
Establish `hae : cjT k r κ τ =ᵐ[μ] id`. Rewrite using `[Filter.EventuallyEq, ae_iff]`. Use `measure_mono_null (fun x hx => ?_) h.2.2.1` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq] at hx ⊢`. Introduce `hU`.

Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Use `show cj k r κ τ (Matrix.of x) i j = x i j`. Rewrite using `[cj_UW hκ hτ hU]`. Both sides reduce to the same expression.

Rewrite using `[Measure.map_congr hae, Measure.map_id]`.
-/
theorem map_cjT_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)}
    (h : IsHaarOn (UWset k r z) μ) : μ.map (cjT k r κ τ) = μ := by
  have hae : cjT k r κ τ =ᵐ[μ] id := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) h.2.2.1
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro hU
    apply hx
    funext i j
    show cj k r κ τ (Matrix.of x) i j = x i j
    rw [cj_UW hκ hτ hU]; rfl
  rw [Measure.map_congr hae, Measure.map_id]

/- English proof (translation)
Take `⟨μ0, h0⟩` from `Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT`. Establish `hC` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z`. Establish `hK` using `Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT`. Establish `fin : ∀ (m : Measure (Mt k r)), m Set.univ = 1 → ∀ K : Set (Mt k r), IsCompact K → m K < ⊤` using `fun m hm K _ => (measure_mono (Set.subset_univ K)).trans_lt (by rw [hm]; exact ENNReal.one_lt_top)`. Take `⟨c, hc⟩` from `Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 μ hC h0 hμ.2.2.1 hμ.2.2.2 (fin μ hμ1)`.

Take `⟨d, hd⟩` from `Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 ν hC h0 hν.2.2.1 hν.2.2.2 (fin ν hν1)`. Establish `hfin : μ0 Set.univ ≠ ⊤`. Establish `hle` using `measure_univ_le_add_compl (μ := μ0) (UWset k r z : Set (Mt k r))`. Establish `hc0 : μ0 (UWset k r z : Set (Mt k r))ᶜ < ⊤` using `(le_of_eq h0.conc).trans_lt ENNReal.zero_lt_top`. Conclude with `(lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨h0.finite_compact _ hK, hc0⟩)).ne`.

Establish `hne : μ0 Set.univ ≠ 0`. Introduce `h`. Apply `h0.ne_zero` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero]`. Conclude with `h`.

Establish `e1 : (c : ENNReal) * μ0 Set.univ = 1` using `by rw [← hμ1, hc]; rfl`. Establish `e2 : (d : ENNReal) * μ0 Set.univ = 1` using `by rw [← hν1, hd]; rfl`. Establish `hcd : (c : ENNReal) = d`. Use `e1.trans e2.symm` as an intermediate fact. Conclude with `(ENNReal.mul_left_inj hne hfin).mp this`.

Rewrite using `[hc, hd, ENNReal.coe_injective hcd]`.
-/
theorem haarProb_unique {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn (UWset k r z) μ) (hμ1 : μ Set.univ = 1) (hν : IsHaarOn (UWset k r z) ν) (hν1 : ν Set.univ = 1) :
    μ = ν := by
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  have hC := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hK := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT
  have fin : ∀ (m : Measure (Mt k r)), m Set.univ = 1 → ∀ K : Set (Mt k r), IsCompact K → m K < ⊤ :=
    fun m hm K _ => (measure_mono (Set.subset_univ K)).trans_lt (by rw [hm]; exact ENNReal.one_lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 μ hC h0 hμ.2.2.1 hμ.2.2.2 (fin μ hμ1)
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 ν hC h0 hν.2.2.1 hν.2.2.2 (fin ν hν1)
  have hfin : μ0 Set.univ ≠ ⊤ := by
    have hle := measure_univ_le_add_compl (μ := μ0) (UWset k r z : Set (Mt k r))
    have hc0 : μ0 (UWset k r z : Set (Mt k r))ᶜ < ⊤ := (le_of_eq h0.conc).trans_lt ENNReal.zero_lt_top
    exact (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨h0.finite_compact _ hK, hc0⟩)).ne
  have hne : μ0 Set.univ ≠ 0 := by
    intro h; apply h0.ne_zero; rw [← Measure.measure_univ_eq_zero]; exact h
  have e1 : (c : ENNReal) * μ0 Set.univ = 1 := by rw [← hμ1, hc]; rfl
  have e2 : (d : ENNReal) * μ0 Set.univ = 1 := by rw [← hν1, hd]; rfl
  have hcd : (c : ENNReal) = d := by
    have := e1.trans e2.symm
    exact (ENNReal.mul_left_inj hne hfin).mp this
  rw [hc, hd, ENNReal.coe_injective hcd]

section Choice

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

/- English proof (translation)
Rewrite using `[map_cjT_UW (inv_pos.mpr (kaB_pos D)) one_pos (C.muW_haar u τ)]`. Use `show (μW_exists X C u (vOf X τ)).choose = _`. Take `⟨h1, h2⟩` from `(μW_exists X C u (vOf X τ)).choose_spec`. Generalize the expression as in `(μW_exists X C u (vOf X τ)).choose = m at h1 h2 ⊢`. Establish `hS : UWset D.R.k D.R.rS (zc X C u (vOf X τ)) = UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)`.

Rewrite using `[zc_vOf_eq_zB_of_inWb C u u τ hz, UWset_smul one_pos]`. Rewrite `h1` using `[hS]`. Conclude with `haarProb_unique hz hT h1 h2 (C.muW_haar u τ) (C.muW_one u τ)`.
-/
theorem muWc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ))
    (hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1) := by
  rw [map_cjT_UW (inv_pos.mpr (kaB_pos D)) one_pos (C.muW_haar u τ)]
  show (μW_exists X C u (vOf X τ)).choose = _
  obtain ⟨h1, h2⟩ := (μW_exists X C u (vOf X τ)).choose_spec
  generalize (μW_exists X C u (vOf X τ)).choose = m at h1 h2 ⊢
  have hS : UWset D.R.k D.R.rS (zc X C u (vOf X τ)) = UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [zc_vOf_eq_zB_of_inWb C u u τ hz, UWset_smul one_pos]
  rw [hS] at h1
  exact haarProb_unique hz hT h1 h2 (C.muW_haar u τ) (C.muW_one u τ)

end Choice

end Formalism.L2.SG.Pf.Carrier.CarPinTor
