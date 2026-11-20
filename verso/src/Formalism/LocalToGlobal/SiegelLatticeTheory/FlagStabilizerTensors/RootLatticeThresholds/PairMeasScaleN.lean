import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ} {κ τ : ℝ}

/- English proof (translation)
Take `⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩` from `x`. Use `Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)` and prove the remaining obligations. Use `show (fun i j => cj k r κ τ (a * Matrix.of x2) i j) = fun i j => (cj k r κ τ a * Matrix.of (cjT k r κ τ x2)) i j`. Rewrite using `[cj_mul hκ hτ]`. Both sides reduce to the same expression.

Use `show (fun i j => cj k r κ τ (g⁻¹ * a * g * Matrix.of x4) i j) = fun i j => ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * Matrix.of (cjT k r κ τ x4)) i j`. Rewrite using `[cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]`. Both sides reduce to the same expression.
-/
theorem phiP_stabAct (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) (x : PairSp k r) :
    phiP k r κ τ (stabAct g a x) = stabAct (cj k r κ τ g) (cj k r κ τ a) (phiP k r κ τ x) := by
  obtain ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · show (fun i j => cj k r κ τ (a * Matrix.of x2) i j) =
      fun i j => (cj k r κ τ a * Matrix.of (cjT k r κ τ x2)) i j
    rw [cj_mul hκ hτ]
    rfl
  · show (fun i j => cj k r κ τ (g⁻¹ * a * g * Matrix.of x4) i j) =
      fun i j => ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * Matrix.of (cjT k r κ τ x4)) i j
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
    rfl

/- English proof (translation)
Introduce `f hf`. Rewrite using `[pairMeas_trD hκ hτ]`. Establish `exp_product_square_inv : (pairMeas L).map (phiP k r κ τ) = (pairMeas L).map (phiE (k` using `k) (r := r) hκ hτ) := rfl`. Rewrite using `[exp_product_square_inv, lintegral_map_equiv]`. Rewrite using `[h (fun x => f (phiE hκ hτ x)) (hf.comp (phiE hκ hτ).measurable)]`.

Establish `eP : ν.map (phiP k r κ τ) = ν.map (phiE (k` using `k) (r := r) hκ hτ) := rfl`. Rewrite using `[eP, lintegral_map_equiv]`. Use `lintegral_congr (fun x => ?_)` and prove the remaining obligations. Establish `eT : μR.map (cjT k r κ τ) = μR.map (cjE (k` using `k) (r := r) hκ hτ) := rfl`. Rewrite using `[eT, lintegral_map_equiv]`.

Use `lintegral_congr (fun a => ?_)` and prove the remaining obligations. Use `show f (phiP k r κ τ (stabAct g (Matrix.of a) x)) = f (stabAct (cj k r κ τ g) (Matrix.of (cjT k r κ τ a)) (phiP k r κ τ x))`. Rewrite using `[phiP_stabAct hκ hτ]`. Both sides reduce to the same expression.
-/
theorem isOrbQuot_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (h : IsOrbQuot L g μR ν) :
    IsOrbQuot (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') (cj k r κ τ g)
      (μR.map (cjT k r κ τ)) (ν.map (phiP k r κ τ)) := by
  intro f hf
  rw [pairMeas_trD hκ hτ]
  have exp_product_square_inv : (pairMeas L).map (phiP k r κ τ) = (pairMeas L).map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [exp_product_square_inv, lintegral_map_equiv]
  rw [h (fun x => f (phiE hκ hτ x)) (hf.comp (phiE hκ hτ).measurable)]
  have eP : ν.map (phiP k r κ τ) = ν.map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [eP, lintegral_map_equiv]
  refine lintegral_congr (fun x => ?_)
  have eT : μR.map (cjT k r κ τ) = μR.map (cjE (k := k) (r := r) hκ hτ) := rfl
  rw [eT, lintegral_map_equiv]
  refine lintegral_congr (fun a => ?_)
  show f (phiP k r κ τ (stabAct g (Matrix.of a) x)) =
    f (stabAct (cj k r κ τ g) (Matrix.of (cjT k r κ τ a)) (phiP k r κ τ x))
  rw [phiP_stabAct hκ hτ]
  rfl

/- English proof (translation)
Introduce `a ha`. Take `⟨b, rfl⟩ : ∃ b, a = cj k r κ τ b` from `⟨cjI k r κ τ a, (cj_cjI hκ hτ a).symm⟩`. Establish `hb : b ∈ RStab k r g` using `(cj_mem_RStab_iff hκ hτ g b).1 ha`. Establish `e : (cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g = cj k r κ τ (g⁻¹ * b * g)`. Rewrite using `[cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]`.

Use `show psi k r ((τ : ℂ) • L.z) ((κ : ℂ) * L.c) (cj k r κ τ b) = psi k r ((τ : ℂ) • L.z') ((κ : ℂ) * L.c) ((cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g)`. Rewrite using `[e, psi_cj hκ hτ L.hz.1, psi_cj hκ hτ L.hz'.1]`. Conclude with `h b hb`.
-/
theorem isRelStab_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} (h : IsRelStab L g) :
    IsRelStab (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') (cj k r κ τ g) := by
  intro a ha
  obtain ⟨b, rfl⟩ : ∃ b, a = cj k r κ τ b := ⟨cjI k r κ τ a, (cj_cjI hκ hτ a).symm⟩
  have hb : b ∈ RStab k r g := (cj_mem_RStab_iff hκ hτ g b).1 ha
  have e : (cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g = cj k r κ τ (g⁻¹ * b * g) := by
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
  show psi k r ((τ : ℂ) • L.z) ((κ : ℂ) * L.c) (cj k r κ τ b) =
    psi k r ((τ : ℂ) • L.z') ((κ : ℂ) * L.c) ((cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g)
  rw [e, psi_cj hκ hτ L.hz.1, psi_cj hκ hτ L.hz'.1]
  exact h b hb

/- English proof (translation)
Introduce `f hf`. Rewrite using `[hP, lintegral_smul_measure, lintegral_smul_measure, h f hf]`.
-/
theorem isOrbQuot_smul {L L' : LocBessel k r} {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (h : IsOrbQuot L g μR ν) (t : ENNReal) (hP : pairMeas L' = t • pairMeas L) : IsOrbQuot L' g μR (t • ν) := by
  intro f hf
  rw [hP, lintegral_smul_measure, lintegral_smul_measure, h f hf]

/- English proof (translation)
Use `haveI : SFinite L.μN := sFinite_haarLie _ _`. Use `haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩`. Unfold `pairMeas`. Rewrite using `[hW, hW', hN, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]`.
-/
theorem pairMeas_scaleN {L L' : LocBessel k r} (hW : L'.μW = L.μW) (hW' : L'.μW' = L.μW') (t : ENNReal)
    (hN : L'.μN = t • L.μN) : pairMeas L' = (t * t) • pairMeas L := by
  haveI : SFinite L.μN := sFinite_haarLie _ _
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  unfold pairMeas
  rw [hW, hW', hN, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, smul_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
