import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Establish `hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ))) (MA.Qset P.r P.TT)` using `MA.wirt_smooth (fnZ P u).2 w`. Set `ι : ℂ → MA.E P.r` to `fun ζ => ((fun _ => (1 : ℂ)), ζ)`. Establish `hι : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ι` using `contDiff_const.prodMk contDiff_id`. Establish `hmap : Set.MapsTo ι (Ann P) (MA.Qset P.r P.TT)` using `fun ζ hζ => ⟨fun _ => one_ne_zero, hζ⟩`. Use `(hs.comp hι.contDiffOn hmap).congr fun ζ hζ => ?_` and prove the remaining obligations.

Conclude with `(hF ⟨ι ζ, hmap hζ⟩).symm`.
-/
private theorem contDiffOn_ann_of_wirt_fnZ_eq (P : M.Par) {u : ℂ → ℂ} (w : M.Var P.r) (F : ℂ → ℂ)
    (hF : ∀ q : MA.Qp P.r P.TT,
      MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = F q.1.2) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ann P) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ))) (MA.Qset P.r P.TT) :=
    MA.wirt_smooth (fnZ P u).2 w
  let ι : ℂ → MA.E P.r := fun ζ => ((fun _ => (1 : ℂ)), ζ)
  have hι : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ι := contDiff_const.prodMk contDiff_id
  have hmap : Set.MapsTo ι (Ann P) (MA.Qset P.r P.TT) := fun ζ hζ => ⟨fun _ => one_ne_zero, hζ⟩
  refine (hs.comp hι.contDiffOn hmap).congr fun ζ hζ => ?_
  exact (hF ⟨ι ζ, hmap hζ⟩).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨contDiffOn_ann_of_wirt_fnZ_eq P M.vz _ fun q => wirtinger_derivative_fibre_function P hu q, contDiffOn_ann_of_wirt_fnZ_eq P M.vzb _ fun q => wirt_fnZ_zb P hu q⟩`.
-/
theorem dZ_smooth (P : M.Par) {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (Ann P)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ u) (Ann P) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb u) (Ann P) :=
  ⟨contDiffOn_ann_of_wirt_fnZ_eq P M.vz _ fun q => wirtinger_derivative_fibre_function P hu q, contDiffOn_ann_of_wirt_fnZ_eq P M.vzb _ fun q => wirt_fnZ_zb P hu q⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hSm : SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ)` using `fun ρ => ⟨(hAB ρ).1.add ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).1), (hAB ρ).2.sub ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).2)⟩`. Use `⟨hSm, fun Φ ρ => ?_⟩` and prove the remaining obligations. Establish `hc` using `conj_smooth (hu ρ).1`. Rewrite using `[trR_phase P Bs e u hu, trR_phase P Bs e u hu, trR_phase P Bs e u hu, (hC Φ ρ).1, (hC Φ ρ).2]`. Use `set g := trR P Bs e Φ ρ`.

Prove the components needed by the constructor for the conclusion. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Establish `hq : q.1.2 ∈ Ann P` using `q.2.2`. Establish `e1 : ((dzQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = NF.dZ (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q + star (u ρ q.1.2) * MA.wirt M.vz (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1`.

Rewrite using `[dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hc, fnZ_val P hc]`. Simplify using `only [MulMemClass.coe_mul, AddMemClass.coe_add, Pi.mul_apply, Pi.add_apply]`. Rewrite using `[e1, dzQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).1, fnZ_val P (hSm ρ).1, (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).1]`. Expand and normalize the polynomial expressions, which then agree. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `q`. Establish `hq : q.1.2 ∈ Ann P` using `q.2.2`. Establish `e1 : ((dzbQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = NF.dZb (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q + star (u ρ q.1.2) * MA.wirt M.vzb (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1`. Rewrite using `[dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hc, fnZ_val P hc]`. Simplify using `only [MulMemClass.coe_mul, AddMemClass.coe_add, NegMemClass.coe_neg, Pi.mul_apply, Pi.add_apply, Pi.neg_apply]`.

Rewrite using `[e1, dzbQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).2, fnZ_val P (hSm ρ).2, (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem connF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
  have hSm : SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := fun ρ =>
    ⟨(hAB ρ).1.add ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).1),
      (hAB ρ).2.sub ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).2)⟩
  refine ⟨hSm, fun Φ ρ => ?_⟩
  have hc := conj_smooth (hu ρ).1
  rw [trR_phase P Bs e u hu, trR_phase P Bs e u hu, trR_phase P Bs e u hu, (hC Φ ρ).1, (hC Φ ρ).2]
  set g := trR P Bs e Φ ρ
  constructor
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZ (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vz (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, Pi.mul_apply, Pi.add_apply]
    rw [e1, dzQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).1, fnZ_val P (hSm ρ).1,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).1]
    ring
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzbQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZb (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vzb (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, NegMemClass.coe_neg, Pi.mul_apply,
      Pi.add_apply, Pi.neg_apply]
    rw [e1, dzbQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).2, fnZ_val P (hSm ρ).2,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).2]
    ring

end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
