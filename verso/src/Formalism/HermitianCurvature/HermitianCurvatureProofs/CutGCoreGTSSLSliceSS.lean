import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocalCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

/- English proof (translation)
Introduce `Φ Φ' c c' _ _ _ ζ _`. Simplify using the standard rewrite rules.
-/
theorem sliceLoc_zero : SliceLoc P Bs 0 := by
  intro Φ Φ' c c' _ _ _ ζ _
  simp

/- English proof (translation)
Introduce `Φ Φ' c c' hc hc' h ζ hζ`. Simplify using `only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]`. Rewrite using `[hT Φ Φ' c c' hc hc' h ζ hζ, hS Φ Φ' c c' hc hc' h ζ hζ]`.
-/
theorem sliceLoc_add {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T + S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ, hS Φ Φ' c c' hc hc' h ζ hζ]

/- English proof (translation)
Introduce `Φ Φ' c c' hc hc' h ζ hζ`. Simplify using `only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]`. Rewrite using `[hT Φ Φ' c c' hc hc' h ζ hζ]`.
-/
theorem sliceLoc_smul {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (a : ℂ) (hT : SliceLoc P Bs T) :
    SliceLoc P Bs (a • T) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ]

/- English proof (translation)
Introduce `Φ Φ' c c' hc hc' h ζ hζ`. Conclude with `hT (S Φ) (S Φ') c c' hc hc' (hS Φ Φ' c c' hc hc' h) ζ hζ`.
-/
theorem sliceLoc_mul {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T * S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  exact hT (S Φ) (S Φ') c c' hc hc' (hS Φ Φ' c c' hc hc' h) ζ hζ

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty]`. Conclude with `sliceLoc_zero`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.sum_insert hi]`. Conclude with `sliceLoc_add (hT i (Finset.mem_insert_self _ _)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))`.
-/
theorem sliceLoc_sum {ι : Type} (s : Finset ι) (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (hT : ∀ i ∈ s, SliceLoc P Bs (T i)) : SliceLoc P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact sliceLoc_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact sliceLoc_add (hT i (Finset.mem_insert_self _ _)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Establish `hTU : T = a⁻¹ • U` using `by rw [hU, smul_smul, inv_mul_cancel₀ ha, one_smul]`. Rewrite using `[hTU]`. Conclude with `sliceLoc_smul _ h`.
-/
theorem sliceLoc_of_smul {T U : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {a : ℂ} (ha : a ≠ 0)
    (hU : U = a • T) (h : SliceLoc P Bs U) : SliceLoc P Bs T := by
  have hTU : T = a⁻¹ • U := by rw [hU, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hTU]
  exact sliceLoc_smul _ h

end closure

open Formalism.FourierDecayAlt.P.NFx4.NO in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hH hT l hl`. Establish `hP` using `hH.1.1`. Establish `hRel` using `hH.2.2.2.2.2.1`. Establish `hQQ` using `hH.2.2.2.2.2.2`. Take `⟨Qr, hQ⟩` from `gauge_kappa_pointwise_holds Wp Wq P Bs X d hH`.

Establish `hK : ∀ f : M.Ty P → ℂ, SliceLoc P Bs (d.κ f).1`. Introduce `f Φ Φ' c c' hc hc' h ζ hζ`. Establish `e1` using `hQ.2.2.2 f Φ ⟨(c, ζ), ⟨hc, hζ⟩⟩`. Establish `e2` using `hQ.2.2.2 f Φ' ⟨(c', ζ), ⟨hc', hζ⟩⟩`. Simplify using `only at e1 e2`.

Rewrite using `[e1, e2, h ζ hζ]`. Establish `hPj : ∀ ρ, SliceLoc P Bs (Pj d ρ).1` using `fun ρ => hK _`. Establish `e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1` using `fun Y => by rw [← hQQ Y]; rfl`. Establish `e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1` using `fun Y => by rw [← hQQ Y]; rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hdec : (d.SS l).1 = ∑ a, ∑ b, (Pj d a * d.SS l * Pj d b).1`. Establish `h` using `congrArg (fstA _) (decomp d (d.SS l))`. Simplify using `only [map_sum] at h`. Conclude with `h`. Rewrite using `[hdec]`.

Use `sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hUp : M.Up P l b a`. Use `set Y : ℂ := -(M.rho P b l : ℂ) with hY`. Establish `hc0 : M.xEx P {l} b Y ≠ 0`. Unfold `M.xEx`.

Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_sdiff.1 hi`. Establish `hne : M.rho P b i ≠ M.rho P b l` using `rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `: ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ)` using `by rw [hY] at h0; linear_combination h0`. Conclude with `this` after adjusting the coercions. Establish `hE : (Pj d a).1 * X.t Y 1 0 * (Pj d b).1 = M.xEx P {l} b Y • (Pj d a * d.SS l * Pj d b).1`. Establish `h` using `congrArg (fstA _) (B1 hRel hl hUp Y)`. Rewrite `h` using `[map_mul, map_mul, map_smul]`.

Rewrite using `[e10]`. Conclude with `h`. Conclude with `sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 1 0)) (hPj b))`. Rewrite using `[block_zero hRel hUp]`. Conclude with `sliceLoc_zero`.

Establish `hdec : (star (d.SS l)).1 = ∑ a, ∑ b, (Pj d a * star (d.SS l) * Pj d b).1`. Establish `h` using `congrArg (fstA _) (decomp d (star (d.SS l)))`. Simplify using `only [map_sum] at h`. Conclude with `h`. Rewrite using `[hdec]`.

Use `sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hUp : M.Up P l a b`. Use `set Y : ℂ := -(M.rho P b l : ℂ) with hY`. Establish `hc0 : M.xEx P {l} a Y ≠ 0`. Unfold `M.xEx`.

Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_sdiff.1 hi`. Establish `hil : i ≠ l` using `fun e => hi'.2 (by simp [e])`. Establish `hup` using `Formalism.FourierDecayAlt.P.Mx3.rhoUp P l a b hUp i hi'.1`. Rewrite `hup` using `[if_neg hil, add_zero]`.

Establish `hne : M.rho P b i ≠ M.rho P b l` using `rho_ne P hP b hi'.1 hl hil`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `: ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ)`. Rewrite `h0` using `[hY]`.

Rewrite using `[hup]`. Take the linear combination `h0`. Conclude with `this` after adjusting the coercions. Establish `hE : (Pj d a).1 * X.t Y 0 1 * (Pj d b).1 = M.xEx P {l} a Y • (Pj d a * star (d.SS l) * Pj d b).1`. Establish `h` using `congrArg (fstA _) (B4 hRel hl hUp Y)`.

Rewrite `h` using `[map_mul, map_mul, map_smul]`. Rewrite using `[e01]`. Conclude with `h`. Conclude with `sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 0 1)) (hPj b))`. Rewrite using `[star_block_zero hRel hUp]`.

Conclude with `sliceLoc_zero`.
-/
theorem second_shift_slice_operator : GTSSLSliceSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT l hl
  have hP := hH.1.1
  have hRel := hH.2.2.2.2.2.1
  have hQQ := hH.2.2.2.2.2.2
  obtain ⟨Qr, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  have hK : ∀ f : M.Ty P → ℂ, SliceLoc P Bs (d.κ f).1 := by
    intro f Φ Φ' c c' hc hc' h ζ hζ
    have e1 := hQ.2.2.2 f Φ ⟨(c, ζ), ⟨hc, hζ⟩⟩
    have e2 := hQ.2.2.2 f Φ' ⟨(c', ζ), ⟨hc', hζ⟩⟩
    simp only at e1 e2
    rw [e1, e2, h ζ hζ]
  have hPj : ∀ ρ, SliceLoc P Bs (Pj d ρ).1 := fun ρ => hK _
  have e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1 := fun Y => by rw [← hQQ Y]; rfl
  have e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1 := fun Y => by rw [← hQQ Y]; rfl
  refine ⟨?_, ?_⟩
  · have hdec : (d.SS l).1 = ∑ a, ∑ b, (Pj d a * d.SS l * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (d.SS l))
      simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l b a
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} b Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hne : M.rho P b i ≠ M.rho P b l :=
          rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by rw [hY] at h0; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 1 0 * (Pj d b).1 = M.xEx P {l} b Y • (Pj d a * d.SS l * Pj d b).1 := by
        have h := congrArg (fstA _) (B1 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e10]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 1 0)) (hPj b))
    · rw [block_zero hRel hUp]
      exact sliceLoc_zero
  · have hdec : (star (d.SS l)).1 = ∑ a, ∑ b, (Pj d a * star (d.SS l) * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (star (d.SS l)))
      simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l a b
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} a Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hil : i ≠ l := fun e => hi'.2 (by simp [e])
        have hup := Formalism.FourierDecayAlt.P.Mx3.rhoUp P l a b hUp i hi'.1
        rw [if_neg hil, add_zero] at hup
        have hne : M.rho P b i ≠ M.rho P b l := rho_ne P hP b hi'.1 hl hil
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by
          rw [hY] at h0; rw [hup]; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 0 1 * (Pj d b).1 = M.xEx P {l} a Y • (Pj d a * star (d.SS l) * Pj d b).1 := by
        have h := congrArg (fstA _) (B4 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e01]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 0 1)) (hPj b))
    · rw [star_block_zero hRel hUp]
      exact sliceLoc_zero

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
