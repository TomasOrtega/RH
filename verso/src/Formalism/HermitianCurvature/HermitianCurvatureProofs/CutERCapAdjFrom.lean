import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERHaarPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialAdjointOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section smooth

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hd : HasFDerivAt ψ (fderiv ℝ ψ (Formalism.FourierDecayAlt.P.B4.cv false X 0 g)) (Formalism.FourierDecayAlt.P.B4.cv false X 0 g)` using `((hψ.differentiable (by simp)) _).hasFDerivAt`. Establish `h` using `hd.comp_hasDerivAt (0 : ℝ) (Formalism.FourierDecayAlt.P.B4.cv_hasDerivAt false X g)`. Rewrite `h` using `[Formalism.FourierDecayAlt.P.B4.cv_zero]`. Conclude with `h.deriv`.
-/
theorem rdV_global {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X ψ = fun g => fderiv ℝ ψ g (g * X) := by
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ (Formalism.FourierDecayAlt.P.B4.cv false X 0 g)) (Formalism.FourierDecayAlt.P.B4.cv false X 0 g) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (Formalism.FourierDecayAlt.P.B4.cv_hasDerivAt false X g)
  rw [Formalism.FourierDecayAlt.P.B4.cv_zero] at h
  exact h.deriv

/- English proof (translation)
Rewrite using `[rdV_global hψ X]`. Conclude with `(hψ.fderiv_right (m := ∞) (by simp)).clm_apply (Formalism.FourierDecayAlt.P.B4.mulR X).contDiff`.
-/
theorem rdV_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) : ContDiff ℝ ∞ (RdV X ψ) := by
  rw [rdV_global hψ X]
  exact (hψ.fderiv_right (m := ∞) (by simp)).clm_apply (Formalism.FourierDecayAlt.P.B4.mulR X).contDiff

/- English proof (translation)
The claim follows from `| [] => hψ | X :: w => rdV_contDiff (rw_contDiff hψ w) X`.
-/
theorem rw_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) : ∀ w : List (B.Mat k r), ContDiff ℝ ∞ (B.Rw w ψ)
  | [] => hψ
  | X :: w => rdV_contDiff (rw_contDiff hψ w) X

/- English proof (translation)
The claim follows from `| [], _ => by simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : B.Mat k r => (0 : E))) | i :: L, h => by simp only [List.map_cons, List.sum_cons] exact (h i (by simp)).add (contDiff_listSum f L fun j hj => h j (by simp [hj]))`.
-/
theorem contDiff_listSum {ι : Type*} (f : ι → B.Mat k r → E) :
    ∀ L : List ι, (∀ i ∈ L, ContDiff ℝ ∞ (f i)) → ContDiff ℝ ∞ (fun g => (L.map fun i => f i g).sum)
  | [], _ => by simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : B.Mat k r => (0 : E)))
  | i :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (contDiff_listSum f L fun j hj => h j (by simp [hj]))

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, ψ, isOpen_univ, trivial, (hψ.of_le (by exact_mod_cast (le_top : m ≤ ⊤))).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem ckOn_of_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (m : ℕ∞) (UU : Set (B.Mat k r)) :
    B.CkOn m UU ψ :=
  fun _ _ => ⟨Set.univ, ψ, isOpen_univ, trivial,
    (hψ.of_le (by exact_mod_cast (le_top : m ≤ ⊤))).contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `g hg` and use `hf g (h hg)`.
-/
theorem ckOn_sub_set {m : ℕ∞} {UU UU' : Set (B.Mat k r)} (h : UU' ⊆ UU) {f : B.Mat k r → E}
    (hf : B.CkOn m UU f) : B.CkOn m UU' f :=
  fun g hg => hf g (h hg)

end smooth

section pointwise

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `B.opAdj`. Use `contDiff_listSum (fun (T : B.DTerm k r Wp Wq) g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (ψ x)) g) _ fun T hT => ?_` and prove the remaining obligations. Take `⟨c, w, rfl⟩` from `mem_capOp s (capLw k r Y) hT`. Use `(rw_contDiff ?_ _).const_smul _` and prove the remaining obligations. Use `show ContDiff ℝ ∞ (fun x => (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (ψ x))`.

Simplify using `using hψ.const_smul (conj c)`.
-/
theorem opAdj_capTh_contDiff (s Y : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (B.opAdj (capTh k r Wp Wq s Y) ψ) := by
  unfold B.opAdj
  refine contDiff_listSum (fun (T : B.DTerm k r Wp Wq) g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse
    (fun x => T.coefAdj x (ψ x)) g) _ fun T hT => ?_
  obtain ⟨c, w, rfl⟩ := mem_capOp s (capLw k r Y) hT
  refine (rw_contDiff ?_ _).const_smul _
  show ContDiff ℝ ∞ (fun x => (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (ψ x))
  simpa using hψ.const_smul (conj c)

/- English proof (translation)
Establish `h` using `(Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_smul c A`. Rewrite `h` using `[Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply]`. Conclude with `h`.
-/
theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  have h := (Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_smul c A
  rw [Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply] at h
  exact h

/- English proof (translation)
Establish `h` using `(Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_sub A C`. Rewrite `h` using `[Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply]`. Conclude with `h`.
-/
theorem hsVec_sub (A C : Wq →L[ℂ] Wp) : B.hsVec (A - C) = B.hsVec A - B.hsVec C := by
  have h := (Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_sub A C
  rw [Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply] at h
  exact h

/- English proof (translation)
Unfold `B.hsInner`. Rewrite using `[hsVec_sub, inner_sub_left]`.
-/
theorem hs_sub_right (A C D : Wq →L[ℂ] Wp) : B.hsInner A (C - D) = B.hsInner A C - B.hsInner A D := by
  unfold B.hsInner
  rw [hsVec_sub, inner_sub_left]

/- English proof (translation)
Unfold `B.hsInner`. Rewrite using `[hsVec_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules.
-/
theorem hsInner_smul_self (c : ℂ) (A : Wq →L[ℂ] Wp) :
    B.hsInner (c • A) A = c * ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [hsVec_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩`. Take `⟨L, hL, hCV⟩` from `Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)`. Use `set Θ := capTh k r Wp Wq s Y`. Use `set Ht : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => B.opAdj Θ ψ g - conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum with hHt`. Establish `hCVg : ∀ g ∈ B.GV k r, Q.CV k r (conj Y) ψ g = (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum` using `fun g hg => hCV _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg`.

Establish `hS : ContDiff ℝ ∞ (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum)` using `contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 ψ g) L fun cw _ => (rw_contDiff hψ _).const_smul _`. Establish `hA : ContDiff ℝ ∞ (B.opAdj Θ ψ)` using `opAdj_capTh_contDiff s Y hψ`. Establish `hHs : ContDiff ℝ ∞ Ht` using `hA.sub (hS.const_smul _)`. Assume the negation of the conclusion as `hne`. Establish `hH0 : Ht g₀ ≠ 0`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use `sub_eq_zero.1 h0` as an intermediate fact. Rewrite using `[hCVg g₀ hg₀]`. Conclude with `this`.

Take `⟨β⟩ : Nonempty (ContDiffBump g₀)` from `⟨⟨1, 2, one_pos, one_lt_two⟩⟩`. Establish `hβs : ContDiff ℝ ∞ (fun g => ((β g : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp β.contDiff`. Establish `hβc : HasCompactSupport (fun g => ((β g : ℝ) : ℂ))` using `β.hasCompactSupport.comp_left Complex.ofReal_zero`. Use `set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • Ht g with hφ`. Establish `hφs : ContDiff ℝ ∞ φ` using `hβs.smul hHs`.

Establish `hφc : HasCompactSupport φ` using `hβc.smul_right`. Establish `hInt` using `hI k r Wp Wq s Y μ hμ φ ψ hφs hφc hψ hψc`. Establish `hcont1 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x)))` using `Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk hA.continuous)`. Establish `hcs1 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x)))` using `hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)`. Establish `i1` using `hcont1.integrable_of_hasCompactSupport (μ := μ) hcs1`.

Establish `hcont2 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum))` using `Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk (hS.const_smul _).continuous)`. Establish `hcs2 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum))` using `hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)`. Establish `i2` using `hcont2.integrable_of_hasCompactSupport (μ := μ) hcs2`. Establish `hae2 : (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x))) =ᵐ[μ] fun x => B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)` using `by filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx`. Rewrite using `[hCVg _ hx]`.

Rewrite `hInt` using `[integral_congr_ae hae2]`. Use `set h : Mt k r → ℝ := fun x => β (Matrix.of x) * ‖B.hsVec (Ht (Matrix.of x))‖ ^ 2 with hh`. Establish `hpt : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x)) - B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) = ((h x : ℝ) : ℂ)`. Introduce `x`. Rewrite using `[← hs_sub_right]`.

Use `show B.hsInner (((β (Matrix.of x) : ℝ) : ℂ) • Ht (Matrix.of x)) (Ht (Matrix.of x)) = _`. Rewrite using `[hsInner_smul_self]`. Simplify using `[hh]`. Establish `hzero : ∫ x, ((h x : ℝ) : ℂ) ∂μ = 0`. Rewrite using `[← integral_congr_ae (Eventually.of_forall hpt), integral_sub i1 i2, hInt, sub_self]`.

Establish `hnn : 0 ≤ h` using `fun x => mul_nonneg (β.nonneg) (sq_nonneg _)`. Establish `hcv : Continuous (fun x : B.Mat k r => B.hsVec (Ht x))` using `((Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).continuous.comp hHs.continuous).congr (fun x => Formalism.FourierDecayAlt.P.B5.hsL_apply _)`. Establish `hcont : Continuous h` using `β.continuous.mul ((continuous_norm.comp hcv).pow 2)`. Establish `hint : Integrable h μ`. Use `(i1.sub i2).congr (Eventually.of_forall hpt)` as an intermediate fact.

Conclude with `this.re.congr (Eventually.of_forall fun x => by simp)`. Establish `hzero' : ∫ x, h x ∂μ = 0`. Use `hzero` as an intermediate fact. Rewrite `this` using `[integral_complex_ofReal]`. Conclude with `this` after adjusting the coercions.

Establish `hae : h =ᵐ[μ] 0` using `(integral_eq_zero_iff_of_nonneg hnn hint).1 hzero'`. Establish `hO : IsOpen {x : Mt k r | 0 < h x}` using `isOpen_lt continuous_const hcont`. Establish `hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < h x}` using `by show 0 < β g₀ * ‖B.hsVec (Ht g₀)‖ ^ 2`. Establish `h1 : β g₀ = 1` using `β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)`. Rewrite using `[h1, one_mul]`.

Establish `: B.hsVec (Ht g₀) ≠ 0` using `fun h0 => hH0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by`. Rewrite using `[← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))`. Check the signs of the components of the expression. Establish `hpos` using `haar_open_pos hμ hO (g₀ := g₀) hg₀ hg₀O`. Apply `hpos` to reduce the goal to its premises.

Establish `: {x : Mt k r | 0 < h x} ⊆ {x | h x ≠ 0}` using `fun x hx => (ne_of_gt hx)`. Conclude with `measure_mono_null this (by simpa [Filter.EventuallyEq, ae_iff] using hae)`.
-/
theorem pt_of_int (hI : CapAdjInt) {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) (s Y : ℂ)
    {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {g₀ : B.Mat k r}
    (hg₀ : g₀ ∈ B.GV k r) :
    B.opAdj (capTh k r Wp Wq s Y) ψ g₀ = conj s • Q.CV k r (conj Y) ψ g₀ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set Θ := capTh k r Wp Wq s Y
  set Ht : B.Mat k r → (Wq →L[ℂ] Wp) := fun g =>
    B.opAdj Θ ψ g - conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum with hHt
  have hCVg : ∀ g ∈ B.GV k r, Q.CV k r (conj Y) ψ g = (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum :=
    fun g hg => hCV _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg
  have hS : ContDiff ℝ ∞ (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) :=
    contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 ψ g) L fun cw _ => (rw_contDiff hψ _).const_smul _
  have hA : ContDiff ℝ ∞ (B.opAdj Θ ψ) := opAdj_capTh_contDiff s Y hψ
  have hHs : ContDiff ℝ ∞ Ht := hA.sub (hS.const_smul _)
  by_contra hne
  have hH0 : Ht g₀ ≠ 0 := by
    intro h0
    apply hne
    have := sub_eq_zero.1 h0
    rw [hCVg g₀ hg₀]
    exact this

  obtain ⟨β⟩ : Nonempty (ContDiffBump g₀) := ⟨⟨1, 2, one_pos, one_lt_two⟩⟩
  have hβs : ContDiff ℝ ∞ (fun g => ((β g : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hβc : HasCompactSupport (fun g => ((β g : ℝ) : ℂ)) :=
    β.hasCompactSupport.comp_left Complex.ofReal_zero
  set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • Ht g with hφ
  have hφs : ContDiff ℝ ∞ φ := hβs.smul hHs
  have hφc : HasCompactSupport φ := hβc.smul_right
  have hInt := hI k r Wp Wq s Y μ hμ φ ψ hφs hφc hψ hψc

  have hcont1 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x))) :=
    Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk hA.continuous)
  have hcs1 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x))) :=
    hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)
  have i1 := hcont1.integrable_of_hasCompactSupport (μ := μ) hcs1
  have hcont2 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x))
      (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)) :=
    Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk (hS.const_smul _).continuous)
  have hcs2 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x))
      (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)) :=
    hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)
  have i2 := hcont2.integrable_of_hasCompactSupport (μ := μ) hcs2
  have hae2 : (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x))) =ᵐ[μ]
      fun x => B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCVg _ hx]
  rw [integral_congr_ae hae2] at hInt

  set h : Mt k r → ℝ := fun x => β (Matrix.of x) * ‖B.hsVec (Ht (Matrix.of x))‖ ^ 2 with hh
  have hpt : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x)) -
      B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) =
      ((h x : ℝ) : ℂ) := by
    intro x
    rw [← hs_sub_right]
    show B.hsInner (((β (Matrix.of x) : ℝ) : ℂ) • Ht (Matrix.of x)) (Ht (Matrix.of x)) = _
    rw [hsInner_smul_self]
    simp [hh]
  have hzero : ∫ x, ((h x : ℝ) : ℂ) ∂μ = 0 := by
    rw [← integral_congr_ae (Eventually.of_forall hpt), integral_sub i1 i2, hInt, sub_self]
  have hnn : 0 ≤ h := fun x => mul_nonneg (β.nonneg) (sq_nonneg _)
  have hcv : Continuous (fun x : B.Mat k r => B.hsVec (Ht x)) :=
    ((Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).continuous.comp hHs.continuous).congr
      (fun x => Formalism.FourierDecayAlt.P.B5.hsL_apply _)
  have hcont : Continuous h := β.continuous.mul ((continuous_norm.comp hcv).pow 2)
  have hint : Integrable h μ := by
    have := (i1.sub i2).congr (Eventually.of_forall hpt)
    exact this.re.congr (Eventually.of_forall fun x => by simp)
  have hzero' : ∫ x, h x ∂μ = 0 := by
    have := hzero
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  have hae : h =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero'
  have hO : IsOpen {x : Mt k r | 0 < h x} := isOpen_lt continuous_const hcont
  have hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < h x} := by
    show 0 < β g₀ * ‖B.hsVec (Ht g₀)‖ ^ 2
    have h1 : β g₀ = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
    rw [h1, one_mul]
    have : B.hsVec (Ht g₀) ≠ 0 := fun h0 => hH0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by
      rw [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))
    positivity
  have hpos := haar_open_pos hμ hO (g₀ := g₀) hg₀ hg₀O
  apply hpos
  have : {x : Mt k r | 0 < h x} ⊆ {x | h x ≠ 0} := fun x hx => (ne_of_gt hx)
  exact measure_mono_null this (by simpa [Filter.EventuallyEq, ae_iff] using hae)

end pointwise

/- English proof (translation)
Introduce `hI k r Wp Wq _ _ _ _ _ _ s Y F hF g₀ hg₀`. Take `⟨μ, hμ⟩` from `Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r`. Take `⟨U, F', hU, hg₀U, hc, he⟩` from `hF g₀ hg₀`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hU g₀ hg₀U`. Take `⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2` from `⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩`.

Use `set ψ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • F' g with hψ`. Establish `hψs : ContDiff ℝ ∞ ψ`. Use `contDiff_iff_contDiffAt.2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Conclude with `((Complex.ofRealCLM.contDiff.comp β.contDiff).contDiffAt).smul ((hc.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_rfl))`.

Establish `hx2 : ε ≤ dist x g₀`. Assume the negation of the conclusion as `hlt`. Conclude with `hx (hball (Metric.mem_ball.2 (lt_of_not_ge hlt)))`. Establish `hO : IsOpen {y : B.Mat k r | ε / 2 < dist y g₀}` using `isOpen_lt continuous_const (continuous_id.dist continuous_const)`. Establish `hev : ∀ᶠ y in 𝓝 x, β y = 0` using `by filter_upwards [hO.mem_nhds (show ε / 2 < dist x g₀ by linarith)] with y hy`.

Conclude with `β.zero_of_le_dist (by rw [hβout]; exact le_of_lt hy)`. Use `contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : Wq →L[ℂ] Wp)) ?_` and prove the remaining obligations. Use `filter_upwards [hev] with y hy`. Simplify using `[hψ, hy]`. Establish `hψc : HasCompactSupport ψ` using `(β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right`.

Establish `hV : IsOpen (Metric.ball g₀ (ε / 4))` using `Metric.isOpen_ball`. Establish `hagree : ∀ x ∈ Metric.ball g₀ (ε / 4), x ∈ B.GV k r → F x = ψ x`. Introduce `x hx hxG`. Establish `h1 : β x = 1` using `β.one_of_mem_closedBall (by rw [hβin]; exact Metric.ball_subset_closedBall hx)`. Establish `hxU : x ∈ U` using `hball (Metric.ball_subset_ball (by linarith) hx)`.

Simplify using `[hψ, h1, he x hxU hxG]`. Establish `hg₀V : g₀ ∈ Metric.ball g₀ (ε / 4)` using `Metric.mem_ball_self (by positivity)`. Establish `h1` using `Formalism.FourierDecayAlt.P.JFxG.adj_local (capTh k r Wp Wq s Y) hV hagree g₀ hg₀V hg₀`. Establish `h2` using `Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r _ (Metric.ball g₀ (ε / 4)) F ψ (conj Y) hV (ckOn_sub_set Set.inter_subset_right (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF)) (ckOn_of_contDiff hψs _ _) (fun x hx => hagree x hx.1 hx.2) g₀ ⟨hg₀V, hg₀⟩`. Rewrite using `[h1, h2]`.

Conclude with `pt_of_int hI hμ s Y hψs hψc hg₀`.
-/
theorem capacity_adjoint_from_integral : CapAdjFromInt := by
  intro hI k r Wp Wq _ _ _ _ _ _ s Y F hF g₀ hg₀
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨U, F', hU, hg₀U, hc, he⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hg₀U
  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  set ψ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • F' g with hψ
  have hψs : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp β.contDiff).contDiffAt).smul
        ((hc.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_rfl))
    · have hx2 : ε ≤ dist x g₀ := by
        by_contra hlt
        exact hx (hball (Metric.mem_ball.2 (lt_of_not_ge hlt)))
      have hO : IsOpen {y : B.Mat k r | ε / 2 < dist y g₀} := isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hev : ∀ᶠ y in 𝓝 x, β y = 0 := by
        filter_upwards [hO.mem_nhds (show ε / 2 < dist x g₀ by linarith)] with y hy
        exact β.zero_of_le_dist (by rw [hβout]; exact le_of_lt hy)
      refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : Wq →L[ℂ] Wp)) ?_
      filter_upwards [hev] with y hy
      simp [hψ, hy]
  have hψc : HasCompactSupport ψ :=
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right
  have hV : IsOpen (Metric.ball g₀ (ε / 4)) := Metric.isOpen_ball
  have hagree : ∀ x ∈ Metric.ball g₀ (ε / 4), x ∈ B.GV k r → F x = ψ x := by
    intro x hx hxG
    have h1 : β x = 1 := β.one_of_mem_closedBall (by rw [hβin]; exact Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U := hball (Metric.ball_subset_ball (by linarith) hx)
    simp [hψ, h1, he x hxU hxG]
  have hg₀V : g₀ ∈ Metric.ball g₀ (ε / 4) := Metric.mem_ball_self (by positivity)
  have h1 := Formalism.FourierDecayAlt.P.JFxG.adj_local (capTh k r Wp Wq s Y) hV hagree g₀ hg₀V hg₀
  have h2 := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r _ (Metric.ball g₀ (ε / 4)) F ψ (conj Y) hV
    (ckOn_sub_set Set.inter_subset_right (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF))
    (ckOn_of_contDiff hψs _ _) (fun x hx => hagree x hx.1 hx.2) g₀ ⟨hg₀V, hg₀⟩
  rw [h1, h2]
  exact pt_of_int hI hμ s Y hψs hψc hg₀

/- English proof (translation)
The claim follows from `capacity_adjoint_from_integral hI`.
-/
theorem capAdj_of_int (hI : CapAdjInt) : CapAdj := capacity_adjoint_from_integral hI

end

end Formalism.FourierDecayAlt.P.CutMP.ER
