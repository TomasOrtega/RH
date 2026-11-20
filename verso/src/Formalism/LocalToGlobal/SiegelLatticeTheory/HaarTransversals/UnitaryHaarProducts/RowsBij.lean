import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Lemmata.GeneralBFactRightLast.Slot

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.L2.SG.RowsDef

def UnimodGf : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], μf.IsMulRightInvariant

section Lin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/- English proof (translation)
Establish `key : ⟪ψ (a • y + b) - a • ψ y - ψ b, ψ (a • y + b) - a • ψ y - ψ b⟫_ℂ = 0`. Simplify using `only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h]`. Simplify using `only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[inner_self_eq_zero, sub_sub, sub_eq_zero]`.

Conclude with `key`.
-/
theorem map_lin_of_inner (ψ : E → F) (C : ℂ) (h : ∀ y y', ⟪ψ y, ψ y'⟫_ℂ = C * ⟪y, y'⟫_ℂ)
    (a : ℂ) (y b : E) : ψ (a • y + b) = a • ψ y + ψ b := by
  have key : ⟪ψ (a • y + b) - a • ψ y - ψ b, ψ (a • y + b) - a • ψ y - ψ b⟫_ℂ = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    ring
  rw [inner_self_eq_zero, sub_sub, sub_eq_zero] at key
  exact key

/- English proof (translation)
Establish `h0` using `h 0 0`. Rewrite `h0` using `[inner_zero_left, mul_zero, inner_self_eq_zero]`. Conclude with `h0`.
-/
theorem map_zero_of_inner (ψ : E → F) (C : ℂ) (h : ∀ y y', ⟪ψ y, ψ y'⟫_ℂ = C * ⟪y, y'⟫_ℂ) :
    ψ 0 = 0 := by
  have h0 := h 0 0
  rw [inner_zero_left, mul_zero, inner_self_eq_zero] at h0
  exact h0

def linOfInner (ψ : E → F) (C : ℂ) (h : ∀ y y', ⟪ψ y, ψ y'⟫_ℂ = C * ⟪y, y'⟫_ℂ) : E →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := ψ
      map_add' := fun y b => by simpa using map_lin_of_inner ψ C h 1 y b
      map_smul' := fun a y => by
        have := map_lin_of_inner ψ C h a y 0
        rw [add_zero, map_zero_of_inner ψ C h, add_zero] at this
        simpa using this }
    (Real.sqrt ‖C‖) (fun y => by
      have h1 : ‖ψ y‖ ^ 2 ≤ (Real.sqrt ‖C‖ * ‖y‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
        calc RCLike.re (C * ⟪y, y⟫_ℂ) ≤ ‖C * ⟪y, y⟫_ℂ‖ := RCLike.re_le_norm _
          _ = ‖C‖ * ‖y‖ ^ 2 := by rw [norm_mul, inner_self_eq_norm_sq_to_K]; simp
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem linOfInner_apply (ψ : E → F) (C : ℂ) (h : ∀ y y', ⟪ψ y, ψ y'⟫_ℂ = C * ⟪y, y'⟫_ℂ)
    (y : E) : linOfInner ψ C h y = ψ y := rfl

end Lin

/- English proof (translation)
Establish `hb : ρ b = (ρ a).comp (ρ (a⁻¹ * b))` using `by rw [← hm, mul_inv_cancel_left]`. Rewrite using `[hb, ContinuousLinearMap.comp_apply]`. Conclude with `LinearIsometry.inner_map_map ⟨(ρ a).toLinearMap, hi a⟩ x (ρ (a⁻¹ * b) y)`.
-/
theorem inner_orbit {G K : Type*} [Group G] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (ρ : G → (K →L[ℂ] K)) (hm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hi : ∀ a z, ‖ρ a z‖ = ‖z‖)
    (a b : G) (x y : K) : ⟪ρ a x, ρ b y⟫_ℂ = ⟪x, ρ (a⁻¹ * b) y⟫_ℂ := by
  have hb : ρ b = (ρ a).comp (ρ (a⁻¹ * b)) := by rw [← hm, mul_inv_cancel_left]
  rw [hb, ContinuousLinearMap.comp_apply]
  exact LinearIsometry.inner_map_map ⟨(ρ a).toLinearMap, hi a⟩ x (ρ (a⁻¹ * b) y)

section Tens

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun u hu => ?_` and prove the remaining obligations. Establish `hu' : u ≠ j` using `Finset.ne_of_mem_erase hu`. Simplify using `[hu']`.

Simplify using the standard rewrite rules.
-/
theorem prod_update_inner (x : ∀ i, H i) (j : ι) (y y' : H j) :
    ∏ u, ⟪Function.update x j y u, Function.update x j y' u⟫_ℂ =
      (∏ u ∈ Finset.univ.erase j, ⟪x u, x u⟫_ℂ) * ⟪y, y'⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun u hu => ?_
    have hu' : u ≠ j := Finset.ne_of_mem_erase hu
    simp [hu']
  · simp

def slice (tens : (∀ i, H i) → Hs) (htin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (x : ∀ i, H i) (j : ι) : H j →L[ℂ] Hs :=
  linOfInner (fun y => tens (Function.update x j y)) (∏ u ∈ Finset.univ.erase j, ⟪x u, x u⟫_ℂ)
    (fun y y' => by rw [htin]; exact prod_update_inner x j y y')

/- English proof (translation)
Establish `hsq : ∀ x y, ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ i, ⟪x i, x i⟫_ℂ) - (∏ i, ⟪x i, y i⟫_ℂ) - (∏ i, ⟪y i, x i⟫_ℂ) + ∏ i, ⟪y i, y i⟫_ℂ)`. Introduce `x y`. Rewrite using `[← htin, ← htin, ← htin, ← htin, ← inner_self_eq_norm_sq (𝕜 := ℂ)]`. Establish `e : ⟪tens x - tens y, tens x - tens y⟫_ℂ = ⟪tens x, tens x⟫_ℂ - ⟪tens x, tens y⟫_ℂ - ⟪tens y, tens x⟫_ℂ + ⟪tens y, tens y⟫_ℂ`. Simplify using `only [inner_sub_left, inner_sub_right]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`. Rewrite using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`.

Establish `hg : Continuous fun x : ∀ i, H i => RCLike.re ((∏ i, ⟪x i, x i⟫_ℂ) - (∏ i, ⟪x i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x i⟫_ℂ) + ∏ i, ⟪x0 i, x0 i⟫_ℂ)` using `by fun_prop`. Establish `h0` using `(Real.continuous_sqrt.comp hg).tendsto x0`. Establish `heq : (fun x => ‖tens x - tens x0‖) = fun x => Real.sqrt (RCLike.re ((∏ i, ⟪x i, x i⟫_ℂ) - (∏ i, ⟪x i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x i⟫_ℂ) + ∏ i, ⟪x0 i, x0 i⟫_ℂ))`. Use function extensionality and compare the values at `x`. Rewrite using `[← hsq, Real.sqrt_sq (norm_nonneg _)]`.

Rewrite using `[heq]`. Establish `hval : Real.sqrt (RCLike.re ((∏ i, ⟪x0 i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x0 i⟫_ℂ) + ∏ i, ⟪x0 i, x0 i⟫_ℂ)) = 0` using `by simp`. Simplify using `only [Function.comp_apply] at h0`. Rewrite `h0` using `[hval]`. Conclude with `h0`.
-/
theorem tens_continuous (tens : (∀ i, H i) → Hs) (htin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) :
    Continuous tens := by
  have hsq : ∀ x y, ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ i, ⟪x i, x i⟫_ℂ) - (∏ i, ⟪x i, y i⟫_ℂ) -
      (∏ i, ⟪y i, x i⟫_ℂ) + ∏ i, ⟪y i, y i⟫_ℂ) := by
    intro x y
    rw [← htin, ← htin, ← htin, ← htin, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have e : ⟪tens x - tens y, tens x - tens y⟫_ℂ = ⟪tens x, tens x⟫_ℂ - ⟪tens x, tens y⟫_ℂ -
        ⟪tens y, tens x⟫_ℂ + ⟪tens y, tens y⟫_ℂ := by
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [e]
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Continuous fun x : ∀ i, H i => RCLike.re ((∏ i, ⟪x i, x i⟫_ℂ) - (∏ i, ⟪x i, x0 i⟫_ℂ) -
      (∏ i, ⟪x0 i, x i⟫_ℂ) + ∏ i, ⟪x0 i, x0 i⟫_ℂ) := by fun_prop
  have h0 := (Real.continuous_sqrt.comp hg).tendsto x0
  have heq : (fun x => ‖tens x - tens x0‖) = fun x => Real.sqrt (RCLike.re ((∏ i, ⟪x i, x i⟫_ℂ) -
      (∏ i, ⟪x i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x i⟫_ℂ) + ∏ i, ⟪x0 i, x0 i⟫_ℂ)) := by
    funext x
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  have hval : Real.sqrt (RCLike.re ((∏ i, ⟪x0 i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x0 i⟫_ℂ) - (∏ i, ⟪x0 i, x0 i⟫_ℂ) +
      ∏ i, ⟪x0 i, x0 i⟫_ℂ)) = 0 := by simp
  simp only [Function.comp_apply] at h0
  rw [hval] at h0
  exact h0

/- English proof (translation)
Establish `key : ∀ S : Finset ι, ∀ x : ∀ i, H i, (∀ i, i ∉ S → x i ∈ A i) → tens x ∈ M`. Introduce `S`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `h0 x fun i => hx i (by simp)`.

Introduce `j S hj ih x hx`. Set `L` to `slice tens htin x j`. Establish `hL : ∀ y, L y = tens (Function.update x j y)` using `fun y => rfl`. Set `P : Submodule ℂ (H j)` to `M.comap (L : H j →ₗ[ℂ] Hs)`. Establish `hPc : IsClosed (P : Set (H j))` using `hM.preimage L.continuous`.

Establish `hAP : A j ⊆ P`. Introduce `a ha`. Use `show L a ∈ M`. Rewrite using `[hL]`. Apply `ih` to reduce the goal to its premises.

Introduce `i hi`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using ha`. Rewrite using `[Function.update_of_ne hij]`.

Conclude with `hx i (by simp [hi, hij])`. Establish `htop : (⊤ : Submodule ℂ (H j)) ≤ P`. Rewrite using `[← hA j]`. Conclude with `Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hAP) hPc`. Establish `hxj` using `htop (Submodule.mem_top : x j ∈ ⊤)`.

Simplify `hxj` using `[P, hL, Submodule.mem_comap]`. Introduce `x`. Conclude with `key Finset.univ x (fun i hi => absurd (Finset.mem_univ i) hi)`.
-/
theorem tens_mem_of (tens : (∀ i, H i) → Hs) (htin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (M : Submodule ℂ Hs) (hM : IsClosed (M : Set Hs)) (A : ∀ i, Set (H i))
    (hA : ∀ i, (Submodule.span ℂ (A i)).topologicalClosure = ⊤)
    (h0 : ∀ x : ∀ i, H i, (∀ i, x i ∈ A i) → tens x ∈ M) : ∀ x, tens x ∈ M := by
  classical
  have key : ∀ S : Finset ι, ∀ x : ∀ i, H i, (∀ i, i ∉ S → x i ∈ A i) → tens x ∈ M := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro x hx
      exact h0 x fun i => hx i (by simp)
    · intro j S hj ih x hx
      let L := slice tens htin x j
      have hL : ∀ y, L y = tens (Function.update x j y) := fun y => rfl
      let P : Submodule ℂ (H j) := M.comap (L : H j →ₗ[ℂ] Hs)
      have hPc : IsClosed (P : Set (H j)) := hM.preimage L.continuous
      have hAP : A j ⊆ P := by
        intro a ha
        show L a ∈ M
        rw [hL]
        apply ih
        intro i hi
        by_cases hij : i = j
        · subst hij
          simpa using ha
        · rw [Function.update_of_ne hij]
          exact hx i (by simp [hi, hij])
      have htop : (⊤ : Submodule ℂ (H j)) ≤ P := by
        rw [← hA j]
        exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hAP) hPc
      have hxj := htop (Submodule.mem_top : x j ∈ ⊤)
      simpa [P, hL, Submodule.mem_comap] using hxj
  intro x
  exact key Finset.univ x (fun i hi => absurd (Finset.mem_univ i) hi)

end Tens

instance pf_muG_right {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsMulRightInvariant :=
  ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩

/- English proof (translation)
Establish `: μf.IsMulRightInvariant` using `hU I μf`. Establish `: (I.muA μf).IsMulLeftInvariant` using `Measure.prod.instIsMulLeftInvariant`. Establish `: (I.muA μf).IsMulRightInvariant` using `Measure.prod.instIsMulRightInvariant`. Establish `h1 : Formalism.MainNotions.LeviCoordinates.rr_FD (I.muA μf) (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund` using `⟨hfund.1, hfund.2.1, hfund.2.2⟩`. Establish `h2 : Formalism.MainNotions.LeviCoordinates.rr_IsReg (I.muA μf) (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund R` using `hR`.

Conclude with `⟨fun a b => Formalism.MainNotions.LeviCoordinates.rr_mul h1 h2 a b, Formalism.MainNotions.LeviCoordinates.rr_one h1 h2, fun a F => Formalism.MainNotions.LeviCoordinates.rr_norm h1 h2 a F⟩`.
-/
theorem reg_alg (hU : UnimodGf) (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hR : I.IsRightReg μf fund R) :
    (∀ a b, R (a * b) = (R a).comp (R b)) ∧ R 1 = 1 ∧ ∀ a F, ‖R a F‖ = ‖F‖ := by
  have : μf.IsMulRightInvariant := hU I μf
  have : (I.muA μf).IsMulLeftInvariant := Measure.prod.instIsMulLeftInvariant
  have : (I.muA μf).IsMulRightInvariant := Measure.prod.instIsMulRightInvariant
  have h1 : Formalism.MainNotions.LeviCoordinates.rr_FD (I.muA μf) (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund := ⟨hfund.1, hfund.2.1, hfund.2.2⟩
  have h2 : Formalism.MainNotions.LeviCoordinates.rr_IsReg (I.muA μf) (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund R := hR
  exact ⟨fun a b => Formalism.MainNotions.LeviCoordinates.rr_mul h1 h2 a b, Formalism.MainNotions.LeviCoordinates.rr_one h1 h2,
    fun a F => Formalism.MainNotions.LeviCoordinates.rr_norm h1 h2 a F⟩

/- English proof (translation)
Take `⟨hd, hF2⟩` from `hF`. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hph : ∀ g, Formalism.L2.SG.ProjRows.phLoc (ε` using `ε) σ w d g * ⟪x, σ (umat g) w⟫_ℂ = (d : ℂ) * (coefOn σ w x g * star (coefOn σ w w g)) := by`. Introduce `g`. Simplify using `only [Formalism.L2.SG.ProjRows.phLoc, coefOn]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hph]`. Establish `hww : ⟪w, w⟫_ℂ = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, hw]`. Simplify using the standard rewrite rules.

Rewrite using `[MeasureTheory.integral_const_mul, (hF2 w x w w).2, hww, one_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem loc_schur {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} {w : H} (x : H)
    (hF : IsFdeg (Formalism.REAL.muG ε) σ d) (hw : ‖w‖ = 1) :
    ∫ g, phLoc (ε := ε) σ w d g * ⟪x, σ (umat g) w⟫_ℂ ∂(Formalism.REAL.muG ε) = ⟪x, w⟫_ℂ := by
  obtain ⟨hd, hF2⟩ := hF
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hph : ∀ g, Formalism.L2.SG.ProjRows.phLoc (ε := ε) σ w d g * ⟪x, σ (umat g) w⟫_ℂ =
      (d : ℂ) * (coefOn σ w x g * star (coefOn σ w w g)) := by
    intro g
    simp only [Formalism.L2.SG.ProjRows.phLoc, coefOn]
    ring
  simp_rw [hph]
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  rw [MeasureTheory.integral_const_mul, (hF2 w x w w).2, hww, one_mul]
  field_simp

section Glob

variable (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
  [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

/- English proof (translation)
The claim follows from `htens.2.1 g w`.
-/
theorem orbit_eq (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (htens : I.IsHilbTensor σ σs tens)
    (w : ∀ v, H v) (g : I.Ginf) :
    σs g (tens w) = tens fun v => σ v (umat (g v)) (w v) := htens.2.1 g w

/- English proof (translation)
Take `⟨⟨h1, hmul⟩, hiso, hcont⟩` from `hU`. Take `⟨sp, hsp⟩ : ∃ sp : Submodule ℂ K, sp = Submodule.span ℂ (Set.range fun g : Formalism.REAL.UJ ε => σ (umat g) w)` from `⟨_, rfl⟩`. Rewrite using `[← hsp]`. Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1`. Rewrite using `[Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hunit : ∀ m ∈ UJset ε, ∃ g : Formalism.REAL.UJ ε, umat g = m`. Introduce `m hm`.

Establish `hm' : (Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε` using `hm`. Establish `hl : Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m = 1`. Establish `e : Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε * ((Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, hm', hJJ]`.

Establish `hr : m * (Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε) = 1` using `mul_eq_one_comm.mp hl`. Conclude with `⟨⟨⟨m, Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε, hr, hl⟩, hm⟩, rfl⟩`. Establish `hinv : ∀ m ∈ UJset ε, ∀ v ∈ sp.topologicalClosure, σ m v ∈ sp.topologicalClosure`. Introduce `m hm v hv`. Take `⟨g', rfl⟩` from `hunit m hm`.

Establish `hspan : sp ≤ sp.comap (σ (umat g') : K →ₗ[ℂ] K)`. Rewrite using `[hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `σ (umat g') (σ (umat g) w) ∈ Submodule.span ℂ (Set.range fun g : Formalism.REAL.UJ ε => σ (umat g) w)`.

Rewrite using `[← ContinuousLinearMap.comp_apply, ← hmul _ (Formalism.MainNotions.BridgeCSchur.umat_mem g') _ (Formalism.MainNotions.BridgeCSchur.umat_mem g)]`. Conclude with `Submodule.subset_span ⟨g' * g, rfl⟩`. Establish `hcl : sp.topologicalClosure ≤ sp.topologicalClosure.comap (σ (umat g') : K →ₗ[ℂ] K)`. Apply `Submodule.topologicalClosure_minimal` to reduce the goal to its premises. Conclude with `hspan.trans (Submodule.comap_mono (Submodule.le_topologicalClosure _))`.

Conclude with `(Submodule.isClosed_topologicalClosure _).preimage (σ (umat g')).continuous`. Conclude with `hcl hv`. Break down `hI _ (Submodule.isClosed_topologicalClosure _) hinv with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hw0 : w ∈ sp.topologicalClosure`.

Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises. Rewrite using `[hsp]`. Conclude with `Submodule.subset_span ⟨1, by simp [umat, h1]⟩`. Rewrite `hw0` using `[h, Submodule.mem_bot]`. Rewrite `hw` using `[hw0, norm_zero]`.

Conclude with `zero_ne_one hw`. Conclude with `h`.
-/
theorem loc_cyc {n : ℕ} {ε : Fin n → Bool} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ)
    {w : K} (hw : ‖w‖ = 1) :
    (Submodule.span ℂ (Set.range fun g : Formalism.REAL.UJ ε => σ (umat g) w)).topologicalClosure = ⊤ := by
  classical
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hU
  obtain ⟨sp, hsp⟩ : ∃ sp : Submodule ℂ K,
      sp = Submodule.span ℂ (Set.range fun g : Formalism.REAL.UJ ε => σ (umat g) w) := ⟨_, rfl⟩
  rw [← hsp]
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num

  have hunit : ∀ m ∈ UJset ε, ∃ g : Formalism.REAL.UJ ε, umat g = m := by
    intro m hm
    have hm' : (Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
    have hl : Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m = 1 := by
      have e : Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε * ((Matrix.conjTranspose m) * Formalism.REAL.Jm ε * m) := by
        simp only [Matrix.mul_assoc]
      rw [e, hm', hJJ]
    have hr : m * (Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp hl
    exact ⟨⟨⟨m, Formalism.REAL.Jm ε * (Matrix.conjTranspose m) * Formalism.REAL.Jm ε, hr, hl⟩, hm⟩, rfl⟩
  have hinv : ∀ m ∈ UJset ε, ∀ v ∈ sp.topologicalClosure, σ m v ∈ sp.topologicalClosure := by
    intro m hm v hv
    obtain ⟨g', rfl⟩ := hunit m hm
    have hspan : sp ≤ sp.comap (σ (umat g') : K →ₗ[ℂ] K) := by
      rw [hsp, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change σ (umat g') (σ (umat g) w) ∈ Submodule.span ℂ (Set.range fun g : Formalism.REAL.UJ ε => σ (umat g) w)
      rw [← ContinuousLinearMap.comp_apply,
        ← hmul _ (Formalism.MainNotions.BridgeCSchur.umat_mem g') _ (Formalism.MainNotions.BridgeCSchur.umat_mem g)]
      exact Submodule.subset_span ⟨g' * g, rfl⟩
    have hcl : sp.topologicalClosure ≤ sp.topologicalClosure.comap (σ (umat g') : K →ₗ[ℂ] K) := by
      apply Submodule.topologicalClosure_minimal
      · exact hspan.trans (Submodule.comap_mono (Submodule.le_topologicalClosure _))
      · exact (Submodule.isClosed_topologicalClosure _).preimage (σ (umat g')).continuous
    exact hcl hv
  rcases hI _ (Submodule.isClosed_topologicalClosure _) hinv with h | h
  · exfalso
    have hw0 : w ∈ sp.topologicalClosure := by
      apply Submodule.le_topologicalClosure
      rw [hsp]
      exact Submodule.subset_span ⟨1, by simp [umat, h1]⟩
    rw [h, Submodule.mem_bot] at hw0
    rw [hw0, norm_zero] at hw
    exact zero_ne_one hw
  · exact h

/- English proof (translation)
Establish `htin` using `htens.1`. Take `⟨M, hM⟩ : ∃ M : Submodule ℂ Hs, M = (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g (tens w))).topologicalClosure` from `⟨_, rfl⟩`. Rewrite using `[← hM]`. Establish `hMc : IsClosed (M : Set Hs)`. Rewrite using `[hM]`.

Conclude with `Submodule.isClosed_topologicalClosure _`. Establish `hall : ∀ x, tens x ∈ M`. Use `tens_mem_of tens htin M hMc (fun v => Set.range fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g) (w v)) (fun v => loc_cyc (hU v) (hIrr v) (hw v)) ?_` and prove the remaining obligations. Introduce `x hx`. Use `choose g hg using hx`.

Establish `hx' : tens x = σs g (tens w)`. Rewrite using `[htens.2.1 g w]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `(hg v).symm`.

Rewrite using `[hx', hM]`. Conclude with `Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Establish `hsub : (Submodule.span ℂ (Set.range tens) : Set Hs) ⊆ M` using `Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hall x)`.

Conclude with `hMc.closure_subset_iff.mpr hsub (htens.2.2 z)`.
-/
theorem glob_cyc [∀ v, CompleteSpace (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (hU : ∀ v, IsURepOn (UJset (I.ε v)) (σ v)) (hIrr : ∀ v, IsIrredOn (UJset (I.ε v)) (σ v))
    (hw : ∀ v, ‖w v‖ = 1)
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (htens : I.IsHilbTensor σ σs tens) :
    (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g (tens w))).topologicalClosure = ⊤ := by
  classical
  have htin := htens.1
  obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ Hs,
      M = (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g (tens w))).topologicalClosure := ⟨_, rfl⟩
  rw [← hM]
  have hMc : IsClosed (M : Set Hs) := by
    rw [hM]
    exact Submodule.isClosed_topologicalClosure _
  have hall : ∀ x, tens x ∈ M := by
    refine tens_mem_of tens htin M hMc (fun v => Set.range fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g) (w v))
      (fun v => loc_cyc (hU v) (hIrr v) (hw v)) ?_
    intro x hx
    choose g hg using hx
    have hx' : tens x = σs g (tens w) := by
      rw [htens.2.1 g w]
      congr 1
      funext v
      exact (hg v).symm
    rw [hx', hM]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)
  rw [eq_top_iff]
  intro z _
  have hsub : (Submodule.span ℂ (Set.range tens) : Set Hs) ⊆ M :=
    Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hall x)
  exact hMc.closure_subset_iff.mpr hsub (htens.2.2 z)

/- English proof (translation)
Establish `hρ : ∀ v, IsURep (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g))` using `fun v => isURep_of_on (hU v)`. Establish `hph : Integrable (phInf I σ w dv) (muInf I)`. Rewrite using `[phInf_eq]`. Conclude with `Integrable.fintype_prod_dep hL`. Use `set F : I.Ginf → Hs := fun g => σs g (tens w) with hFdef`.

Establish `hFc : Continuous F`. Establish `: F = tens ∘ fun g v => σ v (umat (g v)) (w v)`. Use function extensionality and compare the values at `g`. Conclude with `orbit_eq I σ σs tens htens w g`. Rewrite using `[this]`.

Conclude with `(tens_continuous tens htens.1).comp (continuous_pi fun v => ((hρ v).2.2.2 (w v)).comp (continuous_apply v))`. Establish `hF1 : ∀ g, ‖F g‖ = 1`. Introduce `g`. Establish `h1 : ⟪F g, F g⟫_ℂ = 1`. Simplify using `only [hFdef]`.

Rewrite using `[orbit_eq I σ σs tens htens w g, htens.1]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Set `L : H v →ₗᵢ[ℂ] H v` to `⟨(σ v (umat (g v)) : H v →ₗ[ℂ] H v), fun z => (hρ v).2.2.1 (g v) z⟩`. Use `L.inner_map_map (w v) (w v)` as an intermediate fact. Simplify using `only [L] at this`.

Rewrite using `[show (σ v (umat (g v))) (w v) = L (w v) from rfl, this, inner_self_eq_norm_sq_to_K, hw v]`. Simplify using the standard rewrite rules. Rewrite using `[norm_eq_sqrt_re_inner (𝕜 := ℂ), h1]`. Simplify using the standard rewrite rules. Establish `hint : ∀ u : Hs, Integrable (fun g => phInf I σ w dv g * ⟪u, F g⟫_ℂ) (muInf I)`.

Introduce `u`. Use `Integrable.mono' (hph.norm.mul_const ‖u‖) (hph.aestronglyMeasurable.mul (continuous_const.inner hFc).aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `⟨hint u, ?_⟩` and prove the remaining obligations. Set `Λ : Hs → ℂ` to `fun u => ∫ g, phInf I σ w dv g * ⟪u, F g⟫_ℂ ∂(muInf I)`. Establish `hadd : ∀ a b, Λ (a + b) = Λ a + Λ b`. Introduce `a b`. Simplify using `only [Λ, inner_add_left, mul_add]`.

Conclude with `integral_add (hint a) (hint b)`. Establish `hsmul : ∀ (c : ℂ) a, Λ (c • a) = (starRingEnd ℂ) c * Λ a`. Introduce `c a`. Simplify using `only [Λ, inner_smul_left]`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Expand and normalize the polynomial expressions, which then agree. Set `ΛL : Hs →L⋆[ℂ] ℂ` to `LinearMap.mkContinuous { toFun := Λ, map_add' := hadd, map_smul' := fun c a => by rw [hsmul]; rfl } (∫ g, ‖phInf I σ w dv g‖ ∂(muInf I)) (fun a => by show ‖Λ a‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation.

Use `norm_integral_le_of_norm_le (hph.norm.mul_const ‖a‖) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = (∫ g, ‖phInf I σ w dv g‖ ∂(muInf I)) * ‖a‖ := integral_mul_const _ _)`.

Establish `hΛL : ∀ a, ΛL a = Λ a` using `fun a => rfl`. Set `Z : Submodule ℂ Hs` to `{ carrier := {a | Λ a = ⟪a, tens w⟫_ℂ} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq] at *`. Rewrite using `[hadd, ha, hb, inner_add_left]`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_ofPred_eq, Λ, inner_zero_left, mul_zero, integral_zero]`. Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_ofPred_eq] at *`. Rewrite using `[hsmul, ha, inner_smul_left] }`. Establish `hZc : IsClosed (Z : Set Hs)`.

Establish `: (Z : Set Hs) = {a | ΛL a = ⟪a, tens w⟫_ℂ}` using `rfl`. Rewrite using `[this]`. Conclude with `isClosed_eq ΛL.continuous (continuous_id.inner continuous_const)`. Establish `hpure : ∀ x, tens x ∈ Z`. Introduce `x`.

Use `show Λ (tens x) = ⟪tens x, tens w⟫_ℂ`. Establish `e1 : ∀ g : I.Ginf, phInf I σ w dv g * ⟪tens x, F g⟫_ℂ = ∏ v, (phLoc (ε` using `I.ε v) (σ v) (w v) (dv v) (g v) * ⟪x v, σ v (umat (g v)) (w v)⟫_ℂ) := by`. Introduce `g`. Simplify using `only [hFdef]`. Rewrite using `[orbit_eq I σ σs tens htens w g, htens.1, phInf_eq, Finset.prod_mul_distrib]`.

Simplify using `only [Λ]`. Repeatedly rewrite using `[e1]`. Rewrite using `[integral_fintype_prod_eq_prod (fun v (g : Formalism.REAL.UJ (I.ε v)) => phLoc (ε := I.ε v) (σ v) (w v) (dv v) g * ⟪x v, σ v (umat g) (w v)⟫_ℂ), htens.1]`. Conclude with `Finset.prod_congr rfl fun v _ => loc_schur (x v) (hF v) (hw v)`. Establish `hle : Submodule.span ℂ (Set.range tens) ≤ Z` using `Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hpure x)`.

Establish `: u ∈ closure (Submodule.span ℂ (Set.range tens) : Set Hs)` using `by rw [htens.2.2.closure_eq]; trivial`. Conclude with `(closure_minimal hle hZc) this`.
-/
theorem glob_schur (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (dv : InfinitePlace I.F → ℝ)
    (w : ∀ v, H v)
    (hU : ∀ v, IsURepOn (UJset (I.ε v)) (σ v)) (hF : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (dv v))
    (hw : ∀ v, ‖w v‖ = 1) (hL : ∀ v, Integrable (phLoc (ε := I.ε v) (σ v) (w v) (dv v)) (Formalism.REAL.muG (I.ε v)))
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (htens : I.IsHilbTensor σ σs tens) (u : Hs) :
    Integrable (fun g => phInf I σ w dv g * ⟪u, σs g (tens w)⟫_ℂ) (muInf I) ∧
      ∫ g, phInf I σ w dv g * ⟪u, σs g (tens w)⟫_ℂ ∂(muInf I) = ⟪u, tens w⟫_ℂ := by
  classical
  have hρ : ∀ v, IsURep (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g)) := fun v => isURep_of_on (hU v)
  have hph : Integrable (phInf I σ w dv) (muInf I) := by
    rw [phInf_eq]; exact Integrable.fintype_prod_dep hL

  set F : I.Ginf → Hs := fun g => σs g (tens w) with hFdef
  have hFc : Continuous F := by
    have : F = tens ∘ fun g v => σ v (umat (g v)) (w v) := by
      funext g; exact orbit_eq I σ σs tens htens w g
    rw [this]
    exact (tens_continuous tens htens.1).comp
      (continuous_pi fun v => ((hρ v).2.2.2 (w v)).comp (continuous_apply v))
  have hF1 : ∀ g, ‖F g‖ = 1 := by
    intro g
    have h1 : ⟪F g, F g⟫_ℂ = 1 := by
      simp only [hFdef]
      rw [orbit_eq I σ σs tens htens w g, htens.1]
      refine Finset.prod_eq_one fun v _ => ?_
      let L : H v →ₗᵢ[ℂ] H v := ⟨(σ v (umat (g v)) : H v →ₗ[ℂ] H v), fun z => (hρ v).2.2.1 (g v) z⟩
      have := L.inner_map_map (w v) (w v)
      simp only [L] at this
      rw [show (σ v (umat (g v))) (w v) = L (w v) from rfl, this, inner_self_eq_norm_sq_to_K, hw v]
      simp
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), h1]
    simp
  have hint : ∀ u : Hs, Integrable (fun g => phInf I σ w dv g * ⟪u, F g⟫_ℂ) (muInf I) := by
    intro u
    refine Integrable.mono' (hph.norm.mul_const ‖u‖) (hph.aestronglyMeasurable.mul
      (continuous_const.inner hFc).aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖⟪u, F g⟫_ℂ‖ ≤ ‖u‖ * ‖F g‖ := norm_inner_le_norm _ _
      _ = ‖u‖ := by rw [hF1, mul_one]
  refine ⟨hint u, ?_⟩

  let Λ : Hs → ℂ := fun u => ∫ g, phInf I σ w dv g * ⟪u, F g⟫_ℂ ∂(muInf I)
  have hadd : ∀ a b, Λ (a + b) = Λ a + Λ b := by
    intro a b
    simp only [Λ, inner_add_left, mul_add]
    exact integral_add (hint a) (hint b)
  have hsmul : ∀ (c : ℂ) a, Λ (c • a) = (starRingEnd ℂ) c * Λ a := by
    intro c a
    simp only [Λ, inner_smul_left]
    rw [← integral_const_mul]
    congr 1; funext g; ring
  let ΛL : Hs →L⋆[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := Λ, map_add' := hadd, map_smul' := fun c a => by rw [hsmul]; rfl }
    (∫ g, ‖phInf I σ w dv g‖ ∂(muInf I)) (fun a => by
      show ‖Λ a‖ ≤ _
      calc ‖Λ a‖ ≤ ∫ g, ‖phInf I σ w dv g‖ * ‖a‖ ∂(muInf I) := by
            refine norm_integral_le_of_norm_le (hph.norm.mul_const ‖a‖) (Filter.Eventually.of_forall fun g => ?_)
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            calc ‖⟪a, F g⟫_ℂ‖ ≤ ‖a‖ * ‖F g‖ := norm_inner_le_norm _ _
              _ = ‖a‖ := by rw [hF1, mul_one]
        _ = (∫ g, ‖phInf I σ w dv g‖ ∂(muInf I)) * ‖a‖ := integral_mul_const _ _)
  have hΛL : ∀ a, ΛL a = Λ a := fun a => rfl

  let Z : Submodule ℂ Hs :=
    { carrier := {a | Λ a = ⟪a, tens w⟫_ℂ}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *; rw [hadd, ha, hb, inner_add_left]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Λ, inner_zero_left, mul_zero, integral_zero]
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at *; rw [hsmul, ha, inner_smul_left] }
  have hZc : IsClosed (Z : Set Hs) := by
    have : (Z : Set Hs) = {a | ΛL a = ⟪a, tens w⟫_ℂ} := rfl
    rw [this]
    exact isClosed_eq ΛL.continuous (continuous_id.inner continuous_const)

  have hpure : ∀ x, tens x ∈ Z := by
    intro x
    show Λ (tens x) = ⟪tens x, tens w⟫_ℂ
    have e1 : ∀ g : I.Ginf, phInf I σ w dv g * ⟪tens x, F g⟫_ℂ =
        ∏ v, (phLoc (ε := I.ε v) (σ v) (w v) (dv v) (g v) * ⟪x v, σ v (umat (g v)) (w v)⟫_ℂ) := by
      intro g
      simp only [hFdef]
      rw [orbit_eq I σ σs tens htens w g, htens.1, phInf_eq, Finset.prod_mul_distrib]
    simp only [Λ]
    simp_rw [e1]
    rw [integral_fintype_prod_eq_prod (fun v (g : Formalism.REAL.UJ (I.ε v)) =>
      phLoc (ε := I.ε v) (σ v) (w v) (dv v) g * ⟪x v, σ v (umat g) (w v)⟫_ℂ), htens.1]
    exact Finset.prod_congr rfl fun v _ => loc_schur (x v) (hF v) (hw v)
  have hle : Submodule.span ℂ (Set.range tens) ≤ Z := Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hpure x)
  have : u ∈ closure (Submodule.span ℂ (Set.range tens) : Set Hs) := by rw [htens.2.2.closure_eq]; trivial
  exact (closure_minimal hle hZc) this

end Glob

/- English proof (translation)
Introduce `I μf _ _ fund hfund R hR e Re hRe H _ _ _ σ dv w hU hIrr hF hw hL T hT Hs _ _ _ σs tens htens`. Take `⟨hmul, hone, hiso⟩` from `reg_alg hUn I μf fund hfund R hR`. Establish `hRP : IsRowProj (fun g => R (g, 1)) (mInf I σ w) T` using `hP I μf fund hfund R hR H σ dv w hU hF hw hL T hT`. Establish `hρ : ∀ v, IsURep (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g))` using `fun v => isURep_of_on (hU v)`. Use `set tw := tens w with htw`.

Use `set π : I.Ginf → (I.L2 μf fund →L[ℂ] I.L2 μf fund) := fun g => R (g, 1) with hπ`. Establish `hπmul : ∀ a b, π (a * b) = (π a).comp (π b)`. Introduce `a b`. Simplify using `only [hπ]`. Rewrite using `[← hmul, Prod.mk_mul_mk, mul_one]`.

Establish `hπiso : ∀ a F, ‖π a F‖ = ‖F‖` using `fun a F => hiso _ F`. Establish `hπone : π 1 = 1` using `hone`. Establish `hcomm : ∀ g : I.Ginf, Re.comp (π g) = (π g).comp Re`. Introduce `g`. Use `ext1 y`.

Use `ext_inner_left ℂ fun x => ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.comp_apply, hπ]`. Rewrite using `[hRe.2, ← ContinuousLinearMap.adjoint_inner_left, hRe.2]`. Use `congr 1`. Use function extensionality and compare the values at `h`.

Rewrite using `[ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply (R (1, h)), ← ContinuousLinearMap.comp_apply (R (g, 1)), ← hmul, ← hmul]`. Use `congr 3`. Apply the tactic sequence `ext <;> simp`. Establish `hσmul : ∀ a b : I.Ginf, σs a (σs b tw) = σs (a * b) tw`. Introduce `a b`.

Rewrite using `[orbit_eq I σ σs tens htens w b, htens.2.1, orbit_eq I σ σs tens htens w (a * b)]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Use `(hρ v).2.1 (a v) (b v)` as an intermediate fact. Simplify using `only at this`.

Rewrite using `[show (a * b) v = a v * b v from rfl, this]`. Both sides reduce to the same expression. Establish `hσ1 : σs 1 tw = tw`. Rewrite using `[orbit_eq I σ σs tens htens w 1]`. Use `congr 1`.

Use function extensionality and compare the values at `v`. Use `(hρ v).1` as an intermediate fact. Simplify using `only at this`. Rewrite using `[show (1 : I.Ginf) v = 1 from rfl, this]`. Both sides reduce to the same expression.

Establish `hσinner : ∀ a b : I.Ginf, ⟪σs a tw, σs b tw⟫_ℂ = mInf I σ w (a⁻¹ * b)`. Introduce `a b`. Rewrite using `[orbit_eq I σ σs tens htens w a, orbit_eq I σ σs tens htens w b, htens.1]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Conclude with `inner_orbit (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g)) (hρ v).2.1 (hρ v).2.2.1 (a v) (b v) (w v) (w v)`.

Establish `hcyc` using `glob_cyc I σ w hU hIrr hw σs tens htens`. Establish `hTA : ∀ A : Hs →L[ℂ] I.L2 μf fund, (∀ g, A.comp (σs g) = (π g).comp A) → T (A tw) = A tw`. Introduce `A hA`. Use `ext_inner_left ℂ fun x => ?_` and prove the remaining obligations. Rewrite using `[hT x (A tw)]`.

Establish `e1 : ∀ g : I.Ginf, phInf I σ w dv g * ⟪x, π g (A tw)⟫_ℂ = phInf I σ w dv g * ⟪ContinuousLinearMap.adjoint A x, σs g tw⟫_ℂ`. Introduce `g`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply (π g) A, ← hA g, ContinuousLinearMap.comp_apply]`. Repeatedly rewrite using `[e1]`. Rewrite using `[(glob_schur I σ dv w hU hF hw hL σs tens htens _).2, ContinuousLinearMap.adjoint_inner_left]`.

Establish `hexists : ∀ z, T z = z → ∃ A : Hs →L[ℂ] I.L2 μf fund, (∀ g, A.comp (σs g) = (π g).comp A) ∧ A tw = z`. Introduce `z hz`. Establish `hpair : ∀ a b : I.Ginf, ⟪π a z, π b z⟫_ℂ = ⟪z, z⟫_ℂ * ⟪σs a tw, σs b tw⟫_ℂ`. Introduce `a b`. Rewrite using `[inner_orbit π hπmul hπiso, hσinner]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hRP.2.2 (a⁻¹ * b)]`. Rewrite using `[ContinuousLinearMap.smul_apply, inner_smul_right, hz]`. Use `_ = ⟪z, z⟫_ℂ * mInf I σ w (a⁻¹ * b) := mul_comm _ _`. Set `Φ₁ : (I.Ginf →₀ ℂ) →ₗ[ℂ] Hs` to `Finsupp.linearCombination ℂ fun g => σs g tw`.

Set `Φ₂ : (I.Ginf →₀ ℂ) →ₗ[ℂ] I.L2 μf fund` to `Finsupp.linearCombination ℂ fun g => π g z`. Establish `hkey : ∀ c c', ⟪Φ₂ c, Φ₂ c'⟫_ℂ = ⟪z, z⟫_ℂ * ⟪Φ₁ c, Φ₁ c'⟫_ℂ`. Introduce `c c'`. Simplify using `only [Φ₁, Φ₂, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hpair, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => by ring` and prove the remaining obligations.

Establish `hnorm : ∀ c, ‖Φ₂ c‖ = ‖z‖ * ‖Φ₁ c‖`. Introduce `c`. Establish `h` using `hkey c c`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h' : ‖Φ₂ c‖ ^ 2 = (‖z‖ * ‖Φ₁ c‖) ^ 2` using `by rw [mul_pow]; exact_mod_cast h`.

Conclude with `(pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'`. Establish `hker : LinearMap.ker Φ₁ ≤ LinearMap.ker Φ₂`. Introduce `c hc`. Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← norm_eq_zero, hnorm, hc, norm_zero, mul_zero]`.

Set `B : LinearMap.range Φ₁ →ₗ[ℂ] I.L2 μf fund` to `((LinearMap.ker Φ₁).liftQ Φ₂ hker).comp (Φ₁.quotKerEquivRange.symm : LinearMap.range Φ₁ →ₗ[ℂ] _)`. Establish `hB : ∀ c, B ⟨Φ₁ c, LinearMap.mem_range_self Φ₁ c⟩ = Φ₂ c`. Introduce `c`. Simplify using `only [B, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]`. Establish `hBn : ∀ y, ‖B y‖ ≤ ‖z‖ * ‖y‖`.

Introduce and unpack `⟨_, c, rfl⟩`. Rewrite using `[hB, hnorm]`. Both sides reduce to the same expression. Set `BL : LinearMap.range Φ₁ →L[ℂ] I.L2 μf fund` to `B.mkContinuous ‖z‖ hBn`. Set `eL : LinearMap.range Φ₁ →L[ℂ] Hs` to `(LinearMap.range Φ₁).subtypeL`.

Establish `hdense : DenseRange eL`. Establish `h1 : Set.range eL = (LinearMap.range Φ₁ : Set Hs)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `y.2`. Introduce `hx`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Rewrite using `[DenseRange, h1, Finsupp.range_linearCombination, Submodule.dense_iff_topologicalClosure_eq_top]`. Conclude with `hcyc`.

Establish `hui : IsUniformInducing eL` using `isUniformEmbedding_subtype_val.isUniformInducing`. Set `A` to `BL.extend eL`. Establish `hAk : ∀ k, A (σs k tw) = π k z`. Introduce `k`. Establish `h1 : σs k tw = eL ⟨Φ₁ (Finsupp.single k 1), LinearMap.mem_range_self Φ₁ _⟩`.

Simplify using `[eL, Φ₁]`. Rewrite using `[h1, ContinuousLinearMap.extend_eq BL hdense hui]`. Use `show B _ = _`. Rewrite using `[hB]`. Simplify using `[Φ₂]`.

Use `⟨A, fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `hker2 : (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g tw)).topologicalClosure ≤ LinearMap.ker ((A.comp (σs h) - (π h).comp A : Hs →L[ℂ] I.L2 μf fund) : Hs →ₗ[ℂ] I.L2 μf fund)`. Use `Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) (ContinuousLinearMap.isClosed_ker _)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]`.

Rewrite using `[hσmul, hAk, hAk, hπmul, ContinuousLinearMap.comp_apply, sub_self]`. Rewrite `hker2` using `[hcyc]`. Use `ext1 u`. Use `hker2 (Submodule.mem_top (x := u))` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, ContinuousLinearMap.coe_coe]`.

Conclude with `sub_eq_zero.1 this`. Use `hAk 1` as an intermediate fact. Rewrite `this` using `[hσ1, hπone, ContinuousLinearMap.one_apply]`. Then use the resulting hypothesis. Establish `hmemE : ∀ S, S ∈ I.eHom σs μf fund R Re ↔ ∃ A : Hs →L[ℂ] I.L2 μf fund, (∀ g, A.comp (σs g) = (π g).comp A) ∧ Re.comp A = S`. Introduce `S`.

Simplify using `only [AutInst.eHom, Submodule.mem_map]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨S, hS⟩ h0`.

Take `⟨A, hA, rfl⟩` from `(hmemE S).1 hS`. Establish `h0' : (Re.comp A) tw = 0` using `h0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Re.comp A = 0`. Establish `hker2 : (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g tw)).topologicalClosure ≤ LinearMap.ker ((Re.comp A : Hs →L[ℂ] I.L2 μf fund) : Hs →ₗ[ℂ] I.L2 μf fund)`.

Use `Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) (ContinuousLinearMap.isClosed_ker _)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]`. Rewrite using `[← ContinuousLinearMap.comp_apply (Re.comp A), ContinuousLinearMap.comp_assoc, hA k, ← ContinuousLinearMap.comp_assoc, hcomm k, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_apply, h0', map_zero]`. Rewrite `hker2` using `[hcyc]`.

Use `ext1 u`. Use `LinearMap.mem_ker.1 (hker2 (Submodule.mem_top (x := u)))` as an intermediate fact. Rewrite `this` using `[ContinuousLinearMap.coe_coe]`. Rewrite using `[this, ContinuousLinearMap.zero_apply]`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨S, hS⟩, rfl⟩`. Take `⟨A, hA, rfl⟩` from `(hmemE S).1 hS`. Use `⟨A tw, ?_⟩` and prove the remaining obligations. Use `show Re (T (A tw)) = Re (A tw)`.

Rewrite using `[hTA A hA]`. Introduce and unpack `⟨y, rfl⟩`. Establish `hz : T (T y) = T y`. Use `hRP.2.1` as an intermediate fact. Rewrite using `[← ContinuousLinearMap.comp_apply, this]`.

Take `⟨A, hA, hAw⟩` from `hexists (T y) hz`. Use `⟨⟨Re.comp A, (hmemE _).2 ⟨A, hA, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use `show Re (A tw) = Re (T y)`. Rewrite using `[hAw]`.
-/
theorem rows_bijective (hP : ProjRowsR) (hUn : UnimodGf) : RowsBij := by
  classical
  intro I μf _ _ fund hfund R hR e Re hRe H _ _ _ σ dv w hU hIrr hF hw hL T hT Hs _ _ _ σs tens htens
  obtain ⟨hmul, hone, hiso⟩ := reg_alg hUn I μf fund hfund R hR
  have hRP : IsRowProj (fun g => R (g, 1)) (mInf I σ w) T := hP I μf fund hfund R hR H σ dv w hU hF hw hL T hT
  have hρ : ∀ v, IsURep (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g)) := fun v => isURep_of_on (hU v)
  set tw := tens w with htw
  set π : I.Ginf → (I.L2 μf fund →L[ℂ] I.L2 μf fund) := fun g => R (g, 1) with hπ
  have hπmul : ∀ a b, π (a * b) = (π a).comp (π b) := by
    intro a b; simp only [hπ]; rw [← hmul, Prod.mk_mul_mk, mul_one]
  have hπiso : ∀ a F, ‖π a F‖ = ‖F‖ := fun a F => hiso _ F
  have hπone : π 1 = 1 := hone

  have hcomm : ∀ g : I.Ginf, Re.comp (π g) = (π g).comp Re := by
    intro g
    ext1 y
    refine ext_inner_left ℂ fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, hπ]
    rw [hRe.2, ← ContinuousLinearMap.adjoint_inner_left, hRe.2]
    congr 1; funext h
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply (R (1, h)),
      ← ContinuousLinearMap.comp_apply (R (g, 1)), ← hmul, ← hmul]
    congr 3
    ext <;> simp

  have hσmul : ∀ a b : I.Ginf, σs a (σs b tw) = σs (a * b) tw := by
    intro a b
    rw [orbit_eq I σ σs tens htens w b, htens.2.1, orbit_eq I σ σs tens htens w (a * b)]
    congr 1; funext v
    have := (hρ v).2.1 (a v) (b v)
    simp only at this
    rw [show (a * b) v = a v * b v from rfl, this]; rfl
  have hσ1 : σs 1 tw = tw := by
    rw [orbit_eq I σ σs tens htens w 1]
    congr 1; funext v
    have := (hρ v).1
    simp only at this
    rw [show (1 : I.Ginf) v = 1 from rfl, this]; rfl
  have hσinner : ∀ a b : I.Ginf, ⟪σs a tw, σs b tw⟫_ℂ = mInf I σ w (a⁻¹ * b) := by
    intro a b
    rw [orbit_eq I σ σs tens htens w a, orbit_eq I σ σs tens htens w b, htens.1]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact inner_orbit (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g)) (hρ v).2.1 (hρ v).2.2.1 (a v) (b v) (w v) (w v)
  have hcyc := glob_cyc I σ w hU hIrr hw σs tens htens

  have hTA : ∀ A : Hs →L[ℂ] I.L2 μf fund, (∀ g, A.comp (σs g) = (π g).comp A) → T (A tw) = A tw := by
    intro A hA
    refine ext_inner_left ℂ fun x => ?_
    rw [hT x (A tw)]
    have e1 : ∀ g : I.Ginf, phInf I σ w dv g * ⟪x, π g (A tw)⟫_ℂ =
        phInf I σ w dv g * ⟪ContinuousLinearMap.adjoint A x, σs g tw⟫_ℂ := by
      intro g
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply (π g) A, ← hA g,
        ContinuousLinearMap.comp_apply]
    simp_rw [e1]
    rw [(glob_schur I σ dv w hU hF hw hL σs tens htens _).2, ContinuousLinearMap.adjoint_inner_left]

  have hexists : ∀ z, T z = z → ∃ A : Hs →L[ℂ] I.L2 μf fund, (∀ g, A.comp (σs g) = (π g).comp A) ∧ A tw = z := by
    intro z hz
    have hpair : ∀ a b : I.Ginf, ⟪π a z, π b z⟫_ℂ = ⟪z, z⟫_ℂ * ⟪σs a tw, σs b tw⟫_ℂ := by
      intro a b
      rw [inner_orbit π hπmul hπiso, hσinner]
      calc ⟪z, π (a⁻¹ * b) z⟫_ℂ = ⟪T z, π (a⁻¹ * b) (T z)⟫_ℂ := by rw [hz]
        _ = ⟪z, T (π (a⁻¹ * b) (T z))⟫_ℂ := hRP.1 _ _
        _ = ⟪z, (T.comp ((π (a⁻¹ * b)).comp T)) z⟫_ℂ := rfl
        _ = mInf I σ w (a⁻¹ * b) * ⟪z, z⟫_ℂ := by
          rw [hRP.2.2 (a⁻¹ * b)]
          rw [ContinuousLinearMap.smul_apply, inner_smul_right, hz]
        _ = ⟪z, z⟫_ℂ * mInf I σ w (a⁻¹ * b) := mul_comm _ _
    let Φ₁ : (I.Ginf →₀ ℂ) →ₗ[ℂ] Hs := Finsupp.linearCombination ℂ fun g => σs g tw
    let Φ₂ : (I.Ginf →₀ ℂ) →ₗ[ℂ] I.L2 μf fund := Finsupp.linearCombination ℂ fun g => π g z
    have hkey : ∀ c c', ⟪Φ₂ c, Φ₂ c'⟫_ℂ = ⟪z, z⟫_ℂ * ⟪Φ₁ c, Φ₁ c'⟫_ℂ := by
      intro c c'
      simp only [Φ₁, Φ₂, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hpair, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => by ring
    have hnorm : ∀ c, ‖Φ₂ c‖ = ‖z‖ * ‖Φ₁ c‖ := by
      intro c
      have h := hkey c c
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
      have h' : ‖Φ₂ c‖ ^ 2 = (‖z‖ * ‖Φ₁ c‖) ^ 2 := by rw [mul_pow]; exact_mod_cast h
      exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
    have hker : LinearMap.ker Φ₁ ≤ LinearMap.ker Φ₂ := by
      intro c hc
      rw [LinearMap.mem_ker] at hc ⊢
      rw [← norm_eq_zero, hnorm, hc, norm_zero, mul_zero]
    let B : LinearMap.range Φ₁ →ₗ[ℂ] I.L2 μf fund :=
      ((LinearMap.ker Φ₁).liftQ Φ₂ hker).comp (Φ₁.quotKerEquivRange.symm : LinearMap.range Φ₁ →ₗ[ℂ] _)
    have hB : ∀ c, B ⟨Φ₁ c, LinearMap.mem_range_self Φ₁ c⟩ = Φ₂ c := by
      intro c
      simp only [B, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
        Submodule.mkQ_apply, Submodule.liftQ_apply]
    have hBn : ∀ y, ‖B y‖ ≤ ‖z‖ * ‖y‖ := by
      rintro ⟨_, c, rfl⟩
      rw [hB, hnorm]
      rfl
    let BL : LinearMap.range Φ₁ →L[ℂ] I.L2 μf fund := B.mkContinuous ‖z‖ hBn
    let eL : LinearMap.range Φ₁ →L[ℂ] Hs := (LinearMap.range Φ₁).subtypeL
    have hdense : DenseRange eL := by
      have h1 : Set.range eL = (LinearMap.range Φ₁ : Set Hs) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩; exact y.2
        · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
      rw [DenseRange, h1, Finsupp.range_linearCombination, Submodule.dense_iff_topologicalClosure_eq_top]
      exact hcyc
    have hui : IsUniformInducing eL := isUniformEmbedding_subtype_val.isUniformInducing
    let A := BL.extend eL
    have hAk : ∀ k, A (σs k tw) = π k z := by
      intro k
      have h1 : σs k tw = eL ⟨Φ₁ (Finsupp.single k 1), LinearMap.mem_range_self Φ₁ _⟩ := by
        simp [eL, Φ₁]
      rw [h1, ContinuousLinearMap.extend_eq BL hdense hui]
      show B _ = _
      rw [hB]
      simp [Φ₂]
    refine ⟨A, fun h => ?_, ?_⟩
    ·
      have hker2 : (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g tw)).topologicalClosure ≤
          LinearMap.ker ((A.comp (σs h) - (π h).comp A : Hs →L[ℂ] I.L2 μf fund) : Hs →ₗ[ℂ] I.L2 μf fund) := by
        refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
          (ContinuousLinearMap.isClosed_ker _)
        rintro _ ⟨k, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
        rw [hσmul, hAk, hAk, hπmul, ContinuousLinearMap.comp_apply, sub_self]
      rw [hcyc] at hker2
      ext1 u
      have := hker2 (Submodule.mem_top (x := u))
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
      exact sub_eq_zero.1 this
    · have := hAk 1
      rwa [hσ1, hπone, ContinuousLinearMap.one_apply] at this

  have hmemE : ∀ S, S ∈ I.eHom σs μf fund R Re ↔
      ∃ A : Hs →L[ℂ] I.L2 μf fund, (∀ g, A.comp (σs g) = (π g).comp A) ∧ Re.comp A = S := by
    intro S
    simp only [AutInst.eHom, Submodule.mem_map]
    rfl
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    rintro ⟨S, hS⟩ h0
    obtain ⟨A, hA, rfl⟩ := (hmemE S).1 hS
    have h0' : (Re.comp A) tw = 0 := h0
    apply Subtype.ext
    show Re.comp A = 0
    have hker2 : (Submodule.span ℂ (Set.range fun g : I.Ginf => σs g tw)).topologicalClosure ≤
        LinearMap.ker ((Re.comp A : Hs →L[ℂ] I.L2 μf fund) : Hs →ₗ[ℂ] I.L2 μf fund) := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
        (ContinuousLinearMap.isClosed_ker _)
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [← ContinuousLinearMap.comp_apply (Re.comp A), ContinuousLinearMap.comp_assoc, hA k,
        ← ContinuousLinearMap.comp_assoc, hcomm k, ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_apply, h0', map_zero]
    rw [hcyc] at hker2
    ext1 u
    have := LinearMap.mem_ker.1 (hker2 (Submodule.mem_top (x := u)))
    rw [ContinuousLinearMap.coe_coe] at this
    rw [this, ContinuousLinearMap.zero_apply]
  ·
    ext v
    constructor
    · rintro ⟨⟨S, hS⟩, rfl⟩
      obtain ⟨A, hA, rfl⟩ := (hmemE S).1 hS
      refine ⟨A tw, ?_⟩
      show Re (T (A tw)) = Re (A tw)
      rw [hTA A hA]
    · rintro ⟨y, rfl⟩
      have hz : T (T y) = T y := by
        have := hRP.2.1
        rw [← ContinuousLinearMap.comp_apply, this]
      obtain ⟨A, hA, hAw⟩ := hexists (T y) hz
      refine ⟨⟨Re.comp A, (hmemE _).2 ⟨A, hA, rfl⟩⟩, ?_⟩
      show Re (A tw) = Re (T y)
      rw [hAw]

end Formalism.L2.SG.Pf
