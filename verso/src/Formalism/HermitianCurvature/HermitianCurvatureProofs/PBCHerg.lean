import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCSplit

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def psiG (g : ℝ) (l c : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * (l * c).re / g : ℝ) : ℂ))

def Fz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, D v h h' (z v)

def Nz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℝ :=
  if Good z then (Fz Y κ D z).re else 0

/- English proof (translation)
Set `k : Option (Fin f) → H → H → ℂ` to `fun o => match o with`. Consider the case `none => κ`. Consider the case `some v => fun h h' => D v h h' (z v)`. Establish `hk : ∀ o, TB.PSDOn Y (k o)`. Introduce `o`.

Break down `o with _ | v` into its components or cases. Conclude with `hκ`. Conclude with `hD v (z v) (hz v)`. Establish `hS` using `Formalism.FourierDecayAlt.P.schur_product _ (Option (Fin f)) Y k hk`. Establish `hC` using `JCx1.decay.psd_compress Y _ hS (fun _ : Unit => Y) (fun _ => id) (fun _ h hh => hh)`.

Use `hC.diag_nonneg (i := ())` as an intermediate fact. Simplify using `only [Matrix.of_apply, id] at this`. Use `this using 1` and compare the differences between its conclusion and the goal. Unfold `Fz`. Simplify using `[Fintype.prod_option, k]`.
-/
theorem Fz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) (hz : Good z) :
    0 ≤ Fz Y κ D z := by
  let k : Option (Fin f) → H → H → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => D v h h' (z v)
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o; rcases o with _ | v
    · exact hκ
    · exact hD v (z v) (hz v)
  have hS := Formalism.FourierDecayAlt.P.schur_product _ (Option (Fin f)) Y k hk
  have hC := JCx1.decay.psd_compress Y _ hS (fun _ : Unit => Y) (fun _ => id) (fun _ h hh => hh)
  have := hC.diag_nonneg (i := ())
  simp only [Matrix.of_apply, id] at this
  convert this using 1
  unfold Fz
  simp [Fintype.prod_option, k]

/- English proof (translation)
Unfold `Nz`. Use `split_ifs with hz`. Conclude with `(Complex.nonneg_iff.1 (Fz_nonneg Y κ hκ D hD z hz)).1`. Conclude with `le_rfl`.
-/
theorem Nz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) : 0 ≤ Nz Y κ D z := by
  unfold Nz; split_ifs with hz
  · exact (Complex.nonneg_iff.1 (Fz_nonneg Y κ hκ D hD z hz)).1
  · exact le_rfl

/- English proof (translation)
Establish `: {z : crystallineComparison.V f | Good z} = ⋂ v, (fun z : crystallineComparison.V f => z v) ⁻¹' {0}ᶜ`. Use extensionality with `z`. Simplify using `[Good]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun v => (continuous_apply v).isOpen_preimage _ isOpen_compl_singleton`.
-/
theorem isOpen_good : IsOpen {z : crystallineComparison.V f | Good z} := by
  have : {z : crystallineComparison.V f | Good z} = ⋂ v, (fun z : crystallineComparison.V f => z v) ⁻¹' {0}ᶜ := by
    ext z; simp [Good]
  rw [this]
  exact isOpen_iInter_of_finite fun v => (continuous_apply v).isOpen_preimage _ isOpen_compl_singleton

/- English proof (translation)
Unfold `Fz ContinuousAt`. Use `tendsto_finsetSum _ fun h hh => tendsto_finsetSum _ fun h' hh' => ?_` and prove the remaining obligations. Use `tendsto_const_nhds.mul (tendsto_finsetProd _ fun v _ => ?_)` and prove the remaining obligations. Use `(hDc v h hh h' hh').continuousAt (isOpen_compl_singleton.mem_nhds (hz v))` as an intermediate fact. Conclude with `this.tendsto.comp (continuous_apply v).continuousAt.tendsto`.
-/
theorem Fz_continuousAt (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) (z : crystallineComparison.V f) (hz : Good z) :
    ContinuousAt (Fz Y κ D) z := by
  unfold Fz ContinuousAt
  refine tendsto_finsetSum _ fun h hh => tendsto_finsetSum _ fun h' hh' => ?_
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun v _ => ?_)
  have := (hDc v h hh h' hh').continuousAt (isOpen_compl_singleton.mem_nhds (hz v))
  exact this.tendsto.comp (continuous_apply v).continuousAt.tendsto

/- English proof (translation)
Introduce `z y hy`. Distinguish the cases in `hz : Good z`. Establish `hc : ContinuousAt (fun z => (Fz Y κ D z).re) z` using `Complex.continuous_re.continuousAt.comp (Fz_continuousAt Y κ D hDc z hz)`. Establish `h1 : ∀ᶠ z' in 𝓝 z, Good z'` using `isOpen_good.mem_nhds hz`. Establish `hy' : y < (Fz Y κ D z).re` using `by simpa [Nz, hz] using hy`.

Use `filter_upwards [h1, hc.eventually (lt_mem_nhds hy')] with z' hg hl`. Simplify `hl` using `[Nz, hg]`. Establish `hy' : y < 0` using `by simpa [Nz, hz] using hy`. Conclude with `Filter.Eventually.of_forall fun z' => hy'.trans_le (Nz_nonneg Y κ hκ D hD z')`.
-/
theorem Nz_lsc (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) : LowerSemicontinuous (Nz Y κ D) := by
  intro z y hy
  by_cases hz : Good z
  · have hc : ContinuousAt (fun z => (Fz Y κ D z).re) z :=
      Complex.continuous_re.continuousAt.comp (Fz_continuousAt Y κ D hDc z hz)
    have h1 : ∀ᶠ z' in 𝓝 z, Good z' := isOpen_good.mem_nhds hz
    have hy' : y < (Fz Y κ D z).re := by simpa [Nz, hz] using hy
    filter_upwards [h1, hc.eventually (lt_mem_nhds hy')] with z' hg hl
    simpa [Nz, hg] using hl
  · have hy' : y < 0 := by simpa [Nz, hz] using hy
    exact Filter.Eventually.of_forall fun z' => hy'.trans_le (Nz_nonneg Y κ hκ D hD z')

/- English proof (translation)
Establish `: ∀ v : Fin f, ∀ᵐ z : crystallineComparison.V f, z v ≠ 0`. Introduce `v`. Rewrite using `[ae_iff]`. Simplify using `only [ne_eq, not_not]`. Rewrite using `[MeasureTheory.volume_pi]`.

Conclude with `Measure.pi_hyperplane _ v 0`. Conclude with `(ae_all_iff.2 this).mono fun z hz => hz`.
-/
theorem ae_good : ∀ᵐ z : crystallineComparison.V f, Good z := by
  have : ∀ v : Fin f, ∀ᵐ z : crystallineComparison.V f, z v ≠ 0 := by
    intro v
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_hyperplane _ v 0
  exact (ae_all_iff.2 this).mono fun z hz => hz

/- English proof (translation)
Unfold `Fz`. Use `integrable_finsetSum _ fun h hh => integrable_finsetSum _ fun h' hh' => ?_` and prove the remaining obligations. Conclude with `(Integrable.fintype_prod (f := fun v => D v h h') fun v => hDi v h hh h' hh').const_mul _`.
-/
theorem Fz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Fz Y κ D) := by
  unfold Fz
  refine integrable_finsetSum _ fun h hh => integrable_finsetSum _ fun h' hh' => ?_
  exact (Integrable.fintype_prod (f := fun v => D v h h') fun v => hDi v h hh h' hh').const_mul _

/- English proof (translation)
Use `(Fz_integrable Y κ D hDi).re.congr ?_` and prove the remaining obligations. Use `filter_upwards [ae_good] with z hz`. Simplify using `[Nz, hz]`.
-/
theorem Nz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Nz Y κ D) := by
  refine (Fz_integrable Y κ D hDi).re.congr ?_
  filter_upwards [ae_good] with z hz
  simp [Nz, hz]

end

end Formalism.FourierDecayAlt.P.PBC
