import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.EInjective
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ContinuousQZ

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Introduce `a ha`. Establish `hga` using `hg a ha`. Establish `h1 : (g⁻¹ : GL (Fin n) k).val * g.val = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2 : g.val * (g⁻¹ : GL (Fin n) k).val = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Use `_ = (g⁻¹ : GL (Fin n) k).val * (a * g.val) * (g⁻¹ : GL (Fin n) k).val := by rw [hga]`. Use `_ = (g⁻¹ : GL (Fin n) k).val * a := by`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem inv_mem_Gz {g : GL (Fin n) k} (hg : g ∈ Gz Z) : g⁻¹ ∈ Gz Z := by
  intro a ha
  have hga := hg a ha
  have h1 : (g⁻¹ : GL (Fin n) k).val * g.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : g.val * (g⁻¹ : GL (Fin n) k).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc a * (g⁻¹ : GL (Fin n) k).val
      = (g⁻¹ : GL (Fin n) k).val * (g.val * a) * (g⁻¹ : GL (Fin n) k).val := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    _ = (g⁻¹ : GL (Fin n) k).val * (a * g.val) * (g⁻¹ : GL (Fin n) k).val := by rw [hga]
    _ = (g⁻¹ : GL (Fin n) k).val * a := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Introduce `a ha`. Establish `h1` using `hg a ha`. Establish `h2` using `inv_mem_Gz hg a ha`. Establish `h3` using `hw a ha`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_mem_Bz {g : GL (Fin n) k} (hg : g ∈ Gz Z) {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ Bz Z) :
    g.val * w * g⁻¹.val ∈ Bz Z := by
  intro a ha
  have h1 := hg a ha
  have h2 := inv_mem_Gz hg a ha
  have h3 := hw a ha
  calc a * (g.val * w * g⁻¹.val) = a * g.val * w * g⁻¹.val := by simp only [Matrix.mul_assoc]
    _ = g.val * (a * w) * g⁻¹.val := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = g.val * w * (a * g⁻¹.val) := by rw [h3]; simp only [Matrix.mul_assoc]
    _ = g.val * w * g⁻¹.val * a := by rw [h2]; simp only [Matrix.mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Unfold `B0 at hw ⊢`. Rewrite `hw`, the goal using `[Submodule.mem_inf]`. Take `⟨hw1, hw2⟩` from `hw`. Use `⟨conj_mem_Bz hg hw1, ?_⟩` and prove the remaining obligations. Rewrite `hw2`, the goal using `[LinearMap.mem_ker]`.

Establish `hq : qZ Z w = 0` using `hw2`. Use `show qZ Z (g.val * w * g⁻¹.val) = 0`. Rewrite using `[qZ_conj Z hg w]`. Conclude with `hq`.
-/
theorem conj_mem_nilpotent_cone {g : GL (Fin n) k} (hg : g ∈ Gz Z) {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) :
    g.val * w * g⁻¹.val ∈ B0 Z := by
  unfold B0 at hw ⊢
  rw [Submodule.mem_inf] at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨conj_mem_Bz hg hw1, ?_⟩
  rw [LinearMap.mem_ker] at hw2 ⊢
  have hq : qZ Z w = 0 := hw2
  show qZ Z (g.val * w * g⁻¹.val) = 0
  rw [qZ_conj Z hg w]
  exact hq

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem tr_conj (A P g g' : Matrix (Fin n) (Fin n) k) : trace (A * (g * P * g')) = trace (g' * A * g * P) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

variable (hZ : CR Z) (h : Hyp Z)
include hZ h

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Take `⟨u, rfl⟩` from `exists_E Z hw`. Establish `hP : Pr Z y = E Z ((G Z)⁻¹ *ᵥ D Z y)` using `rfl`. Rewrite using `[hP]`. Use `congr 1`. Establish `h1 : D Z (Pr Z y) = D Z y` using `D_Pr hZ h y`.

Rewrite `h1` using `[hP, D_E]`. Rewrite `hD` using `[D_E]`. Establish `hz : G Z *ᵥ (u - (G Z)⁻¹ *ᵥ D Z y) = 0`. Rewrite using `[Matrix.mulVec_sub, hD, h1, sub_self]`. Conclude with `sub_eq_zero.mp (G_inj hZ h hz)`.
-/
theorem Pr_unique {w y : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) (hD : D Z w = D Z y) : w = Pr Z y := by
  obtain ⟨u, rfl⟩ := exists_E Z hw
  have hP : Pr Z y = E Z ((G Z)⁻¹ *ᵥ D Z y) := rfl
  rw [hP]
  congr 1
  have h1 : D Z (Pr Z y) = D Z y := D_Pr hZ h y
  rw [hP, D_E] at h1
  rw [D_E] at hD
  have hz : G Z *ᵥ (u - (G Z)⁻¹ *ᵥ D Z y) = 0 := by
    rw [Matrix.mulVec_sub, hD, h1, sub_self]
  exact sub_eq_zero.mp (G_inj hZ h hz)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Take `⟨u, rfl⟩` from `exists_E Z hw`. Establish `h0` using `D_sub_Pr hZ h x`. Establish `hz : trace (E Z u * (x - Pr Z x)) = 0`. Rewrite using `[E_apply, Finset.sum_mul, Matrix.trace_sum]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mul, Matrix.trace_smul]`. Establish `hj : D Z (x - Pr Z x) j = 0` using `by rw [h0]; rfl`. Establish `hj' : trace (ee Z j * (x - Pr Z x)) = 0` using `hj`. Rewrite using `[hj', smul_zero]`. Rewrite `hz` using `[Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero]`.

Conclude with `hz`.
-/
theorem trace_nilpotent_cone_projection {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) (x : Matrix (Fin n) (Fin n) k) :
    trace (w * x) = trace (w * Pr Z x) := by
  obtain ⟨u, rfl⟩ := exists_E Z hw
  have h0 := D_sub_Pr hZ h x
  have hz : trace (E Z u * (x - Pr Z x)) = 0 := by
    rw [E_apply, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul]
    have hj : D Z (x - Pr Z x) j = 0 := by rw [h0]; rfl
    have hj' : trace (ee Z j * (x - Pr Z x)) = 0 := hj
    rw [hj', smul_zero]
  rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero] at hz
  exact hz

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `hPx : Pr Z x ∈ B0 Z` using `E_mem Z _`. Use `(Pr_unique hZ h (conj_mem_nilpotent_cone hg hPx) ?_).symm` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Use `show trace (ee Z j * (g.val * Pr Z x * g⁻¹.val)) = trace (ee Z j * (g.val * x * g⁻¹.val))`. Rewrite using `[tr_conj, tr_conj]`.

Establish `hee : ee Z j ∈ B0 Z` using `((bas Z) j).2`. Establish `hm` using `conj_mem_nilpotent_cone (inv_mem_Gz hg) hee`. Rewrite `hm` using `[inv_inv]`. Conclude with `(trace_nilpotent_cone_projection hZ h hm x).symm`.
-/
theorem Pr_conj {g : GL (Fin n) k} (hg : g ∈ Gz Z) (x : Matrix (Fin n) (Fin n) k) :
    Pr Z (g.val * x * g⁻¹.val) = g.val * Pr Z x * g⁻¹.val := by
  have hPx : Pr Z x ∈ B0 Z := E_mem Z _
  refine (Pr_unique hZ h (conj_mem_nilpotent_cone hg hPx) ?_).symm
  funext j
  show trace (ee Z j * (g.val * Pr Z x * g⁻¹.val)) = trace (ee Z j * (g.val * x * g⁻¹.val))
  rw [tr_conj, tr_conj]
  have hee : ee Z j ∈ B0 Z := ((bas Z) j).2
  have hm := conj_mem_nilpotent_cone (inv_mem_Gz hg) hee
  rw [inv_inv] at hm
  exact (trace_nilpotent_cone_projection hZ h hm x).symm

end PositivityTheory.RgUd.T.Nil.Four.Phi2
