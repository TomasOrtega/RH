import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

/- English proof (translation)
Simplify using `only [ev_eq, map_sum]`.
-/
theorem ev_finset_sum {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) {ι : Type} (s : Finset ι) (z : ι → Chn G m) :
    ev ρ F y (∑ i ∈ s, z i) = ∑ i ∈ s, ev ρ F y (z i) := by
  simp only [ev_eq, map_sum]

/- English proof (translation)
Introduce `g y`. Simplify using `only [dC]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hE g (fun j => y (i.succAbove j))]`.
-/
theorem inv_dC {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (E : (Fin (m + 1) → Y) → ℝ) (hE : Inv ρ E) : Inv ρ (dC E) := by
  intro g y
  simp only [dC]
  exact Finset.sum_congr rfl fun i _ => by rw [hE g (fun j => y (i.succAbove j))]

/- English proof (translation)
Introduce `G H Y _ _ _ ρ m E hE y z`. Use `Finsupp.induction_linear z ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[ev_zero]`. Introduce `a b ha hb`. Rewrite using `[ev_add, map_add, ev_add, ha, hb]`.

Introduce `g a`. Establish `hbd : bd G m (Finsupp.single g a) = a • bd G m (Finsupp.single g 1)`. Rewrite using `[← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hbd, ev_smul, ev_single]`. Use `congr 1`.

Simplify using `only [bd, Finsupp.linearCombination_single, one_smul]`. Rewrite using `[ev_add, ev_single, one_mul, ev_finset_sum]`. Simplify using `only [ev_smul, ev_single, one_mul]`. Simplify using `only [dC]`. Rewrite using `[Fin.sum_univ_succ]`.

Use `congr 1`. Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]`. Establish `: (fun j : Fin (m + 1) => ρ (Fin.partialProd g j.succ) • y) = fun j => ρ (g 0) • (ρ (Fin.partialProd (fun i : Fin m => g i.succ) j) • y)`. Use function extensionality and compare the values at `j`. Rewrite using `[Fin.partialProd_succ', map_mul, mul_smul]`.

Both sides reduce to the same expression. Rewrite using `[this, hE (g 0)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.partialProd_contractNth]`. Simplify using `[Fin.val_succ]`.
-/
theorem pEvDC : PEvDC := by
  intro G H Y _ _ _ ρ m E hE y z
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp [ev_zero]
  · intro a b ha hb
    rw [ev_add, map_add, ev_add, ha, hb]
  · intro g a
    have hbd : bd G m (Finsupp.single g a) = a • bd G m (Finsupp.single g 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hbd, ev_smul, ev_single]
    congr 1
    simp only [bd, Finsupp.linearCombination_single, one_smul]
    rw [ev_add, ev_single, one_mul, ev_finset_sum]
    simp only [ev_smul, ev_single, one_mul]
    simp only [dC]
    rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      have : (fun j : Fin (m + 1) => ρ (Fin.partialProd g j.succ) • y) =
          fun j => ρ (g 0) • (ρ (Fin.partialProd (fun i : Fin m => g i.succ) j) • y) := by
        funext j
        rw [Fin.partialProd_succ', map_mul, mul_smul]
        rfl
      rw [this, hE (g 0)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.partialProd_contractNth]
      simp [Fin.val_succ]

/- English proof (translation)
Introduce `G _ m F hF hz`. Set `φ : Chn G (m + 1) →ₗ[ℝ] ℝ` to `Finsupp.linearCombination ℝ (fun g : Fin (m + 1) → G => F fun j => Fin.partialProd g j)`. Establish `hφ : ∀ z, φ z = ev (MonoidHom.id G) F 1 z` using `fun z => by`. Rewrite using `[ev_eq]`. Simplify using `[φ]`.

Establish `hker : LinearMap.ker (bd G m) ≤ LinearMap.ker φ` using `fun z hz' => by`. Rewrite `hz'`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hφ]`. Conclude with `hz z hz'`. Set `ψ₀ : LinearMap.range (bd G m) →ₗ[ℝ] ℝ` to `(LinearMap.ker (bd G m)).liftQ φ hker ∘ₗ (bd G m).quotKerEquivRange.symm.toLinearMap`.

Take `⟨ψ, hψ⟩` from `LinearMap.exists_extend ψ₀`. Establish `hψbd : ∀ z, ψ (bd G m z) = φ z` using `fun z => by`. Establish `h1` using `LinearMap.congr_fun hψ ⟨bd G m z, LinearMap.mem_range_self _ z⟩`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1`. Rewrite using `[h1]`.

Simplify using `[ψ₀, LinearMap.quotKerEquivRange_symm_apply_image]`. Set `E : (Fin (m + 1) → G) → ℝ` to `fun y => ψ (Finsupp.single (fun j : Fin m => (y j.castSucc)⁻¹ * y j.succ) 1)`. Establish `hEinv : Inv (MonoidHom.id G) E`. Introduce `g y`. Simplify using `only [E, MonoidHom.id_apply, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.

Establish `hevE : ∀ w : Chn G m, ev (MonoidHom.id G) E 1 w = ψ w`. Introduce `w`. Use `Finsupp.induction_linear w ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[ev_zero]`. Introduce `a b ha hb`.

Rewrite using `[ev_add, ha, hb, map_add]`. Introduce `g a`. Rewrite using `[ev_single]`. Simplify using `only [E, MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.partialProd_right_inv]`. Rewrite using `[← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]`.

Use `⟨E, hEinv, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Use `set g' : Fin (m + 1) → G := fun i => (y i.castSucc)⁻¹ * y i.succ`. Establish `hy : y = fun j => y 0 * Fin.partialProd g' j`. Use `Fin.partialProd_left_inv y` as an intermediate fact.

Use function extensionality and compare the values at `j`. Conclude with `(congrFun this j).symm`. Establish `h1 : dC E y = dC E (fun j => Fin.partialProd g' j)` using `by conv_lhs => rw [hy]`. Conclude with `inv_dC (MonoidHom.id G) E hEinv (y 0) _`. Establish `h2 : F y = F (fun j => Fin.partialProd g' j)` using `by conv_lhs => rw [hy]`.

Conclude with `hF (y 0) _`. Rewrite using `[h1, h2]`. Establish `h3` using `pEvDC G G G (MonoidHom.id G) m E hEinv 1 (Finsupp.single g' 1)`. Rewrite `h3` using `[ev_single, hevE, hψbd, hφ, ev_single]`. Simplify using `using h3`.
-/
theorem pCob : PCob := by
  intro G _ m F hF hz
  let φ : Chn G (m + 1) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun g : Fin (m + 1) → G => F fun j => Fin.partialProd g j)
  have hφ : ∀ z, φ z = ev (MonoidHom.id G) F 1 z := fun z => by
    rw [ev_eq]; simp [φ]
  have hker : LinearMap.ker (bd G m) ≤ LinearMap.ker φ := fun z hz' => by
    rw [LinearMap.mem_ker] at hz' ⊢; rw [hφ]; exact hz z hz'
  let ψ₀ : LinearMap.range (bd G m) →ₗ[ℝ] ℝ :=
    (LinearMap.ker (bd G m)).liftQ φ hker ∘ₗ (bd G m).quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  have hψbd : ∀ z, ψ (bd G m z) = φ z := fun z => by
    have h1 := LinearMap.congr_fun hψ ⟨bd G m z, LinearMap.mem_range_self _ z⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ψ₀, LinearMap.quotKerEquivRange_symm_apply_image]
  let E : (Fin (m + 1) → G) → ℝ := fun y =>
    ψ (Finsupp.single (fun j : Fin m => (y j.castSucc)⁻¹ * y j.succ) 1)
  have hEinv : Inv (MonoidHom.id G) E := by
    intro g y
    simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hevE : ∀ w : Chn G m, ev (MonoidHom.id G) E 1 w = ψ w := by
    intro w
    refine Finsupp.induction_linear w ?_ ?_ ?_
    · simp [ev_zero]
    · intro a b ha hb; rw [ev_add, ha, hb, map_add]
    · intro g a
      rw [ev_single]
      simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.partialProd_right_inv]
      rw [← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨E, hEinv, ?_⟩
  funext y
  set g' : Fin (m + 1) → G := fun i => (y i.castSucc)⁻¹ * y i.succ
  have hy : y = fun j => y 0 * Fin.partialProd g' j := by
    have := Fin.partialProd_left_inv y
    funext j
    exact (congrFun this j).symm
  have h1 : dC E y = dC E (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact inv_dC (MonoidHom.id G) E hEinv (y 0) _
  have h2 : F y = F (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact hF (y 0) _
  rw [h1, h2]
  have h3 := pEvDC G G G (MonoidHom.id G) m E hEinv 1 (Finsupp.single g' 1)
  rw [ev_single, hevE, hψbd, hφ, ev_single] at h3
  simpa using h3

end PositivityTheory.KB.AffineStabilizerVanishing

end
