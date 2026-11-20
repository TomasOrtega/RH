import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.SumNormMulVecSqLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.DetGramNonneg

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

/- English proof (translation)
Simplify using `[uMat]`.
-/
theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  simp [uMat]

/- English proof (translation)
Simplify using `[uMat]`.
-/
theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := by
  simp [uMat]

/- English proof (translation)
Establish `hA : ((x * (y, k)).1 v)⁻¹ = (y v)⁻¹ * (x.1 v)⁻¹`. Rewrite using `[← _root_.mul_inv_rev]`. Both sides reduce to the same expression. Unfold `coordV`. Rewrite using `[hA, uMat_mul, Matrix.mulVec_mulVec, mul_assoc]`.
-/
theorem coordV_mul (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I (x * (y, k)) v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
  have hA : ((x * (y, k)).1 v)⁻¹ = (y v)⁻¹ * (x.1 v)⁻¹ := by
    rw [← _root_.mul_inv_rev]
    rfl
  unfold coordV
  rw [hA, uMat_mul, Matrix.mulVec_mulVec, mul_assoc]

/- English proof (translation)
Rewrite using `[coordV_mul, Matrix.mulVec_mulVec, ← uMat_mul, mul_inv_cancel, uMat_one, Matrix.one_mulVec]`.
-/
theorem coordV_mul' (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I x v u = uMat (y v) *ᵥ coordV I (x * (y, k)) v u := by
  rw [coordV_mul, Matrix.mulVec_mulVec, ← uMat_mul, mul_inv_cancel, uMat_one, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[Filter.eventually_all]`. Introduce `v`. Establish `c1 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2`. Unfold `uMat`. Use `fun_prop`.

Establish `c2 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2`. Unfold `uMat`. Use `fun_prop`. Use `Filter.Eventually.and ?_ ?_` and prove the remaining obligations. Conclude with `c1.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)`.

Conclude with `c2.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)`.
-/
theorem eventually_uMat_near (I : AutInst) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 (1 : I.Ginf), ∀ v, ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 < δ := by
  rw [Filter.eventually_all]
  intro v
  have c1 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  have c2 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  refine Filter.Eventually.and ?_ ?_
  · exact c1.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)
  · exact c2.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)

/- English proof (translation)
Establish `ho` using `I.topf_open 1 le_rfl`. Use `ho.mem_nhds ?_` and prove the remaining obligations. Conclude with `⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, by simp⟩⟩`.
-/
theorem eventually_kg_one (I : AutInst) : ∀ᶠ k in 𝓝 (1 : I.Gf), k ∈ I.Kg 1 := by
  have ho := I.topf_open 1 le_rfl
  refine ho.mem_nhds ?_
  exact ⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, by simp⟩⟩

/- English proof (translation)
Introduce `I x r hr`. Use `set N := Fintype.card (InfinitePlace I.F)`. Use `set c : ℝ := r ^ (((N + 1 : ℕ) : ℝ)⁻¹) with hcdef`. Establish `hc1 : 1 < c` using `Real.one_lt_rpow hr (by positivity)`. Establish `hcN : c ^ N ≤ r`.

Combine the equalities or inequalities in the displayed calculation. Use `set ε : ℝ := (c - 1) / 2 with hεdef`. Establish `hε : 0 < ε` using `by rw [hεdef]; linarith`. Use `set δ : ℝ := ε ^ 2 / (1 + ε) with hδdef`. Establish `hδ : 0 < δ` using `by positivity`.

Establish `hbound : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 < δ → ∀ w : Fin I.n → ℂ, ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2`. Introduce `M hM w`. Use `(sum_norm_mulVec_sq_le M w hε).trans ?_` and prove the remaining obligations. Establish `hw : 0 ≤ ∑ i, ‖w i‖ ^ 2` using `by positivity`. Use `mul_le_mul_of_nonneg_right ?_ hw` and prove the remaining obligations.

Establish `h1 : (1 + 1 / ε) * ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 ≤ (1 + 1 / ε) * δ` using `mul_le_mul_of_nonneg_left hM.le (by positivity)`. Establish `h2 : (1 + 1 / ε) * δ = ε`. Rewrite using `[hδdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hW : ∀ᶠ z in 𝓝 (1 : I.GA), (∀ v, ∑ i, ∑ l, ‖(uMat (z.1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧ ∑ i, ∑ l, ‖(uMat (z.1 v) - 1) i l‖ ^ 2 < δ) ∧ z.2 ∈ I.Kg 1`. Establish `h` using `(eventually_uMat_near I hδ).prod_mk (eventually_kg_one I)`. Rewrite using `[show (1 : I.GA) = (1, 1) from rfl, nhds_prod_eq]`. Conclude with `h`.

Establish `hx : ∀ᶠ x' in 𝓝 x, (∀ v, ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧ ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v) - 1) i l‖ ^ 2 < δ) ∧ (x⁻¹ * x').2 ∈ I.Kg 1`. Establish `ht : Tendsto (fun x' : I.GA => x⁻¹ * x') (𝓝 x) (𝓝 1)`. Establish `h` using `(continuous_const_mul x⁻¹).tendsto x`. Rewrite `h` using `[inv_mul_cancel]`. Then use the resulting hypothesis. Conclude with `ht.eventually hW`.

Use `filter_upwards [hx] with x' hx'`. Take `⟨hy, hk⟩` from `hx'`. Use `set y := (x⁻¹ * x').1`. Use `set k := (x⁻¹ * x').2`. Establish `hxe : x * (y, k) = x'`.

Express the relevant statement in the definitionally equal form `x * ((x⁻¹ * x').1, (x⁻¹ * x').2) = x'`. Rewrite using `[Prod.mk.eta, mul_inv_cancel_left]`. Establish `hlat : latSet I x' = latSet I x`. Establish `h` using `h4 I x y k hk.1`. Rewrite `h` using `[hxe]`. Then use the resulting hypothesis.

Establish `hc1' : ∀ v u, coordV I x' v u = uMat (y v)⁻¹ *ᵥ coordV I x v u`. Introduce `v u`. Establish `h` using `coordV_mul I x y k v u`. Rewrite `h` using `[hxe]`. Then use the resulting hypothesis. Establish `hc2' : ∀ v u, coordV I x v u = uMat (y v) *ᵥ coordV I x' v u`.

Introduce `v u`. Establish `h` using `coordV_mul' I x y k v u`. Rewrite `h` using `[hxe]`. Then use the resulting hypothesis. Use `⟨fun s => ⟨subOfEq I hlat s, ?_⟩, fun s' => ⟨subOfEq I hlat.symm s', ?_⟩⟩` and prove the remaining obligations. Conclude with `(size_subOfEq_le I h5 hlat _ hc1' hc1.le (fun v w => hbound _ (hy v).1 w) s).trans (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s))`.

Conclude with `(size_subOfEq_le I h5 hlat.symm _ hc2' hc1.le (fun v w => hbound _ (hy v).2 w) s').trans (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s'))`.
-/
theorem sizes_locally_comparable (h4 : LatticeRightInvariant) (h5 : GramDistortionBound) : SizesLocallyComparable := by
  intro I x r hr
  set N := Fintype.card (InfinitePlace I.F)
  set c : ℝ := r ^ (((N + 1 : ℕ) : ℝ)⁻¹) with hcdef
  have hc1 : 1 < c := Real.one_lt_rpow hr (by positivity)
  have hcN : c ^ N ≤ r := by
    calc c ^ N ≤ c ^ (N + 1) := pow_le_pow_right₀ hc1.le (Nat.le_succ N)
      _ = r := Real.rpow_inv_natCast_pow (by linarith) (Nat.succ_ne_zero N)
  set ε : ℝ := (c - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set δ : ℝ := ε ^ 2 / (1 + ε) with hδdef
  have hδ : 0 < δ := by positivity
  have hbound : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 < δ →
      ∀ w : Fin I.n → ℂ, ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2 := by
    intro M hM w
    refine (sum_norm_mulVec_sq_le M w hε).trans ?_
    have hw : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hw
    have h1 : (1 + 1 / ε) * ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 ≤ (1 + 1 / ε) * δ :=
      mul_le_mul_of_nonneg_left hM.le (by positivity)
    have h2 : (1 + 1 / ε) * δ = ε := by
      rw [hδdef]
      field_simp
      ring
    linarith
  have hW : ∀ᶠ z in 𝓝 (1 : I.GA), (∀ v, ∑ i, ∑ l, ‖(uMat (z.1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (z.1 v) - 1) i l‖ ^ 2 < δ) ∧ z.2 ∈ I.Kg 1 := by
    have h := (eventually_uMat_near I hδ).prod_mk (eventually_kg_one I)
    rw [show (1 : I.GA) = (1, 1) from rfl, nhds_prod_eq]
    exact h
  have hx : ∀ᶠ x' in 𝓝 x, (∀ v, ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v) - 1) i l‖ ^ 2 < δ) ∧ (x⁻¹ * x').2 ∈ I.Kg 1 := by
    have ht : Tendsto (fun x' : I.GA => x⁻¹ * x') (𝓝 x) (𝓝 1) := by
      have h := (continuous_const_mul x⁻¹).tendsto x
      rwa [inv_mul_cancel] at h
    exact ht.eventually hW
  filter_upwards [hx] with x' hx'
  obtain ⟨hy, hk⟩ := hx'
  set y := (x⁻¹ * x').1
  set k := (x⁻¹ * x').2
  have hxe : x * (y, k) = x' := by
    change x * ((x⁻¹ * x').1, (x⁻¹ * x').2) = x'
    rw [Prod.mk.eta, mul_inv_cancel_left]
  have hlat : latSet I x' = latSet I x := by
    have h := h4 I x y k hk.1
    rwa [hxe] at h
  have hc1' : ∀ v u, coordV I x' v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
    intro v u
    have h := coordV_mul I x y k v u
    rwa [hxe] at h
  have hc2' : ∀ v u, coordV I x v u = uMat (y v) *ᵥ coordV I x' v u := by
    intro v u
    have h := coordV_mul' I x y k v u
    rwa [hxe] at h
  refine ⟨fun s => ⟨subOfEq I hlat s, ?_⟩, fun s' => ⟨subOfEq I hlat.symm s', ?_⟩⟩
  · exact (size_subOfEq_le I h5 hlat _ hc1' hc1.le (fun v w => hbound _ (hy v).1 w) s).trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s))
  · exact (size_subOfEq_le I h5 hlat.symm _ hc2' hc1.le (fun v w => hbound _ (hy v).2 w) s').trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s'))

end Formalism.L2.SG.Pf.Tau
