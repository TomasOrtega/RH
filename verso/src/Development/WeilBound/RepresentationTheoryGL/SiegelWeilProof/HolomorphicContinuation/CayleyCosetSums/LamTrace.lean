import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RhoPSmul

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

include hι hK hψ hψc ha hb in
/- English proof (translation)
Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ` to `{ toFun := fun Y => star (abelian₂ μ ι m e ψ a b z Y) map_add' := fun Y W => by simp [Lam_add μ ι hι hK m e hψ hψc ha hb] map_smul' := fun c Y => by simp [Lam_smul, mul_comm] }`. Establish `h` using `inv_trace L (fun U Y hU hY => by`. Simplify using `only [L, LinearMap.coe_mk, AddHom.coe_mk, Lam_inv μ ι hK m e ha hb z hU hY]) X`. Simplify using `only [L, LinearMap.coe_mk, AddHom.coe_mk] at h`. Establish `h'` using `congrArg star h`.

Rewrite `h'` using `[star_star]`. Rewrite using `[h']`. Simplify using `[star_div₀, mul_comm]`.
-/
theorem Lam_trace (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = abelian₂ μ ι m e ψ a b z 1 / n * star X.trace := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Y => star (abelian₂ μ ι m e ψ a b z Y)
      map_add' := fun Y W => by simp [Lam_add μ ι hι hK m e hψ hψc ha hb]
      map_smul' := fun c Y => by simp [Lam_smul, mul_comm] }
  have h := inv_trace L (fun U Y hU hY => by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Lam_inv μ ι hK m e ha hb z hU hY]) X
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at h
  have h' := congrArg star h
  rw [star_star] at h'
  rw [h']
  simp [star_div₀, mul_comm]

include hι hK hψ hψc ha hb in
/- English proof (translation)
Establish `hιK : ∀ k, InK (ι k)` using `ιK ι hK`. Establish `hιG : ∀ k, InG (ι k)` using `fun k => (hιK k).1`. Establish `hb21 : Continuous fun x : M2 n => toBlocks₂₁ x` using `continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))`. Establish `hb22 : Continuous fun x : M2 n => toBlocks₂₂ x` using `continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))`. Establish `hu1 : Continuous fun x : M2 n => u1 x` using `by show Continuous fun x : M2 n => Complex.I • toBlocks₂₁ x + toBlocks₂₂ x`.

Conclude with `(hb21.const_smul Complex.I).add hb22`. Establish `hu2 : Continuous fun x : M2 n => u2 x` using `by show Continuous fun x : M2 n => -(Complex.I • toBlocks₂₁ x) + toBlocks₂₂ x`. Conclude with `(hb21.const_smul Complex.I).neg.add hb22`. Establish `hR : (rhoP ⇑ι m e 1) = fun k => star ((det (ι k) ^ e * (u1 (ι k)).det ^ (-(m : ℤ))) * ((u2 (ι k))ᴴ * u1 (ι k)).trace)`. Use function extensionality and compare the values at `k`.

Rewrite using `[rhoP, Matrix.mul_one, Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary (hιK k))]`. Simplify using `[fz]`. Establish `hRc : Continuous (rhoP ⇑ι m e 1)`. Rewrite using `[hR]`. Use `Continuous.star (Continuous.mul (Continuous.mul ?_ ?_) ?_)` and prove the remaining obligations.

Conclude with `hι.matrix_det.zpow₀ e fun k => Or.inl (LoweringDerivative.isUnit_det_of_inG (hιG k)).ne_zero`. Conclude with `(hu1.comp hι).matrix_det.zpow₀ _ fun k => Or.inl (det_first_block_ne_zero_group (hιG k))`. Conclude with `(((hu2.comp hι).matrix_conjTranspose).matrix_mul (hu1.comp hι)).matrix_trace`. Establish `hH : Continuous fun p : Kg × ℂ => Hf m e ψ a b p.2 (ι p.1)`. Establish `h1` using `continuous_Hf m e hψ hψc ha hb`.

Use `h1.comp (f := fun p : Kg × ℂ => ((⟨ι p.1, hιG p.1⟩ : Gs n), p.2)) ?_` and prove the remaining obligations. Use `Continuous.prodMk ?_ continuous_snd` and prove the remaining obligations. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `hι.comp continuous_fst`. Use `set G : Kg → ℂ → ℂ := fun k w => rhoP ⇑ι m e 1 k * Hf m e ψ a b w (ι k) with hGdef`.

Establish `hG : Continuous (Function.uncurry G)` using `(hRc.comp continuous_fst).mul hH`. Establish `hGd : ∀ k, Differentiable ℂ (G k)` using `fun k => (differentiable_Hf m e hψ hψc ha hb (hιG k)).const_mul _`. Establish `hLam : (fun z => abelian₂ μ ι m e ψ a b z 1) = fun z => ∫ k, G k z ∂μ`. Use function extensionality and compare the values at `z`. Rewrite using `[Lam_eq]`.

Rewrite using `[hLam]`. Introduce `z0`. Take `⟨C, hC⟩` from `(isCompact_univ.prod (isCompact_closedBall z0 2)).exists_bound_of_continuousOn hG.continuousOn`. Establish `hbd : ∀ k, ∀ z ∈ Metric.ball z0 1, ‖deriv (G k) z‖ ≤ C`. Introduce `k z hz`.

Use `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := C) one_pos (hGd k).diffContOnCl (fun w hw => by` as an intermediate fact. Apply `hC (k, w)` to reduce the goal to its premises. Use `⟨Set.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall]`. Rewrite `hw` using `[Metric.mem_sphere]`.

Rewrite `hz` using `[Metric.mem_ball]`. Combine the linear relations using `[dist_triangle w z z0])`. Simplify using `using this`. Establish `hmeas : Measurable fun k => deriv (G k) z0`. Establish `hm` using `measurable_deriv_with_param (𝕜 := ℂ) (F := ℂ) (f := G) hG`.

Conclude with `hm.comp (f := fun k : Kg => (k, z0)) (measurable_id.prodMk measurable_const)`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z k => G k z) (F' := fun z k => deriv (G k) z) (x₀ := z0) (bound := fun _ => C) (Metric.ball_mem_nhds z0 one_pos) (Filter.Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).aestrongly …`. Conclude with `key.2.differentiableAt`.
-/
theorem Lam_diff : Differentiable ℂ fun z => abelian₂ μ ι m e ψ a b z 1 := by
  have hιK : ∀ k, InK (ι k) := ιK ι hK
  have hιG : ∀ k, InG (ι k) := fun k => (hιK k).1
  have hb21 : Continuous fun x : M2 n => toBlocks₂₁ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have hb22 : Continuous fun x : M2 n => toBlocks₂₂ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  have hu1 : Continuous fun x : M2 n => u1 x := by
    show Continuous fun x : M2 n => Complex.I • toBlocks₂₁ x + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).add hb22
  have hu2 : Continuous fun x : M2 n => u2 x := by
    show Continuous fun x : M2 n => -(Complex.I • toBlocks₂₁ x) + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).neg.add hb22
  have hR : (rhoP ⇑ι m e 1) = fun k =>
      star ((det (ι k) ^ e * (u1 (ι k)).det ^ (-(m : ℤ))) * ((u2 (ι k))ᴴ * u1 (ι k)).trace) := by
    funext k
    rw [rhoP, Matrix.mul_one, Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary (hιK k))]
    simp [fz]
  have hRc : Continuous (rhoP ⇑ι m e 1) := by
    rw [hR]
    refine Continuous.star (Continuous.mul (Continuous.mul ?_ ?_) ?_)
    · exact hι.matrix_det.zpow₀ e fun k => Or.inl (LoweringDerivative.isUnit_det_of_inG (hιG k)).ne_zero
    · exact (hu1.comp hι).matrix_det.zpow₀ _ fun k => Or.inl (det_first_block_ne_zero_group (hιG k))
    · exact (((hu2.comp hι).matrix_conjTranspose).matrix_mul (hu1.comp hι)).matrix_trace
  have hH : Continuous fun p : Kg × ℂ => Hf m e ψ a b p.2 (ι p.1) := by
    have h1 := continuous_Hf m e hψ hψc ha hb
    refine h1.comp (f := fun p : Kg × ℂ => ((⟨ι p.1, hιG p.1⟩ : Gs n), p.2)) ?_
    refine Continuous.prodMk ?_ continuous_snd
    refine Continuous.subtype_mk ?_ _
    exact hι.comp continuous_fst
  set G : Kg → ℂ → ℂ := fun k w => rhoP ⇑ι m e 1 k * Hf m e ψ a b w (ι k) with hGdef
  have hG : Continuous (Function.uncurry G) := (hRc.comp continuous_fst).mul hH
  have hGd : ∀ k, Differentiable ℂ (G k) := fun k =>
    (differentiable_Hf m e hψ hψc ha hb (hιG k)).const_mul _
  have hLam : (fun z => abelian₂ μ ι m e ψ a b z 1) = fun z => ∫ k, G k z ∂μ := by
    funext z
    rw [Lam_eq]
  rw [hLam]
  intro z0
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall z0 2)).exists_bound_of_continuousOn
    hG.continuousOn
  have hbd : ∀ k, ∀ z ∈ Metric.ball z0 1, ‖deriv (G k) z‖ ≤ C := by
    intro k z hz
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := C) one_pos
      (hGd k).diffContOnCl (fun w hw => by
        apply hC (k, w)
        refine ⟨Set.mem_univ _, ?_⟩
        rw [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at hw
        rw [Metric.mem_ball] at hz
        linarith [dist_triangle w z z0])
    simpa using this
  have hmeas : Measurable fun k => deriv (G k) z0 :=
    by
    have hm := measurable_deriv_with_param (𝕜 := ℂ) (F := ℂ) (f := G) hG
    exact hm.comp (f := fun k : Kg => (k, z0)) (measurable_id.prodMk measurable_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z k => G k z)
    (F' := fun z k => deriv (G k) z) (x₀ := z0) (bound := fun _ => C)
    (Metric.ball_mem_nhds z0 one_pos)
    (Filter.Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z0 1)
    hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k z hz => hbd k z hz)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k z _ => ((hGd k) z).hasDerivAt)
  exact key.2.differentiableAt

end Main

/- English proof (translation)
Introduce `n m e Kg _ _ _ _ _ _ μ _ ι hι hK ψ a b hψ hψc ha hb`. Use `⟨fun z => -(abelian₂ μ ι m e ψ a b z 1 / n), ?_, ?_⟩` and prove the remaining obligations. Conclude with `((Lam_diff μ ι hι hK m e hψ hψc ha hb).div_const _).neg`. Introduce `Y z x hx`. Take `⟨p, k, hp, hk, hpk⟩` from `AbsSt.iwa n (AbsSt.mkGR x hx)`.

Establish `hxe : x = mR p * mR k`. Establish `h` using `congrArg mR hpk`. Rewrite `h` using `[AbsSt.mR_mkGR]`. Rewrite using `[h]`. Both sides reduce to the same expression.

Take `⟨k1, hk1⟩` from `(hK (mR k)).mp hk`. Establish `hpG : InG (mR p)` using `p.2`. Establish `hk1K : InK (ι k1)` using `hk1 ▸ hk`. Rewrite using `[hxe, ← hk1, tOp_formula μ ι hK m e ψ ha hb hpG hp k1 Y z]`. Express the relevant statement in the definitionally equal form `lam m e z (mR p) * fz m e 0 (ι k1) * abelian₂ μ ι m e ψ a b z (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) = _`.

Rewrite using `[Lam_trace μ ι hι hK m e hψ hψc ha hb, eQ, fz_up hpG hp hk1K.1, Om_up hpG hp hk1K.1, fz_K m e z hk1K, Om_K hk1K, Matrix.inv_eq_left_inv (first_cayley_block_compact_unitary hk1K), Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk1K)]`. Establish `htr : star (u2 (ι k1) * Y * (u1 (ι k1))ᴴ).trace = ((u2 (ι k1))ᴴ * u1 (ι k1) * Yᴴ).trace`. Rewrite using `[← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]`. Rewrite using `[htr]`. Simplify using `only [Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lt2 : MultiplicityOneTestOperators := by
  intro n m e Kg _ _ _ _ _ _ μ _ ι hι hK ψ a b hψ hψc ha hb
  refine ⟨fun z => -(abelian₂ μ ι m e ψ a b z 1 / n), ?_, ?_⟩
  · exact ((Lam_diff μ ι hι hK m e hψ hψc ha hb).div_const _).neg
  · intro Y z x hx
    obtain ⟨p, k, hp, hk, hpk⟩ := AbsSt.iwa n (AbsSt.mkGR x hx)
    have hxe : x = mR p * mR k := by
      have h := congrArg mR hpk
      rw [AbsSt.mR_mkGR] at h
      rw [h]
      rfl
    obtain ⟨k1, hk1⟩ := (hK (mR k)).mp hk
    have hpG : InG (mR p) := p.2
    have hk1K : InK (ι k1) := hk1 ▸ hk
    rw [hxe, ← hk1, tOp_formula μ ι hK m e ψ ha hb hpG hp k1 Y z]
    change lam m e z (mR p) * fz m e 0 (ι k1) *
      abelian₂ μ ι m e ψ a b z (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) = _
    rw [Lam_trace μ ι hι hK m e hψ hψc ha hb, eQ, fz_up hpG hp hk1K.1, Om_up hpG hp hk1K.1,
      fz_K m e z hk1K, Om_K hk1K, Matrix.inv_eq_left_inv (first_cayley_block_compact_unitary hk1K),
      Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk1K)]
    have htr : star (u2 (ι k1) * Y * (u1 (ι k1))ᴴ).trace = ((u2 (ι k1))ᴴ * u1 (ι k1) * Yᴴ).trace := by
      rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rw [htr]
    simp only [Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
      ← Matrix.mul_assoc]
    ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

namespace PositivityTheory.Rg.Sw.HSt

/- English proof (translation)
The claim follows from `CompactCayleyBlocks.lt2`.
-/
theorem lt2 : MultiplicityOneTestOperators := CompactCayleyBlocks.lt2

end PositivityTheory.Rg.Sw.HSt
