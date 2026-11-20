import Mathlib

noncomputable section

open NumberField IsDedekindDomain TensorProduct Topology

namespace GlobalTheory

/- English proof (translation)
Use `set K := w.adicCompletion E with hK`. Use `set B := Algebra.TensorProduct.basis K b with hB`. Use `set Φ : (ι → K) → K ⊗[E] E' := fun t => ∑ i, t i • B i with hΦ`. Establish `hrepr : ∀ t, B.repr (Φ t) = Finsupp.equivFunOnFinite.symm t`. Introduce `t`.

Use extensionality with `i`. Simplify using `[hΦ, map_sum, Finsupp.smul_apply, Finsupp.single_apply]`. Establish `hM : Continuous fun t => Algebra.leftMulMatrix B (Φ t)`. Establish `h : (fun t => Algebra.leftMulMatrix B (Φ t)) = fun t => ∑ i, t i • Algebra.leftMulMatrix B (B i)`. Use function extensionality and compare the values at `t`.

Simplify using `only [hΦ, map_sum, map_smul]`. Rewrite using `[h]`. Conclude with `continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const`. Use `set f1 : (ι → K) → ι → K := fun t => B.repr (Φ t * Φ t - Φ t) with hf1`. Use `set f2 : (ι → K) → K := fun t => ψ (Φ t) - 1 with hf2`.

Use `set f3 : (ι → K) → K := fun t => Algebra.norm K (p + q * (Φ t - e)) - Algebra.norm K p with hf3`. Establish `hf1c : Continuous f1`. Establish `h : f1 = fun t => Matrix.mulVec (Algebra.leftMulMatrix B (Φ t)) t - t`. Use function extensionality and compare the values at `t`. Use function extensionality and compare the values at `i`.

Simplify using `only [hf1, map_sub, Finsupp.coe_sub, Pi.sub_apply]`. Rewrite using `[← Algebra.leftMulMatrix_mulVec_repr, hrepr]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `(hM.matrix_mulVec continuous_id).sub continuous_id`.

Establish `hf2c : Continuous f2`. Establish `hl : Continuous fun t => ψ (Φ t)`. Establish `h` using `LinearMap.continuous_on_pi (ψ.toLinearMap ∘ₗ B.equivFun.symm.toLinearMap)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`.

Simplify using `[hΦ, Module.Basis.equivFun_symm_apply]`. Conclude with `hl.sub continuous_const`. Establish `hf3c : Continuous f3`. Establish `h : (fun t => Algebra.norm K (p + q * (Φ t - e))) = fun t => (Algebra.leftMulMatrix B (p - q * e) + Algebra.leftMulMatrix B q * Algebra.leftMulMatrix B (Φ t)).det`. Use function extensionality and compare the values at `t`.

Rewrite using `[Algebra.norm_eq_matrix_det B, ← map_mul, ← map_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `: Continuous fun t => Algebra.norm K (p + q * (Φ t - e))`. Rewrite using `[h]`.

Conclude with `(continuous_const.add (continuous_const.matrix_mul hM)).matrix_det`. Conclude with `this.sub continuous_const`. Use `set t₀ : ι → K := fun i => B.repr e i with ht₀`. Establish `hΦ₀ : Φ t₀ = e` using `by simp only [hΦ, ht₀]; exact B.sum_repr e`. Establish `hball' : ∀ x₀ : K, Valued.v x₀ ≠ 0 → {z : K | Valued.v z ≤ Valued.v x₀} ∈ 𝓝 (0 : K)`.

Introduce `x₀ hx₀`. Establish `hl : {y : K | Valued.v y = Valued.v x₀} ∈ 𝓝 x₀` using `Valued.locally_const hx₀`. Establish `hc : ContinuousAt (fun z : K => z + x₀) 0` using `(continuous_id.add continuous_const).continuousAt`. Establish `h'` using `hc.preimage_mem_nhds (by simpa using hl)`. Use `filter_upwards [h'] with z hz`.

Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢`. Combine the equalities or inequalities in the displayed calculation. Establish `hva : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x` using `fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x`. Take `⟨π, hπ⟩` from `w.valuation_exists_uniformizer E`. Establish `hx₀ : Valued.v ((algebraMap E K π) ^ n) = WithZero.exp (-(n : ℤ))`.

Rewrite using `[map_pow, hva, hπ, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hball : ∀ γ, γ = WithZero.exp (-(n : ℤ)) ∨ γ = 1 → {z : K | Valued.v z ≤ γ} ∈ 𝓝 (0 : K)`. Introduce and unpack `γ (rfl | rfl)`.

Rewrite using `[← hx₀]`. Conclude with `hball' _ (by rw [hx₀]; exact WithZero.exp_ne_zero)`. Use `hball' 1 (by simp)` as an intermediate fact. Simplify using `using this`. Establish `h1 : ∀ᶠ t in 𝓝 t₀, ∀ i, Valued.v (f1 t i) ≤ 1`.

Rewrite using `[Filter.eventually_all]`. Introduce `i`. Establish `hc : ContinuousAt (fun t => f1 t i) t₀` using `((continuous_apply i).comp hf1c).continuousAt`. Establish `h0 : f1 t₀ i = 0` using `by simp [hf1, hΦ₀, he]`. Conclude with `hc.preimage_mem_nhds (by rw [h0]; exact hball 1 (Or.inr rfl))`.

Establish `h2 : ∀ᶠ t in 𝓝 t₀, Valued.v (f2 t) ≤ WithZero.exp (-(n : ℤ))`. Establish `h0 : f2 t₀ = 0` using `by simp [hf2, hΦ₀, hψ]`. Conclude with `hf2c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))`. Establish `h3 : ∀ᶠ t in 𝓝 t₀, Valued.v (f3 t) ≤ WithZero.exp (-(n : ℤ))`. Establish `h0 : f3 t₀ = 0` using `by simp [hf3, hΦ₀]`.

Conclude with `hf3c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))`. Establish `hd : DenseRange (Pi.map fun _ : ι => (algebraMap E K : E → K))` using `DenseRange.piMap fun _ => w.denseRange_algebraMap E`. Take `⟨c, hc1, hc2, hc3⟩` from `hd.mem_nhds (h1.and (h2.and h3))`. Use `set ε : E' := ∑ i, c i • b i with hε`. Establish `hΦc : Φ (Pi.map (fun _ : ι => (algebraMap E K : E → K)) c) = (1 : K) ⊗ₜ ε`.

Simplify using `only [hΦ, Pi.map_apply, hε]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hB, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, algebraMap_smul]`. Use `⟨ε, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Establish `h` using `hc1 i`. Simplify using `only [hf1, hΦc] at h`. Rewrite `h` using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub, hB, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [one_smul, Finsupp.mapRange_apply] at h`.

Rewrite using `[← hva]`. Conclude with `h`. Establish `h` using `hc2`. Simplify `h` using `only [hf2, hΦc]`. Establish `h` using `hc3`.

Simplify `h` using `only [hf3, hΦc]`.
-/
theorem exists_global_near_idempotent (E E' : Type) [Field E] [NumberField E] [Field E']
    [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E)
    (e : w.adicCompletion E ⊗[E] E') (he : e * e = e) (hψ : ψ e = 1)
    (p q : w.adicCompletion E ⊗[E] E') (n : ℕ) :
    ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧
      Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) -
        Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  set K := w.adicCompletion E with hK
  set B := Algebra.TensorProduct.basis K b with hB
  set Φ : (ι → K) → K ⊗[E] E' := fun t => ∑ i, t i • B i with hΦ
  have hrepr : ∀ t, B.repr (Φ t) = Finsupp.equivFunOnFinite.symm t := by
    intro t
    ext i
    simp [hΦ, map_sum, Finsupp.smul_apply, Finsupp.single_apply]
  have hM : Continuous fun t => Algebra.leftMulMatrix B (Φ t) := by
    have h : (fun t => Algebra.leftMulMatrix B (Φ t)) =
        fun t => ∑ i, t i • Algebra.leftMulMatrix B (B i) := by
      funext t
      simp only [hΦ, map_sum, map_smul]
    rw [h]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

  set f1 : (ι → K) → ι → K := fun t => B.repr (Φ t * Φ t - Φ t) with hf1
  set f2 : (ι → K) → K := fun t => ψ (Φ t) - 1 with hf2
  set f3 : (ι → K) → K := fun t => Algebra.norm K (p + q * (Φ t - e)) - Algebra.norm K p with hf3
  have hf1c : Continuous f1 := by
    have h : f1 = fun t => Matrix.mulVec (Algebra.leftMulMatrix B (Φ t)) t - t := by
      funext t
      funext i
      simp only [hf1, map_sub, Finsupp.coe_sub, Pi.sub_apply]
      rw [← Algebra.leftMulMatrix_mulVec_repr, hrepr]
      simp
    rw [h]
    exact (hM.matrix_mulVec continuous_id).sub continuous_id
  have hf2c : Continuous f2 := by
    have hl : Continuous fun t => ψ (Φ t) := by
      have h := LinearMap.continuous_on_pi (ψ.toLinearMap ∘ₗ B.equivFun.symm.toLinearMap)
      convert h using 1
      funext t
      simp [hΦ, Module.Basis.equivFun_symm_apply]
    exact hl.sub continuous_const
  have hf3c : Continuous f3 := by
    have h : (fun t => Algebra.norm K (p + q * (Φ t - e))) = fun t =>
        (Algebra.leftMulMatrix B (p - q * e) + Algebra.leftMulMatrix B q *
          Algebra.leftMulMatrix B (Φ t)).det := by
      funext t
      rw [Algebra.norm_eq_matrix_det B, ← map_mul, ← map_add]
      congr 2
      ring
    have : Continuous fun t => Algebra.norm K (p + q * (Φ t - e)) := by
      rw [h]
      exact (continuous_const.add (continuous_const.matrix_mul hM)).matrix_det
    exact this.sub continuous_const
  set t₀ : ι → K := fun i => B.repr e i with ht₀
  have hΦ₀ : Φ t₀ = e := by simp only [hΦ, ht₀]; exact B.sum_repr e
  have hball' : ∀ x₀ : K, Valued.v x₀ ≠ 0 → {z : K | Valued.v z ≤ Valued.v x₀} ∈ 𝓝 (0 : K) := by
    intro x₀ hx₀
    have hl : {y : K | Valued.v y = Valued.v x₀} ∈ 𝓝 x₀ := Valued.locally_const hx₀
    have hc : ContinuousAt (fun z : K => z + x₀) 0 := (continuous_id.add continuous_const).continuousAt
    have h' := hc.preimage_mem_nhds (by simpa using hl)
    filter_upwards [h'] with z hz
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    calc Valued.v z = Valued.v ((z + x₀) - x₀) := by rw [add_sub_cancel_right]
      _ ≤ max (Valued.v (z + x₀)) (Valued.v x₀) := Valuation.map_sub _ _ _
      _ = Valued.v x₀ := by rw [hz, max_self]
  have hva : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hx₀ : Valued.v ((algebraMap E K π) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hva, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : ∀ γ, γ = WithZero.exp (-(n : ℤ)) ∨ γ = 1 → {z : K | Valued.v z ≤ γ} ∈ 𝓝 (0 : K) := by
    rintro γ (rfl | rfl)
    · rw [← hx₀]
      exact hball' _ (by rw [hx₀]; exact WithZero.exp_ne_zero)
    · have := hball' 1 (by simp)
      simpa using this
  have h1 : ∀ᶠ t in 𝓝 t₀, ∀ i, Valued.v (f1 t i) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t => f1 t i) t₀ := ((continuous_apply i).comp hf1c).continuousAt
    have h0 : f1 t₀ i = 0 := by simp [hf1, hΦ₀, he]
    exact hc.preimage_mem_nhds (by rw [h0]; exact hball 1 (Or.inr rfl))
  have h2 : ∀ᶠ t in 𝓝 t₀, Valued.v (f2 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f2 t₀ = 0 := by simp [hf2, hΦ₀, hψ]
    exact hf2c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have h3 : ∀ᶠ t in 𝓝 t₀, Valued.v (f3 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f3 t₀ = 0 := by simp [hf3, hΦ₀]
    exact hf3c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have hd : DenseRange (Pi.map fun _ : ι => (algebraMap E K : E → K)) :=
    DenseRange.piMap fun _ => w.denseRange_algebraMap E
  obtain ⟨c, hc1, hc2, hc3⟩ := hd.mem_nhds (h1.and (h2.and h3))
  set ε : E' := ∑ i, c i • b i with hε
  have hΦc : Φ (Pi.map (fun _ : ι => (algebraMap E K : E → K)) c) = (1 : K) ⊗ₜ ε := by
    simp only [hΦ, Pi.map_apply, hε]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, algebraMap_smul]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro i
    have h := hc1 i
    simp only [hf1, hΦc] at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub,
      hB, Algebra.TensorProduct.basis_repr_tmul] at h
    simp only [one_smul, Finsupp.mapRange_apply] at h
    rw [← hva]
    exact h
  · have h := hc2
    simpa only [hf2, hΦc] using h
  · have h := hc3
    simpa only [hf3, hΦc] using h

end GlobalTheory
