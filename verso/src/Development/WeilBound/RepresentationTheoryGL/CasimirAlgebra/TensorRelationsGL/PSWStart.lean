import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStartB

noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

section Int

variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Use `haveI := hfin`. Use `set V := Submodule.span ℂ (Set.range fun γ => ρ γ y) with hV`. Set `b` to `Module.finBasis ℂ V`. Establish `hext : ∀ i, ∃ f : M →ₗ[ℂ] ℂ, f ∘ₗ V.subtype = b.coord i` using `fun i => LinearMap.exists_extend _`. Use `choose e he using hext`.

Establish `hmem : ∀ k, ρ k y ∈ V` using `fun k => Submodule.subset_span ⟨k, rfl⟩`. Establish `hrepr : ∀ k, ρ k y = ∑ i, e i (ρ k y) • (b i : M)`. Introduce `k`. Establish `hc : ∀ i, e i (ρ k y) = b.repr ⟨ρ k y, hmem k⟩ i` using `fun i => by`. Use `LinearMap.congr_fun (he i) ⟨ρ k y, hmem k⟩` as an intermediate fact.

Simplify using `using this`. Repeatedly rewrite using `[hc]`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨ρ k y, hmem k⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Conclude with `h.symm`.

Establish `hint : ∀ i, Integrable (fun k => g k * e i (ρ k y)) μ` using `fun i => integrable_of_cont μ (hg.mul (hcont (e i)))`. Use `⟨∑ i, (∫ k, g k * e i (ρ k y) ∂μ) • (b i : M), fun lam => ?_⟩` and prove the remaining obligations. Establish `hpt : ∀ k, g k * lam (ρ k y) = ∑ i, g k * e i (ρ k y) * lam (b i)`. Introduce `k`. Use `conv_lhs => rw [hrepr k]`.

Simplify using `[map_sum, Finset.mul_sum, mul_assoc]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_finset_sum _ (fun i _ => (hint i).mul_const _)]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, integral_mul_const]`.
-/
theorem int_exists (ρ : Γ → Module.End ℂ M) (y : M)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y)))
    (hcont : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun γ => lam (ρ γ y)) {g : Γ → ℂ} (hg : Continuous g) :
    ∃ x : M, ∀ lam : M →ₗ[ℂ] ℂ, lam x = ∫ k, g k * lam (ρ k y) ∂μ := by
  classical
  haveI := hfin
  set V := Submodule.span ℂ (Set.range fun γ => ρ γ y) with hV
  let b := Module.finBasis ℂ V
  have hext : ∀ i, ∃ f : M →ₗ[ℂ] ℂ, f ∘ₗ V.subtype = b.coord i := fun i => LinearMap.exists_extend _
  choose e he using hext
  have hmem : ∀ k, ρ k y ∈ V := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hrepr : ∀ k, ρ k y = ∑ i, e i (ρ k y) • (b i : M) := by
    intro k
    have hc : ∀ i, e i (ρ k y) = b.repr ⟨ρ k y, hmem k⟩ i := fun i => by
      have := LinearMap.congr_fun (he i) ⟨ρ k y, hmem k⟩
      simpa using this
    simp_rw [hc]
    have h := congrArg Subtype.val (b.sum_repr ⟨ρ k y, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hint : ∀ i, Integrable (fun k => g k * e i (ρ k y)) μ := fun i =>
    integrable_of_cont μ (hg.mul (hcont (e i)))
  refine ⟨∑ i, (∫ k, g k * e i (ρ k y) ∂μ) • (b i : M), fun lam => ?_⟩
  have hpt : ∀ k, g k * lam (ρ k y) = ∑ i, g k * e i (ρ k y) * lam (b i) := by
    intro k
    conv_lhs => rw [hrepr k]
    simp [map_sum, Finset.mul_sum, mul_assoc]
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun i _ => (hint i).mul_const _)]
  simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
/- English proof (translation)
Establish `hd : ∀ τ, (κ τ γ).det ≠ 0` using `fun τ => det_ne hK τ γ`. Establish `hc : (∏ τ, (κ τ γ).det ^ (-c τ)) * ∏ τ, (κ τ γ).det ^ (c τ) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `τ _`.

Rewrite using `[← zpow_add₀ (hd τ)]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `J _`.

Simplify using `only [mono, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (∏ τ, (κ τ k).det ^ (c τ)) * ∏ p, ∑ j, κ (lab p) γ (I p) j * κ (lab p) k j (K p) := by`. Rewrite using `[Fintype.prod_sum, Finset.mul_sum]`. Use `_ = (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by`.

Simplify using `only [mono, hK.mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]`. Rewrite using `[← mul_assoc, ← mul_assoc, hc, one_mul]`.
-/
theorem mono_left (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) (γ k : Γ) :
    ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k =
      (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
  have hd : ∀ τ, (κ τ γ).det ≠ 0 := fun τ => det_ne hK τ γ
  have hc : (∏ τ, (κ τ γ).det ^ (-c τ)) * ∏ τ, (κ τ γ).det ^ (c τ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    rw [← zpow_add₀ (hd τ)]
    simp
  calc ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k
      = ∑ J : Fin m → Fin n, (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, (κ (lab p) γ (I p) (J p) * κ (lab p) k (J p) (K p)) := by
        apply Finset.sum_congr rfl
        intro J _
        simp only [mono, Finset.prod_mul_distrib]
        ring
    _ = (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, ∑ j, κ (lab p) γ (I p) j * κ (lab p) k j (K p) := by
        rw [Fintype.prod_sum, Finset.mul_sum]
    _ = (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
        simp only [mono, hK.mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
        rw [← mul_assoc, ← mul_assoc, hc, one_mul]

/- English proof (translation)
Use `choose ξ hξ using fun I : Fin m → Fin n => int_exists μ ρ y (hG.fin y) (hG.cont y) (g := mono κ lab c I K) (mono_cont hK lab c I K)`. Use `⟨ξ, fun γ => ?_, hξ⟩` and prove the remaining obligations. Establish `hLc : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun k => lam (ρ (γ * k) y)`. Introduce `lam`. Simplify `hG.cont y (lam ∘ₗ ρ γ)` using `[hG.mul, Module.End.mul_apply]`.

Establish `hD : (∏ τ, (κ τ γ).det ^ (-c τ)) = (∏ τ, (κ τ γ).det ^ (c τ))⁻¹`. Simplify using `[_root_.zpow_neg, Finset.prod_inv_distrib]`. Use function extensionality and compare the values at `I`. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `lam`.

Rewrite using `[map_sub, sub_eq_zero]`. Establish `h1 : ∀ J, lam (ρ γ (ξ J)) = ∫ k, mono κ lab c J K k * lam (ρ (γ * k) y) ∂μ`. Introduce `J`. Use `hξ J (lam ∘ₗ ρ γ)` as an intermediate fact. Simplify `this` using `[hG.mul, Module.End.mul_apply]`.

Simplify using `[actT, h1, hξ I lam]`. Repeatedly rewrite using `[← integral_const_mul]`. Rewrite using `[← integral_finset_sum]`. Rewrite using `[← integral_mul_left_eq_self (fun x => (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ * (mono κ lab c I K x * lam (ρ x y))) γ]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[← mul_assoc, ← hD, ← mono_left hK lab c I K γ k, Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `J _`. Expand and normalize the polynomial expressions, which then agree.

Introduce `J _`. Conclude with `integrable_of_cont μ (continuous_const.mul ((mono_cont hK lab c J K).mul (hLc lam)))`.
-/
theorem tensor_exists [IsTopologicalGroup Γ] [μ.IsMulLeftInvariant] {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (y : M) {m : ℕ} (lab : Fin m → ι)
    (c : ι → ℤ) (K : Fin m → Fin n) :
    ∃ ξ : TV n M (Fin m), (∀ γ, actT lab κ ρ γ ξ = (∏ τ, (κ τ γ).det ^ (-c τ)) • ξ) ∧
      ∀ I (lam : M →ₗ[ℂ] ℂ), lam (ξ I) = ∫ k, mono κ lab c I K k * lam (ρ k y) ∂μ := by
  classical
  choose ξ hξ using fun I : Fin m → Fin n =>
    int_exists μ ρ y (hG.fin y) (hG.cont y) (g := mono κ lab c I K) (mono_cont hK lab c I K)
  refine ⟨ξ, fun γ => ?_, hξ⟩
  have hLc : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun k => lam (ρ (γ * k) y) := by
    intro lam
    simpa [hG.mul, Module.End.mul_apply] using hG.cont y (lam ∘ₗ ρ γ)
  have hD : (∏ τ, (κ τ γ).det ^ (-c τ)) = (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ := by
    simp [_root_.zpow_neg, Finset.prod_inv_distrib]
  funext I
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro lam
  rw [map_sub, sub_eq_zero]
  have h1 : ∀ J, lam (ρ γ (ξ J)) = ∫ k, mono κ lab c J K k * lam (ρ (γ * k) y) ∂μ := by
    intro J
    have := hξ J (lam ∘ₗ ρ γ)
    simpa [hG.mul, Module.End.mul_apply] using this
  simp [actT, h1, hξ I lam]
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum]
  · rw [← integral_mul_left_eq_self
      (fun x => (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ * (mono κ lab c I K x * lam (ρ x y))) γ]
    congr 1
    funext k
    rw [← mul_assoc, ← hD, ← mono_left hK lab c I K γ k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    ring
  · intro J _
    exact integrable_of_cont μ (continuous_const.mul ((mono_cont hK lab c J K).mul (hLc lam)))

end Int

end SWS

/- English proof (translation)
Unfold `SWStart`. Introduce `n M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG φ hφ`. Use `letI : MeasurableSpace Γ := borel Γ`. Use `haveI : BorelSpace Γ := ⟨rfl⟩`. Take `⟨H, hH⟩` from `SWS.exists_half bar hK.invol hK.ne`.

Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hφ (LinearMap.ext h)`. Establish `hf : Continuous fun k => φ (ρ k y)` using `hG.cont y φ`.

Establish `h1 : φ (ρ 1 y) ≠ 0` using `by simpa [hG.one] using hy`. Take `⟨g, ⟨m, lab, c, I, K, hlab, rfl⟩, hg⟩` from `SWS.nonvanish (Measure.haar : Measure Γ) hK hH hf 1 h1`. Take `⟨ξ, hξ1, hξ2⟩` from `SWS.tensor_exists (Measure.haar : Measure Γ) hK hG y lab c K`. Use `⟨m, lab, -c, ξ, ?_, ?_, I, 1, Subalgebra.one_mem _, ?_⟩` and prove the remaining obligations. Introduce `p q h`.

Conclude with `(hH (lab q)).1 (hlab q) (h ▸ hlab p)`. Introduce `γ`. Rewrite using `[hξ1 γ]`. Simplify using the standard rewrite rules. Simplify `hg` using `[hξ2 I φ]`.
-/
theorem swStart_holds : SWStart := by
  unfold SWStart
  intro n M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG φ hφ
  classical
  letI : MeasurableSpace Γ := borel Γ
  haveI : BorelSpace Γ := ⟨rfl⟩
  obtain ⟨H, hH⟩ := SWS.exists_half bar hK.invol hK.ne
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  have hf : Continuous fun k => φ (ρ k y) := hG.cont y φ
  have h1 : φ (ρ 1 y) ≠ 0 := by simpa [hG.one] using hy
  obtain ⟨g, ⟨m, lab, c, I, K, hlab, rfl⟩, hg⟩ :=
    SWS.nonvanish (Measure.haar : Measure Γ) hK hH hf 1 h1
  obtain ⟨ξ, hξ1, hξ2⟩ := SWS.tensor_exists (Measure.haar : Measure Γ) hK hG y lab c K
  refine ⟨m, lab, -c, ξ, ?_, ?_, I, 1, Subalgebra.one_mem _, ?_⟩
  · intro p q h
    exact (hH (lab q)).1 (hlab q) (h ▸ hlab p)
  · intro γ
    rw [hξ1 γ]
    simp
  · simpa [hξ2 I φ] using hg

end PositivityTheory.Rg.Cz

end
