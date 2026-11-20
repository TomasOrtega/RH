import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscreteLatticeMinimum

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FinrankRieszBounds

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Establish `hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w`. Introduce `w`. Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v`. Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ)`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v`. Rewrite using `[hl, hr, ← mul_assoc, hcc]`. Establish `hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v`. Simplify using `only [Data.posPart, hl, map_mul]`.

Rewrite using `[← Complex.re_ofReal_mul]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hcc]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Data.maj, hP, hH, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maj_csmul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by
  have hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hl, hr, ← mul_assoc, hcc]
  have hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v := by
    simp only [Data.posPart, hl, map_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hcc]
    ring
  simp only [Data.maj, hP, hH, Complex.re_ofReal_mul]
  ring

variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]

/- English proof (translation)
Set `ℓ : VT (X` to `X) z ξ →ₗ[ℝ] ℝ := { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re map_add' := fun u v => by`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[VT.val_add, Pi.add_apply, map_add, Complex.add_re]`. Use the proof step `map_smul' := fun c u => by`.

Rewrite using `[RingHom.id_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul] }`. Set `d` to `(InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)`. Use `⟨d, fun u hu τ0 => ?_⟩` and prove the remaining obligations.

Establish `hd : ∀ v : VT (X` using `X) z ξ, inner ℝ d v = ℓ v := fun v => by`. Rewrite using `[InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression. Establish `key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re`. Introduce `w hw`.

Set `s : X.Ψ → ℂ` to `fun τ => if τ = τ0 then 1 else 0`. Establish `hw'` using `MajorantOperators.smul_fam_mem s hw`. Establish `h` using `hd (VT.mk _ hw')`. Rewrite `h` using `[inner_eq]`. Simplify using `only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h`.

Rewrite `h` using `[Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right]) (fun h => absurd (Finset.mem_univ τ0) h), Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]`. Simplify using `only [s, if_true, one_smul] at h`. Rewrite using `[← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]`. Establish `h1` using `key u hu`. Establish `h2` using `key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)`.

Simplify using `only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h2`. Apply `Complex.ext` to reduce the goal to its premises. Conclude with `h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem riesz (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) :
    ∃ d : VT (X := X) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ, δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
  classical
  let ℓ : VT (X := X) z ξ →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re
      map_add' := fun u v => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_add, Pi.add_apply, map_add, Complex.add_re]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul] }
  let d := (InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)
  refine ⟨d, fun u hu τ0 => ?_⟩
  have hd : ∀ v : VT (X := X) z ξ, inner ℝ d v = ℓ v := fun v => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

  have key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re := by
    intro w hw
    let s : X.Ψ → ℂ := fun τ => if τ = τ0 then 1 else 0
    have hw' := MajorantOperators.smul_fam_mem s hw
    have h := hd (VT.mk _ hw')
    rw [inner_eq] at h
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h
    rw [Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right])
      (fun h => absurd (Finset.mem_univ τ0) h),
      Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]
      at h
    simp only [s, if_true, one_smul] at h
    rw [← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]
  have h1 := key u hu
  have h2 := key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)
  simp only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub] at h2
  apply Complex.ext
  · exact h1
  · linarith

omit hz in

/- English proof (translation)
Set `Lm : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin 2 → ℂ)` to `{ toFun := fun u τ => ![hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ), hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ)] map_add' := fun u v => by`. Use function extensionality and compare the values at `τ i`. Apply the tactic sequence `fin_cases i <;> simp [hermC_add_left, Data.jp_add]`. Use the proof step `map_smul' := fun c u => by`. Use function extensionality and compare the values at `τ i`.

Apply the tactic sequence `fin_cases i <;> simp [← Complex.coe_smul, hermC_smul_left, Data.jp_smul] }`. Establish `hker : LinearMap.ker Lm = Usub (X` using `X) z ξ := by`. Use extensionality with `u`. Rewrite using `[LinearMap.mem_ker]`. Use `show Lm u = 0 ↔ u ∈ X.Uz z ξ`.

Rewrite using `[MajorantOperators.mem_Uz_iff, funext_iff]`. Use `forall_congr' fun τ => ?_` and prove the remaining obligations. Rewrite using `[funext_iff, Fin.forall_fin_two]`. Simplify using `[Lm]`. Establish `hsurj : LinearMap.range Lm = ⊤`.

Rewrite using `[LinearMap.range_eq_top]`. Introduce `t`. Establish `hm : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ) ≠ 0`. Introduce `τ`. Rewrite using `[← Data.Hf_eq_jp, X.Hf_self hz]`.

Conclude with `(X.maj_pos hz τ (emb_ne_zero τ.1 hξ.2.2)).ne'` after adjusting the coercions. Establish `hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0` using `fun τ => by`. Rewrite using `[hermC_emb, hξ.2.1, map_zero]`. Use `⟨fun τ => (t τ 0 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • X.jp z τ (Data.emb τ.1 ξ) + (t τ 1 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i`.

Use `fin_cases i`. Simplify using `[Lm, hermC_add_left, hermC_smul_left, hee, div_mul_cancel₀ _ (hm τ)]`. Simplify using `[Lm, hermC_add_left, hermC_smul_left, Data.jp_add, Data.jp_smul, X.jp_jp hz, hee, div_mul_cancel₀ _ (hm τ)]`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker Lm`. Rewrite `hrn` using `[hsurj, finrank_top, hker]`.

Establish `hdom : finrank ℝ (X.Ψ → Fin r → ℂ) = Fintype.card X.Ψ * (r * 2)`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Establish `hcod : finrank ℝ (X.Ψ → Fin 2 → ℂ) = Fintype.card X.Ψ * (2 * 2)`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Rewrite `hrn` using `[hdom, hcod]`.

Establish `hV : finrank ℝ (VT (X` using `X) z ξ) = finrank ℝ (Usub (X := X) z ξ) := rfl`. Establish `hΨ : 2 * Fintype.card X.Ψ ≤ finrank ℚ E`. Establish `hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate)`. Rewrite using `[Finset.disjoint_left]`. Introduce `σ hσ hσ'`.

Take `⟨τ, hτ, rfl⟩` from `Finset.mem_image.mp hσ'`. Conclude with `(X.cmType τ).mp hτ hσ`. Establish `hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ))` using `fun a b h => by`. Use `congrArg ComplexEmbedding.conjugate h` as an intermediate fact. Simplify using `using this`.

Establish `h1` using `Finset.card_le_univ (X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate)`. Rewrite `h1` using `[Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, NumberField.Embeddings.card]`. Rewrite using `[Fintype.card_coe]`. Use linear arithmetic over natural numbers and integers. Establish `hf : Fintype.card X.Ψ ≤ fdeg E`.

Unfold `fdeg`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hV]`. Establish `hk : finrank ℝ (Usub (X` using `X) z ξ) = 2 * Fintype.card X.Ψ * (r - 2) := by`. Rewrite using `[Nat.eq_sub_of_add_eq' hrn, Nat.mul_sub]`.

Put the polynomial expressions in normal form. Rewrite using `[hk]`. Conclude with `Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)`.
-/
theorem finrank_le {ξ : Fin r → E} (hz : z ∈ X.dom) (hξ : X.IsIso ξ) :
    finrank ℝ (VT (X := X) z ξ) ≤ 2 * fdeg E * (r - 2) := by
  classical
  let Lm : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin 2 → ℂ) :=
    { toFun := fun u τ => ![hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ),
        hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ)]
      map_add' := fun u v => by
        funext τ i
        fin_cases i <;> simp [hermC_add_left, Data.jp_add]
      map_smul' := fun c u => by
        funext τ i
        fin_cases i <;> simp [← Complex.coe_smul, hermC_smul_left, Data.jp_smul] }
  have hker : LinearMap.ker Lm = Usub (X := X) z ξ := by
    ext u
    rw [LinearMap.mem_ker]
    show Lm u = 0 ↔ u ∈ X.Uz z ξ
    rw [MajorantOperators.mem_Uz_iff, funext_iff]
    refine forall_congr' fun τ => ?_
    rw [funext_iff, Fin.forall_fin_two]
    simp [Lm]
  have hsurj : LinearMap.range Lm = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    have hm : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ) ≠ 0 := by
      intro τ
      rw [← Data.Hf_eq_jp, X.Hf_self hz]
      exact_mod_cast (X.maj_pos hz τ (emb_ne_zero τ.1 hξ.2.2)).ne'
    have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
      rw [hermC_emb, hξ.2.1, map_zero]
    refine ⟨fun τ => (t τ 0 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) •
        X.jp z τ (Data.emb τ.1 ξ) +
      (t τ 1 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ, ?_⟩
    funext τ i
    fin_cases i
    · simp [Lm, hermC_add_left, hermC_smul_left, hee, div_mul_cancel₀ _ (hm τ)]
    · simp [Lm, hermC_add_left, hermC_smul_left, Data.jp_add, Data.jp_smul, X.jp_jp hz, hee,
        div_mul_cancel₀ _ (hm τ)]
  have hrn := LinearMap.finrank_range_add_finrank_ker Lm
  rw [hsurj, finrank_top, hker] at hrn
  have hdom : finrank ℝ (X.Ψ → Fin r → ℂ) = Fintype.card X.Ψ * (r * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hcod : finrank ℝ (X.Ψ → Fin 2 → ℂ) = Fintype.card X.Ψ * (2 * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hdom, hcod] at hrn
  have hV : finrank ℝ (VT (X := X) z ξ) = finrank ℝ (Usub (X := X) z ξ) := rfl

  have hΨ : 2 * Fintype.card X.Ψ ≤ finrank ℚ E := by
    have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
      rw [Finset.disjoint_left]
      intro σ hσ hσ'
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ'
      exact (X.cmType τ).mp hτ hσ
    have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
      fun a b h => by
        have := congrArg ComplexEmbedding.conjugate h
        simpa using this
    have h1 := Finset.card_le_univ (X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      NumberField.Embeddings.card] at h1
    rw [Fintype.card_coe]
    omega
  have hf : Fintype.card X.Ψ ≤ fdeg E := by
    unfold fdeg
    omega
  rw [hV]
  have hk : finrank ℝ (Usub (X := X) z ξ) = 2 * Fintype.card X.Ψ * (r - 2) := by
    rw [Nat.eq_sub_of_add_eq' hrn, Nat.mul_sub]
    ring_nf
  rw [hk]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)

end FinrankRieszBounds

end ReciprocityTheory.ChartRestriction.G.FD
