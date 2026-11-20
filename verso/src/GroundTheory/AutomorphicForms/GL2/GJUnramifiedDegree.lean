import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLocalZeta
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Levi

open Matrix GLnLocal Parabolic MeasureTheory Polynomial ValuativeRel
open scoped NNReal ENNReal

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (levi F n β)] [BorelSpace (levi F n β)]

/- English proof (translation)
Take `⟨ω, hω⟩` from `exists_blockChar (F := F) hσ`. Take `⟨s₀, -, hconv⟩` from `exists_lintegral_lt_top hσ hc θ hθ μM`. Use `set B1 : Finset (Set.range β) := Finset.univ.filter fun b => blockSize β b = 1 with hB1`. Use `⟨s₀, ∏ b ∈ B1, (1 - Polynomial.C ((θ (blockUnif F b) : ℂ) * ω b) * Polynomial.X), ?_, ?_, fun Ψ hΨ w ℓ hℓ => ⟨fun s hs => integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w ℓ hℓ), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval_prod]`.

Conclude with `Finset.prod_eq_one fun b _ => by simp`. Use `(natDegree_prod_le _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_card_nsmul _ _ 1 fun b _ => ?_).trans ?_` and prove the remaining obligations. Use `(natDegree_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[natDegree_one]`.

Conclude with `max_le (Nat.zero_le _) ((natDegree_C_mul_le _ X).trans natDegree_X_le)`. Rewrite using `[smul_eq_mul, mul_one]`. Conclude with `(Finset.card_le_univ _).trans ((Fintype.card_range_le β).trans (Fintype.card_fin n).le)`. Take `⟨Ψ', hΨ', hvan, hint⟩` from `exists_removeBlocks hσ θ hθ μM hω w ℓ (fun s hs k => hconv s hs w ℓ hℓ k) hΨ B1`. Take `⟨N, P, hNP⟩` from `exists_laurent hσ hc θ hθ μM hΨ' (fun b hb => hvan b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) w hℓ (fun s hs w' k => hconv s hs w' ℓ hℓ k)`.

Use `⟨N, P, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[← hNP s hs, hint s hs, Polynomial.eval_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hb).2, pow_one]`.

Simplify using the standard rewrite rules.
-/
theorem exists_leviZeta_natDegree (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ D.natDegree ≤ n ∧
      ∀ Ψ : Matrix (Fin n) (Fin n) F → ℂ, IsLeviSchwartz β Ψ → ∀ w : W,
        ∀ ℓ ∈ smoothVectors (Representation.dual σ),
          (∀ s : ℂ, s₀ < s.re → Integrable (leviIntegrand σ θ Ψ w ℓ s) μM) ∧
          ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
            D.eval (qs F s) * ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μM =
              P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨ω, hω⟩ := exists_blockChar (F := F) hσ
  obtain ⟨s₀, -, hconv⟩ := exists_lintegral_lt_top hσ hc θ hθ μM
  set B1 : Finset (Set.range β) := Finset.univ.filter fun b => blockSize β b = 1 with hB1
  refine ⟨s₀, ∏ b ∈ B1, (1 - Polynomial.C ((θ (blockUnif F b) : ℂ) * ω b) * Polynomial.X),
    ?_, ?_, fun Ψ hΨ w ℓ hℓ => ⟨fun s hs =>
      integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w ℓ hℓ), ?_⟩⟩
  · rw [Polynomial.eval_prod]
    exact Finset.prod_eq_one fun b _ => by simp
  · refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun b _ => ?_).trans ?_
    · refine (natDegree_sub_le _ _).trans ?_
      rw [natDegree_one]
      exact max_le (Nat.zero_le _) ((natDegree_C_mul_le _ X).trans natDegree_X_le)
    · rw [smul_eq_mul, mul_one]
      exact (Finset.card_le_univ _).trans ((Fintype.card_range_le β).trans (Fintype.card_fin n).le)
  · obtain ⟨Ψ', hΨ', hvan, hint⟩ := exists_removeBlocks hσ θ hθ μM hω w ℓ
      (fun s hs k => hconv s hs w ℓ hℓ k) hΨ B1
    obtain ⟨N, P, hNP⟩ := exists_laurent hσ hc θ hθ μM hΨ'
      (fun b hb => hvan b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) w hℓ
      (fun s hs w' k => hconv s hs w' ℓ hℓ k)
    refine ⟨N, P, fun s hs => ?_⟩
    rw [← hNP s hs, hint s hs, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [(Finset.mem_filter.1 hb).2, pow_one]
    simp

end Levi

section Induced

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Polynomial ValuativeRel Topology
open scoped NNReal ENNReal Pointwise

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

/- English proof (translation)
Use `borelize F`. Establish `: BorelSpace (levi F n β)` using `Subtype.borelSpace _`. Establish `: BorelSpace (integralGL F n)` using `Subtype.borelSpace _`. Establish `: CompactSpace (integralGL F n)` using `isCompact_iff_compactSpace.1 (isCompact_integralGL F n)`. Set `μ𝔪 : Measure (LeviIndex n β → F)` to `Measure.addHaar`.

Set `μ𝔫 : Measure (UnipotentIndex n β → F)` to `Measure.addHaar`. Set `μK : Measure (integralGL F n)` to `Measure.haar`. Set `θ : levi F n β →* ℝ≥0` to `leviRatio β * leviSqrtModular β`. Establish `hθ : Continuous θ` using `continuous_leviRatio.mul continuous_leviSqrtModular`. Take `⟨s₀, D, hD0, hDn, hM⟩` from `exists_leviZeta_natDegree hσ hc θ hθ (haarLevi β μ𝔪)`.

Use `⟨s₀, D, hD0, hDn, fun Φ hΦ φ hφ ℓ hℓ => ?_⟩` and prove the remaining obligations. Take `⟨r₁, hr₁⟩` from `hΦ.exists_mul_congruenceSubgroup`. Take `⟨K', hK'o, hK'⟩` from `hφ.2`. Take `⟨r₂, -, hr₂⟩` from `(hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)`. Establish `hinv : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n (max r₁ r₂), inducedIntegrand Φ φ ℓ s (g * k) = inducedIntegrand Φ φ ℓ s g`.

Introduce `s g k hk`. Establish `hk₀ : k ∈ integralGL F n` using `congruenceSubgroup_le F n _ hk`. Simplify using `only [inducedIntegrand, Units.val_mul]`. Rewrite using `[hr₁ _ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk), detPow_mul_of_mem_integralGL g hk₀, hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g]`. Establish `: Finite (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n))` using `Subgroup.quotient_finite_of_isOpen _ ((isOpen_congruenceSubgroup F n _).preimage continuous_subtype_val)`.

Set `_` to `Fintype.ofFinite (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n))`. Set `Q` to `integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)`. Set `y : Q → GL (Fin n) F` to `fun q => ((q.out : integralGL F n) : GL (Fin n) F)`. Establish `hy : ∀ q, y q ∈ integralGL F n` using `fun q => (q.out).2`. Set `Ψ : Q → Matrix (Fin n) (Fin n) F → ℂ` to `fun q X => ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F)) ∂μ𝔫`.

Set `Ψa : Q → Matrix (Fin n) (Fin n) F → ℂ` to `fun q X => ∫ u, ((‖Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫`. Establish `hΨ : ∀ q, IsLeviSchwartz β (Ψ q)` using `fun q => isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q))`. Establish `hΨa : ∀ q, IsLeviSchwartz β (Ψa q)` using `fun q => isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q)).norm`. Use `choose N Pq hNP using fun q => (hM (Ψ q) (hΨ q) (φ (y q)) ℓ hℓ).2`. Establish `hcont : ∀ s, Continuous (inducedIntegrand Φ φ ℓ s)` using `fun s => continuous_inducedIntegrand hΦ hφ.2 ℓ s`.

Establish `hintP : ∀ s : ℂ, s₀ < s.re → ∀ z ∈ integralGL F n, Integrable (fun p : blockUpper F n β => inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z)) (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))`. Introduce `s hs z hz`. Establish `hΨz` using `isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight z).norm`. Use `⟨((hcont s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z)‖ₑ ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) < ⊤`.

Rewrite using `[lintegral_inducedIntegrand_mul μ𝔪 μ𝔫 hΦ hφ ℓ s hz]`. Conclude with `((hM _ hΨz (φ z) ℓ hℓ).1 s hs).2`. Establish `hP0 : haarParabolic (parabolicMeasure β μ𝔪 μ𝔫) (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0` using `((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _ ⟨1, by simp [one_mem]⟩`. Establish `hK0 : μK Set.univ ≠ 0` using `isOpen_univ.measure_ne_zero μK Set.univ_nonempty`. Establish `hintG : ∀ s : ℂ, s₀ < s.re → Integrable (inducedIntegrand Φ φ ℓ s) μG`.

Introduce `s hs`. Use `⟨(hcont s).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hC` using `lintegral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) μK (hcont s).enorm.measurable (fun g k hk => by rw [hinv s g k hk])`. Establish `hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)) * ∑ q : Q, ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y q)‖ₑ ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) < ⊤` using `ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top (ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.sum_lt_top.2 fun q _ => (hintP s hs (y q) (hy q)).2))`. Rewrite `hlt` using `[hC]`.

Conclude with `ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)`. Use `set κ : ℝ := (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)).real (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ with hκ`. Use `set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n) : Set (integralGL F n)) with hκ'`. Establish `hκ0 : κ ≠ 0`. Rewrite using `[hκ]`.

Establish `hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) : Set (blockUpper F n β))` using `(Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_integralGL F n)`. Conclude with `mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩) (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)`. Establish `hformula : ∀ s : ℂ, s₀ < s.re → ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG = ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q : Q, ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪)`. Introduce `s hs`. Establish `hC` using `integral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) μK (hintG s hs) (hinv s) (hintP s hs)`.

Establish `hB : ∀ q : Q, ∫ p, inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y q) ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) = ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪)` using `fun q => integral_inducedIntegrand_mul μ𝔪 μ𝔫 hφ ℓ s (hy q) (hintP s hs _ (hy q))`. Rewrite `hC` using `[Finset.sum_congr rfl fun q _ => hB q]`. Rewrite `hC` using `[Complex.real_smul, Complex.real_smul, Complex.real_smul]`. Establish `hκC : (κ : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hκ0`. Rewrite `hC` using `[← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ']`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hC.symm`. Use `⟨hintG, ∑ q, N q, C ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q, Pq q * X ^ (∑ j, N j - N q), fun s hs => ?_⟩` and prove the remaining obligations. Use `show D.eval (qs F s) * ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG = _`.

Rewrite using `[hformula s hs, mul_left_comm, Finset.mul_sum, Finset.sum_congr rfl fun q _ => hNP q s hs]`. Conclude with `sum_eval_div_pow N Pq _ (qs_ne_zero s)`.
-/
theorem exists_inducedZeta_natDegree (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ D.natDegree ≤ n ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ →
        ∀ φ ∈ parabolicIndSpace F n β σ, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
          (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
            Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g)) μG) ∧
          ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
            D.eval (qs F s) * ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g) ∂μG =
              P.eval (qs F s) / qs F s ^ N := by
  classical
  borelize F
  have : BorelSpace (levi F n β) := Subtype.borelSpace _
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  let μ𝔪 : Measure (LeviIndex n β → F) := Measure.addHaar
  let μ𝔫 : Measure (UnipotentIndex n β → F) := Measure.addHaar
  let μK : Measure (integralGL F n) := Measure.haar
  let θ : levi F n β →* ℝ≥0 := leviRatio β * leviSqrtModular β
  have hθ : Continuous θ := continuous_leviRatio.mul continuous_leviSqrtModular
  obtain ⟨s₀, D, hD0, hDn, hM⟩ := exists_leviZeta_natDegree hσ hc θ hθ (haarLevi β μ𝔪)
  refine ⟨s₀, D, hD0, hDn, fun Φ hΦ φ hφ ℓ hℓ => ?_⟩

  obtain ⟨r₁, hr₁⟩ := hΦ.exists_mul_congruenceSubgroup
  obtain ⟨K', hK'o, hK'⟩ := hφ.2
  obtain ⟨r₂, -, hr₂⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)
  have hinv : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n (max r₁ r₂),
      inducedIntegrand Φ φ ℓ s (g * k) = inducedIntegrand Φ φ ℓ s g := by
    intro s g k hk
    have hk₀ : k ∈ integralGL F n := congruenceSubgroup_le F n _ hk
    simp only [inducedIntegrand, Units.val_mul]
    rw [hr₁ _ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk),
      detPow_mul_of_mem_integralGL g hk₀,
      hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g]
  have : Finite (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)) :=
    Subgroup.quotient_finite_of_isOpen _
      ((isOpen_congruenceSubgroup F n _).preimage continuous_subtype_val)
  let _ := Fintype.ofFinite
    (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n))

  let Q := integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)
  let y : Q → GL (Fin n) F := fun q => ((q.out : integralGL F n) : GL (Fin n) F)
  have hy : ∀ q, y q ∈ integralGL F n := fun q => (q.out).2
  let Ψ : Q → Matrix (Fin n) (Fin n) F → ℂ := fun q X =>
    ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F)) ∂μ𝔫
  let Ψa : Q → Matrix (Fin n) (Fin n) F → ℂ := fun q X =>
    ∫ u, ((‖Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫
  have hΨ : ∀ q, IsLeviSchwartz β (Ψ q) := fun q =>
    isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q))
  have hΨa : ∀ q, IsLeviSchwartz β (Ψa q) := fun q =>
    isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q)).norm
  choose N Pq hNP using fun q => (hM (Ψ q) (hΨ q) (φ (y q)) ℓ hℓ).2
  have hcont : ∀ s, Continuous (inducedIntegrand Φ φ ℓ s) := fun s =>
    continuous_inducedIntegrand hΦ hφ.2 ℓ s

  have hintP : ∀ s : ℂ, s₀ < s.re → ∀ z ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z))
        (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) := by
    intro s hs z hz
    have hΨz := isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight z).norm
    refine ⟨((hcont s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z)‖ₑ
      ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) < ⊤
    rw [lintegral_inducedIntegrand_mul μ𝔪 μ𝔫 hΦ hφ ℓ s hz]
    exact ((hM _ hΨz (φ z) ℓ hℓ).1 s hs).2

  have hP0 : haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)
      (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0 :=
    ((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _
      ⟨1, by simp [one_mem]⟩
  have hK0 : μK Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μK Set.univ_nonempty

  have hintG : ∀ s : ℂ, s₀ < s.re → Integrable (inducedIntegrand Φ φ ℓ s) μG := by
    intro s hs
    refine ⟨(hcont s).aestronglyMeasurable, ?_⟩
    have hC := lintegral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))
      μK (hcont s).enorm.measurable (fun g k hk => by rw [hinv s g k hk])
    have hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf
        (integralGL F n)) * ∑ q : Q, ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s
          ((p : GL (Fin n) F) * y q)‖ₑ ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) < ⊤ :=
      ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top
        (ENNReal.mul_lt_top (measure_lt_top _ _)
          (ENNReal.sum_lt_top.2 fun q _ => (hintP s hs (y q) (hy q)).2))
    rw [hC] at hlt
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)

  set κ : ℝ := (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)).real
      (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ with hκ
  set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf
      (integralGL F n) : Set (integralGL F n)) with hκ'
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    have hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) :
        Set (blockUpper F n β)) :=
      (Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_integralGL F n)
    exact mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)
  have hformula : ∀ s : ℂ, s₀ < s.re → ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG =
      ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q : Q, ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪) := by
    intro s hs
    have hC := integral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) μK
      (hintG s hs) (hinv s) (hintP s hs)
    have hB : ∀ q : Q, ∫ p, inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y q)
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
        ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪) := fun q =>
      integral_inducedIntegrand_mul μ𝔪 μ𝔫 hφ ℓ s (hy q) (hintP s hs _ (hy q))
    rw [Finset.sum_congr rfl fun q _ => hB q] at hC
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul] at hC
    have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ0
    rw [← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ'] at hC
    push_cast
    field_simp
    linear_combination hC.symm
  refine ⟨hintG, ∑ q, N q, C ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q, Pq q * X ^ (∑ j, N j - N q),
    fun s hs => ?_⟩
  show D.eval (qs F s) * ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG = _
  rw [hformula s hs, mul_left_comm, Finset.mul_sum,
    Finset.sum_congr rfl fun q _ => hNP q s hs]
  exact sum_eval_div_pow N Pq _ (qs_ne_zero s)

end Induced

section Core

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory Polynomial
open scoped NNReal ENNReal

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

/- English proof (translation)
Take `⟨β, W, _, _, σ, hσirr, hσs, hσc, -, ι, hι⟩` from `exists_embedding_parabolicInd (π := π) hπ.1`. Use `hσirr` as an intermediate fact. Take `⟨s₀, D, hD0, hDn, hJ⟩` from `exists_inducedZeta_natDegree (β := β) hσs hσc μ`. Use `⟨s₀, D, hD0, hDn, fun Φ hΦ v ℓ hℓ => ?_⟩` and prove the remaining obligations. Take `⟨m₀, hm₀⟩` from `hΦ.exists_congruence_invariant`.

Take `⟨m₁, -, hm₁⟩` from `(hasBasis_nhds_one F n).mem_iff.1 ((hπ.1 v).mem_nhds (one_mem (stabilizerOf π v)))`. Take `⟨m₂, -, hm₂⟩` from `(hasBasis_nhds_one F n).mem_iff.1 ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))`. Use `set m := max m₀ (max m₁ m₂) with hmdef`. Use `set K := congruenceSubgroup F n m with hKdef`. Establish `hKc : IsCompact (K : Set (GL (Fin n) F))` using `isCompact_congruenceSubgroup F n m`.

Establish `hKo : IsOpen (K : Set (GL (Fin n) F))` using `isOpen_congruenceSubgroup F n m`. Establish `hK0 : ∀ k ∈ K, k ∈ integralGL F n` using `fun k hk => congruenceSubgroup_le F n m hk`. Establish `hvK : ∀ k ∈ K, π k v = v` using `fun k hk => hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)`. Establish `hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x` using `mem_fixedVectors_dual.1 fun k hk => hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)`. Establish `hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧ Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X` using `fun k hk => hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)`.

Take `⟨lam, hlamK, hlam⟩` from `exists_extend_dual hπ.1 (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK`. Take `⟨R, hR₀, hR⟩` from `exists_reps_congruenceSubgroup F n m`. Take `⟨ℓx, hℓxK, hdec⟩` from `exists_eval_decomposition hσs hR₀ hR lam`. Use `set φ : parabolicIndSpace F n β σ := ι v with hφdef`. Establish `hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K` using `fun k hk => by`.

Rewrite using `[hφdef, ← ι.isIntertwining, hvK k hk]`. Establish `hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ)` using `fun g => by`. Rewrite using `[matrixCoeff, ← hlam, hφdef, ι.isIntertwining]`. Establish `hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ)` using `fun x => mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)`. Establish `hJx` using `fun x : GL (Fin n) F => hJ (fun X => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X)) (hΦ.comp_mul_left x⁻¹) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)`.

Use `choose hJint N P hJeq using hJx`. Use `set T : GL (Fin n) F → ℂ → GL (Fin n) F → ℂ := fun x s g => Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) (x * g)) with hTdef`. Establish `hTJ : ∀ x ∈ R, ∀ s g, T x s g = (fun y : GL (Fin n) F => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) * detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) (x * g)`. Introduce `x hx s g`. Simplify using `only [T]`.

Rewrite using `[detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul, Units.val_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Establish `hTint : ∀ x ∈ R, ∀ s : ℂ, s₀ < s.re → Integrable (T x s) μ`. Introduce `x hx s hs`. Conclude with `((hJint x s hs).comp_mul_left x).congr (Filter.Eventually.of_forall fun g => (hTJ x hx s g).symm)`. Establish `hTeq : ∀ x ∈ R, ∀ s, ∫ g, T x s g ∂μ = ∫ g, Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) g) ∂μ`.

Introduce `x hx s`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall (hTJ x hx s))]`. Conclude with `integral_mul_left_eq_self (μ := μ) (fun y : GL (Fin n) F => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) * detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) x`. Take `⟨r, A, -, hA⟩` from `hΦ.exists_invariant`. Use `set h : ℤ → GL (Fin n) F → ℂ := fun k => {g : GL (Fin n) F | ordDet g = k}.indicator fun g => Φ (g : Matrix (Fin n) (Fin n) F) with hhdef`.

Establish `hhcs : ∀ k, HasCompactSupport (h k)` using `fun k => HasCompactSupport.intro (isCompact_shell F n A k) fun g hg => by`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq]`. Use `split_ifs with hk`. Assume the negation of the conclusion as `hne`. Conclude with `hg ⟨hA _ hne, hk⟩`.

Both sides reduce to the same expression. Establish `hhl : ∀ k, ∀ k' ∈ K, ∀ g, h k (k' * g) = h k g` using `fun k k' hk' g => by`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul, ordDet_of_mem_integralGL (hK0 k' hk'), zero_add, Units.val_mul, (hΦK k' hk' _).1]`. Establish `hhr : ∀ k, ∀ k' ∈ K, ∀ g, h k (g * k') = h k g` using `fun k k' hk' g => by`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul, ordDet_of_mem_integralGL (hK0 k' hk'), add_zero, Units.val_mul, (hΦK k' hk' _).2]`.

Establish `hcont : ∀ H : GL (Fin n) F → ℂ, (∀ g, ∀ k ∈ K, H (g * k) = H g) → Continuous H` using `fun H hH => (isLocallyConstant_of_mul_right hKo hH).continuous`. Establish `hfr : ∀ g, ∀ k ∈ K, lam (parabolicInd F n β σ (g * k) φ) = lam (parabolicInd F n β σ g φ)` using `fun g k hk => by rw [map_mul, Module.End.mul_apply, show parabolicInd F n β σ k φ = φ from hφK k hk]`. Establish `hφr : ∀ x g, ∀ k ∈ K, (φ : GL (Fin n) F → W) (x * (g * k)) = (φ : GL (Fin n) F → W) (x * g)` using `fun x g k hk => by`. Use `congrArg (fun ψ : parabolicIndSpace F n β σ => (ψ : GL (Fin n) F → W) (x * g)) (hφK k hk)` as an intermediate fact. Simplify using `only [coe_indRep_apply] at this`.

Rewrite using `[← mul_assoc, this]`. Establish `hdetr : ∀ s g, ∀ k ∈ K, detPow (g * k) s = detPow g s` using `fun s g k hk => by`. Rewrite using `[detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]`. Establish `hΦr : ∀ g, ∀ k ∈ K, Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Φ (g : Matrix (Fin n) (Fin n) F)` using `fun g k hk => by rw [Units.val_mul, (hΦK k hk _).2]`. Establish `hhf : ∀ k, Integrable (fun g => ‖h k g * lam (parabolicInd F n β σ g φ)‖) μ` using `fun k => ((hcont _ fun g k' hk' => by rw [hhr k k' hk', hfr g k' hk']).norm).integrable_of_hasCompactSupport (hhcs k).mul_right.norm`.

Establish `hhint : ∀ k, ∀ x ∈ R, Integrable (fun g => ‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) μ` using `fun k x _ => ((hcont _ fun g k' hk' => by rw [hhr k k' hk']).norm.mul (hcont _ fun g k' hk' => by rw [hφr x g k' hk']).norm).integrable_of_hasCompactSupport (hhcs k).norm.mul_right`. Establish `hshellZ : ∀ s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) g = qs F s ^ k * (h k g * lam (parabolicInd F n β σ g φ))`. Introduce `s k g`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq]`. Use `split_ifs with hk`.

Rewrite using `[hf g, detPow_eq_qs_zpow, hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hshellT : ∀ x s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (T x s) g = qs F s ^ k * (h k g * ℓx x ((φ : GL (Fin n) F → W) (x * g)))`. Introduce `x s k g`.

Simplify using `only [h, T, Set.indicator_apply, Set.mem_ofPred_eq]`. Use `split_ifs with hk`. Rewrite using `[detPow_eq_qs_zpow, hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Establish `hZint : ∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ`. Introduce `s hs`. Use `⟨(hcont _ fun g k hk => by` and prove the remaining obligations. Rewrite using `[hΦr g k hk, hdetr s g k hk, hf, hf, hfr g k hk]).aestronglyMeasurable, ?_⟩`. Rewrite using `[HasFiniteIntegral]`.

Repeatedly rewrite using `[← ofReal_norm]`. Rewrite using `[lintegral_eq_tsum_shell]`. Establish `hterm : ∀ k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ ≤ ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖T x s g‖ ∂μ`. Introduce `k`. Establish `e1 : ∀ g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal ‖h k g * lam (parabolicInd F n β σ g φ)‖`.

Introduce `g`. Rewrite using `[← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul, ← hshellZ s k g]`. Distinguish the cases in `hg : g ∈ {g : GL (Fin n) F | ordDet g = k}`. Simplify using `[Set.indicator_of_mem hg]`. Simplify using `[Set.indicator_of_notMem hg]`.

Establish `e2 : ∀ x g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal ‖T x s g‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal (‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖)`. Introduce `x g`. Rewrite using `[← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul, ← norm_mul, ← hshellT x s k g]`. Distinguish the cases in `hg : g ∈ {g : GL (Fin n) F | ordDet g = k}`. Simplify using `[Set.indicator_of_mem hg]`.

Simplify using `[Set.indicator_of_notMem hg]`. Rewrite using `[← lintegral_indicator (measurableSet_shell k), lintegral_congr e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Repeatedly rewrite using `[← lintegral_indicator (measurableSet_shell k), e2]`. Repeatedly rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← Finset.mul_sum]`. Conclude with `mul_le_mul' le_rfl (lintegral_norm_mul_coeff_le μ hKc hKo hlamK hφK hdec (hhcs k) (hhl k) (hhr k) (hhf k) (hhint k))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Summable.tsum_finsetSum fun _ _ => ENNReal.summable]`. Conclude with `Finset.sum_congr rfl fun x _ => (lintegral_eq_tsum_shell μ _).symm`. Use `_ < ∞ := by`. Use `ENNReal.sum_lt_top.2 fun x hx => ?_` and prove the remaining obligations.

Use `(hTint x hx s hs).2` as an intermediate fact. Simplify `this` using `[HasFiniteIntegral, ofReal_norm]`. Use `⟨hZint, ?_⟩` and prove the remaining obligations. Use `⟨∑ x ∈ R, N x, ∑ x ∈ R, P x * X ^ (∑ y ∈ R, N y - N x), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hZsum` using `hasSum_integral_shell μ (hZint s hs)`.

Establish `hTsum : ∀ x ∈ R, HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ) (∫ g, T x s g ∂μ)` using `fun x hx => hasSum_integral_shell μ (hTint x hx s hs)`. Establish `hsum` using `hasSum_sum hTsum`. Establish `hshell_eq : ∀ k : ℤ, ∫ g in {g : GL (Fin n) F | ordDet g = k}, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ = ∑ x ∈ R, ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ`. Introduce `k`. Rewrite using `[← integral_indicator (measurableSet_shell k)]`.

Repeatedly rewrite using `[hshellZ s k]`. Rewrite using `[integral_const_mul, integral_mul_coeff_eq μ hKc hKo hφK hdec (hhcs k) (hhl k) (hhr k), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_indicator (measurableSet_shell k)]`. Repeatedly rewrite using `[hshellT x s k]`.

Rewrite using `[integral_const_mul]`. Establish `hZ : ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ = ∑ x ∈ R, ∫ g, T x s g ∂μ`. Use `hZsum.unique ?_` and prove the remaining obligations. Use `hsum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Conclude with `hshell_eq k`. Establish `hterm : ∀ x ∈ R, D.eval (qs F s) * ∫ g, T x s g ∂μ = (P x).eval (qs F s) / qs F s ^ N x`. Introduce `x hx`. Rewrite using `[hTeq x hx s]`. Conclude with `hJeq x s hs`.

Rewrite using `[hZ, Finset.mul_sum, Finset.sum_congr rfl hterm, eval_finsetSum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `hle : N x ≤ ∑ y ∈ R, N y` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx`. Rewrite using `[eval_mul, eval_pow, eval_X, pow_sub₀ _ (qs_ne_zero s) hle]`. Clear the denominators using the available nonvanishing facts.

Conclude with `(mul_div_mul_right _ _ (pow_ne_zero _ (qs_ne_zero s))).symm`.
-/
theorem exists_zeta_core_natDegree [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ D.natDegree ≤ n ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
        ℓ ∈ smoothVectors (Representation.dual π) →
        (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          D.eval (qs F s) * ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g s ∂μ = P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, -, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hπ.1
  have := hσirr
  obtain ⟨s₀, D, hD0, hDn, hJ⟩ := exists_inducedZeta_natDegree (β := β) hσs hσc μ
  refine ⟨s₀, D, hD0, hDn, fun Φ hΦ v ℓ hℓ => ?_⟩

  obtain ⟨m₀, hm₀⟩ := hΦ.exists_congruence_invariant
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ.1 v).mem_nhds (one_mem (stabilizerOf π v)))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))
  set m := max m₀ (max m₁ m₂) with hmdef
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hK0 : ∀ k ∈ K, k ∈ integralGL F n := fun k hk => congruenceSubgroup_le F n m hk
  have hvK : ∀ k ∈ K, π k v = v := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)
  have hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun k hk =>
    hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)

  obtain ⟨lam, hlamK, hlam⟩ := exists_extend_dual hπ.1 (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK
  obtain ⟨R, hR₀, hR⟩ := exists_reps_congruenceSubgroup F n m
  obtain ⟨ℓx, hℓxK, hdec⟩ := exists_eval_decomposition hσs hR₀ hR lam
  set φ : parabolicIndSpace F n β σ := ι v with hφdef
  have hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K := fun k hk => by
    rw [hφdef, ← ι.isIntertwining, hvK k hk]
  have hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ) := fun g => by
    rw [matrixCoeff, ← hlam, hφdef, ι.isIntertwining]
  have hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ) := fun x =>
    mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)

  have hJx := fun x : GL (Fin n) F => hJ
    (fun X => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X))
    (hΦ.comp_mul_left x⁻¹) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)
  choose hJint N P hJeq using hJx

  set T : GL (Fin n) F → ℂ → GL (Fin n) F → ℂ := fun x s g =>
    Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) (x * g))
    with hTdef
  have hTJ : ∀ x ∈ R, ∀ s g, T x s g = (fun y : GL (Fin n) F =>
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) *
        detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) (x * g) := by
    intro x hx s g
    simp only [T]
    rw [detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul, Units.val_mul, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hTint : ∀ x ∈ R, ∀ s : ℂ, s₀ < s.re → Integrable (T x s) μ := by
    intro x hx s hs
    exact ((hJint x s hs).comp_mul_left x).congr
      (Filter.Eventually.of_forall fun g => (hTJ x hx s g).symm)
  have hTeq : ∀ x ∈ R, ∀ s, ∫ g, T x s g ∂μ = ∫ g,
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) *
        detPow g s * ℓx x ((φ : GL (Fin n) F → W) g) ∂μ := by
    intro x hx s
    rw [integral_congr_ae (Filter.Eventually.of_forall (hTJ x hx s))]
    exact integral_mul_left_eq_self (μ := μ) (fun y : GL (Fin n) F =>
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) *
        detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) x

  obtain ⟨r, A, -, hA⟩ := hΦ.exists_invariant
  set h : ℤ → GL (Fin n) F → ℂ := fun k =>
    {g : GL (Fin n) F | ordDet g = k}.indicator fun g => Φ (g : Matrix (Fin n) (Fin n) F)
    with hhdef
  have hhcs : ∀ k, HasCompactSupport (h k) := fun k =>
    HasCompactSupport.intro (isCompact_shell F n A k) fun g hg => by
      simp only [h, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hk
      · by_contra hne
        exact hg ⟨hA _ hne, hk⟩
      · rfl
  have hhl : ∀ k, ∀ k' ∈ K, ∀ g, h k (k' * g) = h k g := fun k k' hk' g => by
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul,
      ordDet_of_mem_integralGL (hK0 k' hk'), zero_add, Units.val_mul, (hΦK k' hk' _).1]
  have hhr : ∀ k, ∀ k' ∈ K, ∀ g, h k (g * k') = h k g := fun k k' hk' g => by
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul,
      ordDet_of_mem_integralGL (hK0 k' hk'), add_zero, Units.val_mul, (hΦK k' hk' _).2]

  have hcont : ∀ H : GL (Fin n) F → ℂ, (∀ g, ∀ k ∈ K, H (g * k) = H g) → Continuous H :=
    fun H hH => (isLocallyConstant_of_mul_right hKo hH).continuous
  have hfr : ∀ g, ∀ k ∈ K, lam (parabolicInd F n β σ (g * k) φ) = lam (parabolicInd F n β σ g φ) :=
    fun g k hk => by rw [map_mul, Module.End.mul_apply, show parabolicInd F n β σ k φ = φ from hφK k hk]
  have hφr : ∀ x g, ∀ k ∈ K, (φ : GL (Fin n) F → W) (x * (g * k)) = (φ : GL (Fin n) F → W) (x * g) :=
    fun x g k hk => by
      have := congrArg (fun ψ : parabolicIndSpace F n β σ => (ψ : GL (Fin n) F → W) (x * g)) (hφK k hk)
      simp only [coe_indRep_apply] at this
      rw [← mul_assoc, this]
  have hdetr : ∀ s g, ∀ k ∈ K, detPow (g * k) s = detPow g s := fun s g k hk => by
    rw [detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]
  have hΦr : ∀ g, ∀ k ∈ K, Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Φ (g : Matrix (Fin n) (Fin n) F) := fun g k hk => by rw [Units.val_mul, (hΦK k hk _).2]

  have hhf : ∀ k, Integrable (fun g => ‖h k g * lam (parabolicInd F n β σ g φ)‖) μ := fun k =>
    ((hcont _ fun g k' hk' => by rw [hhr k k' hk', hfr g k' hk']).norm).integrable_of_hasCompactSupport
      (hhcs k).mul_right.norm
  have hhint : ∀ k, ∀ x ∈ R, Integrable (fun g => ‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) μ :=
    fun k x _ => ((hcont _ fun g k' hk' => by rw [hhr k k' hk']).norm.mul
      (hcont _ fun g k' hk' => by rw [hφr x g k' hk']).norm).integrable_of_hasCompactSupport
      (hhcs k).norm.mul_right
  have hshellZ : ∀ s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g =>
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) g =
      qs F s ^ k * (h k g * lam (parabolicInd F n β σ g φ)) := by
    intro s k g
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hk
    · rw [hf g, detPow_eq_qs_zpow, hk]; ring
    · simp
  have hshellT : ∀ x s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (T x s) g =
      qs F s ^ k * (h k g * ℓx x ((φ : GL (Fin n) F → W) (x * g))) := by
    intro x s k g
    simp only [h, T, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hk
    · rw [detPow_eq_qs_zpow, hk]; ring
    · simp

  have hZint : ∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ := by
    intro s hs
    refine ⟨(hcont _ fun g k hk => by
      rw [hΦr g k hk, hdetr s g k hk, hf, hf, hfr g k hk]).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [← ofReal_norm]
    rw [lintegral_eq_tsum_shell]
    have hterm : ∀ k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal
        ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ ≤
        ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖T x s g‖ ∂μ := by
      intro k
      have e1 : ∀ g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal
          ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖) g =
          ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal ‖h k g * lam (parabolicInd F n β σ g φ)‖ := by
        intro g
        rw [← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul,
          ← hshellZ s k g]
        by_cases hg : g ∈ {g : GL (Fin n) F | ordDet g = k}
        · simp [Set.indicator_of_mem hg]
        · simp [Set.indicator_of_notMem hg]
      have e2 : ∀ x g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal
          ‖T x s g‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) *
            ENNReal.ofReal (‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) := by
        intro x g
        rw [← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul,
          ← norm_mul, ← hshellT x s k g]
        by_cases hg : g ∈ {g : GL (Fin n) F | ordDet g = k}
        · simp [Set.indicator_of_mem hg]
        · simp [Set.indicator_of_notMem hg]
      rw [← lintegral_indicator (measurableSet_shell k), lintegral_congr e1,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp_rw [← lintegral_indicator (measurableSet_shell k), e2]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← Finset.mul_sum]
      exact mul_le_mul' le_rfl (lintegral_norm_mul_coeff_le μ hKc hKo hlamK hφK hdec (hhcs k)
        (hhl k) (hhr k) (hhf k) (hhint k))
    calc ∑' k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal
          ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ
        ≤ ∑' k : ℤ, ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k},
            ENNReal.ofReal ‖T x s g‖ ∂μ := ENNReal.tsum_le_tsum hterm
      _ = ∑ x ∈ R, ∫⁻ g, ENNReal.ofReal ‖T x s g‖ ∂μ := by
          rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          exact Finset.sum_congr rfl fun x _ => (lintegral_eq_tsum_shell μ _).symm
      _ < ∞ := by
          refine ENNReal.sum_lt_top.2 fun x hx => ?_
          have := (hTint x hx s hs).2
          simpa [HasFiniteIntegral, ofReal_norm] using this
  refine ⟨hZint, ?_⟩

  refine ⟨∑ x ∈ R, N x, ∑ x ∈ R, P x * X ^ (∑ y ∈ R, N y - N x), fun s hs => ?_⟩
  have hZsum := hasSum_integral_shell μ (hZint s hs)
  have hTsum : ∀ x ∈ R, HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ)
      (∫ g, T x s g ∂μ) := fun x hx => hasSum_integral_shell μ (hTint x hx s hs)
  have hsum := hasSum_sum hTsum
  have hshell_eq : ∀ k : ℤ, ∫ g in {g : GL (Fin n) F | ordDet g = k},
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ =
      ∑ x ∈ R, ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ := by
    intro k
    rw [← integral_indicator (measurableSet_shell k)]
    simp_rw [hshellZ s k]
    rw [integral_const_mul, integral_mul_coeff_eq μ hKc hKo hφK hdec (hhcs k) (hhl k) (hhr k),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← integral_indicator (measurableSet_shell k)]
    simp_rw [hshellT x s k]
    rw [integral_const_mul]
  have hZ : ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ =
      ∑ x ∈ R, ∫ g, T x s g ∂μ := by
    refine hZsum.unique ?_
    convert hsum using 1
    funext k
    exact hshell_eq k
  have hterm : ∀ x ∈ R, D.eval (qs F s) * ∫ g, T x s g ∂μ = (P x).eval (qs F s) / qs F s ^ N x := by
    intro x hx
    rw [hTeq x hx s]
    exact hJeq x s hs
  rw [hZ, Finset.mul_sum, Finset.sum_congr rfl hterm, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hle : N x ≤ ∑ y ∈ R, N y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
  rw [eval_mul, eval_pow, eval_X, pow_sub₀ _ (qs_ne_zero s) hle]
  field_simp
  exact (mul_div_mul_right _ _ (pow_ne_zero _ (qs_ne_zero s))).symm

end Core

section Ideal

open Matrix GLnLocal Parabolic MeasureTheory Polynomial

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

/- English proof (translation)
Take `⟨s₀, D, hD0, hDn, hcore⟩` from `exists_zeta_core_natDegree hπ μ`. Use `set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef`. Establish `hc : c ≠ 0` using `qs_ne_zero _`. Use `set D' : ℂ[X] := D.comp (C c * X) with hD'def`. Establish `hD'0 : D'.eval 0 = 1` using `by simp [D', hD0]`.

Establish `hD'ne : D' ≠ 0` using `fun h => by rw [h, eval_zero] at hD'0; exact zero_ne_one hD'0`. Take `⟨ε, hε, hεD⟩` from `exists_eval_ne_zero hD'ne`. Take `⟨s₁, hs₁⟩` from `exists_re_of_norm_qs_lt (F := F) hε`. Establish `hre : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re → s₀ < (s + ((n : ℂ) - 1) / 2).re` using `fun s hs => by`. Use `(le_max_left _ _).trans_lt hs` as an intermediate fact.

Rewrite using `[re_shift]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDs : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re → D'.eval (qs F s) ≠ 0` using `fun s hs => hεD _ (qs_ne_zero s) (hs₁ s ((le_max_right _ _).trans_lt hs))`. Establish `hD'n : D'.natDegree ≤ n`. Use `natDegree_comp_le.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `⟨max (s₀ - ((n : ℝ) - 1) / 2) s₁, D', hD'0, hD'n, hDs, fun Φ hΦ v ℓ hℓ => ?_⟩` and prove the remaining obligations. Take `⟨hint, N, P, hP⟩` from `hcore Φ hΦ v ℓ hℓ`. Use `⟨fun s hs => hint _ (hre s hs), N, C (c ^ N)⁻¹ * P.comp (C c * X), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hx : qs F s ≠ 0` using `qs_ne_zero s`.

Establish `hDx` using `hDs s hs`. Establish `hQ : (X ^ N * D').eval (qs F s) ≠ 0`. Rewrite using `[eval_mul, eval_pow, eval_X]`. Conclude with `mul_ne_zero (pow_ne_zero _ hx) hDx`. Rewrite using `[eval_div_algebraMap _ _ hQ]`.

Establish `h1` using `hP _ (hre s hs)`. Rewrite `h1` using `[qs_add, ← hcdef]`. Establish `hDx' : D.eval (qs F s * c) ≠ 0`. Rewrite using `[mul_comm]`. Rewrite `hDx` using `[hD'def, eval_comp, eval_mul, eval_C, eval_X]`.

Conclude with `hDx`. Establish `h2` using `eq_div_of_mul_eq hDx' ((mul_comm _ _).trans h1)`. Rewrite using `[zetaIntegral, h2]`. Simplify using `only [D', eval_mul, eval_comp, eval_C, eval_X, eval_pow]`. Rewrite using `[mul_comm c (qs F s), mul_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_zeta_rat_natDegree [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ D.natDegree ≤ n ∧ (∀ s : ℂ, s₀ < s.re → D.eval (qs F s) ≠ 0) ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
        ℓ ∈ smoothVectors (Representation.dual π) →
        (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g (s + ((n : ℂ) - 1) / 2)) μ) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          zetaIntegral μ Φ (matrixCoeff π v ℓ) s =
            (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * D)).eval
              (RingHom.id ℂ) (qs F s) := by
  obtain ⟨s₀, D, hD0, hDn, hcore⟩ := exists_zeta_core_natDegree hπ μ
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  set D' : ℂ[X] := D.comp (C c * X) with hD'def
  have hD'0 : D'.eval 0 = 1 := by simp [D', hD0]
  have hD'ne : D' ≠ 0 := fun h => by rw [h, eval_zero] at hD'0; exact zero_ne_one hD'0
  obtain ⟨ε, hε, hεD⟩ := exists_eval_ne_zero hD'ne
  obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
  have hre : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re →
      s₀ < (s + ((n : ℂ) - 1) / 2).re := fun s hs => by
    have := (le_max_left _ _).trans_lt hs
    rw [re_shift]
    linarith
  have hDs : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re → D'.eval (qs F s) ≠ 0 :=
    fun s hs => hεD _ (qs_ne_zero s) (hs₁ s ((le_max_right _ _).trans_lt hs))
  have hD'n : D'.natDegree ≤ n := by
    refine natDegree_comp_le.trans ?_
    calc D.natDegree * (C c * X).natDegree ≤ D.natDegree * 1 :=
          Nat.mul_le_mul_left _ ((natDegree_C_mul_le c X).trans natDegree_X_le)
      _ ≤ n := by rw [mul_one]; exact hDn
  refine ⟨max (s₀ - ((n : ℝ) - 1) / 2) s₁, D', hD'0, hD'n, hDs, fun Φ hΦ v ℓ hℓ => ?_⟩
  obtain ⟨hint, N, P, hP⟩ := hcore Φ hΦ v ℓ hℓ
  refine ⟨fun s hs => hint _ (hre s hs), N, C (c ^ N)⁻¹ * P.comp (C c * X), fun s hs => ?_⟩
  have hx : qs F s ≠ 0 := qs_ne_zero s
  have hDx := hDs s hs
  have hQ : (X ^ N * D').eval (qs F s) ≠ 0 := by
    rw [eval_mul, eval_pow, eval_X]
    exact mul_ne_zero (pow_ne_zero _ hx) hDx
  rw [eval_div_algebraMap _ _ hQ]
  have h1 := hP _ (hre s hs)
  rw [qs_add, ← hcdef] at h1
  have hDx' : D.eval (qs F s * c) ≠ 0 := by
    rw [mul_comm]
    rw [hD'def, eval_comp, eval_mul, eval_C, eval_X] at hDx
    exact hDx
  have h2 := eq_div_of_mul_eq hDx' ((mul_comm _ _).trans h1)
  rw [zetaIntegral, h2]
  simp only [D', eval_mul, eval_comp, eval_C, eval_X, eval_pow]
  rw [mul_comm c (qs F s), mul_pow]
  field_simp

/- English proof (translation)
Take `⟨s₀, D, hD0, hDn, -, h⟩` from `exists_zeta_rat_natDegree hπ μ`. Use `⟨D, hD0, hDn, fun R hR => ?_⟩` and prove the remaining obligations. Take `⟨Φ, v, ℓ, hΦ, hℓ, s₁, hZ⟩` from `hR`. Take `⟨-, N, P, hP⟩` from `h Φ hΦ v ℓ hℓ`. Use `⟨N, P, ?_⟩` and prove the remaining obligations.

Take `⟨ε, hε, hεs⟩` from `exists_qs_of_small (F := F) (max s₀ s₁)`. Use `eq_of_eval_eq hε fun x hx hxε => ?_` and prove the remaining obligations. Take `⟨s, hs, rfl⟩` from `hεs x hx hxε`. Rewrite using `[← hZ s ((le_max_right _ _).trans_lt hs), hP s ((le_max_left _ _).trans_lt hs)]`.
-/
theorem exists_zetaSet_eq_natDegree [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] :
    ∃ D : ℂ[X], D.eval 0 = 1 ∧ D.natDegree ≤ n ∧ ∀ R ∈ zetaSet π μ, ∃ (N : ℕ) (P : ℂ[X]),
      R = algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * D) := by
  obtain ⟨s₀, D, hD0, hDn, -, h⟩ := exists_zeta_rat_natDegree hπ μ
  refine ⟨D, hD0, hDn, fun R hR => ?_⟩
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₁, hZ⟩ := hR
  obtain ⟨-, N, P, hP⟩ := h Φ hΦ v ℓ hℓ
  refine ⟨N, P, ?_⟩
  obtain ⟨ε, hε, hεs⟩ := exists_qs_of_small (F := F) (max s₀ s₁)
  refine eq_of_eval_eq hε fun x hx hxε => ?_
  obtain ⟨s, hs, rfl⟩ := hεs x hx hxε
  rw [← hZ s ((le_max_right _ _).trans_lt hs), hP s ((le_max_left _ _).trans_lt hs)]

/- English proof (translation)
Take `⟨D, hD0, hDn, hD⟩` from `exists_zetaSet_eq_natDegree hπ μ`. Establish `hDne : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]`. Introduce `h`. Rewrite `hD0` using `[h, eval_zero]`.

Conclude with `zero_ne_one hD0`. Use `⟨D, hD0, hDn, fun R hR => ?_⟩` and prove the remaining obligations. Use `Submodule.span_induction (p := fun R _ => algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) ?_ ?_ ?_ ?_ hR` and prove the remaining obligations. Introduce `R hR`. Take `⟨N, P, rfl⟩` from `hD R hR`.

Use `mem_laurentSubalgebra_iff.2 ⟨P, N, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, RatFunc.algebraMap_X]`. Establish `hX : (RatFunc.X : RatFunc ℂ) ≠ 0` using `RatFunc.X_ne_zero`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[mul_add]`. Conclude with `add_mem hx hy`. Introduce `c x _ hx`. Rewrite using `[mul_smul_comm]`.

Conclude with `Subalgebra.smul_mem _ hx c`.
-/
theorem exists_denominator_zetaIdeal_natDegree [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ D : ℂ[X], D.eval 0 = 1 ∧ D.natDegree ≤ n ∧
      ∀ R ∈ zetaIdeal π μ, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra := by
  obtain ⟨D, hD0, hDn, hD⟩ := exists_zetaSet_eq_natDegree hπ μ
  have hDne : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    intro h
    rw [h, eval_zero] at hD0
    exact zero_ne_one hD0
  refine ⟨D, hD0, hDn, fun R hR => ?_⟩
  refine Submodule.span_induction
    (p := fun R _ => algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) ?_ ?_ ?_ ?_ hR
  · intro R hR
    obtain ⟨N, P, rfl⟩ := hD R hR
    refine mem_laurentSubalgebra_iff.2 ⟨P, N, ?_⟩
    rw [map_mul, map_pow, RatFunc.algebraMap_X]
    have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    field_simp
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Subalgebra.smul_mem _ hx c

/- English proof (translation)
Take `⟨hP0, hP⟩` from `LPolynomial_spec hπ μ`. Establish `hmem : (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π))⁻¹ ∈ zetaIdeal π μ` using `(hP _).2 ⟨1, one_mem _, by rw [one_div]⟩`. Establish `hφD : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0` using `RatFunc.algebraMap_ne_zero hD0`. Use `dvd_of_inv_eq_laurent_div (by rw [hP0]; exact one_ne_zero) (hD _ hmem) ?_` and prove the remaining obligations. Rewrite using `[mul_div_cancel_left₀ _ hφD]`.
-/
theorem LPolynomial_dvd [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {D : ℂ[X]} (hD0 : D ≠ 0)
    (hD : ∀ R ∈ zetaIdeal π μ, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) :
    LPolynomial π ∣ D := by
  obtain ⟨hP0, hP⟩ := LPolynomial_spec hπ μ
  have hmem : (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π))⁻¹ ∈ zetaIdeal π μ :=
    (hP _).2 ⟨1, one_mem _, by rw [one_div]⟩
  have hφD : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := RatFunc.algebraMap_ne_zero hD0
  refine dvd_of_inv_eq_laurent_div (by rw [hP0]; exact one_ne_zero) (hD _ hmem) ?_
  rw [mul_div_cancel_left₀ _ hφD]

/- English proof (translation)
Take `⟨D, hD0, hDn, hD⟩` from `exists_denominator_zetaIdeal_natDegree hπ (Measure.haar : Measure (GL (Fin n) F))`. Establish `hDne : D ≠ 0` using `fun h => by rw [h, eval_zero] at hD0; exact zero_ne_one hD0`. Conclude with `(natDegree_le_of_dvd (LPolynomial_dvd hπ Measure.haar hDne hD) hDne).trans hDn`.
-/
theorem natDegree_LPolynomial_le [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π) :
    (LPolynomial π).natDegree ≤ n := by
  obtain ⟨D, hD0, hDn, hD⟩ :=
    exists_denominator_zetaIdeal_natDegree hπ (Measure.haar : Measure (GL (Fin n) F))
  have hDne : D ≠ 0 := fun h => by rw [h, eval_zero] at hD0; exact zero_ne_one hD0
  exact (natDegree_le_of_dvd (LPolynomial_dvd hπ Measure.haar hDne hD) hDne).trans hDn

end Ideal

end GodementJacquet

end GroundTheory.Automorphic
