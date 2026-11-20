import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeightStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGLStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped NNReal

namespace GlobalTheory.RatCount

/- English proof (translation)
Take `⟨C0, k, hk⟩` from `hA F E`. Take `⟨c, a, ha⟩` from `hB F E`. Use `⟨C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)), a * k * (N * N), fun T hT => ?_⟩` and prove the remaining obligations. Use `set B : ℝ := max 1 c * T ^ a with hBdef`. Establish `hB1 : 1 ≤ B` using `one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hT)`.

Take `⟨hXf, hXc⟩` from `hk B hB1`. Use `set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef`. Use `set S := {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T} with hSdef`. Establish `hmem : ∀ γ ∈ S, ∀ p : Fin N × Fin N, (γ : Matrix (Fin N) (Fin N) E) p.1 p.2 ∈ X`. Introduce `γ hγ p j`.

Use `(ha _ j).trans ?_` and prove the remaining obligations. Establish `h1 : (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ≤ T` using `(NNReal.coe_le_coe.2 (hC F E N γ p.1 p.2)).trans hγ`. Combine the equalities or inequalities in the displayed calculation. Set `f : GL (Fin N) E → (Fin N × Fin N → E)` to `fun γ p => (γ : Matrix (Fin N) (Fin N) E) p.1 p.2`. Establish `hinj : Set.InjOn f S` using `fun γ _ δ _ h => Units.ext (Matrix.ext fun i j => congrFun h (i, j))`.

Use `set P : Finset (Fin N × Fin N → E) := Fintype.piFinset fun _ => hXf.toFinset with hPdef`. Establish `hmaps : ∀ γ ∈ S, f γ ∈ (P : Set (Fin N × Fin N → E))` using `fun γ hγ => by`. Simplify using `only [P, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]`. Conclude with `fun p => hmem γ hγ p`. Establish `hSf : S.Finite` using `Set.Finite.of_finite_image ((P.finite_toSet).subset (by`.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `hmaps γ hγ)) hinj`. Use `⟨hSf, ?_⟩` and prove the remaining obligations. Establish `h1 : S.ncard ≤ (P : Set (Fin N × Fin N → E)).ncard` using `Set.ncard_le_ncard_of_injOn f hmaps hinj P.finite_toSet`. Rewrite `h1` using `[Set.ncard_coe_finset, hPdef, Fintype.card_piFinset]`.

Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1`. Rewrite `h1` using `[← Set.ncard_eq_toFinset_card X hXf]`. Establish `hC0 : 0 ≤ C0`. Use `(Nat.cast_nonneg (α := ℝ) _).trans hXc` as an intermediate fact. Conclude with `nonneg_of_mul_nonneg_left this (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hBdef]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gl_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ))
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.Finite ∧
      (({γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C0, k, hk⟩ := hA F E
  obtain ⟨c, a, ha⟩ := hB F E
  refine ⟨C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)), a * k * (N * N), fun T hT => ?_⟩
  set B : ℝ := max 1 c * T ^ a with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hT)
  obtain ⟨hXf, hXc⟩ := hk B hB1
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set S := {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T} with hSdef
  have hmem : ∀ γ ∈ S, ∀ p : Fin N × Fin N, (γ : Matrix (Fin N) (Fin N) E) p.1 p.2 ∈ X := by
    intro γ hγ p j
    refine (ha _ j).trans ?_
    have h1 : (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ≤ T :=
      (NNReal.coe_le_coe.2 (hC F E N γ p.1 p.2)).trans hγ
    calc c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a
        ≤ max 1 c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 a)
          (zero_le_one.trans (le_max_left _ _))
  let f : GL (Fin N) E → (Fin N × Fin N → E) := fun γ p => (γ : Matrix (Fin N) (Fin N) E) p.1 p.2
  have hinj : Set.InjOn f S := fun γ _ δ _ h => Units.ext (Matrix.ext fun i j => congrFun h (i, j))
  set P : Finset (Fin N × Fin N → E) := Fintype.piFinset fun _ => hXf.toFinset with hPdef
  have hmaps : ∀ γ ∈ S, f γ ∈ (P : Set (Fin N × Fin N → E)) := fun γ hγ => by
    simp only [P, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun p => hmem γ hγ p
  have hSf : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset (by
    rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj
  refine ⟨hSf, ?_⟩
  have h1 : S.ncard ≤ (P : Set (Fin N × Fin N → E)).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj P.finite_toSet
  rw [Set.ncard_coe_finset, hPdef, Fintype.card_piFinset] at h1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  rw [← Set.ncard_eq_toFinset_card X hXf] at h1
  have hC0 : 0 ≤ C0 := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans hXc
    exact nonneg_of_mul_nonneg_left this (by positivity)
  calc ((S.ncard : ℕ) : ℝ) ≤ ((X.ncard : ℝ)) ^ (N * N) := by exact_mod_cast h1
    _ ≤ (C0 * B ^ k) ^ (N * N) := pow_le_pow_left₀ (by positivity) hXc _
    _ = C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)) * T ^ (a * k * (N * N)) := by
        rw [hBdef]; ring

/- English proof (translation)
Take `⟨C, A, h⟩` from `gl_count hA hB hC D.host.F D.host.E V.rank`. Use `⟨C, A, fun T hT => ?_⟩` and prove the remaining obligations. Take `⟨hf, hc⟩` from `h T hT`. Establish `hex : ∀ γ : GQ V, ∃ δ : GL (Fin V.rank) D.host.E, bc (inclR (F` using `D.host.F) (AF D.host.F)) δ = matHom V (γ : GA D V) := by`. Introduce `γ`.

Establish `h1` using `γ.2`. Simplify using `only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf, Subgroup.mem_map] at h1`. Take `⟨δ, -, hδ⟩` from `h1`. Conclude with `⟨δ, hδ⟩`. Use `choose φ hφ using hex`.

Establish `hmaps : ∀ γ ∈ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}, φ γ ∈ {δ : GL (Fin V.rank) D.host.E | (heightGL D.host.F (bc (inclR (F` using `D.host.F) (AF D.host.F)) δ) : ℝ) ≤ T} := by`. Introduce `γ hγ`. Simplify using `only [Set.mem_setOf_eq] at hγ ⊢`. Rewrite using `[hφ]`. Conclude with `hγ`.

Establish `hinj : Set.InjOn φ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}`. Introduce `a _ b _ hab`. Establish `h2 : matHom V (a : GA D V) = matHom V (b : GA D V)` using `by rw [← hφ, ← hφ, hab]`. Unfold `Formalism.L2.Theta.matHom at h2`. Conclude with `Subtype.ext (Subgroup.subtype_injective _ h2)`.

Use `⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩` and prove the remaining obligations. Conclude with `(Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)).trans hc`.
-/
theorem gq_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ)) {D : D7} (V : HSp D) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.Finite ∧
      (({γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C, A, h⟩ := gl_count hA hB hC D.host.F D.host.E V.rank
  refine ⟨C, A, fun T hT => ?_⟩
  obtain ⟨hf, hc⟩ := h T hT
  have hex : ∀ γ : GQ V, ∃ δ : GL (Fin V.rank) D.host.E,
      bc (inclR (F := D.host.F) (AF D.host.F)) δ = matHom V (γ : GA D V) := by
    intro γ
    have h1 := γ.2
    simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf, Subgroup.mem_map] at h1
    obtain ⟨δ, -, hδ⟩ := h1
    exact ⟨δ, hδ⟩
  choose φ hφ using hex
  have hmaps : ∀ γ ∈ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T},
      φ γ ∈ {δ : GL (Fin V.rank) D.host.E | (heightGL D.host.F (bc (inclR (F := D.host.F) (AF D.host.F)) δ) : ℝ) ≤ T} := by
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    rw [hφ]
    exact hγ
  have hinj : Set.InjOn φ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T} := by
    intro a _ b _ hab
    have h2 : matHom V (a : GA D V) = matHom V (b : GA D V) := by rw [← hφ, ← hφ, hab]
    unfold Formalism.L2.Theta.matHom at h2
    exact Subtype.ext (Subgroup.subtype_injective _ h2)
  refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
  exact (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)).trans hc

/- English proof (translation)
Introduce `D V Ω hΩ`. Take `⟨C, A, hcount⟩` from `gq_count GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL V`. Establish `hK : IsCompact ((fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω))` using `(hΩ.prod hΩ).image (by fun_prop)`. Take `⟨C₀, hC₀⟩` from `GlobalTheory.Grow.exists_height_le_of_isCompact V hK`. Establish `hC : 0 ≤ C`.

Use `(Nat.cast_nonneg (α := ℝ) _).trans (hcount 1 le_rfl).2` as an intermediate fact. Simplify using `using this`. Use `⟨A, C * max C₀ 1 ^ A, fun g x => ?_⟩` and prove the remaining obligations. Break down `Set.eq_empty_or_nonempty {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} with hS | ⟨γ₀, hγ₀⟩` into its components or cases. Rewrite using `[hS]`.

Use `⟨Set.finite_empty, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.ncard_empty, Nat.cast_zero]`. Use `GlobalTheory.Grow.height_pos V g` as an intermediate fact. Check the signs of the components of the expression. Use `set T : ℝ := max C₀ 1 * GlobalTheory.Grow.height V g ^ 2 with hTdef`.

Establish `hT : 1 ≤ T` using `one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ (GlobalTheory.Grow.one_le_height V g))`. Take `⟨hf, hc⟩` from `hcount T hT`. Set `φ : GQ V → GQ V` to `fun γ => γ * γ₀⁻¹`. Take `⟨y₀, hy₀, e₀⟩` from `hγ₀`. Establish `hmaps : ∀ γ ∈ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}, φ γ ∈ {δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T}`.

Introduce `γ hγ`. Take `⟨y, hy, e⟩` from `hγ`. Establish `h1 : ((φ γ : GQ V) : GA D V) = g * (y * y₀⁻¹) * g⁻¹`. Establish `e' : (γ : GA D V) = g * y * x⁻¹`. Rewrite using `[show g * y = (γ : GA D V) * x from e, mul_inv_cancel_right]`.

Establish `e₀' : (γ₀ : GA D V) = g * y₀ * x⁻¹`. Rewrite using `[show g * y₀ = (γ₀ : GA D V) * x from e₀, mul_inv_cancel_right]`. Simplify using `only [φ, Subgroup.coe_mul, Subgroup.coe_inv, e', e₀']`. Use `group`. Establish `hyy : GlobalTheory.Grow.height V (y * y₀⁻¹) ≤ max C₀ 1` using `(hC₀ _ ⟨(y, y₀), ⟨hy, hy₀⟩, rfl⟩).trans (le_max_left _ _)`.

Use `show GlobalTheory.Grow.height V ((φ γ : GQ V) : GA D V) ≤ T`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[GlobalTheory.Grow.height_inv]`. Use `GlobalTheory.Grow.height_pos V g` as an intermediate fact.

Use `gcongr`. Use `_ = T := by rw [hTdef]; ring`. Establish `hinj : Set.InjOn φ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}` using `fun a _ b _ hab => mul_right_cancel hab`. Use `⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ncard_rat_mem_translate_le : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  intro D V Ω hΩ
  obtain ⟨C, A, hcount⟩ := gq_count GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL V
  have hK : IsCompact ((fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω)) :=
    (hΩ.prod hΩ).image (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  have hC : 0 ≤ C := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans (hcount 1 le_rfl).2
    simpa using this
  refine ⟨A, C * max C₀ 1 ^ A, fun g x => ?_⟩
  rcases Set.eq_empty_or_nonempty {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} with hS | ⟨γ₀, hγ₀⟩
  · rw [hS]
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero]
    have := GlobalTheory.Grow.height_pos V g
    positivity
  · set T : ℝ := max C₀ 1 * GlobalTheory.Grow.height V g ^ 2 with hTdef
    have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (one_le_pow₀ (GlobalTheory.Grow.one_le_height V g))
    obtain ⟨hf, hc⟩ := hcount T hT
    let φ : GQ V → GQ V := fun γ => γ * γ₀⁻¹
    obtain ⟨y₀, hy₀, e₀⟩ := hγ₀
    have hmaps : ∀ γ ∈ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω},
        φ γ ∈ {δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T} := by
      intro γ hγ
      obtain ⟨y, hy, e⟩ := hγ
      have h1 : ((φ γ : GQ V) : GA D V) = g * (y * y₀⁻¹) * g⁻¹ := by
        have e' : (γ : GA D V) = g * y * x⁻¹ := by
          rw [show g * y = (γ : GA D V) * x from e, mul_inv_cancel_right]
        have e₀' : (γ₀ : GA D V) = g * y₀ * x⁻¹ := by
          rw [show g * y₀ = (γ₀ : GA D V) * x from e₀, mul_inv_cancel_right]
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, e', e₀']
        group
      have hyy : GlobalTheory.Grow.height V (y * y₀⁻¹) ≤ max C₀ 1 :=
        (hC₀ _ ⟨(y, y₀), ⟨hy, hy₀⟩, rfl⟩).trans (le_max_left _ _)
      show GlobalTheory.Grow.height V ((φ γ : GQ V) : GA D V) ≤ T
      rw [h1]
      calc GlobalTheory.Grow.height V (g * (y * y₀⁻¹) * g⁻¹)
          ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height V (y * y₀⁻¹) * GlobalTheory.Grow.height V g⁻¹ :=
            (GlobalTheory.Grow.height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.Grow.height_mul_le V _ _)
              (GlobalTheory.Grow.height_pos V _).le)
        _ ≤ GlobalTheory.Grow.height V g * max C₀ 1 * GlobalTheory.Grow.height V g := by
            rw [GlobalTheory.Grow.height_inv]
            have := GlobalTheory.Grow.height_pos V g
            gcongr
        _ = T := by rw [hTdef]; ring
    have hinj : Set.InjOn φ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} :=
      fun a _ b _ hab => mul_right_cancel hab
    refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
    calc (({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℕ) : ℝ)
        ≤ (({δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T}.ncard : ℕ) : ℝ) :=
          Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)
      _ ≤ C * T ^ A := hc
      _ = C * max C₀ 1 ^ A * GlobalTheory.Grow.height V g ^ (2 * A) := by rw [hTdef]; ring

end GlobalTheory.RatCount
