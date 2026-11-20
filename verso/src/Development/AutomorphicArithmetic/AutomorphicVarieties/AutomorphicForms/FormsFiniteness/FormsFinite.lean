import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicSaturationSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfBddCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceTypesOfBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceCentreOfBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceAutomorphicProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgebraicModuleOfVanishingBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SiegelLeviBlockAevalStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfFiniteDimensionalLeviSlices

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨ψ, hψ, g, hg, hf⟩` from `hf`. Introduce `γ m`.

Rewrite using `[hf, hf, h ψ hψ g hg]`. Consider the case `zero => exact isLeftInvariant_zero`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `smul c x _ hx => exact hx.smul c`.
-/
private theorem slLeft {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

/- English proof (translation)
Take `⟨ι, _, ⟨D⟩⟩` from `UpperTheory.exists_idempotent_decomposition_mixedSpace K`. Take `⟨hN, hG, hL, hSat, hinv⟩` from `UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK`. Establish `hT` using `UpperTheory.constantTermSpace_types_of_bdd K (r + s) r S hS`. Establish `hC` using `UpperTheory.constantTermSpace_centre_of_bdd K (r + s) r S hS`. Establish `hcap` using `UpperTheory.algebraic_module_of_vanishing_block K r s (ctSp r S) hN hC ι D`.

Establish `hb1 : ∀ γ : GL (Fin r) K, emb (e1 r s) γ = blk γ (1 : GL (Fin s) K)`. Introduce `γ`. Simplify using `[blk]`. Establish `hb2 : ∀ γ : GL (Fin s) K, emb (e2 r s) γ = blk (1 : GL (Fin r) K) γ`. Introduce `γ`.

Simplify using `[blk]`. Use `UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices K r s (ctSp r S) hN hSat hL hT ?_ ?_` and prove the remaining obligations. Use `h₁ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).1 hG, (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K r (r + s) (e1 r s) _ _ hT, ?_⟩` and prove the remaining obligations. Apply `slLeft` to reduce the goal to its premises. Introduce and unpack `ψ hψ _ ⟨m₂, rfl⟩ γ m`.

Rewrite using `[map_mul, ← mul_assoc, ← emb_comm, mul_assoc, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K r (r + s) (e1 r s)).2.1 γ, hb1, hinv ψ hψ]`. Use `UpperTheory.siegelLevi_block_aeval_stable K r (r + s) (e1 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).1)` and prove the remaining obligations. Introduce and unpack `ψ hψ _ ⟨m₂, rfl⟩ m`. Rewrite using `[← emb_comm]`. Conclude with `hψ m m₂`.

Use `h₂ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).1 hG, (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K s (r + s) (e2 r s) _ _ hT, ?_⟩` and prove the remaining obligations. Apply `slLeft` to reduce the goal to its premises. Introduce and unpack `ψ hψ _ ⟨m₁, rfl⟩ γ m`. Rewrite using `[map_mul, ← mul_assoc, emb_comm m₁ (AdelicGLn.diagonal K s γ), mul_assoc, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K s (r + s) (e2 r s)).2.1 γ, hb2, hinv ψ hψ]`. Use `UpperTheory.siegelLevi_block_aeval_stable K s (r + s) (e2 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).2)` and prove the remaining obligations.

Introduce and unpack `ψ hψ _ ⟨m₁, rfl⟩ m`. Conclude with `hψ m₁ m`.
-/
theorem ctFin {r s : ℕ} (h₁ : FinAt K r) (h₂ : FinAt K s) {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S)
    (hK : Sat S) : FiniteDimensional ℂ (ctSp r S) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hSat, hinv⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K (r + s) r S hS
  have hC := UpperTheory.constantTermSpace_centre_of_bdd K (r + s) r S hS
  have hcap := UpperTheory.algebraic_module_of_vanishing_block K r s (ctSp r S) hN hC ι D
  have hb1 : ∀ γ : GL (Fin r) K, emb (e1 r s) γ = blk γ (1 : GL (Fin s) K) := by
    intro γ
    simp [blk]
  have hb2 : ∀ γ : GL (Fin s) K, emb (e2 r s) γ = blk (1 : GL (Fin r) K) γ := by
    intro γ
    simp [blk]
  refine UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices K r s (ctSp r S) hN hSat hL hT ?_ ?_
  · refine h₁ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K r (r + s) (e1 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, ← emb_comm, mul_assoc, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K r (r + s) (e1 r s)).2.1 γ, hb1,
        hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K r (r + s) (e1 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).1)
      rintro ψ hψ _ ⟨m₂, rfl⟩ m
      rw [← emb_comm]
      exact hψ m m₂
  · refine h₂ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K s (r + s) (e2 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, emb_comm m₁ (AdelicGLn.diagonal K s γ), mul_assoc,
        (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K s (r + s) (e2 r s)).2.1 γ, hb2, hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K s (r + s) (e2 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).2)
      rintro ψ hψ _ ⟨m₁, rfl⟩ m
      exact hψ m₁ m

/- English proof (translation)
Apply `Module.rank_lt_aleph0_iff.mp` to reduce the goal to its premises. Rewrite using `[← LinearMap.rank_range_add_rank_ker f]`. Conclude with `Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 ℂ _) (Module.rank_lt_aleph0 ℂ _)`.
-/
private theorem fin_of_ker {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (h1 : FiniteDimensional ℂ (LinearMap.range f)) (h2 : FiniteDimensional ℂ (LinearMap.ker f)) :
    FiniteDimensional ℂ M := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [← LinearMap.rank_range_add_rank_ker f]
  exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 ℂ _) (Module.rank_lt_aleph0 ℂ _)

/- English proof (translation)
Introduce `S hS`. Take `⟨S', hSS', hB', hSat'⟩` from `UpperTheory.exists_automorphic_saturation_submodule K n S hS`. Establish `hct : ∀ r, 0 < r → r < n → FiniteDimensional ℂ (ctSp r S')`. Introduce `r hr0 hrn`. Take `⟨s, rfl⟩` from `Nat.exists_eq_add_of_le hrn.le`.

Conclude with `ctFin (ih r hrn) (ih s (by omega)) hB' hSat'`. Use `choose F hF1 _ using fun r => UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r`. Set `ι : S' →ₗ[ℂ] automorphicForms K n` to `LinearMap.codRestrict _ ((archSmooth K n).subtype ∘ₗ S'.subtype) (fun φ => UpperTheory.isAutomorphicForm_of_bdd_submodule K n S' hB' φ.1 φ.2)`. Set `I` to `{r : Fin n // 0 < r.val}`. Establish `hmem : ∀ (i : I) (φ : S'), F i.1.val (ι φ) ∈ ctSp i.1.val S'` using `fun i φ => Submodule.subset_span ⟨φ.1, φ.2, hF1 _ _⟩`.

Set `G : S' →ₗ[ℂ] ((i : I) → ctSp i.1.val S')` to `LinearMap.pi (fun i => LinearMap.codRestrict _ ((F i.1.val).comp ι) (hmem i))`. Use `haveI : ∀ i : I, FiniteDimensional ℂ (ctSp i.1.val S') := fun i => hct _ i.2 i.1.2`. Use `haveI : FiniteDimensional ℂ S' := by`. Use `fin_of_ker G inferInstance ?_` and prove the remaining obligations. Establish `hW : FiniteDimensional ℂ ((LinearMap.ker G).map S'.subtype)`.

Use `UpperTheory.finiteDimensional_of_bdd_cuspidal K n _ (hB'.mono (Submodule.map_subtype_le _ _)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ r hr0 hrn g`. Establish `h0 : F r (ι x) = 0`. Use `congrFun (LinearMap.mem_ker.mp hx) ⟨⟨r, hrn⟩, hr0⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`.

Establish `h1` using `congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) g) h0`. Simplify using `only [hF1] at h1`. Conclude with `h1`. Conclude with `LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ S'.injective_subtype _).symm`. Conclude with `Submodule.finiteDimensional_of_le hSS'`.
-/
theorem finAt_of {n : ℕ} (ih : ∀ m < n, FinAt K m) : FinAt K n := by
  intro S hS
  obtain ⟨S', hSS', hB', hSat'⟩ := UpperTheory.exists_automorphic_saturation_submodule K n S hS
  have hct : ∀ r, 0 < r → r < n → FiniteDimensional ℂ (ctSp r S') := by
    intro r hr0 hrn
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn.le
    exact ctFin (ih r hrn) (ih s (by omega)) hB' hSat'
  choose F hF1 _ using fun r => UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r
  let ι : S' →ₗ[ℂ] automorphicForms K n :=
    LinearMap.codRestrict _ ((archSmooth K n).subtype ∘ₗ S'.subtype)
      (fun φ => UpperTheory.isAutomorphicForm_of_bdd_submodule K n S' hB' φ.1 φ.2)
  let I := {r : Fin n // 0 < r.val}
  have hmem : ∀ (i : I) (φ : S'), F i.1.val (ι φ) ∈ ctSp i.1.val S' := fun i φ =>
    Submodule.subset_span ⟨φ.1, φ.2, hF1 _ _⟩
  let G : S' →ₗ[ℂ] ((i : I) → ctSp i.1.val S') :=
    LinearMap.pi (fun i => LinearMap.codRestrict _ ((F i.1.val).comp ι) (hmem i))
  haveI : ∀ i : I, FiniteDimensional ℂ (ctSp i.1.val S') := fun i => hct _ i.2 i.1.2
  haveI : FiniteDimensional ℂ S' := by
    refine fin_of_ker G inferInstance ?_
    have hW : FiniteDimensional ℂ ((LinearMap.ker G).map S'.subtype) := by
      refine UpperTheory.finiteDimensional_of_bdd_cuspidal K n _ (hB'.mono (Submodule.map_subtype_le _ _)) ?_
      rintro _ ⟨x, hx, rfl⟩ r hr0 hrn g
      have h0 : F r (ι x) = 0 := by
        have := congrFun (LinearMap.mem_ker.mp hx) ⟨⟨r, hrn⟩, hr0⟩
        exact congrArg Subtype.val this
      have h1 := congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) g) h0
      simp only [hF1] at h1
      exact h1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ S'.injective_subtype _).symm
  exact Submodule.finiteDimensional_of_le hSS'

/- English proof (translation)
Introduce `_ _ _ n` and use `Nat.strong_induction_on n fun _ ih => finAt_of ih`.
-/
theorem formsFinite : FormsFinite := fun _ _ _ n => Nat.strong_induction_on n fun _ ih => finAt_of ih

end UpperTheory.V.Af.Fin
