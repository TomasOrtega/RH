import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnits
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

/- English proof (translation)
Set `σ' : E ≃ₐ[FixedPoints.subfield G E] E` to `AlgEquiv.ofRingEquiv (f := σ) fun x => h x x.2`. Take `⟨g, hg⟩` from `FixedPoints.toAlgAut_surjective G E σ'`. Use `⟨g, fun x => ?_⟩` and prove the remaining obligations. Conclude with `DFunLike.congr_fun hg x`.
-/
private theorem exists_of_fixed {E : Type} [Field E] (G : Type) [Group G] [Finite G] [MulSemiringAction G E] (σ : E ≃+* E)
    (h : ∀ x ∈ FixedPoints.subfield G E, σ x = x) : ∃ g : G, ∀ x : E, g • x = σ x := by
  let σ' : E ≃ₐ[FixedPoints.subfield G E] E := AlgEquiv.ofRingEquiv (f := σ) fun x => h x x.2
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective G E σ'
  refine ⟨g, fun x => ?_⟩
  exact DFunLike.congr_fun hg x

/- English proof (translation)
Introduce `Ω _ _ _ ε X H' M hM hle γ hγ`. Establish `hfin : Finite (H'.map (GlobalTheory.KZ.FracGen.rhoF X M))` using `by haveI := GlobalTheory.KZ.FracGen.finite_range X M hM`. Establish `hr : H'.map (GlobalTheory.KZ.FracGen.rhoF X M) ≤ (GlobalTheory.KZ.FracGen.rhoF X M).range`. Introduce and unpack `_ ⟨δ, -, rfl⟩`. Conclude with `⟨δ, rfl⟩`.

Conclude with `Finite.of_injective _ (Subgroup.inclusion_injective hr)`. Take `⟨s, hs⟩` from `exists_of_fixed (H'.map (GlobalTheory.KZ.FracGen.rhoF X M)) (GlobalTheory.KZ.FracGen.rhoF X M γ⁻¹).toRingEquiv (by`. Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show X.sl (ofSL γ⁻¹⁻¹) x = x`.

Rewrite using `[inv_inv]`. Use `hγ _ ((mem_lev_iff X H' _).2 fun δ hδ => ?_)` and prove the remaining obligations. Establish `h1` using `hx ⟨GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹, ⟨δ⁻¹, inv_mem hδ, rfl⟩⟩`. Establish `h2` using `congrArg Subtype.val h1`. Establish `h3 : ((GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹ x : GlobalTheory.KZ.FracGen.FM X M) : X.K) = X.sl (ofSL δ⁻¹⁻¹) x` using `GlobalTheory.KZ.FracGen.rhoF_apply X M δ⁻¹ x`.

Rewrite `h3` using `[inv_inv]`. Rewrite using `[← h3]`. Conclude with `h2)`. Take `⟨_, ⟨δ, hδ, rfl⟩⟩` from `s`. Establish `hact : ∀ x : GlobalTheory.KZ.FracGen.FM X M, X.sl (ofSL δ⁻¹) x = X.sl (ofSL γ) x`.

Introduce `x`. Establish `h1` using `congrArg Subtype.val (hs x)`. Establish `h2` using `GlobalTheory.KZ.FracGen.rhoF_apply X M δ x`. Establish `h3` using `GlobalTheory.KZ.FracGen.rhoF_apply X M γ⁻¹ x`. Rewrite `h3` using `[inv_inv]`.

Rewrite using `[← h2, ← h3]`. Conclude with `h1`. Establish `hc1 : 1 < 6 * M + 1` using `by omega`. Establish `hc6 : Nat.Coprime (6 * M + 1) 6` using `by simp`. Establish `hcM : 6 * M + 1 ≡ 1 [MOD M]`.

Simplify using `[Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]`. Establish `hfix : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) → X.sl (ofSL (δ⁻¹ * γ⁻¹)) (siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M]) = siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M]`. Introduce `a b hab`. Establish `hmem` using `(GlobalTheory.KZ.FracGen.mem_FM X M _).2 (GlobalTheory.KZ.FracGen.siegel_inv X M _ hM hc1 hc6 hcM a b hab)`. Establish `h1` using `hact ⟨_, hmem⟩`.

Rewrite using `[map_mul, X.sl_mul]`. Use `(congrArg (X.sl (ofSL γ⁻¹)) h1).trans ?_` and prove the remaining obligations. Rewrite using `[← X.sl_mul, ← map_mul, mul_inv_cancel, map_one]`. Conclude with `X.sl_one _`. Break down `GlobalTheory.T.siegel_invariance_implies_congruence ε X M (6 * M + 1) (δ⁻¹ * γ⁻¹) hM hc1 hc6 hcM hfix with h | h` into its components or cases.

Use `left`. Establish `e : γ = (δ * (δ⁻¹ * γ⁻¹))⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `inv_mem (mul_mem hδ (hle h))`. Use `right`.

Establish `e : -γ = (δ * -(δ⁻¹ * γ⁻¹))⁻¹`. Rewrite using `[mul_neg, inv_neg]`. Use `congr 1`. Use `group`. Rewrite using `[e]`.

Conclude with `inv_mem (mul_mem hδ (hle h))`.
-/
theorem UpperTheory.Kd.K4.faith :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ H' → ∀ γ : SL(2, ℤ), (∀ f ∈ lev X H', X.sl (ofSL γ) f = f) → γ ∈ H' ∨ -γ ∈ H' := by
  intro Ω _ _ _ ε X H' M hM hle γ hγ
  have hfin : Finite (H'.map (GlobalTheory.KZ.FracGen.rhoF X M)) := by
    haveI := GlobalTheory.KZ.FracGen.finite_range X M hM
    have hr : H'.map (GlobalTheory.KZ.FracGen.rhoF X M) ≤ (GlobalTheory.KZ.FracGen.rhoF X M).range := by
      rintro _ ⟨δ, -, rfl⟩
      exact ⟨δ, rfl⟩
    exact Finite.of_injective _ (Subgroup.inclusion_injective hr)
  obtain ⟨s, hs⟩ := exists_of_fixed (H'.map (GlobalTheory.KZ.FracGen.rhoF X M))
    (GlobalTheory.KZ.FracGen.rhoF X M γ⁻¹).toRingEquiv (by
      intro x hx
      apply Subtype.ext
      show X.sl (ofSL γ⁻¹⁻¹) x = x
      rw [inv_inv]
      refine hγ _ ((mem_lev_iff X H' _).2 fun δ hδ => ?_)
      have h1 := hx ⟨GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹, ⟨δ⁻¹, inv_mem hδ, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      have h3 : ((GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹ x : GlobalTheory.KZ.FracGen.FM X M) : X.K) = X.sl (ofSL δ⁻¹⁻¹) x :=
        GlobalTheory.KZ.FracGen.rhoF_apply X M δ⁻¹ x
      rw [inv_inv] at h3
      rw [← h3]
      exact h2)
  obtain ⟨_, ⟨δ, hδ, rfl⟩⟩ := s

  have hact : ∀ x : GlobalTheory.KZ.FracGen.FM X M, X.sl (ofSL δ⁻¹) x = X.sl (ofSL γ) x := by
    intro x
    have h1 := congrArg Subtype.val (hs x)
    have h2 := GlobalTheory.KZ.FracGen.rhoF_apply X M δ x
    have h3 := GlobalTheory.KZ.FracGen.rhoF_apply X M γ⁻¹ x
    rw [inv_inv] at h3
    rw [← h2, ← h3]
    exact h1
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by simp
  have hcM : 6 * M + 1 ≡ 1 [MOD M] := by
    simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
  have hfix : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) →
      X.sl (ofSL (δ⁻¹ * γ⁻¹)) (siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M]) =
        siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M] := by
    intro a b hab
    have hmem := (GlobalTheory.KZ.FracGen.mem_FM X M _).2 (GlobalTheory.KZ.FracGen.siegel_inv X M _ hM hc1 hc6 hcM a b hab)
    have h1 := hact ⟨_, hmem⟩
    rw [map_mul, X.sl_mul]
    refine (congrArg (X.sl (ofSL γ⁻¹)) h1).trans ?_
    rw [← X.sl_mul, ← map_mul, mul_inv_cancel, map_one]
    exact X.sl_one _
  rcases GlobalTheory.T.siegel_invariance_implies_congruence ε X M (6 * M + 1) (δ⁻¹ * γ⁻¹) hM hc1 hc6 hcM hfix with h | h
  · left
    have e : γ = (δ * (δ⁻¹ * γ⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem (mul_mem hδ (hle h))
  · right
    have e : -γ = (δ * -(δ⁻¹ * γ⁻¹))⁻¹ := by
      rw [mul_neg, inv_neg]
      congr 1
      group
    rw [e]
    exact inv_mem (mul_mem hδ (hle h))
