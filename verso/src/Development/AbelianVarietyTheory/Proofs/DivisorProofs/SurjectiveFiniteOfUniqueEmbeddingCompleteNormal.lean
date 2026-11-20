import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open IsLocalRing

namespace GlobalTheory.DegreeOne

/- English proof (translation)
Introduce `B R _ _ _ _ _ _ _ _ _ ψ hB hinj hfin huniq`. Use `haveI := hB`. Use `letI : Algebra B R := ψ.toAlgebra`. Use `haveI : Module.Finite B R := hfin`. Use `haveI : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R`.

Use `haveI : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).2 hinj`. Use `haveI : CharZero B := ⟨fun m n h => Nat.cast_injective (R := R) (by simpa only [map_natCast] using congrArg ψ h)⟩`. Set `K` to `FractionRing B`. Set `M` to `FractionRing R`. Establish `hBM : Function.Injective (algebraMap B M)`.

Rewrite using `[IsScalarTower.algebraMap_eq B R M]`. Conclude with `(IsFractionRing.injective R M).comp hinj`. Use `haveI : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).2 hBM`. Use `letI : Algebra K M := FractionRing.liftAlgebra B M`. Use `haveI : IsScalarTower B K M := FractionRing.isScalarTower_liftAlgebra B M`.

Use `haveI : Module.Finite K M := Module.Finite.of_isLocalization B R (Rₚ := K) (Sₚ := M) (nonZeroDivisors B)`. Use `haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing B (K := K)`. Set `Ω` to `AlgebraicClosure M`. Set `L` to `IntermediateField.normalClosure K M Ω`. Use `haveI : FiniteDimensional K L := normalClosure.is_finiteDimensional K M Ω`.

Use `haveI : IsScalarTower B K Ω := inferInstance`. Use `haveI : IsScalarTower B K L := inferInstance`. Use `haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective`. Set `C` to `integralClosure B L`. Use `haveI : Module.Finite B C := IsIntegralClosure.finite B K L C`.

Use `haveI : IsLocalRing C := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := B) C`. Use `haveI : IsNoetherianRing C := IsNoetherianRing.of_finite B C`. Use `haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K`. Use `haveI : CharZero C := ⟨fun m n h => Nat.cast_injective (R := L) (by simpa using congrArg Subtype.val h)⟩`. Establish `hCc : IsAdicComplete (maximalIdeal C) C` using `CompleteFiniteExtension.isAdicComplete_of_finite_local B C`.

Establish `hK : ∀ b : B, algebraMap K L (algebraMap B K b) = algebraMap B L b` using `fun b => (IsScalarTower.algebraMap_apply B K L b).symm`. Establish `key : ∀ σ : M →ₐ[K] Ω, ∃ f : R →+* C, Function.Injective f ∧ IsLocalHom f ∧ f.comp ψ = algebraMap B C ∧ ∀ r, ((f r : L) : Ω) = σ (algebraMap R M r)`. Introduce `σ`. Establish `hmem : ∀ x, (σ.toRingHom.comp (algebraMap R M)) x ∈ L` using `fun x => σ.fieldRange_le_normalClosure ⟨_, rfl⟩`. Set `g₀ : R →+* L` to `(σ.toRingHom.comp (algebraMap R M)).codRestrict L hmem`.

Establish `hg₀ : ∀ b, g₀ (algebraMap B R b) = algebraMap B L b`. Introduce `b`. Apply `Subtype.val_injective` to reduce the goal to its premises. Use `show σ (algebraMap R M (algebraMap B R b)) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply B R M, IsScalarTower.algebraMap_apply B K M, σ.commutes, ← hK]`.

Both sides reduce to the same expression. Set `g : R →ₐ[B] L` to `{ g₀ with commutes' := hg₀ }`. Establish `hC : ∀ r, g r ∈ C` using `fun r => (Algebra.IsIntegral.isIntegral (R := B) r).map g`. Set `f : R →+* C` to `(g : R →+* L).codRestrict C hC`. Establish `hcomm : f.comp ψ = algebraMap B C`.

Use extensionality with `b`. Conclude with `congrArg Subtype.val (hg₀ b)`. Establish `hfinj : Function.Injective f` using `fun x y h => IsFractionRing.injective R M (σ.injective (congrArg (fun c : C => ((c : L) : Ω)) h))`. Establish `hfi : f.IsIntegral`. Use `letI : Algebra R C := f.toAlgebra`.

Use `haveI : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq' hcomm.symm`. Introduce `c`. Conclude with `(integralClosure.isIntegral c).tower_top`. Conclude with `⟨f, hfinj, RingHom.IsIntegral.isLocalHom hfi hfinj, hcomm, fun r => rfl⟩`. Use `choose f hfi hfl hfc hfv using key`.

Establish `hemb : ∀ σ τ : M →ₐ[K] Ω, σ = τ`. Introduce `σ τ`. Establish `h` using `huniq C hCc (f σ) (f τ) (hfi σ) (hfi τ) (hfl σ) (hfl τ) ((hfc σ).trans (hfc τ).symm)`. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (nonZeroDivisors R) (S := M)` to reduce the goal to its premises.

Use extensionality with `r`. Simplify using `only [RingHom.comp_apply, AlgHom.coe_toRingHom]`. Rewrite using `[← hfv σ r, ← hfv τ r, h]`. Establish `hrank : Module.finrank K M = 1`. Rewrite using `[← Field.finSepDegree_eq_finrank_of_isSeparable K M]`.

Unfold `Field.finSepDegree`. Use `haveI : Subsingleton (Field.Emb K M) := ⟨hemb⟩`. Conclude with `Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨IsAlgClosed.lift⟩⟩`. Establish `hbot : (⊥ : Subalgebra K M) = ⊤` using `Subalgebra.bot_eq_top_of_finrank_eq_one hrank`. Introduce `r`.

Take `⟨k, hk⟩` from `Algebra.mem_bot.1 (hbot.symm ▸ Algebra.mem_top : algebraMap R M r ∈ (⊥ : Subalgebra K M))`. Establish `hki : IsIntegral B k`. Establish `h1 : IsIntegral B (algebraMap K M k)` using `hk ▸ (Algebra.IsIntegral.isIntegral (R := B) r).map (IsScalarTower.toAlgHom B R M)`. Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom B K M) (algebraMap K M).injective).1 h1`. Take `⟨b, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hki`.

Use `⟨b, IsFractionRing.injective R M ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, ← IsScalarTower.algebraMap_apply B K M, IsScalarTower.algebraMap_apply B R M]`. Both sides reduce to the same expression.
-/
theorem surjective_of_unique_injective_localHom : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  intro B R _ _ _ _ _ _ _ _ _ ψ hB hinj hfin huniq
  haveI := hB
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hfin
  haveI : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  haveI : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).2 hinj
  haveI : CharZero B := ⟨fun m n h => Nat.cast_injective (R := R) (by simpa only [map_natCast] using congrArg ψ h)⟩
  let K := FractionRing B
  let M := FractionRing R
  have hBM : Function.Injective (algebraMap B M) := by
    rw [IsScalarTower.algebraMap_eq B R M]
    exact (IsFractionRing.injective R M).comp hinj
  haveI : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).2 hBM
  letI : Algebra K M := FractionRing.liftAlgebra B M
  haveI : IsScalarTower B K M := FractionRing.isScalarTower_liftAlgebra B M
  haveI : Module.Finite K M := Module.Finite.of_isLocalization B R (Rₚ := K) (Sₚ := M) (nonZeroDivisors B)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing B (K := K)
  let Ω := AlgebraicClosure M
  let L := IntermediateField.normalClosure K M Ω
  haveI : FiniteDimensional K L := normalClosure.is_finiteDimensional K M Ω
  haveI : IsScalarTower B K Ω := inferInstance
  haveI : IsScalarTower B K L := inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let C := integralClosure B L
  haveI : Module.Finite B C := IsIntegralClosure.finite B K L C
  haveI : IsLocalRing C := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := B) C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : CharZero C := ⟨fun m n h => Nat.cast_injective (R := L) (by simpa using congrArg Subtype.val h)⟩
  have hCc : IsAdicComplete (maximalIdeal C) C := CompleteFiniteExtension.isAdicComplete_of_finite_local B C

  have hK : ∀ b : B, algebraMap K L (algebraMap B K b) = algebraMap B L b := fun b =>
    (IsScalarTower.algebraMap_apply B K L b).symm
  have key : ∀ σ : M →ₐ[K] Ω, ∃ f : R →+* C, Function.Injective f ∧ IsLocalHom f ∧ f.comp ψ = algebraMap B C ∧
      ∀ r, ((f r : L) : Ω) = σ (algebraMap R M r) := by
    intro σ
    have hmem : ∀ x, (σ.toRingHom.comp (algebraMap R M)) x ∈ L := fun x =>
      σ.fieldRange_le_normalClosure ⟨_, rfl⟩
    let g₀ : R →+* L := (σ.toRingHom.comp (algebraMap R M)).codRestrict L hmem
    have hg₀ : ∀ b, g₀ (algebraMap B R b) = algebraMap B L b := by
      intro b
      apply Subtype.val_injective
      show σ (algebraMap R M (algebraMap B R b)) = _
      rw [← IsScalarTower.algebraMap_apply B R M, IsScalarTower.algebraMap_apply B K M, σ.commutes,
        ← hK]
      rfl
    let g : R →ₐ[B] L := { g₀ with commutes' := hg₀ }
    have hC : ∀ r, g r ∈ C := fun r => (Algebra.IsIntegral.isIntegral (R := B) r).map g
    let f : R →+* C := (g : R →+* L).codRestrict C hC
    have hcomm : f.comp ψ = algebraMap B C := by
      ext b
      exact congrArg Subtype.val (hg₀ b)
    have hfinj : Function.Injective f := fun x y h =>
      IsFractionRing.injective R M (σ.injective (congrArg (fun c : C => ((c : L) : Ω)) h))
    have hfi : f.IsIntegral := by
      letI : Algebra R C := f.toAlgebra
      haveI : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq' hcomm.symm
      intro c
      exact (integralClosure.isIntegral c).tower_top
    exact ⟨f, hfinj, RingHom.IsIntegral.isLocalHom hfi hfinj, hcomm, fun r => rfl⟩
  choose f hfi hfl hfc hfv using key
  have hemb : ∀ σ τ : M →ₐ[K] Ω, σ = τ := by
    intro σ τ
    have h := huniq C hCc (f σ) (f τ) (hfi σ) (hfi τ) (hfl σ) (hfl τ) ((hfc σ).trans (hfc τ).symm)
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R) (S := M)
    ext r
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
    rw [← hfv σ r, ← hfv τ r, h]
  have hrank : Module.finrank K M = 1 := by
    rw [← Field.finSepDegree_eq_finrank_of_isSeparable K M]
    unfold Field.finSepDegree
    haveI : Subsingleton (Field.Emb K M) := ⟨hemb⟩
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨IsAlgClosed.lift⟩⟩
  have hbot : (⊥ : Subalgebra K M) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hrank
  intro r
  obtain ⟨k, hk⟩ := Algebra.mem_bot.1 (hbot.symm ▸ Algebra.mem_top : algebraMap R M r ∈ (⊥ : Subalgebra K M))
  have hki : IsIntegral B k := by
    have h1 : IsIntegral B (algebraMap K M k) := hk ▸
      (Algebra.IsIntegral.isIntegral (R := B) r).map (IsScalarTower.toAlgHom B R M)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B K M) (algebraMap K M).injective).1 h1
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hki
  refine ⟨b, IsFractionRing.injective R M ?_⟩
  rw [← hk, ← IsScalarTower.algebraMap_apply B K M, IsScalarTower.algebraMap_apply B R M]
  rfl

end GlobalTheory.DegreeOne
