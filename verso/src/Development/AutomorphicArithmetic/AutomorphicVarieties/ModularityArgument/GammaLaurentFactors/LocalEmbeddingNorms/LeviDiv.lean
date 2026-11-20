import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdMulti
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralLaurentExpansion
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralShellMean
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralTateComparison
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaFunctionalUniqueness

noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

/- English proof (translation)
Establish `hsm : IsSmooth σ` using `hσ.1`. Use `haveI bGL : ∀ m, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m`. Use `haveI nz : ∀ a : ↑(Set.range β), NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩`. Take `⟨e, he⟩ : ∃ e, e = leviEquivPi F β` from `⟨_, rfl⟩`. Take `⟨τ, hτ⟩ : ∃ τ, τ = twist (nnrealCharC κ) σ` from `⟨_, rfl⟩`.

Take `⟨E, hE⟩ : ∃ E, E = (prodPUnitEquiv.{_, 0} ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F)).trans e.symm` from `⟨_, rfl⟩`. Take `⟨ρ, hρ⟩ : ∃ ρ : Representation ℂ (((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F) × PUnit.{1}) W, ρ = τ.comp E.toMonoidHom` from `⟨_, rfl⟩`. Establish `hEx : ∀ x, E (x, (1 : PUnit.{1})) = e.symm x` using `fun x => by subst hE; rfl`. Establish `hτm : ∀ m v, τ m v = nnrealCharC κ m • σ m v` using `fun m v => by subst hτ; rfl`. Establish `hρx : ∀ x v, ρ (x, (1 : PUnit.{1})) v = nnrealCharC κ (e.symm x) • σ (e.symm x) v` using `fun x v => by`.

Substitute `hρ` using the available equality. Rewrite using `[← hτm, ← hEx]`. Both sides reduce to the same expression. Establish `hτA : IsAdmissible τ` using `hτ ▸ isAdmissible_twist κ hκ σ hσ`. Use `haveI hτI : Representation.IsIrreducible τ := hτ ▸ isIrreducible_twist κ σ`.

Establish `hρA : IsAdmissible ρ` using `hρ ▸ (isAdmissible_comp_iff E τ).2 hτA`. Use `haveI hρI : Representation.IsIrreducible ρ := hρ ▸ (isIrreducible_comp_iff E τ).2 hτI`. Establish `hℓ : ∀ ℓ, ℓ ∈ smoothVectors (Representation.dual ρ) ↔ ℓ ∈ smoothVectors σ.dual` using `fun ℓ => by`. Substitute `hρ hτ` using the available equality. Rewrite using `[mem_smoothVectors_dual_comp_iff, mem_smoothVectors_dual_twist_iff κ hκ]`.

Use `haveI : Nontrivial W := nontrivial_of_isIrreducible σ`. Take `⟨ω, hω⟩` from `exists_blockChar (σ := τ) hτA.1`. Establish `hω0 : ∀ b, ω b ≠ 0`. Introduce `b h0`. Take `⟨v, hv⟩` from `exists_ne (0 : W)`.

Apply `hv` to reduce the goal to its premises. Establish `h1 : τ (blockUnif F b)⁻¹ (τ (blockUnif F b) v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite using `[← h1, hω, h0, zero_smul, map_zero]`. Establish `hcent : ∀ (i : ↑(Set.range β)) (v : W), ρ (Pi.mulSingle i (centralUnif F (blockSize β i)), (1 : PUnit.{1})) v = ω i • v`.

Introduce `i v`. Rewrite using `[← hω, ← leviEquivPi_symm_mulSingle, ← he, ← hEx]`. Substitute `hρ` using the available equality. Both sides reduce to the same expression. Establish `hcpt : ∀ (v : W), ∀ ℓ ∈ smoothVectors (Representation.dual ρ), ∃ C, IsCompact C ∧ ∀ (x : (a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F), ℓ (ρ (x, (1 : PUnit.{1})) v) ≠ 0 → ∃ j : ↑(Set.range β) → ℤ, (fun i => centralUnif F (blockSize β i) ^ j i) * x ∈ C`.

Introduce `v ℓ hl`. Take `⟨C0, hC0, hC0m⟩` from `exists_compact_of_coeff hsm hc v ((hℓ ℓ).1 hl) (fun _ => 0) (fun a => (blockSize β a : ℤ) - 1)`. Use `⟨e '' C0, hC0.image e.continuous, fun x hx => ?_⟩` and prove the remaining obligations. Use `⟨fun a => -(ordDet (x a) / (blockSize β a : ℤ)), ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩ : ∃ y, y = (fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) * x` from `⟨_, rfl⟩`.

Rewrite using `[← hy]`. Use `⟨e.symm y, hC0m _ ?_ ?_, e.apply_symm_apply y⟩` and prove the remaining obligations. Establish `h1 : ρ (y, (1 : PUnit.{1})) v = (∏ i, ω i ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) • ρ (x, (1 : PUnit.{1})) v`. Establish `hp : (y, (1 : PUnit.{1})) = ((fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))), (1 : PUnit.{1})) * (x, (1 : PUnit.{1}))` using `by rw [hy]; rfl`. Rewrite using `[hp, map_mul, Module.End.mul_apply, apply_centralPow ρ hω0 hcent]`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Establish `h2 : ℓ (ρ (y, (1 : PUnit.{1})) v) = 0` using `by rw [hρx, map_smul, h0, smul_zero]`. Rewrite `h2` using `[h1, map_smul, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hω0 i))`.

Introduce `b`. Rewrite using `[← ordDet_leviEquivPi, ← he, e.apply_symm_apply, hy]`. Simplify using `only [Pi.mul_apply, ordDet_centralUnif_zpow_mul]`. Establish `hd : (0:ℤ) < blockSize β b` using `by exact_mod_cast blockSize_pos β b`. Establish `h3` using `Int.emod_nonneg (ordDet (x b)) hd.ne'`.

Establish `h4` using `Int.emod_lt_of_pos (ordDet (x b)) hd`. Establish `h5` using `Int.mul_ediv_add_emod (ordDet (x b)) (blockSize β b)`. Apply the tactic sequence `constructor <;> linarith`. Take `⟨μ', hμ'⟩ : ∃ μ' : (a : ↑(Set.range β)) → Measure (GL (Fin (blockSize β a)) F), μ' = fun _ => Measure.haar` from `⟨_, rfl⟩`. Use `haveI hμ'H : ∀ a, (μ' a).IsHaarMeasure := fun a => by subst hμ'; infer_instance`.

Take `⟨γ, hγs, hγfe⟩` from `ldMulti_all (F := F) (W := W) hB hψ hψ1 (Fintype.card ↑(Set.range β)) ↑(Set.range β) rfl (fun a => blockSize β a) μ' PUnit.{1} ρ hρA hρI ω hω0 hcent hcpt`. Take `⟨s₁, hs₁⟩` from `exists_integrable_multi ρ hρA.1 hω0 hcent hcpt μ'`. Use `⟨γ, ?_, ?_⟩` and prove the remaining obligations. Use `hγs using 1` and compare the differences between its conclusion and the goal. Substitute `he` using the available equality.

Unfold `cntF`. Rewrite using `[Finset.sum_boole, Nat.cast_id]`. Use `congr 1`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `i _`.

Apply `and_congr_right` to reduce the goal to its premises. Introduce `_`. Apply `forall₂_congr` to reduce the goal to its premises. Introduce `g hg`. Establish `hk : κ ((leviEquivPi F β).symm (Pi.mulSingle i g)) = 1`.

Use `eq_one_of_mem_compact κ hκ (K := (integralGL F (blockSize β i)).map (((leviEquivPi F β).symm.toMonoidHom).comp (MonoidHom.mulSingle _ i))) ?_ (Subgroup.mem_map_of_mem _ hg)` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map]`. Conclude with `(isCompact_integralGL F _).image (f := fun x => (leviEquivPi F β).symm (Pi.mulSingle i x)) ((leviEquivPi F β).symm.continuous.comp (continuous_mulSingle (A := fun a : ↑(Set.range β) => GL (Fin (blockSize β a)) F) i))`. Establish `hx : ρ (Pi.mulSingle i g, (1 : PUnit.{1})) = σ ((leviEquivPi F β).symm (Pi.mulSingle i g))`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Rewrite using `[hρx, nnrealCharC_apply, hk]`. Simplify using the standard rewrite rules. Rewrite using `[hx]`. Introduce `φ hφ w ℓ hl`. Establish `hlρ` using `(hℓ ℓ).2 hl`.

Take `⟨Ψ, hΨ⟩ : ∃ Ψ : (a : ↑(Set.range β)) → Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ, Ψ = fun a => blockTensor β φ a` from `⟨_, rfl⟩`. Establish `hΨs : ∀ a, IsSchwartzBruhat (Ψ a)` using `by subst hΨ; exact isSchwartzBruhat_blockTensor hφ`. Establish `hΨh : ∀ a, IsSchwartzBruhat (GJMatrix.localMatrixFourier ψ (Ψ a))` using `fun a => (hΨs a).localMatrixFourier hψ hψ1`. Establish `hA : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) = multiA ρ Ψ w ℓ s x`. Introduce `s x`.

Substitute `he hΨ` using the available equality. Simplify using `only [leviIntegrand, multiA, leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρx, map_smul, smul_eq_mul, nnrealCharC_apply, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB2 : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) = multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x`. Introduce `s x`.

Substitute `he hΨ` using the available equality. Establish `hd : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) = ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s)` using `fun a => by rw [sub_eq_add_neg, detPow_add, detPow_natCast]`. Simplify using `only [leviIntegrandB, multiB, leviTensorHat_leviEquivPi_symm, detPow_leviEquivPi_symm, leviModulus_leviEquivPi_symm, hρx, map_inv, map_smul, smul_eq_mul, nnrealCharC_apply, hd, Finset.prod_mul_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨em, hem⟩ : ∃ em : levi F n β ≃ᵐ ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F), em = e.toHomeomorph.toMeasurableEquiv` from `⟨_, rfl⟩`. Establish `hemx : ∀ m, em m = e m` using `fun m => by subst hem; rfl`. Use `haveI : (μM.map em).IsHaarMeasure := by`. Substitute `hem` using the available equality. Conclude with `ContinuousMulEquiv.isHaarMeasure_map μM e`.

Take `⟨c, hc⟩ : ∃ c : ℝ≥0, c = (μM.map em).haarScalarFactor (Measure.pi μ')` from `⟨_, rfl⟩`. Establish `hmap : μM.map em = (c : ℝ≥0∞) • Measure.pi μ'`. Rewrite using `[hc]`. Conclude with `isMulLeftInvariant_eq_smul _ _`. Establish `hcomp : ∀ g : levi F n β → ℂ, (fun x => g (e.symm x)) ∘ em = g` using `fun g => by`.

Use function extensionality and compare the values at `m`. Simplify using `only [Function.comp, hemx, ContinuousMulEquiv.symm_apply_apply]`. Establish `hint : ∀ g : levi F n β → ℂ, Integrable (fun x => g (e.symm x)) (Measure.pi μ') → Integrable g μM`. Introduce `g hg`. Use `hg.smul_measure (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top` as an intermediate fact.

Rewrite `this` using `[← hmap, em.measurableEmbedding.integrable_map_iff, hcomp]`. Conclude with `this`. Establish `hI : ∀ g : levi F n β → ℂ, ∫ m, g m ∂μM = (c : ℂ) * ∫ x, g (e.symm x) ∂(Measure.pi μ')`. Introduce `g`. Establish `h1` using `integral_map_equiv (μ := μM) em (fun x => g (e.symm x))`.

Rewrite `h1` using `[hmap, integral_smul_measure]`. Simplify using `only [hemx, ContinuousMulEquiv.symm_apply_apply] at h1`. Rewrite using `[← h1]`. Simplify using `[Complex.real_smul]`. Use `⟨⟨s₁, fun s hs => hint _ ?_⟩, ⟨-s₁, fun s hs => hint _ ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [hA]`. Conclude with `(hs₁ Ψ hΨs w ℓ hlρ).1 s hs`. Simplify using `only [hB2]`. Conclude with `(hs₁ _ hΨh w ℓ hlρ).2 s hs`. Use `((hγfe Ψ hΨs w ℓ hlρ).const_mul (c : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hI]`. Simplify using `only [hA]`. Rewrite using `[hI]`. Simplify using `only [hB2]`.
-/
private theorem exists_shape (hB : LdBlock) (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ γ : RatFunc ℂ, LdShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ (cntF σ) ∧ LeviFE F σ κ μM ψ γ := by
  classical
  have hsm : IsSmooth σ := hσ.1
  haveI bGL : ∀ m, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  haveI nz : ∀ a : ↑(Set.range β), NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  obtain ⟨e, he⟩ : ∃ e, e = leviEquivPi F β := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = twist (nnrealCharC κ) σ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (prodPUnitEquiv.{_, 0} ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F)).trans e.symm :=
    ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Representation ℂ (((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F) × PUnit.{1}) W,
      ρ = τ.comp E.toMonoidHom := ⟨_, rfl⟩
  have hEx : ∀ x, E (x, (1 : PUnit.{1})) = e.symm x := fun x => by subst hE; rfl
  have hτm : ∀ m v, τ m v = nnrealCharC κ m • σ m v := fun m v => by subst hτ; rfl
  have hρx : ∀ x v, ρ (x, (1 : PUnit.{1})) v = nnrealCharC κ (e.symm x) • σ (e.symm x) v := fun x v => by
    subst hρ; rw [← hτm, ← hEx]; rfl
  have hτA : IsAdmissible τ := hτ ▸ isAdmissible_twist κ hκ σ hσ
  haveI hτI : Representation.IsIrreducible τ := hτ ▸ isIrreducible_twist κ σ
  have hρA : IsAdmissible ρ := hρ ▸ (isAdmissible_comp_iff E τ).2 hτA
  haveI hρI : Representation.IsIrreducible ρ := hρ ▸ (isIrreducible_comp_iff E τ).2 hτI
  have hℓ : ∀ ℓ, ℓ ∈ smoothVectors (Representation.dual ρ) ↔ ℓ ∈ smoothVectors σ.dual := fun ℓ => by
    subst hρ hτ
    rw [mem_smoothVectors_dual_comp_iff, mem_smoothVectors_dual_twist_iff κ hκ]
  haveI : Nontrivial W := nontrivial_of_isIrreducible σ
  obtain ⟨ω, hω⟩ := exists_blockChar (σ := τ) hτA.1
  have hω0 : ∀ b, ω b ≠ 0 := by
    intro b h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : τ (blockUnif F b)⁻¹ (τ (blockUnif F b) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  have hcent : ∀ (i : ↑(Set.range β)) (v : W),
      ρ (Pi.mulSingle i (centralUnif F (blockSize β i)), (1 : PUnit.{1})) v = ω i • v := by
    intro i v
    rw [← hω, ← leviEquivPi_symm_mulSingle, ← he, ← hEx]
    subst hρ; rfl
  have hcpt : ∀ (v : W), ∀ ℓ ∈ smoothVectors (Representation.dual ρ), ∃ C, IsCompact C ∧
      ∀ (x : (a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F),
        ℓ (ρ (x, (1 : PUnit.{1})) v) ≠ 0 →
          ∃ j : ↑(Set.range β) → ℤ, (fun i => centralUnif F (blockSize β i) ^ j i) * x ∈ C := by
    intro v ℓ hl
    obtain ⟨C0, hC0, hC0m⟩ := exists_compact_of_coeff hsm hc v ((hℓ ℓ).1 hl) (fun _ => 0)
      (fun a => (blockSize β a : ℤ) - 1)
    refine ⟨e '' C0, hC0.image e.continuous, fun x hx => ?_⟩
    refine ⟨fun a => -(ordDet (x a) / (blockSize β a : ℤ)), ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, y = (fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) * x :=
      ⟨_, rfl⟩
    rw [← hy]
    refine ⟨e.symm y, hC0m _ ?_ ?_, e.apply_symm_apply y⟩
    · have h1 : ρ (y, (1 : PUnit.{1})) v =
          (∏ i, ω i ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) • ρ (x, (1 : PUnit.{1})) v := by
        have hp : (y, (1 : PUnit.{1})) = ((fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))),
            (1 : PUnit.{1})) * (x, (1 : PUnit.{1})) := by rw [hy]; rfl
        rw [hp, map_mul, Module.End.mul_apply, apply_centralPow ρ hω0 hcent]
      intro h0
      apply hx
      have h2 : ℓ (ρ (y, (1 : PUnit.{1})) v) = 0 := by rw [hρx, map_smul, h0, smul_zero]
      rw [h1, map_smul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hω0 i))
    · intro b
      rw [← ordDet_leviEquivPi, ← he, e.apply_symm_apply, hy]
      simp only [Pi.mul_apply, ordDet_centralUnif_zpow_mul]
      have hd : (0:ℤ) < blockSize β b := by exact_mod_cast blockSize_pos β b
      have h3 := Int.emod_nonneg (ordDet (x b)) hd.ne'
      have h4 := Int.emod_lt_of_pos (ordDet (x b)) hd
      have h5 := Int.mul_ediv_add_emod (ordDet (x b)) (blockSize β b)
      constructor <;> linarith
  obtain ⟨μ', hμ'⟩ : ∃ μ' : (a : ↑(Set.range β)) → Measure (GL (Fin (blockSize β a)) F),
      μ' = fun _ => Measure.haar := ⟨_, rfl⟩
  haveI hμ'H : ∀ a, (μ' a).IsHaarMeasure := fun a => by subst hμ'; infer_instance
  obtain ⟨γ, hγs, hγfe⟩ := ldMulti_all (F := F) (W := W) hB hψ hψ1 (Fintype.card ↑(Set.range β))
    ↑(Set.range β) rfl (fun a => blockSize β a) μ' PUnit.{1} ρ hρA hρI ω hω0 hcent hcpt
  obtain ⟨s₁, hs₁⟩ := exists_integrable_multi ρ hρA.1 hω0 hcent hcpt μ'
  refine ⟨γ, ?_, ?_⟩
  · convert hγs using 1
    subst he
    unfold cntF
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    apply Finset.filter_congr
    intro i _
    apply and_congr_right
    intro _
    apply forall₂_congr
    intro g hg
    have hk : κ ((leviEquivPi F β).symm (Pi.mulSingle i g)) = 1 := by
      refine eq_one_of_mem_compact κ hκ (K := (integralGL F (blockSize β i)).map
        (((leviEquivPi F β).symm.toMonoidHom).comp (MonoidHom.mulSingle _ i))) ?_ (Subgroup.mem_map_of_mem _ hg)
      rw [Subgroup.coe_map]
      exact (isCompact_integralGL F _).image
        (f := fun x => (leviEquivPi F β).symm (Pi.mulSingle i x))
        ((leviEquivPi F β).symm.continuous.comp (continuous_mulSingle (A := fun a : ↑(Set.range β) => GL (Fin (blockSize β a)) F) i))
    have hx : ρ (Pi.mulSingle i g, (1 : PUnit.{1})) = σ ((leviEquivPi F β).symm (Pi.mulSingle i g)) := by
      refine LinearMap.ext fun v => ?_
      rw [hρx, nnrealCharC_apply, hk]
      simp
    rw [hx]
  · intro φ hφ w ℓ hl
    have hlρ := (hℓ ℓ).2 hl
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (a : ↑(Set.range β)) → Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ,
        Ψ = fun a => blockTensor β φ a := ⟨_, rfl⟩
    have hΨs : ∀ a, IsSchwartzBruhat (Ψ a) := by subst hΨ; exact isSchwartzBruhat_blockTensor hφ
    have hΨh : ∀ a, IsSchwartzBruhat (GJMatrix.localMatrixFourier ψ (Ψ a)) :=
      fun a => (hΨs a).localMatrixFourier hψ hψ1
    have hA : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) = multiA ρ Ψ w ℓ s x := by
      intro s x
      subst he hΨ
      simp only [leviIntegrand, multiA, leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρx, map_smul,
        smul_eq_mul, nnrealCharC_apply, Finset.prod_mul_distrib]
      ring
    have hB2 : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
        multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
      intro s x
      subst he hΨ
      have hd : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) = ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) :=
        fun a => by rw [sub_eq_add_neg, detPow_add, detPow_natCast]
      simp only [leviIntegrandB, multiB, leviTensorHat_leviEquivPi_symm, detPow_leviEquivPi_symm,
        leviModulus_leviEquivPi_symm, hρx, map_inv, map_smul, smul_eq_mul, nnrealCharC_apply, hd,
        Finset.prod_mul_distrib]
      push_cast
      ring
    obtain ⟨em, hem⟩ : ∃ em : levi F n β ≃ᵐ ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F),
        em = e.toHomeomorph.toMeasurableEquiv := ⟨_, rfl⟩
    have hemx : ∀ m, em m = e m := fun m => by subst hem; rfl
    haveI : (μM.map em).IsHaarMeasure := by
      subst hem
      exact ContinuousMulEquiv.isHaarMeasure_map μM e
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, c = (μM.map em).haarScalarFactor (Measure.pi μ') := ⟨_, rfl⟩
    have hmap : μM.map em = (c : ℝ≥0∞) • Measure.pi μ' := by
      rw [hc]; exact isMulLeftInvariant_eq_smul _ _
    have hcomp : ∀ g : levi F n β → ℂ, (fun x => g (e.symm x)) ∘ em = g := fun g => by
      funext m; simp only [Function.comp, hemx, ContinuousMulEquiv.symm_apply_apply]
    have hint : ∀ g : levi F n β → ℂ,
        Integrable (fun x => g (e.symm x)) (Measure.pi μ') → Integrable g μM := by
      intro g hg
      have := hg.smul_measure (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top
      rw [← hmap, em.measurableEmbedding.integrable_map_iff, hcomp] at this
      exact this
    have hI : ∀ g : levi F n β → ℂ, ∫ m, g m ∂μM = (c : ℂ) * ∫ x, g (e.symm x) ∂(Measure.pi μ') := by
      intro g
      have h1 := integral_map_equiv (μ := μM) em (fun x => g (e.symm x))
      rw [hmap, integral_smul_measure] at h1
      simp only [hemx, ContinuousMulEquiv.symm_apply_apply] at h1
      rw [← h1]
      simp [Complex.real_smul]
    refine ⟨⟨s₁, fun s hs => hint _ ?_⟩, ⟨-s₁, fun s hs => hint _ ?_⟩, ?_⟩
    · simp only [hA]
      exact (hs₁ Ψ hΨs w ℓ hlρ).1 s hs
    · simp only [hB2]
      exact (hs₁ _ hΨh w ℓ hlρ).2 s hs
    · refine ((hγfe Ψ hΨs w ℓ hlρ).const_mul (c : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
      · rw [hI]; simp only [hA]
      · rw [hI]; simp only [hB2]

end UpperTheory.V.Z.Gam

/- English proof (translation)
Introduce `F _ _ _ _ _ _ n β W _ _ σ hσ hirr hc κ hκ μ _ ψ hψ hψ1 γ hγ`. Establish `hB : LdBlock` using `ldBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison`. Take `⟨γ₀, hshape, hfe⟩` from `UpperTheory.V.Z.Gam.exists_shape hB hσ hc κ hκ μ hψ hψ1`. Take `rfl` from `UpperTheory.local_zeta_functional_uniqueness F n β W σ hσ hirr κ hκ μ ψ γ γ₀ hγ hfe`. Conclude with `hshape`.
-/
theorem UpperTheory.V.Z.Gam.leviDiv :
    UpperTheory.V.Z.Gam.LeviDiv := by
  intro F _ _ _ _ _ _ n β W _ _ σ hσ hirr hc κ hκ μ _ ψ hψ hψ1 γ hγ
  have hB : LdBlock := ldBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison
  obtain ⟨γ₀, hshape, hfe⟩ := UpperTheory.V.Z.Gam.exists_shape hB hσ hc κ hκ μ hψ hψ1
  obtain rfl := UpperTheory.local_zeta_functional_uniqueness F n β W σ hσ hirr κ hκ μ ψ γ γ₀ hγ hfe
  exact hshape
