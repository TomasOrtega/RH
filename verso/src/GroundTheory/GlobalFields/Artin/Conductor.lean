import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal
import GroundTheory.LocalFields.ArtinConductorBrauer
import GroundTheory.LocalFields.ConductorTransport

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section Transport

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {L₁ : Type*} [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Algebra F L₁] [ValuativeExtension F L₁] [FiniteDimensional F L₁] [IsGalois F L₁]
  {L₂ : Type*} [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Algebra F L₂] [ValuativeExtension F L₂] [FiniteDimensional F L₂] [IsGalois F L₂]

/- English proof (translation)
Rewrite using `[charArtinConductor_eq_sum_lowerIndex, charArtinConductor_eq_sum_lowerIndex]`. Establish `hcard : Nat.card (lowerRamificationGroup F L₂ 0) = Nat.card (lowerRamificationGroup F L₁ 0)`. Rewrite using `[← map_lowerRamificationGroup_autCongr e 0]`. Conclude with `Subgroup.card_map_of_injective e.autCongr.injective`. Rewrite using `[hcard]`.

Use `congr 1`. Use `Fintype.sum_equiv e.autCongr.toEquiv _ _ (fun σ ↦ ?_)` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_one, lowerIndex_autCongr]`.
-/
theorem charArtinConductor_autCongr (e : L₁ ≃ₐ[F] L₂) (χ : (L₂ ≃ₐ[F] L₂) → ℂ) :
    charArtinConductor F L₁ (fun σ ↦ χ (e.autCongr σ)) = charArtinConductor F L₂ χ := by
  rw [charArtinConductor_eq_sum_lowerIndex, charArtinConductor_eq_sum_lowerIndex]
  have hcard : Nat.card (lowerRamificationGroup F L₂ 0) =
      Nat.card (lowerRamificationGroup F L₁ 0) := by
    rw [← map_lowerRamificationGroup_autCongr e 0]
    exact Subgroup.card_map_of_injective e.autCongr.injective
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv e.autCongr.toEquiv _ _ (fun σ ↦ ?_)
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_one, lowerIndex_autCongr]

end Transport

section Local

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

def localToGlobal (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    Gal(w.adicCompletion L/v.adicCompletion K) →* Gal(L/K) :=
  (MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
    (decompositionMulEquiv v w).symm.toMonoidHom

/- English proof (translation)
Use `show ((decompositionMulEquiv v w).symm (decompositionMulEquiv v w τ) : Gal(L/K)) = τ`. Rewrite using `[MulEquiv.symm_apply_apply]`.
-/
theorem localToGlobal_decompositionMulEquiv (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    localToGlobal v w (decompositionMulEquiv v w τ) = τ := by
  show ((decompositionMulEquiv v w).symm (decompositionMulEquiv v w τ) : Gal(L/K)) = τ
  rw [MulEquiv.symm_apply_apply]

/- English proof (translation)
Use `algEquiv_ext_adicCompletion v w' (continuous_decompositionAlgEquiv v w' _) ?_ (fun x ↦ ?_)` and prove the remaining obligations. Conclude with `(SemiLocal.continuous_galEquiv v σ w w' h).comp ((continuous_decompositionAlgEquiv v w τ).comp (SemiLocal.continuous_galEquiv_symm v σ w w' h))`. Establish `hs : (SemiLocal.galEquiv v σ w w' h).symm (algebraMap L (w'.adicCompletion L) x) = algebraMap L (w.adicCompletion L) (σ⁻¹ x)`. Rewrite using `[AlgEquiv.symm_apply_eq, SemiLocal.galEquiv_algebraMap, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`. Rewrite using `[decompositionMulEquiv_apply, decompositionToLocal_algebraMap, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply, hs, decompositionMulEquiv_apply, decompositionToLocal_algebraMap, SemiLocal.galEquiv_algebraMap]`.

Simplify using `only [AlgEquiv.mul_apply]`.
-/
theorem decompositionMulEquiv_conj (σ : Gal(L/K)) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w)
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (hτ : σ * τ * σ⁻¹ ∈ MulAction.stabilizer Gal(L/K) w'.asIdeal) :
    decompositionMulEquiv v w' ⟨σ * τ * σ⁻¹, hτ⟩ =
      (SemiLocal.galEquiv v σ w w' h).autCongr (decompositionMulEquiv v w τ) := by
  refine algEquiv_ext_adicCompletion v w' (continuous_decompositionAlgEquiv v w' _) ?_
    (fun x ↦ ?_)
  · exact (SemiLocal.continuous_galEquiv v σ w w' h).comp
      ((continuous_decompositionAlgEquiv v w τ).comp
        (SemiLocal.continuous_galEquiv_symm v σ w w' h))
  · have hs : (SemiLocal.galEquiv v σ w w' h).symm (algebraMap L (w'.adicCompletion L) x) =
        algebraMap L (w.adicCompletion L) (σ⁻¹ x) := by
      rw [AlgEquiv.symm_apply_eq, SemiLocal.galEquiv_algebraMap, ← AlgEquiv.mul_apply,
        mul_inv_cancel, AlgEquiv.one_apply]
    rw [decompositionMulEquiv_apply, decompositionToLocal_algebraMap, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, AlgEquiv.trans_apply, hs, decompositionMulEquiv_apply,
      decompositionToLocal_algebraMap, SemiLocal.galEquiv_algebraMap]
    simp only [AlgEquiv.mul_apply]

/- English proof (translation)
Take `⟨τ, rfl⟩` from `(decompositionMulEquiv v w).surjective T`. Establish `hτ : σ * τ * σ⁻¹ ∈ MulAction.stabilizer Gal(L/K) w'.asIdeal`. Substitute `h` using the available equality. Rewrite using `[MulAction.mem_stabilizer_iff, SemiLocal.smul_asIdeal, mul_smul, mul_smul, inv_smul_smul, smul_asIdeal_of_mem_stabilizer w τ]`. Rewrite using `[← decompositionMulEquiv_conj v σ w w' h τ hτ, localToGlobal_decompositionMulEquiv, localToGlobal_decompositionMulEquiv]`.
-/
theorem localToGlobal_autCongr (σ : Gal(L/K)) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w)
    (T : Gal(w.adicCompletion L/v.adicCompletion K)) :
    localToGlobal v w' ((SemiLocal.galEquiv v σ w w' h).autCongr T) =
      σ * localToGlobal v w T * σ⁻¹ := by
  obtain ⟨τ, rfl⟩ := (decompositionMulEquiv v w).surjective T
  have hτ : σ * τ * σ⁻¹ ∈ MulAction.stabilizer Gal(L/K) w'.asIdeal := by
    subst h
    rw [MulAction.mem_stabilizer_iff, SemiLocal.smul_asIdeal, mul_smul, mul_smul, inv_smul_smul,
      smul_asIdeal_of_mem_stabilizer w τ]
  rw [← decompositionMulEquiv_conj v σ w w' h τ hτ, localToGlobal_decompositionMulEquiv,
    localToGlobal_decompositionMulEquiv]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal Gal(L/K)`. Conclude with `⟨σ, HeightOneSpectrum.ext (by rw [SemiLocal.smul_asIdeal, hσ])⟩`.
-/
theorem exists_smul_eq_of_liesOver (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] : ∃ σ : Gal(L/K), w' = σ • w := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal Gal(L/K)
  exact ⟨σ, HeightOneSpectrum.ext (by rw [SemiLocal.smul_asIdeal, hσ])⟩

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_smul_eq_of_liesOver v w w'`. Rewrite using `[← charArtinConductor_autCongr (SemiLocal.galEquiv v σ w w' hσ)]`. Use `congr 1`. Use function extensionality and compare the values at `T`. Rewrite using `[localToGlobal_autCongr v σ w w' hσ, hχ]`.
-/
theorem charArtinConductor_localToGlobal_eq (χ : Gal(L/K) → ℂ)
    (hχ : ∀ g h : Gal(L/K), χ (h * g * h⁻¹) = χ g) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] :
    charArtinConductor (v.adicCompletion K) (w.adicCompletion L) (fun T ↦ χ (localToGlobal v w T)) =
      charArtinConductor (v.adicCompletion K) (w'.adicCompletion L)
        (fun T ↦ χ (localToGlobal v w' T)) := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver v w w'
  rw [← charArtinConductor_autCongr (SemiLocal.galEquiv v σ w w' hσ)]
  congr 1
  funext T
  rw [localToGlobal_autCongr v σ w w' hσ, hχ]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def localArtinConductor (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (ρ : Representation ℂ Gal(L/K) V) : ℚ :=
  artinConductor (ρ.comp (localToGlobal v w))

/- English proof (translation)
The claim follows from `artinConductor_eq_charArtinConductor _`.
-/
theorem natCast_localArtinConductor (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (ρ : Representation ℂ Gal(L/K) V) :
    (localArtinConductor v w ρ : ℂ) = charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
      (fun T ↦ ρ.character (localToGlobal v w T)) :=
  artinConductor_eq_charArtinConductor _

/- English proof (translation)
Apply `Rat.cast_injective (α := ℂ)` to reduce the goal to its premises. Rewrite using `[natCast_localArtinConductor, natCast_localArtinConductor]`. Conclude with `charArtinConductor_localToGlobal_eq v ρ.character (fun g h ↦ ρ.char_conj g h) w w'`.
-/
theorem localArtinConductor_eq (ρ : Representation ℂ Gal(L/K) V) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] :
    localArtinConductor v w ρ = localArtinConductor v w' ρ := by
  apply Rat.cast_injective (α := ℂ)
  rw [natCast_localArtinConductor, natCast_localArtinConductor]
  exact charArtinConductor_localToGlobal_eq v ρ.character (fun g h ↦ ρ.char_conj g h) w w'

/- English proof (translation)
The claim follows from `exists_nat_artinConductor _`.
-/
theorem exists_nat_localArtinConductor (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (ρ : Representation ℂ Gal(L/K) V) : ∃ n : ℕ, localArtinConductor v w ρ = n :=
  exists_nat_artinConductor _

def artinExponent (ρ : Representation ℂ Gal(L/K) V) : ℕ :=
  ⌊localArtinConductor v (placeAbove (L := L) v) ρ⌋₊

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_nat_localArtinConductor v w ρ`. Rewrite using `[artinExponent, localArtinConductor_eq v ρ (placeAbove v) w, hn, Nat.floor_natCast]`.
-/
theorem artinExponent_eq (ρ : Representation ℂ Gal(L/K) V) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] : (artinExponent v ρ : ℚ) = localArtinConductor v w ρ := by
  obtain ⟨n, hn⟩ := exists_nat_localArtinConductor v w ρ
  rw [artinExponent, localArtinConductor_eq v ρ (placeAbove v) w, hn, Nat.floor_natCast]

/- English proof (translation)
Rewrite using `[← natCast_localArtinConductor, ← artinExponent_eq v ρ w]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem natCast_artinExponent (ρ : Representation ℂ Gal(L/K) V) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    (artinExponent v ρ : ℂ) = charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
      (fun T ↦ ρ.character (localToGlobal v w T)) := by
  rw [← natCast_localArtinConductor, ← artinExponent_eq v ρ w]
  push_cast
  rfl

/- English proof (translation)
Establish `hI : w.asIdeal.inertia Gal(L/K) = ⊥`. Rewrite using `[← Subgroup.card_eq_one, natCard_inertia v w, he]`. Establish `h0 : lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 = ⊥`. Rewrite using `[← map_inertia_decompositionMulEquiv v w, hI, Subgroup.bot_subgroupOf, Subgroup.map_bot]`. Establish `hq : localArtinConductor v w ρ = 0`.

Rewrite using `[localArtinConductor, artinConductor_eq_zero_iff]`. Introduce `σ hσ`. Rewrite `hσ` using `[h0, Subgroup.mem_bot]`. Substitute `hσ` using the available equality. Conclude with `map_one _`.

Conclude with `(artinExponent_eq v ρ w).trans hq` after adjusting the coercions.
-/
theorem artinExponent_eq_zero_of_ramificationIdx_eq_one (ρ : Representation ℂ Gal(L/K) V)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) : artinExponent v ρ = 0 := by
  have hI : w.asIdeal.inertia Gal(L/K) = ⊥ := by
    rw [← Subgroup.card_eq_one, natCard_inertia v w, he]
  have h0 : lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 = ⊥ := by
    rw [← map_inertia_decompositionMulEquiv v w, hI, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hq : localArtinConductor v w ρ = 0 := by
    rw [localArtinConductor, artinConductor_eq_zero_iff]
    intro σ hσ
    rw [h0, Subgroup.mem_bot] at hσ
    subst hσ
    exact map_one _
  exact_mod_cast (artinExponent_eq v ρ w).trans hq

end Local

section Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in

/- English proof (translation)
Use `show LinearMap.trace ℂ (V × W) ((ρ g).prodMap (ρ' g)) = _`. Conclude with `LinearMap.trace_prodMap' _ _`.
-/
theorem character_prod {G : Type*} [Monoid G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (g : G) :
    (ρ.prod ρ').character g = ρ.character g + ρ'.character g := by
  show LinearMap.trace ℂ (V × W) ((ρ g).prodMap (ρ' g)) = _
  exact LinearMap.trace_prodMap' _ _

/- English proof (translation)
Apply `Nat.cast_injective (R := ℂ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[natCast_artinExponent v _ (placeAbove v), natCast_artinExponent v ρ (placeAbove v), natCast_artinExponent v ρ' (placeAbove v), ← charArtinConductor_add]`. Use `congr 1`. Use function extensionality and compare the values at `T`.

Rewrite using `[Pi.add_apply, character_prod]`.
-/
theorem artinExponent_prod (v : HeightOneSpectrum (𝓞 K)) (ρ : Representation ℂ Gal(L/K) V)
    (ρ' : Representation ℂ Gal(L/K) W) :
    artinExponent v (ρ.prod ρ') = artinExponent v ρ + artinExponent v ρ' := by
  apply Nat.cast_injective (R := ℂ)
  push_cast
  rw [natCast_artinExponent v _ (placeAbove v), natCast_artinExponent v ρ (placeAbove v),
    natCast_artinExponent v ρ' (placeAbove v), ← charArtinConductor_add]
  congr 1
  funext T
  rw [Pi.add_apply, character_prod]

/- English proof (translation)
Establish `hq : localArtinConductor v (placeAbove (L` using `L) v) ρ = 0 := by`. Rewrite using `[localArtinConductor, artinConductor_eq_zero_iff]`. Conclude with `fun σ _ ↦ hρ _`. Rewrite using `[artinExponent, hq, Nat.floor_zero]`.
-/
theorem artinExponent_eq_zero_of_forall_eq_one (v : HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ Gal(L/K) V) (hρ : ∀ g, ρ g = 1) : artinExponent v ρ = 0 := by
  have hq : localArtinConductor v (placeAbove (L := L) v) ρ = 0 := by
    rw [localArtinConductor, artinConductor_eq_zero_iff]
    exact fun σ _ ↦ hρ _
  rw [artinExponent, hq, Nat.floor_zero]

variable (K) in

/- English proof (translation)
Use `(finite_setOf_exists_ramificationIdx_ne_one K L).subset fun v hv ↦ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_ofPred_eq, not_exists, not_and, not_not] at h`. Conclude with `hv (artinExponent_eq_zero_of_ramificationIdx_eq_one v ρ (placeAbove v) (h _ inferInstance))`.
-/
theorem finite_support_artinExponent (ρ : Representation ℂ Gal(L/K) V) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) ↦ artinExponent v ρ).Finite := by
  refine (finite_setOf_exists_ramificationIdx_ne_one K L).subset fun v hv ↦ ?_
  by_contra h
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_not] at h
  exact hv (artinExponent_eq_zero_of_ramificationIdx_eq_one v ρ (placeAbove v)
    (h _ inferInstance))

def artinConductorIdeal (ρ : Representation ℂ Gal(L/K) V) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ artinExponent v ρ

/- English proof (translation)
Rewrite using `[Function.HasFiniteMulSupport, mulSupport_asIdeal_pow]`. Conclude with `finite_support_artinExponent K ρ`.
-/
theorem hasFiniteMulSupport_artinExponent (ρ : Representation ℂ Gal(L/K) V) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal ^ artinExponent v ρ := by
  rw [Function.HasFiniteMulSupport, mulSupport_asIdeal_pow]
  exact finite_support_artinExponent K ρ

omit [FiniteDimensional ℂ V] in

/- English proof (translation)
The claim follows from `finprod_asIdeal_pow_ne_bot _`.
-/
theorem artinConductorIdeal_ne_bot (ρ : Representation ℂ Gal(L/K) V) :
    artinConductorIdeal ρ ≠ ⊥ :=
  finprod_asIdeal_pow_ne_bot _

/- English proof (translation)
Rewrite using `[artinConductorIdeal, artinConductorIdeal, artinConductorIdeal, ← finprod_mul_distrib (hasFiniteMulSupport_artinExponent ρ) (hasFiniteMulSupport_artinExponent ρ')]`. Conclude with `finprod_congr fun v ↦ by rw [artinExponent_prod, pow_add]`.
-/
theorem artinConductorIdeal_prod (ρ : Representation ℂ Gal(L/K) V)
    (ρ' : Representation ℂ Gal(L/K) W) :
    artinConductorIdeal (ρ.prod ρ') = artinConductorIdeal ρ * artinConductorIdeal ρ' := by
  rw [artinConductorIdeal, artinConductorIdeal, artinConductorIdeal,
    ← finprod_mul_distrib (hasFiniteMulSupport_artinExponent ρ)
      (hasFiniteMulSupport_artinExponent ρ')]
  exact finprod_congr fun v ↦ by rw [artinExponent_prod, pow_add]

/- English proof (translation)
Rewrite using `[artinConductorIdeal, ← Ideal.one_eq_top]`. Conclude with `finprod_eq_one_of_forall_eq_one fun v ↦ by`. Rewrite using `[artinExponent_eq_zero_of_forall_eq_one v ρ hρ, pow_zero]`.
-/
theorem artinConductorIdeal_eq_top_of_forall_eq_one (ρ : Representation ℂ Gal(L/K) V)
    (hρ : ∀ g, ρ g = 1) : artinConductorIdeal ρ = ⊤ := by
  rw [artinConductorIdeal, ← Ideal.one_eq_top]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by
    rw [artinExponent_eq_zero_of_forall_eq_one v ρ hρ, pow_zero]

def artinConductorConstant (ρ : Representation ℂ Gal(L/K) V) : ℕ :=
  (discr K).natAbs ^ finrank ℂ V * Ideal.absNorm (artinConductorIdeal ρ)

end Ideal

end GroundTheory.Global
