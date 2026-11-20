import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagProjSpecialDimSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagProjTrdegLe

/- English proof (translation)
Establish `hker : RingHom.ker (g.comp f) = RingHom.ker f`. Use extensionality with `a`. Simplify using `only [RingHom.mem_ker, AlgHom.comp_apply]`. Conclude with `⟨fun h => hg (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩`. Rewrite using `[← hker]`.

Conclude with `(Ideal.quotientKerEquivRange (g.comp f)).trdeg_eq`.
-/
theorem trdeg_quot_ker_eq_range {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) (hg : Function.Injective g) :
    Algebra.trdeg R (A ⧸ RingHom.ker f) = Algebra.trdeg R (g.comp f).range := by
  have hker : RingHom.ker (g.comp f) = RingHom.ker f := by
    ext a
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    exact ⟨fun h => hg (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  rw [← hker]
  exact (Ideal.quotientKerEquivRange (g.comp f)).trdeg_eq

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[pointConeMap, FieldNumbers.blockIncl]`.
-/
theorem rename_comp_pointConeMap {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O).comp
        (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p))) =
      (pointConeMap O pt).comp (rename (FieldNumbers.blockIncl j ι')) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp [pointConeMap, FieldNumbers.blockIncl]

/- English proof (translation)
Establish `hren : Function.Injective ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O)` using `rename_injective _ j.injective`. Rewrite using `[pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren, trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), rename_comp_pointConeMap, AlgHom.id_comp]`. Conclude with `trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _)) (Subalgebra.inclusion_injective _)`.
-/
theorem trdeg_blocks_le {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  have hren : Function.Injective ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O) :=
    rename_injective _ j.injective
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), rename_comp_pointConeMap,
    AlgHom.id_comp]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)

/- English proof (translation)
Set `ren : MvPolynomial K' Φ →ₐ[O] MvPolynomial Λ Φ` to `(rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O`. Establish `hren : Function.Injective ren` using `rename_injective _ j.injective`. Set `F` to `ren.comp (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p)))`. Set `z : MvPolynomial Λ Φ` to `C (pt ⟨b, l⟩) * X b`. Establish `hLO : Function.Injective (algebraMap O (MvPolynomial Λ Φ))`.

Rewrite using `[IsScalarTower.algebraMap_eq O Φ (MvPolynomial Λ Φ)]`. Conclude with `(C_injective Λ Φ).comp hO`. Set `ψ : MvPolynomial Λ Φ →+* Polynomial (MvPolynomial Λ Φ)` to `eval₂Hom (Polynomial.C.comp C) (fun o => if o = b then Polynomial.C (C (pt ⟨b, l⟩)⁻¹) * Polynomial.X else Polynomial.C (X o))`. Establish `hψren : ψ.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom = Polynomial.C.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Simplify using `[ψ]`. Introduce `o`. Simplify using `[ψ, hjb o]`. Establish `hψz : ψ z = Polynomial.X`.

Simplify using `only [ψ, z, map_mul, eval₂Hom_C, eval₂Hom_X', if_true, RingHom.comp_apply]`. Rewrite using `[← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one, one_mul]`. Establish `hadj : Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ)) = F.range` using `Algebra.adjoin_eq _`. Establish `htr : Transcendental (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) z`. Rewrite using `[transcendental_iff]`.

Introduce `p hp`. Establish `hψA : ψ.comp (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ)) = Polynomial.C.comp (algebraMap _ (MvPolynomial Λ Φ))`. Use extensionality with `⟨a, ha⟩ : 1`. Take `⟨q, rfl⟩ : a ∈ F.range` from `hadj ▸ ha`. Conclude with `RingHom.congr_fun hψren _`.

Establish `h` using `congrArg ψ hp`. Rewrite `h` using `[Polynomial.aeval_def, Polynomial.hom_eval₂, hψA, hψz, map_zero]`. Conclude with `Polynomial.map_injective (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ)) Subtype.val_injective (by rw [Polynomial.map_zero]; exact h)`. Establish `hadd` using `AdjoinTrdegAdd.proof O (MvPolynomial Λ Φ) hLO (F.range : Set (MvPolynomial Λ Φ)) {z} Unit (fun _ => z) (by rintro _ ⟨_, rfl⟩; rfl) ((algebraicIndependent_unique_type_iff).2 htr) (fun a ha => by`. Rewrite using `[Set.mem_singleton_iff.1 ha]`.

Conclude with `isAlgebraic_algebraMap (⟨z, Algebra.subset_adjoin (Set.mem_union_right _ ⟨(), rfl⟩)⟩ : Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ Set.range fun _ : Unit => z)))`. Rewrite `hadd` using `[hadj, Fintype.card_unit, Nat.cast_one]`. Establish `hle : Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ {z}) ≤ (pointConeMap O pt).range`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ (⟨q, rfl⟩ | hz)`.

Conclude with `⟨rename (FieldNumbers.blockIncl j ι') q, (AlgHom.congr_fun (rename_comp_pointConeMap (O := O) ι' j pt) q).symm⟩`. Rewrite using `[Set.mem_singleton_iff.1 hz]`. Conclude with `⟨X ⟨b, l⟩, by simp [pointConeMap, z]⟩`. Rewrite using `[pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren, trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), AlgHom.id_comp]`. Express the relevant statement in the definitionally equal form `Algebra.trdeg O F.range + 1 ≤ _`.

Rewrite using `[← hadd]`. Conclude with `trdeg_le_of_injective (Subalgebra.inclusion hle) (Subalgebra.inclusion_injective _)`.
-/
theorem trdeg_blocks_add_one_le {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ]
    (hO : Function.Injective (algebraMap O Φ)) {Λ K' : Type} (ι' : Λ → Type) (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ)
    (b : Λ) (hjb : ∀ o, j o ≠ b) (l : ι' b) (hc : pt ⟨b, l⟩ ≠ 0) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) + 1 ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  classical
  let ren : MvPolynomial K' Φ →ₐ[O] MvPolynomial Λ Φ :=
    (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O
  have hren : Function.Injective ren := rename_injective _ j.injective
  let F := ren.comp (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p)))
  let z : MvPolynomial Λ Φ := C (pt ⟨b, l⟩) * X b
  have hLO : Function.Injective (algebraMap O (MvPolynomial Λ Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial Λ Φ)]
    exact (C_injective Λ Φ).comp hO

  let ψ : MvPolynomial Λ Φ →+* Polynomial (MvPolynomial Λ Φ) :=
    eval₂Hom (Polynomial.C.comp C)
      (fun o => if o = b then Polynomial.C (C (pt ⟨b, l⟩)⁻¹) * Polynomial.X else Polynomial.C (X o))
  have hψren : ψ.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom =
      Polynomial.C.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ψ]
    · intro o
      simp [ψ, hjb o]
  have hψz : ψ z = Polynomial.X := by
    simp only [ψ, z, map_mul, eval₂Hom_C, eval₂Hom_X', if_true, RingHom.comp_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one, one_mul]
  have hadj : Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ)) = F.range := Algebra.adjoin_eq _
  have htr : Transcendental (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) z := by
    rw [transcendental_iff]
    intro p hp
    have hψA : ψ.comp (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ)) =
        Polynomial.C.comp (algebraMap _ (MvPolynomial Λ Φ)) := by
      ext ⟨a, ha⟩ : 1
      obtain ⟨q, rfl⟩ : a ∈ F.range := hadj ▸ ha
      exact RingHom.congr_fun hψren _
    have h := congrArg ψ hp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hψA, hψz, map_zero] at h
    exact Polynomial.map_injective (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ))
      Subtype.val_injective (by rw [Polynomial.map_zero]; exact h)
  have hadd := AdjoinTrdegAdd.proof O (MvPolynomial Λ Φ) hLO (F.range : Set (MvPolynomial Λ Φ)) {z} Unit
    (fun _ => z) (by rintro _ ⟨_, rfl⟩; rfl) ((algebraicIndependent_unique_type_iff).2 htr)
    (fun a ha => by
      rw [Set.mem_singleton_iff.1 ha]
      exact isAlgebraic_algebraMap
        (⟨z, Algebra.subset_adjoin (Set.mem_union_right _ ⟨(), rfl⟩)⟩ :
          Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ Set.range fun _ : Unit => z)))
  rw [hadj, Fintype.card_unit, Nat.cast_one] at hadd
  have hle : Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ {z}) ≤ (pointConeMap O pt).range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ (⟨q, rfl⟩ | hz)
    · exact ⟨rename (FieldNumbers.blockIncl j ι') q,
        (AlgHom.congr_fun (rename_comp_pointConeMap (O := O) ι' j pt) q).symm⟩
    · rw [Set.mem_singleton_iff.1 hz]
      exact ⟨X ⟨b, l⟩, by simp [pointConeMap, z]⟩
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), AlgHom.id_comp]
  change Algebra.trdeg O F.range + 1 ≤ _
  rw [← hadd]
  exact trdeg_le_of_injective (Subalgebra.inclusion hle) (Subalgebra.inclusion_injective _)

def zeroNewBlocks {O K : Type} [CommRing O] {ι : K → Type} {M M' : ℕ} :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → MRing ι O
  | ⟨some (some k), i⟩ => X ⟨k, i⟩
  | ⟨some none, _⟩ => 0
  | ⟨none, _⟩ => 0

/- English proof (translation)
Set `ren : MvPolynomial K Φ →ₐ[O] MvPolynomial (Option (Option K)) Φ` to `(rename (fun k : K => some (some k)) : MvPolynomial K Φ →ₐ[Φ] _).restrictScalars O`. Establish `hren : Function.Injective ren` using `rename_injective _ ((Option.some_injective _).comp (Option.some_injective _))`. Establish `hG : pointConeMap O (flagClosurePt y w e φ φ' t 0) = (ren.comp (pointConeMap O (fun p => algebraMap Ω Φ (y p)))).comp (aeval (zeroNewBlocks (O` using `O))) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Apply the tactic sequence `rintro ⟨(_ | _ | k), i⟩ <;>`.

Simplify using `[ren, pointConeMap, flagClosurePt, pairProjCoord, projCoord, flagCoord, zeroNewBlocks]`. Rewrite using `[← pointIdeal_algebraMap (O := O) (Φ := Φ) y]`. Unfold `pointIdeal`. Rewrite using `[trdeg_quot_ker_eq_range (pointConeMap O (flagClosurePt y w e φ φ' t 0)) (AlgHom.id O _) (fun _ _ h => h), trdeg_quot_ker_eq_range (pointConeMap O (fun p => algebraMap Ω Φ (y p))) ren hren, AlgHom.id_comp, hG]`. Conclude with `trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _)) (Subalgebra.inclusion_injective _)`.
-/
theorem trdeg_flag_zero_le {O Ω K : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : K → Type} {N M M' : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
    (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (flagClosurePt y w e φ φ' t 0)) ≤
      Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) := by
  let ren : MvPolynomial K Φ →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (rename (fun k : K => some (some k)) : MvPolynomial K Φ →ₐ[Φ] _).restrictScalars O
  have hren : Function.Injective ren :=
    rename_injective _ ((Option.some_injective _).comp (Option.some_injective _))
  have hG : pointConeMap O (flagClosurePt y w e φ φ' t 0) =
      (ren.comp (pointConeMap O (fun p => algebraMap Ω Φ (y p)))).comp (aeval (zeroNewBlocks (O := O))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨(_ | _ | k), i⟩ <;>
      simp [ren, pointConeMap, flagClosurePt, pairProjCoord, projCoord, flagCoord, zeroNewBlocks]
  rw [← pointIdeal_algebraMap (O := O) (Φ := Φ) y]
  unfold pointIdeal
  rw [trdeg_quot_ker_eq_range (pointConeMap O (flagClosurePt y w e φ φ' t 0)) (AlgHom.id O _) (fun _ _ h => h),
    trdeg_quot_ker_eq_range (pointConeMap O (fun p => algebraMap Ω Φ (y p))) ren hren, AlgHom.id_comp, hG]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)

end FlagProjTrdegLe

open FlagProjTrdegLe in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hkN`. Establish `hO : Function.Injective (algebraMap O Φ)`. Rewrite using `[IsScalarTower.algebraMap_eq O Ω Φ]`. Use `(FaithfulSMul.algebraMap_injective Ω Φ).comp ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Establish `hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`. Rewrite using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha, map_zero]`. Rewrite `hy` using `[hV.noTorsion]`. Simplify using `using hy`.

Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Establish `h0` using `trdeg_flag_zero_le (O := O) y w e φ φ' t`. Simplify using `only [Nat.cast_zero, add_zero]`. Conclude with `⟨(trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') Function.Embedding.some (flagClosurePt y w e φ φ' t 0)).trans h0, (trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') secondFactorBlocks (flagClosurePt y w e φ φ' t 0)).trans h0⟩`. Establish `hH` using `hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN.le`.

Establish `hne : ∀ kk, ∃ i, y ⟨kk, i⟩ ≠ 0` using `fun kk => by`. Take `⟨i, hi⟩` from `hV.multiProj.relevant kk`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Rewrite using `[pointIdeal, RingHom.mem_ker]`. Simplify using `[pointConeMap, h0]`.

Use `choose c hc using hne`. Establish `hyc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun kk _ => hc kk`. Establish `hli` using `ht.linearIndependent`. Take `⟨l', hl'⟩` from `SegreFlagClosureModel.exists_flag_ne_zero w e hli φ' (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN.le`. Take `⟨l, hl⟩` from `SegreFlagClosureModel.exists_flag_ne_zero w e hli φ (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN.le`.

Establish `key : ∀ a : Cardinal, a + 1 ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal) → a ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal)`. Introduce `a ha`. Rewrite `ha` using `[Nat.cast_add, Nat.cast_one, ← add_assoc]`. Conclude with `Cardinal.add_one_le_add_one_iff.1 ha`. Use `⟨key _ ?_, key _ ?_⟩` and prove the remaining obligations.

Rewrite using `[← hH]`. Conclude with `trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') Function.Embedding.some (flagClosurePt y w e φ φ' t k) none (fun o => Option.some_ne_none o) l' hl'`. Rewrite using `[← hH]`. Apply the tactic sequence `exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') secondFactorBlocks (flagClosurePt y w e φ φ' t k) (some none) (by rintro (_ | _) h <;> cases h) l hl`.
-/
theorem FlagProjTrdegLe.proof (hTr : SegreFlagClosureTrdeg.Statement) : FlagProjTrdegLe.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hkN

  have hO : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    refine (FaithfulSMul.algebraMap_injective Ω Φ).comp ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 := trdeg_flag_zero_le (O := O) y w e φ φ' t
    simp only [Nat.cast_zero, add_zero]
    exact ⟨(trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') Function.Embedding.some
        (flagClosurePt y w e φ φ' t 0)).trans h0,
      (trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') secondFactorBlocks
        (flagClosurePt y w e φ φ' t 0)).trans h0⟩
  · have hH := hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN.le

    have hne : ∀ kk, ∃ i, y ⟨kk, i⟩ ≠ 0 := fun kk => by
      obtain ⟨i, hi⟩ := hV.multiProj.relevant kk
      refine ⟨i, fun h0 => hi ?_⟩
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    choose c hc using hne
    have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun kk _ => hc kk
    have hli := ht.linearIndependent
    obtain ⟨l', hl'⟩ := SegreFlagClosureModel.exists_flag_ne_zero w e hli φ'
      (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN.le
    obtain ⟨l, hl⟩ := SegreFlagClosureModel.exists_flag_ne_zero w e hli φ
      (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN.le
    have key : ∀ a : Cardinal, a + 1 ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal) →
        a ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) := by
      intro a ha
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at ha
      exact Cardinal.add_one_le_add_one_iff.1 ha
    refine ⟨key _ ?_, key _ ?_⟩
    · rw [← hH]
      exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') Function.Embedding.some
        (flagClosurePt y w e φ φ' t k) none (fun o => Option.some_ne_none o) l' hl'
    · rw [← hH]
      exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') secondFactorBlocks
        (flagClosurePt y w e φ φ' t k) (some none) (by rintro (_ | _) h <;> cases h) l hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
