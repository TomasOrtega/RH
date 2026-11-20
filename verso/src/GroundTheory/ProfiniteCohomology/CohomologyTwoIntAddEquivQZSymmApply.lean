import Mathlib
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.Characters
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem isAddTorsion_QZ : IsAddTorsion QZ := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q.den, q.den_pos, ?_⟩
  change ((q.den • q : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨q.num, ?_⟩
  rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num, zsmul_one]

section Eval

variable {G : Type*} [Group G] [TopologicalSpace G]

def evalCharacter (σ : G) : (Additive G →ₜ+ QZ) →+ QZ where
  toFun χ := χ (Additive.ofMul σ)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalCharacter_apply (σ : G) (χ : Additive G →ₜ+ QZ) :
    evalCharacter σ χ = χ (Additive.ofMul σ) :=
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem evalCharacter_injective {σ : G} (hσ : IsTopologicalGenerator σ) :
    Function.Injective (evalCharacter σ) := by
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  have hlc : IsLocallyConstant fun g : G => χ (Additive.ofMul g) :=
    (IsLocallyConstant.iff_continuous _).2 (χ.continuous.comp continuous_ofMul)
  have h := hσ.eq_of_forall_zpow hlc (IsLocallyConstant.const (0 : QZ)) fun n => by
    change χ (Additive.ofMul (σ ^ n)) = 0
    rw [ofMul_zpow, map_zsmul]
    change n • evalCharacter σ χ = 0
    rw [hχ, smul_zero]
  ext x
  exact congrFun h (Additive.toMul x)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem evalCharacter_surjective [IsTopologicalGroup G] {σ : G} (hσ : IsZHatGenerator σ) :
    Function.Surjective (evalCharacter σ) := by
  intro x
  have hn : 0 < addOrderOf x := (isAddTorsion_QZ x).addOrderOf_pos
  obtain ⟨φ, hφo, hφσ⟩ := hσ.exists_hom _ hn
  let ψ : ZMod (addOrderOf x) →+ QZ := ZMod.lift (addOrderOf x)
    ⟨zmultiplesHom QZ x, by simp [addOrderOf_nsmul_eq_zero]⟩
  let χ₀ : Additive G →+ QZ := ψ.comp (MonoidHom.toAdditive φ)
  have hlc : IsLocallyConstant fun a : Additive G => χ₀ a :=
    ((φ.isLocallyConstant_of_isOpen_ker hφo).comp fun z => ψ (Multiplicative.toAdd z)).comp_continuous
      continuous_toMul
  refine ⟨⟨χ₀, hlc.continuous⟩, ?_⟩
  change ψ (Multiplicative.toAdd (φ σ)) = x
  rw [hφσ, toAdd_ofAdd, ← Int.cast_one, ZMod.lift_coe]
  simp

noncomputable def evalCharacterEquiv [IsTopologicalGroup G] {σ : G} (hσ : IsZHatGenerator σ) :
    (Additive G →ₜ+ QZ) ≃+ QZ :=
  AddEquiv.ofBijective (evalCharacter σ) ⟨evalCharacter_injective hσ.dense, evalCharacter_surjective hσ⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalCharacterEquiv_apply [IsTopologicalGroup G] {σ : G} (hσ : IsZHatGenerator σ)
    (χ : Additive G →ₜ+ QZ) : evalCharacterEquiv hσ χ = χ (Additive.ofMul σ) :=
  rfl

end Eval

section H2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {σ : G}

noncomputable def cohomologyTwoIntIsoQZ (hσ : IsZHatGenerator σ) :
    cohomology (Rep.trivial ℤ G ℤ) 2 ≅ ModuleCat.of ℤ QZ :=
  cohomologyTwoIntIso G ≪≫ (evalCharacterEquiv hσ).toIntLinearEquiv.toModuleIso

noncomputable def cohomologyTwoIntAddEquivQZ (hσ : IsZHatGenerator σ) :
    cohomology (Rep.trivial ℤ G ℤ) 2 ≃+ QZ :=
  (cohomologyTwoIntAddEquiv G).trans (evalCharacterEquiv hσ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem cohomologyTwoIntAddEquivQZ_δ (hσ : IsZHatGenerator σ) (χ : Additive G →ₜ+ QZ) :
    cohomologyTwoIntAddEquivQZ hσ
      ((δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom
        ((cohomologyOneRatModIntIso G).inv.hom χ)) = χ (Additive.ofMul σ) := by
  rw [← cohomologyTwoIntAddEquiv_symm_apply, cohomologyTwoIntAddEquivQZ, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, evalCharacterEquiv_apply]

end H2

end GroundTheory.ProfCoh
