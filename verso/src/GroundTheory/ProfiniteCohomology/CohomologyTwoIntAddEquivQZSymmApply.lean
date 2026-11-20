import Mathlib
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.Characters
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

/- English proof (translation)
Introduce `x`. Take `⟨q, rfl⟩` from `QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) x`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q.den, q.den_pos, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((q.den • q : ℚ) : AddCircle (1 : ℚ)) = 0`. Rewrite using `[AddCircle.coe_eq_zero_iff]`.

Use `⟨q.num, ?_⟩` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num, zsmul_one]`.
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
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `χ hχ`. Establish `hlc : IsLocallyConstant fun g : G => χ (Additive.ofMul g)` using `(IsLocallyConstant.iff_continuous _).2 (χ.continuous.comp continuous_ofMul)`. Establish `h` using `hσ.eq_of_forall_zpow hlc (IsLocallyConstant.const (0 : QZ)) fun n => by`. Express the relevant statement in the definitionally equal form `χ (Additive.ofMul (σ ^ n)) = 0`.

Rewrite using `[ofMul_zpow, map_zsmul]`. Express the relevant statement in the definitionally equal form `n • evalCharacter σ χ = 0`. Rewrite using `[hχ, smul_zero]`. Use extensionality with `x`. Conclude with `congrFun h (Additive.toMul x)`.
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
Introduce `x`. Establish `hn : 0 < addOrderOf x` using `(isAddTorsion_QZ x).addOrderOf_pos`. Take `⟨φ, hφo, hφσ⟩` from `hσ.exists_hom _ hn`. Set `ψ : ZMod (addOrderOf x) →+ QZ` to `ZMod.lift (addOrderOf x) ⟨zmultiplesHom QZ x, by simp [addOrderOf_nsmul_eq_zero]⟩`. Set `χ₀ : Additive G →+ QZ` to `ψ.comp (MonoidHom.toAdditive φ)`.

Establish `hlc : IsLocallyConstant fun a : Additive G => χ₀ a` using `((φ.isLocallyConstant_of_isOpen_ker hφo).comp fun z => ψ (Multiplicative.toAdd z)).comp_continuous continuous_toMul`. Use `⟨⟨χ₀, hlc.continuous⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (Multiplicative.toAdd (φ σ)) = x`. Rewrite using `[hφσ, toAdd_ofAdd, ← Int.cast_one, ZMod.lift_coe]`. Simplify using the standard rewrite rules.
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
Rewrite using `[← cohomologyTwoIntAddEquiv_symm_apply, cohomologyTwoIntAddEquivQZ, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, evalCharacterEquiv_apply]`.
-/
theorem cohomologyTwoIntAddEquivQZ_δ (hσ : IsZHatGenerator σ) (χ : Additive G →ₜ+ QZ) :
    cohomologyTwoIntAddEquivQZ hσ
      ((δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom
        ((cohomologyOneRatModIntIso G).inv.hom χ)) = χ (Additive.ofMul σ) := by
  rw [← cohomologyTwoIntAddEquiv_symm_apply, cohomologyTwoIntAddEquivQZ, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, evalCharacterEquiv_apply]

end H2

end GroundTheory.ProfCoh
