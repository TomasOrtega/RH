import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.DataMink
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsTer
open NumberField Formalism.BasicNotions

namespace GlobalTheory.AutLattice

section
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem`. Consider the case `exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem`. Consider the case `(apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem ..)`.
-/
theorem exists_int_smul_mem (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem ..)

/- English proof (translation)
Set `_i : Module ℚ V` to `Module.compHom V (algebraMap ℚ E)`. Establish `: IsScalarTower ℚ E V` using `IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Rewrite using `[Module.finrank_mul_finrank ℚ E V, IsLocalization.finrank_eq ℚ (N := V) (nonZeroDivisors ℤ) le_rfl]`. Set `f : L →ₗ[ℤ] V` to `L.subtype.toAddMonoidHom.toIntLinearMap`. Establish `: IsLocalizedModule (nonZeroDivisors ℤ) f` using `{ map_units := fun s => (isLocalizedModule_id (nonZeroDivisors ℤ) V ℚ).map_units s surj := fun v => by`.

Take `⟨n, hn, h⟩` from `exists_int_smul_mem L hL v`. Conclude with `⟨(⟨n • v, h⟩, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), rfl⟩`. Use `exists_of_eq := fun {x y} h => ⟨1, by`. Establish `: x = y` using `Subtype.ext h`. Rewrite using `[this]⟩ }`.

Conclude with `(IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) f le_rfl).symm`.
-/
theorem finrank_int_eq (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) :
    Module.finrank ℤ L = Module.finrank ℚ E * Module.finrank E V := by
  let _i : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  rw [Module.finrank_mul_finrank ℚ E V,
    IsLocalization.finrank_eq ℚ (N := V) (nonZeroDivisors ℤ) le_rfl]
  let f : L →ₗ[ℤ] V := L.subtype.toAddMonoidHom.toIntLinearMap
  have : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    { map_units := fun s =>
        (isLocalizedModule_id (nonZeroDivisors ℤ) V ℚ).map_units s
      surj := fun v => by
        obtain ⟨n, hn, h⟩ := exists_int_smul_mem L hL v
        exact ⟨(⟨n • v, h⟩, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), rfl⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : x = y := Subtype.ext h
        rw [this]⟩ }
  exact (IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) f le_rfl).symm

end

/- English proof (translation)
Introduce `hM E V _ _ _ _ _ _ _ L hfg hL G hG hGL`. Establish `: Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.2 hfg`. Establish `: Module.Finite ℤ L` using `Module.Finite.trans (𝓞 E) L`. Establish `: IsAddTorsionFree V` using `IsAddTorsionFree.of_isTorsionFree E V`. Establish `: Module.Free ℤ L` using `inferInstance`.

Rewrite using `[← finrank_int_eq L hL]`. Set `b` to `Module.finBasis ℤ L`. Set `r : G →* Module.End ℤ L` to `{ toFun := fun g => AddMonoidHom.toIntLinearMap { toFun := fun x => ⟨g.1 x.1, hGL g.1 g.2 x.1 x.2⟩ map_zero' := Subtype.ext (by simp) map_add' := fun x y => Subtype.ext (by simp) } map_one' := by ext x; rfl map_mul' := fun g h => by ext x; rfl }`. Establish `hr : Function.Injective r`. Introduce `g h hgh`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Apply `LinearMap.ext_on hL` to reduce the goal to its premises. Introduce `x hx`. Conclude with `congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)`.

Set `φ : G →* GL (Fin (Module.finrank ℤ L)) ℤ` to `((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits`. Establish `hφ : Function.Injective φ`. Introduce `g h hgh`. Apply `hr` to reduce the goal to its premises. Apply `(LinearMap.toMatrixAlgEquiv b).injective` to reduce the goal to its premises.

Conclude with `congrArg Units.val hgh`. Establish `e` using `MonoidHom.ofInjective hφ`. Rewrite using `[Nat.card_congr e.toEquiv]`. Conclude with `hM _ φ.range (Finite.of_equiv _ e.toEquiv)`.
-/
theorem card_dvd_minkM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V), L.FG → Submodule.span E (L : Set V) = ⊤ → ∀ G : Subgroup (V ≃ₗ[E] V), Finite G → (∀ g ∈ G, ∀ x ∈ L, g x ∈ L) → Nat.card G ∣ minkM (Module.finrank ℚ E * Module.finrank E V) := by
  intro hM E V _ _ _ _ _ _ _ L hfg hL G hG hGL
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree E V
  have : Module.Free ℤ L := inferInstance
  rw [← finrank_int_eq L hL]
  let b := Module.finBasis ℤ L
  let r : G →* Module.End ℤ L :=
    { toFun := fun g => AddMonoidHom.toIntLinearMap
        { toFun := fun x => ⟨g.1 x.1, hGL g.1 g.2 x.1 x.2⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      map_one' := by ext x; rfl
      map_mul' := fun g h => by ext x; rfl }
  have hr : Function.Injective r := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hL
    intro x hx
    exact congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)
  let φ : G →* GL (Fin (Module.finrank ℤ L)) ℤ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply hr
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact congrArg Units.val hgh
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM _ φ.range (Finite.of_equiv _ e.toEquiv)

end GlobalTheory.AutLattice
