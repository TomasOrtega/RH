import Mathlib
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.FieldNumbers

universe u

/- English proof (translation)
Take `⟨s, g, hginj, hgfin⟩` from `exists_finite_inj_algHom_of_fg k A`. Use `set B := MvPolynomial (Fin s) k`. Set `: Algebra B A` to `g.toRingHom.toAlgebra`. Establish `: Module.Finite B A` using `hgfin`. Set `: Algebra B K` to `((algebraMap A K).comp (algebraMap B A)).toAlgebra`.

Set `: Algebra B L` to `((algebraMap A L).comp (algebraMap B A)).toAlgebra`. Establish `: IsScalarTower B A K` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: IsScalarTower B A L` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: IsScalarTower B K L` using `IsScalarTower.of_algebraMap_eq fun x => by`. Express the relevant statement in the definitionally equal form `algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))`.

Conclude with `IsScalarTower.algebraMap_apply A K L _`. Establish `hinjBK : Function.Injective (algebraMap B K)` using `(IsFractionRing.injective A K).comp hginj`. Establish `: FaithfulSMul B K` using `(faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK`. Set `: Algebra (FractionRing B) K` to `FractionRing.liftAlgebra B K`. Set `: Algebra (FractionRing B) L` to `((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra`.

Establish `: IsScalarTower (FractionRing B) K L` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: IsScalarTower B (FractionRing B) L` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply (FractionRing B) K L, ← IsScalarTower.algebraMap_apply B (FractionRing B) K, ← IsScalarTower.algebraMap_apply B K L]`. Establish `: Algebra.IsIntegral B A` using `Algebra.IsIntegral.of_finite B A`. Establish `: FiniteDimensional (FractionRing B) K`.

Take `⟨t, ht⟩` from `(Module.Finite.fg_top : (⊤ : Submodule B A).FG)`. Set `T : Set K` to `algebraMap A K '' t`. Establish `hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x`. Introduce and unpack `_ ⟨a, -, rfl⟩`. Establish `: IsIntegral B (algebraMap A K a)` using `(Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)`.

Conclude with `this.tower_top`. Establish `: Finite T` using `(t.finite_toSet.image _).to_subtype`. Establish `hfd` using `IntermediateField.finiteDimensional_adjoin hTint`. Establish `htop : IntermediateField.adjoin (FractionRing B) T = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `x -`. Establish `hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T`. Introduce `a`. Establish `ha : a ∈ Submodule.span B (t : Set A)` using `ht ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul b y _ hy`.

Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B (FractionRing B) K]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) hy`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := A) x`. Conclude with `div_mem (hA a) (hA b)`. Rewrite `hfd` using `[htop]`.

Conclude with `(IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional`. Establish `: FiniteDimensional (FractionRing B) L` using `Module.Finite.trans K L`. Establish `hB` using `hpoly s L`. Establish `hle : (integralClosure A L).toSubmodule.restrictScalars B ≤ (integralClosure B L).toSubmodule` using `fun y hy => isIntegral_trans (R := B) (A := A) y hy`. Establish `: IsNoetherian B (integralClosure B L).toSubmodule` using `isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)`.

Establish `: IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B)` using `isNoetherian_of_le hle`. Establish `: Module.Finite B (integralClosure A L)` using `Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)`. Conclude with `Module.Finite.of_restrictScalars_finite B A (integralClosure A L)`.
-/
theorem finite_integralClosure_of_forall_mvPolynomial
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L]
    (hpoly : ∀ (s : ℕ) (L' : Type u) [Field L'] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L']
      [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L']
      [Algebra (MvPolynomial (Fin s) k) L']
      [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L'],
      Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L')) :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  set B := MvPolynomial (Fin s) k
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hgfin
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  let : Algebra B L := ((algebraMap A L).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))
    exact IsScalarTower.algebraMap_apply A K L _
  have hinjBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hginj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK
  let : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  let : Algebra (FractionRing B) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra
  have : IsScalarTower (FractionRing B) K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (FractionRing B) L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing B) K L,
      ← IsScalarTower.algebraMap_apply B (FractionRing B) K,
      ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional (FractionRing B) K := by
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B A).FG)
    let T : Set K := algebraMap A K '' t
    have hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x := by
      rintro _ ⟨a, -, rfl⟩
      have : IsIntegral B (algebraMap A K a) :=
        (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)
      exact this.tower_top
    have : Finite T := (t.finite_toSet.image _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing B) T = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T := by
        intro a
        have ha : a ∈ Submodule.span B (t : Set A) := ht ▸ Submodule.mem_top
        induction ha using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
        | smul b y _ hy =>
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply B (FractionRing B) K]
          exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional (FractionRing B) L := Module.Finite.trans K L
  have hB := hpoly s L
  have hle : (integralClosure A L).toSubmodule.restrictScalars B ≤
      (integralClosure B L).toSubmodule := fun y hy => isIntegral_trans (R := B) (A := A) y hy
  have : IsNoetherian B (integralClosure B L).toSubmodule :=
    isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)
  have : IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B) :=
    isNoetherian_of_le hle
  have : Module.Finite B (integralClosure A L) :=
    Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

/- English proof (translation)
The claim follows from `IsIntegralClosure.finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L (integralClosure (MvPolynomial (Fin s) k) L)`.
-/
theorem finite_integralClosure_mvPolynomial_of_isSeparable (k : Type u) [Field k] (s : ℕ)
    (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) :=
  IsIntegralClosure.finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L
    (integralClosure (MvPolynomial (Fin s) k) L)

/- English proof (translation)
Establish `: CharZero (FractionRing (MvPolynomial (Fin s) k))` using `(RingHom.charZero_iff ((algebraMap (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k))).comp (algebraMap k (MvPolynomial (Fin s) k))).injective).mp inferInstance`. Conclude with `finite_integralClosure_mvPolynomial_of_isSeparable k s L`.
-/
theorem finite_integralClosure_mvPolynomial_of_charZero (k : Type u) [Field k] [CharZero k]
    (s : ℕ) (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by
  have : CharZero (FractionRing (MvPolynomial (Fin s) k)) :=
    (RingHom.charZero_iff ((algebraMap (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k))).comp (algebraMap k (MvPolynomial (Fin s) k))).injective).mp
      inferInstance
  exact finite_integralClosure_mvPolynomial_of_isSeparable k s L

/- English proof (translation)
The claim follows from `finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ => finite_integralClosure_mvPolynomial_of_charZero k s L'`.
-/
theorem finite_integralClosure_of_charZero
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) :=
  finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ =>
    finite_integralClosure_mvPolynomial_of_charZero k s L'

end GroundTheory.Heights₂.Heights.FieldNumbers
