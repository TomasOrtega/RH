import Mathlib

universe u v w x

variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]

namespace Derivation

/- English proof (authored)
Multiplication by y on N agrees with the action of its image in S′, which is a unit. Acting by the inverse unit gives the inverse additive map. It is S-linear because scalars from S commute with those from S′, so this is an inverse in the endomorphism ring over S.
-/
private theorem isUnit_algebraMap_moduleEnd (M : Submonoid S) [IsLocalization M S'] (y : M) :
    IsUnit ((algebraMap S (Module.End S N)) (y : S)) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units (M := M) S' y
  have hcomm : ∀ (s : S) (c : S') (n : N), c • s • n = s • c • n := by
    intro s c n
    rw [← IsScalarTower.algebraMap_smul S' s n, ← IsScalarTower.algebraMap_smul S' s (c • n),
      smul_smul, smul_smul, mul_comm]
  have h1 : ∀ n : N, (y : S) • (((u⁻¹ : S'ˣ) : S') • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) (((u⁻¹ : S'ˣ) : S') • n), ← hu, smul_smul,
      u.mul_inv, one_smul]
  have h2 : ∀ n : N, ((u⁻¹ : S'ˣ) : S') • ((y : S) • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) n, ← hu, smul_smul, u.inv_mul, one_smul]
  exact ⟨⟨(algebraMap S (Module.End S N)) (y : S),
    { toFun := fun n => ((u⁻¹ : S'ˣ) : S') • n
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s n => hcomm s ((u⁻¹ : S'ˣ) : S') n },
    LinearMap.ext fun n => h1 n, LinearMap.ext fun n => h2 n⟩, rfl⟩

/- English proof (authored)
Factor D through the universal derivation to obtain an S-linear map from the differential module to N. Every element inverted in S′ acts invertibly on N. Thus the linear map extends across the localization of the differential module, which is the differential module of S′ over R. The extension is S′-linear, since the action of each inverted scalar is forced by its inverse. Compose with the universal derivation on S′. Naturality of the universal differential and the extension property show that the result agrees with D on the images of S.
-/
private theorem exists_liftToLocalization (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' N, ∀ s : S, D' (algebraMap S S' s) = D s := by
  have hu : ∀ y : M, IsUnit ((algebraMap S (Module.End S N)) (y : S)) := fun y =>
    isUnit_algebraMap_moduleEnd (S' := S') M y
  have : IsLocalizedModule M (KaehlerDifferential.map R R S S') := inferInstance
  refine ⟨(LinearMap.extendScalarsOfIsLocalization M S'
      (IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu)).compDer (KaehlerDifferential.D R S'), fun s => ?_⟩
  show IsLocalizedModule.lift M (KaehlerDifferential.map R R S S') D.liftKaehlerDifferential hu
      (KaehlerDifferential.D R S' (algebraMap S S' s)) = D s
  have key : IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu
        (KaehlerDifferential.map R R S S' (KaehlerDifferential.D R S s))
      = D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun
      (IsLocalizedModule.lift_comp M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu) (KaehlerDifferential.D R S s)
  rw [← KaehlerDifferential.map_D R R S S' s, key]
  exact D.liftKaehlerDifferential_comp_D s

noncomputable def liftToLocalization (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' N :=
  (exists_liftToLocalization (S' := S') D M).choose

@[simp]
/- English proof (authored)
The chosen derivation is selected from the extensions of D to the localization. Every extension in this construction takes the image of s to D(s), so the chosen one does as well.
-/
theorem liftToLocalization_algebraMap (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] (s : S) :
    (D.liftToLocalization (S' := S') M) (algebraMap S S' s) = D s :=
  (exists_liftToLocalization (S' := S') D M).choose_spec s

/- English proof (authored)
Compose D with the localization map on its values, so it becomes a derivation on S with values in S′. Extend this derivation to S′ using the localization property. It then sends an element coming from s to the localization of D(s).
-/
private theorem exists_mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' S', ∀ s : S,
      D' (algebraMap S S' s) = algebraMap S S' (D s) := by
  obtain ⟨D', hD'⟩ :=
    exists_liftToLocalization (S' := S') (N := S') ((Algebra.linearMap S S').compDer D) M
  exact ⟨D', fun s => hD' s⟩

noncomputable def mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' S' :=
  (exists_mapToLocalization (S' := S') D M).choose

@[simp]
/- English proof (authored)
The chosen derivation on S′ extends the original derivation with its values mapped to S′. Its evaluation on the image of s is therefore the image of D(s).
-/
theorem mapToLocalization_algebraMap (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] (s : S) :
    (D.mapToLocalization (S' := S') M) (algebraMap S S' s) = algebraMap S S' (D s) :=
  (exists_mapToLocalization (S' := S') D M).choose_spec s

/- English proof (authored)
The derivation D corresponds to a linear map from the differential module over S to S′. Because the module is finitely presented, a common denominator from the multiplicative set clears this linear map. Indeed one can clear denominators on a finite generating set and then multiply by another element of the multiplicative set to kill the images of the finitely many relations. Thus the cleared map comes from a linear map to S. Compose that map with the universal derivation to obtain D₀. Evaluating the cleared equality on each differential gives the asserted formula.
-/
theorem exists_derivation_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D s = algebraMap S S' (D₀ s) := by
  obtain ⟨ψ, m, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    M (Algebra.linearMap S S') D.liftKaehlerDifferential
  refine ⟨m, LinearMap.compDer ψ (KaehlerDifferential.D R S), fun s => ?_⟩
  have h1 : algebraMap S S' (ψ (KaehlerDifferential.D R S s))
      = (m : S) • D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun hψ (KaehlerDifferential.D R S s)
  rw [Derivation.liftKaehlerDifferential_comp_D, Algebra.smul_def] at h1
  exact h1.symm

/- English proof (authored)
Precompose D with the ring map from S to S′, viewing its values in S′. This is a derivation over R on S. Apply the common denominator result for derivations from S to S′ and evaluate the resulting equality on s.
-/
theorem exists_derivation_mul_eq_of_isLocalization (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S' S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₀ s) := by
  obtain ⟨m, D₀, h⟩ := exists_derivation_mul_eq (S' := S') M (D.compAlgebraMap S)
  exact ⟨m, D₀, fun s => h s⟩

end Derivation
