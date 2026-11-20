import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorLocal

open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

/- English proof (translation)
Use `LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))` as an intermediate fact. Use `QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))` as an intermediate fact. Conclude with `⟨⟩`.
-/
theorem isNoetherian_of_finiteType {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact ⟨⟩

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = genericPoint X`. Substitute `hx` using the available equality. Express the relevant statement in the definitionally equal form `UniqueFactorizationMonoid X.functionField`. Use `infer_instance`.

Set `Z : PrimeDivisor X` to `⟨x, ringKrullDim_stalk_eq_one hX hx⟩`. Establish `: IsDedekindDomain (X.presheaf.stalk x)` using `Z.isDedekindDomain_stalk`. Establish `: IsPrincipalIdealRing (X.presheaf.stalk x)`. Use `IsPrincipalIdealRing.of_finite_maximals ?_` and prove the remaining obligations. Use `(Set.finite_singleton (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).subset ?_` and prove the remaining obligations.

Introduce `I hI`. Conclude with `IsLocalRing.eq_maximalIdeal hI`. Use `infer_instance`.
-/
theorem isLocallyFactorial_of_dim_le_one {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (hX : topologicalKrullDim X ≤ 1) : IsLocallyFactorial X := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    change UniqueFactorizationMonoid X.functionField
    infer_instance
  · let Z : PrimeDivisor X := ⟨x, ringKrullDim_stalk_eq_one hX hx⟩
    have : IsDedekindDomain (X.presheaf.stalk x) := Z.isDedekindDomain_stalk
    have : IsPrincipalIdealRing (X.presheaf.stalk x) := by
      refine IsPrincipalIdealRing.of_finite_maximals ?_
      refine (Set.finite_singleton (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).subset ?_
      intro I hI
      exact IsLocalRing.eq_maximalIdeal hI
    infer_instance

end GroundTheory.Arith.SchemeCoh
