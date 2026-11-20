import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

/- English proof (translation)
Introduce `L _ _ _ n V _ _ _ R U hU`. Take `⟨S, hS⟩` from `GlobalTheory.T.definiteUnitary_classSet_finite L n (U.subgroupOf (finU L n)) hU.2`. Set `T : AF R U →ₗ[ℂ] (S → V)` to `{ toFun := fun φ s => φ.1 s.1 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ h0 => ?_)` and prove the remaining obligations. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations.

Take `⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩` from `hS g`. Establish `hφ : IsAF R U φ.1` using `φ.2`. Establish `hz : φ.1 s = 0` using `congrFun h0 ⟨s, hs⟩`. Rewrite using `[hφ.level _ (Subgroup.mem_subgroupOf.1 hk), hφ.inf x hx, hφ.left γ hγ, hz, map_zero]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Sym.Al.afFin :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), IsLevel U → FiniteDimensional ℂ (AF R U) := by
  intro L _ _ _ n V _ _ _ R U hU
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite L n (U.subgroupOf (finU L n)) hU.2
  let T : AF R U →ₗ[ℂ] (S → V) :=
    { toFun := fun φ s => φ.1 s.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ h0 => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  have hφ : IsAF R U φ.1 := φ.2
  have hz : φ.1 s = 0 := congrFun h0 ⟨s, hs⟩
  rw [hφ.level _ (Subgroup.mem_subgroupOf.1 hk), hφ.inf x hx, hφ.left γ hγ, hz, map_zero]
  rfl
