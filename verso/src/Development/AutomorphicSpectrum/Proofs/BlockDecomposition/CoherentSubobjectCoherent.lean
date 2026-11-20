import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Establish `hEq` using `hE.1`. Establish `hC : (cokernel D.arrow).IsQuasicoherent` using `inferInstance`. Establish `hK : IsCoherent (kernel (cokernel.π D.arrow))` using `isCoherent_kernel _ hE`. Set `e : (D : X.Modules) ≅ kernel (cokernel.π D.arrow)` to `IsLimit.conePointUniqueUpToIso (Abelian.monoIsKernelOfCokernel (f := D.arrow) (CokernelCofork.ofπ _ (cokernel.condition D.arrow)) (cokernelIsCokernel _)) (limit.isLimit _)`. Use `⟨hD, fun U hU => ?_⟩` and prove the remaining obligations.

Use `hK.2 U hU` as an intermediate fact. Set `f : Γ(kernel (cokernel.π D.arrow), U) →ₗ[Γ(X, U)] Γ((D : X.Modules), U)` to `{ toFun := e.inv.app U map_add' := map_add _ map_smul' := Scheme.Modules.Hom.app_smul _ }`. Conclude with `Module.Finite.of_surjective f (bijective_app_of_iso e.symm U).2`.
-/
theorem isCoherent_subobject {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}
    (hE : IsCoherent E) (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) :
    IsCoherent (D : X.Modules) := by
  have hEq := hE.1
  have hC : (cokernel D.arrow).IsQuasicoherent := inferInstance
  have hK : IsCoherent (kernel (cokernel.π D.arrow)) := isCoherent_kernel _ hE
  let e : (D : X.Modules) ≅ kernel (cokernel.π D.arrow) :=
    IsLimit.conePointUniqueUpToIso
      (Abelian.monoIsKernelOfCokernel (f := D.arrow)
        (CokernelCofork.ofπ _ (cokernel.condition D.arrow)) (cokernelIsCokernel _))
      (limit.isLimit _)
  refine ⟨hD, fun U hU => ?_⟩
  have := hK.2 U hU
  let f : Γ(kernel (cokernel.π D.arrow), U) →ₗ[Γ(X, U)] Γ((D : X.Modules), U) :=
    { toFun := e.inv.app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective f (bijective_app_of_iso e.symm U).2

end GlobalTheory.CompanionTheory.GE
