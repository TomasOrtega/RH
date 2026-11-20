import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSummand

/- English proof (translation)
Introduce `F _ _ C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA O _ _ a`. Use `haveI : Nontrivial C₀ := by`. Use `⟨⟨0, 1, fun h ↦ ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (1 : C) ∈ RingHom.ker π` using `by rw [RingHom.mem_ker, map_one]; exact h.symm`. Establish `h2 : (1 : C) ∈ RingHom.ker π ^ 2`.

Rewrite using `[pow_two]`. Simplify using `using Ideal.mul_mem_mul h1 h1`. Rewrite `h2` using `[hsq]`. Conclude with `one_ne_zero ((Submodule.mem_bot C).1 h2)`. Use `haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ`.

Take `⟨red, hfin, hproj, hsurj, hker, -, hequiv, -⟩` from `GlobalTheory.T.exists_crystal_reduction_squareZero_artinian C C₀ π hπ hsq A₀ hA O a`. Set `a' : OAct (𝓞 F) A₀` to `{ act := fun x ↦ a.act (algebraMap (𝓞 F) O x) hom := fun x ↦ a.hom _ one := by rw [map_one]; exact a.one mul := fun x y ↦ by rw [mul_comm, map_mul, a.mul] add := fun x y ↦ by rw [map_add, a.add] }`. Take `⟨f, fsurj, fker, fequiv⟩` from `GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel C₀ A₀ hA (𝓞 F) a'`. Establish `hB` using `GlobalTheory.isAbelianScheme_pullback_obj (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ hA`. Establish `hP` using `GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers F (IsLocalRing.ResidueField C₀) _ hB (OAct.pullback _ A₀ a')`.

Set `σ : C →+* IsLocalRing.ResidueField C₀` to `(algebraMap C₀ (IsLocalRing.ResidueField C₀)).comp π`. Establish `hσ : Function.Surjective σ` using `IsLocalRing.residue_surjective.comp hπ`. Use `haveI : RingHomCompTriple π (algebraMap C₀ (IsLocalRing.ResidueField C₀)) σ := ⟨rfl⟩`. Establish `hle : RingHom.ker π ≤ RingHom.ker σ` using `fun b hb ↦ by`. Rewrite `hb`, the goal using `[RingHom.mem_ker]`.

Use `show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0`. Rewrite using `[hb, map_zero]`. Use `GlobalTheory.T.projective_tensor_of_fibre_projective' C (IsLocalRing.ResidueField C₀) (𝓞 F) σ hσ _ _ ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)) (act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback _ A₀ a')) (f.comp red) hfin h …` and prove the remaining obligations. Introduce `h hh`. Establish `h1 : red h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))` using `fker _ hh`.

Establish `h2 : ∀ y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)), ∃ x ∈ RingHom.ker σ • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)), red x = y`. Introduce `y hy`. Use `Submodule.smul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `c hc y _`. Take `⟨b, rfl⟩` from `hπ c`.

Take `⟨x, rfl⟩` from `hsurj y`. Use `⟨b • x, Submodule.smul_mem_smul ?_ Submodule.mem_top, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker] show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0`. Rewrite using `[IsLocalRing.ResidueField.algebraMap_eq]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hc`.

Conclude with `LinearMap.map_smulₛₗ red b x`. Introduce and unpack `y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩`. Conclude with `⟨x + x', add_mem hx hx', map_add _ _ _⟩`. Take `⟨x, hx, hxe⟩` from `h2 _ h1`. Establish `h3 : h - x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))` using `hker _ (by rw [map_sub, hxe, sub_self])`.

Establish `h4` using `Submodule.smul_mono_left hle h3`. Simplify using `using add_mem h4 hx`. Introduce `x h show f (red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a (algebraMap (𝓞 F) O x) h)) = _`. Rewrite using `[hequiv]`. Conclude with `fequiv x (red h)`.
-/
theorem crys_projective : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  intro F _ _ C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA O _ _ a
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  obtain ⟨red, hfin, hproj, hsurj, hker, -, hequiv, -⟩ := GlobalTheory.T.exists_crystal_reduction_squareZero_artinian C C₀ π hπ hsq A₀ hA O a
  let a' : OAct (𝓞 F) A₀ :=
    { act := fun x ↦ a.act (algebraMap (𝓞 F) O x)
      hom := fun x ↦ a.hom _
      one := by rw [map_one]; exact a.one
      mul := fun x y ↦ by rw [mul_comm, map_mul, a.mul]
      add := fun x y ↦ by rw [map_add, a.add] }
  obtain ⟨f, fsurj, fker, fequiv⟩ := GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel C₀ A₀ hA (𝓞 F) a'
  have hB := GlobalTheory.isAbelianScheme_pullback_obj (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ hA
  have hP := GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers F (IsLocalRing.ResidueField C₀) _ hB (OAct.pullback _ A₀ a')
  let σ : C →+* IsLocalRing.ResidueField C₀ := (algebraMap C₀ (IsLocalRing.ResidueField C₀)).comp π
  have hσ : Function.Surjective σ := IsLocalRing.residue_surjective.comp hπ
  haveI : RingHomCompTriple π (algebraMap C₀ (IsLocalRing.ResidueField C₀)) σ := ⟨rfl⟩
  have hle : RingHom.ker π ≤ RingHom.ker σ := fun b hb ↦ by
    rw [RingHom.mem_ker] at hb ⊢
    show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0
    rw [hb, map_zero]
  refine GlobalTheory.T.projective_tensor_of_fibre_projective' C (IsLocalRing.ResidueField C₀) (𝓞 F) σ hσ _ _
    ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O))
    (act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback _ A₀ a')) (f.comp red) hfin hproj
    (fsurj.comp hsurj) ?_ ?_ hP
  · intro h hh
    have h1 : red h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)) := fker _ hh
    have h2 : ∀ y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)),
        ∃ x ∈ RingHom.ker σ • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)), red x = y := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro c hc y _
        obtain ⟨b, rfl⟩ := hπ c
        obtain ⟨x, rfl⟩ := hsurj y
        refine ⟨b • x, Submodule.smul_mem_smul ?_ Submodule.mem_top, ?_⟩
        · rw [RingHom.mem_ker]
          show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0
          rw [IsLocalRing.ResidueField.algebraMap_eq]
          exact (IsLocalRing.residue_eq_zero_iff _).2 hc
        · exact LinearMap.map_smulₛₗ red b x
      · rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        exact ⟨x + x', add_mem hx hx', map_add _ _ _⟩
    obtain ⟨x, hx, hxe⟩ := h2 _ h1
    have h3 : h - x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)) :=
      hker _ (by rw [map_sub, hxe, sub_self])
    have h4 := Submodule.smul_mono_left hle h3
    simpa using add_mem h4 hx
  · intro x h
    show f (red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a (algebraMap (𝓞 F) O x) h)) = _
    rw [hequiv]
    exact fequiv x (red h)

end GlobalTheory.HTSummand
