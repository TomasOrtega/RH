import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ModelPresentation

/- English proof (translation)
Establish `hA` using `(GlobalTheory.isAmple_projective_O_one R N).pull_of_isClosedImmersion ι`. Establish `hL` using `hA.isLB`. Take `⟨a, ha⟩` from `(tendsto_natCast_atTop_atTop.eventually (hA.eventually_isGloballyGenerated_twistZ F)).exists`. Take `⟨k, s, hs⟩` from `GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 ha`. Establish `h₁` using `(GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs`.

Establish `h₂` using `(GlobalTheory.Twist.epi_map_iff (GlobalTheory.Twist.isLB_lbZPow hL (-(a : ℤ))) (GlobalTheory.QCoh.sectionsHom s)).2 h₁`. Conclude with `⟨a, k, (GlobalTheory.Twist.twistZPullIso ι (GlobalTheory.ProjSpace.O1_isLB R N) _ (-(a : ℤ))).inv ≫ GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫ (GlobalTheory.Twist.twistZAddIso F hL (add_neg_cancel (a : ℤ))).hom ≫ (GlobalTheory.Twist.twistZZeroIso F hL).inv, infe …`.
-/
theorem exists_epi_twist_free {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}} (ι : X ⟶ PSpace R N)
    [IsClosedImmersion ι] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] :
    ∃ (a m : ℕ) (φ : GlobalTheory.twist (GlobalTheory.QCoh.freeModule X (Fin m)) ((GlobalTheory.ProjSpace.On R N (-(a : ℤ))).pull ι) ⟶ F),
      Epi φ := by
  have hA := (GlobalTheory.isAmple_projective_O_one R N).pull_of_isClosedImmersion ι
  have hL := hA.isLB
  obtain ⟨a, ha⟩ := (tendsto_natCast_atTop_atTop.eventually (hA.eventually_isGloballyGenerated_twistZ F)).exists
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 ha
  have h₁ := (GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs
  have h₂ := (GlobalTheory.Twist.epi_map_iff (GlobalTheory.Twist.isLB_lbZPow hL (-(a : ℤ))) (GlobalTheory.QCoh.sectionsHom s)).2 h₁
  exact ⟨a, k, (GlobalTheory.Twist.twistZPullIso ι (GlobalTheory.ProjSpace.O1_isLB R N) _ (-(a : ℤ))).inv ≫
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫ (GlobalTheory.Twist.twistZAddIso F hL (add_neg_cancel (a : ℤ))).hom ≫
    (GlobalTheory.Twist.twistZZeroIso F hL).inv, inferInstance⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨cokernelEpiComp ψ (kernel.ι φ) ≪≫ (cokernelIsCokernel (kernel.ι φ)).coconePointUniqueUpToIso (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι φ) (kernel.condition φ)) (kernelIsKernel φ))⟩`.
-/
theorem nonempty_cokernel_iso {C : Type*} [Category C] [Abelian C] {A B F : C} (φ : B ⟶ F) [Epi φ]
    (ψ : A ⟶ kernel φ) [Epi ψ] : Nonempty (cokernel (ψ ≫ kernel.ι φ) ≅ F) :=
  ⟨cokernelEpiComp ψ (kernel.ι φ) ≪≫ (cokernelIsCokernel (kernel.ι φ)).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι φ) (kernel.condition φ)) (kernelIsKernel φ))⟩

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `: IsDiscreteValuationRing (c.V W)`. Use `(isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1` and prove the remaining obligations. Rewrite `hW`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`.

Break down `hW with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hp`. Conclude with `Or.inr fun h' => h (by simpa [Coeff.V] using h')`. Use `infer_instance`.
-/
theorem isNoetherianRing_place {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsNoetherianRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  infer_instance

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W hp hW Y i₀ Z F _`. Use `isNoetherianRing_place Z.i.c W hp.ne_zero hW` as an intermediate fact. Establish `: IsProper (PSpace.str (Z.i.c.V W) Z.n)` using `isProper_str _ _`. Establish `: IsLocallyNoetherian Z.X` using `LocallyOfFiniteType.isLocallyNoetherian (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n)`. Take `⟨a, m, φ, hφ⟩` from `exists_epi_twist_free Z.I.subschemeι F`.

Use `GlobalTheory.Twist.isFiniteQC_twist (F := GlobalTheory.QCoh.freeModule Z.X (Fin m)) (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB (Z.i.c.V W) Z.n (-(a : ℤ))) Z.I.subschemeι)` as an intermediate fact. Take `⟨a', m', ψ, hψ⟩` from `exists_epi_twist_free Z.I.subschemeι (kernel φ)`. Establish `h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F)` using `⟨⟨a, m, a', m', ψ ≫ kernel.ι φ⟩, nonempty_cokernel_iso φ ψ⟩`. Rewrite using `[Mdl.ofMod, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem nonempty_ofMod_toMod_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (F : Z.X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], Nonempty ((Z.ofMod F).toMod ≅ F) := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z F _
  have := isNoetherianRing_place Z.i.c W hp.ne_zero hW
  have : IsProper (PSpace.str (Z.i.c.V W) Z.n) := isProper_str _ _
  have : IsLocallyNoetherian Z.X :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n)
  obtain ⟨a, m, φ, hφ⟩ := exists_epi_twist_free Z.I.subschemeι F
  have := GlobalTheory.Twist.isFiniteQC_twist (F := GlobalTheory.QCoh.freeModule Z.X (Fin m))
    (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB (Z.i.c.V W) Z.n (-(a : ℤ))) Z.I.subschemeι)
  obtain ⟨a', m', ψ, hψ⟩ := exists_epi_twist_free Z.I.subschemeι (kernel φ)
  have h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F) :=
    ⟨⟨a, m, a', m', ψ ≫ kernel.ι φ⟩, nonempty_cokernel_iso φ ψ⟩
  rw [Mdl.ofMod, dif_pos h]
  exact h.choose_spec

end GlobalTheory.ModelPresentation
