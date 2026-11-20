import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FilTop

section Inj
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Establish `hτ : ∀ T, Function.Bijective ((toSq a b ha).τ T)`. Introduce `T`. Use `⟨fun x y hxy => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `h1 : (Ideal.Quotient.mk (b.S T) (show A.obj T from x)) = Ideal.Quotient.mk (b.S T) (show A.obj T from y)` using `congrArg Subtype.val hxy`. Rewrite `h1` using `[Ideal.Quotient.eq, hb T, Ideal.mem_bot, sub_eq_zero]`.

Conclude with `h1`. Take `⟨z, hz⟩` from `z`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `⟨x, rfl⟩`. Use `⟨fun f g hfg => ?_, fun f' => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `s`. Conclude with `(hτ _).1 (congrFun hfg s)`. Use `⟨fun s => Function.surjInv (hτ _).2 (f' s), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Conclude with `Function.surjInv_eq (hτ _).2 (f' s)`.
-/
theorem toSq_pullC_bij (a b : IdF A) (ha : ∀ T, a.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (n : ℕ) :
    Function.Bijective ((toSq a b ha).pullC n) := by
  have hτ : ∀ T, Function.Bijective ((toSq a b ha).τ T) := by
    intro T
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (Ideal.Quotient.mk (b.S T) (show A.obj T from x)) = Ideal.Quotient.mk (b.S T) (show A.obj T from y) :=
        congrArg Subtype.val hxy
      rw [Ideal.Quotient.eq, hb T, Ideal.mem_bot, sub_eq_zero] at h1
      exact h1
    · obtain ⟨z, hz⟩ := z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨x, rfl⟩
  refine ⟨fun f g hfg => ?_, fun f' => ?_⟩
  · funext s
    exact (hτ _).1 (congrFun hfg s)
  · refine ⟨fun s => Function.surjInv (hτ _).2 (f' s), ?_⟩
    funext s
    exact Function.surjInv_eq (hτ _).2 (f' s)

end Inj

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `m.pull n (Submodule.Quotient.mk z) = 0 at hx`.

Unfold `CH.Mor.pull Cx.Hom.mapH at hx`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `m.pullC n z.1 ∈ (CH.cx F').B n at hx`. Express the relevant statement in the definitionally equal form `z.1 ∈ (CH.cx F).B n`. Consider the cases of `n with`.

Consider the case `zero`. Establish `h0 : m.pullC 0 z.1 = 0` using `hx`. Establish `: z.1 = 0` using `(hb 0).1 (h0.trans (map_zero _).symm)`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `succ n`. Take `⟨g, hg⟩` from `hx`. Take `⟨g0, rfl⟩` from `(hb n).2 g`. Use `⟨g0, (hb (n + 1)).1 ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `m.pullC (n + 1) (CH.d F n g0) = m.pullC (n + 1) z.1`.

Rewrite using `[← CH.Mor.d_pullC]`. Conclude with `hg`.
-/
theorem pull_inj_of_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {C' : Type 1} [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
    (hb : ∀ n, Function.Bijective (m.pullC n)) (n : ℕ) : Function.Injective (m.pull n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  change m.pull n (Submodule.Quotient.mk z) = 0 at hx
  unfold CH.Mor.pull Cx.Hom.mapH at hx
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  change m.pullC n z.1 ∈ (CH.cx F').B n at hx
  change z.1 ∈ (CH.cx F).B n
  cases n with
  | zero =>
    have h0 : m.pullC 0 z.1 = 0 := hx
    have : z.1 = 0 := (hb 0).1 (h0.trans (map_zero _).symm)
    rw [this]; exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨g, hg⟩ := hx
    obtain ⟨g0, rfl⟩ := (hb n).2 g
    refine ⟨g0, (hb (n + 1)).1 ?_⟩
    change m.pullC (n + 1) (CH.d F n g0) = m.pullC (n + 1) z.1
    rw [← CH.Mor.d_pullC]
    exact hg

/- English proof (translation)
Introduce `_ _ _ _ _ hKIso _ K _ _ X q _ d _ j x hx`. Take `⟨U, hU⟩` from `(GlobalTheory.T.exists_smooth_coordinate_cover q).2 d inferInstance`. Establish `h𝒱 : sSup (Set.range U.U) = ⊤` using `by rw [sSup_range]; exact U.cover`. Establish `hk` using `hKIso q U (d + 1) (fun α => by rw [hU α]; omega) (Set.range U.U) h𝒱 j`. Establish `h0 : quoK q (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ) j x = 0` using `(hk.2 (d + 1) le_rfl x).1 hx`.

Establish `hb : ∀ T, (sFil (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ)).S T = ⊥`. Introduce `T`. Express the relevant statement in the definitionally equal form `T.obj.pdPow ((d + 1 : ℕ) : ℤ).toNat = ⊥`. Rewrite using `[Int.toNat_natCast]`. Conclude with `T.property.1.1`.

Establish `hinj` using `GlobalTheory.CompanionTheory.FilTop.pull_inj_of_bij _ (GlobalTheory.CompanionTheory.FilTop.toSq_pullC_bij (sFil (KS q (d + 1) (Set.range U.U)) 0) _ (fun T => T.obj.pdPow_zero) hb) j`. Establish `h1 : resK q (KS q (d + 1) (Set.range U.U)) j x = 0` using `hinj (by`. Rewrite using `[map_zero]`. Conclude with `h0)`. Conclude with `hk.1.1 (h1.trans (map_zero _).symm)`.
-/
theorem fil_top_vanish : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  intro _ _ _ _ _ hKIso _ K _ _ X q _ d _ j x hx
  obtain ⟨U, hU⟩ := (GlobalTheory.T.exists_smooth_coordinate_cover q).2 d inferInstance
  have h𝒱 : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hk := hKIso q U (d + 1) (fun α => by rw [hU α]; omega) (Set.range U.U) h𝒱 j
  have h0 : quoK q (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ) j x = 0 := (hk.2 (d + 1) le_rfl x).1 hx
  have hb : ∀ T, (sFil (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ)).S T = ⊥ := by
    intro T
    change T.obj.pdPow ((d + 1 : ℕ) : ℤ).toNat = ⊥
    rw [Int.toNat_natCast]
    exact T.property.1.1
  have hinj := GlobalTheory.CompanionTheory.FilTop.pull_inj_of_bij _
    (GlobalTheory.CompanionTheory.FilTop.toSq_pullC_bij (sFil (KS q (d + 1) (Set.range U.U)) 0) _ (fun T => T.obj.pdPow_zero) hb) j
  have h1 : resK q (KS q (d + 1) (Set.range U.U)) j x = 0 := hinj (by
    rw [map_zero]; exact h0)
  exact hk.1.1 (h1.trans (map_zero _).symm)

end GlobalTheory.CompanionTheory.FilTop
