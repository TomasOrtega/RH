import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PSpaceDeg

/- English proof (translation)
Rewrite using `[ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k) (algebraMap ℤ k).injective_int]`. Conclude with `IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField`.
-/
theorem ringKrullDim_eq_one (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ringKrullDim k = 1 := by
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k)
    (algebraMap ℤ k).injective_int]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

/- English proof (translation)
The claim follows from `ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D`.
-/
theorem isArithVar (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    IsArithVar (PSpace.str k D) D :=
  ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D

/- English proof (translation)
Use `(RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comap_ker]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)`.
-/
theorem injective_ringHom {k : Type} [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (ψ : k →+* ℂ) : Function.Injective ψ := by
  refine (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

def ringHomEquiv (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] [Field K]
    [Algebra k K] [IsFractionRing k K] : (k →+* ℂ) ≃ (K →+* ℂ) where
  toFun ψ := IsFractionRing.lift (injective_ringHom ψ)
  invFun φ := φ.comp (algebraMap k K)
  left_inv ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom ψ) x
  right_inv φ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k) (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom (φ.comp (algebraMap k K))) x

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

/- English proof (translation)
Use `haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'`. Use `haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance`. Set `b` to `Module.Free.chooseBasis ℤ k`. Set `b'` to `b.localizationLocalization ℚ (nonZeroDivisors ℤ) K`.

Conclude with `⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm, Module.Finite.of_basis b'⟩`.
-/
theorem finrank_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    [Field K] [Algebra k K] [IsFractionRing k K] [CharZero K] :
    Module.finrank ℚ K = Module.finrank ℤ k ∧ FiniteDimensional ℚ K := by
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  let b := Module.Free.chooseBasis ℤ k
  let b' := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  exact ⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm,
    Module.Finite.of_basis b'⟩

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

/- English proof (translation)
Use `haveI : CharZero (FractionRing k) := charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))`. Take `⟨h1, h2⟩` from `finrank_fractionRing k (FractionRing k)`. Use `haveI : NumberField (FractionRing k) := ⟨⟩`. Rewrite using `[Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card, NumberField.Embeddings.card, h1]`.
-/
theorem card_ringHom (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  haveI : CharZero (FractionRing k) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
  obtain ⟨h1, h2⟩ := finrank_fractionRing k (FractionRing k)
  haveI : NumberField (FractionRing k) := ⟨⟩
  rw [Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card, h1]

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

open Set
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

/- English proof (translation)
Take `⟨c, h₁, h₂, h₃⟩` from `StdProjChart.exists_of_bijective (p := PSpace.str k N) σ (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)`. Use `⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩` and prove the remaining obligations. Establish `hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0)` using `h₁ ▸ c.e.map_target (h₂ ▸ trivial)`. Establish `h` using `Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N) (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1)) (c.e.symm v)`. Use `h.trans ?_` and prove the remaining obligations.

Establish `h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0) (c.e.symm v) = 1`. Simplify using `only [ProjSpace.ratio, ProjSpace.ratioOn_self]`. Rewrite using `[ev_eq hv, map_one]`. Establish `key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2`. Rewrite using `[Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]`.

Simplify using `only [Fin.succAbove_zero] at h₃`. Simplify using `only [h₃, norm_one, one_pow]`. Rewrite using `[← key]`. Simplify using `[Matrix.one_apply, ev]`.
-/
theorem exists_stdChart (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    ∃ (c : AlgChart (PSpace.str k N) σ N) (i : (ProjSpace.hermitianTwistingSheaf k N).B.ι),
      c.e.source = ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) ∧ c.e.target = Set.univ ∧
      c.e.source ⊆ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U i) ∧
      ∀ v, ((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  obtain ⟨c, h₁, h₂, h₃⟩ := StdProjChart.exists_of_bijective (p := PSpace.str k N) σ
    (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)
  refine ⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩
  have hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) :=
    h₁ ▸ c.e.map_target (h₂ ▸ trivial)
  have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N)
    (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1))
    (c.e.symm v)
  refine h.trans ?_
  have h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0)
      (c.e.symm v) = 1 := by
    simp only [ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv, map_one]
  have key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0)
      (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
    rw [Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.succAbove_zero] at h₃
    simp only [h₃, norm_one, one_pow]
  rw [← key]
  simp [Matrix.one_apply, ev]

/- English proof (translation)
Establish `hA` using `isArithVar k N`. Establish `hproj : IsProjOver (PSpace.str k N)` using `hA.isProjOver`. Use `haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N`. Use `haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj`. Establish `hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf` using `(ProjSpace.hermitianTwistingSheaf k N).cInf _`.

Establish `hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N` using `(HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _`. Use `⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩` and prove the remaining obligations. Take `⟨c, i, hsrc, htgt, hsub, hφv⟩` from `exists_stdChart k σ N`. Establish `hmem : c.e.symm 0 ∈ c.e.source` using `c.e.map_target (htgt ▸ mem_univ _)`. Establish `hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0`.

Establish `h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0)` using `hsrc ▸ hmem`. Conclude with `((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2 ⟨_, by simp, mem_ptsIn.1 h0⟩`. Establish `hnull` using `ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1`. Establish `hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ = {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ}`. Use extensionality with `y`.

Simplify using `[mem_ptsIn]`. Rewrite `hnull` using `[← hcX, ← hsrc]`. Establish `hmeas : MeasurableSet c.e.source` using `c.e.open_source.measurableSet`. Rewrite using `[← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero, Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt, Measure.restrict_univ]`. Use `Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)` and prove the remaining obligations.

Establish `hv : c.e.symm v ∈ c.e.source` using `c.e.map_target (htgt ▸ mem_univ _)`. Rewrite using `[AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]`. Establish `hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) = fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)` using `funext fun w => by rw [hφv w]`. Rewrite using `[hf, FSDet.det_fubiniStudy_hess N v]`. Simplify using the standard rewrite rules.
-/
theorem chern_mass_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (N : ℕ) (σ : k →+* ℂ) :
    ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 Set.univ = 1 ∧
      ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N (-1) Set.univ = 0 := by
  have hA := isArithVar k N
  have hproj : IsProjOver (PSpace.str k N) := hA.isProjOver
  haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf := (ProjSpace.hermitianTwistingSheaf k N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := exists_stdChart k σ N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ
    (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1
  have hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ =
      {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈
        ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ} := by
    ext y
    simp [mem_ptsIn]
  rw [← hcX, ← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, FSDet.det_fubiniStudy_hess N v]
  simp

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

/- English proof (translation)
Establish `hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1`. Introduce `σ`. Take `⟨h1, h0⟩` from `chern_mass_hermitian_O_one_projective k D σ`. Rewrite using `[GdegPullProof.chernInt_one, h1, h0]`. Simplify using the standard rewrite rules.

Use `haveI : Finite (k →+* ℂ) := by haveI : CharZero (FractionRing k) := charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k)) haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2 haveI : NumberField (FractionRing k) := ⟨ …`. Conclude with `Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm`. Use `haveI := Fintype.ofFinite (k →+* ℂ)`. Simplify using `only [gdeg, chInt, hσ]`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]`.
-/
theorem degree_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) := by
  have hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1 := by
    intro σ
    obtain ⟨h1, h0⟩ := chern_mass_hermitian_O_one_projective k D σ
    rw [GdegPullProof.chernInt_one, h1, h0]
    simp
  haveI : Finite (k →+* ℂ) := by
    haveI : CharZero (FractionRing k) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
    haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2
    haveI : NumberField (FractionRing k) := ⟨⟩
    exact Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [gdeg, chInt, hσ]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

/- English proof (translation)
Introduce `k _ _ _ _ D` and use `⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩`.
-/
theorem main : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ),
    IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧
      Nat.card (k →+* ℂ) = Module.finrank ℤ k :=
  fun k _ _ _ _ D => ⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩

end GlobalTheory.PSpaceDeg
