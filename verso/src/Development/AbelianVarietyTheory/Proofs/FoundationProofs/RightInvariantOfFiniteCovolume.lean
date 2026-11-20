import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.VolumePerpendicular
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHostStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivialStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometryStatement

noncomputable section

namespace GlobalTheory.VolumeRatioTypings

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
open GlobalTheory.VolRatioCompare (reLat)
open scoped TensorProduct Matrix ENNReal

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ` as an intermediate fact. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ` using `Measure.isMulLeftInvariant_eq_smul _ μ`. Establish `h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ` using `h.preimage_of_equiv (f := (· * g)) ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩ Function.bijective_id fun γ x => mul_assoc _ _ _`.

Establish `h1 : μ.map (· * g) 𝓕 = μ 𝓕` using `((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)`. Rewrite `h1` using `[e, Measure.smul_apply, smul_eq_mul]`. Establish `h2` using `(ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)`. Rewrite using `[e, h2, one_smul]`.
-/
theorem rightInvariant_of_finite_covolume {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) : μ.IsMulRightInvariant := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  refine ⟨fun g => ?_⟩
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [e, h2, one_smul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Take `⟨i1, i2, i3⟩` from `GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram` as an intermediate fact. Establish `: BorelSpace (UpqT P Q)` using `⟨rfl⟩`. Establish `: LocallyCompactSpace (UpqT P Q)` using `(UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace`.

Use `D.cd.haar P Q` as an intermediate fact. Use `h.1` as an intermediate fact. Use `h'.1` as an intermediate fact. Establish `e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ` using `Measure.isMulLeftInvariant_eq_smul μ' μ`. Take `⟨U, hU1, hU, hfin⟩` from `(D.cd.cd P Q).exists_isOpen_measure_lt_top 1`.

Take `⟨θ, hθ⟩` from `h.2.1`. Take `⟨A, hA⟩` from `(h.2.2 θ hθ).1`. Establish `h1` using `(h.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet`. Establish `h2` using `(h'.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet`. Rewrite `h2` using `[e, Measure.smul_apply, smul_eq_mul, h1]`.

Establish `h3` using `(ENNReal.mul_left_inj (Finset.prod_ne_zero_iff.2 fun _ _ => hU.measure_ne_zero _ ⟨1, hU1⟩) (ENNReal.prod_ne_top fun _ _ => hfin.ne)).1 (h2.trans (one_mul _).symm)`. Rewrite using `[e, h3, one_smul]`.
-/
theorem volMeas_unique (V : HSp D) {P Q : ℕ} {μ μ' : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (h' : IsVolMeas D V P Q μ') : μ' = μ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have := D.cd.haar P Q
  have := h.1
  have := h'.1
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  obtain ⟨U, hU1, hU, hfin⟩ := (D.cd.cd P Q).exists_isOpen_measure_lt_top 1
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨A, hA⟩ := (h.2.2 θ hθ).1
  have h1 := (h.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  have h2 := (h'.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  rw [e, Measure.smul_apply, smul_eq_mul, h1] at h2
  have h3 := (ENNReal.mul_left_inj (Finset.prod_ne_zero_iff.2 fun _ _ => hU.measure_ne_zero _ ⟨1, hU1⟩)
    (ENNReal.prod_ne_top fun _ _ => hfin.ne)).1 (h2.trans (one_mul _).symm)
  rw [e, h3, one_smul]

/- English proof (translation)
Use `⟨hx, ⟨μ, h⟩, fun μ' h' => ?_⟩` and prove the remaining obligations. Take `rfl` from `volMeas_unique V h h'`. Use `⟨⟨𝓕, h𝓕⟩, fun 𝓖 h𝓖 => ?_⟩` and prove the remaining obligations. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram` as an intermediate fact. Use `h.1` as an intermediate fact.

Establish `: Countable (GQ V)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ'` as an intermediate fact. Establish `h𝓖' : IsFundamentalDomain (GQ V) 𝓖 μ'` using `h𝓖`. Conclude with `(h𝓖'.measure_eq h𝓕).trans e`.
-/
theorem isVol_of_pair (V : HSp D) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ) {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {x : ℝ} (hx : 0 < x) (e : μ 𝓕 = ENNReal.ofReal x) : IsVol D V P Q x := by
  refine ⟨hx, ⟨μ, h⟩, fun μ' h' => ?_⟩
  obtain rfl := volMeas_unique V h h'
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓖 h𝓖 => ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ'
  have h𝓖' : IsFundamentalDomain (GQ V) 𝓖 μ' := h𝓖
  exact (h𝓖'.measure_eq h𝓕).trans e

/- English proof (translation)
Take `⟨p, h1, h2⟩` from `GlobalTheory.VolPairExists.exists_volPair V hs`. Simplify using `only [hPQ] at h1`. Conclude with `⟨p.1, p.2, h1, h2⟩`.
-/
theorem exists_pair (V : HSp D) (hs : V.SigOK) {P Q : ℕ} (hPQ : ∀ τ, V.sig τ = (P, Q)) :
    ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsVolMeas D V P Q μ ∧ IsFundamentalDomain (GQ V) 𝓕 μ := by
  obtain ⟨p, h1, h2⟩ := GlobalTheory.VolPairExists.exists_volPair V hs
  simp only [hPQ] at h1
  exact ⟨p.1, p.2, h1, h2⟩

/- English proof (translation)
Take `⟨γ, hfin, hγ⟩` from `GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host D V L h1 h2`. Take `⟨k, hk, hkv⟩` from `GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial D V γ hfin`. Use `⟨k, hk, fun y => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E V y).trans (Iff.trans ?_ (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E (reLat V L h1 h2) _).symm)` and prove the remaining obligations. Use `forall_congr' fun v => (hγ v _).trans (iff_of_eq ?_)` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[← hkv v]`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom _ y i).symm`.
-/
theorem exists_conj (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : ∃ k ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) := by
  obtain ⟨γ, hfin, hγ⟩ := GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host D V L h1 h2
  obtain ⟨k, hk, hkv⟩ := GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial D V γ hfin
  refine ⟨k, hk, fun y => ?_⟩
  refine (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E V y).trans (Iff.trans ?_
    (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E (reLat V L h1 h2) _).symm)
  refine forall_congr' fun v => (hγ v _).trans (iff_of_eq ?_)
  congr 1
  rw [← hkv v]
  funext i
  exact (RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v)
    (AlgHom.id D.host.F D.host.E)).toRingHom _ y i).symm

/- English proof (translation)
Take `⟨k, hk, hkL⟩` from `exists_conj V L h1 h2`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram` as an intermediate fact. Use `h.1` as an intermediate fact. Use `⟨h.1, h.2.1, fun θ hθ => ⟨(h.2.2 θ hθ).1, fun A hA B hB => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← (h.2.2 θ hθ).2 A hA B hB, ← measure_preimage_mul μ k⁻¹, ← measure_preimage_mul_right μ k]`.

Use `congrArg μ (Set.ext fun (g : GA D V) => and_congr ?_ ?_)` and prove the remaining obligations. Use `show (∀ y : Fin V.rank → _, y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) ↔ (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2))) ↔ ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram (k⁻¹ * (g * k))).mulVec y ∈ …`. Establish `hm : ∀ (a b : GA D V) y, (finMat D.sp.cm.sig V.gram (a * b)).mulVec y = (finMat D.sp.cm.sig V.gram a).mulVec ((finMat D.sp.cm.sig V.gram b).mulVec y)` using `fun a b y => by`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, Matrix.mulVec_mulVec]`. Establish `ho : ∀ y, (finMat D.sp.cm.sig V.gram k).mulVec ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y) = y` using `fun y => by`.

Rewrite using `[← hm, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `hg y`. Use `(hkL y).trans (Iff.trans (hg _) (Iff.trans (iff_of_eq ?_) (hkL _).symm))` and prove the remaining obligations. Rewrite using `[hm, ho, hm]`.

Introduce `hg y`. Use `hg ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y)` as an intermediate fact. Use `(hkL _).symm.trans (this.trans (hkL _))` as an intermediate fact. Rewrite `this` using `[hm, hm, ho, ho]`. Conclude with `this`.

Establish `hk1 : ∀ a ∈ GfC V, ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) a = 1` using `fun a ha ρ => by`. Establish `ha' : infHom V a = 1` using `ha`. Rewrite using `[GlobalTheory.SmoothForms.RealPts.infMat_eq V, ha', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `forall_congr' fun ρ => ?_` and prove the remaining obligations. Establish `e : infMat D.sp.cm.sig V.gram (θ ρ) (k⁻¹ * (g * k)) = infMat D.sp.cm.sig V.gram (θ ρ) g`.

Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, hk1 k hk, hk1 _ (inv_mem hk), one_mul, mul_one]`. Conclude with `iff_of_eq (congrArg (fun m : Matrix (Fin (reLat V L h1 h2).rank) (Fin (reLat V L h1 h2).rank) ℂ => ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * m) e.symm)`.
-/
theorem isVolMeas_reLat (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (hr : μ.IsMulRightInvariant) : IsVolMeas D (reLat V L h1 h2) P Q μ := by
  obtain ⟨k, hk, hkL⟩ := exists_conj V L h1 h2
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  refine ⟨h.1, h.2.1, fun θ hθ => ⟨(h.2.2 θ hθ).1, fun A hA B hB => ?_⟩⟩
  rw [← (h.2.2 θ hθ).2 A hA B hB, ← measure_preimage_mul μ k⁻¹, ← measure_preimage_mul_right μ k]
  refine congrArg μ (Set.ext fun (g : GA D V) => and_congr ?_ ?_)
  · show (∀ y : Fin V.rank → _, y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) ↔
        (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2))) ↔
      ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram (k⁻¹ * (g * k))).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)
    have hm : ∀ (a b : GA D V) y, (finMat D.sp.cm.sig V.gram (a * b)).mulVec y =
        (finMat D.sp.cm.sig V.gram a).mulVec ((finMat D.sp.cm.sig V.gram b).mulVec y) := fun a b y => by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, Matrix.mulVec_mulVec]
    have ho : ∀ y, (finMat D.sp.cm.sig V.gram k).mulVec ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y) = y := fun y => by
      rw [← hm, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]
    constructor
    · intro hg y
      refine (hkL y).trans (Iff.trans (hg _) (Iff.trans (iff_of_eq ?_) (hkL _).symm))
      rw [hm, ho, hm]
    · intro hg y
      have := hg ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y)
      have := (hkL _).symm.trans (this.trans (hkL _))
      rw [hm, hm, ho, ho] at this
      exact this
  · have hk1 : ∀ a ∈ GfC V, ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := fun a ha ρ => by
      have ha' : infHom V a = 1 := ha
      rw [GlobalTheory.SmoothForms.RealPts.infMat_eq V, ha', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    refine forall_congr' fun ρ => ?_
    have e : infMat D.sp.cm.sig V.gram (θ ρ) (k⁻¹ * (g * k)) = infMat D.sp.cm.sig V.gram (θ ρ) g := by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, hk1 k hk, hk1 _ (inv_mem hk), one_mul, mul_one]
    exact iff_of_eq (congrArg (fun m : Matrix (Fin (reLat V L h1 h2).rank) (Fin (reLat V L h1 h2).rank) ℂ =>
      ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * m) e.symm)

/- English proof (translation)
Establish `h : ∀ x, (∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔ x ∈ V.L0` using `fun x => by conv_rhs => rw [← V.baseLattice_isUnimodular]`. Simplify using `[Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]`. Use extensionality with `x`. Rewrite using `[mem_tMap, ← h]`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, mem_tMap]`.

Use `⟨fun H y hy => ?_, fun H y hy => ?_⟩` and prove the remaining obligations. Use `H (e y) (by simpa using hy)` as an intermediate fact. Rewrite `this` using `[← e.apply_symm_apply x, he]`. Then use the resulting hypothesis. Rewrite using `[← isoSymm e he]`. Conclude with `H _ hy`.
-/
theorem tMap_unimod (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    Formalism.HermitianLatticesTheory.IsUnimodular V'.hT (tMap e V.L0) := by
  have h : ∀ x, (∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔ x ∈ V.L0 := fun x => by
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  ext x
  rw [mem_tMap, ← h]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    mem_tMap]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H (e y) (by simpa using hy)
    rwa [← e.apply_symm_apply x, he] at this
  · rw [← isoSymm e he]
    exact H _ hy

/- English proof (translation)
Take `⟨hx, ⟨μ, hμ⟩, hall⟩` from `h`. Take `⟨⟨𝓕, h𝓕⟩, hv⟩` from `hall μ hμ`. Set `V₁` to `reLat V' (tMap e V.L0) (tMap_lattice e _ V.standardTuple_isLattice) (tMap_unimod V V' e he)`. Apply the tactic sequence `obtain ⟨φ, hc, hc', hQ, hφ⟩ := GlobalTheory.T.exists_volume_transport_of_lattice_isometry D V V₁ e he fun x => by show _ ↔ e x ∈ tMap e V.L0`. Rewrite using `[mem_tMap, e.symm_apply_apply]`.

Take `⟨i1, i2, i3⟩` from `GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V₁.rank V₁.gram`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V₁.gram` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V₁.gram` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram` as an intermediate fact. Establish `: Countable (GQ V₁)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _`.

Set `ψ : GA D V ≃ᵐ GA D V₁` to `⟨φ.toEquiv, hc.measurable, hc'.measurable⟩`. Establish `hν` using `hφ P Q μ hμ`. Use `hν.1` as an intermediate fact. Establish `h𝓕' : IsFundamentalDomain (GQ V) 𝓕 μ` using `h𝓕`. Establish `h𝓖 : IsFundamentalDomain (GQ V₁) (φ.symm ⁻¹' 𝓕) (μ.map φ)` using `h𝓕'.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ ⟨ψ.measurable, rfl⟩).quasiMeasurePreserving (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩) ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)), fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩ fu …`.

Rewrite using `[map_mul, φ.symm_apply_apply]`. Establish `hvol : μ.map φ (φ.symm ⁻¹' 𝓕) = ENNReal.ofReal x`. Rewrite using `[← hv 𝓕 h𝓕]`. Use `(ψ.map_apply _).trans (congrArg μ ?_)` and prove the remaining obligations. Use extensionality with `g`.

Conclude with `iff_of_eq (congrArg (· ∈ 𝓕) (φ.symm_apply_apply g))`. Establish `hr` using `rightInvariant_of_finite_covolume (GQ V₁) (μ.map φ) h𝓖 (hvol ▸ ENNReal.ofReal_ne_top)`. Conclude with `isVol_of_pair V' (isVolMeas_reLat V₁ V'.L0 V'.standardTuple_isLattice V'.baseLattice_isUnimodular hν hr) h𝓖 hx hvol`.
-/
theorem isVol_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y)
    {P Q : ℕ} {x : ℝ} (h : IsVol D V P Q x) : IsVol D V' P Q x := by
  obtain ⟨hx, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  let V₁ := reLat V' (tMap e V.L0) (tMap_lattice e _ V.standardTuple_isLattice) (tMap_unimod V V' e he)
  obtain ⟨φ, hc, hc', hQ, hφ⟩ := GlobalTheory.T.exists_volume_transport_of_lattice_isometry D V V₁ e he fun x => by
    show _ ↔ e x ∈ tMap e V.L0
    rw [mem_tMap, e.symm_apply_apply]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V₁.rank V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V₁) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  let ψ : GA D V ≃ᵐ GA D V₁ := ⟨φ.toEquiv, hc.measurable, hc'.measurable⟩
  have hν := hφ P Q μ hμ
  have := hν.1
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 μ := h𝓕
  have h𝓖 : IsFundamentalDomain (GQ V₁) (φ.symm ⁻¹' 𝓕) (μ.map φ) :=
    h𝓕'.preimage_of_equiv (f := φ.symm)
      (MeasurePreserving.symm ψ ⟨ψ.measurable, rfl⟩).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  have hvol : μ.map φ (φ.symm ⁻¹' 𝓕) = ENNReal.ofReal x := by
    rw [← hv 𝓕 h𝓕]
    refine (ψ.map_apply _).trans (congrArg μ ?_)
    ext g
    exact iff_of_eq (congrArg (· ∈ 𝓕) (φ.symm_apply_apply g))
  have hr := rightInvariant_of_finite_covolume (GQ V₁) (μ.map φ) h𝓖 (hvol ▸ ENNReal.ofReal_ne_top)
  exact isVol_of_pair V' (isVolMeas_reLat V₁ V'.L0 V'.standardTuple_isLattice V'.baseLattice_isUnimodular hν hr) h𝓖 hx hvol

/- English proof (translation)
Establish `hw : (Matrix.of fun i j => W₂.hT (e (W₁.frame i)) (e (W₁.frame j))) = W₁.gram` using `Matrix.ext fun i j => he _ _`. Use `sig_family W₂ τ (D.sp.cm.cmUnram.2.1 τ) _ (hw ▸ h₁ τ) (h₂ τ)` as an intermediate fact. Establish `s1` using `sig_sum W₁ h₁ τ`. Establish `s2` using `sig_sum W₂ h₂ τ`. Conclude with `Prod.ext (by omega) (by omega)`.
-/
theorem sig_eq {W₁ W₂ : HSp D} (e : W₁.V ≃ₗ[D.host.E] W₂.V) (he : ∀ a b, W₂.hT (e a) (e b) = W₁.hT a b)
    (hr : W₁.rank = W₂.rank) (h₁ : W₁.SigOK) (h₂ : W₂.SigOK) (τ : D.host.E →+* ℂ) : W₂.sig τ = W₁.sig τ := by
  have hw : (Matrix.of fun i j => W₂.hT (e (W₁.frame i)) (e (W₁.frame j))) = W₁.gram :=
    Matrix.ext fun i j => he _ _
  have := sig_family W₂ τ (D.sp.cm.cmUnram.2.1 τ) _ (hw ▸ h₁ τ) (h₂ τ)
  have s1 := sig_sum W₁ h₁ τ
  have s2 := sig_sum W₂ h₂ τ
  exact Prod.ext (by omega) (by omega)

def OneVector (D : D7) (W : HSp D) (P Q : ℕ) (β : D.host.E) (P' Q' : ℕ) : Prop :=
  ∃ x : W.V, W.hT x x = β ∧ ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V),
    HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q')) ∧
    ∀ (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (μ' : Measure (GA D W')) (𝓕' : Set (GA D W')),
      IsVolMeas D W P Q μ → IsFundamentalDomain (GQ W) 𝓕 μ → IsVolMeas D W' P' Q' μ' →
      IsFundamentalDomain (GQ W') 𝓕' μ' →
      (μ 𝓕).toReal / (μ' 𝓕').toReal = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank

end GlobalTheory.VolumeRatioTypings
