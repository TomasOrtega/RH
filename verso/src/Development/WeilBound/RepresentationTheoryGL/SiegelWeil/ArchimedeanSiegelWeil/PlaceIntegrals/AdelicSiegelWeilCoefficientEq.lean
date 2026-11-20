import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FubiniFourierHermitianIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAllStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.HermitianLatticeMemIffEntries
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.Coefs

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, e⟩`. Establish `: c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X = u` using `Subtype.ext e`. Rewrite using `[this]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨_, h, rfl⟩`.
-/
theorem mem_gramNear_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (c : HermR R σ n) (U : Set (HermR R σ n)) (X : Fin n → Fin M → R ⊗[F] E) :
    X ∈ gramNear R σ J c U ↔ c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X ∈ U := by
  constructor
  · rintro ⟨u, hu, e⟩
    have : c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X = u := Subtype.ext e
    rwa [this]
  · intro h
    exact ⟨_, h, rfl⟩

/- English proof (translation)
Establish `h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n` using `(c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X).2`. Unfold `gramTest`. Conclude with `dif_pos h`.
-/
theorem gramTest_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (c : HermR R σ n) (ρ : HermR R σ n → ℝ) (X : Fin n → Fin M → R ⊗[F] E) :
    gramTest R σ J c ρ X = ρ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X) := by
  have h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n :=
    (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X).2
  unfold gramTest
  exact dif_pos h

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_sub, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_gramH]`.
-/
theorem hermMap_sub_gramH {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {n : ℕ} (c : HermR R σ n) (X : Fin n → Fin M → R ⊗[F] E) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap f σ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X) =
      GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap f σ c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R' (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  rw [GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_sub, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_gramH]

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_hermOf f σ T hT`.
-/
theorem hermMap_hermOf' {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap f σ (hermOf R σ T hT) = hermOf R' σ T hT :=
  GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_hermOf f σ T hT

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.SiegelND.Coef.hermV GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin`. Rewrite using `[hermMap_sub_gramH hCM hJ, hermMap_sub_gramH hCM hJ, hermMap_hermOf', hermMap_hermOf']`. Both sides reduce to the same expression.
-/
theorem hermV_sub_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (x : Fin n → Fin M → AF F ⊗[F] E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x)) =
      hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin x)) := by
  unfold GlobalTheory.CompanionTheory.SiegelND.Coef.hermV GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin
  rw [hermMap_sub_gramH hCM hJ, hermMap_sub_gramH hCM hJ, hermMap_hermOf', hermMap_hermOf']
  rfl

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf`. Rewrite using `[hermMap_sub_gramH hCM hJ, hermMap_hermOf']`. Both sides reduce to the same expression.
-/
theorem hermInf_sub_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (x : Fin n → Fin M → AF F ⊗[F] E) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) =
      hermOf (Ainf F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) := by
  unfold GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf
  rw [hermMap_sub_gramH hCM hJ, hermMap_hermOf']
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermV_entries {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} (B : HermR (AF F) σ n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (fun a i => (GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) =
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Establish `hh : HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ (latV (M` using `n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := h v hv`. Rewrite `hh` using `[← hermV_entries]`. Conclude with `(h3 v hv _).2 hh`.

Introduce `h v hv`. Establish `hh` using `(h3 v hv _).1 (h v hv)`. Rewrite `hh` using `[hermV_entries]`. Conclude with `hh`.
-/
theorem mem_intH_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (B : HermR (AF F) σ n)
    (h3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E))) :
    B ∈ intH σ b S ↔ GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S := by
  constructor
  · intro h v hv
    have hh : HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := h v hv
    rw [← hermV_entries] at hh
    exact (h3 v hv _).2 hh
  · intro h v hv
    have hh := (h3 v hv _).1 (h v hv)
    rw [hermV_entries] at hh
    exact hh

/- English proof (translation)
Establish `hiff` using `mem_intH_iff b S B h3`. Distinguish the cases in `h : B ∈ intH σ b S`. Conclude with `(Set.indicator_of_mem h (fun _ => (1 : ℂ))).trans (Set.indicator_of_mem (hiff.1 h) (fun _ => (1 : ℂ))).symm`. Conclude with `(Set.indicator_of_notMem h (fun _ => (1 : ℂ))).trans (Set.indicator_of_notMem (fun h' => h (hiff.2 h')) (fun _ => (1 : ℂ))).symm`.
-/
theorem indicator_intH {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (B : HermR (AF F) σ n)
    (h3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E))) :
    (intH σ b S).indicator (fun _ => (1 : ℂ)) B =
      (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) := by
  classical
  have hiff := mem_intH_iff b S B h3
  by_cases h : B ∈ intH σ b S
  · exact (Set.indicator_of_mem h (fun _ => (1 : ℂ))).trans (Set.indicator_of_mem (hiff.1 h) (fun _ => (1 : ℂ))).symm
  · exact (Set.indicator_of_notMem h (fun _ => (1 : ℂ))).trans (Set.indicator_of_notMem (fun h' => h (hiff.2 h')) (fun _ => (1 : ℂ))).symm

/- English proof (translation)
Take `⟨a1, a2, a3, a4, -⟩` from `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1`. Use `haveI := a1`. Use `haveI := a2`. Use `haveI := a3`. Use `haveI := a4`.

Take `⟨t1, -, -, -, -, -, -, hB, -, hG⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)`. Use `haveI := t1`. Use `haveI := hB n M`. Establish `e : gramTest (Ainf F) σ J c ρ = fun X => ρ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) X)`. Use function extensionality and compare the values at `(gramTest_eq hCM hJ (Ainf F) c ρ)`.

Rewrite using `[e]`. Establish `hc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) X` using `Continuous.subtype_mk (continuous_const.sub (hG n M J)) _`. Conclude with `(hρ.comp hc).measurable`.
-/
theorem measurable_gramTest {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {n : ℕ} (c : HermR (Ainf F) σ n) (ρ : HermR (Ainf F) σ n → ℝ) (hρ : Continuous ρ) :
    Measurable (gramTest (Ainf F) σ J c ρ) := by
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  haveI := a1; haveI := a2; haveI := a3; haveI := a4
  obtain ⟨t1, -, -, -, -, -, -, hB, -, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := t1
  haveI := hB n M
  have e : gramTest (Ainf F) σ J c ρ = fun X => ρ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) X) :=
    funext (gramTest_eq hCM hJ (Ainf F) c ρ)
  rw [e]
  have hc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) X :=
    Continuous.subtype_mk (continuous_const.sub (hG n M J)) _
  exact (hρ.comp hc).measurable

/- English proof (translation)
Take `⟨⟨a1, a2, a3⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Take `⟨t1, t2, t3, t4, -, -, -, -, hC, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)`. Use `haveI : IsTopologicalRing (AF F ⊗[F] E) := t1`. Use `haveI : LocallyCompactSpace (AF F ⊗[F] E) := t2`. Use `haveI : SecondCountableTopology (AF F ⊗[F] E) := t3`.

Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))`. Use `haveI : LocallyCompactSpace (HermR (AF F) σ n) := (hC n).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (HermR (AF F) σ n) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SigmaCompactSpace (HermR (AF F) σ n) := inferInstance`.

Use `haveI := h`. Use `haveI := Measure.IsAddHaarMeasure.sigmaFinite db`. Use `infer_instance`.
-/
theorem sfinite_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {n : ℕ} (db : Measure (HermR (AF F) σ n)) (h : db.IsAddHaarMeasure) : SFinite db := by
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨t1, t2, t3, t4, -, -, -, -, hC, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI : IsTopologicalRing (AF F ⊗[F] E) := t1
  haveI : LocallyCompactSpace (AF F ⊗[F] E) := t2
  haveI : SecondCountableTopology (AF F ⊗[F] E) := t3
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  haveI : LocallyCompactSpace (HermR (AF F) σ n) := (hC n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR (AF F) σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (HermR (AF F) σ n) := inferInstance
  haveI := h
  haveI := Measure.IsAddHaarMeasure.sigmaFinite db
  infer_instance

set_option maxHeartbeats 600000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n hn h2n ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT`. Take `⟨hEu, hlat⟩` from `GlobalTheory.T.siegel_weil_product_over_places F E σ hCM M J hJ n hn h2n ψ hψ dx hdx d b laminf lam hinf hlam`. Take `⟨S₀, hS₀⟩` from `GlobalTheory.T.euler_product_almost_all_standard F E M n d b dx 1 _ _ hEu`. Take `⟨S₁, hS₁⟩` from `GlobalTheory.T.hermitian_euler_product_standard F E σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam`. Establish `hq` using `GlobalTheory.T.lattice_gram_integral_almost_all F E σ hCM M J hJ n d b T hT`.

Establish `hlc` using `GlobalTheory.T.hermitian_lattice_mem_iff_entries F E σ hCM n d b`. Establish `hqf` using `Filter.eventually_cofinite.1 hq`. Establish `hlf` using `Filter.eventually_cofinite.1 hlc`. Use `⟨S₀ ∪ S₁ ∪ hqf.toFinset ∪ hlf.toFinset, fun S hS φ hφ A hA hAl => ?_⟩` and prove the remaining obligations. Establish `hS0 : S₀ ⊆ S` using `fun x hx => hS (by simp [hx])`.

Establish `hS1 : S₁ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS2 : ∀ v, v ∉ S → ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n`. Introduce `v hv`. Assume the negation of the conclusion as `hc`. Conclude with `hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr hc)))`.

Establish `hS3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔ (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M` using `n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by`. Introduce `v hv`. Assume the negation of the conclusion as `hc`. Conclude with `hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))`. Take `⟨ρ, U, hρ, hρs, hU, hUs, hUpos, hI, hc, hbd, hlim⟩` from `hS₁ S hS1`.

Establish `hΦSB : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A)` using `GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn h2n d b S φ A hφ hA hAl`. Establish `hΦdx : Integrable (pureN φ A) dx` using `GlobalTheory.T.schwartz_bruhat_integrable_any_haar F E σ hCM M n dx hdx.1 _ hΦSB`. Establish `hstar : Integrable (starN σ J ψ dx (pureN φ A)) db` using `GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB`. Establish `hsd` using `hdx.1`. Establish `hdb1` using `hdb.1`.

Use `haveI : SFinite dx := by infer_instance`. Use `haveI : SFinite db := sfinite_herm hCM db hdb1`. Use `set cI : HermR (Ainf F) σ n := hermOf (Ainf F) σ T hT with hcI`. Establish `hInf` using `GlobalTheory.T.archimedean_siegel_weil_measure F E σ hCM M J hJ n hn h2n d b laminf hinf minf hminf cI φ hφ`. Take `⟨hφm, -, hInf⟩` from `hInf`.

Establish `hInf` using `hInf ρ hρ hρs`. Establish `hV0` using `fun v => GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hCM M J hJ n hn h2n d b v (lam v) (hlam v) (m v) (hm v) (hermOf (Fv F v) σ T hT) (A v) (hA v).1 (hA v).2`. Establish `hV` using `fun v => (hV0 v).2.2 (fun k => U k v) (fun k => hU k v) (hUs v)`. Establish `hρpos : ∀ k, 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)` using `fun k => (hρ k).2.2.2`. Establish `hck : ∀ k, (∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) ≠ 0`.

Introduce `k`. Rewrite using `[hc k]`. Use `mul_ne_zero (by exact_mod_cast (hρpos k).ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)` and prove the remaining obligations. Conclude with `(hUpos k v).ne'` after adjusting the coercions. Establish `hfub` using `fun k => GlobalTheory.T.fubini_fourier_hermitian_integral F E σ M J hJ n hCM ψ hψ dx db inferInstance inferInstance _ hΦdx (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) (hI k).1 (hI k).2 T hT`.

Establish `hchi : Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T)` using `(hfub 0).1`. Establish `hφ'm : ∀ k, Measurable (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ))`. Introduce `k`. Conclude with `hφm.mul (Complex.measurable_ofReal.comp (measurable_gramTest hCM hJ cI (ρ k) (hρ k).1))`. Establish `key : ∀ k, ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) * (starN σ J ψ dx (pureN φ A) B * GlobalTheory.Companion …`.

Introduce `k`. Establish `hf` using `(hfub k).2`. Set `A' : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)` to `fun v => if v ∈ S then A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v) else A v`. Establish `hA'S : ∀ v ∈ S, A' v = A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v)` using `fun v hv => if_pos hv`. Establish `hA'n : ∀ v, v ∉ S → A' v = latV b v` using `fun v hv => (if_neg hv).trans (hAl v hv)`.

Establish `h3 : ∀ (x : Fin n → Fin M → AF F ⊗[F] E) v, GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x)) = hermOf (Fv F v) σ T hT - GlobalTheor …`. Introduce `x v`. Conclude with `hermV_sub_gram hCM hJ T hT x v`. Establish `h0 : ∀ x : Fin n → Fin M → AF F ⊗[F] E, GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) = cI - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus. …`. Introduce `x`.

Conclude with `hermInf_sub_gram hCM hJ T hT x`. Establish `hmem : ∀ x : Fin n → Fin M → AF F ⊗[F] E, (HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A ∧ GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∈ GlobalTheory.CompanionTheory.Siegel …`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, h'⟩ v`.

Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hA'S v hv]`. Use `⟨h v, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_gramNear_iff hCM hJ, ← h3 x v]`. Conclude with `h'.1 v hv`.

Rewrite using `[show A' v = A v from if_neg hv]`. Conclude with `h v`. Introduce `h`. Use `⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`.

Use `h v` as an intermediate fact. Rewrite `this` using `[hA'S v hv]`. Conclude with `this.1`. Use `h v` as an intermediate fact. Rewrite `this` using `[show A' v = A v from if_neg hv]`. Then use the resulting hypothesis.

Use `h v` as an intermediate fact. Rewrite `this` using `[hA'S v hv]`. Rewrite using `[h3 x v, ← mem_gramNear_iff hCM hJ]`. Conclude with `this.2`. Use `h v` as an intermediate fact.

Rewrite `this` using `[hA'n v hv]`. Rewrite using `[h3 x v]`. Conclude with `hS2 v hv _ this`. Establish `hpt : ∀ x, pureN φ A x * GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) = pureN (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) A' x`. Introduce `x`.

Establish `eR : pureN (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) A' x = (φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) * (ρ k (cI - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x)) : ℂ)) * (boxF A').indicator …` using `by show (φ _ * (gramTest (Ainf F) σ J cI (ρ k) _ : ℂ)) * _ = _`. Rewrite using `[gramTest_eq hCM hJ]`. Rewrite using `[eR]`. Unfold `pureN GlobalTheory.CompanionTheory.SiegelND.Coef.testH`. Rewrite using `[h0 x]`.

Distinguish the cases in `h : HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A'`. Take `⟨ha, hb⟩` from `(hmem x).2 h`. Rewrite using `[Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Set.indicator_of_notMem h, mul_zero]`.

Distinguish the cases in `ha : HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A`. Establish `hb : GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∉ GlobalTheory.CompanionTheory.SiegelND.Coef.boxH σ b n S (U k)` using `fun hb => h ((hmem x).1 ⟨ha, hb⟩)`. Rewrite using `[Set.indicator_of_notMem hb]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem ha]`.

Simplify using the standard rewrite rules. Establish `hmeasA' : ∀ v, MeasurableSet (A' v)`. Introduce `v`. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hA'S v hv]`.

Conclude with `((hV v).1 k).1`. Rewrite using `[show A' v = A v from if_neg hv]`. Conclude with `(hV0 v).1`. Establish `hfinA' : ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v) ≠ ⊤`. Introduce `v`.

Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hA'S v hv]`. Conclude with `((hV v).1 k).2`. Rewrite using `[hA'n v hv, hlat v]`. Conclude with `ENNReal.one_ne_top`.

Establish `he` using `(hS₀ S hS0 _ (hφ'm k) (hInf.1 k) A' hmeasA' hfinA' hA'n).2`. Establish `htail : (∏' v : {v // v ∉ S}, (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) b (lam v.1) n M (latV b v.1)).toReal) = 1`. Simplify using `[hlat]`. Rewrite `he` using `[htail]`. Establish `hprod : (∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v)).toReal : ℂ)) = ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v))).toReal : ℂ)` using `Finset.prod_congr rfl fun v hv => by rw [hA'S v hv]`.

Establish `e1 : ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) * (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory …`. Rewrite using `[← integral_div]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun bb => by simp only []; ring)`. Rewrite using `[e1, hf, integral_congr_ae (Filter.Eventually.of_forall hpt), he, hprod, hc k]`. Use `push_cast`.

Rewrite using `[Finset.prod_div_distrib]`. Simplify using `only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one]`. Rewrite using `[div_mul_div_comm]`. Establish `hint : ∀ B : HermR (AF F) σ n, (intH σ b S).indicator (fun _ => (1 : ℂ)) B = (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B)`. Introduce `B`.

Conclude with `indicator_intH b S B hS3`. Establish `lim1 : Filter.Tendsto (fun k => ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) * (starN σ J ψ dx (pureN φ A) B * G …`. Establish `hcs : coefS σ J ψ dx db (pureN φ A) T b S = ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) * (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T …`. Unfold `coefS`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun B => by`.

Simplify using `only [hint B]`. Use the proof step `rfl)`. Rewrite using `[hcs]`. Establish `hnorm : ∀ B, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B‖ = 1` using `fun B => hψ.2.1 _`. Use `tendsto_integral_of_dominated_convergence (fun B => ‖starN σ J ψ dx (pureN φ A) B‖) ?_ hstar.norm ?_ ?_` and prove the remaining obligations.

Introduce `k`. Conclude with `((hI k).1.div_const _).aestronglyMeasurable.mul (hstar.aestronglyMeasurable.mul hchi.aestronglyMeasurable)`. Introduce `k`. Use `Filter.Eventually.of_forall fun B => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, hnorm, mul_one, norm_div]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (norm_pos_iff.2 (hck k))).2 (hbd k B))`. Use `Filter.Eventually.of_forall fun B => ?_` and prove the remaining obligations. Conclude with `(hlim B).mul_const _`. Establish `lim2` using `hInf.2.mul (tendsto_finset_prod S fun v _ => (Complex.continuous_ofReal.tendsto _).comp (hV v).2)`. Conclude with `tendsto_nhds_unique lim1 (lim2.congr fun k => by simpa using (key k).symm)`.
-/
theorem coefS_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → ∀ A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E), (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → coefS σ J ψ dx db (pureN φ A) T b S = (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) * ∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn h2n ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT
  classical
  obtain ⟨hEu, hlat⟩ := GlobalTheory.T.siegel_weil_product_over_places F E σ hCM M J hJ n hn h2n ψ hψ dx hdx d b laminf lam hinf hlam
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.euler_product_almost_all_standard F E M n d b dx 1 _ _ hEu
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.hermitian_euler_product_standard F E σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam
  have hq := GlobalTheory.T.lattice_gram_integral_almost_all F E σ hCM M J hJ n d b T hT
  have hlc := GlobalTheory.T.hermitian_lattice_mem_iff_entries F E σ hCM n d b
  have hqf := Filter.eventually_cofinite.1 hq
  have hlf := Filter.eventually_cofinite.1 hlc
  refine ⟨S₀ ∪ S₁ ∪ hqf.toFinset ∪ hlf.toFinset, fun S hS φ hφ A hA hAl => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : ∀ v, v ∉ S → ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr hc)))
  have hS3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  obtain ⟨ρ, U, hρ, hρs, hU, hUs, hUpos, hI, hc, hbd, hlim⟩ := hS₁ S hS1
  have hΦSB : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) :=
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn h2n d b S φ A hφ hA hAl
  have hΦdx : Integrable (pureN φ A) dx := GlobalTheory.T.schwartz_bruhat_integrable_any_haar F E σ hCM M n dx hdx.1 _ hΦSB
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB
  have hsd := hdx.1
  have hdb1 := hdb.1
  haveI : SFinite dx := by infer_instance
  haveI : SFinite db := sfinite_herm hCM db hdb1
  set cI : HermR (Ainf F) σ n := hermOf (Ainf F) σ T hT with hcI
  have hInf := GlobalTheory.T.archimedean_siegel_weil_measure F E σ hCM M J hJ n hn h2n d b laminf hinf minf hminf cI φ hφ
  obtain ⟨hφm, -, hInf⟩ := hInf
  have hInf := hInf ρ hρ hρs
  have hV0 := fun v => GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hCM M J hJ n hn h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (A v) (hA v).1 (hA v).2
  have hV := fun v => (hV0 v).2.2 (fun k => U k v) (fun k => hU k v) (hUs v)
  have hρpos : ∀ k, 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) := fun k => (hρ k).2.2.2
  have hck : ∀ k, (∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) ≠ 0 := by
    intro k
    rw [hc k]
    refine mul_ne_zero (by exact_mod_cast (hρpos k).ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    exact_mod_cast (hUpos k v).ne'
  have hfub := fun k => GlobalTheory.T.fubini_fourier_hermitian_integral F E σ M J hJ n hCM ψ hψ dx db inferInstance inferInstance _ hΦdx
      (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) (hI k).1 (hI k).2 T hT
  have hchi : Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) := (hfub 0).1
  have hφ'm : ∀ k, Measurable (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) := by
    intro k
    exact hφm.mul (Complex.measurable_ofReal.comp (measurable_gramTest hCM hJ cI (ρ k) (hρ k).1))
  have key : ∀ k, ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db =
      ((∫ X, φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) /
          ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) *
        ∏ v ∈ S, (((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v))).toReal /
            (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℝ) : ℂ) := by
    intro k
    have hf := (hfub k).2
    let A' : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
      if v ∈ S then A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v) else A v
    have hA'S : ∀ v ∈ S, A' v = A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v) :=
      fun v hv => if_pos hv
    have hA'n : ∀ v, v ∉ S → A' v = latV b v := fun v hv => (if_neg hv).trans (hAl v hv)
    have h3 : ∀ (x : Fin n → Fin M → AF F ⊗[F] E) v,
        GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x)) =
          hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin x)) := by
      intro x v
      exact hermV_sub_gram hCM hJ T hT x v
    have h0 : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) =
          cI - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) := by
      intro x
      exact hermInf_sub_gram hCM hJ T hT x
    have hmem : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        (HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A ∧ GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxH σ b n S (U k)) ↔
          HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A' := by
      intro x
      constructor
      · rintro ⟨h, h'⟩ v
        by_cases hv : v ∈ S
        · rw [hA'S v hv]
          refine ⟨h v, ?_⟩
          rw [mem_gramNear_iff hCM hJ, ← h3 x v]
          exact h'.1 v hv
        · rw [show A' v = A v from if_neg hv]
          exact h v
      · intro h
        refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hv : v ∈ S
          · have := h v
            rw [hA'S v hv] at this
            exact this.1
          · have := h v
            rwa [show A' v = A v from if_neg hv] at this
        · have := h v
          rw [hA'S v hv] at this
          rw [h3 x v, ← mem_gramNear_iff hCM hJ]
          exact this.2
        · have := h v
          rw [hA'n v hv] at this
          rw [h3 x v]
          exact hS2 v hv _ this
    have hpt : ∀ x, pureN φ A x * GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) =
        pureN (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) A' x := by
      intro x
      have eR : pureN (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) A' x =
          (φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) * (ρ k (cI - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x)) : ℂ)) *
            (boxF A').indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin x) := by
        show (φ _ * (gramTest (Ainf F) σ J cI (ρ k) _ : ℂ)) * _ = _
        rw [gramTest_eq hCM hJ]
      rw [eR]
      unfold pureN GlobalTheory.CompanionTheory.SiegelND.Coef.testH
      rw [h0 x]
      by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A'
      · obtain ⟨ha, hb⟩ := (hmem x).2 h
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem h]
        ring
      · rw [Set.indicator_of_notMem h, mul_zero]
        by_cases ha : HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A
        · have hb : GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∉ GlobalTheory.CompanionTheory.SiegelND.Coef.boxH σ b n S (U k) :=
            fun hb => h ((hmem x).1 ⟨ha, hb⟩)
          rw [Set.indicator_of_notMem hb]
          simp
        · rw [Set.indicator_of_notMem ha]
          simp
    have hmeasA' : ∀ v, MeasurableSet (A' v) := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).1
      · rw [show A' v = A v from if_neg hv]; exact (hV0 v).1
    have hfinA' : ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v) ≠ ⊤ := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).2
      · rw [hA'n v hv, hlat v]; exact ENNReal.one_ne_top
    have he := (hS₀ S hS0 _ (hφ'm k) (hInf.1 k) A' hmeasA' hfinA' hA'n).2
    have htail : (∏' v : {v // v ∉ S}, (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) b (lam v.1) n M (latV b v.1)).toReal) = 1 := by
      simp [hlat]
    rw [htail] at he
    have hprod : (∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v)).toReal : ℂ)) =
        ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v))).toReal : ℂ) :=
      Finset.prod_congr rfl fun v hv => by rw [hA'S v hv]
    have e1 : ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db =
        (∫ B, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B *
          (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db) /
          ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall fun bb => by simp only []; ring)
    rw [e1, hf, integral_congr_ae (Filter.Eventually.of_forall hpt), he, hprod, hc k]
    push_cast
    rw [Finset.prod_div_distrib]
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one]
    rw [div_mul_div_comm]
  have hint : ∀ B : HermR (AF F) σ n, (intH σ b S).indicator (fun _ => (1 : ℂ)) B =
      (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) := by
    intro B
    exact indicator_intH b S B hS3
  have lim1 : Filter.Tendsto (fun k => ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B /
        ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db) Filter.atTop
      (nhds (coefS σ J ψ dx db (pureN φ A) T b S)) := by
    have hcs : coefS σ J ψ dx db (pureN φ A) T b S = ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db := by
      unfold coefS
      exact integral_congr_ae (Filter.Eventually.of_forall fun B => by
        simp only [hint B]
        rfl)
    rw [hcs]
    have hnorm : ∀ B, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B‖ = 1 := fun B => hψ.2.1 _
    refine tendsto_integral_of_dominated_convergence (fun B => ‖starN σ J ψ dx (pureN φ A) B‖) ?_ hstar.norm ?_ ?_
    · intro k
      exact ((hI k).1.div_const _).aestronglyMeasurable.mul (hstar.aestronglyMeasurable.mul hchi.aestronglyMeasurable)
    · intro k
      refine Filter.Eventually.of_forall fun B => ?_
      rw [norm_mul, norm_mul, hnorm, mul_one, norm_div]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((div_le_one (norm_pos_iff.2 (hck k))).2 (hbd k B))
    · refine Filter.Eventually.of_forall fun B => ?_
      exact (hlim B).mul_const _
  have lim2 := hInf.2.mul (tendsto_finset_prod S fun v _ =>
    (Complex.continuous_ofReal.tendsto _).comp (hV v).2)
  exact tendsto_nhds_unique lim1 (lim2.congr fun k => by simpa using (key k).symm)

end GlobalTheory.CompanionTheory.WhitFree.Coefs
