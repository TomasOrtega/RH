import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzVanishOffTranslates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatricesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubsetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameAtOfUnrAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelAndSchrodingerBoundedSupportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerFunctionInvariantTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerHyperplaneAveragesVanishStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShapeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeFixedThetaVectorSchrodingerIndicatorStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.SplitScalar

def trSet (O K : Type) [CommRing O] [Field K] [Algebra O K] (r t : ℕ) (ϖ : O) (g : GL (Fin r) K) :
    Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) :=
  {x | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) =
    (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)}

/- English proof (translation)
Take `⟨T, hT⟩` from `GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N`. Establish `huniq : ∀ g g' x, x ∈ trSet O K r t ϖ g → x ∈ trSet O K r t ϖ g' → trSet O K r t ϖ g = trSet O K r t ϖ g'`. Introduce and unpack `g g' x ⟨z, hz⟩ ⟨z', hz'⟩`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw⟩`. Conclude with `GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw`. Introduce and unpack `⟨w, hw⟩`. Conclude with `GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw`. Set `rep : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → GL (Fin r) K` to `fun A => if h : ∃ g, trSet O K r t ϖ g = A then h.choose else 1`.

Establish `hrep : ∀ g, trSet O K r t ϖ (rep (trSet O K r t ϖ g)) = trSet O K r t ϖ g` using `fun g => by`. Establish `h : ∃ g', trSet O K r t ϖ g' = trSet O K r t ϖ g` using `⟨g, rfl⟩`. Simplify using `only [rep, dif_pos h]`. Conclude with `h.choose_spec`. Set `gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K` to `fun y => if h : ∃ g, y ∈ trSet O K r t ϖ g then h.choose else 1`.

Use `⟨T.image fun y => rep (trSet O K r t ϖ (gs y)), fun k x hx => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hsupp k x hx`. Take `⟨y, hyT, z', rfl⟩` from `hT x z hz`. Establish `hy : Φ k y ≠ 0` using `by rwa [hinv] at hx`. Establish `hy' : y ∈ trSet O K r t ϖ (gs y)`.

Establish `h` using `hΩ k y hy`. Simplify using `only [gs, dif_pos h]`. Conclude with `h.choose_spec`. Take `⟨z₀, hz₀⟩` from `hy'`. Establish `hx' : y + (ϖ ^ N • z').map (algebraMap O K) ∈ trSet O K r t ϖ (gs y)` using `GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ k _ (by rwa [hinv])) z'`.

Use `⟨rep (trSet O K r t ϖ (gs y)), ⟨Finset.mem_image_of_mem _ hyT, by rwa [hrep]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hg, hxg⟩`. Take `⟨y', -, rfl⟩` from `Finset.mem_image.1 hg`. Rewrite `hxg` using `[hrep]`. Rewrite using `[huniq _ _ _ hxg hx']`.
-/
theorem exists_finset_trSet (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O)
    (hϖ : Irreducible ϖ) {ι : Type} (Φ : ι → Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) (N : ℕ)
    (hinv : ∀ k x (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), Φ k (x + (ϖ ^ N • z).map (algebraMap O K)) = Φ k x)
    (hsupp : ∀ k x, Φ k x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K))
    (hΩ : ∀ k x, Φ k x ≠ 0 → ∃ g, x ∈ trSet O K r t ϖ g) :
    ∃ F : Finset (GL (Fin r) K), ∀ k x, Φ k x ≠ 0 → ∃! g, g ∈ F ∧ x ∈ trSet O K r t ϖ g := by
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N
  have huniq : ∀ g g' x, x ∈ trSet O K r t ϖ g → x ∈ trSet O K r t ϖ g' → trSet O K r t ϖ g = trSet O K r t ϖ g' := by
    rintro g g' x ⟨z, hz⟩ ⟨z', hz'⟩
    ext y; constructor
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw
  let rep : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → GL (Fin r) K := fun A =>
    if h : ∃ g, trSet O K r t ϖ g = A then h.choose else 1
  have hrep : ∀ g, trSet O K r t ϖ (rep (trSet O K r t ϖ g)) = trSet O K r t ϖ g := fun g => by
    have h : ∃ g', trSet O K r t ϖ g' = trSet O K r t ϖ g := ⟨g, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K := fun y =>
    if h : ∃ g, y ∈ trSet O K r t ϖ g then h.choose else 1
  refine ⟨T.image fun y => rep (trSet O K r t ϖ (gs y)), fun k x hx => ?_⟩
  obtain ⟨z, hz⟩ := hsupp k x hx
  obtain ⟨y, hyT, z', rfl⟩ := hT x z hz
  have hy : Φ k y ≠ 0 := by rwa [hinv] at hx
  have hy' : y ∈ trSet O K r t ϖ (gs y) := by
    have h := hΩ k y hy
    simp only [gs, dif_pos h]
    exact h.choose_spec
  obtain ⟨z₀, hz₀⟩ := hy'
  have hx' : y + (ϖ ^ N • z').map (algebraMap O K) ∈ trSet O K r t ϖ (gs y) :=
    GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ k _ (by rwa [hinv])) z'
  refine ⟨rep (trSet O K r t ϖ (gs y)), ⟨Finset.mem_image_of_mem _ hyT, by rwa [hrep]⟩, ?_⟩
  rintro g ⟨hg, hxg⟩
  obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hg
  rw [hrep] at hxg
  rw [huniq _ _ _ hxg hx']

variable {D : D7}

/- English proof (translation)
Introduce `i j` and use `by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]; exact hg i j`.
-/
theorem suppAt_conj' {e : Formalism.L2.Theta.AE D} {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt (cA D e) V g := fun i j => by
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]; exact hg i j

/- English proof (translation)
Introduce `i j` and use `by rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]`.
-/
theorem suppAt_one' (e : Formalism.L2.Theta.AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V 1 := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

section Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

/- English proof (translation)
Establish `he'` using `isSplitIdem_conj he`. Take `⟨r, hr, H⟩` from `hW.om_split (cA D e) he' g h (suppAt_conj' hg) (suppAt_conj' hh) _ _ (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 S g) (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 T h)`. Use `⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (Circle.coe_ne_zero _), fun ℓ hℓ => H ℓ fun u hu => hℓ u ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[GlobalTheory.DualPairCheck.cA_cA]`. Conclude with `hu`.
-/
theorem exists_scalar (hW : IsWeilDatumO ψ S T χS χT om) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S}
    {h : GA D T} (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = s * ℓ f := by
  have he' := isSplitIdem_conj he
  obtain ⟨r, hr, H⟩ := hW.om_split (cA D e) he' g h (suppAt_conj' hg) (suppAt_conj' hh) _ _
    (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 S g) (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 T h)
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (Circle.coe_ne_zero _), fun ℓ hℓ => H ℓ fun u hu => hℓ u ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA] at hu
  exact hu

/- English proof (translation)
Take `⟨s, -, hs⟩` from `exists_scalar hW he hg hh`. Establish `he'` using `isSplitIdem_conj he`. Establish `hdual` using `(GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1`. Establish `hstc` using `@GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1`. Take `⟨ℓ₀, hℓ0, hℓ⟩` from `GlobalTheory.SplitHecke.exists_invariant_form' (ψ := ψ) he (fun y hy hn => exists_dual_half he hdual hstc hy hn) hne (hvac.2 e he) (hvac.2 _ he')`.

Establish `h1` using `hs ℓ₀ hℓ f₀ h0`. Rewrite `h1` using `[GlobalTheory.VecInv.om_latVac_split D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hL x y hx hy f₀ h0 hvac, map_smul, smul_eq_mul]`. Rewrite using `[mul_right_cancel₀ hℓ0 h1]`. Conclude with `hs`.
-/
theorem scalar_eq (hW : IsWeilDatumO ψ S T χS χT om) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f₀ : WO S T → ℂ} (h0 : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f₀)
    {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S}
    {h : GA D T} (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h)
    (hL : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    {x y : (Formalism.L2.Theta.AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) :
    ∀ ℓ, InvForm ψ S T e ℓ → ∀ f, IsThetaFunO ψ S T f →
      ℓ (om (g, h) f) = ((splitFacO χS χT x y : Circle) : ℂ) * ℓ f := by
  obtain ⟨s, -, hs⟩ := exists_scalar hW he hg hh
  have he' := isSplitIdem_conj he
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  obtain ⟨ℓ₀, hℓ0, hℓ⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (ψ := ψ) he
    (fun y hy hn => exists_dual_half he hdual hstc hy hn) hne (hvac.2 e he) (hvac.2 _ he')
  have h1 := hs ℓ₀ hℓ f₀ h0
  rw [GlobalTheory.VecInv.om_latVac_split D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hL x y hx hy f₀ h0 hvac, map_smul,
    smul_eq_mul] at h1
  rw [mul_right_cancel₀ hℓ0 h1]
  exact hs

end Gen

section Lev

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

/- English proof (translation)
Take `⟨-, -, h3, -⟩` from `GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j`. Establish `hs : IsIdemSum e {PP}` using `⟨⟨fun _ => e, fun P h => by rw [Finset.mem_singleton.1 h]; exact he, by simp⟩, he.1.2.1⟩`. Establish `e1` using `GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun P => (L.chi ((j : ℕ) + 1) P)⁻¹) (hL.mu0 j) hs (fun P h => ⟨(L.C.isMu0 j).tame P, by rw [Finset.mem_singleton.1 h]; exact hL.chi j PP hP⟩) x a a' u hx ha fun P _ => hu P`. Establish `e2` using `GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun _ => 1) (hL.xi t) hs (fun P h => ⟨hL.xi_tame t P, by rw [Finset.mem_singleton.1 h]; exact GlobalTheory.VecInv.isRes_one (h3 PP hP)⟩) x a a' u hx ha fun P _ => hu P`. Establish `e3` using `GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun _ => 1) hL.eta hs (fun P _ => ⟨GlobalTheory.VecInv.tameAt_of_unrAt (L.C.isEta.unr P), GlobalTheory.VecInv.isRes_one (L.C.isEta.unr P)⟩) x a a' u hx ha fun P _ => hu P`.

Use `⟨?_, Subtype.ext (e3.trans (Finset.prod_eq_one fun _ _ => rfl))⟩` and prove the remaining obligations. Establish `e0 : ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) = (L.mu0 ((j : ℕ) + 1) x : Circle) * (L.xi t x : Circle)` using `rfl`. Rewrite using `[e0, e1, e2, Finset.prod_singleton, Finset.prod_singleton]`. Simplify using the standard rewrite rules.
-/
theorem mu_val_one (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {PP : Pl D.host.E} (hP : PP ∈ L.Pg) {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (x : (Formalism.L2.Theta.AE D)ˣ) (a : Formalism.L2.Theta.AE D)
    (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ)
    (hx : (x : Formalism.L2.Theta.AE D) = e * a + (1 - e))
    (ha : (a' : Formalism.IndefR.Lev.EAf D) = toEAf D a) (hu : ∀ PP, (u PP : kP PP) = resS D.host.F PP a') :
    ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) = (((L.chi ((j : ℕ) + 1) PP (u PP))⁻¹ : ℂˣ) : ℂ) ∧ L.eta x = 1 := by
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j
  have hs : IsIdemSum e {PP} := ⟨⟨fun _ => e, fun P h => by rw [Finset.mem_singleton.1 h]; exact he, by simp⟩, he.1.2.1⟩
  have e1 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun P => (L.chi ((j : ℕ) + 1) P)⁻¹) (hL.mu0 j) hs
    (fun P h => ⟨(L.C.isMu0 j).tame P, by rw [Finset.mem_singleton.1 h]; exact hL.chi j PP hP⟩) x a a' u hx ha
    fun P _ => hu P
  have e2 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun _ => 1) (hL.xi t) hs
    (fun P h => ⟨hL.xi_tame t P, by rw [Finset.mem_singleton.1 h]; exact GlobalTheory.VecInv.isRes_one (h3 PP hP)⟩) x a a' u hx ha
    fun P _ => hu P
  have e3 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun _ => 1) hL.eta hs
    (fun P _ => ⟨GlobalTheory.VecInv.tameAt_of_unrAt (L.C.isEta.unr P), GlobalTheory.VecInv.isRes_one (L.C.isEta.unr P)⟩) x a a' u hx ha
    fun P _ => hu P
  refine ⟨?_, Subtype.ext (e3.trans (Finset.prod_eq_one fun _ _ => rfl))⟩
  have e0 : ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) = (L.mu0 ((j : ℕ) + 1) x : Circle) * (L.xi t x : Circle) := rfl
  rw [e0, e1, e2, Finset.prod_singleton, Finset.prod_singleton]
  simp

/- English proof (translation)
Take `⟨k, hk⟩` from `(hL.Pg PP).1 hP`. Break down `hP' with hP' | hP'` into its components or cases. Take `⟨k', hk'⟩` from `(hL.Pg PP').1 hP'`. Conclude with `GlobalTheory.ProjectedLift.not_isConjPl L.C.P hk hk'`. Introduce `hc`.

Take `⟨q, hq, hm, hne⟩` from `GlobalTheory.LevelRamif.exists_prime_mem (hL.Q_pl t) hP'`. Conclude with `GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))`.
-/
theorem not_conj (hL : L.Is μ0) (t : T0) {PP PP' : Pl D.host.E} (hP : PP ∈ L.Pg) (hP' : PP' ∈ L.Pg ∨ PP' ∈ L.Q t) :
    ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (hL.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl L.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (hL.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

end Lev

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

/- English proof (translation)
Introduce `h`. Take `⟨κ, hs, hκ⟩` from `GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq D (Vc D i) v φ e he (frCo φ (R.βV i)) (Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h)`. Take `⟨h1, h2, h3, h4⟩` from `GlobalTheory.T.splitPlaceUnitary_integralMatrix_keeps_lattice D (Vc D i) (R.βV i) (R.ΛV i) _ (hL.βV i).choose_spec PP v φ e hφ he red hred h κ hs hκ`. Use `⟨κ, hs, h1, h2, hκ, h3, fun PP' a b => h4 PP' b (not_conj hL t hP a), fun ℓ hℓ f hf => ?_⟩` and prove the remaining obligations. Establish `hvac` using `(hv i t).1`.

Establish `hne : R.vacP i ≠ 0`. Introduce `h0`. Take `⟨⟨p, hp⟩, hn⟩` from `hvac.2.norm`. Establish `n1` using `hn p hp`. Rewrite `n1` using `[h0]`.

Simplify using `[nrm2] at n1`. Establish `hAt` using `(((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1`. Rewrite using `[scalar_eq (hω i t) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) hvac.2.theta hne hvac.2.lat he.1 hs (suppAt_one' e _) (GlobalTheory.VecInv.mem_latO_iff (hL.βV i).choose_s …`. Take `⟨a, ha, hr⟩` from `GlobalTheory.VecInv.exists_det_int h2`. Take `⟨m, n⟩` from `mu_val_one hL t i hP hAt (GlobalTheory.VecInv.detAt e he.1.1 _ κ) _ a _ (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ κ) ha hr`.

Use `congr 1`. Rewrite using `[splitFacO, map_one, map_one, mul_one]`. Express the relevant statement in the definitionally equal form `((((R.toLevCh.mu t ((i : ℕ) + 1) * R.eta⁻¹) _)⁻¹ : Circle) : ℂ) = _`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, n, inv_one, mul_one, Circle.coe_inv, m, h3, Units.val_inv_eq_inv_val, inv_inv]`.
-/
theorem actAt (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (hv : R.thP_vP) (i : Fin D.R.m) (t : T)
    {PP : Pl D.host.E} (hP : PP ∈ R.Pg) {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (hφ : IsProjAt φ PP)
    (he : IsIdemOf φ e) (red : OI v →+* kP PP)
    (hred : ∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F,
        red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) : ActAt R i t PP φ e red := by
  intro h
  obtain ⟨κ, hs, hκ⟩ := GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq D (Vc D i) v φ e he (frCo φ (R.βV i))
    (Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h)
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.splitPlaceUnitary_integralMatrix_keeps_lattice D (Vc D i) (R.βV i) (R.ΛV i) _ (hL.βV i).choose_spec PP v φ e hφ he red hred h κ hs hκ
  refine ⟨κ, hs, h1, h2, hκ, h3, fun PP' a b => h4 PP' b (not_conj hL t hP a), fun ℓ hℓ f hf => ?_⟩
  have hvac := (hv i t).1
  have hne : R.vacP i ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn⟩ := hvac.2.norm
    have n1 := hn p hp
    rw [h0] at n1
    simp [nrm2] at n1
  have hAt := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  rw [scalar_eq (hω i t) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) hvac.2.theta hne hvac.2.lat
    he.1 hs (suppAt_one' e _) (GlobalTheory.VecInv.mem_latO_iff (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 h2
      (by rw [map_one]; exact Subgroup.one_mem _)) (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ κ)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ 1) ℓ hℓ f hf]
  obtain ⟨a, ha, hr⟩ := GlobalTheory.VecInv.exists_det_int h2
  obtain ⟨m, n⟩ := mu_val_one hL t i hP hAt (GlobalTheory.VecInv.detAt e he.1.1 _ κ) _ a _
    (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ κ) ha hr
  congr 1
  rw [splitFacO, map_one, map_one, mul_one]
  change ((((R.toLevCh.mu t ((i : ℕ) + 1) * R.eta⁻¹) _)⁻¹ : Circle) : ℂ) = _
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, n, inv_one, mul_one, Circle.coe_inv, m, h3, Units.val_inv_eq_inv_val,
    inv_inv]

section Fib

variable {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {e : Formalism.L2.Theta.AE D}

/- English proof (translation)
The claim follows from `theta_sum _ _ f hf fun y hy => theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he (hc y hy)) hf)`.
-/
theorem theta_comb (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {c : WO S T' →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y)
    {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) : IsThetaFunO ψ S T' (comb ψ S T' c f) :=
  theta_sum _ _ f hf fun y hy => theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he (hc y hy)) hf)

/- English proof (translation)
Rewrite using `[heisO_comm, map_smul, smul_eq_mul, hℓ y hy _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin (isSplitIdem_conj he) hx) hf)]`.
-/
theorem form_heis (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {ℓ : (WO S T' → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T' e ℓ)
    {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) {x y : WO S T'} (hx : IsHalf (cA D e) x) (hy : IsHalf e y) :
    ℓ (heisO ψ S T' x (heisO ψ S T' y f)) = ψ (symplO S T' x y) * ℓ (heisO ψ S T' x f) := by
  rw [heisO_comm, map_smul, smul_eq_mul,
    hℓ y hy _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin (isSplitIdem_conj he) hx) hf)]

/- English proof (translation)
Unfold `comb Finsupp.sum`. Rewrite using `[heisO_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[heisO_smul, map_smul, smul_eq_mul, form_heis hψ he hℓ hf hx (hc y hy), mul_assoc]`.
-/
theorem form_comb (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {ℓ : (WO S T' → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T' e ℓ)
    {c : WO S T' →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y)
    {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) {x : WO S T'} (hx : IsHalf (cA D e) x) :
    ℓ (heisO ψ S T' x (comb ψ S T' c f)) = (c.sum fun y z => z * ψ (symplO S T' x y)) * ℓ (heisO ψ S T' x f) := by
  unfold comb Finsupp.sum
  rw [heisO_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [heisO_smul, map_smul, smul_eq_mul, form_heis hψ he hℓ hf hx (hc y hy), mul_assoc]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `GlobalTheory.ThetaStalk.eq_zero_of_invariant_forms D ψ hψ S T' _ (isSplitIdem_conj he) _ (theta_sub hf hg) fun ℓ hℓ x hx => ?_` and prove the remaining obligations. Rewrite `hℓ` using `[GlobalTheory.DualPairCheck.cA_cA]`. Rewrite using `[← heisL_apply, map_sub, map_sub, heisL_apply, heisL_apply, h ℓ hℓ x hx, sub_self]`.
-/
theorem eq_of_forms (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f)
    (hg : IsThetaFunO ψ S T' g) (h : ∀ ℓ, InvForm ψ S T' e ℓ → ∀ x, IsHalf (cA D e) x →
      ℓ (heisO ψ S T' x f) = ℓ (heisO ψ S T' x g)) : f = g := by
  rw [← sub_eq_zero]
  refine GlobalTheory.ThetaStalk.eq_zero_of_invariant_forms D ψ hψ S T' _ (isSplitIdem_conj he) _ (theta_sub hf hg)
    fun ℓ hℓ x hx => ?_
  rw [GlobalTheory.DualPairCheck.cA_cA] at hℓ
  rw [← heisL_apply, map_sub, map_sub, heisL_apply, heisL_apply, h ℓ hℓ x hx, sub_self]

/- English proof (translation)
Establish `he'` using `isSplitIdem_conj he`. Use `⟨fun z hz => eq_of_forms hψ he (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' (hA z hz)) hf) hf fun ℓ hℓ x hx => ?_, fun y hy hAy => eq_of_forms hψ he (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he hy) hf) (theta_smul _ hf) fun ℓ hℓ x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← heisO_add_of_orth ψ S T' (half_orth he' hx (hA z hz)), h1 ℓ hℓ x hx z hz]`. Rewrite using `[form_heis hψ he hℓ hf hx hy, heisO_smul, map_smul, smul_eq_mul]`. Distinguish the cases in `h0 : ℓ (heisO ψ S T' x f) = 0`.

Rewrite using `[h0, mul_zero, mul_zero]`. Use `hAy _ (h2 ℓ hℓ x hx h0)` as an intermediate fact. Rewrite using `[show symplO S T' x y = symplO S T' (x - x₀) y + symplO S T' x₀ y by rw [symplO_sub_left, sub_add_cancel], AddChar.map_add_eq_mul, this, one_mul]`.
-/
theorem shape_of_forms (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {A : Set (WO S T')}
    (hA : ∀ z ∈ A, IsHalf (cA D e) z) {x₀ : WO S T'} {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f)
    (h1 : ∀ ℓ, InvForm ψ S T' e ℓ → ∀ x, IsHalf (cA D e) x → ∀ z ∈ A,
      ℓ (heisO ψ S T' (x + z) f) = ℓ (heisO ψ S T' x f))
    (h2 : ∀ ℓ, InvForm ψ S T' e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T' x f) ≠ 0 → x - x₀ ∈ A) :
    Shape ψ S T' e A x₀ f := by
  have he' := isSplitIdem_conj he
  refine ⟨fun z hz => eq_of_forms hψ he (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' (hA z hz)) hf) hf
    fun ℓ hℓ x hx => ?_, fun y hy hAy => eq_of_forms hψ he
      (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he hy) hf) (theta_smul _ hf) fun ℓ hℓ x hx => ?_⟩
  · rw [← heisO_add_of_orth ψ S T' (half_orth he' hx (hA z hz)), h1 ℓ hℓ x hx z hz]
  · rw [form_heis hψ he hℓ hf hx hy, heisO_smul, map_smul, smul_eq_mul]
    by_cases h0 : ℓ (heisO ψ S T' x f) = 0
    · rw [h0, mul_zero, mul_zero]
    · have := hAy _ (h2 ℓ hℓ x hx h0)
      rw [show symplO S T' x y = symplO S T' (x - x₀) y + symplO S T' x₀ y by rw [symplO_sub_left, sub_add_cancel],
        AddChar.map_add_eq_mul, this, one_mul]

/- English proof (translation)
Establish `he'` using `isSplitIdem_conj he`. Use `GlobalTheory.T.heisenbergRelations_extend_to_place_commonEigen D ψ S T' Sb v hv p f (fun u hu => ?_) h` and prove the remaining obligations. Establish `h1 : ∀ y : WO S T', IsHalf e y → IsHalf (idem D (.inl v)) y` using `fun y hy i j => by`. Rewrite using `[← hev, ← hy i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e), he.2.1, add_zero]`. Establish `h2 : ∀ y : WO S T', IsHalf (cA D e) y → IsHalf (idem D (.inl v)) y` using `fun y hy i j => by`.

Rewrite using `[← hev, ← hy i j, ← mul_assoc, add_mul, he'.1, he.2.1, zero_add]`. Establish `hu' : e • u + cA D e • u = u` using `by rw [← add_smul, hev]; exact (isHalf_iff _ _).1 hu`. Establish `ha` using `isHalf_smul he.1 u`. Establish `hb` using `isHalf_smul he'.1 u`. Distinguish the cases in `c1 : ∀ z ∈ A, ψ (symplO S T' z (e • u)) = 1`.

Distinguish the cases in `c2 : cA D e • u ∈ A`. Use `left`. Establish `hne : ψ (symplOH S T' (e • u) (cA D e • u)) ≠ 0` using `fun h0 => by`. Use `AddChar.map_add_eq_mul ψ (symplOH S T' (e • u) (cA D e • u)) (-symplOH S T' (e • u) (cA D e • u))` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul]`.

Conclude with `one_ne_zero this`. Establish `key : ∀ q, Shape ψ S T' e A x₀ q → heisO ψ S T' u q = ((ψ (symplOH S T' (e • u) (cA D e • u)))⁻¹ * ψ (symplO S T' x₀ (e • u))) • q` using `fun q hq => by`. Use `heisO_heisO ψ S T' (e • u) (cA D e • u) q` as an intermediate fact. Rewrite `this` using `[hu', hq.1 _ c2, hq.2 _ ha c1]`. Rewrite using `[mul_smul, this, smul_smul, inv_mul_cancel₀ hne, one_smul]`.

Conclude with `⟨_, key p hp, key f hf⟩`. Take `⟨y, hy, hy1, hy2⟩` from `hd _ hb c2`. Use `Or.inr ⟨y, h1 y hy, ⟨_, hp.2 y hy hy1, hf.2 y hy hy1⟩, psi_skew_ne ?_⟩` and prove the remaining obligations. Rewrite `hy2` using `[symplO_smul, GlobalTheory.DualPairCheck.cA_cA, (isHalf_iff _ _).1 hy]`. Then use the resulting hypothesis. Use `push Not at c1`.

Take `⟨z, hz, hz1⟩` from `c1`. Use `Or.inr ⟨z, h2 z (hA z hz), ⟨1, by rw [hp.1 z hz, one_smul], by rw [hf.1 z hz, one_smul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← (isHalf_iff _ _).1 (hA z hz), symplO_smul, GlobalTheory.DualPairCheck.cA_cA]` and apply the resulting hypothesis.
-/
theorem relOff_drop {v : FinPl D} (he : IsSplitIdem D e) (hev : e + cA D e = idem D (.inl v)) {A : Set (WO S T')}
    (hA : ∀ z ∈ A, IsHalf (cA D e) z)
    (hd : ∀ x, IsHalf (cA D e) x → x ∉ A → ∃ y, IsHalf e y ∧ (∀ z ∈ A, ψ (symplO S T' z y) = 1) ∧ ψ (symplO S T' x y) ≠ 1)
    {x₀ : WO S T'} {p f : WO S T' → ℂ} (hp : Shape ψ S T' e A x₀ p) (hf : Shape ψ S T' e A x₀ f)
    {Sb : Finset (FinPl D)} (hv : v ∈ Sb) (h : RelOff ψ S T' Sb p f) : RelOff ψ S T' (dropPl Sb v) p f := by
  have he' := isSplitIdem_conj he
  refine GlobalTheory.T.heisenbergRelations_extend_to_place_commonEigen D ψ S T' Sb v hv p f (fun u hu => ?_) h
  have h1 : ∀ y : WO S T', IsHalf e y → IsHalf (idem D (.inl v)) y := fun y hy i j => by
    rw [← hev, ← hy i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e), he.2.1, add_zero]
  have h2 : ∀ y : WO S T', IsHalf (cA D e) y → IsHalf (idem D (.inl v)) y := fun y hy i j => by
    rw [← hev, ← hy i j, ← mul_assoc, add_mul, he'.1, he.2.1, zero_add]
  have hu' : e • u + cA D e • u = u := by rw [← add_smul, hev]; exact (isHalf_iff _ _).1 hu
  have ha := isHalf_smul he.1 u
  have hb := isHalf_smul he'.1 u
  by_cases c1 : ∀ z ∈ A, ψ (symplO S T' z (e • u)) = 1
  · by_cases c2 : cA D e • u ∈ A
    · left
      have hne : ψ (symplOH S T' (e • u) (cA D e • u)) ≠ 0 := fun h0 => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T' (e • u) (cA D e • u)) (-symplOH S T' (e • u) (cA D e • u))
        rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
        exact one_ne_zero this
      have key : ∀ q, Shape ψ S T' e A x₀ q → heisO ψ S T' u q =
          ((ψ (symplOH S T' (e • u) (cA D e • u)))⁻¹ * ψ (symplO S T' x₀ (e • u))) • q := fun q hq => by
        have := heisO_heisO ψ S T' (e • u) (cA D e • u) q
        rw [hu', hq.1 _ c2, hq.2 _ ha c1] at this
        rw [mul_smul, this, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact ⟨_, key p hp, key f hf⟩
    · obtain ⟨y, hy, hy1, hy2⟩ := hd _ hb c2
      refine Or.inr ⟨y, h1 y hy, ⟨_, hp.2 y hy hy1, hf.2 y hy hy1⟩, psi_skew_ne ?_⟩
      rwa [symplO_smul, GlobalTheory.DualPairCheck.cA_cA, (isHalf_iff _ _).1 hy] at hy2
  · push Not at c1
    obtain ⟨z, hz, hz1⟩ := c1
    refine Or.inr ⟨z, h2 z (hA z hz), ⟨1, by rw [hp.1 z hz, one_smul], by rw [hf.1 z hz, one_smul]⟩, ?_⟩
    rwa [← (isHalf_iff _ _).1 (hA z hz), symplO_smul, GlobalTheory.DualPairCheck.cA_cA]

/- English proof (translation)
Introduce `i j` and use `by rw [← hev, ← hy i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e), he.2.1, add_zero]`.
-/
theorem half_idem {v : FinPl D} (he : IsSplitIdem D e) (hev : e + cA D e = idem D (.inl v)) {y : WO S T'}
    (hy : IsHalf e y) : IsHalf (idem D (.inl v)) y := fun i j => by
  rw [← hev, ← hy i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e), he.2.1, add_zero]

/- English proof (translation)
Establish `e1 : ((1, h⁻¹) : GA D S × GA D T') * (1, h) = 1` using `by rw [Prod.mk_mul_mk, mul_one, inv_mul_cancel]; rfl`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e1, map_one, Module.End.one_apply]`.
-/
theorem om_inv_om (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (h : GA D T') (f : WO S T' → ℂ) :
    om (1, h⁻¹) (om (1, h) f) = f := by
  have e1 : ((1, h⁻¹) : GA D S × GA D T') * (1, h) = 1 := by rw [Prod.mk_mul_mk, mul_one, inv_mul_cancel]; rfl
  rw [← Module.End.mul_apply, ← map_mul, e1, map_one, Module.End.one_apply]

end Fib

section Coord

variable {v : FinPl D} {ϖ : OI v}

/- English proof (translation)
Introduce `a b` and use `by obtain ⟨o, ho⟩ := hX a b obtain ⟨o', ho'⟩ := hZ a b exact ⟨o + o', by rw [Matrix.add_apply, ho, ho', mul_add, map_add]⟩`.
-/
theorem inPow_add {m n : Type} {N : ℕ} {X Z : Matrix m n (Fv D.host.F v)} (hX : InPow ϖ N X) (hZ : InPow ϖ N Z) :
    InPow ϖ N (X + Z) := fun a b => by
  obtain ⟨o, ho⟩ := hX a b
  obtain ⟨o', ho'⟩ := hZ a b
  exact ⟨o + o', by rw [Matrix.add_apply, ho, ho', mul_add, map_add]⟩

/- English proof (translation)
Introduce `a b` and use `by obtain ⟨o, ho⟩ := hX a b exact ⟨-o, by rw [Matrix.neg_apply, ho, mul_neg, map_neg]⟩`.
-/
theorem inPow_neg {m n : Type} {N : ℕ} {X : Matrix m n (Fv D.host.F v)} (hX : InPow ϖ N X) : InPow ϖ N (-X) := fun a b => by
  obtain ⟨o, ho⟩ := hX a b
  exact ⟨-o, by rw [Matrix.neg_apply, ho, mul_neg, map_neg]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i j => by simpa using h (a.symm i) (b.symm j), fun h i j => h (a i) (b j)⟩`.
-/
theorem inPow_submatrix {m n m' n' : Type} {N : ℕ} (X : Matrix m n (Fv D.host.F v)) (a : m' ≃ m) (b : n' ≃ n) :
    InPow ϖ N (X.submatrix a b) ↔ InPow ϖ N X :=
  ⟨fun h i j => by simpa using h (a.symm i) (b.symm j), fun h i j => h (a i) (b j)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h choose z hz using h`. Use `⟨Matrix.of z, Matrix.ext fun a b => ?_⟩` and prove the remaining obligations. Use `hz a b` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, sub_eq_iff_eq_add', pow_one]`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨z, rfl⟩ a b`. Conclude with `⟨z a b, by simp⟩`.
-/
theorem inPow_iff {r t : ℕ} (X : Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v))
    (E : Matrix (Fin r ⊕ Fin t) (Fin r) (OI v)) :
    InPow ϖ 1 (X - E.map (algebraMap (OI v) (Fv D.host.F v))) ↔
      ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) (OI v), X = (E + ϖ • z).map (algebraMap (OI v) (Fv D.host.F v)) := by
  constructor
  · intro h
    choose z hz using h
    refine ⟨Matrix.of z, Matrix.ext fun a b => ?_⟩
    have := hz a b
    rw [Matrix.sub_apply, sub_eq_iff_eq_add', pow_one] at this
    rw [this]
    simp
  · rintro ⟨z, rfl⟩ a b
    exact ⟨z a b, by simp⟩

def reGL {K : Type} [CommRing K] {r n : ℕ} (h : r = n) (g : GL (Fin r) K) : GL (Fin n) K :=
  ⟨g.val.submatrix (finCongr h).symm (finCongr h).symm, (g⁻¹).val.submatrix (finCongr h).symm (finCongr h).symm,
    by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩

variable (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (i : Fin D.R.m) {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D}
  (he : IsIdemOf φ e)
include hL he

/- English proof (translation)
The claim follows from `GlobalTheory.PlaceTensor.adjCo_isCoord D _ _ _ _ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) v φ e he _ _`.
-/
theorem coord : GlobalTheory.PlaceTensor.IsCoord (cA D e) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True)
      (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i))) ∧ ∀ g h x,
      adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (actO (Vc D i) (Wc D i) g⁻¹ h⁻¹ x) =
        ((grpCo φ (Vc D i) (frCo φ (R.βV i)) g)⁻¹).val * adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x *
          (grpCo φ (Wc D i) (frCo φ (R.βW i)) h).val :=
  GlobalTheory.PlaceTensor.adjCo_isCoord D _ _ _ _ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) v φ e he _ _

/- English proof (translation)
Unfold `coR co`. Rewrite using `[(coord R hL i he).1.1]`. Both sides reduce to the same expression.
-/
theorem coR_add (x y : WO (Vc D i) (Wc D i)) : coR R i φ (x + y) = coR R i φ x + coR R i φ y := by
  unfold coR co
  rw [(coord R hL i he).1.1]
  rfl

/- English proof (translation)
Rewrite using `[eq_sub_iff_add_eq, ← coR_add R hL i he, sub_add_cancel]`.
-/
theorem coR_sub (x y : WO (Vc D i) (Wc D i)) : coR R i φ (x - y) = coR R i φ x - coR R i φ y := by
  rw [eq_sub_iff_add_eq, ← coR_add R hL i he, sub_add_cancel]

/- English proof (translation)
Use `(coord R hL i he).1.2.1.injOn hx hy (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use `congrFun (congrFun h ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)` as an intermediate fact. Simplify `this` using `[coR, co]`.
-/
theorem coR_inj {x y : WO (Vc D i) (Wc D i)} (hx : IsHalf (cA D e) x) (hy : IsHalf (cA D e) y)
    (h : coR R i φ x = coR R i φ y) : x = y := by
  refine (coord R hL i he).1.2.1.injOn hx hy (Matrix.ext fun a b => ?_)
  have := congrFun (congrFun h ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)
  simpa [coR, co] using this

/- English proof (translation)
Establish `h : ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ∃ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x ∧ coR R i φ x = X` using `fun X => by`. Take `⟨x, hx, hX⟩` from `(coord R hL i he).1.2.1.surjOn (Set.mem_univ (X.submatrix (rowIx (rank_V i)).symm (finCongr (rank_weight_component_eq i)).symm))`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Unfold `coR co`. Rewrite using `[hX]`.

Use extensionality with `a b`. Simplify using the standard rewrite rules. Conclude with `⟨fun X => (h X).choose, fun X => (h X).choose_spec⟩`.
-/
theorem exists_section : ∃ σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i),
    ∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X := by
  have h : ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ∃ x : WO (Vc D i) (Wc D i),
      IsHalf (cA D e) x ∧ coR R i φ x = X := fun X => by
    obtain ⟨x, hx, hX⟩ := (coord R hL i he).1.2.1.surjOn
      (Set.mem_univ (X.submatrix (rowIx (rank_V i)).symm (finCongr (rank_weight_component_eq i)).symm))
    refine ⟨x, hx, ?_⟩
    unfold coR co
    rw [hX]
    ext a b
    simp
  exact ⟨fun X => (h X).choose, fun X => (h X).choose_spec⟩

/- English proof (translation)
Establish `h1` using `(coord R hL i he).2 1 h x`. Establish `h2 : grpCo φ (Vc D i) (frCo φ (R.βV i)) 1 = 1` using `by simp [grpCo]`. Rewrite `h1` using `[inv_one, h2, inv_one, Units.val_one, Matrix.one_mul, hh]`. Unfold `coR co`. Rewrite using `[h1, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr (rank_weight_component_eq i))]`.

Use `congr 1`.
-/
theorem coR_act {g : GL (Fin D.R.r) (Fv D.host.F v)} {h : GA D (Wc D i)}
    (hh : grpCo φ (Wc D i) (frCo φ (R.βW i)) h = reGL (rank_weight_component_eq i) g) (x : WO (Vc D i) (Wc D i)) :
    coR R i φ (actO (Vc D i) (Wc D i) 1 h⁻¹ x) = coR R i φ x * g.val := by
  have h1 := (coord R hL i he).2 1 h x
  have h2 : grpCo φ (Vc D i) (frCo φ (R.βV i)) 1 = 1 := by simp [grpCo]
  rw [inv_one, h2, inv_one, Units.val_one, Matrix.one_mul, hh] at h1
  unfold coR co
  rw [h1, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr (rank_weight_component_eq i))]
  congr 1

omit hL he in
/- English proof (translation)
The claim follows from `and_congr Iff.rfl (inPow_submatrix _ _ _).symm`.
-/
theorem mem_halfPow {N : ℕ} {z : WO (Vc D i) (Wc D i)} :
    z ∈ halfPow φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) e ϖ N ↔
      IsHalf (cA D e) z ∧ InPow ϖ N (coR R i φ z) :=
  and_congr Iff.rfl (inPow_submatrix _ _ _).symm

end Coord

set_option maxHeartbeats 400000 in
open Classical in

/- English proof (translation)
Establish `hW` using `hω i t`. Establish `hψ` using `hW.std`. Establish `he'` using `isSplitIdem_conj he.1`. Establish `sdV` using `GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)`. Establish `sdW` using `GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)`.

Establish `frV` using `(hL.βV i).choose_spec.1`. Establish `frW` using `(hL.βW i).choose_spec.1`. Establish `hf` using `hT.1`. Establish `thx : ∀ {x q}, IsHalf (cA D e) x → IsThetaFunO R.ψ (Vc D i) (Wc D i) q → IsThetaFunO R.ψ (Vc D i) (Wc D i) (heisO R.ψ (Vc D i) (Wc D i) x q)` using `fun hx hq => GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hq`. Take `⟨σ, hσ⟩` from `exists_section R hL i he`.

Take `⟨h, hh, hg⟩` from `GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq D (Wc D i) v φ e he (frCo φ (R.βW i)) (reGL (rank_weight_component_eq i) g)`. Establish `hh' : Formalism.L2.Theta.SuppAt e (Wc D i) h⁻¹` using `fun a b => by`. Use `congrFun (congrFun (off_smul_mt_inv hh) a) b` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this`. Rewrite using `[Matrix.sub_apply]`.

Take the linear combination `-this`. Take `⟨s, hs0, hs⟩` from `exists_scalar hW he.1 (suppAt_one' e (Vc D i)) hh'`. Use `set E : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (OI v) := Matrix.fromRows 1 0 with hE`. Use `set x₀ := σ (E.map (algebraMap (OI v) (Fv D.host.F v))) with hx₀`. Use `set A₁ := halfPow φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) e ϖ 1 with hA₁`.

Establish `hf'` using `hW.om_pres (1, h⁻¹) f hf`. Establish `hdual` using `GlobalTheory.T.exists_separating_character_conjugate_half_split D R.ψ hψ _ _ _ _ _ _ sdV sdW frV frW v φ e he ϖ hϖ 1`. Take `⟨N, -, hN⟩` from `GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support D R.ψ hψ _ _ _ _ _ _ sdV sdW frV frW v φ e he ϖ hϖ _ hf'`. Take `⟨c, hc, hcv⟩` from `GlobalTheory.T.finiteFourierExpansion_conjugateHalf_splitPlace D R.ψ hψ _ _ _ _ sdV sdW v φ e he (frCo φ (R.βV i)) (frCo φ (R.βW i)) ϖ hϖ 1 N hdual (fun X => if InPow ϖ 1 (X - adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀) then 1 else 0) (fun X Z hZ => if_congr …`. Use `inPow_add h (inPow_neg hZ)` as an intermediate fact.

Rewrite using `[add_sub_right_comm, add_neg_cancel_right] at this,` and apply the resulting hypothesis. Use `fun h => by rw [add_sub_right_comm]; exact inPow_add h hZ⟩ rfl rfl)`. Use `set F := comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h⁻¹) f) with hF`. Establish `hFt : IsThetaFunO R.ψ (Vc D i) (Wc D i) F` using `theta_comb hψ he.1 hc hf'`. Establish `hB : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ y, IsHalf (cA D e) y → ℓ (heisO R.ψ (Vc D i) (Wc D i) y F) = if y - x₀ ∈ A₁ then ℓ (heisO R.ψ (Vc D i) (Wc D i) y (R.ωP i t (1, h⁻¹) f)) else 0`.

Introduce `ℓ hℓ y hy`. Rewrite using `[hF, form_comb hψ he.1 hℓ hc hf' hy]`. Distinguish the cases in `h0 : ℓ (heisO R.ψ (Vc D i) (Wc D i) y (R.ωP i t (1, h⁻¹) f)) = 0`. Rewrite using `[h0, mul_zero, ite_self]`. Rewrite using `[← hcv y hy (hN ℓ hℓ y hy h0)]`.

Establish `e1 : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (y - x₀) = adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y - adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀`. Rewrite using `[eq_sub_iff_add_eq, ← (coord R hL i he).1.1, sub_add_cancel]`. Establish `e2 : y - x₀ ∈ A₁ ↔ InPow ϖ 1 (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y - adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀)`. Rewrite using `[← e1]`. Conclude with `⟨fun h => h.2, fun h => ⟨isHalf_sub hy (hσ _).1, h⟩⟩`.

Simplify using `only [e2]`. Use `split_ifs`. Rewrite using `[one_mul]`. Rewrite using `[zero_mul]`. Establish `hmove : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x, IsHalf (cA D e) x → ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) q → ℓ (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) 1 h⁻¹ x) (R.ωP i t (1, h⁻¹) q)) = s * ℓ (heisO R.ψ (Vc D i) (Wc D i) x q)` using `fun ℓ hℓ x hx q hq => by`.

Rewrite using `[← hW.om_heis 1 h⁻¹ x q hq, hs ℓ hℓ _ (thx hx hq)]`. Establish `hmem : ∀ x, IsHalf (cA D e) x → (actO (Vc D i) (Wc D i) 1 h⁻¹ x - x₀ ∈ A₁ ↔ coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g)` using `fun x hx => by`. Rewrite using `[hA₁, mem_halfPow, coR_sub R hL i he, coR_act R hL i he hg, hx₀, (hσ _).2, inPow_iff]`. Conclude with `and_iff_right (isHalf_sub (GlobalTheory.SplitHecke.isHalf_actO _ _ hx) (hσ _).1)`. Establish `hback : ∀ y, actO (Vc D i) (Wc D i) 1 h⁻¹ (actO (Vc D i) (Wc D i) 1 h y) = y` using `fun y => by`.

Use `GlobalTheory.SplitHecke.actO_inv_actO (1 : GA D (Vc D i)) h y` as an intermediate fact. Rewrite `this` using `[inv_one]`. Then use the resulting hypothesis. Establish `hsh : Shape R.ψ (Vc D i) (Wc D i) e A₁ x₀ F`. Use `shape_of_forms hψ he.1 (fun z hz => hz.1) hFt (fun ℓ hℓ y hy z hz => ?_) fun ℓ hℓ y hy h0 => ?_` and prove the remaining obligations. Establish `hyz` using `isHalf_add hy hz.1`.

Establish `e1 : y + z - x₀ ∈ A₁ ↔ y - x₀ ∈ A₁`. Establish `hz2` using `((mem_halfPow R i).1 hz).2`. Rewrite using `[hA₁, mem_halfPow, mem_halfPow, add_sub_right_comm, coR_add R hL i he]`. Use `⟨fun h => ⟨isHalf_sub hy (hσ _).1, ?_⟩, fun h => ⟨isHalf_add h.1 hz.1, inPow_add h.2 hz2⟩⟩` and prove the remaining obligations. Use `inPow_add h.2 (inPow_neg hz2)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[hB ℓ hℓ _ hyz, hB ℓ hℓ _ hy]`. Distinguish the cases in `c1 : y - x₀ ∈ A₁`. Establish `c2` using `e1.2 c1`. Rewrite using `[if_pos c1, if_pos c2]`.

Establish `a1` using `GlobalTheory.SplitHecke.isHalf_actO (1 : GA D (Vc D i)) h hy`. Establish `a2` using `GlobalTheory.SplitHecke.isHalf_actO (1 : GA D (Vc D i)) h hyz`. Rewrite `c1` using `[← hback y]`. Rewrite `c2` using `[← hback (y + z)]`. Rewrite using `[← hback (y + z), hmove ℓ hℓ _ a2 f hf]`.

Use `conv_rhs => rw [← hback y, hmove ℓ hℓ _ a1 f hf]`. Rewrite using `[hconst ℓ hℓ _ _ a2 a1 ((hmem _ a2).1 c2) ((hmem _ a1).1 c1)]`. Rewrite using `[if_neg c1, if_neg fun c2 => c1 (e1.1 c2)]`. Assume the negation of the conclusion as `hn`. Conclude with `h0 (by rw [hB ℓ hℓ y hy, if_neg hn])`.

Establish `hvp : Shape R.ψ (Vc D i) (Wc D i) e A₁ x₀ (R.vP i t)`. Use `GlobalTheory.T.typePrime_fixedThetaVector_schrodinger_indicator D R.ψ R.θ _ _ _ _ _ _ _ _ _ _ _ _ _ sdV sdW frV frW (hv i t) PP hP v φ e hφ he ϖ hϖ x₀ (hσ _).1 fun a b => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(rowIx (rank_V i)).surjective a`. Take `⟨b, rfl⟩` from `(finCongr (rank_weight_component_eq i)).surjective b`. Use `congrFun (congrFun (hσ (E.map (algebraMap (OI v) (Fv D.host.F v)))).2 a) b` as an intermediate fact.

Use `Eq.trans this ?_` and prove the remaining obligations. Break down `a with a | a` into its components or cases. Simplify using `[hE, rowIx, Matrix.one_apply, Fin.ext_iff]`. Establish `: D.R.r + a.val ≠ b.val` using `by have := b.2; omega`. Simplify using `[hE, rowIx, this]`.

Take `⟨b1, b2, b3⟩` from `GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape D G Pl0 T A Ks R hω i t Sb v hvS h⁻¹ (fun a b => by rw [← he.2.1]; exact hh' a b) c (fun y hy => half_idem he.1 he.2.1 (hc y hy)) f hT hC hO`. Establish `b4 : LikeOff R i t (dropPl Sb v) F` using `⟨hFt, relOff_drop he.1 he.2.1 (fun z hz => hz.1) (fun x hx hn => hdual x hx fun h => hn ⟨hx, h⟩) hvp hsh hvS b3.2⟩`. Use `⟨R.ωP i t (1, h) F, ⟨h, F, b1, b2, b4, rfl⟩, hW.om_pres _ _ hFt, fun ℓ hℓ x hx => ?_⟩` and prove the remaining obligations. Establish `e1` using `hmove ℓ hℓ x hx _ (hW.om_pres (1, h) _ hFt)`. Rewrite `e1` using `[om_inv_om, hB ℓ hℓ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ hx), hmove ℓ hℓ x hx f hf]`.

Simplify using `only [hmem x hx] at e1`. Apply `mul_left_cancel₀ hs0` to reduce the goal to its premises. Rewrite using `[← e1]`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[mul_zero]`.
-/
theorem piece (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (hv : R.thP_vP) (i : Fin D.R.m) (t : T)
    {PP : Pl D.host.E} (hP : PP ∈ R.Pg) {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (hφ : IsProjAt φ PP)
    (he : IsIdemOf φ e) {ϖ : OI v} (hϖ : Irreducible ϖ) {Sb : Finset (FinPl D)} (hvS : v ∈ Sb)
    {f : WO (Vc D i) (Wc D i) → ℂ} (hT : TypeIn R i t Sb f) (hC : CleanIn R i t Sb f) (hO : LikeOff R i t Sb f)
    (g : GL (Fin D.R.r) (Fv D.host.F v))
    (hconst : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x x', IsHalf (cA D e) x → IsHalf (cA D e) x' →
      coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g →
      coR R i φ x' ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g →
      ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) x' f)) :
    ∃ F ∈ StepGen R i t (dropPl Sb v), IsThetaFunO R.ψ (Vc D i) (Wc D i) F ∧
      ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x, IsHalf (cA D e) x →
        ℓ (heisO R.ψ (Vc D i) (Wc D i) x F) =
          if coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g then ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) else 0 := by
  have hW := hω i t
  have hψ := hW.std
  have he' := isSplitIdem_conj he.1
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  have frV := (hL.βV i).choose_spec.1
  have frW := (hL.βW i).choose_spec.1
  have hf := hT.1
  have thx : ∀ {x q}, IsHalf (cA D e) x → IsThetaFunO R.ψ (Vc D i) (Wc D i) q →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (heisO R.ψ (Vc D i) (Wc D i) x q) := fun hx hq =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hq
  obtain ⟨σ, hσ⟩ := exists_section R hL i he
  obtain ⟨h, hh, hg⟩ := GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq D (Wc D i) v φ e he (frCo φ (R.βW i)) (reGL (rank_weight_component_eq i) g)
  have hh' : Formalism.L2.Theta.SuppAt e (Wc D i) h⁻¹ := fun a b => by
    have := congrFun (congrFun (off_smul_mt_inv hh) a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.sub_apply]
    linear_combination -this
  obtain ⟨s, hs0, hs⟩ := exists_scalar hW he.1 (suppAt_one' e (Vc D i)) hh'
  set E : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (OI v) := Matrix.fromRows 1 0 with hE
  set x₀ := σ (E.map (algebraMap (OI v) (Fv D.host.F v))) with hx₀
  set A₁ := halfPow φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) e ϖ 1 with hA₁
  have hf' := hW.om_pres (1, h⁻¹) f hf
  have hdual := GlobalTheory.T.exists_separating_character_conjugate_half_split D R.ψ hψ _ _ _ _ _ _ sdV sdW frV frW v φ e he ϖ hϖ 1
  obtain ⟨N, -, hN⟩ := GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support D R.ψ hψ _ _ _ _ _ _ sdV sdW frV frW v φ e he ϖ hϖ _ hf'
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.finiteFourierExpansion_conjugateHalf_splitPlace D R.ψ hψ _ _ _ _ sdV sdW v φ e he (frCo φ (R.βV i)) (frCo φ (R.βW i)) ϖ hϖ 1 N hdual
    (fun X => if InPow ϖ 1 (X - adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀) then 1 else 0)
    (fun X Z hZ => if_congr ⟨fun h => by
        have := inPow_add h (inPow_neg hZ)
        rwa [add_sub_right_comm, add_neg_cancel_right] at this,
      fun h => by rw [add_sub_right_comm]; exact inPow_add h hZ⟩ rfl rfl)
  set F := comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h⁻¹) f) with hF
  have hFt : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := theta_comb hψ he.1 hc hf'
  have hB : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ y, IsHalf (cA D e) y →
      ℓ (heisO R.ψ (Vc D i) (Wc D i) y F) =
        if y - x₀ ∈ A₁ then ℓ (heisO R.ψ (Vc D i) (Wc D i) y (R.ωP i t (1, h⁻¹) f)) else 0 := by
    intro ℓ hℓ y hy
    rw [hF, form_comb hψ he.1 hℓ hc hf' hy]
    by_cases h0 : ℓ (heisO R.ψ (Vc D i) (Wc D i) y (R.ωP i t (1, h⁻¹) f)) = 0
    · rw [h0, mul_zero, ite_self]
    · rw [← hcv y hy (hN ℓ hℓ y hy h0)]
      have e1 : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (y - x₀) =
          adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y -
            adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀ := by
        rw [eq_sub_iff_add_eq, ← (coord R hL i he).1.1, sub_add_cancel]
      have e2 : y - x₀ ∈ A₁ ↔ InPow ϖ 1 (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y -
          adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀) := by
        rw [← e1]
        exact ⟨fun h => h.2, fun h => ⟨isHalf_sub hy (hσ _).1, h⟩⟩
      simp only [e2]
      split_ifs
      · rw [one_mul]
      · rw [zero_mul]
  have hmove : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x, IsHalf (cA D e) x → ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) q →
      ℓ (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) 1 h⁻¹ x) (R.ωP i t (1, h⁻¹) q)) =
        s * ℓ (heisO R.ψ (Vc D i) (Wc D i) x q) := fun ℓ hℓ x hx q hq => by
    rw [← hW.om_heis 1 h⁻¹ x q hq, hs ℓ hℓ _ (thx hx hq)]
  have hmem : ∀ x, IsHalf (cA D e) x → (actO (Vc D i) (Wc D i) 1 h⁻¹ x - x₀ ∈ A₁ ↔
      coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g) := fun x hx => by
    rw [hA₁, mem_halfPow, coR_sub R hL i he, coR_act R hL i he hg, hx₀, (hσ _).2, inPow_iff]
    exact and_iff_right (isHalf_sub (GlobalTheory.SplitHecke.isHalf_actO _ _ hx) (hσ _).1)
  have hback : ∀ y, actO (Vc D i) (Wc D i) 1 h⁻¹ (actO (Vc D i) (Wc D i) 1 h y) = y := fun y => by
    have := GlobalTheory.SplitHecke.actO_inv_actO (1 : GA D (Vc D i)) h y
    rwa [inv_one] at this
  have hsh : Shape R.ψ (Vc D i) (Wc D i) e A₁ x₀ F := by
    refine shape_of_forms hψ he.1 (fun z hz => hz.1) hFt (fun ℓ hℓ y hy z hz => ?_) fun ℓ hℓ y hy h0 => ?_
    · have hyz := isHalf_add hy hz.1
      have e1 : y + z - x₀ ∈ A₁ ↔ y - x₀ ∈ A₁ := by
        have hz2 := ((mem_halfPow R i).1 hz).2
        rw [hA₁, mem_halfPow, mem_halfPow, add_sub_right_comm, coR_add R hL i he]
        refine ⟨fun h => ⟨isHalf_sub hy (hσ _).1, ?_⟩, fun h => ⟨isHalf_add h.1 hz.1, inPow_add h.2 hz2⟩⟩
        have := inPow_add h.2 (inPow_neg hz2)
        rwa [add_neg_cancel_right] at this
      rw [hB ℓ hℓ _ hyz, hB ℓ hℓ _ hy]
      by_cases c1 : y - x₀ ∈ A₁
      · have c2 := e1.2 c1
        rw [if_pos c1, if_pos c2]
        have a1 := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D (Vc D i)) h hy
        have a2 := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D (Vc D i)) h hyz
        rw [← hback y] at c1
        rw [← hback (y + z)] at c2
        rw [← hback (y + z), hmove ℓ hℓ _ a2 f hf]
        conv_rhs => rw [← hback y, hmove ℓ hℓ _ a1 f hf]
        rw [hconst ℓ hℓ _ _ a2 a1 ((hmem _ a2).1 c2) ((hmem _ a1).1 c1)]
      · rw [if_neg c1, if_neg fun c2 => c1 (e1.1 c2)]
    · by_contra hn
      exact h0 (by rw [hB ℓ hℓ y hy, if_neg hn])
  have hvp : Shape R.ψ (Vc D i) (Wc D i) e A₁ x₀ (R.vP i t) := by
    refine GlobalTheory.T.typePrime_fixedThetaVector_schrodinger_indicator D R.ψ R.θ _ _ _ _ _ _ _ _ _ _ _ _ _ sdV sdW frV frW (hv i t) PP hP v φ e hφ he ϖ hϖ x₀ (hσ _).1
      fun a b => ?_
    obtain ⟨a, rfl⟩ := (rowIx (rank_V i)).surjective a
    obtain ⟨b, rfl⟩ := (finCongr (rank_weight_component_eq i)).surjective b
    have := congrFun (congrFun (hσ (E.map (algebraMap (OI v) (Fv D.host.F v)))).2 a) b
    refine Eq.trans this ?_
    rcases a with a | a
    · simp [hE, rowIx, Matrix.one_apply, Fin.ext_iff]
    · have : D.R.r + a.val ≠ b.val := by have := b.2; omega
      simp [hE, rowIx, this]
  obtain ⟨b1, b2, b3⟩ := GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape D G Pl0 T A Ks R hω i t Sb v hvS h⁻¹ (fun a b => by rw [← he.2.1]; exact hh' a b) c
    (fun y hy => half_idem he.1 he.2.1 (hc y hy)) f hT hC hO
  have b4 : LikeOff R i t (dropPl Sb v) F :=
    ⟨hFt, relOff_drop he.1 he.2.1 (fun z hz => hz.1) (fun x hx hn => hdual x hx fun h => hn ⟨hx, h⟩) hvp hsh hvS b3.2⟩
  refine ⟨R.ωP i t (1, h) F, ⟨h, F, b1, b2, b4, rfl⟩, hW.om_pres _ _ hFt, fun ℓ hℓ x hx => ?_⟩
  have e1 := hmove ℓ hℓ x hx _ (hW.om_pres (1, h) _ hFt)
  rw [om_inv_om, hB ℓ hℓ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ hx), hmove ℓ hℓ x hx f hf] at e1
  simp only [hmem x hx] at e1
  apply mul_left_cancel₀ hs0
  rw [← e1]
  split_ifs
  · rfl
  · rw [mul_zero]

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t Sb v hvS ⟨PP, hP, hO⟩ f hT hC hLk`. Establish `hL` using `hG.core.lev`. Establish `hω` using `hG.core.thP.ωP`. Establish `hv` using `hG.core.thP.vP`. Establish `hW` using `hω i t`.

Establish `hψ` using `hW.std`. Establish `hf` using `hT.1`. Take `⟨-, e₀, ⟨⟨es, hes, -⟩, -⟩, -⟩` from `hv i t`. Take `⟨v', φ, he, hφ⟩` from `(GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ PP (hes PP (Finset.mem_union_left _ hP))`. Take `rfl : v' = v` from `HeightOneSpectrum.ext ((((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ PP hφ).1).symm.trans hO)`.

Use `set e := es PP`. Establish `he'` using `isSplitIdem_conj he.1`. Take `⟨⟨red, hsurj, hker, -, hred⟩, -⟩` from `GlobalTheory.PlaceRed.red_dict D v' φ PP hφ`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (OI v')`. Establish `: Finite (IsLocalRing.ResidueField (OI v'))` using `Formalism.UG.P.glint_finite_residueField v'`.

Establish `hact` using `actAt R hL hω hv i t hP hφ he red hred`. Take `⟨σ, hσ⟩` from `exists_section R hL i he`. Establish `hσx : ∀ x, IsHalf (cA D e) x → σ (coR R i φ x) = x` using `fun x hx => coR_inj R hL i he (hσ _).1 hx (hσ _).2`. Take `⟨N, hN1, hN2⟩` from `GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support D R.ψ hψ _ _ _ _ _ _ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choo …`. Set `Φ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} → Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v') → ℂ` to `fun ℓ X => ℓ.1 (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)`.

Establish `h2` using `fun ℓ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} => GlobalTheory.T.schrodingerFunction_invariant_typePrime D G Pl0 T A Ks R hL hω i t PP hP v' φ e hφ he red hsurj hker hact Sb hvS σ hσ ℓ.1 ℓ.2 f hT ϖ hϖ`. Establish `h3` using `fun ℓ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} => GlobalTheory.T.schrodinger_hyperplane_averages_vanish D G Pl0 T A Ks R hL hω i t PP hP v' φ e hφ he red hsurj hker hact Sb hvS σ hσ ℓ.1 ℓ.2 f hf hC`. Establish `hsupp : ∀ k X, Φ k X ≠ 0 → ∃ z : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (OI v'), algebraMap (OI v') (Fv D.host.F v') (ϖ ^ N) • X = z.map (algebraMap (OI v') (Fv D.host.F v'))` using `fun k X hX => by choose o ho using hN2 k.1 k.2 _ (hσ X).1 hX`. Use `⟨Matrix.of fun a b => o (rowIx (rank_V i) a) (finCongr (rank_weight_component_eq i) b), Matrix.ext fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, ← ho, ← (hσ X).2, hσx _ (hσ X).1]`.

Both sides reduce to the same expression. Take `⟨Fs, hFs⟩` from `exists_finset_trSet (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ Φ N (fun k X z => by`. Establish `e1 : σ (X + (ϖ ^ N • z).map (algebraMap (OI v') (Fv D.host.F v'))) = σ X + σ ((ϖ ^ N • z).map (algebraMap (OI v') (Fv D.host.F v')))` using `coR_inj R hL i he (hσ _).1 (isHalf_add (hσ _).1 (hσ _).1) (by rw [coR_add R hL i he, (hσ _).2, (hσ _).2, (hσ _).2])`. Simplify using `only [Φ]`. Rewrite using `[e1, heisO_add_of_orth _ _ _ (half_orth he' (hσ _).1 (hσ _).1), hN1 _ ((mem_halfPow R i).2 ⟨(hσ _).1, by rw [(hσ _).2]; exact fun a b => ⟨z a b, rfl⟩⟩)]) hsupp`.

Use `fun k => GlobalTheory.parahoric_schwartz_vanish_off_translates (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ k) N (hsupp k) (h2 k) (h3 k)`. Use `choose P hP1 hP2 hP3 using fun g => piece R hL hω hv i t hP hφ he hϖ hvS hT hC hLk g fun ℓ hℓ x x' hx hx' ⟨z, hz⟩ ⟨z', hz'⟩ => by`. Establish `a1` using `GlobalTheory.T.congruenceInvariant_const_on_frame_translate (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ ⟨ℓ, hℓ⟩) (h2 ⟨ℓ, hℓ⟩) _ g z hz`. Establish `a2` using `GlobalTheory.T.congruenceInvariant_const_on_frame_translate (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ ⟨ℓ, hℓ⟩) (h2 ⟨ℓ, hℓ⟩) _ g z' hz'`. Establish `a3` using `a1.trans a2.symm`.

Simplify using `only [Φ] at a3`. Rewrite `a3` using `[hσx x hx, hσx x' hx']`. Then use the resulting hypothesis. Establish `hsum : f = ∑ g ∈ Fs, P g`. Use `eq_of_forms hψ he.1 hf (theta_sum _ _ f hf fun g _ => hP2 g) fun ℓ hℓ x hx => ?_` and prove the remaining obligations. Rewrite using `[heisO_sum, map_sum, Finset.sum_congr rfl fun g _ => hP3 g ℓ hℓ x hx]`.

Distinguish the cases in `h0 : ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) = 0`. Simplify using `[h0]`. Take `⟨g, ⟨hg, hxg⟩, hu⟩` from `hFs ⟨ℓ, hℓ⟩ (coR R i φ x) (by simp only [Φ]; rwa [hσx x hx])`. Rewrite using `[Finset.sum_eq_single_of_mem g hg fun g' hg' hne => if_neg fun h => hne (hu g' ⟨hg', h⟩), if_pos hxg]`. Rewrite using `[hsum]`.

Conclude with `Submodule.sum_mem _ fun g _ => Submodule.subset_span (hP1 g)`.
-/
theorem gen_at_type_prime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∃ PP ∈ R.Pg, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t Sb v hvS ⟨PP, hP, hO⟩ f hT hC hLk
  classical
  have hL := hG.core.lev
  have hω := hG.core.thP.ωP
  have hv := hG.core.thP.vP
  have hW := hω i t
  have hψ := hW.std
  have hf := hT.1
  obtain ⟨-, e₀, ⟨⟨es, hes, -⟩, -⟩, -⟩ := hv i t
  obtain ⟨v', φ, he, hφ⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ PP (hes PP (Finset.mem_union_left _ hP))
  obtain rfl : v' = v :=
    HeightOneSpectrum.ext ((((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ PP hφ).1).symm.trans hO)
  set e := es PP
  have he' := isSplitIdem_conj he.1
  obtain ⟨⟨red, hsurj, hker, -, hred⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v' φ PP hφ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OI v')
  have : Finite (IsLocalRing.ResidueField (OI v')) := Formalism.UG.P.glint_finite_residueField v'
  have hact := actAt R hL hω hv i t hP hφ he red hred
  obtain ⟨σ, hσ⟩ := exists_section R hL i he
  have hσx : ∀ x, IsHalf (cA D e) x → σ (coR R i φ x) = x := fun x hx => coR_inj R hL i he (hσ _).1 hx (hσ _).2
  obtain ⟨N, hN1, hN2⟩ := GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support D R.ψ hψ _ _ _ _ _ _ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 v' φ e he ϖ hϖ f hf
  let Φ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} → Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v') → ℂ :=
    fun ℓ X => ℓ.1 (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)
  have h2 := fun ℓ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} =>
    GlobalTheory.T.schrodingerFunction_invariant_typePrime D G Pl0 T A Ks R hL hω i t PP hP v' φ e hφ he red hsurj hker hact Sb hvS σ hσ ℓ.1 ℓ.2 f hT ϖ hϖ
  have h3 := fun ℓ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} =>
    GlobalTheory.T.schrodinger_hyperplane_averages_vanish D G Pl0 T A Ks R hL hω i t PP hP v' φ e hφ he red hsurj hker hact Sb hvS σ hσ ℓ.1 ℓ.2 f hf hC
  have hsupp : ∀ k X, Φ k X ≠ 0 → ∃ z : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (OI v'),
      algebraMap (OI v') (Fv D.host.F v') (ϖ ^ N) • X = z.map (algebraMap (OI v') (Fv D.host.F v')) := fun k X hX => by
    choose o ho using hN2 k.1 k.2 _ (hσ X).1 hX
    refine ⟨Matrix.of fun a b => o (rowIx (rank_V i) a) (finCongr (rank_weight_component_eq i) b), Matrix.ext fun a b => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, ← ho, ← (hσ X).2, hσx _ (hσ X).1]
    rfl
  obtain ⟨Fs, hFs⟩ := exists_finset_trSet (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ Φ N (fun k X z => by
      have e1 : σ (X + (ϖ ^ N • z).map (algebraMap (OI v') (Fv D.host.F v'))) =
          σ X + σ ((ϖ ^ N • z).map (algebraMap (OI v') (Fv D.host.F v'))) :=
        coR_inj R hL i he (hσ _).1 (isHalf_add (hσ _).1 (hσ _).1) (by rw [coR_add R hL i he, (hσ _).2, (hσ _).2, (hσ _).2])
      simp only [Φ]
      rw [e1, heisO_add_of_orth _ _ _ (half_orth he' (hσ _).1 (hσ _).1),
        hN1 _ ((mem_halfPow R i).2 ⟨(hσ _).1, by rw [(hσ _).2]; exact fun a b => ⟨z a b, rfl⟩⟩)]) hsupp
    fun k => GlobalTheory.parahoric_schwartz_vanish_off_translates (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ k) N (hsupp k)
      (h2 k) (h3 k)
  choose P hP1 hP2 hP3 using fun g => piece R hL hω hv i t hP hφ he hϖ hvS hT hC hLk g fun ℓ hℓ x x' hx hx' ⟨z, hz⟩ ⟨z', hz'⟩ => by
    have a1 := GlobalTheory.T.congruenceInvariant_const_on_frame_translate (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ ⟨ℓ, hℓ⟩) (h2 ⟨ℓ, hℓ⟩) _ g z hz
    have a2 := GlobalTheory.T.congruenceInvariant_const_on_frame_translate (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ ⟨ℓ, hℓ⟩) (h2 ⟨ℓ, hℓ⟩) _ g z' hz'
    have a3 := a1.trans a2.symm
    simp only [Φ] at a3
    rwa [hσx x hx, hσx x' hx'] at a3
  have hsum : f = ∑ g ∈ Fs, P g := by
    refine eq_of_forms hψ he.1 hf (theta_sum _ _ f hf fun g _ => hP2 g) fun ℓ hℓ x hx => ?_
    rw [heisO_sum, map_sum, Finset.sum_congr rfl fun g _ => hP3 g ℓ hℓ x hx]
    by_cases h0 : ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) = 0
    · simp [h0]
    · obtain ⟨g, ⟨hg, hxg⟩, hu⟩ := hFs ⟨ℓ, hℓ⟩ (coR R i φ x) (by simp only [Φ]; rwa [hσx x hx])
      rw [Finset.sum_eq_single_of_mem g hg fun g' hg' hne => if_neg fun h => hne (hu g' ⟨hg', h⟩), if_pos hxg]
  rw [hsum]
  exact Submodule.sum_mem _ fun g _ => Submodule.subset_span (hP1 g)

end GlobalTheory.DownLift.GenSplit

end
