import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.ReductionH1Kernel

section Gen
variable {G : Type} [Group G] [TopologicalSpace G]
    {LL : Type} [Field LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V}

/- English proof (translation)
Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H w`. Establish `hw : b • w = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Use `show b • w.1 g = 0`. Take `⟨t, ht⟩` from `Submodule.Quotient.mk_surjective _ (w.1 g)`. Rewrite using `[← ht, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top`. Rewrite using `[← Submodule.Quotient.mk_smul, hw, Submodule.Quotient.mk_zero]`.
-/
theorem smul_H1Q_eq_zero (L : Lattice (O := O) ρ) (b : O)
    (hI : StableSub L (Ideal.span {b} • ⊤ : Submodule O ↥L.T)) (z : QuotientCohomology L _ hI) : b • z = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H w =>
    have hw : b • w = 0 := by
      apply Subtype.ext
      funext g
      show b • w.1 g = 0
      obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (w.1 g)
      rw [← ht, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, hw, Submodule.Quotient.mk_zero]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

/- English proof (translation)
Use `Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩` and prove the remaining obligations. Repeatedly rewrite using `[sub_eq_add_neg]`. Conclude with `(hρ x).add continuous_const`. Simplify using `only [map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem cob_mem_Z1T (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) :
    (fun g => ρ g x - x) ∈ latticeCocycles L := by
  refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩
  · simp_rw [sub_eq_add_neg]
    exact (hρ x).add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

/- English proof (translation)
Set `g0 : ↥(latticeCocycles L) →ₗ[O] ↥(quotientCocycles L _ hI)` to `(redT L _).codRestrict _ hZ`. Establish `hB : (latticeCoboundaries L).comap (latticeCocycles L).subtype ≤ ((BQ L _ hI).comap (quotientCocycles L _ hI).subtype).comap g0`. Introduce `d hd`. Rewrite `hd` using `[Submodule.mem_comap, Submodule.subtype_apply]`. Take `⟨x, hx, hxd⟩` from `hd`.

Rewrite using `[Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]`. Use `⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Use `show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) - Submodule.Quotient.mk ⟨x, hx⟩ = Submodule.Quotient.mk (evT L g d)`. Rewrite using `[show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk (actT L g ⟨x, hx⟩) from rfl, ← Submodule.Quotient.mk_sub]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ g x - x = (d : _ → V) g`. Rewrite using `[← hxd]`. Both sides reduce to the same expression.

Set `f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI` to `Submodule.mapQ _ _ g0 hB`. Use `⟨f, ?_, fun d => ⟨hZ d, rfl⟩⟩` and prove the remaining obligations. Establish `hkill` using `smul_H1Q_eq_zero L b hI`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`.

Take `⟨d, rfl⟩` from `Submodule.Quotient.mk_surjective ((latticeCoboundaries L).comap (latticeCocycles L).subtype) z`. Rewrite `hz` using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (g0 d) = (0 : QuotientCohomology L _ hI) at hz`. Rewrite `hz` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]`. Take `⟨y, hy⟩` from `hz`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective (Ideal.span {b} • ⊤ : Submodule O ↥L.T) y`. Establish `hg : ∀ g, ∃ t : ↥L.T, evT L g d - (actT L g x - x) = b • t`. Introduce `g`. Establish `h1` using `congrFun hy g`. Express the relevant statement in the definitionally equal form `actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x = Submodule.Quotient.mk (evT L g d) at h1`.

Rewrite `h1` using `[show actQ L _ hI g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L g x) from rfl, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]`. Rewrite using `[← GlobalTheory.RedLocConst.mem_span_smul_top', ← neg_sub]`. Conclude with `neg_mem h1`. Use `choose t ht using hg`. Set `cx : ↥(latticeCocycles L)` to `⟨_, cob_mem_Z1T L hρ x⟩`.

Establish `h2 : ∀ g, (d : _ → V) g - (ρ g x - x) = algebraMap O LL b • ((t g : ↥L.T) : V)`. Introduce `g`. Rewrite using `[algebraMap_smul]`. Conclude with `congrArg Subtype.val (ht g)`. Establish `hd'Z : (fun g => ((t g : ↥L.T) : V)) ∈ latticeCocycles L`.

Establish `hfun : (fun g => ((t g : ↥L.T) : V)) = (algebraMap O LL b)⁻¹ • ((d : _ → V) - (cx : _ → V))`. Use function extensionality and compare the values at `g`. Use `show _ = (algebraMap O LL b)⁻¹ • ((d : _ → V) g - (ρ g x - x))`. Rewrite using `[h2, inv_smul_smul₀ hb]`. Use `Submodule.mem_inf.2 ⟨?_, Submodule.mem_pi.2 fun g _ => (t g).2⟩` and prove the remaining obligations.

Rewrite using `[hfun]`. Conclude with `(continuousCocycles ρ).smul_mem _ ((continuousCocycles ρ).sub_mem (Submodule.mem_inf.1 d.2).1 (Submodule.mem_inf.1 cx.2).1)`. Establish `hdec : d = b • (⟨_, hd'Z⟩ : ↥(latticeCocycles L)) + cx`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Use `show (d : _ → V) g = b • ((t g : ↥L.T) : V) + (ρ g x - x)`. Rewrite using `[← algebraMap_smul LL b, ← h2, sub_add_cancel]`. Establish `hcx : (Submodule.Quotient.mk cx : LatticeCohomology L) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]`. Conclude with `⟨x, x.2, rfl⟩`.

Rewrite using `[hdec, Submodule.Quotient.mk_add, hcx, add_zero, Submodule.Quotient.mk_smul]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top`. Rewrite using `[Submodule.smul_le]`. Introduce `a ha z _`. Take `⟨a', rfl⟩` from `Ideal.mem_span_singleton'.1 ha`.

Rewrite using `[LinearMap.mem_ker, map_smul, mul_smul, hkill, smul_zero]`.
-/
theorem ker_red_gen (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (b : O)
    (hb : algebraMap O LL b ≠ 0) (hI : StableSub L (Ideal.span {b} • ⊤ : Submodule O ↥L.T))
    (hZ : ∀ d : ↥(latticeCocycles L), redT L _ d ∈ quotientCocycles L _ hI) :
    ∃ f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI, LinearMap.ker f = (Ideal.span {b} • ⊤ : Submodule O (LatticeCohomology L)) ∧
      ∀ d : ↥(latticeCocycles L), ∃ h : redT L _ d ∈ quotientCocycles L _ hI,
        f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT L _ d, h⟩ := by
  let g0 : ↥(latticeCocycles L) →ₗ[O] ↥(quotientCocycles L _ hI) := (redT L _).codRestrict _ hZ
  have hB : (latticeCoboundaries L).comap (latticeCocycles L).subtype ≤
      ((BQ L _ hI).comap (quotientCocycles L _ hI).subtype).comap g0 := by
    intro d hd
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hd
    obtain ⟨x, hx, hxd⟩ := hd
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    funext g
    show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) - Submodule.Quotient.mk ⟨x, hx⟩ =
      Submodule.Quotient.mk (evT L g d)
    rw [show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) =
      Submodule.Quotient.mk (actT L g ⟨x, hx⟩) from rfl, ← Submodule.Quotient.mk_sub]
    congr 1
    apply Subtype.ext
    show ρ g x - x = (d : _ → V) g
    rw [← hxd]; rfl
  let f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI := Submodule.mapQ _ _ g0 hB
  refine ⟨f, ?_, fun d => ⟨hZ d, rfl⟩⟩
  have hkill := smul_H1Q_eq_zero L b hI
  apply le_antisymm
  · intro z hz
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective ((latticeCoboundaries L).comap (latticeCocycles L).subtype) z
    rw [LinearMap.mem_ker] at hz
    change Submodule.Quotient.mk (g0 d) = (0 : QuotientCohomology L _ hI) at hz
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at hz
    obtain ⟨y, hy⟩ := hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {b} • ⊤ : Submodule O ↥L.T) y
    have hg : ∀ g, ∃ t : ↥L.T, evT L g d - (actT L g x - x) = b • t := by
      intro g
      have h1 := congrFun hy g
      change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x =
        Submodule.Quotient.mk (evT L g d) at h1
      rw [show actQ L _ hI g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L g x) from rfl,
        ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
      rw [← GlobalTheory.RedLocConst.mem_span_smul_top', ← neg_sub]
      exact neg_mem h1
    choose t ht using hg
    let cx : ↥(latticeCocycles L) := ⟨_, cob_mem_Z1T L hρ x⟩
    have h2 : ∀ g, (d : _ → V) g - (ρ g x - x) = algebraMap O LL b • ((t g : ↥L.T) : V) := by
      intro g
      rw [algebraMap_smul]
      exact congrArg Subtype.val (ht g)
    have hd'Z : (fun g => ((t g : ↥L.T) : V)) ∈ latticeCocycles L := by
      have hfun : (fun g => ((t g : ↥L.T) : V)) =
          (algebraMap O LL b)⁻¹ • ((d : _ → V) - (cx : _ → V)) := by
        funext g
        show _ = (algebraMap O LL b)⁻¹ • ((d : _ → V) g - (ρ g x - x))
        rw [h2, inv_smul_smul₀ hb]
      refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_pi.2 fun g _ => (t g).2⟩
      rw [hfun]
      exact (continuousCocycles ρ).smul_mem _ ((continuousCocycles ρ).sub_mem (Submodule.mem_inf.1 d.2).1 (Submodule.mem_inf.1 cx.2).1)
    have hdec : d = b • (⟨_, hd'Z⟩ : ↥(latticeCocycles L)) + cx := by
      apply Subtype.ext
      funext g
      show (d : _ → V) g = b • ((t g : ↥L.T) : V) + (ρ g x - x)
      rw [← algebraMap_smul LL b, ← h2, sub_add_cancel]
    have hcx : (Submodule.Quotient.mk cx : LatticeCohomology L) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, x.2, rfl⟩
    rw [hdec, Submodule.Quotient.mk_add, hcx, add_zero, Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top
  · rw [Submodule.smul_le]
    intro a ha z _
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [LinearMap.mem_ker, map_smul, mul_smul, hkill, smul_zero]

end Gen

/- English proof (translation)
Take `⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩` from `hO`. Use `haveI := hDom`. Use `haveI := hDVR`. Use `haveI := hFr`. Use `haveI := htr`.

Use `haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V`. Establish `hT : IsOpen (LA.T : Set A.V)` using `Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span`. Use `set c : LL := algebraMap O LL b with hcdef`. Establish `hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V))` using `(Homeomorph.smulOfNeZero c hb).isOpenMap _ hT`. Establish `hsm : ∀ v : A.V, c • v = b • v` using `fun v => by rw [hcdef, algebraMap_smul]`.

Establish `hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) ↔ (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)`. Introduce `x`. Rewrite using `[GlobalTheory.RedLocConst.mem_span_smul_top']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Use `⟨y, y.2, ?_⟩` and prove the remaining obligations. Use `show c • (y : A.V) = _`. Rewrite using `[hsm]`. Both sides reduce to the same expression. Introduce and unpack `⟨y, hy, hxy⟩`.

Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hxy]`. Use `show c • y = b • y`. Conclude with `hsm y`. Establish `ha : (a : _ → A.V) ∈ latticeCocycles LA` using `a.2`.

Take `⟨⟨hcont, hcoc⟩, -⟩` from `ha`. Establish `hval : ∀ g, ((redT LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) a) g) = Submodule.Quotient.mk (evT LA g a)` using `fun g => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g0`.

Use `⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)), hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩` and prove the remaining obligations. Use `show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)`. Rewrite using `[sub_self]`. Conclude with `⟨0, LA.T.zero_mem, smul_zero c⟩`. Introduce `g hg`.

Rewrite using `[hval, hval, Submodule.Quotient.eq, hmem]`. Conclude with `hg`. Introduce `g h`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) = Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))`. Rewrite using `[show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) = Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]`.

Establish `hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a)` using `Subtype.ext (hcoc g h)`. Rewrite using `[hx]`.
-/
theorem redT_mem_Z1Q_of_ne (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ)
    (b : O) (hb : algebraMap O LL b ≠ 0)
    (hI : StableSub LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)) :
    redT LA _ a ∈ quotientCocycles LA _ hI := by
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL b with hcdef
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hb).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = b • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [GlobalTheory.RedLocConst.mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = b • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) a) g) =
      Submodule.Quotient.mk (evT LA g a) := fun g => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g0
    refine ⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)),
      hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩
    · show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)
      rw [sub_self]; exact ⟨0, LA.T.zero_mem, smul_zero c⟩
    · intro g hg
      rw [hval, hval, Submodule.Quotient.eq, hmem]
      exact hg
  · intro g h
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

/- English proof (translation)
Introduce `l _ P K LL _ _ _ O _ _ hO A LA r hI`. Establish `hb : algebraMap O LL (((l : ℕ) : O) ^ r) ≠ 0`. Rewrite using `[map_pow, map_natCast]`. Use `pow_ne_zero _ ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap ℚ_[l] LL)]`.

Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Conclude with `ker_red_gen LA A.cont _ hb hI (redT_mem_Z1Q_of_ne l K LL O hO A LA _ hb hI)`.
-/
theorem ker_reduction_H1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), ∃ f : LatticeCohomology LA →ₗ[O] QuotientCohomology LA _ hI, LinearMap.ker f = (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA)) ∧ ∀ d : ↥(latticeCocycles LA), ∃ h : redT LA _ d ∈ quotientCocycles LA _ hI, f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT LA _ d, h⟩ := by
  intro l _ P K LL _ _ _ O _ _ hO A LA r hI
  have hb : algebraMap O LL (((l : ℕ) : O) ^ r) ≠ 0 := by
    rw [map_pow, map_natCast]
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact ker_red_gen LA A.cont _ hb hI (redT_mem_Z1Q_of_ne l K LL O hO A LA _ hb hI)

end GlobalTheory.ReductionH1Kernel
