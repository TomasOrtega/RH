import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.RedLocConst

/- English proof (translation)
Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨y, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, Submodule.mem_top, rfl⟩`.
-/
theorem mem_span_smul_top' {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

/- English proof (translation)
Introduce `l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI a`. Take `⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩` from `hO`. Use `haveI := hDom`. Use `haveI := hDVR`. Use `haveI := hFr`.

Use `haveI := htr`. Use `haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V`. Establish `hT : IsOpen (LA.T : Set A.V)` using `Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span`. Use `set c : LL := algebraMap O LL (ϖ ^ r) with hcdef`. Establish `hc : c ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (pow_ne_zero _ hϖ.ne_zero)`.

Establish `hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V))` using `(Homeomorph.smulOfNeZero c hc).isOpenMap _ hT`. Establish `hsm : ∀ v : A.V, c • v = ϖ ^ r • v` using `fun v => by rw [hcdef, algebraMap_smul]`. Establish `hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ↔ (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)`. Introduce `x`. Rewrite using `[mem_span_smul_top']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, y.2, ?_⟩` and prove the remaining obligations. Use `show c • (y : A.V) = _`. Rewrite using `[hsm]`.

Both sides reduce to the same expression. Introduce and unpack `⟨y, hy, hxy⟩`. Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hxy]`. Use `show c • y = ϖ ^ r • y`.

Conclude with `hsm y`. Establish `ha : (a : _ → A.V) ∈ latticeCocycles LA` using `a.2`. Take `⟨⟨hcont, hcoc⟩, -⟩` from `ha`. Establish `hval : ∀ g, ((redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) a) g) = Submodule.Quotient.mk (evT LA g a)` using `fun g => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g0`. Use `⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)), hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩` and prove the remaining obligations. Use `show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)`. Rewrite using `[sub_self]`.

Conclude with `⟨0, LA.T.zero_mem, smul_zero c⟩`. Introduce `g hg`. Rewrite using `[hval, hval, Submodule.Quotient.eq, hmem]`. Conclude with `hg`. Introduce `g h`.

Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) = Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))`. Rewrite using `[show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) = Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]`. Establish `hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a)` using `Subtype.ext (hcoc g h)`. Rewrite using `[hx]`.
-/
theorem redT_mem_Z1Q : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI a
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL (ϖ ^ r) with hcdef
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (pow_ne_zero _ hϖ.ne_zero)
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hc).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = ϖ ^ r • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = ϖ ^ r • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) a) g) =
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
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

end GlobalTheory.RedLocConst
