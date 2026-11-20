import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult.OneLevel

variable {D : D7}

def levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GA D V) :=
  levelOpen D.sp.cm.sig V.gram (frameLat V) ⊓
    (⨅ v : T.S, (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)).comap (proj D.sp.cm.sig V.gram v.1)) ⊓
    U.frame.iwahori.comap (proj D.sp.cm.sig V.gram U.u)

def level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GfC V) := (levelAd T U).subgroupOf (GfC V)

/- English proof (translation)
Simplify using `[levelAd, mem_levelOpen, Subgroup.mem_iInf, and_assoc]`.
-/
theorem mem_levelAd {V : HSp D} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {g : GA D V} :
    g ∈ levelAd T U ↔ (∀ v, proj D.sp.cm.sig V.gram v g ∈ Kv V v) ∧
      (∀ v : T.S, proj D.sp.cm.sig V.gram v.1 g ∈ stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)) ∧
      proj D.sp.cm.sig V.gram U.u g ∈ U.frame.iwahori := by
  simp [levelAd, mem_levelOpen, Subgroup.mem_iInf, and_assoc]

/- English proof (translation)
Simplify using `only [levelAd, Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_comap]`. Use `((isOpen_levelOpen _ _ _).inter (isOpen_iInter_of_finite fun v => ?_)).inter (U.frame.isOpen_iwahori.preimage (continuous_proj _ _ _))` and prove the remaining obligations. Conclude with `(isOpen_stabLocOne _ _ _ (isCMExt_host D)).preimage (continuous_proj _ _ _)`.
-/
theorem isOpen_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (levelAd T U : Set (GA D V)) := by
  simp only [levelAd, Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_comap]
  refine ((isOpen_levelOpen _ _ _).inter (isOpen_iInter_of_finite fun v => ?_)).inter
    (U.frame.isOpen_iwahori.preimage (continuous_proj _ _ _))
  exact (isOpen_stabLocOne _ _ _ (isCMExt_host D)).preimage (continuous_proj _ _ _)

/- English proof (translation)
The claim follows from `Subgroup.isClosed_of_isOpen _ (isOpen_levelAd T U)`.
-/
theorem isClosed_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsClosed (levelAd T U : Set (GA D V)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_levelAd T U)

/- English proof (translation)
Rewrite using `[level, Subgroup.coe_subgroupOf]`. Conclude with `(isOpen_levelAd T U).preimage continuous_subtype_val`.
-/
theorem isOpen_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (level T U : Set (GfC V)) := by
  rw [level, Subgroup.coe_subgroupOf]
  exact (isOpen_levelAd T U).preimage continuous_subtype_val

/- English proof (translation)
Rewrite using `[Subtype.isCompact_iff]`. Establish `e : ((↑) : GfC V → GA D V) '' (level T U : Set (GfC V)) = (levelFin D.sp.cm.sig V.gram (frameLat V) : Set (GA D V)) ∩ levelAd T U`. Use extensionality with `g`. Simplify using `only [level, Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, mem_levelFin]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨x.2, (mem_levelAd.1 hx).1⟩, hx⟩`. Introduce and unpack `⟨⟨hf, -⟩, hg⟩`. Conclude with `⟨⟨g, hf⟩, hg, rfl⟩`. Rewrite using `[e]`.

Conclude with `(isCompact_levelFin _ _ _).inter_right (isClosed_levelAd T U)`.
-/
theorem isCompact_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsCompact (level T U : Set (GfC V)) := by
  rw [Subtype.isCompact_iff]
  have e : ((↑) : GfC V → GA D V) '' (level T U : Set (GfC V)) =
      (levelFin D.sp.cm.sig V.gram (frameLat V) : Set (GA D V)) ∩ levelAd T U := by
    ext g
    simp only [level, Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, mem_levelFin]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.2, (mem_levelAd.1 hx).1⟩, hx⟩
    · rintro ⟨⟨hf, -⟩, hg⟩
      exact ⟨⟨g, hf⟩, hg, rfl⟩
  rw [e]
  exact (isCompact_levelFin _ _ _).inter_right (isClosed_levelAd T U)

/- English proof (translation)
Simplify using `only [conv]`. Rewrite using `[← integral_mul_left_eq_self _ a]`. Use `integral_congr_ae (.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [ha, mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.
-/
theorem conv_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {f f' : G → ℂ} {a : G} (ha : ∀ y, f (a * y) = f y) (x : G) : conv μ f f' (a * x) = conv μ f f' x := by
  simp only [conv]
  rw [← integral_mul_left_eq_self _ a]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [ha, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TrMult.OneLevel

open GlobalTheory.TrMult.OneLevel in

/- English proof (translation)
Introduce `D V T U`. Use `⟨level T U, isOpen_level T U, isCompact_level T U, fun μf hμ ff hT hS => ⟨hT.isFinFamily, fun k hk g => ?_⟩⟩` and prove the remaining obligations. Take `⟨hK, hOne, hI⟩` from `mem_levelAd.1 (Subgroup.mem_subgroupOf.1 hk)`. Simplify using `only [finFn]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_mul, map_mul]`. Generalize the expression as in `proj D.sp.cm.sig V.gram v (g : GA D V) = x`. Distinguish the cases in `hv : v ∈ T.S`. Take `⟨h, -, e⟩` from `hT.2.1 ⟨v, hv⟩`. Establish `he : ∀ y, T.idem μf ⟨v, hv⟩ (proj D.sp.cm.sig V.gram v (k : GA D V) * y) = T.idem μf ⟨v, hv⟩ y` using `fun y => (typeIdem_mul_ker (μf v) (T.frame ⟨v, hv⟩).red (T.τ ⟨v, hv⟩) (k := ⟨_, hK v⟩) (((T.frame ⟨v, hv⟩).red_eq_one_iff _).2 (hOne ⟨v, hv⟩)) y).1`.

Simplify using `only at e`. Rewrite using `[e]`. Conclude with `conv_mul_left _ (conv_mul_left _ he) x`. Distinguish the cases in `hu : v = U.u`. Substitute `hu` using the available equality.

Take `⟨t, -, e⟩` from `hT.2.2.1`. Rewrite using `[e]`. Simplify using `only [SplitAt.cosetFn, SplitAt.iwahoriCoset, Set.indicator]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises.

Rewrite using `[DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, e⟩`. Use `⟨(proj D.sp.cm.sig V.gram U.u (k : GA D V))⁻¹ * a, mul_mem (inv_mem hI) ha, b, hb, ?_⟩` and prove the remaining obligations. Simplify using `only [mul_assoc]`.

Rewrite using `[eq_inv_mul_iff_mul_eq]`. Simplify `e` using `only [mul_assoc]`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨_ * a, mul_mem hI ha, b, hb, by group⟩`. Simplify using `using hS v hv hu _ (hK v) 1 (one_mem _) x`.
-/
theorem GlobalTheory.TrMult.oneLevel : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  intro D V T U
  refine ⟨level T U, isOpen_level T U, isCompact_level T U, fun μf hμ ff hT hS => ⟨hT.isFinFamily, fun k hk g => ?_⟩⟩
  obtain ⟨hK, hOne, hI⟩ := mem_levelAd.1 (Subgroup.mem_subgroupOf.1 hk)
  simp only [finFn]
  refine finprod_congr fun v => ?_
  rw [Subgroup.coe_mul, map_mul]
  generalize proj D.sp.cm.sig V.gram v (g : GA D V) = x
  by_cases hv : v ∈ T.S
  · obtain ⟨h, -, e⟩ := hT.2.1 ⟨v, hv⟩
    have he : ∀ y, T.idem μf ⟨v, hv⟩ (proj D.sp.cm.sig V.gram v (k : GA D V) * y) = T.idem μf ⟨v, hv⟩ y := fun y =>
      (typeIdem_mul_ker (μf v) (T.frame ⟨v, hv⟩).red (T.τ ⟨v, hv⟩) (k := ⟨_, hK v⟩)
        (((T.frame ⟨v, hv⟩).red_eq_one_iff _).2 (hOne ⟨v, hv⟩)) y).1
    simp only at e
    rw [e]
    exact conv_mul_left _ (conv_mul_left _ he) x
  · by_cases hu : v = U.u
    · subst hu
      obtain ⟨t, -, e⟩ := hT.2.2.1
      rw [e]
      simp only [SplitAt.cosetFn, SplitAt.iwahoriCoset, Set.indicator]
      congr 1
      apply propext
      rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨(proj D.sp.cm.sig V.gram U.u (k : GA D V))⁻¹ * a, mul_mem (inv_mem hI) ha, b, hb, ?_⟩
        simp only [mul_assoc]
        rw [eq_inv_mul_iff_mul_eq]
        simpa only [mul_assoc] using e
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨_ * a, mul_mem hI ha, b, hb, by group⟩
    · simpa using hS v hv hu _ (hK v) 1 (one_mem _) x
