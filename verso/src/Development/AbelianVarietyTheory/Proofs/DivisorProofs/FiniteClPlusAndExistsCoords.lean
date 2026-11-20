import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.ChiGrid
open Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open scoped ComplexOrder

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram`. Introduce `x hx`. Take `⟨b, hb⟩` from `(GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨x, hx⟩`. Take `⟨g, rfl⟩` from `hπ.surjective b`. Use `⟨g, Eq.trans ?_ (congrArg Subtype.val hb)⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.Mass.coe_swapPts, hπ g]`. Both sides reduce to the same expression.
-/
theorem UA_le_range_finE (V : HSp D) : UA D.sp.cm V.gram ≤ (finE V).range := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  intro x hx
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, Eq.trans ?_ (congrArg Subtype.val hb)⟩
  rw [GlobalTheory.Mass.coe_swapPts, hπ g]
  rfl

/- English proof (translation)
Establish `h0 : (GinfC V).map (finE V) = ⊥` using `(Subgroup.map_eq_bot_iff _).2 fun g hg => by`. Express the relevant statement in the definitionally equal form `Formalism.UG.bc (swapAE D) (finHom V g) = 1`. Rewrite using `[show finHom V g = 1 from hg, map_one]`. Establish `h` using `congrArg (Subgroup.map (finE V)) (GlobalTheory.Mass.Levels.comap_finE V K)`. Rewrite `h` using `[Subgroup.map_comap_eq_self (hK.trans (UA_le_range_finE V)), Subgroup.map_sup, h0, sup_bot_eq]`.

Conclude with `h.symm`.
-/
theorem map_levA (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))} (hK : K ≤ UA D.sp.cm V.gram) :
    (levA V K).map (finE V) = K := by
  have h0 : (GinfC V).map (finE V) = ⊥ := (Subgroup.map_eq_bot_iff _).2 fun g hg => by
    change Formalism.UG.bc (swapAE D) (finHom V g) = 1
    rw [show finHom V g = 1 from hg, map_one]
  have h := congrArg (Subgroup.map (finE V)) (GlobalTheory.Mass.Levels.comap_finE V K)
  rw [Subgroup.map_comap_eq_self (hK.trans (UA_le_range_finE V)), Subgroup.map_sup, h0, sup_bot_eq] at h
  exact h.symm

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Establish `ho` using `(congLev_open_compact V hΛ h𝔪).1`. Establish `hc` using `(congLev_open_compact V hΛ (𝔪 := ⊤) top_ne_bot).2`. Rewrite using `[← map_levA V (K := congLev D.sp.cm V.gram Λ ⊤) fun _ h => h.1, ← Subgroup.relIndex_comap]`. Use `haveI := isCompact_iff_compactSpace.1 hc`.

Use `haveI : CompactSpace (levA V (congLev D.sp.cm V.gram Λ ⊤)) := this`. Use `haveI := Subgroup.quotient_finite_of_isOpen (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V)).subgroupOf (levA V (congLev D.sp.cm V.gram Λ ⊤))) (ho.preimage continuous_subtype_val)`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem congLev_relIndex_ne_zero (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (congLev D.sp.cm V.gram Λ 𝔪).relIndex (congLev D.sp.cm V.gram Λ ⊤) ≠ 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have ho := (congLev_open_compact V hΛ h𝔪).1
  have hc := (congLev_open_compact V hΛ (𝔪 := ⊤) top_ne_bot).2
  rw [← map_levA V (K := congLev D.sp.cm V.gram Λ ⊤) fun _ h => h.1, ← Subgroup.relIndex_comap]
  haveI := isCompact_iff_compactSpace.1 hc
  haveI : CompactSpace (levA V (congLev D.sp.cm V.gram Λ ⊤)) := this
  haveI := Subgroup.quotient_finite_of_isOpen
    (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V)).subgroupOf (levA V (congLev D.sp.cm V.gram Λ ⊤)))
    (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Establish `hJ` using `(GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V`. Establish `hfin` using `Formalism.UG.Final.ClassSetFiniteL D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram (cm_comp D.sp.cm) (Matrix.ext fun i j => hJ.1 i j) hJ.2.isUnit (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => hV _) Λ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top`. Establish `e : Formalism.UG.levelAfL D.sp.cm.sig V.gram Λ = congLev D.sp.cm V.gram Λ ⊤` using `congLev_top.symm`. Rewrite `hfin` using `[e]`. Use `class_set_finite_of_finite_index _ _ _ _ ?_ ?_ hfin` and prove the remaining obligations.

Conclude with `fun x hx => Subgroup.mem_subgroupOf.2 (congLev_mono le_top (Subgroup.mem_subgroupOf.1 hx))`. Rewrite using `[Subgroup.relIndex_subgroupOf (show congLev D.sp.cm V.gram Λ ⊤ ≤ UA D.sp.cm V.gram from fun _ h => h.1)]`. Conclude with `congLev_relIndex_ne_zero V hΛ h𝔪`.
-/
theorem finite_cl_congLev (V : HSp D) (hV : ∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (Cl D.sp.cm V.gram (congLev D.sp.cm V.gram Λ 𝔪)) := by
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hfin := Formalism.UG.Final.ClassSetFiniteL D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram (cm_comp D.sp.cm)
    (Matrix.ext fun i j => hJ.1 i j) hJ.2.isUnit (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => hV _) Λ
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top
  have e : Formalism.UG.levelAfL D.sp.cm.sig V.gram Λ = congLev D.sp.cm V.gram Λ ⊤ := congLev_top.symm
  rw [e] at hfin
  refine class_set_finite_of_finite_index _ _ _ _ ?_ ?_ hfin
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (congLev_mono le_top (Subgroup.mem_subgroupOf.1 hx))
  · rw [Subgroup.relIndex_subgroupOf (show congLev D.sp.cm V.gram Λ ⊤ ≤ UA D.sp.cm V.gram from fun _ h => h.1)]
    exact congLev_relIndex_ne_zero V hΛ h𝔪

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GlobalTheory.ChiGrid.GridData L sc)

instance finite_clPlus : Finite G.ClPlus :=
  finite_cl_congLev (Xp G) (posDef_Xp G) (isV_Xp G).sd.1 (G.pl.modul_ne_bot sc)

/- English proof (translation)
The claim follows from `haveI := G.finite_datum h inferInstance`.
-/
theorem finite_testIx (h : (L.ΛY 0).FG) : Finite (TestIx G) :=
  haveI := G.finite_datum h
  inferInstance

/- English proof (translation)
Use `haveI := finite_testIx G h`. Use `haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx (Xp G).rank (Xp G).rank (LaP G τ).natW) := fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite _ _ _).to_subtype`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin (TestIx G × VVIdx (LaP G))`. Conclude with `⟨n, ⟨e.symm⟩⟩`.
-/
theorem exists_coords (h : (L.ΛY 0).FG) :
    ∃ n, Nonempty (Fin n ≃ GlobalTheory.FunObj.TestIx G × VVIdx (GlobalTheory.FunObj.LaP G)) := by
  haveI := finite_testIx G h
  haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx (Xp G).rank (Xp G).rank (LaP G τ).natW) :=
    fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite _ _ _).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (TestIx G × VVIdx (LaP G))
  exact ⟨n, ⟨e.symm⟩⟩

end GlobalTheory.FunObj

end
