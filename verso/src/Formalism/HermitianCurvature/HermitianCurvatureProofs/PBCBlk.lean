import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsdFormConjRewrite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

namespace Formalism.FourierDecayAlt.P.PBC.GlobalTheory

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hA : S6.idl E g 1 ν ≠ 0` using `Cx2.idl_ne_zero g hg 1 ν`. Establish `hB : S6.idl E g 2 ν ≠ 0` using `Cx2.idl_ne_zero g hg 2 ν`. Take `⟨hBL, hLA⟩` from `twistedLatticeBetween E (S6.idl E g 1 ν) (S6.idl E g 2 ν) s (Cx2.idl_two_le_one g ν) (different_power_conj_stable E g 2 ν)`. Establish `hmem : ∀ x, x ∈ S6.frameLat E (S6.perLat E g ν s) 1 ↔ ∃ t ∈ S6.perLat E g ν s, mixedEmbedding E t = x`. Introduce `x`.

Simplify using `[S6.frameLat]`. Prove the components needed by the constructor for the conclusion. Establish `hsub : (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) ⊆ (mixedEmbedding.idealLattice E (Units.mk0 _ hA) : Set (mixedEmbedding.mixedSpace E))`. Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `(hmem x).1 hx`.

Conclude with `(mixedEmbedding.mem_idealLattice E _).2 ⟨t, hLA ht, rfl⟩`. Conclude with `DiscreteTopology.of_subset (inferInstanceAs (DiscreteTopology (mixedEmbedding.idealLattice E (Units.mk0 _ hA)))) hsub`. Establish `hsub : (mixedEmbedding.idealLattice E (Units.mk0 _ hB) : Set (mixedEmbedding.mixedSpace E)) ⊆ (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E))`. Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `(mixedEmbedding.mem_idealLattice E _).1 hx`.

Conclude with `(hmem _).2 ⟨t, hBL ht, rfl⟩`. Establish `hr : Set.range (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)) ⊆ (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E))`. Introduce `x hx`. Establish `hx' : x ∈ mixedEmbedding.idealLattice E (Units.mk0 _ hB)`. Rewrite using `[← mixedEmbedding.span_idealLatticeBasis]`.

Conclude with `Submodule.subset_span hx`. Conclude with `hsub hx'`. Rewrite using `[eq_top_iff, ← (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)).span_eq]`. Conclude with `Submodule.span_mono hr`.
-/
theorem frame_facts (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ) :
    DiscreteTopology (S6.frameLat E (S6.perLat E g ν s) 1) ∧
    Submodule.span ℝ (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) = ⊤ := by
  have hA : S6.idl E g 1 ν ≠ 0 := Cx2.idl_ne_zero g hg 1 ν
  have hB : S6.idl E g 2 ν ≠ 0 := Cx2.idl_ne_zero g hg 2 ν
  obtain ⟨hBL, hLA⟩ := twistedLatticeBetween E (S6.idl E g 1 ν) (S6.idl E g 2 ν) s (Cx2.idl_two_le_one g ν)
    (different_power_conj_stable E g 2 ν)
  have hmem : ∀ x, x ∈ S6.frameLat E (S6.perLat E g ν s) 1 ↔
      ∃ t ∈ S6.perLat E g ν s, mixedEmbedding E t = x := by
    intro x
    simp [S6.frameLat]
  constructor
  · have hsub : (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) ⊆
        (mixedEmbedding.idealLattice E (Units.mk0 _ hA) : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
      exact (mixedEmbedding.mem_idealLattice E _).2 ⟨t, hLA ht, rfl⟩
    exact DiscreteTopology.of_subset
      (inferInstanceAs (DiscreteTopology (mixedEmbedding.idealLattice E (Units.mk0 _ hA)))) hsub
  · have hsub : (mixedEmbedding.idealLattice E (Units.mk0 _ hB) : Set (mixedEmbedding.mixedSpace E)) ⊆
        (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (mixedEmbedding.mem_idealLattice E _).1 hx
      exact (hmem _).2 ⟨t, hBL ht, rfl⟩
    have hr : Set.range (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)) ⊆
        (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      have hx' : x ∈ mixedEmbedding.idealLattice E (Units.mk0 _ hB) := by
        rw [← mixedEmbedding.span_idealLatticeBasis]
        exact Submodule.subset_span hx
      exact hsub hx'
    rw [eq_top_iff, ← (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)).span_eq]
    exact Submodule.span_mono hr

/- English proof (translation)
Take `⟨hd, hs⟩` from `frame_facts (E := E) g hg ν s`. Take `⟨hd', hs', -⟩` from `Formalism.FourierDecayAlt.P.euclidean_frame E _ 1 hd hs`. Conclude with `⟨hd', ⟨hs'⟩⟩`.
-/
theorem eLat_facts (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ) :
    ∃ _ : DiscreteTopology (J.eLat E (S6.perLat E g ν s) 1), IsZLattice ℝ (J.eLat E (S6.perLat E g ν s) 1) := by
  obtain ⟨hd, hs⟩ := frame_facts (E := E) g hg ν s
  obtain ⟨hd', hs', -⟩ := Formalism.FourierDecayAlt.P.euclidean_frame E _ 1 hd hs
  exact ⟨hd', ⟨hs'⟩⟩

variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def Qe (S : C.HidaSetting E Wp Wq) : J.CV E ≃ₗ[ℝ] crystallineComparison.V S.f :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace E → ℂ)).trans (LinearEquiv.piCongrLeft' ℝ (fun _ => ℂ) S.pl.symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Qe_apply (S : C.HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) : Qe S c v = c (S.pl v) := by
  rfl

def QL (S : C.HidaSetting E Wp Wq) : J.CV E ≃L[ℝ] crystallineComparison.V S.f := (Qe S).toContinuousLinearEquiv

/- English proof (translation)
Conclude with `Qe_apply S c v`.
-/
theorem QL_apply (S : C.HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) : QL S c v = c (S.pl v) := by
  exact Qe_apply S c v

/- English proof (translation)
Establish `h` using `congrArg (fun z => z v) ((QL S).apply_symm_apply y)`. Simplify `h` using `only [QL_apply]`.
-/
theorem QL_symm_apply (S : C.HidaSetting E Wp Wq) (y : crystallineComparison.V S.f) (v : Fin S.f) : (QL S).symm y (S.pl v) = y v := by
  have h := congrArg (fun z => z v) ((QL S).apply_symm_apply y)
  simpa only [QL_apply] using h

/- English proof (translation)
Establish `h : ⇑(QL S) = Formalism.FourierDecayAlt.P.JCx1.needs.Qm S`. Use function extensionality and compare the values at `c v`. Rewrite using `[QL_apply, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply]`. Rewrite using `[h]`. Conclude with `Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S`.
-/
theorem QL_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (QL S) volume volume := by
  have h : ⇑(QL S) = Formalism.FourierDecayAlt.P.JCx1.needs.Qm S := by
    funext c v
    rw [QL_apply, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply]
  rw [h]
  exact Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S

/- English proof (translation)
Conclude with `MeasurePreserving.symm (QL S).toHomeomorph.toMeasurableEquiv (QL_mp S)`.
-/
theorem QL_symm_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (QL S).symm volume volume := by
  exact MeasurePreserving.symm (QL S).toHomeomorph.toMeasurableEquiv (QL_mp S)

def eT (S : C.HidaSetting E Wp Wq) : crystallineComparison.V S.f ≃L[ℝ] J.CV E :=
  (QL S).symm.trans (Cx2.cj S).toContinuousLinearEquiv

/- English proof (translation)
The claim follows from `(LinearIsometryEquiv.measurePreserving (Cx2.cj S)).comp (QL_symm_mp S)`.
-/
theorem eT_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (eT S) volume volume :=
  (LinearIsometryEquiv.measurePreserving (Cx2.cj S)).comp (QL_symm_mp S)

/- English proof (translation)
Establish `hkey : ∀ t : E, eT S (PBC.embV S t) = J.semb E 1 t`. Introduce `t`. Use extensionality with `w`. Take `⟨v, rfl⟩` from `S.pl.surjective w`. Establish `hq : (QL S).symm (PBC.embV S t) (S.pl v) = S.σ v t` using `QL_symm_apply S _ v`.

Establish `hs : (J.semb E 1 t) (S.pl v) = (S.pl v).embedding t` using `by simp [J.semb, J.cemb]`. Rewrite using `[hs]`. Express the relevant statement in the definitionally equal form `(Cx2.cj S) ((QL S).symm (PBC.embV S t)) (S.pl v) = _`. Distinguish the cases in `h : S.σ v = (S.pl v).embedding`. Rewrite using `[(Cx2.cj_apply S _ v).1 h, hq, h]`.

Rewrite using `[(Cx2.cj_apply S _ v).2 h, hq]`. Establish `hm` using `InfinitePlace.embedding_mk_eq (S.σ v)`. Rewrite `hm` using `[show InfinitePlace.mk (S.σ v) = S.pl v from S.hemb v]`. Break down `hm with hm | hm` into its components or cases. Conclude with `absurd hm.symm h`.

Rewrite using `[hm, ComplexEmbedding.conjugate_coe_eq]`. Use extensionality with `x`. Simplify using `only [PBC.latV, ZLattice.comap, J.eLat, Submodule.mem_map, Submodule.mem_comap, AddMonoidHom.coe_toIntLinearMap, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`.

Conclude with `⟨t, ht, (hkey t).symm⟩`. Introduce and unpack `⟨t, ht, hx⟩`. Use `⟨t, ht, (eT S).injective ?_⟩` and prove the remaining obligations. Rewrite using `[hkey]`. Conclude with `hx`.
-/
theorem latV_eq (S : C.HidaSetting E Wp Wq) (L : Submodule ℤ E) :
    PBC.latV S L.toAddSubgroup = ZLattice.comap ℝ (J.eLat E L 1) (eT S).toLinearEquiv.toLinearMap := by
  have hkey : ∀ t : E, eT S (PBC.embV S t) = J.semb E 1 t := by
    intro t
    ext w
    obtain ⟨v, rfl⟩ := S.pl.surjective w
    have hq : (QL S).symm (PBC.embV S t) (S.pl v) = S.σ v t := QL_symm_apply S _ v
    have hs : (J.semb E 1 t) (S.pl v) = (S.pl v).embedding t := by simp [J.semb, J.cemb]
    rw [hs]
    change (Cx2.cj S) ((QL S).symm (PBC.embV S t)) (S.pl v) = _
    by_cases h : S.σ v = (S.pl v).embedding
    · rw [(Cx2.cj_apply S _ v).1 h, hq, h]
    · rw [(Cx2.cj_apply S _ v).2 h, hq]
      have hm := InfinitePlace.embedding_mk_eq (S.σ v)
      rw [show InfinitePlace.mk (S.σ v) = S.pl v from S.hemb v] at hm
      rcases hm with hm | hm
      · exact absurd hm.symm h
      · rw [hm, ComplexEmbedding.conjugate_coe_eq]
  ext x
  simp only [PBC.latV, ZLattice.comap, J.eLat, Submodule.mem_map, Submodule.mem_comap,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hkey t).symm⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, (eT S).injective ?_⟩
    rw [hkey]
    exact hx

end

end Formalism.FourierDecayAlt.P.PBC.GlobalTheory

namespace Formalism.FourierDecayAlt.P.PBC.GlobalTheory

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Establish `h` using `Fintype.card_congr S.pl`. Rewrite `h` using `[Fintype.card_fin]`. Rewrite using `[h]`. Conclude with `(Formalism.FourierDecayAlt.P.S6x2.degreeFacts E).2.1`.
-/
theorem f_eq_deg (S : C.HidaSetting E Wp Wq) : S.f = S6.deg E := by
  have h := Fintype.card_congr S.pl
  rw [Fintype.card_fin] at h
  rw [h]
  exact (Formalism.FourierDecayAlt.P.S6x2.degreeFacts E).2.1

/- English proof (translation)
Rewrite using `[Formalism.FourierDecayAlt.P.unipotent_dual_lattice_covolume E hU S.g _ s hg]`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, f_eq_deg S]`. Unfold `KB.dlB D.deG`. Establish `hrd` using `Formalism.FourierDecayAlt.P.Jx4.rd_pos E`. Establish `hg' : (0 : ℝ) < (S.g : ℝ)` using `by exact_mod_cast hg`.

Establish `e : S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ)) / (2 / (S6.rd E * (S.g : ℝ) ^ 3)) = S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ)) * (S6.rd E / 2) * (S.g : ℝ) ^ 3`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, mul_pow, mul_pow, ← zpow_natCast, ← zpow_mul, ← pow_mul]`.
-/
theorem prod_dlB_eq_covolume (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (b s : ℕ) :
    ∏ _v : Fin S.f, KB.dlB S b s =
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1) := by
  rw [Formalism.FourierDecayAlt.P.unipotent_dual_lattice_covolume E hU S.g _ s hg]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, f_eq_deg S]
  unfold KB.dlB D.deG
  have hrd := Formalism.FourierDecayAlt.P.Jx4.rd_pos E
  have hg' : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg
  have e : S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ)) / (2 / (S6.rd E * (S.g : ℝ) ^ 3)) =
      S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ)) * (S6.rd E / 2) * (S.g : ℝ) ^ 3 := by
    field_simp
  rw [e, mul_pow, mul_pow, ← zpow_natCast, ← zpow_mul, ← pow_mul]

/- English proof (translation)
Establish `hL` using `latV_eq S (S6.perLat E S.g (S6.nuBlock S.G.r b s) s)`. Take `⟨hd, hz⟩` from `eLat_facts (E := E) S.g hg (S6.nuBlock S.G.r b s) s`. Rewrite using `[show J.LaB E S.g S.G.r b s = (S6.perLat E S.g (S6.nuBlock S.G.r b s) s).toAddSubgroup from rfl, hL, prod_dlB_eq_covolume S hg hU b s]`. Use `haveI := hd`. Use `haveI := hz`.

Establish `hd' : DiscreteTopology (ZLattice.comap ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1) (eT S).toLinearEquiv.toLinearMap)` using `ZLattice.comap_discreteTopology _ _ (eT S).continuous (eT S).injective`. Use `haveI := hd'`. Establish `hz' : IsZLattice ℝ (ZLattice.comap ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1) (eT S).toLinearEquiv.toLinearMap)` using `inferInstance`. Conclude with `⟨hd', hz', ZLattice.covolume_comap _ _ _ (eT_mp S)⟩`.
-/
theorem lat_facts (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (b s : ℕ) :
    ∃ (_ : DiscreteTopology (PBC.latV S (J.LaB E S.g S.G.r b s)))
      (_ : IsZLattice ℝ (PBC.latV S (J.LaB E S.g S.G.r b s))),
      ZLattice.covolume (PBC.latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s := by
  have hL := latV_eq S (S6.perLat E S.g (S6.nuBlock S.G.r b s) s)
  obtain ⟨hd, hz⟩ := eLat_facts (E := E) S.g hg (S6.nuBlock S.G.r b s) s
  rw [show J.LaB E S.g S.G.r b s = (S6.perLat E S.g (S6.nuBlock S.G.r b s) s).toAddSubgroup from rfl, hL,
    prod_dlB_eq_covolume S hg hU b s]
  haveI := hd
  haveI := hz
  have hd' : DiscreteTopology (ZLattice.comap ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1)
      (eT S).toLinearEquiv.toLinearMap) :=
    ZLattice.comap_discreteTopology _ _ (eT S).continuous (eT S).injective
  haveI := hd'
  have hz' : IsZLattice ℝ (ZLattice.comap ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1)
      (eT S).toLinearEquiv.toLinearMap) := inferInstance
  exact ⟨hd', hz', ZLattice.covolume_comap _ _ _ (eT_mp S)⟩

/- English proof (translation)
Set `b0 : Module.Basis (Fin (Module.finrank ℤ La)) ℝ (crystallineComparison.V f)` to `(Pi.basisFun ℝ (Fin (Module.finrank ℤ La))).map (Formalism.FourierDecayAlt.P.PairingConjugationLemmas.Le La).symm`. Set `bd` to `b0.isUnitSMul (w := fun _ => g) (fun _ => isUnit_iff_ne_zero.mpr hg)`. Use `⟨Submodule.span ℤ (Set.range bd), inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Take `⟨m, rfl⟩` from `Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd_surj La σ hσ`.

Establish `hx : (fun j => ((m j : ℤ) : ℝ)) = ∑ j, ((m j : ℤ) : ℝ) • Pi.basisFun ℝ (Fin (Module.finrank ℤ La)) j` using `((Pi.basisFun ℝ _).sum_repr _).symm`. Establish `h : g • Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd La m = ∑ j, (m j) • bd j`. Unfold `Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd`. Rewrite using `[hx, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Module.Basis.isUnitSMul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_comm]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem dual_smul_mem {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (g : ℝ)
    (hg : g ≠ 0) : ∃ (Lm : Submodule ℤ (crystallineComparison.V f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
      ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm := by
  let b0 : Module.Basis (Fin (Module.finrank ℤ La)) ℝ (crystallineComparison.V f) :=
    (Pi.basisFun ℝ (Fin (Module.finrank ℤ La))).map (Formalism.FourierDecayAlt.P.PairingConjugationLemmas.Le La).symm
  let bd := b0.isUnitSMul (w := fun _ => g) (fun _ => isUnit_iff_ne_zero.mpr hg)
  refine ⟨Submodule.span ℤ (Set.range bd), inferInstance, inferInstance, ?_⟩
  intro σ hσ
  obtain ⟨m, rfl⟩ := Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd_surj La σ hσ
  have hx : (fun j => ((m j : ℤ) : ℝ)) = ∑ j, ((m j : ℤ) : ℝ) • Pi.basisFun ℝ (Fin (Module.finrank ℤ La)) j :=
    ((Pi.basisFun ℝ _).sum_repr _).symm
  have h : g • Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd La m = ∑ j, (m j) • bd j := by
    unfold Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd
    rw [hx, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Module.Basis.isUnitSMul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_comm]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Use `set μ : J.CV E := WithLp.toLp 2 (fun w => if S.σ (S.pl.symm w) = w.embedding then 2 * conj (σ (S.pl.symm w)) else 2 * σ (S.pl.symm w)) with hμdef`. Establish `hμv : ∀ v, μ (S.pl v) = if S.σ v = (S.pl v).embedding then 2 * conj (σ v) else 2 * σ v`. Introduce `v`. Simplify using `[hμdef]`. Establish `hμ : μ ∈ Formalism.H.dual (J.eLat E L 1)`.

Rewrite using `[Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule]`. Introduce `y hy`. Take `⟨t, ht, rfl⟩` from `Submodule.mem_map.1 hy`. Establish `hmem : PBC.embV S t ∈ PBC.latV S L.toAddSubgroup` using `Submodule.mem_map.2 ⟨t, ht, rfl⟩`. Establish `h1` using `hσ _ hmem`.

Rewrite `h1` using `[Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h1`. Establish `hpair : Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) = n`. Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`.

Establish `h2 : ((Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) : ℝ) : ℂ) = ((n : ℝ) : ℂ)`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h2` after adjusting the coercions. Establish `hinner : inner ℝ μ ((J.semb E 1).toIntLinearMap t) = Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t)`. Establish `hs : (J.semb E 1).toIntLinearMap t = J.cemb E t` using `by simp [J.semb]`. Rewrite using `[hs, PiLp.inner_apply, ← Equiv.sum_comp S.pl]`. Unfold `Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `hc : (J.cemb E t) (S.pl v) = (S.pl v).embedding t` using `by simp [J.cemb]`. Rewrite using `[hμv v, hc]`. Simplify using `only [PBC.embV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Distinguish the cases in `h : S.σ v = (S.pl v).embedding`.

Rewrite using `[if_pos h, ← h]`. Simplify using `[Complex.inner, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h]`. Establish `h2` using `(Cx2.σ_or S v).resolve_left h`.

Rewrite using `[← h2, ComplexEmbedding.conjugate_coe_eq]`. Simplify using `[Complex.inner, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Submodule.mem_one]`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[innerₗ_apply_apply, hinner, hpair]`. Simplify using the standard rewrite rules. Take `⟨l, hl, hlμ⟩` from `(Formalism.FourierDecayAlt.P.trace_dual_alt E L S.g 1 hg one_ne_zero hL μ).1 hμ`. Use `⟨l, hl, fun v => ?_⟩` and prove the remaining obligations. Establish `hcoord` using `congrArg (fun c : J.CV E => c (S.pl v)) hlμ`.

Simplify using `only [J.dm, hμv v] at hcoord`. Establish `hg' : ((S.g : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Nat.cast_pos.mpr hg).ne'`. Distinguish the cases in `h : S.σ v = (S.pl v).embedding`. Rewrite `hcoord` using `[if_pos h, ← h]`. Use `congrArg conj hcoord` as an intermediate fact.

Simplify using `only [map_mul, Complex.conj_conj, map_ofNat] at this`. Establish `h3 : conj (((2 / ((S.g : ℝ) * 1) : ℝ)) : ℂ) = ((2 / (S.g : ℝ) : ℝ) : ℂ)`. Rewrite using `[Complex.conj_ofReal]`. Simplify using the standard rewrite rules. Rewrite `this` using `[h3]`.

Move the coercions through the operations in `at this ⊢`. Establish `hg2 : (S.g : ℂ) ≠ 0` using `by exact_mod_cast hg.ne'`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hcoord` using `[if_neg h]`. Establish `h2` using `(Cx2.σ_or S v).resolve_left h`.

Rewrite `hcoord` using `[← h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`. Move the coercions through the operations in `at hcoord ⊢`. Establish `hg2 : (S.g : ℂ) ≠ 0` using `by exact_mod_cast hg.ne'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dual_to_E (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (L : Submodule ℤ E)
    (hL : ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L) (σ : crystallineComparison.V S.f)
    (hσ : σ ∈ crystallineComparison.dualSet (PBC.latV S L.toAddSubgroup)) :
    ∃ l ∈ S6.dualLat E S.g L, ∀ v, ((S.g : ℝ) : ℂ) * σ v = S.σ v l := by
  set μ : J.CV E := WithLp.toLp 2 (fun w => if S.σ (S.pl.symm w) = w.embedding then
    2 * conj (σ (S.pl.symm w)) else 2 * σ (S.pl.symm w)) with hμdef
  have hμv : ∀ v, μ (S.pl v) = if S.σ v = (S.pl v).embedding then 2 * conj (σ v) else 2 * σ v := by
    intro v; simp [hμdef]
  have hμ : μ ∈ Formalism.H.dual (J.eLat E L 1) := by
    rw [Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 hy
    have hmem : PBC.embV S t ∈ PBC.latV S L.toAddSubgroup :=
      Submodule.mem_map.2 ⟨t, ht, rfl⟩
    have h1 := hσ _ hmem
    rw [Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpair : Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) = n := by
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : ((Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
        apply mul_left_cancel₀ hne
        rw [hn]; push_cast; ring
      exact_mod_cast h2
    have hinner : inner ℝ μ ((J.semb E 1).toIntLinearMap t) = Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) := by
      have hs : (J.semb E 1).toIntLinearMap t = J.cemb E t := by simp [J.semb]
      rw [hs, PiLp.inner_apply, ← Equiv.sum_comp S.pl]
      unfold Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair
      refine Finset.sum_congr rfl fun v _ => ?_
      have hc : (J.cemb E t) (S.pl v) = (S.pl v).embedding t := by simp [J.cemb]
      rw [hμv v, hc]
      simp only [PBC.embV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      by_cases h : S.σ v = (S.pl v).embedding
      · rw [if_pos h, ← h]
        simp [Complex.inner, Complex.mul_re]
        ring
      · rw [if_neg h]
        have h2 := (Cx2.σ_or S v).resolve_left h
        rw [← h2, ComplexEmbedding.conjugate_coe_eq]
        simp [Complex.inner, Complex.mul_re]
        ring
    rw [Submodule.mem_one]
    refine ⟨n, ?_⟩
    rw [innerₗ_apply_apply, hinner, hpair]
    simp
  obtain ⟨l, hl, hlμ⟩ := (Formalism.FourierDecayAlt.P.trace_dual_alt E L S.g 1 hg one_ne_zero hL μ).1 hμ
  refine ⟨l, hl, fun v => ?_⟩
  have hcoord := congrArg (fun c : J.CV E => c (S.pl v)) hlμ
  simp only [J.dm, hμv v] at hcoord
  have hg' : ((S.g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.cast_pos.mpr hg).ne'
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [if_pos h, ← h] at hcoord
    have := congrArg conj hcoord
    simp only [map_mul, Complex.conj_conj, map_ofNat] at this
    have h3 : conj (((2 / ((S.g : ℝ) * 1) : ℝ)) : ℂ) = ((2 / (S.g : ℝ) : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal]; simp
    rw [h3] at this
    push_cast at this ⊢
    have hg2 : (S.g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    calc (S.g : ℂ) * σ v = ((S.g : ℂ) / 2) * (2 * σ v) := by ring
      _ = ((S.g : ℂ) / 2) * (2 / (S.g : ℂ) * S.σ v l) := by rw [this]
      _ = S.σ v l := by field_simp
  · rw [if_neg h] at hcoord
    have h2 := (Cx2.σ_or S v).resolve_left h
    rw [← h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj] at hcoord
    push_cast at hcoord ⊢
    have hg2 : (S.g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    calc (S.g : ℂ) * σ v = ((S.g : ℂ) / 2) * (2 * σ v) := by ring
      _ = ((S.g : ℂ) / 2) * (2 / (S.g : ℂ) * S.σ v l) := by rw [← hcoord, mul_one]
      _ = S.σ v l := by field_simp

end

end Formalism.FourierDecayAlt.P.PBC.GlobalTheory

namespace Formalism.FourierDecayAlt.P.PBC.GlobalTheory

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate nonZeroDivisors

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Unfold `crystallineComparison.mfac`. Use `split_ifs`. Conclude with `zero_le_one`. Conclude with `le_min zero_le_one (pow_nonneg (div_nonneg hL ha) K)`.
-/
theorem mfac_nonneg (K : ℕ) (L a : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) : 0 ≤ crystallineComparison.mfac K L a := by
  unfold crystallineComparison.mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hL ha) K)

/- English proof (translation)
Unfold `crystallineComparison.mfac`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `min_le_left _ _`.
-/
theorem mfac_le_one (K : ℕ) (L a : ℝ) : crystallineComparison.mfac K L a ≤ 1 := by
  unfold crystallineComparison.mfac
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/- English proof (translation)
Break down `le_total y 1 with h | h` into its components or cases. Rewrite using `[min_eq_right h]`. Conclude with `min_le_right _ _`. Rewrite using `[min_eq_left h, mul_one]`. Conclude with `(min_le_left _ _).trans hc`.
-/
theorem min_scale (c y : ℝ) (hc : 1 ≤ c) (_hy : 0 ≤ y) : min 1 (c * y) ≤ c * min 1 y := by
  rcases le_total y 1 with h | h
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left h, mul_one]
    exact (min_le_left _ _).trans hc

/- English proof (translation)
Unfold `crystallineComparison.mL J.prof`. Rewrite using `[← Equiv.prod_comp S.pl (fun w => min 1 ((Λ (S.pl.symm w) / 3 / w l) ^ K))]`. Simplify using `only [Equiv.symm_apply_apply]`. Rewrite using `[← Fin.prod_const S.f ((3 : ℝ) ^ K), ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun v _ => mfac_nonneg _ _ _ (hΛ v) (norm_nonneg _)) (fun v _ => ?_)` and prove the remaining obligations.

Establish `hpos : 0 < (S.pl v) l`. Rewrite using `[← S.hemb v, InfinitePlace.apply]`. Conclude with `norm_pos_iff.2 ((map_ne_zero _).2 hl0)`. Establish `ha : ‖((S.g : ℝ) • σ) v‖ = (S.pl v) l`. Rewrite using `[Pi.smul_apply, Complex.real_smul, hσ v, ← S.hemb v, InfinitePlace.apply]`.

Both sides reduce to the same expression. Unfold `crystallineComparison.mfac`. Rewrite using `[ha, if_neg hpos.ne']`. Establish `hy : 0 ≤ (Λ v / 3 / (S.pl v) l) ^ K` using `pow_nonneg (div_nonneg (div_nonneg (hΛ v) (by norm_num)) hpos.le) K`. Establish `key` using `min_scale ((3 : ℝ) ^ K) ((Λ v / 3 / (S.pl v) l) ^ K) (one_le_pow₀ (by norm_num)) hy`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ _ := key`.
-/
theorem mL_le_prof (S : C.HidaSetting E Wp Wq) (K : ℕ) (Λ : Fin S.f → ℝ) (hΛ : ∀ v, 0 ≤ Λ v) (σ : crystallineComparison.V S.f)
    (l : E) (hl0 : l ≠ 0) (hσ : ∀ v, ((S.g : ℝ) : ℂ) * σ v = S.σ v l) :
    crystallineComparison.mL K Λ ((S.g : ℝ) • σ) ≤ ((3 : ℝ) ^ K) ^ S.f *
      J.prof (fun w => Λ (S.pl.symm w) / 3) K l := by
  unfold crystallineComparison.mL J.prof
  rw [← Equiv.prod_comp S.pl (fun w => min 1 ((Λ (S.pl.symm w) / 3 / w l) ^ K))]
  simp only [Equiv.symm_apply_apply]
  rw [← Fin.prod_const S.f ((3 : ℝ) ^ K), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => mfac_nonneg _ _ _ (hΛ v) (norm_nonneg _)) (fun v _ => ?_)
  have hpos : 0 < (S.pl v) l := by
    rw [← S.hemb v, InfinitePlace.apply]
    exact norm_pos_iff.2 ((map_ne_zero _).2 hl0)
  have ha : ‖((S.g : ℝ) • σ) v‖ = (S.pl v) l := by
    rw [Pi.smul_apply, Complex.real_smul, hσ v, ← S.hemb v, InfinitePlace.apply]
    rfl
  unfold crystallineComparison.mfac
  rw [ha, if_neg hpos.ne']
  have hy : 0 ≤ (Λ v / 3 / (S.pl v) l) ^ K :=
    pow_nonneg (div_nonneg (div_nonneg (hΛ v) (by norm_num)) hpos.le) K
  have key := min_scale ((3 : ℝ) ^ K) ((Λ v / 3 / (S.pl v) l) ^ K) (one_le_pow₀ (by norm_num)) hy
  calc min 1 ((Λ v / (S.pl v) l) ^ K) = min 1 ((3 : ℝ) ^ K * (Λ v / 3 / (S.pl v) l) ^ K) := by
        rw [← mul_pow]
        congr 2
        field_simp
    _ ≤ _ := key

/- English proof (translation)
Rewrite using `[← Fintype.card_fin S.f]`. Conclude with `Fintype.card_congr S.pl.symm`.
-/
theorem card_places (S : C.HidaSetting E Wp Wq) : Fintype.card (InfinitePlace E) = S.f := by
  rw [← Fintype.card_fin S.f]
  exact Fintype.card_congr S.pl.symm

/- English proof (translation)
Use `set ν := S6.nuBlock S.G.r b s with hν`. Use `set L := S6.perLat E S.g ν s with hLdef`. Establish `hA : S6.idl E S.g 1 ν ≠ 0` using `Cx2.idl_ne_zero S.g hg 1 ν`. Establish `hB : S6.idl E S.g 2 ν ≠ 0` using `Cx2.idl_ne_zero S.g hg 2 ν`. Establish `hL : ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L` using `(twistedIsRealOrderLattice E (S6.idl E S.g 1 ν) (S6.idl E S.g 2 ν) s hB (Cx2.idl_two_le_one S.g ν) (different_power_conj_stable E S.g 2 ν)).2`.

Establish `hLaB : J.LaB E S.g S.G.r b s = L.toAddSubgroup` using `rfl`. Establish `hBL` using `block_lattices lattice_facts_general dualIdealEqLiftIdeal scaledIdealNorm E hU S.g S.G.r b s hg`. Establish `hdual : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)), ∃ l ∈ S6.dualLat E S.g L, ∀ v, ((S.g : ℝ) : ℂ) * (σ : crystallineComparison.V S.f) v = S.σ v l`. Introduce `σ`. Conclude with `dual_to_E S hg L hL σ.1 σ.2`.

Use `choose lσ hlσ hlσv using hdual`. Establish `hΛ0 : ∀ v, 0 ≤ Λ v` using `fun v => (hΛ v).1`. Establish `hF0 : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)), 0 ≤ crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))` using `fun σ => Finset.prod_nonneg fun v _ => mfac_nonneg _ _ _ (hΛ0 v) (norm_nonneg _)`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not T (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0)]`. Use `add_le_add ?_ ?_` and prove the remaining obligations.

Establish `hcard : (T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0)).card ≤ 1`. Rewrite using `[Finset.card_le_one]`. Introduce `a ha a' ha'`. Rewrite `ha`, `ha'` using `[Finset.mem_filter]`. Conclude with `Subtype.ext (ha.2.trans ha'.2.symm)`.

Combine the equalities or inequalities in the displayed calculation. Use `set T1 := T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => ¬ σ.1 = 0) with hT1`. Establish `hl0 : ∀ σ ∈ T1, lσ σ ≠ 0`. Introduce `σ hσ h0`. Rewrite `hσ` using `[hT1, Finset.mem_filter]`.

Apply `hσ.2` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Use `hlσv σ v` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Establish `hg' : (S.g : ℂ) ≠ 0` using `by exact_mod_cast hg.ne'`.

Move the coercions through the operations in `at this`. Conclude with `(mul_eq_zero.1 this).resolve_left hg'`. Establish `hinj : Set.InjOn lσ (T1 : Set _)`. Introduce `σ _ σ' _ h`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `v`. Establish `h1` using `hlσv σ v`. Establish `h2` using `hlσv σ' v`. Rewrite `h1` using `[h]`. Establish `hg' : ((S.g : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Nat.cast_pos.mpr hg).ne'`.

Conclude with `mul_left_cancel₀ hg' (h1.trans h2.symm)`. Use `set x : InfinitePlace E → ℝ := fun w => Λ (S.pl.symm w) / 3 with hx`. Establish `hx0 : ∀ w, 0 ≤ x w` using `fun w => div_nonneg (hΛ0 _) (by norm_num)`. Establish `hN0 : S6.dualIdl E S.g ν ≠ 0` using `hBL.2.2.2.1`. Establish `hNpos : (0 : ℝ) < (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ)`.

Establish `h1 : FractionalIdeal.absNorm (S6.dualIdl E S.g ν) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.absNorm_eq_zero_iff]` and apply the resulting hypothesis. Establish `h2` using `FractionalIdeal.absNorm_nonneg (S6.dualIdl E S.g ν)`. Conclude with `lt_of_le_of_ne h2 (Ne.symm h1)` after adjusting the coercions. Establish `hthr0 : ∀ w, 0 ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w`.

Introduce `w`. Use `hΛ (S.pl.symm w)` as an intermediate fact. Establish `h' : PBC.thr S b s (S.pl.symm w) = J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w`. Simplify using `[PBC.thr]`. Combine the linear relations using `[this.1, this.2, h'.le, h'.ge]`.

Establish `hprodthr : ∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w ≤ √(FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ)`. Establish `hv : (∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w) ^ 2 / (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) ≤ 1` using `hvol`. Rewrite `hv` using `[div_le_one hNpos]`. Conclude with `Real.le_sqrt_of_sq_le hv`. Establish `hprodx : ∏ w, x w ≤ (1 / 3) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hx, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, one_div, inv_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (1 / 3) ^ Fintype.card (InfinitePlace E) * ∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by`. Use `mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun w _ => hΛ0 _) fun w _ => ?_) (by positivity)` and prove the remaining obligations.

Use `(hΛ (S.pl.symm w)).2` as an intermediate fact. Simplify `this` using `[PBC.thr]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left hprodthr (by positivity)`. Establish `hLS` using `hbox (S6.dualIdl E S.g ν) (S6.dualLat E S.g L).toAddSubgroup x C.Kst 3 1 hN0 (fun l hl => hBL.2.1 l hl) hx0 (by norm_num [C.Kst]) le_rfl (by norm_num) (by simpa using hprodx)`. Rewrite `hLS` using `[card_places S]`.

Establish `hep : (C0 * (1 : ℝ) ^ ((C.Kst : ℝ) - 5 / 2) * (3 : ℝ) ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f ≤ C0 ^ S.f`. Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations. Rewrite using `[Real.one_rpow, mul_one]`. Use `mul_le_of_le_one_right (by linarith) ?_` and prove the remaining obligations. Conclude with `Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num [C.Kst])`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum, Finset.sum_image hinj]`. Use `_ ≤ ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f := by`. Use `mul_le_mul_of_nonneg_left ((hLS.2 _ fun l hl => ?_).trans hep) (by positivity)` and prove the remaining obligations. Take `⟨σ, hσ, rfl⟩` from `Finset.mem_image.1 hl`.

Conclude with `⟨hlσ σ, hl0 σ hσ⟩`.
-/
theorem sum_le (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (b s : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hbox : ∀ (aa : FractionalIdeal (𝓞 E)⁰ E) (L : AddSubgroup E) (x : InfinitePlace E → ℝ) (K : ℕ) (Θ a : ℝ),
      aa ≠ 0 → (∀ l ∈ L, l ∈ aa) → (∀ w, 0 ≤ x w) → 3 ≤ K → 1 ≤ a → 2 * a < Θ →
      ∏ w, x w ≤ (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) →
      TA.LatSum L (J.prof x K) ((C0 * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
        Fintype.card (InfinitePlace E)))
    (Λ : Fin S.f → ℝ) (hΛ : ∀ v, 0 ≤ Λ v ∧ Λ v ≤ PBC.thr S b s v) (hvol : S.base.vol b s ≤ 1)
    (T : Finset (crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)))) :
    ∑ σ ∈ T, crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ 1 + ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f := by
  set ν := S6.nuBlock S.G.r b s with hν
  set L := S6.perLat E S.g ν s with hLdef
  have hA : S6.idl E S.g 1 ν ≠ 0 := Cx2.idl_ne_zero S.g hg 1 ν
  have hB : S6.idl E S.g 2 ν ≠ 0 := Cx2.idl_ne_zero S.g hg 2 ν
  have hL : ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L :=
    (twistedIsRealOrderLattice E (S6.idl E S.g 1 ν) (S6.idl E S.g 2 ν) s hB (Cx2.idl_two_le_one S.g ν)
      (different_power_conj_stable E S.g 2 ν)).2
  have hLaB : J.LaB E S.g S.G.r b s = L.toAddSubgroup := rfl
  have hBL := block_lattices lattice_facts_general dualIdealEqLiftIdeal scaledIdealNorm E hU
    S.g S.G.r b s hg
  have hdual : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)),
      ∃ l ∈ S6.dualLat E S.g L, ∀ v, ((S.g : ℝ) : ℂ) * (σ : crystallineComparison.V S.f) v = S.σ v l := by
    intro σ
    exact dual_to_E S hg L hL σ.1 σ.2
  choose lσ hlσ hlσv using hdual
  have hΛ0 : ∀ v, 0 ≤ Λ v := fun v => (hΛ v).1
  have hF0 : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)),
      0 ≤ crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) :=
    fun σ => Finset.prod_nonneg fun v _ => mfac_nonneg _ _ _ (hΛ0 v) (norm_nonneg _)
  rw [← Finset.sum_filter_add_sum_filter_not T (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0)]
  refine add_le_add ?_ ?_
  ·
    have hcard : (T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha a' ha'
      rw [Finset.mem_filter] at ha ha'
      exact Subtype.ext (ha.2.trans ha'.2.symm)
    calc _ ≤ ∑ σ ∈ T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0), (1 : ℝ) :=
          Finset.sum_le_sum fun σ _ => Finset.prod_le_one (fun v _ => mfac_nonneg _ _ _ (hΛ0 v) (norm_nonneg _))
            fun v _ => mfac_le_one _ _ _
      _ ≤ 1 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hcard
  ·
    set T1 := T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => ¬ σ.1 = 0) with hT1
    have hl0 : ∀ σ ∈ T1, lσ σ ≠ 0 := by
      intro σ hσ h0
      rw [hT1, Finset.mem_filter] at hσ
      apply hσ.2
      funext v
      have := hlσv σ v
      rw [h0, map_zero] at this
      have hg' : (S.g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
      push_cast at this
      exact (mul_eq_zero.1 this).resolve_left hg'
    have hinj : Set.InjOn lσ (T1 : Set _) := by
      intro σ _ σ' _ h
      apply Subtype.ext
      funext v
      have h1 := hlσv σ v
      have h2 := hlσv σ' v
      rw [h] at h1
      have hg' : ((S.g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.cast_pos.mpr hg).ne'
      exact mul_left_cancel₀ hg' (h1.trans h2.symm)
    set x : InfinitePlace E → ℝ := fun w => Λ (S.pl.symm w) / 3 with hx
    have hx0 : ∀ w, 0 ≤ x w := fun w => div_nonneg (hΛ0 _) (by norm_num)
    have hN0 : S6.dualIdl E S.g ν ≠ 0 := hBL.2.2.2.1
    have hNpos : (0 : ℝ) < (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) := by
      have h1 : FractionalIdeal.absNorm (S6.dualIdl E S.g ν) ≠ 0 := by
        rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
      have h2 := FractionalIdeal.absNorm_nonneg (S6.dualIdl E S.g ν)
      exact_mod_cast lt_of_le_of_ne h2 (Ne.symm h1)
    have hthr0 : ∀ w, 0 ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by
      intro w
      have := hΛ (S.pl.symm w)
      have h' : PBC.thr S b s (S.pl.symm w) = J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by
        simp [PBC.thr]
      linarith [this.1, this.2, h'.le, h'.ge]
    have hprodthr : ∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w ≤
        √(FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) := by
      have hv : (∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w) ^ 2 /
          (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) ≤ 1 := hvol
      rw [div_le_one hNpos] at hv
      exact Real.le_sqrt_of_sq_le hv
    have hprodx : ∏ w, x w ≤ (1 / 3) ^ Fintype.card (InfinitePlace E) *
        √(FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) := by
      calc ∏ w, x w = (1 / 3) ^ Fintype.card (InfinitePlace E) * ∏ w, Λ (S.pl.symm w) := by
            rw [hx, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, one_div, inv_pow]; ring
        _ ≤ (1 / 3) ^ Fintype.card (InfinitePlace E) * ∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun w _ => hΛ0 _) fun w _ => ?_)
              (by positivity)
            have := (hΛ (S.pl.symm w)).2
            simpa [PBC.thr] using this
        _ ≤ _ := mul_le_mul_of_nonneg_left hprodthr (by positivity)
    have hLS := hbox (S6.dualIdl E S.g ν) (S6.dualLat E S.g L).toAddSubgroup x C.Kst 3 1 hN0
      (fun l hl => hBL.2.1 l hl) hx0 (by norm_num [C.Kst]) le_rfl (by norm_num) (by simpa using hprodx)
    rw [card_places S] at hLS
    have hep : (C0 * (1 : ℝ) ^ ((C.Kst : ℝ) - 5 / 2) * (3 : ℝ) ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f ≤ C0 ^ S.f := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [Real.one_rpow, mul_one]
      refine mul_le_of_le_one_right (by linarith) ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num [C.Kst])
    calc ∑ σ ∈ T1, crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))
        ≤ ∑ σ ∈ T1, ((3 : ℝ) ^ C.Kst) ^ S.f * J.prof x C.Kst (lσ σ) :=
          Finset.sum_le_sum fun σ hσ => mL_le_prof S C.Kst Λ hΛ0 σ (lσ σ) (hl0 σ hσ) (hlσv σ)
      _ = ((3 : ℝ) ^ C.Kst) ^ S.f * ∑ l ∈ T1.image lσ, J.prof x C.Kst l := by
          rw [← Finset.mul_sum, Finset.sum_image hinj]
      _ ≤ ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f := by
          refine mul_le_mul_of_nonneg_left ((hLS.2 _ fun l hl => ?_).trans hep) (by positivity)
          obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hl
          exact ⟨hlσ σ, hl0 σ hσ⟩

end

end Formalism.FourierDecayAlt.P.PBC.GlobalTheory

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset NumberField

/- English proof (translation)
Take `⟨C0, hC0, hbox⟩` from `Formalism.FourierDecayAlt.P.box_sum_lattice Formalism.SA.P.smoothedSumBound`. Use `⟨2 * 3 ^ C.Kst * C0, by` and prove the remaining obligations. Establish `: (1 : ℝ) ≤ 3 ^ C.Kst` using `one_le_pow₀ (by norm_num)`. Use the proof step `nlinarith, ?_⟩`. Introduce `E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b s _hb _hs`.

Establish `hg : 0 < S.g` using `Nat.mul_pos hg1 hg2`. Take `⟨i1, i2, hcov⟩` from `GlobalTheory.lat_facts S hg hU b s`. Use `⟨i1, i2, hcov, GlobalTheory.dual_smul_mem _ _ (by exact_mod_cast hg.ne'), ?_⟩` and prove the remaining obligations. Introduce `Λ hΛ hvol`. Establish `hf : 1 ≤ S.f`.

Rewrite using `[GlobalTheory.f_eq_deg S]`. Conclude with `(Formalism.FourierDecayAlt.P.degreeFacts_statement E).2.2`. Establish `hbound : 1 + ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f ≤ (2 * 3 ^ C.Kst * C0) ^ S.f`. Establish `h1 : (1 : ℝ) ≤ (3 ^ C.Kst * C0) ^ S.f` using `one_le_pow₀ (by`. Establish `: (1 : ℝ) ≤ 3 ^ C.Kst` using `one_le_pow₀ (by norm_num)`.

Use the proof step `nlinarith)`. Establish `h2 : (2 : ℝ) ≤ 2 ^ S.f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow, mul_assoc, mul_pow 2]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsum` using `GlobalTheory.sum_le S hg hU b s C0 hC0 (hbox E) Λ hΛ hvol`. Establish `hF0 : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)), 0 ≤ crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))` using `fun σ => Finset.prod_nonneg fun v _ => GlobalTheory.mfac_nonneg _ _ _ (hΛ v).1 (norm_nonneg _)`. Establish `hS : Summable (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))` using `summable_of_sum_le hF0 (fun T => (hsum T).trans hbound)`. Conclude with `⟨hS, hS.tsum_le_of_sum_le fun T => (hsum T).trans hbound⟩`.
-/
theorem pbc_blockLatV : PBC.BlockLatV := by
  obtain ⟨C0, hC0, hbox⟩ := Formalism.FourierDecayAlt.P.box_sum_lattice Formalism.SA.P.smoothedSumBound
  refine ⟨2 * 3 ^ C.Kst * C0, by
    have : (1 : ℝ) ≤ 3 ^ C.Kst := one_le_pow₀ (by norm_num)
    nlinarith, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b s _hb _hs
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  obtain ⟨i1, i2, hcov⟩ := GlobalTheory.lat_facts S hg hU b s
  refine ⟨i1, i2, hcov, GlobalTheory.dual_smul_mem _ _ (by exact_mod_cast hg.ne'), ?_⟩
  intro Λ hΛ hvol
  have hf : 1 ≤ S.f := by
    rw [GlobalTheory.f_eq_deg S]; exact (Formalism.FourierDecayAlt.P.degreeFacts_statement E).2.2
  have hbound : 1 + ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f ≤ (2 * 3 ^ C.Kst * C0) ^ S.f := by
    have h1 : (1 : ℝ) ≤ (3 ^ C.Kst * C0) ^ S.f := one_le_pow₀ (by
      have : (1 : ℝ) ≤ 3 ^ C.Kst := one_le_pow₀ (by norm_num)
      nlinarith)
    have h2 : (2 : ℝ) ≤ 2 ^ S.f := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ S.f := pow_le_pow_right₀ (by norm_num) hf
    rw [← mul_pow, mul_assoc, mul_pow 2]
    nlinarith
  have hsum := GlobalTheory.sum_le S hg hU b s C0 hC0 (hbox E) Λ hΛ hvol
  have hF0 : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)),
      0 ≤ crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) :=
    fun σ => Finset.prod_nonneg fun v _ => GlobalTheory.mfac_nonneg _ _ _ (hΛ v).1 (norm_nonneg _)
  have hS : Summable (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) =>
      crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :=
    summable_of_sum_le hF0 (fun T => (hsum T).trans hbound)
  exact ⟨hS, hS.tsum_le_of_sum_le fun T => (hsum T).trans hbound⟩

end Formalism.FourierDecayAlt.P.PBC
