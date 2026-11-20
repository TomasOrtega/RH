import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRatOfSeriesRatS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEmbeddingCompatibilityRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingScalarsIntegralStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

/- English proof (translation)
Introduce `h1 h2 h3 h4 hA hC`. Establish `h4'` using `GlobalTheory.SerStdFit.seriesRat_of_seriesRatS h4`. Establish `hD` using `GlobalTheory.T.realization_embedding_compatible`. Establish `hR` using `GlobalTheory.T.exists_coefficient_lattice_span h1 h2 h3 h4'`. Establish `hG` using `GlobalTheory.T.twisted_embedding_compatibility_rows h1 h2 h3 h4' hA hC`.

Establish `hS` using `GlobalTheory.T.twisted_ring_embedding_rows`. Unfold `TwGe`. Unfold `AtFit AtTw AtPts at hD hG hS ⊢`. Unfold `AtTw AtPts at hR`. Use `(((hD.and hR).and hG).and hS).imp fun Fm CH _ H => ?_` and prove the remaining obligations.

Take `⟨x0, hx0⟩` from `((H.1.1.1.and H.1.1.2).and H.1.2).and H.2`. Use `⟨x0, fun x hx h0 i p hp hM w hw j ρ hρ ν rd hfit hcan => ?_⟩` and prove the remaining obligations. Take `⟨⟨⟨k1, k2⟩, k3⟩, k4⟩` from `hx0 x hx h0 i p hp`. Establish `d` using `k1 hM w hw j ρ hρ ν rd hfit hcan`. Establish `r` using `k2 hM w hw j`.

Establish `g` using `k3 hM w hw j ρ hρ ν rd hfit hcan`. Establish `s` using `k4 hM w hw j ρ hρ ν rd hfit hcan`. Take `⟨-, e, he1, he2⟩` from `hfit.1`. Unfold `twLat`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨n, h, w', a, κ, N, hN, hκ, hhw, ha⟩` from `g e he1 he2 z hz`. Use `choose y hy hyv using fun k => r (h k) (hhw k).1 (w' k) (hhw k).2`. Take `⟨b, hb⟩` from `s e he1 he2 z n a y κ N hy hN hκ (ha y hyv)`. Rewrite using `[d e he1 he2 z n (fun k => b * a k) y hy hb]`.

Use `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y k, Submodule.subset_span ⟨h k, (hhw k).1, w' k, (hhw k).2, fun v => ?_⟩, rfl⟩)` and prove the remaining obligations. Rewrite using `[one_smul]`. Conclude with `hyv k v`.
-/
theorem twGe : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → TwAdm → TwChr → TwGe := by
  intro h1 h2 h3 h4 hA hC
  have h4' := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS h4
  have hD := GlobalTheory.T.realization_embedding_compatible
  have hR := GlobalTheory.T.exists_coefficient_lattice_span h1 h2 h3 h4'
  have hG := GlobalTheory.T.twisted_embedding_compatibility_rows h1 h2 h3 h4' hA hC
  have hS := GlobalTheory.T.twisted_ring_embedding_rows
  unfold TwGe
  unfold AtFit AtTw AtPts at hD hG hS ⊢
  unfold AtTw AtPts at hR
  refine (((hD.and hR).and hG).and hS).imp fun Fm CH _ H => ?_
  obtain ⟨x0, hx0⟩ := ((H.1.1.1.and H.1.1.2).and H.1.2).and H.2
  refine ⟨x0, fun x hx h0 i p hp hM w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hx0 x hx h0 i p hp
  have d := k1 hM w hw j ρ hρ ν rd hfit hcan
  have r := k2 hM w hw j
  have g := k3 hM w hw j ρ hρ ν rd hfit hcan
  have s := k4 hM w hw j ρ hρ ν rd hfit hcan
  obtain ⟨-, e, he1, he2⟩ := hfit.1
  unfold twLat
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, h, w', a, κ, N, hN, hκ, hhw, ha⟩ := g e he1 he2 z hz
  choose y hy hyv using fun k => r (h k) (hhw k).1 (w' k) (hhw k).2
  obtain ⟨b, hb⟩ := s e he1 he2 z n a y κ N hy hN hκ (ha y hyv)
  rw [d e he1 he2 z n (fun k => b * a k) y hy hb]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y k,
    Submodule.subset_span ⟨h k, (hhw k).1, w' k, (hhw k).2, fun v => ?_⟩, rfl⟩)
  rw [one_smul]
  exact hyv k v

end GlobalTheory.BigOn.Exp
