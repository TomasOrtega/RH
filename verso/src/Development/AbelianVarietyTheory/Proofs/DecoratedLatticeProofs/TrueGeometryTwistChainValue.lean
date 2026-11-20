import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.TwistPlaces

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sel_under {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hsel : Formalism.L2.Col.IsSel X sel) {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {P : HeightOneSpectrum (𝓞 X.E)}
    (h : P ∈ Formalism.L2.Col.QE sel ξ) : sel (P.under (𝓞 X.F)) = P := by
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    have e : (sel v).under (𝓞 X.F) = v := HeightOneSpectrum.ext (hsel v)
    rw [e]
  · exact absurd h (Finset.notMem_empty _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem places_injective : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (J : QJ a t), J.Reads → Function.Injective fun i => (J.G i).q.v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ i i' hv
  have hv : (J.G i).q.v = (J.G i').q.v := hv
  have und : ∀ n, (J.pl n).under (𝓞 (I.rec7 l Z).host.F) = (J.G n).q.v := fun n => by
    obtain ⟨ε, hε, hε'⟩ := (J.G n).q.above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G n).idem hε hε'
  have hs : ∀ n, I.sel (J.G n).q.v = J.pl n := fun n => by
    rw [← und n]
    exact sel_under hW.tr.ok.sel_ok ((hW.tq.Q t _).1 (J.mem n))
  apply hJ.inj
  rw [← hs i, ← hs i', hv]

end GlobalTheory.TopVol.TwistPlaces
