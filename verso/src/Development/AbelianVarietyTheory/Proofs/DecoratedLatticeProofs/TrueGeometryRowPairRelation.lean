import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairSymmetryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Fam

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha haT hiA`. Apply the tactic sequence `obtain ⟨C, hC, hloc⟩ := GlobalTheory.T.true_geometry_row_pair_symmetry W hAll u a ha haT hiA`. Use `⟨fun j => (C j)⁻¹, fun j hj => inv_ne_zero (hC j hj), ?_⟩` and prove the remaining obligations. Introduce `t J hJ e he j hj α γ`. Take `⟨Ξl, hΞl, hfac⟩` from `hloc t J hJ j hj α γ`.

Take `⟨hv0, hvl, hvT⟩` from `GlobalTheory.T.true_geometry_chain_descent W hAll u a ha haT j hj`. Establish `hinj : Function.Injective fun n : Fin a.n => ((a.pl n : (pk W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E)` using `fun n n' h => a.pl.injective (Subtype.ext h)`. Establish `hmem : ∀ PP, PP ∈ (B.primes X).vGs ↔ ∃ n : Fin a.n, ((a.pl n : (pk W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) = PP`. Introduce `PP`. Use `Iff.trans (hAll.lev.2.1 PP).symm ⟨fun h => ⟨a.pl.symm ⟨PP, h⟩, by rw [Equiv.apply_symm_apply]⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨n, rfl⟩`. Conclude with `(a.pl n).2`. Establish `hL : ∀ i, i ≤ B.R.m → IsSelfDualC _ (a.g.x i).L ∧ ((a.g.x i).L : Set (Fin ((I.rec7 l Z).sp.X i).rank → (I.rec7 l Z).host.E)) = intVec _ _` using `fun i hi => ⟨(ha.x i hi).sd, Set.ext (haT.pinX.xs i hi).2.2⟩`. Establish `key` using `GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (pk W).ψ haT.pinX.std _ _ ((B.primes X).vT u) (B.primes X).vGs a.n _ hinj hmem (GlobalTheory.T.type_primes_disjoint W hAll u) (fun n => (a.G n).cg j) Ξl hΞl (a.g.x j).L (a.g.x (j + 1)).L (hL j (by omega)).1 (hL (j …`. Rewrite `key` using `[← ha.gpin.dG j (by exact hj) _ hvT]`.

Establish `hCj : C j ≠ 0` using `hC j (by omega)`. Use `key using 2 with z` and compare the differences between its conclusion and the goal. Simplify using `only [xiOff, map_mul, hfac z]`. Clear the denominators using the available nonvanishing facts.
-/
theorem ratDatum_xiOff_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : QJ a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (pk W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (pk W).ψ _ _ (a.v.dG j) (comb (pk W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha haT hiA
  obtain ⟨C, hC, hloc⟩ := GlobalTheory.T.true_geometry_row_pair_symmetry W hAll u a ha haT hiA
  refine ⟨fun j => (C j)⁻¹, fun j hj => inv_ne_zero (hC j hj), ?_⟩
  intro t J hJ e he j hj α γ
  obtain ⟨Ξl, hΞl, hfac⟩ := hloc t J hJ j hj α γ
  obtain ⟨hv0, hvl, hvT⟩ := GlobalTheory.T.true_geometry_chain_descent W hAll u a ha haT j hj
  have hinj : Function.Injective fun n : Fin a.n => ((a.pl n : (pk W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) :=
    fun n n' h => a.pl.injective (Subtype.ext h)
  have hmem : ∀ PP, PP ∈ (B.primes X).vGs ↔ ∃ n : Fin a.n, ((a.pl n : (pk W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) = PP := by
    intro PP
    refine Iff.trans (hAll.lev.2.1 PP).symm ⟨fun h => ⟨a.pl.symm ⟨PP, h⟩, by rw [Equiv.apply_symm_apply]⟩, ?_⟩
    rintro ⟨n, rfl⟩
    exact (a.pl n).2
  have hL : ∀ i, i ≤ B.R.m → IsSelfDualC _ (a.g.x i).L ∧
      ((a.g.x i).L : Set (Fin ((I.rec7 l Z).sp.X i).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun i hi => ⟨(ha.x i hi).sd, Set.ext (haT.pinX.xs i hi).2.2⟩
  have key := GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (pk W).ψ haT.pinX.std _ _ ((B.primes X).vT u) (B.primes X).vGs a.n _ hinj hmem
    (GlobalTheory.T.type_primes_disjoint W hAll u) (fun n => (a.G n).cg j) Ξl hΞl (a.g.x j).L (a.g.x (j + 1)).L
    (hL j (by omega)).1 (hL (j + 1) hj).1 (hL j (by omega)).2 (hL (j + 1) hj).2 _ (a.g.vac j) _ hv0 hvl
    (fun e₀ he₀ => GlobalTheory.T.true_geometry_twist_reduction W hAll u a ha haT t J hJ e₀ he₀ j hj (J.ι j α) (J.ι (j + 1) γ)) e he
  rw [← ha.gpin.dG j (by exact hj) _ hvT] at key
  have hCj : C j ≠ 0 := hC j (by omega)
  convert key using 2 with z
  simp only [xiOff, map_mul, hfac z]
  field_simp

end GlobalTheory.Fam

end
