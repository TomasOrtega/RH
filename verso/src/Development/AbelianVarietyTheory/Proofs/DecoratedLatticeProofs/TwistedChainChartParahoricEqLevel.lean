import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopologicalIsoParahoricChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartLevel

variable {D : D7}

open ValuativeRel in
/- English proof (translation)
Establish `h : valuation (Fv D.host.F v) 1 ≤ valuation (Fv D.host.F v) x ↔ Valued.v (1 : Fv D.host.F v) ≤ Valued.v x` using `by haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Rewrite using `[← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)), Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]`. Rewrite `h` using `[map_one, map_one]`. Rewrite using `[← not_le, ← not_le, h]`.
-/
theorem val_lt_one_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h : valuation (Fv D.host.F v) 1 ≤ valuation (Fv D.host.F v) x ↔ Valued.v (1 : Fv D.host.F v) ≤ Valued.v x := by
    haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨⟨r, -, hr0, -, hN⟩, -⟩` from `GlobalTheory.PlaceRed.red_dict D v φ PP hφ`. Take `⟨y, hy⟩` from `hS`. Rewrite using `[← hy, redFn_frGL]`. Take `⟨h, hrd⟩` from `hN _ (y.val a b).2`. Establish `e1 : (Formalism.UG.bc (resS D.host.F PP) y).val a b = resS D.host.F PP (y.val a b)` using `rfl`.

Rewrite using `[e1, ← hrd, hr0]`. Establish `hi : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V g * β`. Rewrite using `[← hy]`. Simplify using `[frGL, MulAut.conj_apply]`. Use `group`.

Establish `hx : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Lev.finE V g) = Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V g)`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Use `show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Lev.finE V g).val i j) = rdA φ ((Formalism.L2.Theta.matHom V g).val i j)`. Conclude with `GlobalTheory.SplitProjChart.rdE_toEAf φ _`. Establish `hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (β⁻¹ * Lev.finE V g * β) = grpCo φ V (frCo φ β) g`.

Rewrite using `[MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hx]`. Both sides reduce to the same expression. Establish `key : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = (grpCo φ V (frCo φ β) g).val a b`. Rewrite using `[← hm, ← hi]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1 ↔ _`. Rewrite using `[key]`.
-/
theorem redFn_entry_eq_zero_iff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V}
    (hS : Lev.finE V g ∈ St β) {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : SplitProj D v} {PP : Pl D.host.E}
    (hφ : IsProjAt φ PP) (a b : Fin V.rank) :
    (redFn β PP (Lev.finE V g)).val a b = 0 ↔ Valued.v ((grpCo φ V (frCo φ β) g).val a b) < 1 := by
  obtain ⟨⟨r, -, hr0, -, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  obtain ⟨y, hy⟩ := hS
  rw [← hy, redFn_frGL]
  obtain ⟨h, hrd⟩ := hN _ (y.val a b).2
  have e1 : (Formalism.UG.bc (resS D.host.F PP) y).val a b = resS D.host.F PP (y.val a b) := rfl
  rw [e1, ← hrd, hr0]
  have hi : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V g * β := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  have hx : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Lev.finE V g) =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V g) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Lev.finE V g).val i j) = rdA φ ((Formalism.L2.Theta.matHom V g).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (β⁻¹ * Lev.finE V g * β) = grpCo φ V (frCo φ β) g := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hx]
    rfl
  have key : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (grpCo φ V (frCo φ β) g).val a b := by
    rw [← hm, ← hi]
    rfl
  change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1 ↔ _
  rw [key]

end GlobalTheory.ChartLevel

namespace GlobalTheory.ChartLevel

variable {D : D7}

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Establish `e : ε (.inl ⟨_, h⟩) = ε (.inr i)` using `Fin.ext (hε _)`. Conclude with `Sum.inl_ne_inr (ε.injective e)`.
-/
theorem eps_inr_ge {r n : ℕ} {B : Type} (ε : Fin r ⊕ B ≃ Fin n) (hε : ∀ i, (ε (.inl i) : ℕ) = i) (i : B) :
    r ≤ (ε (.inr i) : ℕ) := by
  by_contra h
  rw [not_le] at h
  have e : ε (.inl ⟨_, h⟩) = ε (.inr i) := Fin.ext (hε _)
  exact Sum.inl_ne_inr (ε.injective e)

/- English proof (translation)
Unfold `blk2`. Apply the tactic sequence `by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb] <;> omega`.
-/
theorem twoBlockIndex_lt_iff_lowerLeft {r n : ℕ} (a b : Fin n) : blk2 r b < blk2 r a ↔ (b : ℕ) < r ∧ r ≤ (a : ℕ) := by
  unfold blk2
  by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb] <;> omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `h _ _ ((twoBlockIndex_lt_iff_lowerLeft _ _).2 ⟨?_, eps_inr_ge ε hε i⟩)` and prove the remaining obligations. Rewrite using `[hε]`. Conclude with `j.2`.

Introduce `h a b hab`. Rewrite `hab` using `[twoBlockIndex_lt_iff_lowerLeft]`. Take `⟨p, rfl⟩` from `ε.surjective a`. Take `⟨q, rfl⟩` from `ε.surjective b`. Break down `p with p | p` into its components or cases.

It suffices to derive a contradiction. Rewrite `hab` using `[hε]`. Use `p.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Break down `q with q | q` into its components or cases.

Conclude with `h p q`. It suffices to derive a contradiction. Use `eps_inr_ge ε hε q` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem lower_iff {r n : ℕ} {B K : Type} (ε : Fin r ⊕ B ≃ Fin n) (hε : ∀ i, (ε (.inl i) : ℕ) = i) (M : Fin n → Fin n → K)
    (P : K → Prop) : (∀ a b : Fin n, blk2 r b < blk2 r a → P (M a b)) ↔ ∀ i j, P (M (ε (.inr i)) (ε (.inl j))) := by
  constructor
  · intro h i j
    refine h _ _ ((twoBlockIndex_lt_iff_lowerLeft _ _).2 ⟨?_, eps_inr_ge ε hε i⟩)
    rw [hε]; exact j.2
  · intro h a b hab
    rw [twoBlockIndex_lt_iff_lowerLeft] at hab
    obtain ⟨p, rfl⟩ := ε.surjective a
    obtain ⟨q, rfl⟩ := ε.surjective b
    rcases p with p | p
    · exfalso; rw [hε] at hab; have := p.2; omega
    rcases q with q | q
    · exact h p q
    · exfalso; have := eps_inr_ge ε hε q; omega

end GlobalTheory.ChartLevel

open GlobalTheory.ChartLevel in

/- English proof (translation)
Introduce `D c w hw j hj s hs PP hPP v φ hφ ι hι y`. Take `⟨hr, hL, hfl⟩` from `hs`. Establish `hsd : IsSelfDualC s.V s.Λ` using `hfl.selfDual`. Establish `hfr : IsFrame s.β s.Λ` using `hfl.frame`. Take `⟨e, he⟩` from `GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hsd hfr hι`.

Establish `hstab` using `GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer D s j v φ ι hsd hfr hι e he y`. Establish `hv : v = PP.under (𝓞 D.host.F)` using `(GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1`. Take `⟨ε, hε, hch⟩` from `hι`. Establish `hSt : Lev.finE s.V (ι y) ∈ St s.β ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _`. Rewrite using `[GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr, he y, ← hstab]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h v` as an intermediate fact. Rewrite `this` using `[GlobalTheory.AdelicU.proj_emb_self]`. Then use the resulting hypothesis. Introduce `h u`.

Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[GlobalTheory.AdelicU.proj_emb_self]`. Conclude with `h`. Rewrite using `[GlobalTheory.AdelicU.proj_emb_ne _ _ hu]`.

Conclude with `one_mem _`. Establish `hPc : PP ∈ c.Pg` using `by classical`. Rewrite using `[hw.union]`. Conclude with `Finset.mem_union_right _ hPP`. Establish `hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → Lev.finE s.V (ι y) ∈ St s.β → redFn s.β PP' (Lev.finE s.V (ι y)) = 1`.

Introduce `PP' hP' hne hS`. Use `GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_` and prove the remaining obligations. Establish `hu : PP'.under (𝓞 D.host.F) ≠ v`. Introduce `h`. Conclude with `hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))`.

Rewrite using `[he y]`. Conclude with `GlobalTheory.AdelicU.proj_emb_ne _ _ hu _`. Establish `hred : Lev.finE s.V (ι y) ∈ St s.β → (redFn s.β PP (Lev.finE s.V (ι y)) ∈ blockTri (blk2 D.R.r) ↔ ∀ i j', ValuativeRel.valuation (Fv D.host.F v) (y.1 (.inr i) (.inl j')) < 1)`. Introduce `hS`. Rewrite using `[mem_blockTri]`.

Establish `h1 : ∀ a b, (redFn s.β PP (Lev.finE s.V (ι y))).val a b = 0 ↔ Valued.v ((grpCo φ s.V (frCo φ s.β) (ι y)).val a b) < 1` using `redFn_entry_eq_zero_iff hS hφ`. Simplify using `only [h1]`. Rewrite using `[lower_iff ε hε (fun a b => (grpCo φ s.V (frCo φ s.β) (ι y)).val a b) (fun x => Valued.v x < 1)]`. Establish `hy : ∀ p q, (grpCo φ s.V (frCo φ s.β) (ι y)).val (ε p) (ε q) = y.1 p q` using `fun p q => by`. Use `congrFun (congrFun (hch y).2 p) q` as an intermediate fact.

Simplify using `using this`. Simplify using `only [hy, val_lt_one_iff]`. Establish `hG : ι y ∈ GfC s.V`. Rewrite using `[he y]`. Conclude with `GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC _ _ _`.

Establish `hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg` using `by classical`. Introduce `PP' h`. Rewrite using `[hw.union]`. Conclude with `Finset.mem_union.2 h`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, ← hSt, hL, Lev.levG, Lev.mem_levA, mem_lev, mem_parLev]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, ⟨-, hS, -, hQ⟩, -⟩`. Conclude with `⟨hS, (hred hS).1 (hQ PP hPP)⟩`. Introduce and unpack `⟨hS, hlow⟩`. Establish `hPg : ∀ PP' ∈ w.Pg, redFn s.β PP' (Lev.finE s.V (ι y)) = 1`.

Introduce `PP' hP'`. Use `hone PP' (hsub _ (Or.inl hP')) ?_ hS` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `Finset.disjoint_left.1 hw.disj hP' hPP`. Use `⟨hG, ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hS, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `PP' hP'`. Rewrite using `[hPg PP' hP']`. Conclude with `one_mem _`. Introduce `PP' hP'`. Distinguish the cases in `e : PP' = PP`.

Substitute `e` using the available equality. Conclude with `(hred hS).2 hlow`. Rewrite using `[hone PP' (hsub _ (Or.inr hP')) e hS]`. Conclude with `one_mem _`. Establish `h1 : rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B) (Lev.finE s.V (ι y)) = 1`.

Use function extensionality and compare the values at `PP'`. Use `show upperLeftBlock hr (redFn s.β PP'.1 (Lev.finE s.V (ι y))) = 1`. Rewrite using `[hPg PP'.1 PP'.2]`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`. Rewrite using `[h1]`.

Conclude with `one_mem _`.
-/
theorem GlobalTheory.chart_level_iff : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι y
  obtain ⟨hr, hL, hfl⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hfr : IsFrame s.β s.Λ := hfl.frame
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hsd hfr hι
  have hstab := GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer D s j v φ ι hsd hfr hι e he y
  have hv : v = PP.under (𝓞 D.host.F) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  have hSt : Lev.finE s.V (ι y) ∈ St s.β ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr, he y, ← hstab]
    constructor
    · intro h
      have := h v
      rwa [GlobalTheory.AdelicU.proj_emb_self] at this
    · intro h u
      by_cases hu : u = v
      · subst hu
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact h
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ hu]
        exact one_mem _
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → Lev.finE s.V (ι y) ∈ St s.β →
      redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne hS
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : PP'.under (𝓞 D.host.F) ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hred : Lev.finE s.V (ι y) ∈ St s.β → (redFn s.β PP (Lev.finE s.V (ι y)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ i j', ValuativeRel.valuation (Fv D.host.F v) (y.1 (.inr i) (.inl j')) < 1) := by
    intro hS
    rw [mem_blockTri]
    have h1 : ∀ a b, (redFn s.β PP (Lev.finE s.V (ι y))).val a b = 0 ↔
        Valued.v ((grpCo φ s.V (frCo φ s.β) (ι y)).val a b) < 1 := redFn_entry_eq_zero_iff hS hφ
    simp only [h1]
    rw [lower_iff ε hε (fun a b => (grpCo φ s.V (frCo φ s.β) (ι y)).val a b) (fun x => Valued.v x < 1)]
    have hy : ∀ p q, (grpCo φ s.V (frCo φ s.β) (ι y)).val (ε p) (ε q) = y.1 p q := fun p q => by
      have := congrFun (congrFun (hch y).2 p) q
      simpa using this
    simp only [hy, val_lt_one_iff]
  have hG : ι y ∈ GfC s.V := by
    rw [he y]; exact GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC _ _ _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, ← hSt, hL, Lev.levG, Lev.mem_levA, mem_lev, mem_parLev]
  constructor
  · rintro ⟨-, ⟨-, hS, -, hQ⟩, -⟩
    exact ⟨hS, (hred hS).1 (hQ PP hPP)⟩
  · rintro ⟨hS, hlow⟩
    have hPg : ∀ PP' ∈ w.Pg, redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
      intro PP' hP'
      refine hone PP' (hsub _ (Or.inl hP')) ?_ hS
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    refine ⟨hG, ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hS, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPg PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · subst e
        exact (hred hS).2 hlow
      · rw [hone PP' (hsub _ (Or.inr hP')) e hS]
        exact one_mem _
    · have h1 : rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B)
          (Lev.finE s.V (ι y)) = 1 := by
        funext PP'
        show upperLeftBlock hr (redFn s.β PP'.1 (Lev.finE s.V (ι y))) = 1
        rw [hPg PP'.1 PP'.2]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact one_mem _
