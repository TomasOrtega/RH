import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ProperOne : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K →
      ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • Y0 X u' ∈ K → g ∈ C

def InvNbhd : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ N ∈ 𝓝 (1 : MfI X), ∃ Nc : Set (MfI X), IsCompact Nc ∧ ∀ b ∈ N, ∃ c ∈ Nc, c * b = 1

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem rmulT_rmulT {D : D7} (X : HidaSetting D) (b c : MfI X) (Y : TupI X) :
    rmulT X c (rmulT X b Y) = rmulT X (b * c) Y := by
  funext a i
  simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (rmulT X b Y a)) = rmulT X b (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X …`. Use function extensionality and compare the values at `a i`. Simplify using `only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem smul_rmulT {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (b : MfI X)
    (Y : TupI X) : g • rmulT X b Y = rmulT X b (g • Y) := by
  change (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (rmulT X b Y a)) =
    rmulT X b (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (Y a))
  funext a i
  simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `fd_of X`. Use `continuous_pi fun a => continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [rmulT]`. Conclude with `continuous_finsetSum _ fun c _ => ((continuous_apply_apply c a).comp continuous_fst).mul ((continuous_apply_apply c i).comp continuous_snd)`.
-/
theorem continuous_right_mul_tuple {D : D7} (X : HidaSetting D) :
    Continuous (fun p : MfI X × TupI X => rmulT X p.1 p.2) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply_apply c a).comp continuous_fst).mul ((continuous_apply_apply c i).comp continuous_snd)

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hH K hK _`. Take `⟨N, hN, Nc, hNc, hNi⟩` from `hI X`. Establish `hK' : IsCompact ((fun p : MfI X × TupI X => rmulT X p.1 p.2) '' (Nc ×ˢ K))` using `(hNc.prod hK).image (continuous_right_mul_tuple X)`. Take `⟨C, hC, hgC⟩` from `h1 X u' ψ hT μinf νinf fibInf hH _ hK'`. Use `⟨N, hN, C, hC, fun b hb g hg => hgC g ?_⟩` and prove the remaining obligations.

Take `⟨c, hc, hcb⟩` from `hNi b hb`. Establish `hbc : b * c = 1` using `mul_eq_one_comm.1 hcb`. Use `⟨(c, g • rmulT X b (Y0 X u')), ⟨hc, hg⟩, ?_⟩` and prove the remaining obligations. Use `show rmulT X c (g • rmulT X b (Y0 X u')) = g • Y0 X u'`. Rewrite using `[smul_rmulT, rmulT_rmulT, hbc, rmulT_one]`.
-/
theorem properOrb_of_one (h1 : ProperOne) (hI : InvNbhd) : ProperOrb := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK _
  obtain ⟨N, hN, Nc, hNc, hNi⟩ := hI X
  have hK' : IsCompact ((fun p : MfI X × TupI X => rmulT X p.1 p.2) '' (Nc ×ˢ K)) :=
    (hNc.prod hK).image (continuous_right_mul_tuple X)
  obtain ⟨C, hC, hgC⟩ := h1 X u' ψ hT μinf νinf fibInf hH _ hK'
  refine ⟨N, hN, C, hC, fun b hb g hg => hgC g ?_⟩
  obtain ⟨c, hc, hcb⟩ := hNi b hb
  have hbc : b * c = 1 := mul_eq_one_comm.1 hcb
  refine ⟨(c, g • rmulT X b (Y0 X u')), ⟨hc, hg⟩, ?_⟩
  show rmulT X c (g • rmulT X b (Y0 X u')) = g • Y0 X u'
  rw [smul_rmulT, rmulT_rmulT, hbc, rmulT_one]

/- English proof (translation)
The claim follows from `constTest_of_polar_prop hP (properOrb_of_one h1 hI)`.
-/
theorem constTest_of_polar_one (hP : PolarLoc) (h1 : ProperOne) (hI : InvNbhd) : ConstTest :=
  constTest_of_polar_prop hP (properOrb_of_one h1 hI)

end PI.AprimeInfW
