import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjF

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

/- English proof (translation)
Use `PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ x fun v => ?_` and prove the remaining obligations. Use `v.isPrime` as an intermediate fact. Establish `h2` using `(Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v hΛ x).1 (h v)`. Conclude with `(Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2`.
-/
theorem mem_of_bcP {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ x fun v => ?_
  have := v.isPrime
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v hΛ x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem baseChange_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ Λ) (p : PlF D) :
    baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ := Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Rewrite using `[LocFacts.lf_hO Zd p]`. Conclude with `Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨y, hy⟩`.
-/
theorem iE_intD (p : PlF D) {y : D.host.E} (hy : IsIntegral ℤ y) : (D.s.atP p).ιE y ∈ (Zd.M p).L.O := by
  rw [LocFacts.lf_hO Zd p]
  exact Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨y, hy⟩

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc y fun p => by rw [← LocFacts.lf_hO Zd p]; exact h p`.
-/
theorem int_of_loc {y : D.host.E} (h : ∀ p, (D.s.atP p).ιE y ∈ (Zd.M p).L.O) : IsIntegral ℤ y :=
  Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc y fun p => by rw [← LocFacts.lf_hO Zd p]; exact h p

/- English proof (translation)
The claim follows from `baseChangeAt_form Zd.M p (Zd.hcj p) x y`.
-/
theorem localForm_baseChange (p : PlF D) (x y : (VS D).V) :
    (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
  baseChangeAt_form Zd.M p (Zd.hcj p) x y

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem h_eq (p : PlF D) : (locH Zd p).h = LocFacts₂ Zd.M p := rfl

/- English proof (translation)
Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Use `int_of_loc Zd fun p => ?_` and prove the remaining obligations. Rewrite using `[← localForm_baseChange]`.

Conclude with `((hloc p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) (baseChange₂ D p y) (baseChange_mem_localLattice Zd hy p)`. Introduce `h`. Use `mem_of_bcP Zd hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_` and prove the remaining obligations. Rewrite using `[h_eq]`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨y, hy, rfl⟩` from `hw`. Rewrite using `[← h_eq, localForm_baseChange]`. Conclude with `iE_intD Zd p (h y hy)`. Consider the case `zero => rw [LocFacts.localForm_zero_right]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [LocFacts.localForm_add_right]`. Conclude with `add_mem ha hb`. Consider the case `smul o w _ hw`. Express the relevant statement in the definitionally equal form `LocFacts₂ Zd.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _`.

Rewrite using `[LocFacts.localForm_smul_right]`. Conclude with `mul_mem (LocFacts.lf_cjM_mem Zd p _ o.2) hw`.
-/
theorem sd_of_loc {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hloc : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ)) : BwdNA.SD (VS D) Λ := by
  intro x
  constructor
  · intro hx y hy
    refine int_of_loc Zd fun p => ?_
    rw [← localForm_baseChange]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) (baseChange₂ D p y) (baseChange_mem_localLattice Zd hy p)
  · intro h
    refine mem_of_bcP Zd hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    rw [h_eq]
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← h_eq, localForm_baseChange]
      exact iE_intD Zd p (h y hy)
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Zd.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Zd p _ o.2) hw

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tf (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (a : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f a = (TermLoc.sgnP D p a * frFac Zd.δ p a) • baseChange₂ D p (frame (lf D F0) a) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tLam (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) : (tLoc Zd p γ).abelian₂ = lattice₂ D Zd.M p γ.lam := rfl

/- English proof (translation)
Unfold `TermLoc.sgnP`. Use `split`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem sgnP_last (p : PlF D) : TermLoc.sgnP D p (Fin.last D.R.rS) = 1 := by
  unfold TermLoc.sgnP
  split
  · simp
  · rfl

/- English proof (translation)
Unfold `frFac`. Simplify using the standard rewrite rules.
-/
theorem frFac_last' (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

/- English proof (translation)
Rewrite using `[tf, sgnP_last, frFac_last', one_mul, one_smul]`. Use `congr 1`. Simplify using `[frame, FlagG.fvec]`.
-/
theorem tf_last (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) :
    (tLoc Zd p γ).f (Fin.last D.R.rS) = baseChange₂ D p F0.z := by
  rw [tf, sgnP_last, frFac_last', one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_cs (i : Fin D.R.rS) : frame (lf D F0) i.castSucc = F0.e i := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Establish `hs : IsUnit (TermLoc.sgnP D p a)` using `⟨⟨TermLoc.sgnP D p a, TermLoc.sgnP D p a, TermLoc.localSign_sq p a, TermLoc.localSign_sq p a⟩, rfl⟩`. Use `hs.mul ?_` and prove the remaining obligations. Distinguish the cases in `h : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ (D.R.rS - a.val))`. Take `⟨w, hw⟩` from `h`. Unfold `frFac`.

Rewrite using `[← hw, Ring.inverse_unit]`. Conclude with `Units.isUnit _`. It suffices to derive a contradiction. Establish `h0 : frFac Zd.δ p a = 0` using `by unfold frFac; exact Ring.inverse_non_unit _ h`. Establish `hne` using `hfr.1.2.1.ne_zero a`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[tf, h0, mul_zero, zero_smul]`.
-/
theorem unit_of_frame (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {L : Submodule (Zd.M p).L.O (Vp D p)}
    {T : (D.s.atP p).Fp} (hfr : (locH Zd p).IsFrame L D.R.rS (tLoc Zd p γ).f T) (a : Fin (D.R.rS + 1)) :
    IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := by
  have hs : IsUnit (TermLoc.sgnP D p a) := ⟨⟨TermLoc.sgnP D p a, TermLoc.sgnP D p a, TermLoc.localSign_sq p a, TermLoc.localSign_sq p a⟩, rfl⟩
  refine hs.mul ?_
  by_cases h : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
      (D.R.rS - a.val))
  · obtain ⟨w, hw⟩ := h
    unfold frFac
    rw [← hw, Ring.inverse_unit]
    exact Units.isUnit _
  · exfalso
    have h0 : frFac Zd.δ p a = 0 := by unfold frFac; exact Ring.inverse_non_unit _ h
    have hne := hfr.1.2.1.ne_zero a
    apply hne
    rw [tf, h0, mul_zero, zero_smul]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
