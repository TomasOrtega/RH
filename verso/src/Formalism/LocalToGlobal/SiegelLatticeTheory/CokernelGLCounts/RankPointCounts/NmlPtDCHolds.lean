import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemXflagMapLF

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

/- English proof (translation)
Take `⟨F', ⟨hP, hmk⟩, hGv, hcell⟩` from `at_ptOf Y t hG`. Use `⟨F', hGv, hcell, ?_⟩` and prove the remaining obligations. Establish `hrow` using `(Y.rowsOK u).1 t.lam t.mem`. Establish `hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨F', hP⟩` using `hmk.symm`. Establish `hrel` using `(Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow _ _).1 hmk'`.

Take `⟨n, hn, m, hm, hfr, -⟩` from `hrel`. Use `⟨n, NLam_SRat hn, t.lin⁻¹ * m * t.lin, NLam_transport Y t hm, fun a => ?_⟩` and prove the remaining obligations. Use `hfr a` as an intermediate fact. Use `show F'.fl.fvec a = n (t.lin (t.lin.symm (m (t.lin ((X.Fu u').fvec a)))))`. Rewrite using `[LinearEquiv.apply_symm_apply]`.

Rewrite using `[← frame_fvec Y t a]`. Conclude with `this`.
-/
theorem rep_at_pt (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    ∃ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), Gval (lf D (X.Fu u)) F' ≠ 0 ∧
      IsInCell (ZhatOM (Zhat (X.Fu u) F'.fl)) (Formalism.L2.SG.PairVal.ptOf t.toTerm) ∧
      ∃ n ∈ SRat (lf D (X.Fu u)), ∃ m ∈ SRat (lf D (X.Fu u')),
        ∀ a, F'.fl.fvec a = (n * t.lin * m) ((X.Fu u').fvec a) := by
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hcell⟩ := at_ptOf Y t hG
  refine ⟨F', hGv, hcell, ?_⟩
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨F', hP⟩ := hmk.symm
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow _ _).1 hmk'
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hrel
  refine ⟨n, NLam_SRat hn, t.lin⁻¹ * m * t.lin, NLam_transport Y t hm, fun a => ?_⟩
  have := hfr a
  show F'.fl.fvec a = n (t.lin (t.lin.symm (m (t.lin ((X.Fu u').fvec a)))))
  rw [LinearEquiv.apply_symm_apply]
  rw [← frame_fvec Y t a]
  exact this

/- English proof (translation)
Establish `hN2 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t2)` using `by rw [← hp]; exact hN1`. Take `⟨F1, hG1, hc1, n1, hn1, m1, hm1, hF1⟩` from `rep_at_pt Y t1 hN1`. Take `⟨F2, hG2, hc2, n2, hn2, m2, hm2, hF2⟩` from `rep_at_pt Y t2 hN2`. Establish `hw : Formalism.L2.SG.PairVal.ptOf t1.toTerm = Formalism.L2.SG.PairVal.ptOf t2.toTerm` using `toPts_inj _ _ hp`. Rewrite `hc1` using `[hw]`.

Take `⟨g, hg, ⟨M, hM, hgM⟩, U, hU, hgU⟩` from `same_cell (X.Fu u) F1.fl F2.fl hG1 hG2 _ hc1 hc2`. Establish `hgs : g.symm ∈ SRat (lf D (X.Fu u))`. Take `⟨hf, hz⟩` from `flag_of_upUni (X.Fu u) (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V) M hM hgM`. Conclude with `⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hg, hf, hz⟩`. Establish `hgS : g ∈ SRat (lf D (X.Fu u))` using `by simpa using SRat_inv (lf D (X.Fu u)) hgs`.

Use `set ρ1 := n1 * t1.lin * m1 with hρ1`. Use `set ρ2 := n2 * t2.lin * m2 with hρ2`. Use `set s'' := ρ2⁻¹ * g * ρ1 with hs''`. Establish `hs''v : ∀ b, s''.symm ((X.Fu u').fvec b) = ∑ c, U c b • (X.Fu u').fvec c`. Introduce `b`.

Apply `s''.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply, hs'']`. Use `show (X.Fu u').fvec b = ρ2.symm (g (ρ1 (∑ c, U c b • (X.Fu u').fvec c)))`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`.

Establish `e1 : ∀ c, ρ1 ((X.Fu u').fvec c) = F1.fl.fvec c` using `fun c => (hF1 c).symm`. Simplify using `only [e1]`. Rewrite using `[hgU b, hF2 b]`. Simplify using the standard rewrite rules. Establish `hs''S : s'' ∈ SRat (lf D (X.Fu u'))`.

Establish `hs''i : s'' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT`. Use `(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem ?_) hg) ?_` and prove the remaining obligations. Conclude with `(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn2.1 t2.rep.2.2.1) hm2.1`. Conclude with `(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn1.1 t1.rep.2.2.1) hm1.1`. Take `⟨hf, hz⟩` from `flag_of_upUni (X.Fu u') (s''.symm : (VS D).V →ₗ[D.host.E] (VS D).V) U hU hs''v`.

Establish `: s''.symm ∈ SRat (lf D (X.Fu u'))` using `⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hs''i, hf, hz⟩`. Simplify using `using SRat_inv (lf D (X.Fu u')) this`. Use `⟨n2⁻¹ * g * n1, SRat_mul _ (SRat_mul _ (SRat_inv _ hn2) hgS) hn1, m1 * s''⁻¹ * m2⁻¹, SRat_mul _ (SRat_mul _ hm1 (SRat_inv _ hs''S)) (SRat_inv _ hm2), ?_⟩` and prove the remaining obligations. Establish `e : ρ2 = g * ρ1 * s''⁻¹` using `by rw [hs'']; group`. Rewrite `e` using `[hρ2, hρ1]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem ptdc_core (t1 t2 : TauC Y u u') (hN1 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t1))
    (hp : ptPN t1 = ptPN t2) :
    ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s' := by
  have hN2 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t2) := by rw [← hp]; exact hN1
  obtain ⟨F1, hG1, hc1, n1, hn1, m1, hm1, hF1⟩ := rep_at_pt Y t1 hN1
  obtain ⟨F2, hG2, hc2, n2, hn2, m2, hm2, hF2⟩ := rep_at_pt Y t2 hN2
  have hw : Formalism.L2.SG.PairVal.ptOf t1.toTerm = Formalism.L2.SG.PairVal.ptOf t2.toTerm := toPts_inj _ _ hp
  rw [hw] at hc1
  obtain ⟨g, hg, ⟨M, hM, hgM⟩, U, hU, hgU⟩ := same_cell (X.Fu u) F1.fl F2.fl hG1 hG2 _ hc1 hc2

  have hgs : g.symm ∈ SRat (lf D (X.Fu u)) := by
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u) (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V) M hM hgM
    exact ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hg, hf, hz⟩
  have hgS : g ∈ SRat (lf D (X.Fu u)) := by simpa using SRat_inv (lf D (X.Fu u)) hgs
  set ρ1 := n1 * t1.lin * m1 with hρ1
  set ρ2 := n2 * t2.lin * m2 with hρ2
  set s'' := ρ2⁻¹ * g * ρ1 with hs''
  have hs''v : ∀ b, s''.symm ((X.Fu u').fvec b) = ∑ c, U c b • (X.Fu u').fvec c := by
    intro b
    apply s''.injective
    rw [LinearEquiv.apply_symm_apply, hs'']
    show (X.Fu u').fvec b = ρ2.symm (g (ρ1 (∑ c, U c b • (X.Fu u').fvec c)))
    rw [map_sum]
    simp only [map_smul]
    have e1 : ∀ c, ρ1 ((X.Fu u').fvec c) = F1.fl.fvec c := fun c => (hF1 c).symm
    simp only [e1]
    rw [hgU b, hF2 b]
    simp
  have hs''S : s'' ∈ SRat (lf D (X.Fu u')) := by
    have hs''i : s'' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
      refine (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem ?_) hg) ?_
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn2.1 t2.rep.2.2.1) hm2.1
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn1.1 t1.rep.2.2.1) hm1.1
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u') (s''.symm : (VS D).V →ₗ[D.host.E] (VS D).V) U hU hs''v
    have : s''.symm ∈ SRat (lf D (X.Fu u')) := ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hs''i, hf, hz⟩
    simpa using SRat_inv (lf D (X.Fu u')) this
  refine ⟨n2⁻¹ * g * n1, SRat_mul _ (SRat_mul _ (SRat_inv _ hn2) hgS) hn1,
    m1 * s''⁻¹ * m2⁻¹, SRat_mul _ (SRat_mul _ hm1 (SRat_inv _ hs''S)) (SRat_inv _ hm2), ?_⟩
  have e : ρ2 = g * ρ1 * s''⁻¹ := by rw [hs'']; group
  rw [hρ2, hρ1] at e
  calc t2.lin = n2⁻¹ * (n2 * t2.lin * m2) * m2⁻¹ := by group
    _ = n2⁻¹ * (g * (n1 * t1.lin * m1) * s''⁻¹) * m2⁻¹ := by rw [e]
    _ = n2⁻¹ * g * n1 * t1.lin * (m1 * s''⁻¹ * m2⁻¹) := by group

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Use `⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ γ hγ t1 t2 _ _ h1 h2 _ => ?_⟩` and prove the remaining obligations. Substitute `h1` using the available equality. Conclude with `ptdc_core Y t1 t2 hγ h2.symm`.
-/
theorem NmlPtDC_holds : NmlPtDC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ γ hγ t1 t2 _ _ h1 h2 _ => ?_⟩
  subst h1
  exact ptdc_core Y t1 t2 hγ h2.symm

/- English proof (translation)
The claim follows from `nmlSep_of NmlPtDC_holds normalsLemmaG3_holds`.
-/
theorem NmlSep_holds : NmlSep := nmlSep_of NmlPtDC_holds normalsLemmaG3_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
