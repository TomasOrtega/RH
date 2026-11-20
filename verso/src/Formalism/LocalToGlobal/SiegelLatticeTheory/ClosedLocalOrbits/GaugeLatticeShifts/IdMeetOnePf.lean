import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpInhab

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Gen

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Take `⟨n, hn, n', hn', hq⟩` from `h`. Set `H` to `NLamSub Λ (lf D F0)`. Rewrite using `[hq]`. Prove the components needed by the constructor for the conclusion. Introduce `hp`.

Conclude with `H.mul_mem (H.mul_mem hn hp) hn'`. Introduce `hq'`. Establish `e : p.1.2 = n⁻¹ * (n * p.1.2 * n') * n'⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `H.mul_mem (H.mul_mem (H.inv_mem hn) hq') (H.inv_mem hn')`.
-/
theorem nlam_iff_of_rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u F0 F0 Λ Λ}
    (h : GRel X u u F0 F0 Λ Λ p q) : p.1.2 ∈ NLam Λ (lf D F0) ↔ q.1.2 ∈ NLam Λ (lf D F0) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  let H := NLamSub Λ (lf D F0)
  rw [hq]
  constructor
  · intro hp
    exact H.mul_mem (H.mul_mem hn hp) hn'
  · intro hq'
    have e : p.1.2 = n⁻¹ * (n * p.1.2 * n') * n'⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hn) hq') (H.inv_mem hn')

/- English proof (translation)
Establish `key : ∀ a b : GCar X u u F0 F0 Λ Λ, Relation.EqvGen (GRel X u u F0 F0 Λ Λ) a b → (a.1.2 ∈ NLam Λ (lf D F0) ↔ b.1.2 ∈ NLam Λ (lf D F0))`. Introduce `a b hab`. Proceed by induction on `hab with`. Consider the case `rel a b h => exact nlam_iff_of_rel h`. Consider the case `refl a => exact Iff.rfl`.

Consider the case `symm a b _ ih => exact ih.symm`. Consider the case `trans a b c _ _ ih1 ih2 => exact ih1.trans ih2`. Conclude with `key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u F0 F0 Λ Λ) p)))`.
-/
theorem nlam_out_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (p : GCar X u u F0 F0 Λ Λ) :
    (Quot.out (Quot.mk (GRel X u u F0 F0 Λ Λ) p)).1.2 ∈ NLam Λ (lf D F0) ↔ p.1.2 ∈ NLam Λ (lf D F0) := by
  have key : ∀ a b : GCar X u u F0 F0 Λ Λ, Relation.EqvGen (GRel X u u F0 F0 Λ Λ) a b →
      (a.1.2 ∈ NLam Λ (lf D F0) ↔ b.1.2 ∈ NLam Λ (lf D F0)) := by
    intro a b hab
    induction hab with
    | rel a b h => exact nlam_iff_of_rel h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u F0 F0 Λ Λ) p)))

/- English proof (translation)
Unfold `GTerm.isId Formalism.L2.SG.FourParts.termIsId Formalism.L2.SG.FourParts.IsIdT`. Use `⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.SG.FourParts.IsIdF`. Establish `hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`. Establish `hf : mapLF t.lin (lf D F0) = _` using `dif_pos hi`.

Rewrite using `[show t.frame = mapLF t.lin (lf D F0) from rfl, hf]`. Use `⟨t.lin, h, fun a => rfl, ?_⟩` and prove the remaining obligations. Establish `hz : (mapFlag t.lin hi (lf D F0).fl).z = t.lin (lf D F0).fl.z` using `rfl`. Use `show t.lin (lf D F0).fl.z - (mapFlag t.lin hi (lf D F0).fl).z ∈ _`. Rewrite using `[hz, sub_self]`.

Conclude with `zero_mem _`.
-/
theorem isId_of_lin {t : GTerm X u u F0 F0 what₂ what₂} (h : t.lin ∈ NLam t.lam (lf D F0)) : t.isId := by
  unfold GTerm.isId Formalism.L2.SG.FourParts.termIsId Formalism.L2.SG.FourParts.IsIdT
  refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
  unfold Formalism.L2.SG.FourParts.IsIdF
  have hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hf : mapLF t.lin (lf D F0) = _ := dif_pos hi
  rw [show t.frame = mapLF t.lin (lf D F0) from rfl, hf]
  refine ⟨t.lin, h, fun a => rfl, ?_⟩
  have hz : (mapFlag t.lin hi (lf D F0).fl).z = t.lin (lf D F0).fl.z := rfl
  show t.lin (lf D F0).fl.z - (mapFlag t.lin hi (lf D F0).fl).z ∈ _
  rw [hz, sub_self]
  exact zero_mem _

end Gen

/- English proof (translation)
Introduce `D X Y u hneat _`. Use `⟨fun ρ ρ' t hid hm => (hK D X Y u hneat ρ ρ' t hid hm).1, ?_, ?_⟩` and prove the remaining obligations. Introduce `ρ t t' hid hid' hm hm'`. Establish `h1` using `(hK D X Y u hneat ρ ρ t hid hm).2`. Establish `h2` using `(hK D X Y u hneat ρ ρ t' hid' hm').2`.

Take `⟨hl, hl', -⟩` from `hm`. Take `⟨hr, hr', -⟩` from `hm'`. Take `⟨lam, mem, lam', mem', cls⟩` from `t`. Take `⟨lam₂, mem₂, lam₂', mem₂', cls₂⟩` from `t'`. Simplify using `only at hl hl' hr hr'`.

Substitute `hl hl' hr hr'` using the available equality. Establish `h1' : (Quot.out cls).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))` using `h1`. Establish `h2' : (Quot.out cls₂).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))` using `h2`. Establish `hrel : GRel X u u (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) (Quot.out cls) (Quot.out cls₂)` using `⟨(Quot.out cls₂).1.2 * ((Quot.out cls).1.2)⁻¹, Subgroup.mul_mem _ h2' (Subgroup.inv_mem _ h1'), 1, Formalism.L2.SG.Pf.nlam_one _ _, by group⟩`. Establish `hs` using `Quot.sound hrel`.

Establish `hc : cls = cls₂` using `(Quot.out_eq cls).symm.trans (hs.trans (Quot.out_eq cls₂))`. Substitute `hc` using the available equality. Both sides reduce to the same expression. Introduce `ρ`. Establish `hΛ` using `(Y.cs u).lam_mem ρ`.

Set `t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)` to `idGTerm X ((Y.cs u).lamOf ρ) hΛ ((Y.rowsOK u).1 _ hΛ)`. Establish `hlin : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))` using `(nlam_out_iff _).2 (Formalism.L2.SG.Pf.nlam_one _ _)`. Use `⟨t, isId_of_lin hlin, rfl, rfl, ?_⟩` and prove the remaining obligations. Conclude with `(Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin t.rep.2.1).1`.
-/
theorem idMeetOneC_of (hK : IdMeetKeyC) : IdMeetOneC := by
  intro D X Y u hneat _
  refine ⟨fun ρ ρ' t hid hm => (hK D X Y u hneat ρ ρ' t hid hm).1, ?_, ?_⟩
  · intro ρ t t' hid hid' hm hm'
    have h1 := (hK D X Y u hneat ρ ρ t hid hm).2
    have h2 := (hK D X Y u hneat ρ ρ t' hid' hm').2
    obtain ⟨hl, hl', -⟩ := hm
    obtain ⟨hr, hr', -⟩ := hm'
    obtain ⟨lam, mem, lam', mem', cls⟩ := t
    obtain ⟨lam₂, mem₂, lam₂', mem₂', cls₂⟩ := t'
    simp only at hl hl' hr hr'
    subst hl hl' hr hr'
    have h1' : (Quot.out cls).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h1
    have h2' : (Quot.out cls₂).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h2
    have hrel : GRel X u u (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) (Quot.out cls) (Quot.out cls₂) :=
      ⟨(Quot.out cls₂).1.2 * ((Quot.out cls).1.2)⁻¹,
        Subgroup.mul_mem _ h2' (Subgroup.inv_mem _ h1'), 1, Formalism.L2.SG.Pf.nlam_one _ _, by group⟩
    have hs := Quot.sound hrel
    have hc : cls = cls₂ := (Quot.out_eq cls).symm.trans (hs.trans (Quot.out_eq cls₂))
    subst hc
    rfl
  · intro ρ
    have hΛ := (Y.cs u).lam_mem ρ
    let t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) :=
      idGTerm X ((Y.cs u).lamOf ρ) hΛ ((Y.rowsOK u).1 _ hΛ)
    have hlin : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) :=
      (nlam_out_iff _).2 (Formalism.L2.SG.Pf.nlam_one _ _)
    refine ⟨t, isId_of_lin hlin, rfl, rfl, ?_⟩
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin t.rep.2.1).1

end Formalism.L2.SG.Pf.IdMeet
