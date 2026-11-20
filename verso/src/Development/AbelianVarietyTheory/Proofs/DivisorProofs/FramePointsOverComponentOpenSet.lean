import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompConstMulMemHolSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.FramesUnion

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U σ hU Z k y y' hy' hyZ`. Take `⟨hy, hZ⟩` from `hyZ`. Establish `hd : Dom (E` using `E) 0 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩`. Establish `hsec` using `hU.2.2.2.2.1 0 0 hd (GlobalTheory.FlatLine.idem Z) (GlobalTheory.CompRestr.idem_mem_sec Z) k`. Take `⟨w, hw⟩` from `GlobalTheory.CompRat.const_of_idem_on (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r ((U σ).X k)).isPreconnected hsec.1.continuousOn fun x _ => by`.

Rewrite using `[← GlobalTheory.CompRat.rdU_mul_apply', GlobalTheory.FlatLine.idem_mul_idem]`. Establish `hA : AllTest Xo c` using `(GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.test`. Use `haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)`. Establish `e1 : ∀ (g : Rul Xo c) (x : Frame ((U σ).X k).Ψ r) (h : x ∈ ((U σ).X k).dom), rdU (U σ) g k x = toC (evR Xo c g ((U σ).un k ⟨x, h⟩))` using `fun g x h => dif_pos h`. Establish `h1 : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y = 1`.

Rewrite using `[e1 _ _ hy, GlobalTheory.FlatLine.evR_idem hZ (hA _ _)]`. Both sides reduce to the same expression. Establish `h1' : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y' = 1` using `(hw y' hy').trans ((hw y hy).symm.trans h1)`. Use `⟨hy', ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Establish `hoff : LiesOff Z ((U σ).un k ⟨y', hy'⟩)`. Introduce `s hs`. Apply `hn` to reduce the goal to its premises. Introduce `s'`. Establish `: s = s'` using `Subsingleton.elim (α := PrimeSpectrum ℂ) s s'`.

Conclude with `this ▸ hs`. Establish `h0` using `GlobalTheory.FlatLine.idem_mem_suppOn Z (CAt σ) _ hoff`. Rewrite `h1'` using `[e1 _ _ hy', h0]`. Conclude with `zero_ne_one (α := ℂ) h1'`.
-/
theorem framesOn_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), IsUnf (U σ) → ∀ (Z : Comp Xo c) (k : (U σ).Comp) (y y' : Frame ((U σ).X k).Ψ r), y' ∈ ((U σ).X k).dom → (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z → (⟨k, y'⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
  intro E _ _ _ H Dw l Xo c r U σ hU Z k y y' hy' hyZ
  obtain ⟨hy, hZ⟩ := hyZ
  have hd : Dom (E := E) 0 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩
  have hsec := hU.2.2.2.2.1 0 0 hd (GlobalTheory.FlatLine.idem Z) (GlobalTheory.CompRestr.idem_mem_sec Z) k
  obtain ⟨w, hw⟩ := GlobalTheory.CompRat.const_of_idem_on
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r ((U σ).X k)).isPreconnected hsec.1.continuousOn fun x _ => by
      rw [← GlobalTheory.CompRat.rdU_mul_apply', GlobalTheory.FlatLine.idem_mul_idem]
  have hA : AllTest Xo c := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.test
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have e1 : ∀ (g : Rul Xo c) (x : Frame ((U σ).X k).Ψ r) (h : x ∈ ((U σ).X k).dom),
      rdU (U σ) g k x = toC (evR Xo c g ((U σ).un k ⟨x, h⟩)) := fun g x h => dif_pos h
  have h1 : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y = 1 := by
    rw [e1 _ _ hy, GlobalTheory.FlatLine.evR_idem hZ (hA _ _)]
    rfl
  have h1' : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y' = 1 := (hw y' hy').trans ((hw y hy).symm.trans h1)
  refine ⟨hy', ?_⟩
  by_contra hn
  have hoff : LiesOff Z ((U σ).un k ⟨y', hy'⟩) := by
    intro s hs
    apply hn
    intro s'
    have : s = s' := Subsingleton.elim (α := PrimeSpectrum ℂ) s s'
    exact this ▸ hs
  have h0 := GlobalTheory.FlatLine.idem_mem_suppOn Z (CAt σ) _ hoff
  rw [e1 _ _ hy', h0] at h1'
  exact zero_ne_one (α := ℂ) h1'

end GlobalTheory.FramesUnion
