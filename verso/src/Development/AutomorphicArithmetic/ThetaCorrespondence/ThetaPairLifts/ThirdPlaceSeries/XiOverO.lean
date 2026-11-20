import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfIota
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie
  GlobalTheory.SplitRead GlobalTheory.XiOver Formalism.L2.Host
/- English proof (translation)
Introduce `i`. Take `⟨ρ, hρ, hwd, -⟩` from `(_root_.UpperTheory.GalS.weak' h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)`. Establish `hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w)` using `fun w hw => by`. Rewrite using `[hwd w hw]`. Conclude with `(D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1`.

Establish `hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F` using `D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by`. Introduce `w hw B σ hB hσ`. Establish `e` using `D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ`. Take `⟨a, ha⟩` from `Multiset.card_eq_one.1 ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))`. Rewrite `e` using `[ha, charpoly_fin_one]`.

Simplify using `only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e`. Establish `e2` using `C_injective (sub_right_injective e)`. Rewrite using `[← hwd w hw, ha]`. Conclude with `congrArg _ e2.symm`. Set `d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Qbar (D.nd.l i)` to `(Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)`.

Establish `hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0` using `fun g => Matrix.det_fin_one _`. Establish `hd : Continuous d`. Establish `: (d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g => ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0` using `funext hde`. Rewrite using `[this]`. Conclude with `(continuous_apply_apply 0 0).comp hρ`.

Establish `hfin : (placesOver D.host.E (D.nd.l i)).Finite` using `GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero`. Establish `hS : closure {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F` using `D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ := by`. Establish `hd` using `(h5 hfin.toFinset).closure_eq`. Use `hd using 4 with σ` and compare the differences between its conclusion and the goal. Simplify using `[Set.Finite.mem_toFinset]`.

Take `⟨ξ, hξc, hξ⟩` from `exists_integral_char D.nd D.naut i d hd _ hS (by`. Introduce and unpack `σ ⟨w, hw, -, B, hB, hσ⟩`. Take `⟨x, hx⟩` from `frob_value D C nch Tp T V w`. Establish `e` using `hfrob w hw B σ hB hσ`. Rewrite `e` using `[hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde]`.

Conclude with `⟨_, (D.naut.iotaQC i).injective e⟩)`. Use `⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ`. Apply `Units.ext` to reduce the goal to its premises. Apply `iota_inj D.nd D.naut i` to reduce the goal to its premises.

Rewrite using `[hξ, hde, h1]`. Simplify using the standard rewrite rules. Rewrite using `[hfrob w hw B σ hB hσ, ← hde, ← hξ]`. Both sides reduce to the same expression.
-/
theorem xi_over_o_of_adm2 (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (T : Formalism.L2.Host.NCharTied D C nch Tp) (V : Formalism.L2.Host.ValLL0 D C) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut)
    (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : ChebSplit D.nd) : XiOverO D.nd D.naut := by
  intro i
  obtain ⟨ρ, hρ, hwd, -⟩ := (_root_.UpperTheory.GalS.weak' h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)
  have hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w) := fun w hw => by
    rw [hwd w hw]
    exact (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  have hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
        {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by
    intro w hw B σ hB hσ
    have e := D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1
      ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))
    rw [ha, charpoly_fin_one] at e
    simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at e
    have e2 := C_injective (sub_right_injective e)
    rw [← hwd w hw, ha]
    exact congrArg _ e2.symm
  let d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Qbar (D.nd.l i) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    fun g => Matrix.det_fin_one _
  have hd : Continuous d := by
    have : (d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g =>
        ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := funext hde
    rw [this]
    exact (continuous_apply_apply 0 0).comp hρ
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero
  have hS : closure {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ := by
    have hd := (h5 hfin.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_char D.nd D.naut i d hd _ hS (by
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨x, hx⟩ := frob_value D C nch Tp T V w
    have e := hfrob w hw B σ hB hσ
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde] at e
    exact ⟨_, (D.naut.iotaQC i).injective e⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩
  · have h1 := (D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ
    apply Units.ext
    apply iota_inj D.nd D.naut i
    rw [hξ, hde, h1]
    simp
  · rw [hfrob w hw B σ hB hσ, ← hde, ← hξ]
    rfl
end
end GlobalTheory.ResLoc
end
end
