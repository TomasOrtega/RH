import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ConjMatch

variable {D : D7}

/- English proof (translation)
The claim follows from `(GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.SplitHeckeAdj.isConjPl_conj P)`.
-/
theorem conj_eq_cP (P : Pl D.host.E) : Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.SplitHeckeAdj.isConjPl_conj P)

/- English proof (translation)
Rewrite using `[conj_eq_cP, conj_eq_cP]`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]`.
-/
theorem conj_conj (P : Pl D.host.E) : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := by
  rw [conj_eq_cP, conj_eq_cP]
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

/- English proof (translation)
Break down `h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩` into its components or cases. Establish `h1 : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P)`. Rewrite using `[conj_eq_cP]`. Take `⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩` from `h`. Conclude with `⟨⟨by rw [← RingHom.map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε, by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩, GlobalTheory.IdemSupport.Comparison₂.conj ht⟩`.

Conclude with `Or.inl ⟨h1, by rw [Formalism.L2.Theta.cA_cA, add_comm]⟩`. Establish `hc` using `GlobalTheory.IdemSupport.cA_algebraMap (D := D) ε`. Establish `ht'` using `GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht`. Rewrite `ht'` using `[← conj_eq_cP]`. Rewrite `ht'`, the goal using `[hc]`.

Conclude with `Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, ht'⟩`.
-/
theorem isPrimeIdem_conj {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    IsPrimeIdem (Formalism.DivisionValues.conjPl P) (cA D e) f := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have h1 : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) := by
      rw [conj_eq_cP]
      obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
      exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
        by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩, GlobalTheory.IdemSupport.Comparison₂.conj ht⟩
    exact Or.inl ⟨h1, by rw [Formalism.L2.Theta.cA_cA, add_comm]⟩
  · have hc := GlobalTheory.IdemSupport.cA_algebraMap (D := D) ε
    have ht' := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [← conj_eq_cP] at ht'
    rw [hc] at ht' ⊢
    exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, ht'⟩

/- English proof (translation)
Use `⟨h.1, fun e f' hP u hu hh => h.2 (cA D e) f' ?_ u hu ?_⟩` and prove the remaining obligations. Use `isPrimeIdem_conj hP` as an intermediate fact. Rewrite `this` using `[conj_conj]`. Then use the resulting hypothesis. Rewrite using `[Formalism.L2.Theta.cA_cA]`. Conclude with `hh.symm`.
-/
theorem isVacAt_conj (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ)
    (h : IsVacAt ψ S T P f) : IsVacAt ψ S T (Formalism.DivisionValues.conjPl P) f := by
  refine ⟨h.1, fun e f' hP u hu hh => h.2 (cA D e) f' ?_ u hu ?_⟩
  · have := isPrimeIdem_conj hP
    rwa [conj_conj] at this
  · rw [Formalism.L2.Theta.cA_cA]
    exact hh.symm

/- English proof (translation)
Take `⟨e, f, h⟩` from `GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.IdemSupport.exists_comp D).choose_spec P`. Use `⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, h, (GlobalTheory.IdemSupport.suppGroup V f).one_mem⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]`.
-/
theorem one_mem_hyp (V : HSp D) (P : Pl D.host.E) : (1 : GA D V) ∈ hyp V P := by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.IdemSupport.exists_comp D).choose_spec P
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, h,
    (GlobalTheory.IdemSupport.suppGroup V f).one_mem⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

/- English proof (translation)
Introduce `D ψ S T χS χT om P _`. Establish `hv : ∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f` using `fun f => ⟨fun h => by have := isVacAt_conj ψ S T _ f h; rwa [conj_conj] at this, isVacAt_conj ψ S T P f⟩`. Use `⟨hv, fun hF => ?_⟩` and prove the remaining obligations. Establish `hS` using `GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel S P`. Establish `hT` using `GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel T P`.

Use `⟨fun f hf k hk k' hk' => hF f ((hv f).1 hf) k (hS.1 ▸ hk) k' (hT.1 ▸ hk'), fun cS cT => ?_⟩` and prove the remaining obligations. Establish `eS : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inl _ _)) (conjPl P) c f = opOf (om.comp (MonoidHom.inl _ _)) P (dualC c) f` using `fun f hf c => hS.2.2 c _ (om.comp (MonoidHom.inl _ _)) f fun k hk => hF f hf k hk 1 (one_mem_hyp T P)`. Establish `eT : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inr _ _)) (conjPl P) c f = opOf (om.comp (MonoidHom.inr _ _)) P (dualC c) f` using `fun f hf c => hT.2.2 c _ (om.comp (MonoidHom.inr _ _)) f fun k hk => hF f hf 1 (one_mem_hyp S P) k hk`. Prove the components needed by the constructor for the conclusion. Introduce `h f hf`.

Rewrite using `[← eS f hf, ← eT f hf]`. Conclude with `h f ((hv f).2 hf)`. Introduce `h f hf`. Establish `hf'` using `(hv f).1 hf`. Rewrite using `[eS f hf', eT f hf']`.

Conclude with `h f hf'`.
-/
theorem match_conj : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (conjPl P) ∧ ∀ cS cT, Match ψ om (conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  intro D ψ S T χS χT om P _
  have hv : ∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f := fun f =>
    ⟨fun h => by have := isVacAt_conj ψ S T _ f h; rwa [conj_conj] at this, isVacAt_conj ψ S T P f⟩
  refine ⟨hv, fun hF => ?_⟩
  have hS := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel S P
  have hT := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel T P
  refine ⟨fun f hf k hk k' hk' => hF f ((hv f).1 hf) k (hS.1 ▸ hk) k' (hT.1 ▸ hk'), fun cS cT => ?_⟩
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inl _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inl _ _)) P (dualC c) f := fun f hf c =>
    hS.2.2 c _ (om.comp (MonoidHom.inl _ _)) f fun k hk => hF f hf k hk 1 (one_mem_hyp T P)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inr _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inr _ _)) P (dualC c) f := fun f hf c =>
    hT.2.2 c _ (om.comp (MonoidHom.inr _ _)) f fun k hk => hF f hf 1 (one_mem_hyp S P) k hk
  constructor
  · intro h f hf
    rw [← eS f hf, ← eT f hf]
    exact h f ((hv f).2 hf)
  · intro h f hf
    have hf' := (hv f).1 hf
    rw [eS f hf', eT f hf']
    exact h f hf'

end GlobalTheory.Hk3.ConjMatch

end
