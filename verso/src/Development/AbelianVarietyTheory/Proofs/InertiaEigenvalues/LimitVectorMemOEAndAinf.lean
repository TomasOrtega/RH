import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `l _ K bk τ hτ d N ρ tw F T0 R hR hF v hv`. Establish `hcl` using `GlobalTheory.T.breuilKisin_OE_stability_properties l K bk`. Establish `hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE` using `fun s n => ⟨0, s, 0, by simp⟩`. Establish `key : ∀ (k : ℕ) (z : WCb l), (l : WCb l) ^ k ∣ z ↔ Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) z = 0` using `fun k z => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.

Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Apply `hcl.2.1` to reduce the goal to its premises. Introduce `n`. Take `⟨s', hs'⟩` from `hv n`. Use `⟨(R n *ᵥ fun j => bk.evW (s' j)) i, ?_, hs' i⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hevW _)`. Establish `hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x` using `fun x => (inclWA l).commutes x`. Establish `hx : ∀ i k, ∃ a : Ainf l, (l : WCb l) ^ k ∣ (l : WCb l) ^ 0 * (inclW l τ ^ N • (T0 *ᵥ v)) i - inclW l (1 * a)`. Introduce `i k`.

Take `⟨s', hs'⟩` from `hv k`. Take `⟨Y, Y', hY, -⟩` from `GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' k) (fun g => (tw.ρ' k g).val) (F k)`. Use `⟨(((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i, ?_⟩` and prove the remaining obligations. Use `set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) with hq`. Rewrite using `[key, pow_zero, one_mul, one_mul, map_sub, sub_eq_zero]`.

Establish `h1 : (fun i => q (v i)) = fun i => q ((R k *ᵥ fun j => bk.evW (s' j)) i)` using `funext fun i => by`. Use `(key k _).1 (hs' i)` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h2 : (zW (tw.Pi k) * (F k).T).map q = (T0 * R k).map q`. Use extensionality with `i j`.

Use `(key k _).1 (hF k i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `e1 : inclW l ((((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i) = (inclW l τ ^ N • ((zW (tw.Pi k) * (F k).T) *ᵥ fun j => bk.evW (s' j))) i`. Rewrite using `[RingHom.map_mulVec, Matrix.map_mul, hY, Matrix.map_map]`. Establish `: (tw.Pi k).map ((inclW l) ∘ (algebraMap ℤ_[l] (Ainf l))) = zW (tw.Pi k)`.

Use extensionality with `a b`. Simplify using `[zW, hinc]`. Rewrite using `[this, Matrix.mul_smul, Matrix.smul_mulVec]`. Both sides reduce to the same expression. Rewrite using `[e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, RingHom.map_mulVec, RingHom.map_mulVec, h2, Matrix.map_mul, ← Matrix.mulVec_mulVec]`.

Establish `h1' : (⇑q ∘ v) = (R k).map q *ᵥ (⇑q ∘ fun j => bk.evW (s' j))` using `funext fun j => by`. Rewrite using `[Function.comp_apply, ← RingHom.map_mulVec]`. Conclude with `congrFun h1 j`. Rewrite using `[h1']`. Use `⟨fun i => Classical.choose (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i)), funext fun i => ?_⟩` and prove the remaining obligations.

Use `Classical.choose_spec (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i))` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `this.symm`.
-/
theorem GlobalTheory.BKLim.limvec_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hR hF v hv
  have hcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have key : ∀ (k : ℕ) (z : WCb l), (l : WCb l) ^ k ∣ z ↔
      Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) z = 0 := fun k z => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun i => ?_, ?_⟩
  · apply hcl.2.1
    intro n
    obtain ⟨s', hs'⟩ := hv n
    refine ⟨(R n *ᵥ fun j => bk.evW (s' j)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hevW _)
  · have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
      fun x => (inclWA l).commutes x
    have hx : ∀ i k, ∃ a : Ainf l, (l : WCb l) ^ k ∣
        (l : WCb l) ^ 0 * (inclW l τ ^ N • (T0 *ᵥ v)) i - inclW l (1 * a) := by
      intro i k
      obtain ⟨s', hs'⟩ := hv k
      obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' k) (fun g => (tw.ρ' k g).val) (F k)
      refine ⟨(((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i, ?_⟩
      set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) with hq
      rw [key, pow_zero, one_mul, one_mul, map_sub, sub_eq_zero]
      have h1 : (fun i => q (v i)) = fun i => q ((R k *ᵥ fun j => bk.evW (s' j)) i) := funext fun i => by
        have := (key k _).1 (hs' i); rwa [Pi.sub_apply, map_sub, sub_eq_zero] at this
      have h2 : (zW (tw.Pi k) * (F k).T).map q = (T0 * R k).map q := by
        ext i j; have := (key k _).1 (hF k i j); rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      have e1 : inclW l ((((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i) =
          (inclW l τ ^ N • ((zW (tw.Pi k) * (F k).T) *ᵥ fun j => bk.evW (s' j))) i := by
        rw [RingHom.map_mulVec, Matrix.map_mul, hY, Matrix.map_map]
        have : (tw.Pi k).map ((inclW l) ∘ (algebraMap ℤ_[l] (Ainf l))) = zW (tw.Pi k) := by
          ext a b; simp [zW, hinc]
        rw [this, Matrix.mul_smul, Matrix.smul_mulVec]
        rfl
      rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        RingHom.map_mulVec, RingHom.map_mulVec, h2, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      have h1' : (⇑q ∘ v) = (R k).map q *ᵥ (⇑q ∘ fun j => bk.evW (s' j)) := funext fun j => by
        rw [Function.comp_apply, ← RingHom.map_mulVec]; exact congrFun h1 j
      rw [h1']
    refine ⟨fun i => Classical.choose (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i)), funext fun i => ?_⟩
    have := Classical.choose_spec (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i))
    rw [one_mul] at this
    exact this.symm
