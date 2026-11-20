import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalvesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 400000

namespace GlobalTheory.FinPl.ScalarDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl.FrameLat

/- English proof (translation)
Unfold `idAt at ha ⊢`. Take `⟨h0, hw⟩` from `Ideal.mem_inf.1 ha`. Conclude with `Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).1 hw ⟨w.1, fun hp => w.2 (hPQ _ hp)⟩⟩`.
-/
theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w =>
    (Submodule.mem_iInf _).1 hw ⟨w.1, fun hp => w.2 (hPQ _ hp)⟩⟩

/- English proof (translation)
Establish `h1 : q.e * a ∈ idAt D (· = w)` using `Ideal.mul_mem_left _ _ ha`. Establish `h2 : q.e * a ∈ idAt D (· = q.v)` using `Ideal.mul_mem_right _ _ (e_mem_idAt q)`. Unfold `idAt at h1 h2`. Establish `h0 : q.e * a = 0`. Apply `GlobalTheory.FinPlLoc.eq_zero_of_comp` to reduce the goal to its premises.

Conclude with `RingHom.mem_ker.1 (Ideal.mem_inf.1 h1).1`. Introduce `u`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Conclude with `RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h2).2 ⟨u, hw⟩)`.

Conclude with `RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h1).2 ⟨u, hu⟩)`. Rewrite using `[← q.pr_sec (q.pr a), q.sec_pr, h0, map_zero]`.
-/
theorem pr_eq_zero (q : SplitPt D k) {w : Pl D} (hw : w ≠ q.v) {a : AE D} (ha : a ∈ idAt D (· = w)) : q.pr a = 0 := by
  have h1 : q.e * a ∈ idAt D (· = w) := Ideal.mul_mem_left _ _ ha
  have h2 : q.e * a ∈ idAt D (· = q.v) := Ideal.mul_mem_right _ _ (e_mem_idAt q)
  unfold idAt at h1 h2
  have h0 : q.e * a = 0 := by
    apply GlobalTheory.FinPlLoc.eq_zero_of_comp
    · exact RingHom.mem_ker.1 (Ideal.mem_inf.1 h1).1
    · intro u
      by_cases hu : u = w
      · subst hu
        exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h2).2 ⟨u, hw⟩)
      · exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h1).2 ⟨u, hu⟩)
  rw [← q.pr_sec (q.pr a), q.sec_pr, h0, map_zero]

/- English proof (translation)
Establish `hid : cA D (q.sec 1) ∈ idAt D (· = q.v)` using `csec_mem_idAt (p := q) 1`. Establish `hc : cA D (q.sec 1) ∈ intAt D (· = q.v)`. Use `(GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitLineSim.pr_cA_sec]`. Conclude with `zero_mem _`.

Rewrite using `[Formalism.L2.Theta.cA_cA, q.pr_sec]`. Conclude with `one_mem _`. Establish `h2` using `hU.1 _ hc`. Establish `a1` using `((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1.1).1 h2.1).2`. Establish `a2` using `((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.2.1).1 h2.2).2`.

Rewrite `a1`, `a2` using `[map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one]`. Conclude with `⟨a1, a2⟩`.
-/
theorem pr_cA_xi_int (q : SplitPt D k) (hU : q.UnitAA) :
    q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] ∧ q.pr (cA D (incA D D.host.xi0⁻¹)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [GlobalTheory.SplitLineSim.pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := hU.1 _ hc
  have a1 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1.1).1 h2.1).2
  have a2 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.2.1).1 h2.2).2
  rw [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at a1 a2
  exact ⟨a1, a2⟩

/- English proof (translation)
Introduce `D k _ _ _ _ ι p I P hP h h' hh hh' hs hhe d hd`. Establish `hne : D.host.xi0 ≠ 0` using `GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero`. Establish `hv : ∀ i, P (p i).v` using `fun i => (hP.mem _).2 ⟨i, rfl⟩`. Establish `hne_v : ∀ i j, i ≠ j → (p i).v ≠ (p j).v` using `fun i j hij e => hij (hP.inj e)`. Establish `hU` using `fun i => pr_cA_xi_int (p i) (hP.unit i)`.

Establish `hprod : ∀ i, (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr (cA D (incA D D.host.xi0)) = 1`. Introduce `i`. Rewrite using `[← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one, map_one]`. Establish `hch : cA D (incA D h) = incA D h`. Rewrite using `[cA_incA, hhe, star_mul, star_mul, star_star, hs]`.

Put the polynomial expressions in normal form. Establish `hx1 : incA D D.host.xi0⁻¹ * incA D h = cA D (incA D D.host.xi0) * incA D h'`. Rewrite using `[cA_incA, ← map_mul, ← map_mul, hhe, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]`. Establish `hX : ∀ c, incA D D.host.xi0⁻¹ * cA D d * c * incA D h = cA D (incA D D.host.xi0) * (cA D d * incA D h') * c` using `fun c => by`. Take the linear combination `(cA D d * c) * hx1`.

Establish `hcX : ∀ c, cA D (incA D D.host.xi0⁻¹ * cA D d * c * incA D h) = cA D (incA D D.host.xi0⁻¹) * d * (cA D c * incA D h)` using `fun c => by`. Simplify using `only [map_mul, Formalism.L2.Theta.cA_cA, hch]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `hdc c hc hcc`.

Use `(GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).2 ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc), fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]`. Conclude with `mul_mem (mul_mem (hU i).1 (hdc i).2) (hcc i).1`. Rewrite using `[hcX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]`. Conclude with `mul_mem (mul_mem (hU i).2 (hdc i).1) (hcc i).2`.

Introduce `H i`. Establish `hsup : ∀ {a : AE D}, a ∈ idAt D (· = (p i).v) → a ∈ idAt D P` using `fun ha => idAt_mono (fun w hw => by rw [hw]; exact hv i) ha`. Establish `hcond1 : ∀ j, (p j).pr ((p i).sec 1) ∈ 𝒪[k] ∧ (p j).pr (cA D ((p i).sec 1)) * (p j).pr (incA D h) ∈ 𝒪[k]`. Introduce `j`. Distinguish the cases in `hij : j = i`.

Substitute `hij` using the available equality. Rewrite using `[(p j).pr_sec, GlobalTheory.SplitLineSim.pr_cA_sec, zero_mul]`. Conclude with `⟨one_mem _, zero_mem _⟩`. Rewrite using `[pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) 1), pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) 1), zero_mul]`. Conclude with `⟨zero_mem _, zero_mem _⟩`.

Establish `h1` using `(((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (sec_mem_idAt (p i) 1)) hcond1)).2 i).1`. Rewrite `h1` using `[hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr, (p i).pr_sec, mul_one]`. Establish `hh0 : (p i).pr (incA D h) ≠ 0`. Introduce `h0`. Use `congrArg (p i).pr (congrArg (incA D) (mul_inv_cancel₀ hh))` as an intermediate fact.

Rewrite `this` using `[map_mul (incA D), map_mul (p i).pr, h0, zero_mul, map_one, map_one]`. Conclude with `zero_ne_one this`. Establish `hcond2 : ∀ j, (p j).pr (cA D ((p i).sec ((p i).pr (incA D h))⁻¹)) ∈ 𝒪[k] ∧ (p j).pr (cA D (cA D ((p i).sec ((p i).pr (incA D h))⁻¹))) * (p j).pr (incA D h) ∈ 𝒪[k]`. Introduce `j`. Rewrite using `[Formalism.L2.Theta.cA_cA]`.

Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Rewrite using `[GlobalTheory.SplitLineSim.pr_cA_sec, (p j).pr_sec, inv_mul_cancel₀ hh0]`. Conclude with `⟨zero_mem _, one_mem _⟩`. Rewrite using `[pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) ((p i).pr (incA D h))⁻¹), pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹), zero_mul]`.

Conclude with `⟨zero_mem _, zero_mem _⟩`. Establish `h2` using `(((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹)) hcond2)).2 i).2`. Rewrite `h2` using `[hcX, Formalism.L2.Theta.cA_cA]`. Establish `e3 : (p i).pr (cA D (incA D D.host.xi0⁻¹) * d * ((p i).sec ((p i).pr (incA D h))⁻¹ * incA D h)) = (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d`. Simplify using `only [map_mul, (p i).pr_sec]`.

Rewrite using `[inv_mul_cancel₀ hh0, mul_one]`. Rewrite `h2` using `[e3]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e2 : (p i).pr d = (p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d)`. Take the linear combination `(-(p i).pr d) * hprod i`.

Rewrite using `[e2]`. Conclude with `mul_mem (hU i).1 h2`. Establish `e1 : (p i).pr (cA D d) * (p i).pr (incA D h') = (p i).pr (cA D (incA D D.host.xi0⁻¹)) * ((p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D d) * (p i).pr (incA D h')))`. Take the linear combination `(-((p i).pr (cA D d) * (p i).pr (incA D h'))) * hprod i`. Rewrite using `[e1]`.

Conclude with `mul_mem (hU i).2 h1`.
-/
theorem cond_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP h h' hh hh' hs hhe d hd
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hv : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  have hne_v : ∀ i j, i ≠ j → (p i).v ≠ (p j).v := fun i j hij e => hij (hP.inj e)
  have hU := fun i => pr_cA_xi_int (p i) (hP.unit i)
  have hprod : ∀ i, (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr (cA D (incA D D.host.xi0)) = 1 := by
    intro i
    rw [← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one, map_one]
  have hch : cA D (incA D h) = incA D h := by
    rw [cA_incA, hhe, star_mul, star_mul, star_star, hs]
    ring_nf
  have hx1 : incA D D.host.xi0⁻¹ * incA D h = cA D (incA D D.host.xi0) * incA D h' := by
    rw [cA_incA, ← map_mul, ← map_mul, hhe, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hX : ∀ c, incA D D.host.xi0⁻¹ * cA D d * c * incA D h =
      cA D (incA D D.host.xi0) * (cA D d * incA D h') * c := fun c => by
    linear_combination (cA D d * c) * hx1
  have hcX : ∀ c, cA D (incA D D.host.xi0⁻¹ * cA D d * c * incA D h) =
      cA D (incA D D.host.xi0⁻¹) * d * (cA D c * incA D h) := fun c => by
    simp only [map_mul, Formalism.L2.Theta.cA_cA, hch]
    ring
  constructor
  · intro hdc c hc hcc
    refine (GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).2 ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc), fun i => ⟨?_, ?_⟩⟩
    · rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).1 (hdc i).2) (hcc i).1
    · rw [hcX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).2 (hdc i).1) (hcc i).2
  · intro H i
    have hsup : ∀ {a : AE D}, a ∈ idAt D (· = (p i).v) → a ∈ idAt D P :=
      fun ha => idAt_mono (fun w hw => by rw [hw]; exact hv i) ha

    have hcond1 : ∀ j, (p j).pr ((p i).sec 1) ∈ 𝒪[k] ∧
        (p j).pr (cA D ((p i).sec 1)) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      by_cases hij : j = i
      · subst hij
        rw [(p j).pr_sec, GlobalTheory.SplitLineSim.pr_cA_sec, zero_mul]
        exact ⟨one_mem _, zero_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) 1),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) 1), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h1 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (sec_mem_idAt (p i) 1)) hcond1)).2 i).1
    rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr, (p i).pr_sec, mul_one] at h1

    have hh0 : (p i).pr (incA D h) ≠ 0 := by
      intro h0
      have := congrArg (p i).pr (congrArg (incA D) (mul_inv_cancel₀ hh))
      rw [map_mul (incA D), map_mul (p i).pr, h0, zero_mul, map_one, map_one] at this
      exact zero_ne_one this
    have hcond2 : ∀ j, (p j).pr (cA D ((p i).sec ((p i).pr (incA D h))⁻¹)) ∈ 𝒪[k] ∧
        (p j).pr (cA D (cA D ((p i).sec ((p i).pr (incA D h))⁻¹))) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      rw [Formalism.L2.Theta.cA_cA]
      by_cases hij : j = i
      · subst hij
        rw [GlobalTheory.SplitLineSim.pr_cA_sec, (p j).pr_sec, inv_mul_cancel₀ hh0]
        exact ⟨zero_mem _, one_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) ((p i).pr (incA D h))⁻¹),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h2 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹)) hcond2)).2 i).2
    rw [hcX, Formalism.L2.Theta.cA_cA] at h2
    have e3 : (p i).pr (cA D (incA D D.host.xi0⁻¹) * d * ((p i).sec ((p i).pr (incA D h))⁻¹ * incA D h)) =
        (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d := by
      simp only [map_mul, (p i).pr_sec]
      rw [inv_mul_cancel₀ hh0, mul_one]
    rw [e3] at h2
    refine ⟨?_, ?_⟩
    · have e2 : (p i).pr d = (p i).pr (cA D (incA D D.host.xi0)) *
          ((p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d) := by
        linear_combination (-(p i).pr d) * hprod i
      rw [e2]; exact mul_mem (hU i).1 h2
    · have e1 : (p i).pr (cA D d) * (p i).pr (incA D h') = (p i).pr (cA D (incA D D.host.xi0⁻¹)) *
          ((p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D d) * (p i).pr (incA D h'))) := by
        linear_combination (-((p i).pr (cA D d) * (p i).pr (incA D h'))) * hprod i
      rw [e1]; exact mul_mem (hU i).2 h1

end GlobalTheory.FinPl.ScalarDual

end
