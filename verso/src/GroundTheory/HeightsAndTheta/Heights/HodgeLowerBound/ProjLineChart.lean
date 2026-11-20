import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjLineAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace LineChart

def lineLift (w : ((k : Unit) → PBlk 2 k) → ℂ) : (Σ k : Unit, PBlk 2 k) → ℂ := fun p => w fun _ => p.2

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem segre_line (z : (Σ k : Unit, PBlk 2 k) → ℂ) (i : (k : Unit) → PBlk 2 k) :
    segre z i = z ⟨(), i ()⟩ := by
  simp [segre]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem segre_lineLift (w : ((k : Unit) → PBlk 2 k) → ℂ) : segre (lineLift w) = w := by
  funext i
  rw [segre_line]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem lineLift_segre (z : (Σ k : Unit, PBlk 2 k) → ℂ) : lineLift (segre z) = z := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp only [lineLift, segre_line]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Split into cases according to the possible forms of the given data.

Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_mcPts_bot (z : (Σ k : Unit, PBlk 2 k) → ℂ) :
    z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) ↔ ∃ i, z ⟨(), i⟩ ≠ 0 := by
  constructor
  · rintro ⟨h, -⟩
    exact h ()
  · intro h
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · cases k
      exact h
    · rw [Ideal.mem_bot] at hf
      subst hf
      simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem lineLift_mem {w : ((k : Unit) → PBlk 2 k) → ℂ} (hw : w ≠ 0) :
    lineLift w ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine (mem_mcPts_bot _).2 ⟨i (), ?_⟩
  simpa [lineLift] using hi

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem injective_of_good {Ψ : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    (hΨ : IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ) : Function.Injective Ψ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  exact hΨ _ (lineLift_mem hne) (by rw [segre_lineLift]; exact hw)

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_good :
    ∃ Ψ : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ), IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique Unit (Fin 2)).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := (mem_mcPts_bot z).1 hz
  have hs : segre z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [← segre_line z (fun _ => i), hs]; rfl)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem geomDeg_eq_integral (A : HermLine (PBlk 2)) :
    ∃ L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ),
      geomDeg (⊥ : Ideal (MRing (PBlk 2))) A 1 =
        ∫ y : Fin 1 → ℂ, maDensity (fun _ y' => Real.log (A.h (lineLift (L (Fin.cons 1 y'))))) y := by
  have hex := exists_good
  set Ψ := hex.choose with hΨdef
  have hΨ : IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ := hex.choose_spec
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ (((k : Unit) → PBlk 2 k) → ℂ) = Module.finrank ℂ (Fin (1 + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set E := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩ with hE
  set L := E.symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := E.apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := E.symm_apply_apply
  refine ⟨L, ?_⟩
  have hLdiff : Differentiable ℂ fun v => L v := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin 1 → ℂ => (Fin.cons 1 y' : Fin (1 + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin 1 → ℂ) → (Σ k : Unit, PBlk 2 k) → ℂ := fun y' => lineLift (L (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply (fun _ => p.2)).comp (hLdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (1 + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    exact lineLift_mem ((L.map_ne_zero_iff).mpr hv)
  unfold geomDeg ptsIntegral
  rw [dif_pos hex]
  unfold ptsIntegralAt
  congr 1
  funext y
  have hfib : fibre (⊥ : Ideal (MRing (PBlk 2))) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, segre_lineLift _, hΨL _⟩
  have hsheet : IsSheet (⊥ : Ideal (MRing (PBlk 2))) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨segre_lineLift _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [segre_lineLift, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log (A.h (hγ.choose y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (A.h (lineLift (L (Fin.cons 1 y')))) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (hγ.choose y') = L (Fin.cons 1 y') := by
        rw [← hLΨ (segre (hγ.choose y')), hy'.2.2]
      rw [← hs, lineLift_segre]
    rw [one_mul]
    exact maDensity_congr_of_eventuallyEq fun _ => hev
  · exact absurd ⟨γ0, hsheet⟩ hγ

end LineChart

end GroundTheory.Heights₂.Heights.LowerBoundFree
