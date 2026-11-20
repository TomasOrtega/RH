import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants

section loc

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hopen : IsOpen (OmX r)`. Establish `e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0}`. Use extensionality with `x`. Simplify using `[OmX]`. Rewrite using `[e]`.

Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Establish `hev : f₁ =ᶠ[nhds c] f₂` using `Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) h`. Unfold `pbOp wirtBar`. Rewrite using `[if_pos hc, if_pos hc, hev.fderiv_eq]`.
-/
theorem rds_pbOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbOp l f₁ c = pbOp l f₂ c := by
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hev : f₁ =ᶠ[nhds c] f₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) h
  unfold pbOp wirtBar
  rw [if_pos hc, if_pos hc, hev.fderiv_eq]

/- English proof (translation)
The claim follows from `| 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩ | i + 1, f₁, f₂, h, c, hc => by have ih := rds_vABm_loc Y i f₁ f₂ h by_cases hi : i < r · simp only [CutMP.vABm, dif_pos hi] refine ⟨?_, ?_⟩ · simp only [Pi.sub_apply, Pi.smul_apply, cbOp] rw [(ih c hc).1, (ih c hc).2, rds_pbOp_locO _ (fun c …`.
-/
theorem rds_vABm_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (CutMP.vABm r Y i).1 f₁ c = (CutMP.vABm r Y i).1 f₂ c ∧
      (CutMP.vABm r Y i).2 f₁ c = (CutMP.vABm r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    have ih := rds_vABm_loc Y i f₁ f₂ h
    by_cases hi : i < r
    · simp only [CutMP.vABm, dif_pos hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply, Pi.smul_apply, cbOp]
        rw [(ih c hc).1, (ih c hc).2, rds_pbOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [cbiOp]
        rw [(ih c hc).1]
    · simp only [CutMP.vABm, dif_neg hi]
      exact ih c hc

end loc

/- English proof (translation)
Introduce `r E _ _ y f f' h c hc`. Establish `hopen : IsOpen (OmX r)`. Establish `e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0}`. Use extensionality with `x`. Simplify using `[OmX]`.

Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Establish `hpO : ∀ (l : Fin r) (g₁ g₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r, pOp l g₁ c = pOp l g₂ c`. Introduce `l g₁ g₂ hg c hc`. Establish `hev : g₁ =ᶠ[nhds c] g₂` using `Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) hg`.

Unfold `pOp Formalism.QuantumDeterminants.wirt`. Rewrite using `[if_pos hc, if_pos hc, hev.fderiv_eq]`. Establish `hA : ∀ i : ℕ, ∀ g₁ g₂ : (Fin r → ℂ) → E, (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r, (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c ∧ (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero`. Introduce `g₁ g₂ hg c hc`. Simplify using `only [Q.vAB]`. Conclude with `⟨hg c hc, by trivial⟩`. Consider the case `succ i ih`.

Introduce `g₁ g₂ hg c hc`. Establish `ih1 : ∀ c ∈ OmX r, (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c` using `fun c hc => (ih g₁ g₂ hg c hc).1`. Establish `ih2 : ∀ c ∈ OmX r, (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c` using `fun c hc => (ih g₁ g₂ hg c hc).2`. Simplify using `only [Q.vAB]`. Use `split_ifs with hi`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]`. Rewrite using `[ih1 c hc, hpO ⟨i, hi⟩ _ _ ih1 c hc]`. Simplify using `only [cOp]`. Rewrite using `[ih2 c hc]`.

Simplify using `only [ciOp]`. Rewrite using `[ih1 c hc]`. Conclude with `ih g₁ g₂ hg c hc`. Conclude with `⟨(hA r f f' h c hc).1, (rds_vABm_loc y r f f' h c hc).1⟩`.
-/
theorem spectral_action_locality : RDSALoc := by
  intro r E _ _ y f f' h c hc
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hpO : ∀ (l : Fin r) (g₁ g₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      pOp l g₁ c = pOp l g₂ c := by
    intro l g₁ g₂ hg c hc
    have hev : g₁ =ᶠ[nhds c] g₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) hg
    unfold pOp Formalism.QuantumDeterminants.wirt
    rw [if_pos hc, if_pos hc, hev.fderiv_eq]
  have hA : ∀ i : ℕ, ∀ g₁ g₂ : (Fin r → ℂ) → E, (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c ∧ (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := by
    intro i
    induction i with
    | zero =>
      intro g₁ g₂ hg c hc
      simp only [Q.vAB]
      exact ⟨hg c hc, by trivial⟩
    | succ i ih =>
      intro g₁ g₂ hg c hc
      have ih1 : ∀ c ∈ OmX r, (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).1
      have ih2 : ∀ c ∈ OmX r, (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).2
      simp only [Q.vAB]
      split_ifs with hi
      · refine ⟨?_, ?_⟩
        · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          rw [ih1 c hc, hpO ⟨i, hi⟩ _ _ ih1 c hc]
          simp only [cOp]
          rw [ih2 c hc]
        · simp only [ciOp]
          rw [ih1 c hc]
      · exact ih g₁ g₂ hg c hc
  exact ⟨(hA r f f' h c hc).1, (rds_vABm_loc y r f f' h c hc).1⟩

end Formalism.FourierDecayAlt.P.CutSE
