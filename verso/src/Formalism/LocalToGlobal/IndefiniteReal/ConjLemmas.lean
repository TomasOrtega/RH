import Formalism.LocalToGlobal.IndefiniteReal.IsThPKernelSigBase
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.FrobeniusOrbits

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem emb_mul' (g g' : D.R.GG) (x : D.host.E) :
    D.host.emb (g * g') x = D.host.emb g (D.host.sigmaOf g' x) := by
  simp only [Host.emb, Host.sigmaOf, map_mul, RingHom.comp_apply]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem conj_comp_emb (g : D.R.GG) :
    (starRingEnd ℂ).comp (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  ext x
  rw [RingHom.comp_apply, emb_mul', ← D.host.conjE_apply (D.host.emb g)]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cc_mul_cc : D.R.cc * D.R.cc = 1 := by
  simp [Formalism.HC.Frame.cc, c0, Prod.ext_iff]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem ArchLab.emb_eq (A : ArchLab D) (τ : D.what₂.Tau) :
    A.emb τ = D.host.emb ((D.eTau (A.perm τ)).1 * (if A.side then 1 else D.R.cc)) := by
  rcases A with ⟨p, s⟩
  cases s
  · simp [ArchLab.emb, tauE, conj_comp_emb]
  · simp [ArchLab.emb, tauE]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem emb_injective : Function.Injective (D.host.emb) := (factEmb D.R D.host).1.1

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Check the signs of the components of the expression. A detailed English derivation is pending.
-/
theorem tau_nonempty : Nonempty D.what₂.Tau := by
  have h : 0 < Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau]
    unfold Ranks.f Ranks.n
    positivity
  exact Fintype.card_pos_iff.mp h

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem snd_side (b : Bool) : ((if b then 1 else D.R.cc : D.R.GG)).1.2 = if b then 1 else -1 := by
  cases b <;> rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Substitute using the available equality. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
-/
theorem labUnique : LabUnique D := by
  intro σ A A' h h'
  have key : ∀ τ, (D.eTau (A.perm τ)).1 * (if A.side then 1 else D.R.cc) =
      (D.eTau (A'.perm τ)).1 * (if A'.side then 1 else D.R.cc) := by
    intro τ
    apply emb_injective
    rw [← ArchLab.emb_eq, ← ArchLab.emb_eq, ← h τ, ← h' τ]
  obtain ⟨τ0⟩ := tau_nonempty (D := D)
  have hs : A.side = A'.side := by
    have e1 := congrArg (fun g : D.R.GG => g.1.2) (key τ0)
    simp only [Prod.fst_mul, Prod.snd_mul] at e1
    rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau (A.perm τ0)).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau (A'.perm τ0)).2, one_mul, one_mul,
      snd_side, snd_side] at e1
    cases hA : A.side <;> cases hA' : A'.side <;> rw [hA, hA'] at e1 <;> first | rfl | exact absurd e1 (by decide)
  have hp : ∀ τ, A.perm τ = A'.perm τ := by
    intro τ
    have e1 := key τ
    rw [hs] at e1
    exact D.eTau.injective (Subtype.ext (mul_right_cancel e1))
  rcases A with ⟨p, s⟩
  rcases A' with ⟨p', s'⟩
  simp only at hs hp
  subst hs
  congr
  exact Equiv.ext hp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Consider separately whether the proposition holds or fails. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem labExists : LabExists D := by
  intro σ
  obtain ⟨γ, hγ⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have hlab : ∀ τ, labE σ τ = D.host.emb (γ * (D.eTau τ).1) := by
    intro τ
    ext x
    rw [emb_mul', hγ]
    rfl
  by_cases hγP : γ ∈ D.R.Psi
  · let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1, mul_mem hγP (D.eTau τ).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel e1))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), true⟩, fun τ => ?_⟩
    rw [hlab τ]
    simp [ArchLab.emb, tauE, f]
  · have hnot : ∀ τ, γ * (D.eTau τ).1 ∉ D.R.Psi := by
      intro τ hm
      apply hγP
      have h1 : (γ * (D.eTau τ).1).1.2 = 1 := hm
      have h2 : (D.eTau τ).1.1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
      show γ.1.2 = 1
      simpa [Prod.fst_mul, Prod.snd_mul, h2] using h1
    have hmem : ∀ τ, γ * (D.eTau τ).1 * D.R.cc ∈ D.R.Psi := by
      intro τ
      have h1 := hnot τ
      rw [Formalism.HC.Frame.mem_Psi_iff] at h1 ⊢
      show (γ * (D.eTau τ).1).1.2 * (-1) = 1
      rcases Int.units_eq_one_or (γ * (D.eTau τ).1).1.2 with h | h
      · exact absurd h h1
      · rw [h]; rfl
    let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1 * D.R.cc, hmem τ⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel (mul_right_cancel e1)))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), false⟩, fun τ => ?_⟩
    rw [hlab τ, ArchLab.emb_eq]
    simp only [Equiv.ofBijective_apply, f, Equiv.apply_symm_apply, Bool.false_eq_true, if_false]
    rw [mul_assoc (γ * (D.eTau τ).1), cc_mul_cc, mul_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isLabOf_labOf (σ : D.what₂.LL →+* ℂ) : IsLabOf σ (labOf σ) := labOf_spec (labExists σ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem labOf_embLL : labOf (D := D) D.what₂.embLL = baseLab D := labOf_base labUnique

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem labOf_conj (σ : D.what₂.LL →+* ℂ) :
    labOf ((starRingEnd ℂ).comp σ) = (labOf (D := D) σ).flip :=
  labUnique _ _ _ (isLabOf_labOf _) (isLabOf_conj (isLabOf_labOf σ))

end Formalism.IndefR.Conj

end
