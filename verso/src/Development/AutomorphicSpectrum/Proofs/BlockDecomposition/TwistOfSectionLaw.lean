import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisTwist

open PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma ch_mul (h : IsCh Γ ⊤ c₀) (a b : G) : c₀ (a * b) = c₀ a * c₀ b :=
  h.mul a (Subgroup.mem_top a) b (Subgroup.mem_top b)

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma ch_one (h : IsCh Γ ⊤ c₀) : c₀ 1 = 1 :=
  h.rat 1 (one_mem _) (Subgroup.mem_top 1)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma ch_rat_mul (h : IsCh Γ ⊤ c₀) {γ : G} (hγ : γ ∈ Γ) (g : G) : c₀ (γ * g) = c₀ g := by
  rw [ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma ch_norm (h : IsCh Γ ⊤ c₀) (g : G) : ‖c₀ g‖ = 1 :=
  h.norm g (Subgroup.mem_top g)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma ch_cont (h : IsCh Γ ⊤ c₀) : Continuous c₀ := by
  have h' := h.cont
  rw [Subgroup.coe_top] at h'
  exact continuousOn_univ.mp h'

def twRep (h : IsCh Γ ⊤ c₀) (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) : K →* (W →L[ℂ] W) where
  toFun r := c₀ r • ρ r
  map_one' := by simp [ch_one h]
  map_mul' a b := by
    ext w
    simp [ch_mul h, smul_smul, mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma twRep_apply (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (r : K) :
    twRep h K ρ r = c₀ r • ρ r := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma twRep_cont (h : IsCh Γ ⊤ c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous (twRep h K ρ) :=
  ((ch_cont h).comp continuous_subtype_val).smul hρ

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
lemma secSp_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) :
    secSp K P (c * c₀) ρ = secSp K P c (twRep h K ρ) := by
  ext w
  have key : ∀ r : K, (c * c₀) (r : G) • ρ r w = c (r : G) • twRep h K ρ r w := fun r => by
    rw [twRep_apply, ContinuousLinearMap.smul_apply, smul_smul, Pi.mul_apply]
  change (∀ r : K, (r : G) ∈ P → (c * c₀) (r : G) • ρ r w = w) ↔
    ∀ r : K, (r : G) ∈ P → c (r : G) • twRep h K ρ r w = w
  simp only [key]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities.
-/
lemma sec_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (g : G) :
    sec K P (c * c₀) ρ g = c₀ g • sec K P c (twRep h K ρ) g := by
  unfold sec
  by_cases hk : ∃ k : K, g * (k : G)⁻¹ ∈ P
  · rw [dif_pos hk, dif_pos hk, twRep_apply, Pi.mul_apply, Subgroup.coe_inv, ch_mul h g, smul_smul, smul_smul]
    congr 1
    ring
  · rw [dif_neg hk, dif_neg hk, smul_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma eis_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (Λ : G → ℂ)
    (g : G) (w : W) :
    eis Γ K P (c * c₀) ρ Λ g w = c₀ g • eis Γ K P c (twRep h K ρ) Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [sec_twist h, ContinuousLinearMap.smul_apply, ch_rat_mul h hq, smul_comm]

def castL {A B : Submodule ℂ W} (e : A = B) : A →L[ℂ] B :=
  (ContinuousLinearEquiv.ofEq A B e).toContinuousLinearMap

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
lemma leftGood_cast {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {A B : Submodule ℂ W} (e : A = B)
    {Op : ℂ → (X →L[ℂ] A)} {a : ℝ} (hO : LeftGood Op a) :
    LeftGood (fun z => (castL e).comp (Op z)) a := by
  subst e
  have hid : (fun z => (castL (rfl : A = A)).comp (Op z)) = Op := by
    funext z
    ext x
    rfl
  rwa [hid]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
lemma wall_twist (h : IsCh Γ ⊤ c₀) {P P' : Subgroup G} {c : G → ℂ} {η η' β : G → ℝ}
    {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W} {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (L →L[ℂ] secSp K P' c (twRep h K ρ))} {H : ℂ → G → (L →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β (twRep h K ρ) L R D Op H) :
    Wall Γ K P P' (c * c₀) η η' β ρ L R D
      (fun z => (castL (secSp_twist h ρ P' c).symm).comp (Op z)) (fun z g => c₀ g • H z g) where
  le := by
    rw [secSp_twist h ρ P c]
    exact hw.le
  pos := hw.pos
  convR := hw.convR
  convL := hw.convL
  dEnt := hw.dEnt
  dNe := hw.dNe
  op := leftGood_cast _ hw.op
  hol g := (hw.hol g).const_smul (c₀ g)
  cont := ((ch_cont h).comp continuous_snd).smul hw.cont
  bdd b a g := by
    obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g
    refine ⟨U, hU, M, fun z h1 h2 g' hg' => ?_⟩
    rw [norm_smul, ch_norm h, one_mul]
    exact hM z h1 h2 g' hg'
  eqR z hz g w := by
    rw [ContinuousLinearMap.smul_apply, hw.eqR z hz g w, eis_twist h, smul_comm]
  eqL z hz g w := by
    rw [ContinuousLinearMap.smul_apply, hw.eqL z hz g w, eis_twist h]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem twist : SecLaw → Twist := by
  intro _ G _ _ _ _ _ Γ K S P P' c c₀ η η' β ξ N _ h _ _ _
  refine ⟨fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_⟩
  · obtain ⟨R, D, Op, H, hw⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasWall
    rw [secSp_twist h ρ P c]
    exact ⟨R, D, _, _, wall_twist h hw⟩
  · obtain ⟨R, D, Op, H, hw, ⟨a, ha0, ha⟩, O, hO, hOp⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasFirst
    rw [secSp_twist h ρ S c]
    refine ⟨R, D, _, _, wall_twist h hw, ⟨a, ha0, fun g w => ?_⟩,
      fun z => (castL (secSp_twist h ρ P' c).symm).comp (O z), leftGood_cast _ hO, fun z hz => ?_⟩
    · rw [ContinuousLinearMap.smul_apply, ha g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]
    · change (castL (secSp_twist h ρ P' c).symm).comp (Op z) = _
      rw [hOp z hz, ContinuousLinearMap.comp_smul]
  · obtain ⟨R, D, Op, H, hw, hd, T, hT⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasLast
    rw [secSp_twist h ρ P c]
    refine ⟨R, D, _, _, wall_twist h hw, hd,
      (castL (secSp_twist h ρ S c).symm).comp T, fun g w => ?_⟩
    rw [ContinuousLinearMap.smul_apply, hT g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]
    rfl

end GlobalTheory.CompanionTheory.RgEisTwist
