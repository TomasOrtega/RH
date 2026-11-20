import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisTwist

open PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}

/- English proof (translation)
The claim follows from `h.mul a (Subgroup.mem_top a) b (Subgroup.mem_top b)`.
-/
lemma ch_mul (h : IsCh Γ ⊤ c₀) (a b : G) : c₀ (a * b) = c₀ a * c₀ b :=
  h.mul a (Subgroup.mem_top a) b (Subgroup.mem_top b)

/- English proof (translation)
The claim follows from `h.rat 1 (one_mem _) (Subgroup.mem_top 1)`.
-/
lemma ch_one (h : IsCh Γ ⊤ c₀) : c₀ 1 = 1 :=
  h.rat 1 (one_mem _) (Subgroup.mem_top 1)

/- English proof (translation)
Rewrite using `[ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]`.
-/
lemma ch_rat_mul (h : IsCh Γ ⊤ c₀) {γ : G} (hγ : γ ∈ Γ) (g : G) : c₀ (γ * g) = c₀ g := by
  rw [ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]

/- English proof (translation)
The claim follows from `h.norm g (Subgroup.mem_top g)`.
-/
lemma ch_norm (h : IsCh Γ ⊤ c₀) (g : G) : ‖c₀ g‖ = 1 :=
  h.norm g (Subgroup.mem_top g)

/- English proof (translation)
Establish `h'` using `h.cont`. Rewrite `h'` using `[Subgroup.coe_top]`. Conclude with `continuousOn_univ.mp h'`.
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
The claim follows from `((ch_cont h).comp continuous_subtype_val).smul hρ`.
-/
lemma twRep_cont (h : IsCh Γ ⊤ c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous (twRep h K ρ) :=
  ((ch_cont h).comp continuous_subtype_val).smul hρ

/- English proof (translation)
Use extensionality with `w`. Establish `key : ∀ r : K, (c * c₀) (r : G) • ρ r w = c (r : G) • twRep h K ρ r w` using `fun r => by`. Rewrite using `[twRep_apply, ContinuousLinearMap.smul_apply, smul_smul, Pi.mul_apply]`. Express the relevant statement in the definitionally equal form `(∀ r : K, (r : G) ∈ P → (c * c₀) (r : G) • ρ r w = w) ↔ ∀ r : K, (r : G) ∈ P → c (r : G) • twRep h K ρ r w = w`. Simplify using `only [key]`.
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
Unfold `sec`. Distinguish the cases in `hk : ∃ k : K, g * (k : G)⁻¹ ∈ P`. Rewrite using `[dif_pos hk, dif_pos hk, twRep_apply, Pi.mul_apply, Subgroup.coe_inv, ch_mul h g, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[dif_neg hk, dif_neg hk, smul_zero]`.
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
Unfold `eis`. Rewrite using `[← tsum_const_smul'']`. Use `tsum_congr fun q => ?_` and prove the remaining obligations. Establish `hq : rep q ∈ Γ` using `(Quotient.out q).2`. Rewrite using `[sec_twist h, ContinuousLinearMap.smul_apply, ch_rat_mul h hq, smul_comm]`.
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
Substitute `e` using the available equality. Establish `hid : (fun z => (castL (rfl : A = A)).comp (Op z)) = Op`. Use function extensionality and compare the values at `z`. Use extensionality with `x`. Both sides reduce to the same expression.

Rewrite using `[hid]` and apply the resulting hypothesis.
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
Rewrite using `[secSp_twist h ρ P c]`. Conclude with `hw.le`. Use `pos := hw.pos`. Use `convR := hw.convR`. Use `convL := hw.convL`.

Use `dEnt := hw.dEnt`. Use `dNe := hw.dNe`. Use `op := leftGood_cast _ hw.op`. Use `hol g := (hw.hol g).const_smul (c₀ g)`. Use `cont := ((ch_cont h).comp continuous_snd).smul hw.cont`.

Use `bdd b a g := by`. Take `⟨U, hU, M, hM⟩` from `hw.bdd b a g`. Use `⟨U, hU, M, fun z h1 h2 g' hg' => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, ch_norm h, one_mul]`. Conclude with `hM z h1 h2 g' hg'`.

Use `eqR z hz g w := by`. Rewrite using `[ContinuousLinearMap.smul_apply, hw.eqR z hz g w, eis_twist h, smul_comm]`. Use `eqL z hz g w := by`. Rewrite using `[ContinuousLinearMap.smul_apply, hw.eqL z hz g w, eis_twist h]`. Both sides reduce to the same expression.
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
Introduce `_ G _ _ _ _ _ Γ K S P P' c c₀ η η' β ξ N _ h _ _ _`. Use `⟨fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_⟩` and prove the remaining obligations. Take `⟨R, D, Op, H, hw⟩` from `hA W (twRep h K ρ) (twRep_cont h hρ)`. Unfold `HasWall`. Rewrite using `[secSp_twist h ρ P c]`.

Conclude with `⟨R, D, _, _, wall_twist h hw⟩`. Take `⟨R, D, Op, H, hw, ⟨a, ha0, ha⟩, O, hO, hOp⟩` from `hA W (twRep h K ρ) (twRep_cont h hρ)`. Unfold `HasFirst`. Rewrite using `[secSp_twist h ρ S c]`. Use `⟨R, D, _, _, wall_twist h hw, ⟨a, ha0, fun g w => ?_⟩, fun z => (castL (secSp_twist h ρ P' c).symm).comp (O z), leftGood_cast _ hO, fun z hz => ?_⟩` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.smul_apply, ha g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]`. Express the relevant statement in the definitionally equal form `(castL (secSp_twist h ρ P' c).symm).comp (Op z) = _`. Rewrite using `[hOp z hz, ContinuousLinearMap.comp_smul]`. Take `⟨R, D, Op, H, hw, hd, T, hT⟩` from `hA W (twRep h K ρ) (twRep_cont h hρ)`. Unfold `HasLast`.

Rewrite using `[secSp_twist h ρ P c]`. Use `⟨R, D, _, _, wall_twist h hw, hd, (castL (secSp_twist h ρ S c).symm).comp T, fun g w => ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.smul_apply, hT g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]`. Both sides reduce to the same expression.
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
