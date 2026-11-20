import Formalism.HermitianCurvature.HermitianCurvatureProofs.ArelStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lift

variable {k i r' : ℕ}

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Simplify using `only [ιLev]`. Rewrite using `[dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]`. Apply the tactic sequence `congr 1 <;> ext <;> simp`.
-/
theorem ιLev_apply_lev (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g ⟨p.val + i, by omega⟩ ⟨q.val + i, by omega⟩ = g p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [ιLev]
  rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp

/- English proof (translation)
Use extensionality with `p q`. Use `congrFun (congrFun h ⟨p.val + i, by omega⟩) ⟨q.val + i, by omega⟩` as an intermediate fact. Rewrite `this` using `[ιLev_apply_lev, ιLev_apply_lev]`. Then use the resulting hypothesis.
-/
theorem ιLev_inj' {g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ}
    (h : ιLev k i r' g = ιLev k i r' g') : g = g' := by
  ext p q
  have := congrFun (congrFun h ⟨p.val + i, by omega⟩) ⟨q.val + i, by omega⟩
  rwa [ιLev_apply_lev, ιLev_apply_lev] at this

/- English proof (translation)
Use `contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_` and prove the remaining obligations. Unfold `ιLev`. Use `split_ifs`. Conclude with `(contDiff_apply ℝ ℂ _).comp (contDiff_apply ℝ (Fin (2 * r' + k + 1) → ℂ) _)`. Apply the tactic sequence `all_goals exact contDiff_const`.
-/
theorem contDiff_ιLev' : ContDiff ℝ ∞ (ιLev k i r') := by
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  unfold ιLev
  split_ifs
  · exact (contDiff_apply ℝ ℂ _).comp (contDiff_apply ℝ (Fin (2 * r' + k + 1) → ℂ) _)
  all_goals exact contDiff_const

/- English proof (translation)
Unfold `zetaL`. Rewrite using `[fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]`.
-/
theorem zeta_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    zetaL k (i + r') (liftVec k i r' z) (liftVec k i r' z') (Fin.last (i + r')) (ιLev k i r' g) =
      zetaL k r' z z' (Fin.last r') g := by
  unfold zetaL
  rw [fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]

/- English proof (translation)
Unfold `Tz`. Rewrite using `[PIQnLT.herm_liftVec]`.
-/
theorem tz_lift (z : Fin (2 * r' + k + 1) → ℂ) : Tz k (i + r') (liftVec k i r' z) = Tz k r' z := by
  unfold Tz; rw [PIQnLT.herm_liftVec]

/- English proof (translation)
Unfold `GGl`. Rewrite using `[zeta_lift, tz_lift, tz_lift]`.
-/
theorem ggl_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    GGl k (i + r') (liftVec k i r' z) (liftVec k i r' z') (ιLev k i r' g) = GGl k r' z z' g := by
  unfold GGl; rw [zeta_lift, tz_lift, tz_lift]

/- English proof (translation)
Unfold `fnVal`. Apply the tactic sequence `split <;> simp only [zeta_lift, ggl_lift]`.
-/
theorem fnVal_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (j : Fin 6) (g : Mx k r') :
    fnVal k (i + r') (liftVec k i r' z) (liftVec k i r' z') j (ιLev k i r' g) = fnVal k r' z z' j g := by
  unfold fnVal
  split <;> simp only [zeta_lift, ggl_lift]

/- English proof (translation)
Establish `hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1))` using `Fin.ext (by simp; omega)`. Establish `himg` using `QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'`. Establish `hG : ∀ x : Mx k r', x ∈ Glev k r' (Fin.last r') ↔ x ∈ UH (Hpk k r')` using `fun x => ⟨fun h => h.1, fun h => ⟨h, fun a _ => absurd a.isLt (by omega)⟩⟩`. Rewrite using `[hl, himg, hG]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g0, hg0, e⟩`. Rewrite using `[← ιLev_inj' e]` and apply the resulting hypothesis. Introduce `hg`. Conclude with `⟨g, hg, rfl⟩`.
-/
theorem glev_lift (hr' : r' = 0) (g : Mx k r') :
    ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ↔ g ∈ Glev k r' (Fin.last r') := by
  have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
  have himg := QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'
  have hG : ∀ x : Mx k r', x ∈ Glev k r' (Fin.last r') ↔ x ∈ UH (Hpk k r') := fun x =>
    ⟨fun h => h.1, fun h => ⟨h, fun a _ => absurd a.isLt (by omega)⟩⟩
  rw [hl, himg, hG]
  constructor
  · rintro ⟨g0, hg0, e⟩
    rwa [← ιLev_inj' e]
  · intro hg
    exact ⟨g, hg, rfl⟩

/- English proof (translation)
Use `show (c ∈ OmX (i + r') ∧ ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ∧ 0 < GGl k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') (ιLev k i r' g)) ↔ (c' ∈ OmX r' ∧ g ∈ Glev k r' (Fin.last r') ∧ 0 < GGl k r' zs zs' g)`. Rewrite using `[glev_lift hr', ggl_lift]`. Conclude with `⟨fun h => ⟨fun l => absurd l.isLt (by omega), h.2⟩, fun h => ⟨hc, h.2⟩⟩`.
-/
theorem domR_lift (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (c' : Fin r' → ℂ) (g : Mx k r') :
    (c, ιLev k i r' g) ∈ DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') ↔ (c', g) ∈ DomR k r' zs zs' := by
  show (c ∈ OmX (i + r') ∧ ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ∧
      0 < GGl k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') (ιLev k i r' g)) ↔
    (c' ∈ OmX r' ∧ g ∈ Glev k r' (Fin.last r') ∧ 0 < GGl k r' zs zs' g)
  rw [glev_lift hr', ggl_lift]
  exact ⟨fun h => ⟨fun l => absurd l.isLt (by omega), h.2⟩, fun h => ⟨hc, h.2⟩⟩

def rsF {E : Type*} (c : Fin (i + r') → ℂ) (Φ : Fn k (i + r') E) : Fn k r' E := fun _ g => Φ c (ιLev k i r' g)

end lift

section rs

variable {k i r' : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Take `⟨h0, hs, he⟩` from `hΦ`. Use `⟨fun x hx => h0 _ fun h => hx ((domR_lift hr' hc zs zs' x.1 x.2).1 h), fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩` and prove the remaining obligations. Take `⟨U, F, hU, hxU, hF, hΦF⟩` from `hs _ ((domR_lift hr' hc zs zs' x₀.1 x₀.2).2 hx₀)`. Set `e : (Fin r' → ℂ) × Mx k r' → (Fin (i + r') → ℂ) × Mx k (i + r')` to `fun x => (c, ιLev k i r' x.2)`. Establish `he_c : ContDiff ℝ ∞ e` using `contDiff_const.prodMk (contDiff_ιLev'.comp contDiff_snd)`.

Use `⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx), fun x hx hg => ?_⟩` and prove the remaining obligations. Conclude with `hΦF (e x) hx ((glev_lift hr' x.2).2 hg)`. Establish `hx'` using `(domR_lift hr' hc zs zs' x.1 x.2).2 hx show Φ c (ιLev k i r' (h * x.2 * h')) = _`. Rewrite using `[(PI.QnLevBasicsW.level_group_homomorphism k i r').2, (PI.QnLevBasicsW.level_group_homomorphism k i r').2]`. Conclude with `he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs' h' hh')`.
-/
theorem rs_mem (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)} {Φ : Fn k (i + r') (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    rsF c Φ ∈ RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) := by
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 _ fun h => hx ((domR_lift hr' hc zs zs' x.1 x.2).1 h), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs _ ((domR_lift hr' hc zs zs' x₀.1 x₀.2).2 hx₀)
    let e : (Fin r' → ℂ) × Mx k r' → (Fin (i + r') → ℂ) × Mx k (i + r') := fun x => (c, ιLev k i r' x.2)
    have he_c : ContDiff ℝ ∞ e := contDiff_const.prodMk (contDiff_ιLev'.comp contDiff_snd)
    refine ⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx),
      fun x hx hg => ?_⟩
    exact hΦF (e x) hx ((glev_lift hr' x.2).2 hg)
  · have hx' := (domR_lift hr' hc zs zs' x.1 x.2).2 hx
    show Φ c (ιLev k i r' (h * x.2 * h')) = _
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').2, (PI.QnLevBasicsW.level_group_homomorphism k i r').2]
    exact he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs' h' hh')

def rsL (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (π : Mx k (i + r') → (Wp →L[ℂ] Wp)) (π' : Mx k (i + r') → (Wq →L[ℂ] Wq)) :
    RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π' →ₗ[ℂ]
      RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) where
  toFun Φ := ⟨rsF c (Φ : Fn k (i + r') (Wq →L[ℂ] Wp)), rs_mem hr' hc Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
  {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c' g`. Distinguish the cases in `hx : (c', g) ∈ DomR k r' zs zs'`. Establish `hx'` using `(domR_lift hr' hc zs zs' c' g).2 hx`. Rewrite using `[X.t_apply Y a b _ (c', g) hx]`.

Use `show _ = (X₀.t Y a b Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)`. Rewrite using `[X₀.t_apply Y a b Φ (c, ιLev k i r' g) hx']`. Establish `hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1))` using `Fin.ext (by simp; omega)`. Establish `h0 : (Fin.last r') = (0 : Fin (r' + 1))` using `Fin.ext (by simp; omega)`. Rewrite using `[hl, h0]`.

Conclude with `(Formalism.FourierDecayAlt.P.level_transfer _ k i r' zs zs' Y a b ((Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c) g hx.2.1.1).symm`. Rewrite using `[(X.t Y a b (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]`. Conclude with `((X₀.t Y a b Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm`.
-/
theorem t_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.t Y a b (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.t Y a b Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.t_apply Y a b _ (c', g) hx]
    show _ = (X₀.t Y a b Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.t_apply Y a b Φ (c, ιLev k i r' g) hx']
    have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
    have h0 : (Fin.last r') = (0 : Fin (r' + 1)) := Fin.ext (by simp; omega)
    rw [hl, h0]
    exact (Formalism.FourierDecayAlt.P.level_transfer _ k i r' zs zs' Y a b ((Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c) g
      hx.2.1.1).symm
  · rw [(X.t Y a b (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.t Y a b Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c' g`. Distinguish the cases in `hx : (c', g) ∈ DomR k r' zs zs'`. Establish `hx'` using `(domR_lift hr' hc zs zs' c' g).2 hx`. Rewrite using `[X.fn_apply j _ (c', g) hx]`.

Use `show _ = (X₀.fn j Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)`. Rewrite using `[X₀.fn_apply j Φ (c, ιLev k i r' g) hx', fnVal_lift]`. Both sides reduce to the same expression. Rewrite using `[(X.fn j (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]`. Conclude with `((X₀.fn j Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm`.
-/
theorem fn_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (j : Fin 6)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.fn j (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.fn j Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.fn_apply j _ (c', g) hx]
    show _ = (X₀.fn j Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.fn_apply j Φ (c, ιLev k i r' g) hx', fnVal_lift]
    rfl
  · rw [(X.fn j (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.fn j Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

end rs

end Formalism.FourierDecayAlt.P.WordCorrespondence
