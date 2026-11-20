import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.AdmissibleStableUnderFrameChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.MemSpanImageEquiv

noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `v`. Establish `hmap : XS D F₂.fl = (XS D x.fl).map ((γ.restrictScalars (𝓞 D.host.E) : (VS D).V ≃ₗ[𝓞 D.host.E] (VS D).V) : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V)`. Unfold `XS`. Rewrite using `[Submodule.map_span]`. Use `congr 1`.

Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, c, hc, rfl⟩`. Conclude with `⟨c • x.fl.e a, ⟨a, c, hc, rfl⟩, by simp [he]⟩`.

Introduce and unpack `⟨_, ⟨a, c, hc, rfl⟩, rfl⟩`. Conclude with `⟨a, c, hc, by simp [he]⟩`. Rewrite using `[hmap, Submodule.mem_map_equiv]`. Both sides reduce to the same expression.
-/
theorem tr_XS (D : D7) {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (VS D) D.R.rS T'} (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    Tr γ (XS D F₂.fl) (XS D x.fl) := by
  intro v
  have hmap : XS D F₂.fl = (XS D x.fl).map
      ((γ.restrictScalars (𝓞 D.host.E) : (VS D).V ≃ₗ[𝓞 D.host.E] (VS D).V) :
        (VS D).V →ₗ[𝓞 D.host.E] (VS D).V) := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, c, hc, rfl⟩
      exact ⟨c • x.fl.e a, ⟨a, c, hc, rfl⟩, by simp [he]⟩
    · rintro ⟨_, ⟨a, c, hc, rfl⟩, rfl⟩
      exact ⟨a, c, hc, by simp [he]⟩
  rw [hmap, Submodule.mem_map_equiv]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fixedConv_tr Λ (gS D) hΛ he hz hiso hx.1, Tr.eq (tr_XLam Λ hΛ he) (tr_XS D he) hx.2⟩`.
-/
theorem frameOK_tr (D : D7) {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (VS D) D.R.rS T'} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Tr γ Λ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z)
    (hiso : ∀ a b, (VS D).hT (γ a) (γ b) = (VS D).hT a b) (hx : FrameOK D Λ x) : FrameOK D Λ F₂ :=
  ⟨fixedConv_tr Λ (gS D) hΛ he hz hiso hx.1, Tr.eq (tr_XLam Λ hΛ he) (tr_XS D he) hx.2⟩

/- English proof (translation)
Introduce `F0 Λ hΛ x F₂ hDC`. Take `⟨hxl, hxa, hxf⟩` from `x.2`. Take `⟨n, hn, m, hm, hfr, hzt⟩` from `hDC`. Take `⟨_, ⟨_, _, hFl, hFc⟩, _⟩` from `hΛ`. Establish `hΛn : Tr n Λ Λ` using `tr_of_gmap hn.1.2`.

Establish `hΛm : Tr m Λ Λ` using `tr_of_gmap hm.1.2`. Establish `hΛγ : Tr (m.trans n) Λ Λ`. Introduce `v`. Rewrite using `[LinearEquiv.symm_trans_apply, ← hΛm, ← hΛn]`. Establish `hn1 : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b` using `hn.1.1`.

Establish `hm1 : ∀ a b, (VS D).hT (m a) (m b) = (VS D).hT a b` using `hm.1.1`. Establish `hiso : ∀ a b, (VS D).hT ((m.trans n) a) ((m.trans n) b) = (VS D).hT a b`. Introduce `a b`. Rewrite using `[LinearEquiv.trans_apply, LinearEquiv.trans_apply, hn1, hm1]`. Establish `he : ∀ k, F₂.fl.e k = (m.trans n) (x.1.fl.e k)`.

Introduce `k`. Use `hfr k.castSucc` as an intermediate fact. Rewrite `this` using `[frame_castSucc, frame_castSucc]`. Then use the resulting hypothesis. Establish `hz : F₂.fl.z = (m.trans n) x.1.fl.z`. Use `hfr (Fin.last _)` as an intermediate fact.

Rewrite `this` using `[frame_last, frame_last]`. Then use the resulting hypothesis. Conclude with `⟨isLift_tr Λ hΛγ hz hzt hxl, admissible_stable_under_frame_change Λ (gS D) (lf D F0) x.1 F₂ hFl.1 hFc hxl.1 hxf.1 hxa n hn m hm hfr, frameOK_tr D Λ hΛγ he hz hiso hxf⟩`.
-/
theorem termStable_holds (D : D7) (u u' : D.what₂.Word) : TermStable D u u' := by
  intro F0 Λ hΛ x F₂ hDC
  obtain ⟨hxl, hxa, hxf⟩ := x.2
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := hDC
  obtain ⟨_, ⟨_, _, hFl, hFc⟩, _⟩ := hΛ
  have hΛn : Tr n Λ Λ := tr_of_gmap hn.1.2
  have hΛm : Tr m Λ Λ := tr_of_gmap hm.1.2
  have hΛγ : Tr (m.trans n) Λ Λ := by
    intro v
    rw [LinearEquiv.symm_trans_apply, ← hΛm, ← hΛn]
  have hn1 : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b := hn.1.1
  have hm1 : ∀ a b, (VS D).hT (m a) (m b) = (VS D).hT a b := hm.1.1
  have hiso : ∀ a b, (VS D).hT ((m.trans n) a) ((m.trans n) b) = (VS D).hT a b := by
    intro a b
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hn1, hm1]
  have he : ∀ k, F₂.fl.e k = (m.trans n) (x.1.fl.e k) := by
    intro k
    have := hfr k.castSucc
    rwa [frame_castSucc, frame_castSucc] at this
  have hz : F₂.fl.z = (m.trans n) x.1.fl.z := by
    have := hfr (Fin.last _)
    rwa [frame_last, frame_last] at this
  exact ⟨isLift_tr Λ hΛγ hz hzt hxl,
    admissible_stable_under_frame_change Λ (gS D) (lf D F0) x.1 F₂ hFl.1 hFc hxl.1 hxf.1 hxa n hn m hm hfr,
    frameOK_tr D Λ hΛγ he hz hiso hxf⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨lf D F0, pd_self F0 Λ hΛ⟩, lf D F0, 1, one_mem_NLam Λ _, 1, one_mem_NLam Λ _, fun _ => rfl, rfl⟩`.
-/
theorem hyp_inhabited (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) :
    ∃ (x : Carrier (PD D Λ (lf D F0) u)) (F₂ : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)),
      DCRel Λ (lf D F0) x.1 F₂ :=
  ⟨⟨lf D F0, pd_self F0 Λ hΛ⟩, lf D F0, 1, one_mem_NLam Λ _, 1, one_mem_NLam Λ _, fun _ => rfl, rfl⟩

end D7

end PI.TCS
