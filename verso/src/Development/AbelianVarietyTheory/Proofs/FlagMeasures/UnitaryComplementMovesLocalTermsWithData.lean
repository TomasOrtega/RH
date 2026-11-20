import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.LocalMove

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP h hh d d' τ hτ hmv`. Use `letI := hM.loc`. Use `haveI := hM.char0`. Take `⟨S, ⟨c⟩⟩` from `GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrk hP`. Take `⟨hH0, -, -, hlat, -⟩` from `GlobalTheory.HL.CoordMass.transport M hM H r k P S c`.

Take `⟨-, hmov, -⟩` from `GlobalTheory.HL.CoordDatum.transport M hM H r k P S c`. Take `⟨-, hNA, hNB, -⟩` from `GlobalTheory.HL.CoordUnip.transport M hM H r k P S c`. Establish `hh0 : c.grp h ∈ S.H0` using `(hH0 h).1 hh`. Establish `ge : ∀ (g : V ≃ₗ[E] V) (x : V), c.grp g (c.e x) = c.e (g x)` using `GlobalTheory.HL.CoordTerm.grp_e c`. Take `⟨Λ, f, f', T, T'⟩` from `τ`.

Take `⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, hG⟩` from `hτ`. Simplify using `only at hT hT' hf hΛ hf' hΛ' hG ⊢`. Substitute `hT hT' hf hf'` using the available equality. Establish `fixA : ∀ b, h (n (P.A.f b)) = n (P.A.f b)`. Introduce `b`.

Apply `c.e.injective` to reduce the goal to its premises. Rewrite using `[← ge, ← ge, ← c.f_eq]`. Conclude with `GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_left (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn) (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))`. Establish `fixB : ∀ b, h (n' (P.B.f b)) = n' (P.B.f b)`. Introduce `b`.

Apply `c.e.injective` to reduce the goal to its premises. Rewrite using `[← ge, ← ge, ← c.f'_eq]`. Conclude with `GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_right (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn') (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))`. Simplify using `only [fixA, fixB]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hW` using `(GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1 ⟨⟨rfl, rfl, ⟨n, hn, rfl, hΛ⟩, ⟨n', hn', rfl, hΛ'⟩, hG⟩, hn, hn', hΛ, hΛ'⟩`. Take `⟨m, m', hW', hm, hm'⟩` from `GlobalTheory.HL.ComplAct.termW S hW hh0`. Rewrite `hW'` using `[(hmov h hh d d').1 hmv, ← hlat]`. Take `⟨m0, rfl⟩` from `c.grp.surjective m`. Take `⟨m0', rfl⟩` from `c.grp.surjective m'`.

Establish `e1 : (fun b => m0 (P.A.f b)) = fun b => n (P.A.f b)`. Use function extensionality and compare the values at `b`. Apply `c.e.injective` to reduce the goal to its premises. Rewrite using `[← ge, ← ge, ← c.f_eq]`. Conclude with `hm b`.

Establish `e2 : (fun b => m0' (P.B.f b)) = fun b => n' (P.B.f b)`. Use function extensionality and compare the values at `b`. Apply `c.e.injective` to reduce the goal to its premises. Rewrite using `[← ge, ← ge, ← c.f'_eq]`. Conclude with `hm' b`.

Use `((GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' m0 m0' (LocNG.img h Λ)).2 hW').1` as an intermediate fact. Rewrite `this` using `[e1, e2]`. Conclude with `this`. Use `set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with ht`. Establish `fam : ∀ i, h (H.MMfam t i) = H.MMfam t i`.

Introduce `i`. Unfold `HermSp.MMfam`. Consider the cases of `M.split with`. Consider the case `none => rcases i with b | b <;> simp [ht, fixA, fixB]`. Consider the case `some g => rcases i with b | b <;> simp [ht, fixA, fixB, map_sub]`.

Establish `fixS : ∀ x ∈ Submodule.span E (Set.range (H.MMfam t)), h x = x`. Introduce `x hx`. Use `LinearMap.eqOn_span' (f := (h : V →ₗ[E] V)) (g := LinearMap.id) (s := Set.range (H.MMfam t)) (by rintro _ ⟨i, rfl⟩; exact fam i) hx` as an intermediate fact. Simplify using `using this`. Express the relevant statement in the definitionally equal form `(∃ v ∈ LocNG.img h Λ, _) ↔ ∃ v ∈ Λ, _`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hE, hO⟩`. Take `⟨w, hw, rfl⟩` from `hv`. Establish `hw' : h w = w`. Use `fixS _ hE` as an intermediate fact.

Conclude with `h.injective (by simpa using this)`. Simplify using `only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hE hO ⊢`. Rewrite `hE`, `hO` using `[hw']`. Conclude with `⟨w, hw, hE, hO⟩`. Introduce and unpack `⟨v, hv, hE, hO⟩`.

Conclude with `⟨v, ⟨v, hv, fixS v hE⟩, hE, hO⟩`.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP h hh d d' τ hτ hmv
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨hH0, -, -, hlat, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, hmov, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh0 : c.grp h ∈ S.H0 := (hH0 h).1 hh
  have ge : ∀ (g : V ≃ₗ[E] V) (x : V), c.grp g (c.e x) = c.e (g x) := GlobalTheory.HL.CoordTerm.grp_e c
  obtain ⟨Λ, f, f', T, T'⟩ := τ
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, hG⟩ := hτ
  dsimp only at hT hT' hf hΛ hf' hΛ' hG ⊢
  subst hT hT' hf hf'

  have fixA : ∀ b, h (n (P.A.f b)) = n (P.A.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_left
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn) (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  have fixB : ∀ b, h (n' (P.B.f b)) = n' (P.B.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f'_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_right
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn') (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  simp only [fixA, fixB]
  refine ⟨?_, ?_⟩
  · have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1
      ⟨⟨rfl, rfl, ⟨n, hn, rfl, hΛ⟩, ⟨n', hn', rfl, hΛ'⟩, hG⟩, hn, hn', hΛ, hΛ'⟩
    obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hh0
    rw [(hmov h hh d d').1 hmv, ← hlat] at hW'
    obtain ⟨m0, rfl⟩ := c.grp.surjective m
    obtain ⟨m0', rfl⟩ := c.grp.surjective m'
    have e1 : (fun b => m0 (P.A.f b)) = fun b => n (P.A.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f_eq]; exact hm b
    have e2 : (fun b => m0' (P.B.f b)) = fun b => n' (P.B.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f'_eq]; exact hm' b
    have := ((GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' m0 m0' (LocNG.img h Λ)).2 hW').1
    rw [e1, e2] at this
    exact this
  ·
    set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with ht
    have fam : ∀ i, h (H.MMfam t i) = H.MMfam t i := by
      intro i
      unfold HermSp.MMfam
      cases M.split with
      | none => rcases i with b | b <;> simp [ht, fixA, fixB]
      | some g => rcases i with b | b <;> simp [ht, fixA, fixB, map_sub]
    have fixS : ∀ x ∈ Submodule.span E (Set.range (H.MMfam t)), h x = x := by
      intro x hx
      have := LinearMap.eqOn_span' (f := (h : V →ₗ[E] V)) (g := LinearMap.id)
        (s := Set.range (H.MMfam t)) (by rintro _ ⟨i, rfl⟩; exact fam i) hx
      simpa using this
    change (∃ v ∈ LocNG.img h Λ, _) ↔ ∃ v ∈ Λ, _
    constructor
    · rintro ⟨v, hv, hE, hO⟩
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : h w = w := by
        have := fixS _ hE
        exact h.injective (by simpa using this)
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hE hO ⊢
      rw [hw'] at hE hO
      exact ⟨w, hw, hE, hO⟩
    · rintro ⟨v, hv, hE, hO⟩
      exact ⟨v, ⟨v, hv, fixS v hE⟩, hE, hO⟩

end GlobalTheory.HL.LocalMove
