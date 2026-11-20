import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmGLBridge

/- English proof (translation)
Introduce `k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ p h1 h2`. Establish `hblk : ∀ x y, β x = β y ↔ blk e x = blk e y`. Introduce `x y`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h3` using `(hβ x y).not.1 (by omega)`. Establish `h4` using `(hβ y x).not.1 (by omega)`. Conclude with `le_antisymm (not_lt.1 h4) (not_lt.1 h3)`. Introduce `h`. Establish `h3` using `(hβ x y).not.2 (by rw [h]; exact lt_irrefl _)`.

Establish `h4` using `(hβ y x).not.2 (by rw [h]; exact lt_irrefl _)`. Use linear arithmetic over natural numbers and integers. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.ext` to reduce the goal to its premises.

Introduce `x y`. Rewrite using `[hφ]`. Rewrite using `[show ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ : levi k N β) : GL (Fin N) k).val x y = _ from GroundTheory.Automorphic.Parabolic.leviProj_apply _ x y]`. Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective x`. Take `⟨⟨b, j⟩, rfl⟩` from `e.surjective y`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos ((hblk _ _).2 (by simp))]`. Use `leviEmb_apply_same k e (leviProj k e ⟨p, h1⟩) a i j` as an intermediate fact. Rewrite using `[this, leviProj_apply]`.

Rewrite using `[if_neg (fun h => hab (by simpa using (hblk _ _).1 h))]`. Conclude with `leviEmb_apply_ne k e _ hab i j`.
-/
theorem leviProj_found_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ p h1 h2
  have hblk : ∀ x y, β x = β y ↔ blk e x = blk e y := by
    intro x y
    constructor
    · intro h
      have h3 := (hβ x y).not.1 (by omega)
      have h4 := (hβ y x).not.1 (by omega)
      exact le_antisymm (not_lt.1 h4) (not_lt.1 h3)
    · intro h
      have h3 := (hβ x y).not.2 (by rw [h]; exact lt_irrefl _)
      have h4 := (hβ y x).not.2 (by rw [h]; exact lt_irrefl _)
      omega
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro x y
  rw [hφ]
  rw [show ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ : levi k N β) : GL (Fin N) k).val x y = _ from GroundTheory.Automorphic.Parabolic.leviProj_apply _ x y]
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases hab : a = b
  · subst hab
    rw [if_pos ((hblk _ _).2 (by simp))]
    have := leviEmb_apply_same k e (leviProj k e ⟨p, h1⟩) a i j
    rw [this, leviProj_apply]
  · rw [if_neg (fun h => hab (by simpa using (hblk _ _).1 h))]
    exact leviEmb_apply_ne k e _ hab i j

end GlobalTheory.CompanionTheory.SmGLBridge
