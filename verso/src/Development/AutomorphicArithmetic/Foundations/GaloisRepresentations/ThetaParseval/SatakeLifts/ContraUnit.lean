import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqMapBijective

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc

/- English proof (translation)
Introduce `hci k _ _ _ _ n V _ _ ρ hsm hirr hu`. Take `⟨B, hherm, hpos, hinv⟩` from `hu`. Establish `hnd : ∀ w : V, (∀ v : V, B v w = 0) → w = 0`. Introduce `w hw`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hpos w hne`. Rewrite `h1` using `[hw w]`. Simplify using `at h1`. Choose the witnesses or unpack the hypotheses as in `⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Use `haveI : IsSimpleOrder (Subrepresentation ρ) := hirr`. Apply `(bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)` to reduce the goal to its premises. Generalize the expression as in `(⊥ : Subrepresentation ρ) = a`. Generalize the expression as in `(⊤ : Subrepresentation ρ) = b`.

Take `⟨A, hA⟩` from `a`. Take `⟨A', hA'⟩` from `b`. Use `congr 1`. Use extensionality with `x`. Rewrite using `[hne x]`.

Simplify using `only [Submodule.zero_mem]`. Establish `hcirr : (contra ρ).IsIrreducible` using `(hci k n V ρ hsm hirr).1`. Establish `hbij` using `GlobalTheory.HermDualSelf.sesqMap_bijective ρ hsm B hinv hnd ⟨w0, hw0⟩ hcirr`. Establish `hcomm` using `GlobalTheory.HermDualSelf.sesqMap_comm ρ hsm B hinv`. Use `set S := GlobalTheory.HermDualSelf.sesqMap ρ hsm B hinv with hS`.

Set `e` to `LinearEquiv.ofBijective S hbij`. Set `T : ↥(GlobalTheory.PRep.smoothPart ρ.dual) →ₗ⋆[ℂ] V` to `e.symm.toLinearMap`. Establish `hST : ∀ f, S (T f) = f` using `fun f => e.apply_symm_apply f`. Establish `hTS : ∀ w, T (S w) = w` using `fun w => e.symm_apply_apply w`. Establish `hTg : ∀ g f, T (contra ρ g f) = ρ g (T f)`.

Introduce `g f`. Rewrite using `[← hST f, ← hcomm, hTS, hTS]`. Use `⟨⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => B (T f') (T f)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, ⟨e, fun g x => hcomm g x⟩⟩` and prove the remaining obligations. Introduce `f₁ f₂ f'`. Simplify using `[map_add]`.

Introduce `c f f'`. Simplify using `[LinearMap.map_smulₛₗ]`. Introduce `f f₁ f₂`. Simplify using `[map_add]`. Introduce `c f f'`.

Simplify using `[LinearMap.map_smulₛₗ]`. Introduce `f f'`. Simplify using `only [LinearMap.mk₂'ₛₗ_apply]`. Conclude with `hherm (T f') (T f)`. Introduce `f hf`.

Simplify using `only [LinearMap.mk₂'ₛₗ_apply]`. Conclude with `hpos _ (fun h => hf (by rw [← hST f, h, map_zero]))`. Introduce `g f f'`. Simplify using `only [LinearMap.mk₂'ₛₗ_apply]`. Rewrite using `[hTg, hTg]`.

Conclude with `hinv g _ _`.
-/
theorem UpperTheory.Gal.TP.Loc.contraUnit :
    UpperTheory.Gal.TP.Loc.ContraIrr → UpperTheory.Gal.TP.Loc.ContraUnit := by
  intro hci k _ _ _ _ n V _ _ ρ hsm hirr hu
  obtain ⟨B, hherm, hpos, hinv⟩ := hu
  have hnd : ∀ w : V, (∀ v : V, B v w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hpos w hne
    rw [hw w] at h1
    simp at h1
  obtain ⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    generalize (⊥ : Subrepresentation ρ) = a
    generalize (⊤ : Subrepresentation ρ) = b
    obtain ⟨A, hA⟩ := a
    obtain ⟨A', hA'⟩ := b
    congr 1
    ext x
    rw [hne x]
    simp only [Submodule.zero_mem]
  have hcirr : (contra ρ).IsIrreducible := (hci k n V ρ hsm hirr).1
  have hbij := GlobalTheory.HermDualSelf.sesqMap_bijective ρ hsm B hinv hnd ⟨w0, hw0⟩ hcirr
  have hcomm := GlobalTheory.HermDualSelf.sesqMap_comm ρ hsm B hinv
  set S := GlobalTheory.HermDualSelf.sesqMap ρ hsm B hinv with hS
  let e := LinearEquiv.ofBijective S hbij
  let T : ↥(GlobalTheory.PRep.smoothPart ρ.dual) →ₗ⋆[ℂ] V := e.symm.toLinearMap
  have hST : ∀ f, S (T f) = f := fun f => e.apply_symm_apply f
  have hTS : ∀ w, T (S w) = w := fun w => e.symm_apply_apply w
  have hTg : ∀ g f, T (contra ρ g f) = ρ g (T f) := by
    intro g f
    rw [← hST f, ← hcomm, hTS, hTS]
  refine ⟨⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => B (T f') (T f))
    ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, ⟨e, fun g x => hcomm g x⟩⟩
  · intro f₁ f₂ f'
    simp [map_add]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f₁ f₂
    simp [map_add]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm (T f') (T f)
  · intro f hf
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hpos _ (fun h => hf (by rw [← hST f, h, map_zero]))
  · intro g f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [hTg, hTg]
    exact hinv g _ _
