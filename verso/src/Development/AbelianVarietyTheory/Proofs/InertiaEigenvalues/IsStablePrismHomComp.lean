import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
The claim follows from `Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)`.
-/
theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {B C D : Obj l R} (h : Hom B C) (h₂ : Hom C D) (m : ℕ) :
    qmap (h₂.comp h) m = (qmap h₂ m).comp (qmap h m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/- English proof (translation)
Introduce `l _ R _ B C D h h₂ s s₂`. Use `⟨fun m => ?_, fun B' k => ?_⟩` and prove the remaining obligations. Rewrite using `[qmap_comp]`. Conclude with `RingHom.Flat.comp (s.flat m) (s₂.flat m)`. Take `⟨C', k', h', p⟩` from `s.po B' k`.

Take `⟨D', k'', h₂', p₂⟩` from `s₂.po C' k'`. Use `⟨D', k'', h₂'.comp h', ⟨?_, fun m => ?_⟩⟩` and prove the remaining obligations. Apply `Hom.ext'` to reduce the goal to its premises. Establish `e1` using `congrArg Hom.f p.comm`. Establish `e2` using `congrArg Hom.f p₂.comm`.

Express the relevant statement in the definitionally equal form `k''.f.comp (h₂.f.comp h.f) = (h₂'.f.comp h'.f).comp k.f`. Express the relevant statement in the definitionally equal form `k'.f.comp h.f = h'.f.comp k.f at e1`. Express the relevant statement in the definitionally equal form `k''.f.comp h₂.f = h₂'.f.comp k'.f at e2`. Rewrite using `[← RingHom.comp_assoc, e2, RingHom.comp_assoc, e1, RingHom.comp_assoc]`. Use `(p.po m).paste_horiz (p₂.po m)` as an intermediate fact.

Rewrite using `[qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]`. Conclude with `this`.
-/
theorem stable_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C)
    (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  intro l _ R _ B C D h h₂ s s₂
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · rw [qmap_comp]
    exact RingHom.Flat.comp (s.flat m) (s₂.flat m)
  · obtain ⟨C', k', h', p⟩ := s.po B' k
    obtain ⟨D', k'', h₂', p₂⟩ := s₂.po C' k'
    refine ⟨D', k'', h₂'.comp h', ⟨?_, fun m => ?_⟩⟩
    · apply Hom.ext'
      have e1 := congrArg Hom.f p.comm
      have e2 := congrArg Hom.f p₂.comm
      change k''.f.comp (h₂.f.comp h.f) = (h₂'.f.comp h'.f).comp k.f
      change k'.f.comp h.f = h'.f.comp k.f at e1
      change k''.f.comp h₂.f = h₂'.f.comp k'.f at e2
      rw [← RingHom.comp_assoc, e2, RingHom.comp_assoc, e1, RingHom.comp_assoc]
    · have := (p.po m).paste_horiz (p₂.po m)
      rw [qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
      exact this

end GlobalTheory.BSP
