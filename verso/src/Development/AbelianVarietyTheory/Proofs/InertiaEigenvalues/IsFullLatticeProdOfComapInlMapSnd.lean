import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Take `⟨f₁, s₁⟩` from `h₁`. Take `⟨f₂, s₂⟩` from `h₂`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_` and prove the remaining obligations. Establish `: M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) = (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A)`.

Use extensionality with `⟨a, b⟩`. Simplify using `only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map, Submodule.mem_comap, LinearMap.inl_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hM, rfl⟩`. Conclude with `⟨a, hM, rfl⟩`.

Introduce and unpack `⟨c, hc, he⟩`. Rewrite `he` using `[Prod.mk.injEq]`. Take `⟨rfl, rfl⟩` from `he`. Conclude with `⟨hc, rfl⟩`. Rewrite using `[this]`.

Conclude with `f₁.map _`. Use `set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS`. Establish `hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S`. Introduce `a`. Establish `ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)`.

Rewrite using `[s₁]`. Discharge the goal by the elementary cases of `trivial`. Establish `hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map (LinearMap.inl K.E B₁.A B₂.A) ≤ S`. Rewrite using `[Submodule.map_span]`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `hc`. Conclude with `hle ⟨a, ha, rfl⟩`. Establish `hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤`. Rewrite using `[hS, Submodule.map_span, ← s₂]`.

Use `congr 1`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨a, b⟩ -`. Establish `hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A)` using `by rw [hsnd]; trivial`. Take `⟨y, hy, hyb⟩` from `hb`.

Establish `: ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0)`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[← hyb]`. Rewrite using `[this]`.

Conclude with `S.add_mem hy (hinl _)`.
-/
theorem isLat_of_comap_inl_of_map_snd (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by
  obtain ⟨f₁, s₁⟩ := h₁
  obtain ⟨f₂, s₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_
    have : M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) =
        (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A) := by
      ext ⟨a, b⟩
      simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
        Submodule.mem_comap, LinearMap.inl_apply]
      constructor
      · rintro ⟨hM, rfl⟩
        exact ⟨a, hM, rfl⟩
      · rintro ⟨c, hc, he⟩
        rw [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hc, rfl⟩
    rw [this]
    exact f₁.map _
  · set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS
    have hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S := by
      intro a
      have ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A) := by
        rw [s₁]; trivial
      have hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map
          (LinearMap.inl K.E B₁.A B₂.A) ≤ S := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨c, hc, rfl⟩
        exact hc
      exact hle ⟨a, ha, rfl⟩
    have hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤ := by
      rw [hS, Submodule.map_span, ← s₂]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A) := by rw [hsnd]; trivial
    obtain ⟨y, hy, hyb⟩ := hb
    have : ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0) := by
      ext
      · simp
      · simp [← hyb]
    rw [this]
    exact S.add_mem hy (hinl _)

end GlobalTheory.UnitLemma
