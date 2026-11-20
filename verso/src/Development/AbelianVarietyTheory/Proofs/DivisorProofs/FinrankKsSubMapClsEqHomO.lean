import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho

/- English proof (translation)
Use `set Zc := Z.comap G.subtype`. Use `set hom := homO (qAct (rAct σ G hG) Zc (fun a x hx => hZ a x hx)) (qAct σ G hG)`. Set `Ψ : hom →ₗ[k] (G →ₗ[k] H ⧸ G)` to `(LinearMap.lcomp k (H ⧸ G) Zc.mkQ) ∘ₗ hom.subtype`. Establish `hΨ : ∀ S : hom, Ψ S = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) ∘ₗ Zc.mkQ` using `fun S => rfl`. Establish `inj : Function.Injective Ψ`.

Introduce `S S' h`. Rewrite `h` using `[hΨ, hΨ]`. Conclude with `Subtype.ext (LinearMap.ext fun q => by`. Take `⟨x, rfl⟩` from `Zc.mkQ_surjective q`. Conclude with `LinearMap.congr_fun h x)`.

Establish `hr : LinearMap.range Ψ = (ksSub σ 0 G Z).map (cls G)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨S, rfl⟩`. Take `⟨G', hG'⟩` from `Submodule.exists_isCompl G`. Take `⟨s, hs⟩` from `LinearMap.exists_rightInverse_of_surjective G.mkQ (Submodule.range_mkQ G)`.

Establish `hs' : ∀ q, G.mkQ (s q) = q` using `fun q => LinearMap.congr_fun hs q`. Set `T : G →ₗ[k] H ⧸ G` to `Ψ S`. Set `f : H →ₗ[k] H` to `s ∘ₗ T ∘ₗ Submodule.linearProjOfIsCompl G G' hG'`. Establish `hf : ∀ x (hx : x ∈ G), G.mkQ (f x) = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) (Zc.mkQ ⟨x, hx⟩)`. Introduce `x hx`.

Establish `hp : Submodule.linearProjOfIsCompl G G' hG' x = ⟨x, hx⟩` using `Submodule.linearProjOfIsCompl_apply_left hG' ⟨x, hx⟩`. Simplify using `only [f, LinearMap.comp_apply, hp, hs']`. Both sides reduce to the same expression. Use `⟨f, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a x hx`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))`. Rewrite using `[hf _ (hG a x hx), ← qAct_mk σ G hG, hf x hx]`. Rewrite using `[← (mem_homO _ _ _).1 S.2 a]`. Both sides reduce to the same expression.

Introduce `x hx`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `G.mkQ (f x) = 0`. Rewrite using `[hf x (hZG hx)]`. Establish `: Zc.mkQ ⟨x, hZG hx⟩ = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hx`.

Rewrite using `[this, map_zero]`. Introduce `x _ y _`. Simplify using the standard rewrite rules. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨x, hx⟩`.

Conclude with `hf x hx`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `hker : Zc ≤ LinearMap.ker (cls G f)`. Introduce `x hx`. Rewrite using `[LinearMap.mem_ker]`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (hf.2.1 x hx)`. Set `S0` to `Zc.liftQ (cls G f) hker`. Establish `hS0 : S0 ∈ hom`. Rewrite using `[mem_homO]`. Introduce `a q`.

Take `⟨x, rfl⟩` from `Zc.mkQ_surjective q`. Express the relevant statement in the definitionally equal form `S0 (Zc.mkQ (rAct σ G hG a x)) = qAct σ G hG a (S0 (Zc.mkQ x))`. Simplify using `only [S0, Submodule.liftQ_mkQ]`. Express the relevant statement in the definitionally equal form `G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))`. Rewrite using `[← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hf.1 a x x.2`. Use `⟨⟨S0, hS0⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hΨ]`. Conclude with `Submodule.liftQ_mkQ _ _ _`. Rewrite using `[← hr, LinearMap.finrank_range_of_inj inj]`.
-/
theorem finrank_ksSub_map_cls_eq_homO {k O H : Type*} [Field k] [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx))
        (qAct σ G hG)) := by
  set Zc := Z.comap G.subtype
  set hom := homO (qAct (rAct σ G hG) Zc (fun a x hx => hZ a x hx)) (qAct σ G hG)
  let Ψ : hom →ₗ[k] (G →ₗ[k] H ⧸ G) := (LinearMap.lcomp k (H ⧸ G) Zc.mkQ) ∘ₗ hom.subtype
  have hΨ : ∀ S : hom, Ψ S = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) ∘ₗ Zc.mkQ := fun S => rfl
  have inj : Function.Injective Ψ := by
    intro S S' h
    rw [hΨ, hΨ] at h
    exact Subtype.ext (LinearMap.ext fun q => by
      obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
      exact LinearMap.congr_fun h x)
  have hr : LinearMap.range Ψ = (ksSub σ 0 G Z).map (cls G) := by
    apply le_antisymm
    · rintro _ ⟨S, rfl⟩
      obtain ⟨G', hG'⟩ := Submodule.exists_isCompl G
      obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective G.mkQ (Submodule.range_mkQ G)
      have hs' : ∀ q, G.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
      let T : G →ₗ[k] H ⧸ G := Ψ S
      let f : H →ₗ[k] H := s ∘ₗ T ∘ₗ Submodule.linearProjOfIsCompl G G' hG'
      have hf : ∀ x (hx : x ∈ G), G.mkQ (f x) = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) (Zc.mkQ ⟨x, hx⟩) := by
        intro x hx
        have hp : Submodule.linearProjOfIsCompl G G' hG' x = ⟨x, hx⟩ :=
          Submodule.linearProjOfIsCompl_apply_left hG' ⟨x, hx⟩
        simp only [f, LinearMap.comp_apply, hp, hs']
        rfl
      refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro a x hx
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [hf _ (hG a x hx), ← qAct_mk σ G hG, hf x hx]
        rw [← (mem_homO _ _ _).1 S.2 a]
        rfl
      · intro x hx
        rw [← Submodule.Quotient.mk_eq_zero]
        change G.mkQ (f x) = 0
        rw [hf x (hZG hx)]
        have : Zc.mkQ ⟨x, hZG hx⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
        rw [this, map_zero]
      · intro x _ y _
        simp
      · apply LinearMap.ext
        rintro ⟨x, hx⟩
        exact hf x hx
    · rintro _ ⟨f, hf, rfl⟩
      have hker : Zc ≤ LinearMap.ker (cls G f) := by
        intro x hx
        rw [LinearMap.mem_ker]
        exact (Submodule.Quotient.mk_eq_zero _).2 (hf.2.1 x hx)
      let S0 := Zc.liftQ (cls G f) hker
      have hS0 : S0 ∈ hom := by
        rw [mem_homO]
        intro a q
        obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
        change S0 (Zc.mkQ (rAct σ G hG a x)) = qAct σ G hG a (S0 (Zc.mkQ x))
        simp only [S0, Submodule.liftQ_mkQ]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hf.1 a x x.2
      refine ⟨⟨S0, hS0⟩, ?_⟩
      rw [hΨ]
      exact Submodule.liftQ_mkQ _ _ _
  rw [← hr, LinearMap.finrank_range_of_inj inj]

end GlobalTheory.HTRho
