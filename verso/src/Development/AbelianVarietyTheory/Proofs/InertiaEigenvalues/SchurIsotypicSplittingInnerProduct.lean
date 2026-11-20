import Mathlib

namespace GlobalTheory

open Submodule

section SchurIsotypic
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
lemma schur_act_inv (act : G →* Module.End ℂ H) (g : G) (y : H) : act g (act g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Introduce `g e he`. Rewrite `he`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Use `hact g _ _ (he _ (hP g⁻¹ u hu))` as an intermediate fact. Rewrite `this` using `[schur_act_inv]`. Then use the resulting hypothesis.
-/
lemma schur_orth_stable (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (P : Submodule ℂ H) (hP : ∀ g, ∀ p ∈ P, act g p ∈ P) :
    ∀ g, ∀ e ∈ Pᗮ, act g e ∈ Pᗮ := by
  intro g e he
  rw [Submodule.mem_orthogonal] at he ⊢
  intro u hu
  have := hact g _ _ (he _ (hP g⁻¹ u hu))
  rwa [schur_act_inv] at this

/- English proof (translation)
Conclude with `⟨P.starProjection x, P.starProjection_apply_mem x, P.sub_starProjection_mem_orthogonal x⟩`.
-/
lemma schur_decomp [FiniteDimensional ℂ H] (P : Submodule ℂ H) (x : H) :
    ∃ p ∈ P, x - p ∈ Pᗮ := by
  exact ⟨P.starProjection x, P.starProjection_apply_mem x, P.sub_starProjection_mem_orthogonal x⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨e₀, he₀E, he₀⟩` from `hne`. Set `K : Submodule ℂ H` to `LinearMap.ker φ ⊓ E`. Establish `hK : ∀ g, ∀ k ∈ K, act g k ∈ K`.

Introduce `g k hk`. Take `⟨hk1, hk2⟩` from `Submodule.mem_inf.1 hk`. Use `Submodule.mem_inf.2 ⟨?_, hE g k hk2⟩` and prove the remaining obligations. Rewrite `hk1`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hφ g k hk2, hk1, map_zero]`.

Set `C : Submodule ℂ H` to `Kᗮ ⊓ E`. Establish `hC : ∀ g, ∀ c ∈ C, act g c ∈ C` using `fun g c hc => Submodule.mem_inf.2 ⟨schur_orth_stable act hact K hK g c (Submodule.mem_inf.1 hc).1, hE g c (Submodule.mem_inf.1 hc).2⟩`. Establish `hCE : ∀ c ∈ C, c ∈ E` using `fun c hc => (Submodule.mem_inf.1 hc).2`. Establish `hinj : ∀ c ∈ C, φ c = 0 → c = 0`. Introduce `c hc h0`.

Establish `hcK : c ∈ K` using `Submodule.mem_inf.2 ⟨h0, hCE c hc⟩`. Use `(Submodule.mem_orthogonal _ _).1 (Submodule.mem_inf.1 hc).1 c hcK` as an intermediate fact. Conclude with `inner_self_eq_zero.1 this`. Establish `hU : C.map φ = ⊤`. Break down `hirr (C.map φ) (by` into its components or cases.

Introduce `g`. Introduce and unpack `_ ⟨_, ⟨c, hc, rfl⟩, rfl⟩`. Conclude with `⟨act g c, hC g c hc, hφ g c (hCE c hc)⟩) with h | h`. It suffices to derive a contradiction. Take `⟨p, hp, hr⟩` from `schur_decomp K e₀`.

Establish `hrE : e₀ - p ∈ E` using `E.sub_mem he₀E (Submodule.mem_inf.1 hp).2`. Establish `hrC : e₀ - p ∈ C` using `Submodule.mem_inf.2 ⟨hr, hrE⟩`. Establish `hm : φ (e₀ - p) ∈ C.map φ` using `Submodule.mem_map_of_mem hrC`. Rewrite `hm` using `[h, Submodule.mem_bot, map_sub, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hp).1, sub_zero]`. Conclude with `he₀ hm`.

Conclude with `h`. Set `ψ : C →ₗ[ℂ] W` to `φ.comp C.subtype`. Establish `hψi : Function.Injective ψ`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `c hc`.

Conclude with `Subtype.ext (hinj c c.2 (LinearMap.mem_ker.1 hc))`. Establish `hψs : Function.Surjective ψ`. Introduce `w`. Establish `hw : w ∈ C.map φ` using `hU ▸ Submodule.mem_top`. Take `⟨c, hc, hcw⟩` from `hw`.

Conclude with `⟨⟨c, hc⟩, hcw⟩`. Set `e` to `LinearEquiv.ofBijective ψ ⟨hψi, hψs⟩`. Set `χ : W →ₗ[ℂ] H` to `C.subtype.comp e.symm.toLinearMap`. Establish `hχC : ∀ w, χ w ∈ C` using `fun w => (e.symm w).2`. Establish `hφχ : ∀ w, φ (χ w) = w` using `fun w => by show ψ (e.symm w) = w`.

Conclude with `e.apply_symm_apply w`. Establish `hχ : ∀ g w, χ (ρ g w) = act g (χ w)`. Introduce `g w`. Establish `hd : χ (ρ g w) - act g (χ w) ∈ C` using `C.sub_mem (hχC _) (hC g _ (hχC w))`. Use `hinj _ hd (by rw [map_sub, hφχ, hφ g _ (hCE _ (hχC w)), hφχ, sub_self])` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Establish `h0 : χ w = 0` using `inner_self_eq_zero.1 (hEorth χ hχ w (χ w) (hCE _ (hχC w)))`. Conclude with `hw (by rw [← hφχ w, h0, map_zero])`.
-/
lemma schur_vanish {W : Type} [AddCommGroup W] [Module ℂ W] [Nontrivial W] [FiniteDimensional ℂ H]
    (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (ρ : G →* Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (E : Submodule ℂ H) (hE : ∀ g, ∀ e ∈ E, act g e ∈ E)
    (hEorth : ∀ χ : W →ₗ[ℂ] H, (∀ g w, χ (ρ g w) = act g (χ w)) →
      ∀ w, ∀ e ∈ E, inner ℂ (χ w) e = 0)
    (φ : H →ₗ[ℂ] W) (hφ : ∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) : ∀ e ∈ E, φ e = 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨e₀, he₀E, he₀⟩ := hne
  let K : Submodule ℂ H := LinearMap.ker φ ⊓ E
  have hK : ∀ g, ∀ k ∈ K, act g k ∈ K := by
    intro g k hk
    obtain ⟨hk1, hk2⟩ := Submodule.mem_inf.1 hk
    refine Submodule.mem_inf.2 ⟨?_, hE g k hk2⟩
    rw [LinearMap.mem_ker] at hk1 ⊢
    rw [hφ g k hk2, hk1, map_zero]
  let C : Submodule ℂ H := Kᗮ ⊓ E
  have hC : ∀ g, ∀ c ∈ C, act g c ∈ C := fun g c hc =>
    Submodule.mem_inf.2 ⟨schur_orth_stable act hact K hK g c (Submodule.mem_inf.1 hc).1,
      hE g c (Submodule.mem_inf.1 hc).2⟩
  have hCE : ∀ c ∈ C, c ∈ E := fun c hc => (Submodule.mem_inf.1 hc).2
  have hinj : ∀ c ∈ C, φ c = 0 → c = 0 := by
    intro c hc h0
    have hcK : c ∈ K := Submodule.mem_inf.2 ⟨h0, hCE c hc⟩
    have := (Submodule.mem_orthogonal _ _).1 (Submodule.mem_inf.1 hc).1 c hcK
    exact inner_self_eq_zero.1 this
  have hU : C.map φ = ⊤ := by
    rcases hirr (C.map φ) (by
      intro g
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨act g c, hC g c hc, hφ g c (hCE c hc)⟩) with h | h
    · exfalso
      obtain ⟨p, hp, hr⟩ := schur_decomp K e₀
      have hrE : e₀ - p ∈ E := E.sub_mem he₀E (Submodule.mem_inf.1 hp).2
      have hrC : e₀ - p ∈ C := Submodule.mem_inf.2 ⟨hr, hrE⟩
      have hm : φ (e₀ - p) ∈ C.map φ := Submodule.mem_map_of_mem hrC
      rw [h, Submodule.mem_bot, map_sub, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hp).1,
        sub_zero] at hm
      exact he₀ hm
    · exact h
  let ψ : C →ₗ[ℂ] W := φ.comp C.subtype
  have hψi : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    exact Subtype.ext (hinj c c.2 (LinearMap.mem_ker.1 hc))
  have hψs : Function.Surjective ψ := by
    intro w
    have hw : w ∈ C.map φ := hU ▸ Submodule.mem_top
    obtain ⟨c, hc, hcw⟩ := hw
    exact ⟨⟨c, hc⟩, hcw⟩
  let e := LinearEquiv.ofBijective ψ ⟨hψi, hψs⟩
  let χ : W →ₗ[ℂ] H := C.subtype.comp e.symm.toLinearMap
  have hχC : ∀ w, χ w ∈ C := fun w => (e.symm w).2
  have hφχ : ∀ w, φ (χ w) = w := fun w => by
    show ψ (e.symm w) = w
    exact e.apply_symm_apply w
  have hχ : ∀ g w, χ (ρ g w) = act g (χ w) := by
    intro g w
    have hd : χ (ρ g w) - act g (χ w) ∈ C := C.sub_mem (hχC _) (hC g _ (hχC w))
    have := hinj _ hd (by rw [map_sub, hφχ, hφ g _ (hCE _ (hχC w)), hφχ, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h0 : χ w = 0 := inner_self_eq_zero.1 (hEorth χ hχ w (χ w) (hCE _ (hχC w)))
  exact hw (by rw [← hφχ w, h0, map_zero])

end SchurIsotypic

/- English proof (translation)
Introduce `G W H _ _ _ _ _ _ _ act hact ρ hirr x`. Set `S : Set H` to `{q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}`. Set `I : Submodule ℂ H` to `Submodule.span ℂ S`. Establish `hI : ∀ g, ∀ y ∈ I, act g y ∈ I`. Introduce `g y hy`.

Establish `hle : I.map (act g) ≤ I`. Rewrite using `[Submodule.map_span]`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span ⟨φ, ρ g w, hφ, (hφ g w).symm⟩`.

Conclude with `hle (Submodule.mem_map_of_mem hy)`. Take `⟨q, hq, hxq⟩` from `schur_decomp I x`. Use `⟨q, hq, Iᗮ, schur_orth_stable act hact I hI, ?_, hxq⟩` and prove the remaining obligations. Introduce `φ hφ`. Use `schur_vanish act hact ρ hirr Iᗮ (schur_orth_stable act hact I hI) ?_ φ hφ` and prove the remaining obligations.

Introduce `χ hχ w e he`. Conclude with `(Submodule.mem_orthogonal _ _).1 he _ (Submodule.subset_span ⟨χ, w, hχ, rfl⟩)`.
-/
theorem schur_isotypic_splitting : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  intro G W H _ _ _ _ _ _ _ act hact ρ hirr x
  let S : Set H := {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}
  let I : Submodule ℂ H := Submodule.span ℂ S
  have hI : ∀ g, ∀ y ∈ I, act g y ∈ I := by
    intro g y hy
    have hle : I.map (act g) ≤ I := by
      rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨φ, ρ g w, hφ, (hφ g w).symm⟩
    exact hle (Submodule.mem_map_of_mem hy)
  obtain ⟨q, hq, hxq⟩ := schur_decomp I x
  refine ⟨q, hq, Iᗮ, schur_orth_stable act hact I hI, ?_, hxq⟩
  intro φ hφ
  refine schur_vanish act hact ρ hirr Iᗮ (schur_orth_stable act hact I hI) ?_ φ hφ
  intro χ hχ w e he
  exact (Submodule.mem_orthogonal _ _).1 he _ (Submodule.subset_span ⟨χ, w, hχ, rfl⟩)

end GlobalTheory
