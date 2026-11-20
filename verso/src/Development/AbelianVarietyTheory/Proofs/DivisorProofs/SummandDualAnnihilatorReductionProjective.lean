import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualSummand

open Module Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[disjoint_iff, eq_bot_iff]`. Introduce `f hf`. Rewrite `hf` using `[mem_inf, mem_dualAnnihilator, mem_dualAnnihilator]`. Rewrite using `[mem_bot]`.

Use extensionality with `c`. Rewrite using `[← projection_add_projection_eq_self h c, map_add, hf.1 _ (projection_apply_mem h c), hf.2 _ (projection_apply_mem h.symm c)]`. Simplify using the standard rewrite rules. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `f _`.

Establish `e : f = f ∘ₗ N.projection K h.symm + f ∘ₗ K.projection N h`. Use extensionality with `c`. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply]`. Rewrite using `[← map_add, add_comm, projection_add_projection_eq_self h c]`. Rewrite using `[e]`.

Use `add_mem_sup ?_ ?_` and prove the remaining obligations. Rewrite using `[mem_dualAnnihilator]`. Introduce `k hk`. Simplify using `[projection_apply_of_mem_right h.symm hk]`. Rewrite using `[mem_dualAnnihilator]`.

Introduce `n hn`. Simplify using `[projection_apply_of_mem_right h hn]`.
-/
theorem isCompl_dualAnnihilator {K N : Submodule R C} (h : IsCompl K N) :
    IsCompl K.dualAnnihilator N.dualAnnihilator := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro f hf
    rw [mem_inf, mem_dualAnnihilator, mem_dualAnnihilator] at hf
    rw [mem_bot]
    ext c
    rw [← projection_add_projection_eq_self h c, map_add, hf.1 _ (projection_apply_mem h c),
      hf.2 _ (projection_apply_mem h.symm c)]
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have e : f = f ∘ₗ N.projection K h.symm + f ∘ₗ K.projection N h := by
      ext c
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [← map_add, add_comm, projection_add_projection_eq_self h c]
    rw [e]
    refine add_mem_sup ?_ ?_
    · rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk]
    · rw [mem_dualAnnihilator]
      intro n hn
      simp [projection_apply_of_mem_right h hn]

/- English proof (translation)
Use `le_antisymm (fun c hc => ?_) (le_dualAnnihilator_dualCoannihilator _)` and prove the remaining obligations. Rewrite `hc` using `[mem_dualCoannihilator]`. Establish `hn : N.projection K h.symm c = 0`. Rewrite using `[← forall_dual_apply_eq_zero_iff R]`. Introduce `φ`.

Use `hc (φ ∘ₗ N.projection K h.symm) (by` as an intermediate fact. Rewrite using `[mem_dualAnnihilator]`. Introduce `k hk`. Simplify using `[projection_apply_of_mem_right h.symm hk])`. Simplify using `using this`.

Rewrite using `[← projection_add_projection_eq_self h c, hn, add_zero]`. Conclude with `projection_apply_mem h c`.
-/
theorem dualAnnihilator_dualCoannihilator_eq [Projective R C] {K N : Submodule R C}
    (h : IsCompl K N) : K.dualAnnihilator.dualCoannihilator = K := by
  refine le_antisymm (fun c hc => ?_) (le_dualAnnihilator_dualCoannihilator _)
  rw [mem_dualCoannihilator] at hc
  have hn : N.projection K h.symm c = 0 := by
    rw [← forall_dual_apply_eq_zero_iff R]
    intro φ
    have := hc (φ ∘ₗ N.projection K h.symm) (by
      rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk])
    simpa using this
  rw [← projection_add_projection_eq_self h c, hn, add_zero]
  exact projection_apply_mem h c

/- English proof (translation)
Take `⟨s, hs⟩` from `projective_def.mp (inferInstance : Projective R C)`. Rewrite using `[← hs c, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Conclude with `smul_mem_smul (by simpa using h (Finsupp.lapply m ∘ₗ s)) mem_top`.
-/
theorem mem_smul_top_of_forall_dual [Projective R C] (I : Ideal R) (c : C)
    (h : ∀ x : Dual R C, x c ∈ I) : c ∈ I • (⊤ : Submodule R C) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  rw [← hs c, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact smul_mem_smul (by simpa using h (Finsupp.lapply m ∘ₗ s)) mem_top

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

/- English proof (translation)
Take `⟨s, hs⟩` from `projective_def.mp (inferInstance : Projective R C)`. Use `⟨Finsupp.linearCombination R (fun m => Function.surjInv hπ (y (ρ m))) ∘ₗ s, fun c => ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← hs c]`. Simplify using `only [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, smul_eq_mul, map_mul, Function.surjInv_eq, LinearMap.map_smulₛₗ, id, RingHom.id_apply]`.
-/
theorem exists_dual_lift [Projective R C] (hπ : Function.Surjective π) (ρ : C →ₛₗ[π] C₀)
    (y : Dual R₀ C₀) : ∃ x : Dual R C, ∀ c, π (x c) = y (ρ c) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  refine ⟨Finsupp.linearCombination R (fun m => Function.surjInv hπ (y (ρ m))) ∘ₗ s, fun c => ?_⟩
  conv_rhs => rw [← hs c]
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    smul_eq_mul, map_mul, Function.surjInv_eq, LinearMap.map_smulₛₗ, id, RingHom.id_apply]

/- English proof (translation)
Establish `hI : RingHom.ker π • (⊤ : Submodule R C) ≤ Submodule.comap x (RingHom.ker π)`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr n _`. Rewrite using `[Submodule.mem_comap, map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ hr`.

Establish `hx : ∀ a b, ρ a = ρ b → π (x a) = π (x b)`. Introduce `a b hab`. Establish `h1 : a - b ∈ RingHom.ker π • (⊤ : Submodule R C)` using `(hker _).mp (by rw [map_sub, hab, sub_self])`. Establish `h2` using `hI h1`. Rewrite `h2` using `[Submodule.mem_comap, map_sub]`.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `(RingHom.mem_ker).mp h2`. Set `g` to `Function.surjInv hρ`. Establish `hg : ∀ v, ρ (g v) = v` using `Function.surjInv_eq hρ`. Use `⟨{ toFun := fun v => π (x (g v)), map_add' := ?_, map_smul' := ?_ }, fun c => hx _ _ (hg _)⟩` and prove the remaining obligations.

Introduce `a b`. Rewrite using `[show π (x (g a)) + π (x (g b)) = π (x (g a + g b)) by simp]`. Conclude with `hx _ _ (by rw [map_add, hg, hg, hg])`. Introduce `r v`. Take `⟨r', rfl⟩` from `hπ r`.

Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Rewrite using `[← map_mul, ← smul_eq_mul, ← map_smul]`. Conclude with `hx _ _ (by rw [LinearMap.map_smulₛₗ, hg, hg])`.
-/
theorem exists_dual_descent {ρ : C →ₛₗ[π] C₀} (hπ : Function.Surjective π)
    (hρ : Function.Surjective ρ) (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (x : Dual R C) : ∃ y : Dual R₀ C₀, ∀ c, y (ρ c) = π (x c) := by
  have hI : RingHom.ker π • (⊤ : Submodule R C) ≤ Submodule.comap x (RingHom.ker π) := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  have hx : ∀ a b, ρ a = ρ b → π (x a) = π (x b) := by
    intro a b hab
    have h1 : a - b ∈ RingHom.ker π • (⊤ : Submodule R C) := (hker _).mp (by rw [map_sub, hab, sub_self])
    have h2 := hI h1
    rw [Submodule.mem_comap, map_sub] at h2
    rw [← sub_eq_zero, ← map_sub]
    exact (RingHom.mem_ker).mp h2
  let g := Function.surjInv hρ
  have hg : ∀ v, ρ (g v) = v := Function.surjInv_eq hρ
  refine ⟨{ toFun := fun v => π (x (g v)), map_add' := ?_, map_smul' := ?_ }, fun c => hx _ _ (hg _)⟩
  · intro a b
    rw [show π (x (g a)) + π (x (g b)) = π (x (g a + g b)) by simp]
    exact hx _ _ (by rw [map_add, hg, hg, hg])
  · intro r v
    obtain ⟨r', rfl⟩ := hπ r
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← map_mul, ← smul_eq_mul, ← map_smul]
    exact hx _ _ (by rw [LinearMap.map_smulₛₗ, hg, hg])

end GlobalTheory.DualSummand

namespace GlobalTheory.DualSummand

open Module Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]
variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

/- English proof (translation)
Take `⟨c, rfl⟩` from `hρ v`. Rewrite using `[hker]`. Use `mem_smul_top_of_forall_dual _ c fun x => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `exists_dual_descent hπ hρ hker x`. Rewrite using `[RingHom.mem_ker, ← hy]`.

Conclude with `hv y`.
-/
theorem eq_zero_of_forall_dual_reduction [Projective R C] {ρ : C →ₛₗ[π] C₀}
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (v : C₀) (hv : ∀ φ : Dual R₀ C₀, φ v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hρ v
  rw [hker]
  refine mem_smul_top_of_forall_dual _ c fun x => ?_
  obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker x
  rw [RingHom.mem_ker, ← hy]
  exact hv y

/- English proof (translation)
Establish `hsurj : ∀ ψ : Dual R (Dual R C), ∃ k : C, ∀ φ : Dual R C, φ k = ψ φ`. Introduce `ψ`. Take `⟨k, hk⟩` from `(Module.bijective_dual_eval R C).2 ψ`. Conclude with `⟨k, fun φ => by rw [← hk, Dual.eval_apply]⟩`. Establish `hsplit : ∀ φ : Dual R C, G.projection H hGH φ + H.projection G hGH.symm φ = φ` using `projection_add_projection_eq_self hGH`.

Establish `hKL : IsCompl G.dualCoannihilator H.dualCoannihilator`. Prove the components needed by the constructor for the conclusion. Rewrite using `[disjoint_iff, eq_bot_iff]`. Introduce `c hc`. Rewrite `hc` using `[mem_inf, mem_dualCoannihilator, mem_dualCoannihilator]`.

Rewrite using `[mem_bot, ← forall_dual_apply_eq_zero_iff R]`. Introduce `φ`. Rewrite using `[← hsplit φ, LinearMap.add_apply, hc.1 _ (projection_apply_mem hGH φ), hc.2 _ (projection_apply_mem hGH.symm φ), add_zero]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `c _`.

Take `⟨k, hk⟩` from `hsurj (Dual.eval R C c ∘ₗ H.projection G hGH.symm)`. Take `⟨l, hl⟩` from `hsurj (Dual.eval R C c ∘ₗ G.projection H hGH)`. Use `Submodule.mem_sup.mpr ⟨k, ?_, l, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_dualCoannihilator]`. Introduce `g hg`.

Rewrite using `[hk g]`. Simplify using `[projection_apply_of_mem_right hGH.symm hg]`. Rewrite using `[mem_dualCoannihilator]`. Introduce `h hh`. Rewrite using `[hl h]`.

Simplify using `[projection_apply_of_mem_right hGH hh]`. Rewrite using `[← sub_eq_zero, ← forall_dual_apply_eq_zero_iff R]`. Introduce `φ`. Rewrite using `[map_sub, map_add, hk φ, hl φ]`. Simplify using `only [LinearMap.comp_apply, Dual.eval_apply]`.

Rewrite using `[← LinearMap.add_apply, add_comm, hsplit φ, sub_self]`. Use `⟨G.dualCoannihilator, ⟨_, hKL⟩, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[mem_dualAnnihilator]`. Introduce `k hk`.

Conclude with `(mem_dualCoannihilator _).mp hk g hg`. Introduce `φ hφ`. Rewrite `hφ` using `[mem_dualAnnihilator]`. Establish `h0 : H.projection G hGH.symm φ = 0`. Use extensionality with `c`.

Take `⟨k, hk, l, hl, rfl⟩` from `Submodule.mem_sup.mp (hKL.sup_eq_top ▸ mem_top : c ∈ _)`. Establish `e : H.projection G hGH.symm φ = φ - G.projection H hGH φ`. Rewrite using `[eq_sub_iff_add_eq, add_comm, hsplit φ]`. Rewrite using `[map_add, (mem_dualCoannihilator _).mp hl _ (projection_apply_mem hGH.symm φ), e, LinearMap.sub_apply, hφ k hk, (mem_dualCoannihilator _).mp hk _ (projection_apply_mem hGH φ)]`. Simplify using the standard rewrite rules.

Rewrite using `[← hsplit φ, h0, add_zero]`. Conclude with `projection_apply_mem hGH φ`.
-/
theorem exists_eq_dualAnnihilator [Projective R C] [Module.Finite R C]
    {G H : Submodule R (Dual R C)} (hGH : IsCompl G H) :
    ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  have hsurj : ∀ ψ : Dual R (Dual R C), ∃ k : C, ∀ φ : Dual R C, φ k = ψ φ := by
    intro ψ
    obtain ⟨k, hk⟩ := (Module.bijective_dual_eval R C).2 ψ
    exact ⟨k, fun φ => by rw [← hk, Dual.eval_apply]⟩
  have hsplit : ∀ φ : Dual R C, G.projection H hGH φ + H.projection G hGH.symm φ = φ :=
    projection_add_projection_eq_self hGH
  have hKL : IsCompl G.dualCoannihilator H.dualCoannihilator := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro c hc
      rw [mem_inf, mem_dualCoannihilator, mem_dualCoannihilator] at hc
      rw [mem_bot, ← forall_dual_apply_eq_zero_iff R]
      intro φ
      rw [← hsplit φ, LinearMap.add_apply, hc.1 _ (projection_apply_mem hGH φ),
        hc.2 _ (projection_apply_mem hGH.symm φ), add_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      obtain ⟨k, hk⟩ := hsurj (Dual.eval R C c ∘ₗ H.projection G hGH.symm)
      obtain ⟨l, hl⟩ := hsurj (Dual.eval R C c ∘ₗ G.projection H hGH)
      refine Submodule.mem_sup.mpr ⟨k, ?_, l, ?_, ?_⟩
      · rw [mem_dualCoannihilator]
        intro g hg
        rw [hk g]
        simp [projection_apply_of_mem_right hGH.symm hg]
      · rw [mem_dualCoannihilator]
        intro h hh
        rw [hl h]
        simp [projection_apply_of_mem_right hGH hh]
      · rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff R]
        intro φ
        rw [map_sub, map_add, hk φ, hl φ]
        simp only [LinearMap.comp_apply, Dual.eval_apply]
        rw [← LinearMap.add_apply, add_comm, hsplit φ, sub_self]
  refine ⟨G.dualCoannihilator, ⟨_, hKL⟩, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [mem_dualAnnihilator]
    intro k hk
    exact (mem_dualCoannihilator _).mp hk g hg
  · intro φ hφ
    rw [mem_dualAnnihilator] at hφ
    have h0 : H.projection G hGH.symm φ = 0 := by
      ext c
      obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.mp (hKL.sup_eq_top ▸ mem_top : c ∈ _)
      have e : H.projection G hGH.symm φ = φ - G.projection H hGH φ := by
        rw [eq_sub_iff_add_eq, add_comm, hsplit φ]
      rw [map_add, (mem_dualCoannihilator _).mp hl _ (projection_apply_mem hGH.symm φ), e,
        LinearMap.sub_apply, hφ k hk, (mem_dualCoannihilator _).mp hk _ (projection_apply_mem hGH φ)]
      simp
    rw [← hsplit φ, h0, add_zero]
    exact projection_apply_mem hGH φ

end GlobalTheory.DualSummand

namespace GlobalTheory.LiftSys

open Module Submodule GlobalTheory.DualSummand

/- English proof (translation)
Introduce `R R₀ _ _ π hπ C C₀ _ _ _ _ _ _ ρ hρ hker F₀ ⟨N₀, hF⟩`. Use `⟨fun K ⟨N, hKN⟩ => ⟨⟨_, isCompl_dualAnnihilator hKN⟩, dualAnnihilator_dualCoannihilator_eq hKN, ?_⟩, fun G ⟨H, hGH⟩ => exists_eq_dualAnnihilator hGH⟩` and prove the remaining obligations. Establish `hsplit : ∀ c, K.projection N hKN c + N.projection K hKN.symm c = c` using `projection_add_projection_eq_self hKN`. Establish `hNK : ∀ k ∈ K, N.projection K hKN.symm k = 0` using `fun k hk => projection_apply_of_mem_right hKN.symm hk`. Prove the components needed by the constructor for the conclusion.

Introduce `hL y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite `hy` using `[mem_dualAnnihilator]`. Take `⟨x₀, hx₀⟩` from `exists_dual_lift hπ ρ y`.

Use `⟨x₀ ∘ₗ N.projection K hKN.symm, ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_dualAnnihilator]`. Introduce `k hk`. Simplify using `[hNK k hk]`. Rewrite using `[LinearMap.comp_apply, hx₀] conv_lhs => rw [← hsplit c]`.

Rewrite using `[map_add, map_add, hy _ ((hL _).mp (mem_sup_left (projection_apply_mem hKN c))), zero_add]`. Introduce and unpack `⟨x, hx, hxy⟩`. Rewrite `hx`, the goal using `[mem_dualAnnihilator]`. Introduce `f hf`. Take `⟨c, rfl⟩` from `hρ f`.

Take `⟨k, hk, m, hm, rfl⟩` from `Submodule.mem_sup.mp ((hL c).mpr hf)`. Rewrite using `[map_add, (hker m).mpr hm, add_zero, hxy, hx k hk, map_zero]`. Introduce `hR c`. Prove the components needed by the constructor for the conclusion. Introduce `hc`.

Take `⟨k, hk, m, hm, rfl⟩` from `Submodule.mem_sup.mp hc`. Rewrite using `[map_add, (hker m).mpr hm, add_zero]`. Establish `hv : N₀.projection F₀ hF.symm (ρ k) = 0`. Use `eq_zero_of_forall_dual_reduction hπ hρ hker _ fun φ => ?_` and prove the remaining obligations. Take `⟨x, hx, hxy⟩` from `(hR (φ ∘ₗ N₀.projection F₀ hF.symm)).mp (by`.

Rewrite using `[mem_dualAnnihilator]`. Introduce `f hf`. Simplify using `[projection_apply_of_mem_right hF.symm hf])`. Use `hxy k` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply]`.

Rewrite using `[this, (mem_dualAnnihilator _).mp hx k hk, map_zero]`. Rewrite using `[← projection_add_projection_eq_self hF (ρ k), hv, add_zero]`. Conclude with `projection_apply_mem hF _`. Introduce `hc`. Rewrite using `[← hsplit c]`.

Use `add_mem_sup (projection_apply_mem hKN c) ?_` and prove the remaining obligations. Use `mem_smul_top_of_forall_dual _ _ fun x₀ => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `exists_dual_descent hπ hρ hker (x₀ ∘ₗ N.projection K hKN.symm)`. Establish `hyF : y ∈ F₀.dualAnnihilator` using `(hR y).mpr ⟨x₀ ∘ₗ N.projection K hKN.symm, by`. Rewrite using `[mem_dualAnnihilator]`.

Introduce `k hk`. Simplify using `[hNK k hk], hy⟩`. Rewrite using `[RingHom.mem_ker, ← LinearMap.comp_apply, ← hy]`. Conclude with `(mem_dualAnnihilator _).mp hyF _ hc`.
-/
theorem summand_dual_reduction :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  intro R R₀ _ _ π hπ C C₀ _ _ _ _ _ _ ρ hρ hker F₀ ⟨N₀, hF⟩
  refine ⟨fun K ⟨N, hKN⟩ => ⟨⟨_, isCompl_dualAnnihilator hKN⟩,
    dualAnnihilator_dualCoannihilator_eq hKN, ?_⟩, fun G ⟨H, hGH⟩ => exists_eq_dualAnnihilator hGH⟩
  have hsplit : ∀ c, K.projection N hKN c + N.projection K hKN.symm c = c :=
    projection_add_projection_eq_self hKN
  have hNK : ∀ k ∈ K, N.projection K hKN.symm k = 0 := fun k hk =>
    projection_apply_of_mem_right hKN.symm hk
  constructor
  · intro hL y
    constructor
    · intro hy
      rw [mem_dualAnnihilator] at hy
      obtain ⟨x₀, hx₀⟩ := exists_dual_lift hπ ρ y
      refine ⟨x₀ ∘ₗ N.projection K hKN.symm, ?_, fun c => ?_⟩
      · rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk]
      · rw [LinearMap.comp_apply, hx₀]
        conv_lhs => rw [← hsplit c]
        rw [map_add, map_add,
          hy _ ((hL _).mp (mem_sup_left (projection_apply_mem hKN c))), zero_add]
    · rintro ⟨x, hx, hxy⟩
      rw [mem_dualAnnihilator] at hx ⊢
      intro f hf
      obtain ⟨c, rfl⟩ := hρ f
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp ((hL c).mpr hf)
      rw [map_add, (hker m).mpr hm, add_zero, hxy, hx k hk, map_zero]
  · intro hR c
    constructor
    · intro hc
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp hc
      rw [map_add, (hker m).mpr hm, add_zero]
      have hv : N₀.projection F₀ hF.symm (ρ k) = 0 := by
        refine eq_zero_of_forall_dual_reduction hπ hρ hker _ fun φ => ?_
        obtain ⟨x, hx, hxy⟩ := (hR (φ ∘ₗ N₀.projection F₀ hF.symm)).mp (by
          rw [mem_dualAnnihilator]
          intro f hf
          simp [projection_apply_of_mem_right hF.symm hf])
        have := hxy k
        rw [LinearMap.comp_apply] at this
        rw [this, (mem_dualAnnihilator _).mp hx k hk, map_zero]
      rw [← projection_add_projection_eq_self hF (ρ k), hv, add_zero]
      exact projection_apply_mem hF _
    · intro hc
      rw [← hsplit c]
      refine add_mem_sup (projection_apply_mem hKN c) ?_
      refine mem_smul_top_of_forall_dual _ _ fun x₀ => ?_
      obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker (x₀ ∘ₗ N.projection K hKN.symm)
      have hyF : y ∈ F₀.dualAnnihilator := (hR y).mpr ⟨x₀ ∘ₗ N.projection K hKN.symm, by
        rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk], hy⟩
      rw [RingHom.mem_ker, ← LinearMap.comp_apply, ← hy]
      exact (mem_dualAnnihilator _).mp hyF _ hc

end GlobalTheory.LiftSys
