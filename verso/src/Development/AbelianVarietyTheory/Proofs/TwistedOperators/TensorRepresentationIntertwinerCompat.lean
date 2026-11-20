import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

/- English proof (translation)
Establish `hinj : Function.Injective P.dualMap` using `LinearMap.dualMap_injective_of_surjective hP`. Establish `hmap : (invFun σ).map P.dualMap = invFun ρ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, hl, rfl⟩ g v`. Express the relevant statement in the definitionally equal form `l (P (ρ g v)) = l (P v)`.

Rewrite using `[he, mem_invFun.1 hl]`. Introduce `l hl`. Take `⟨s, hs⟩` from `P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)`. Establish `hs' : ∀ w, P (s w) = w` using `fun w => LinearMap.congr_fun hs w`. Establish `key : ∀ v, l (s (P v)) = l v` using `fun v => by`.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `hk l hl _ (by rw [map_sub, hs', sub_self])`. Use `⟨l ∘ₗ s, fun g w => ?_, ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `hP w`. Express the relevant statement in the definitionally equal form `l (s _) = l (s _)`.

Rewrite using `[← he, key, key, mem_invFun.1 hl]`. Use extensionality with `v`. Conclude with `key v`. Rewrite using `[← hmap]`. Conclude with `((invFun σ).equivMapOfInjective _ hinj).finrank_eq.symm`.
-/
theorem finrank_invFun_eq_of_surjective {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (P : V →ₗ[ℂ] W) (hP : Function.Surjective P)
    (he : ∀ g v, P (ρ g v) = σ g (P v)) (hk : ∀ l ∈ invFun ρ, ∀ v, P v = 0 → l v = 0) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  have hinj : Function.Injective P.dualMap := LinearMap.dualMap_injective_of_surjective hP
  have hmap : (invFun σ).map P.dualMap = invFun ρ := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩ g v
      change l (P (ρ g v)) = l (P v)
      rw [he, mem_invFun.1 hl]
    · intro l hl
      obtain ⟨s, hs⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
      have hs' : ∀ w, P (s w) = w := fun w => LinearMap.congr_fun hs w
      have key : ∀ v, l (s (P v)) = l v := fun v => by
        rw [← sub_eq_zero, ← map_sub]
        exact hk l hl _ (by rw [map_sub, hs', sub_self])
      refine ⟨l ∘ₗ s, fun g w => ?_, ?_⟩
      · obtain ⟨v, rfl⟩ := hP w
        change l (s _) = l (s _)
        rw [← he, key, key, mem_invFun.1 hl]
      · ext v
        exact key v
  rw [← hmap]
  exact ((invFun σ).equivMapOfInjective _ hinj).finrank_eq.symm

/- English proof (translation)
Take `⟨s, hs⟩` from `p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)`. Take `⟨t, ht⟩` from `q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)`. Establish `hs' : ∀ w, p (s w) = w` using `fun w => LinearMap.congr_fun hs w`. Establish `ht' : ∀ w, q (t w) = w` using `fun w => LinearMap.congr_fun ht w`. Establish `key : ∀ z, l (TensorProduct.map s t (TensorProduct.map p q z)) = l z`.

Introduce `z`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul u w`.

Simplify using `only [TensorProduct.map_tmul]`. Establish `e1` using `h1 (s (p u) - u) (t (q w)) (by rw [map_sub, hs', sub_self])`. Establish `e2` using `h2 u (t (q w) - w) (by rw [map_sub, ht', sub_self])`. Rewrite `e1` using `[TensorProduct.sub_tmul, map_sub, sub_eq_zero]`. Rewrite `e2` using `[TensorProduct.tmul_sub, map_sub, sub_eq_zero]`.

Rewrite using `[e1, e2]`. Rewrite using `[← key, hz, map_zero, map_zero]`.
-/
theorem dual_eq_zero_of_map_eq_zero {U W X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : U →ₗ[ℂ] X) (q : W →ₗ[ℂ] Y)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (l : Module.Dual ℂ (U ⊗[ℂ] W))
    (h1 : ∀ u w, p u = 0 → l (u ⊗ₜ w) = 0) (h2 : ∀ u w, q w = 0 → l (u ⊗ₜ w) = 0) (z : U ⊗[ℂ] W)
    (hz : TensorProduct.map p q z = 0) : l z = 0 := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  obtain ⟨t, ht⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have hs' : ∀ w, p (s w) = w := fun w => LinearMap.congr_fun hs w
  have ht' : ∀ w, q (t w) = w := fun w => LinearMap.congr_fun ht w
  have key : ∀ z, l (TensorProduct.map s t (TensorProduct.map p q z)) = l z := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul u w =>
      simp only [TensorProduct.map_tmul]
      have e1 := h1 (s (p u) - u) (t (q w)) (by rw [map_sub, hs', sub_self])
      have e2 := h2 u (t (q w) - w) (by rw [map_sub, ht', sub_self])
      rw [TensorProduct.sub_tmul, map_sub, sub_eq_zero] at e1
      rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at e2
      rw [e1, e2]
  rw [← key, hz, map_zero, map_zero]

/- English proof (translation)
Use `⟨(TensorProduct.tensorTensorTensorComm ℂ A C B D).trans (TensorProduct.assoc ℂ A B (C ⊗[ℂ] D)), fun g z => ?_⟩` and prove the remaining obligations. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul u w`.

Proceed by induction on `u with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]`. Consider the case `tmul u1 u2`. Proceed by induction on `w with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]`. Consider the case `tmul w1 w2 => simp`.
-/
theorem iso_tprod_shuffle {Γ A B C D : Type} [Monoid Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B)
    (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) :
    Iso ((a.tprod c).tprod (b.tprod d)) (a.tprod (b.tprod (c.tprod d))) := by
  refine ⟨(TensorProduct.tensorTensorTensorComm ℂ A C B D).trans (TensorProduct.assoc ℂ A B (C ⊗[ℂ] D)), fun g z => ?_⟩
  induction z with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u w =>
    induction u with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul u1 u2 =>
      induction w with
      | zero => simp
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
      | tmul w1 w2 => simp

/- English proof (translation)
Rewrite using `[← (iso_tprod_shuffle a b c d).finrank_invFun]`. Establish `ep' : ∀ g z, p (a.tprod c g z) = x g (p z)`. Introduce `g z`. Proceed by induction on `z with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul u w => simp [ep]`. Establish `eq' : ∀ g z, q (b.tprod d g z) = y g (q z)`. Introduce `g z`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul u w => simp [eq]`. Use `finrank_invFun_eq_of_surjective _ _ (TensorProduct.map p q) (TensorProduct.map_surjective hp hq) (fun g z => ?_) (fun l hl z hz => dual_eq_zero_of_map_eq_zero p q hp hq l ?_ ?_ z hz)` and prove the remaining obligations. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul u w`. Rewrite using `[Representation.tprod_apply, Representation.tprod_apply x, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, ep', eq']`. Introduce `u w hu`.

Use `kp (l ∘ₗ (TensorProduct.mk ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D)).flip w) (fun g hb hd u1 u2 => ?_) u hu` and prove the remaining obligations. Use `mem_invFun.1 hl g ((u1 ⊗ₜ u2) ⊗ₜ w)` as an intermediate fact. Simplify `this` using `[hb, hd, Module.End.one_eq_id]`. Introduce `u w hw`. Use `kq (l ∘ₗ TensorProduct.mk ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D) u) (fun g ha hc w1 w2 => ?_) w hw` and prove the remaining obligations.

Use `mem_invFun.1 hl g (u ⊗ₜ (w1 ⊗ₜ w2))` as an intermediate fact. Simplify `this` using `[ha, hc, Module.End.one_eq_id]`.
-/
theorem finrank_invFun_two_contractions (Γ A B C D X Y : Type) [Monoid Γ] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B)
    (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) (x : Representation ℂ Γ X) (y : Representation ℂ Γ Y)
    (p : A ⊗[ℂ] C →ₗ[ℂ] X) (q : B ⊗[ℂ] D →ₗ[ℂ] Y) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (ep : ∀ g u w, p (a g u ⊗ₜ[ℂ] c g w) = x g (p (u ⊗ₜ[ℂ] w)))
    (eq : ∀ g u w, q (b g u ⊗ₜ[ℂ] d g w) = y g (q (u ⊗ₜ[ℂ] w)))
    (kp : ∀ l : Module.Dual ℂ (A ⊗[ℂ] C),
      (∀ g, b g = 1 → d g = 1 → ∀ u w, l (a g u ⊗ₜ[ℂ] c g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, p z = 0 → l z = 0)
    (kq : ∀ l : Module.Dual ℂ (B ⊗[ℂ] D),
      (∀ g, a g = 1 → c g = 1 → ∀ u w, l (b g u ⊗ₜ[ℂ] d g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, q z = 0 → l z = 0) :
    Module.finrank ℂ (invFun (a.tprod (b.tprod (c.tprod d)))) = Module.finrank ℂ (invFun (x.tprod y)) := by
  rw [← (iso_tprod_shuffle a b c d).finrank_invFun]
  have ep' : ∀ g z, p (a.tprod c g z) = x g (p z) := by
    intro g z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul u w => simp [ep]
  have eq' : ∀ g z, q (b.tprod d g z) = y g (q z) := by
    intro g z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul u w => simp [eq]
  refine finrank_invFun_eq_of_surjective _ _ (TensorProduct.map p q) (TensorProduct.map_surjective hp hq)
    (fun g z => ?_) (fun l hl z hz => dual_eq_zero_of_map_eq_zero p q hp hq l ?_ ?_ z hz)
  · induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul u w =>
      rw [Representation.tprod_apply, Representation.tprod_apply x, TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul, ep', eq']
  · intro u w hu
    refine kp (l ∘ₗ (TensorProduct.mk ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D)).flip w) (fun g hb hd u1 u2 => ?_) u hu
    have := mem_invFun.1 hl g ((u1 ⊗ₜ u2) ⊗ₜ w)
    simpa [hb, hd, Module.End.one_eq_id] using this
  · intro u w hw
    refine kq (l ∘ₗ TensorProduct.mk ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D) u) (fun g ha hc w1 w2 => ?_) w hw
    have := mem_invFun.1 hl g (u ⊗ₜ (w1 ⊗ₜ w2))
    simpa [ha, hc, Module.End.one_eq_id] using this

end GlobalTheory.OneFunctional
