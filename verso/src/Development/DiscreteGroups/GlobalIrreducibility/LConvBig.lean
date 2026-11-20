import Development.DiscreteGroups.GlobalIrreducibility.LConvBigD
import GroundTheory.AutomorphicForms.SmoothRepSchur

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

section Irr

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/- English proof (translation)
Break down `IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hv0` to reduce the goal to its premises. Establish `: v ∈ (⟨S, hS⟩ : Subrepresentation ρ)` using `hv`. Rewrite `this` using `[h]`.

Conclude with `(Submodule.mem_bot ℂ).1 this`. Establish `: w ∈ (⊤ : Subrepresentation ρ)` using `Submodule.mem_top`. Rewrite `this` using `[← h]`. Conclude with `this`.
-/
theorem irr_mem [ρ.IsIrreducible] (S : Submodule ℂ V) (hS : ∀ g, ∀ ⦃x⦄, x ∈ S → ρ g x ∈ S) {v : V} (hv0 : v ≠ 0)
    (hv : v ∈ S) (w : V) : w ∈ S := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h
  · exfalso
    apply hv0
    have : v ∈ (⟨S, hS⟩ : Subrepresentation ρ) := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : w ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact this

/- English proof (translation)
Assume the negation of the conclusion as `hb0`. Set `S : Submodule ℂ V` to `{ carrier := {x | ∀ g, l (ρ g x) = 0} add_mem' := fun {x y} hx hy g => by rw [map_add, map_add, hx g, hy g, add_zero] zero_mem' := fun g => by rw [map_zero, map_zero] smul_mem' := fun c x hx g => by rw [map_smul, map_smul, hx g, smul_zero] }`. Establish `hS : ∀ h, ∀ ⦃x⦄, x ∈ S → ρ h x ∈ S` using `fun h x hx g => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `hx (g * h)`.

Use `irr_mem S hS hb0 hb v₀ 1` as an intermediate fact. Rewrite `this` using `[map_one, Module.End.one_apply]`. Conclude with `hv₀ this`.
-/
theorem eq_zero_of_forall [ρ.IsIrreducible] (l : Module.Dual ℂ V) {v₀ : V} (hv₀ : l v₀ ≠ 0) {b : V}
    (hb : ∀ g, l (ρ g b) = 0) : b = 0 := by
  by_contra hb0
  let S : Submodule ℂ V :=
    { carrier := {x | ∀ g, l (ρ g x) = 0}
      add_mem' := fun {x y} hx hy g => by rw [map_add, map_add, hx g, hy g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c x hx g => by rw [map_smul, map_smul, hx g, smul_zero] }
  have hS : ∀ h, ∀ ⦃x⦄, x ∈ S → ρ h x ∈ S := fun h x hx g => by
    rw [← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have := irr_mem S hS hb0 hb v₀ 1
  rw [map_one, Module.End.one_apply] at this
  exact hv₀ this

end Irr

/- English proof (translation)
Introduce `k _ _ _ _ ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ hW ⟨v₁, v₂, hX, h0⟩`. Use `π₁.irr` as an intermediate fact. Use `π₂.irr` as an intermediate fact. Take `⟨ω₁, -, h₁⟩` from `GlobalTheory.LocGL.exists_smooth_hasCentralChar π₁.smooth π₁.irr`. Take `⟨ω₂, -, h₂⟩` from `GlobalTheory.LocGL.exists_smooth_hasCentralChar π₂.smooth π₂.irr`.

Take `rfl` from `centralChar_eq hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hX h0`. Establish `hall : ∀ (a : π₁.V) (b : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) a) = l₂ (π₂.ρ (corner g) b)) → ∀ g, l₁ (π₁.ρ g a) = l₂ (π₂.ρ g b)` using `fun a b hab g => agree_all hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hab g`. Set `Y : Submodule ℂ (π₁.V × π₂.V)` to `{ carrier := {x | ∀ g, l₁ (π₁.ρ g x.1) = l₂ (π₂.ρ g x.2)} add_mem' := fun {x y} hx hy g => by`. Rewrite using `[Prod.fst_add, Prod.snd_add, map_add, map_add, map_add, map_add, hx g, hy g]`. Use the proof step `zero_mem' := fun g => by simp`.

Use the proof step `smul_mem' := fun c x hx g => by`. Rewrite using `[Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, map_smul, map_smul, hx g] }`. Establish `hY : ∀ h (x : π₁.V × π₂.V), x ∈ Y → (π₁.ρ h x.1, π₂.ρ h x.2) ∈ Y` using `fun h x hx g => by show l₁ (π₁.ρ g (π₁.ρ h x.1)) = l₂ (π₂.ρ g (π₂.ρ h x.2))`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Conclude with `hx (g * h)`.

Establish `hv : (v₁, v₂) ∈ Y` using `hall v₁ v₂ hX`. Establish `h0' : l₂ v₂ ≠ 0`. Use `hv 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one, Module.End.one_apply, Module.End.one_apply]`. Rewrite using `[← this]` and apply the resulting hypothesis.

Establish `hv₁ : v₁ ≠ 0` using `fun e => h0 (by rw [e, map_zero])`. Establish `hv₂ : v₂ ≠ 0` using `fun e => h0' (by rw [e, map_zero])`. Set `f₁ : Y →ₗ[ℂ] π₁.V` to `(LinearMap.fst ℂ π₁.V π₂.V).comp Y.subtype`. Set `f₂ : Y →ₗ[ℂ] π₂.V` to `(LinearMap.snd ℂ π₁.V π₂.V).comp Y.subtype`. Establish `inj₁ : Function.Injective f₁`.

Use `(injective_iff_map_eq_zero f₁).2 fun y hy => ?_` and prove the remaining obligations. Establish `hy1 : (y : π₁.V × π₂.V).1 = 0` using `hy`. Establish `hy2 : (y : π₁.V × π₂.V).2 = 0` using `eq_zero_of_forall (ρ := π₂.ρ) l₂ h0' fun g => by`. Rewrite using `[← y.2 g, hy1, map_zero, map_zero]`. Conclude with `Subtype.ext (Prod.ext hy1 hy2)`.

Establish `inj₂ : Function.Injective f₂`. Use `(injective_iff_map_eq_zero f₂).2 fun y hy => ?_` and prove the remaining obligations. Establish `hy2 : (y : π₁.V × π₂.V).2 = 0` using `hy`. Establish `hy1 : (y : π₁.V × π₂.V).1 = 0` using `eq_zero_of_forall (ρ := π₁.ρ) l₁ h0 fun g => by`. Rewrite using `[y.2 g, hy2, map_zero, map_zero]`.

Conclude with `Subtype.ext (Prod.ext hy1 hy2)`. Establish `surj₁ : Function.Surjective f₁` using `fun a => by`. Use `irr_mem (ρ := π₁.ρ) (LinearMap.range f₁) (fun h x hx => by` as an intermediate fact. Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₁ ⟨⟨_, hv⟩, rfl⟩ a`.

Conclude with `this`. Establish `surj₂ : Function.Surjective f₂` using `fun b => by`. Use `irr_mem (ρ := π₂.ρ) (LinearMap.range f₂) (fun h x hx => by` as an intermediate fact. Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₂ ⟨⟨_, hv⟩, rfl⟩ b`.

Conclude with `this`. Set `e₁` to `LinearEquiv.ofBijective f₁ ⟨inj₁, surj₁⟩`. Set `e₂` to `LinearEquiv.ofBijective f₂ ⟨inj₂, surj₂⟩`. Set `T : π₁.V ≃ₗ[ℂ] π₂.V` to `e₁.symm.trans e₂`. Establish `hT : ∀ a, (a, T a) ∈ Y` using `fun a => by`.

Establish `h1 : ((e₁.symm a : Y) : π₁.V × π₂.V).1 = a` using `e₁.apply_symm_apply a`. Use `(e₁.symm a).2` as an intermediate fact. Rewrite `this` using `[← Prod.mk.eta (p := ((e₁.symm a : Y) : π₁.V × π₂.V)), h1]`. Conclude with `this`. Establish `hint : ∀ g a, T (π₁.ρ g a) = π₂.ρ g (T a)` using `fun g a => by`.

Establish `h1 : e₁.symm (π₁.ρ g a) = ⟨_, hY g _ (hT a)⟩` using `e₁.injective (by rw [e₁.apply_symm_apply]; rfl)`. Use `show e₂ (e₁.symm (π₁.ρ g a)) = _`. Rewrite using `[h1]`. Both sides reduce to the same expression. Set `Tint : Representation.IntertwiningMap π₁.ρ π₂.ρ` to `{ toLinearMap := T.toLinearMap isIntertwining' := fun g => LinearMap.ext fun a => hint g a }`.

Conclude with `⟨Tint.ofBijective T.bijective⟩`.
-/
theorem bigCell : BigCell := by
  intro k _ _ _ _ ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ hW ⟨v₁, v₂, hX, h0⟩
  have := π₁.irr
  have := π₂.irr
  obtain ⟨ω₁, -, h₁⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₁.smooth π₁.irr
  obtain ⟨ω₂, -, h₂⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₂.smooth π₂.irr
  obtain rfl := centralChar_eq hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hX h0
  have hall : ∀ (a : π₁.V) (b : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) a) = l₂ (π₂.ρ (corner g) b)) →
      ∀ g, l₁ (π₁.ρ g a) = l₂ (π₂.ρ g b) := fun a b hab g =>
    agree_all hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hab g
  let Y : Submodule ℂ (π₁.V × π₂.V) :=
    { carrier := {x | ∀ g, l₁ (π₁.ρ g x.1) = l₂ (π₂.ρ g x.2)}
      add_mem' := fun {x y} hx hy g => by
        rw [Prod.fst_add, Prod.snd_add, map_add, map_add, map_add, map_add, hx g, hy g]
      zero_mem' := fun g => by simp
      smul_mem' := fun c x hx g => by
        rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, map_smul, map_smul, hx g] }
  have hY : ∀ h (x : π₁.V × π₂.V), x ∈ Y → (π₁.ρ h x.1, π₂.ρ h x.2) ∈ Y := fun h x hx g => by
    show l₁ (π₁.ρ g (π₁.ρ h x.1)) = l₂ (π₂.ρ g (π₂.ρ h x.2))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have hv : (v₁, v₂) ∈ Y := hall v₁ v₂ hX
  have h0' : l₂ v₂ ≠ 0 := by
    have := hv 1
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
    rwa [← this]
  have hv₁ : v₁ ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hv₂ : v₂ ≠ 0 := fun e => h0' (by rw [e, map_zero])

  let f₁ : Y →ₗ[ℂ] π₁.V := (LinearMap.fst ℂ π₁.V π₂.V).comp Y.subtype
  let f₂ : Y →ₗ[ℂ] π₂.V := (LinearMap.snd ℂ π₁.V π₂.V).comp Y.subtype
  have inj₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero f₁).2 fun y hy => ?_
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := hy
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := eq_zero_of_forall (ρ := π₂.ρ) l₂ h0' fun g => by
      rw [← y.2 g, hy1, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have inj₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero f₂).2 fun y hy => ?_
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := hy
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := eq_zero_of_forall (ρ := π₁.ρ) l₁ h0 fun g => by
      rw [y.2 g, hy2, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have surj₁ : Function.Surjective f₁ := fun a => by
    have := irr_mem (ρ := π₁.ρ) (LinearMap.range f₁) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₁ ⟨⟨_, hv⟩, rfl⟩ a
    exact this
  have surj₂ : Function.Surjective f₂ := fun b => by
    have := irr_mem (ρ := π₂.ρ) (LinearMap.range f₂) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₂ ⟨⟨_, hv⟩, rfl⟩ b
    exact this
  let e₁ := LinearEquiv.ofBijective f₁ ⟨inj₁, surj₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨inj₂, surj₂⟩
  let T : π₁.V ≃ₗ[ℂ] π₂.V := e₁.symm.trans e₂
  have hT : ∀ a, (a, T a) ∈ Y := fun a => by
    have h1 : ((e₁.symm a : Y) : π₁.V × π₂.V).1 = a := e₁.apply_symm_apply a
    have := (e₁.symm a).2
    rw [← Prod.mk.eta (p := ((e₁.symm a : Y) : π₁.V × π₂.V)), h1] at this
    exact this
  have hint : ∀ g a, T (π₁.ρ g a) = π₂.ρ g (T a) := fun g a => by
    have h1 : e₁.symm (π₁.ρ g a) = ⟨_, hY g _ (hT a)⟩ := e₁.injective (by rw [e₁.apply_symm_apply]; rfl)
    show e₂ (e₁.symm (π₁.ρ g a)) = _
    rw [h1]
    rfl
  let Tint : Representation.IntertwiningMap π₁.ρ π₂.ρ :=
    { toLinearMap := T.toLinearMap
      isIntertwining' := fun g => LinearMap.ext fun a => hint g a }
  exact ⟨Tint.ofBijective T.bijective⟩

end DiscreteGroups.sglob.LConv

end
