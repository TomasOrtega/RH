import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Depth

variable {O : Type} [CommRing O] (bar : O → O) (ψ w : InvFun O)

def IsStarDepth {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
    v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v ∧ B ∈ rcone γ ∧ B - t • toReal v ∈ rcone γ

def depthSet (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Set ℝ :=
  {t | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Finite O X₁) (r : (Fin n → O) →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ (∀ x, (∀ y, B₁ x y = 0) → x = 0) ∧
    (∀ a b, B a b = B₁ (r a) (r b)) ∧ IsStarDepth bar ψ w B₁ t}

variable {bar ψ w}

/- English proof (translation)
Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩`. Establish `hker : LinearMap.ker r ≤ LinearMap.ker ρ`. Introduce `x hx`.

Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Use `hrad _ fun y => ?_` and prove the remaining obligations. Take `⟨y', rfl⟩` from `hρ y`. Establish `h1` using `hB x y'`. Establish `h2` using `hB 0 y'`.

Simplify using `only [hx, map_zero, LinearMap.zero_apply] at h1 h2`. Rewrite using `[← h1, h2]`. Set `ρ' : (Fin m → O) →ₗ[O] X₁` to `(LinearMap.ker r).liftQ ρ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap`. Establish `hρ' : ∀ a, ρ' (r a) = ρ a` using `fun a => by`. Establish `: (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]`. Use `⟨X₁, i1, i2, i3, ρ', B₁, fun x => ?_, hrad, fun a b => ?_, hd⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hρ x`.

Conclude with `⟨r a, hρ' a⟩`. Take `⟨a, rfl⟩` from `hr a`. Take `⟨b, rfl⟩` from `hr b`. Rewrite using `[hρ', hρ']`. Conclude with `hB a b`.

Introduce and unpack `⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩`. Conclude with `⟨X₁, i1, i2, i3, ρ ∘ₗ r, B₁, hρ.comp hr, hrad, fun a b => hB (r a) (r b), hd⟩`.
-/
theorem depthSet_comp {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r)
    (B : (Fin m → O) → (Fin m → O) → ℝ) : depthSet bar ψ w n (fun a b => B (r a) (r b)) = depthSet bar ψ w m B := by
  ext t
  constructor
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    have hker : LinearMap.ker r ≤ LinearMap.ker ρ := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      refine hrad _ fun y => ?_
      obtain ⟨y', rfl⟩ := hρ y
      have h1 := hB x y'
      have h2 := hB 0 y'
      simp only [hx, map_zero, LinearMap.zero_apply] at h1 h2
      rw [← h1, h2]
    let ρ' : (Fin m → O) →ₗ[O] X₁ :=
      (LinearMap.ker r).liftQ ρ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hρ' : ∀ a, ρ' (r a) = ρ a := fun a => by
      have : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    refine ⟨X₁, i1, i2, i3, ρ', B₁, fun x => ?_, hrad, fun a b => ?_, hd⟩
    · obtain ⟨a, rfl⟩ := hρ x
      exact ⟨r a, hρ' a⟩
    · obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      rw [hρ', hρ']
      exact hB a b
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    exact ⟨X₁, i1, i2, i3, ρ ∘ₗ r, B₁, hρ.comp hr, hrad, fun a b => hB (r a) (r b), hd⟩

/- English proof (translation)
Use `Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, hρ, _, _, _, _, _, v, _, _, _, hv, _⟩ => ?_` and prove the remaining obligations. Use `haveI : Subsingleton X₁ := ⟨fun x y => by`. Take `⟨a, rfl⟩` from `hρ x`. Take `⟨b, rfl⟩` from `hρ y`. Rewrite using `[Subsingleton.elim a b]⟩`.

Rewrite `hv` using `[InvFun.evalZ, w.eval_of_subsingleton]`. Conclude with `zero_ne_one hv`.
-/
theorem depthSet_zero (B : (Fin 0 → O) → (Fin 0 → O) → ℝ) : depthSet bar ψ w 0 B = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, hρ, _, _, _, _, _, v, _, _, _, hv, _⟩ => ?_
  haveI : Subsingleton X₁ := ⟨fun x y => by
    obtain ⟨a, rfl⟩ := hρ x
    obtain ⟨b, rfl⟩ := hρ y
    rw [Subsingleton.elim a b]⟩
  rw [InvFun.evalZ, w.eval_of_subsingleton] at hv
  exact zero_ne_one hv

variable (bar ψ w)

def starDepth : InvFun O where
  toFun n B := sSup (depthSet bar ψ w n B)
  inv n m r hr B := by rw [depthSet_comp hr]
  zero B := by rw [depthSet_zero, Real.sSup_empty]

def starFun (K D : ℕ) : InvFun O where
  toFun n B := D * (K * ψ.toFun n B + (starDepth bar ψ w).toFun n B)
  inv n m r hr B := by simp only [InvFun.inv _ _ _ r hr]
  zero B := by simp only [InvFun.zero, mul_zero, add_zero]

variable {bar ψ w}

/- English proof (translation)
The claim follows from `Real.sSup_nonneg fun _ h => h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1`.
-/
theorem starDepth_toFun_nonneg (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : 0 ≤ (starDepth bar ψ w).toFun n B :=
  Real.sSup_nonneg fun _ h => h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1

/- English proof (translation)
Take `⟨n, r, hr⟩` from `Module.Finite.exists_fin' O X`. Rewrite using `[InvFun.eval_eq _ hr]`. Conclude with `starDepth_toFun_nonneg n _`.
-/
theorem starDepth_eval_nonneg {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    0 ≤ (starDepth bar ψ w).eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  exact starDepth_toFun_nonneg n _

/- English proof (translation)
Take `⟨n, r, hr⟩` from `Module.Finite.exists_fin' O X`. Rewrite using `[InvFun.eval_eq _ hr, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]`. Both sides reduce to the same expression.
-/
theorem starFun_eval {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ) (B : X → X → ℝ) :
    (starFun bar ψ w K D).eval X B = D * (K * ψ.eval X B + (starDepth bar ψ w).eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  rfl

/- English proof (translation)
The claim follows from `starFun_eval K D _`.
-/
theorem starFun_evalZ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (β : LinearMap.BilinForm ℤ X) :
    (starFun bar ψ w K D).evalZ β = D * (K * ψ.evalZ β + (starDepth bar ψ w).evalZ β) :=
  starFun_eval K D _

/- English proof (translation)
The claim follows from `starFun_eval K D _`.
-/
theorem starFun_evalR {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (starFun bar ψ w K D) B = D * (K * evalR ψ B + evalR (starDepth bar ψ w) B) :=
  starFun_eval K D _

/- English proof (translation)
Establish `: depthSet bar ψ (zeroFun O) n B = ∅` using `Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, _, _, _, _, _, _, v, _, _, _, hv, _⟩ => by`. Rewrite `hv` using `[zeroFun_evalZ]`. Conclude with `zero_ne_one hv`. Use `show sSup _ = 0`. Rewrite using `[this, Real.sSup_empty]`.
-/
theorem starDepth_zeroFun (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : (starDepth bar ψ (zeroFun O)).toFun n B = 0 := by
  have : depthSet bar ψ (zeroFun O) n B = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, _, _, _, _, _, _, v, _, _, _, hv, _⟩ => by
      rw [zeroFun_evalZ] at hv
      exact zero_ne_one hv
  show sSup _ = 0
  rw [this, Real.sSup_empty]

end Depth

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

/- English proof (translation)
Introduce `σ hσ n B` and use `by show _ * (_ * _ + _) = _ * (_ * _ + _) rw [hψ σ hσ n B, hd σ hσ n B]`.
-/
theorem isTwInv_starFun {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hd : IsTwInv H (starDepth H.bar ψ w)) (K D : ℕ) :
    IsTwInv H (starFun H.bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

end Twist

end GlobalTheory.PolFan
