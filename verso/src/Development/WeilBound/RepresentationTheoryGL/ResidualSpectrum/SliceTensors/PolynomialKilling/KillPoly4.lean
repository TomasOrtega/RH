import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.WeilBound.SimpleEigenvalues.SimpleEigenvalueExtension.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.ExistsContDiffEventuallyEq

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Rs.KillingPolynomialDegreeFour

def trl {G : Type} [Group G] (a : ℝ → G) (t : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun F g := F (a t * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Introduce `G _ a F₀ ha hcont hfin`. Use `set V := Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)) with hVdef`. Establish `ha0 : a 0 = 1`. Establish `h` using `ha 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `left_eq_mul.mp h`. Establish `hcomm : ∀ s t, a s * a t = a t * a s` using `fun s t => by rw [← ha, ← ha, add_comm]`. Establish `hmem : ∀ t, (fun g => F₀ (a t * g)) ∈ V` using `fun t => Submodule.subset_span ⟨t, rfl⟩`. Establish `hinv : ∀ t, ∀ x ∈ V, trl a t x ∈ V`. Introduce `t x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨s, rfl⟩` from `h`. Establish `e : trl a t (fun g => F₀ (a s * g)) = fun g => F₀ (a (s + t) * g)`. Use function extensionality and compare the values at `g`.

Use `show F₀ (a s * (a t * g)) = F₀ (a (s + t) * g)`. Rewrite using `[ha, mul_assoc]`. Rewrite using `[e]`. Conclude with `hmem _`. Consider the case `zero => rw [map_zero]`.

Conclude with `V.zero_mem`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `V.add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `V.smul_mem c hx`.

Establish `hcV : ∀ x ∈ V, ∀ g, Continuous fun t => x (a t * g)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨s, rfl⟩` from `h`.

Introduce `g`. Establish `e : (fun t => F₀ (a s * (a t * g))) = fun t => F₀ (a t * (a s * g))`. Use function extensionality and compare the values at `t`. Rewrite using `[← mul_assoc, hcomm, mul_assoc]`. Conclude with `e ▸ hcont (a s * g)`.

Consider the case `zero => intro g`. Conclude with `continuous_const`. Consider the case `add x y _ _ hx hy => intro g`. Conclude with `(hx g).add (hy g)`. Consider the case `smul c x _ hx => intro g`.

Conclude with `continuous_const.mul (hx g)`. Establish `: FiniteDimensional ℂ V` using `hfin`. Set `T : ℝ → Module.End ℂ V` to `fun t => (trl a t).restrict (hinv t)`. Establish `hT : ∀ t (x : V) g, ((T t x : V) : G → ℂ) g = (x : G → ℂ) (a t * g)` using `fun t x g => rfl`. Establish `hTc : ∀ s t, T s * T t = T t * T s`.

Introduce `s t`. Use `LinearMap.ext fun x => Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Use `show (x : G → ℂ) (a t * (a s * g)) = (x : G → ℂ) (a s * (a t * g))`. Rewrite using `[← mul_assoc, ← mul_assoc, hcomm]`. Set `v₀ : V` to `⟨fun g => F₀ (a 0 * g), hmem 0⟩`.

Establish `hpow : ∀ j : ℕ, ∀ g, (((T 1 ^ j) v₀ : V) : G → ℂ) g = F₀ (a j * g)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro g`. Simplify using `[v₀]`.

Consider the case `succ j ih`. Introduce `g`. Rewrite using `[pow_succ', Module.End.mul_apply, hT, ih, ← mul_assoc, ← ha]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hint : IsIntegral ℂ (T 1)` using `Algebra.IsIntegral.isIntegral _`. Use `⟨minpoly ℂ (T 1), minpoly.monic hint, fun g => ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `congrArg (fun w : V => (w : G → ℂ) g) (LinearMap.congr_fun (minpoly.aeval ℂ (T 1)) v₀)`. Simplify using `only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hpow, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply] at h0`. Conclude with `h0`.

Introduce `z hz`. Establish `hev : Module.End.HasEigenvalue (T 1) z` using `Module.End.hasEigenvalue_iff_isRoot.2 hz`. Establish `hW : Module.End.eigenspace (T 1) z ≠ ⊥` using `Module.End.hasEigenvalue_iff.1 hev`. Establish `hWi : ∀ t, ∀ x ∈ Module.End.eigenspace (T 1) z, T t x ∈ Module.End.eigenspace (T 1) z`. Introduce `t x hx`.

Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Establish `e` using `LinearMap.congr_fun (hTc 1 t) x`. Rewrite `e` using `[Module.End.mul_apply, Module.End.mul_apply, hx, map_smul]`. Conclude with `e`. Take `⟨v, hvW, hv0, hμ⟩` from `UpperTheory.V.LinAlg.simEig T hTc _ _ rfl hW hWi`.

Establish `hf0 : (v : G → ℂ) ≠ 0` using `fun h => hv0 (Subtype.ext h)`. Take `⟨g₀, hg₀⟩` from `Function.ne_iff.1 hf0`. Establish `hg₀' : (v : G → ℂ) g₀ ≠ 0` using `hg₀`. Establish `heig : ∀ t g, (v : G → ℂ) (a t * g) = (v : G → ℂ) (a t * g₀) / (v : G → ℂ) g₀ * (v : G → ℂ) g`. Introduce `t g`.

Take `⟨μ, hμt⟩` from `hμ t`. Establish `e : ∀ g, (v : G → ℂ) (a t * g) = μ * (v : G → ℂ) g` using `fun g => congrArg (fun w : V => (w : G → ℂ) g) hμt`. Rewrite using `[e g, e g₀, mul_div_cancel_right₀ _ hg₀']`. Take `⟨c, hc⟩` from `UpperTheory.V.Lib.Small.exists_eq_exp (fun t => (v : G → ℂ) (a t * g₀) / (v : G → ℂ) g₀) ((hcV _ v.2 g₀).div_const _) (by simp only [ha0, one_mul, div_self hg₀']) (fun s t => by show (v : G → ℂ) (a (s + t) * g₀) / (v : G → ℂ) g₀ = (v : G → ℂ) (a s * g₀) / (v : G → ℂ) g₀ * ((v : G …`. Rewrite using `[ha, mul_assoc, heig s (a t * g₀), mul_div_assoc])`.

Use `⟨c, ?_, (v : G → ℂ), v.2, hf0, fun t g => ?_⟩` and prove the remaining obligations. Establish `h1 : (v : G → ℂ) (a 1 * g₀) = z * (v : G → ℂ) g₀` using `congrArg (fun w : V => (w : G → ℂ) g₀) (Module.End.mem_eigenspace_iff.1 hvW)`. Establish `e` using `hc 1`. Rewrite `e` using `[h1, mul_div_cancel_right₀ _ hg₀', Complex.ofReal_one, mul_one]`. Conclude with `e`.

Rewrite using `[heig t g, hc t]`.
-/
theorem killPoly4 : KillPoly := by
  intro G _ a F₀ ha hcont hfin
  set V := Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)) with hVdef
  have ha0 : a 0 = 1 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hcomm : ∀ s t, a s * a t = a t * a s := fun s t => by rw [← ha, ← ha, add_comm]
  have hmem : ∀ t, (fun g => F₀ (a t * g)) ∈ V := fun t => Submodule.subset_span ⟨t, rfl⟩
  have hinv : ∀ t, ∀ x ∈ V, trl a t x ∈ V := by
    intro t x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨s, rfl⟩ := h
      have e : trl a t (fun g => F₀ (a s * g)) = fun g => F₀ (a (s + t) * g) := by
        funext g
        show F₀ (a s * (a t * g)) = F₀ (a (s + t) * g)
        rw [ha, mul_assoc]
      rw [e]
      exact hmem _
    | zero => rw [map_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact V.smul_mem c hx
  have hcV : ∀ x ∈ V, ∀ g, Continuous fun t => x (a t * g) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨s, rfl⟩ := h
      intro g
      have e : (fun t => F₀ (a s * (a t * g))) = fun t => F₀ (a t * (a s * g)) := by
        funext t
        rw [← mul_assoc, hcomm, mul_assoc]
      exact e ▸ hcont (a s * g)
    | zero => intro g; exact continuous_const
    | add x y _ _ hx hy => intro g; exact (hx g).add (hy g)
    | smul c x _ hx => intro g; exact continuous_const.mul (hx g)
  have : FiniteDimensional ℂ V := hfin
  let T : ℝ → Module.End ℂ V := fun t => (trl a t).restrict (hinv t)
  have hT : ∀ t (x : V) g, ((T t x : V) : G → ℂ) g = (x : G → ℂ) (a t * g) := fun t x g => rfl
  have hTc : ∀ s t, T s * T t = T t * T s := by
    intro s t
    refine LinearMap.ext fun x => Subtype.ext (funext fun g => ?_)
    show (x : G → ℂ) (a t * (a s * g)) = (x : G → ℂ) (a s * (a t * g))
    rw [← mul_assoc, ← mul_assoc, hcomm]
  let v₀ : V := ⟨fun g => F₀ (a 0 * g), hmem 0⟩
  have hpow : ∀ j : ℕ, ∀ g, (((T 1 ^ j) v₀ : V) : G → ℂ) g = F₀ (a j * g) := by
    intro j
    induction j with
    | zero => intro g; simp [v₀]
    | succ j ih =>
      intro g
      rw [pow_succ', Module.End.mul_apply, hT, ih, ← mul_assoc, ← ha]
      push_cast
      rfl
  have hint : IsIntegral ℂ (T 1) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly ℂ (T 1), minpoly.monic hint, fun g => ?_, ?_⟩
  · have h0 := congrArg (fun w : V => (w : G → ℂ) g) (LinearMap.congr_fun (minpoly.aeval ℂ (T 1)) v₀)
    simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hpow, LinearMap.zero_apply,
      Submodule.coe_zero, Pi.zero_apply] at h0
    exact h0
  · intro z hz
    have hev : Module.End.HasEigenvalue (T 1) z := Module.End.hasEigenvalue_iff_isRoot.2 hz
    have hW : Module.End.eigenspace (T 1) z ≠ ⊥ := Module.End.hasEigenvalue_iff.1 hev
    have hWi : ∀ t, ∀ x ∈ Module.End.eigenspace (T 1) z, T t x ∈ Module.End.eigenspace (T 1) z := by
      intro t x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have e := LinearMap.congr_fun (hTc 1 t) x
      rw [Module.End.mul_apply, Module.End.mul_apply, hx, map_smul] at e
      exact e
    obtain ⟨v, hvW, hv0, hμ⟩ := UpperTheory.V.LinAlg.simEig T hTc _ _ rfl hW hWi
    have hf0 : (v : G → ℂ) ≠ 0 := fun h => hv0 (Subtype.ext h)
    obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hf0
    have hg₀' : (v : G → ℂ) g₀ ≠ 0 := hg₀
    have heig : ∀ t g, (v : G → ℂ) (a t * g) = (v : G → ℂ) (a t * g₀) / (v : G → ℂ) g₀ * (v : G → ℂ) g := by
      intro t g
      obtain ⟨μ, hμt⟩ := hμ t
      have e : ∀ g, (v : G → ℂ) (a t * g) = μ * (v : G → ℂ) g := fun g =>
        congrArg (fun w : V => (w : G → ℂ) g) hμt
      rw [e g, e g₀, mul_div_cancel_right₀ _ hg₀']
    obtain ⟨c, hc⟩ := UpperTheory.V.Lib.Small.exists_eq_exp (fun t => (v : G → ℂ) (a t * g₀) / (v : G → ℂ) g₀)
      ((hcV _ v.2 g₀).div_const _) (by simp only [ha0, one_mul, div_self hg₀'])
      (fun s t => by
        show (v : G → ℂ) (a (s + t) * g₀) / (v : G → ℂ) g₀ =
          (v : G → ℂ) (a s * g₀) / (v : G → ℂ) g₀ * ((v : G → ℂ) (a t * g₀) / (v : G → ℂ) g₀)
        rw [ha, mul_assoc, heig s (a t * g₀), mul_div_assoc])
    refine ⟨c, ?_, (v : G → ℂ), v.2, hf0, fun t g => ?_⟩
    · have h1 : (v : G → ℂ) (a 1 * g₀) = z * (v : G → ℂ) g₀ :=
        congrArg (fun w : V => (w : G → ℂ) g₀) (Module.End.mem_eigenspace_iff.1 hvW)
      have e := hc 1
      rw [h1, mul_div_cancel_right₀ _ hg₀', Complex.ofReal_one, mul_one] at e
      exact e
    · rw [heig t g, hc t]

end PositivityTheory.Rg.Rs.KillingPolynomialDegreeFour

end
