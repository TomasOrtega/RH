import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubquotientJacUIntertwining
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ _ _ n m e X G₁ _ _ _ π ι hι U M Λ hMU hU hM hsm hNinv hequiv`. Use `set N := unipRad k e with hNdef`. Use `set L : GL (Fin m) k →* GL (Fin n) k := (leviEmb k e).comp (midIncl k m) with hLdef`. Use `set σ := GlobalTheory.PRep.sub π U hU with hσ`. Set `P : Submodule ℂ X` to `(twKer σ N 1).map U.subtype`.

Establish `hgen : ∀ g ∈ N, ∀ ψ ∈ U, π g ψ - ψ ∈ P`. Introduce `g hg ψ hψ`. Use `⟨σ g ⟨ψ, hψ⟩ - (((1 : N →* ℂˣ) ⟨g, hg⟩ : ℂˣ) : ℂ) • ⟨ψ, hψ⟩, Submodule.subset_span ⟨⟨g, hg⟩, ⟨ψ, hψ⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[σ, GlobalTheory.PRep.sub]`. Establish `hσsm : IsSmooth σ`.

Introduce `v`. Establish `: {g | σ g v = v} = {g | π g (v : X) = v}`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Subtype.ext_iff]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hsm v v.2`. Establish `step1 : ∀ φ ∈ M, φ ∈ P → Λ φ = 0`. Introduce `φ hφM hφP`. Take `⟨ψ, hψ, rfl⟩` from `hφP`.

Use `GlobalTheory.MidJacquet.map_eq_zero_of_unipRad e hσsm (m := 1) (Λ ∘ₗ U.subtype ∘ₗ LinearMap.proj 0) (fun _ => ψ) (fun g hg => ?_) (fun _ => hψ)` as an intermediate fact. Simplify using `using this`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]`. Conclude with `hNinv _ hφM g hg`. Set `q : M →ₗ[ℂ] X ⧸ P` to `P.mkQ ∘ₗ M.subtype`.

Establish `hker : LinearMap.ker q ≤ LinearMap.ker (Λ ∘ₗ M.subtype)`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Conclude with `step1 x x.2 ((Submodule.Quotient.mk_eq_zero _).1 hx)`. Set `φ₀ : LinearMap.range q →ₗ[ℂ] (G₁ → ℂ)` to `(LinearMap.ker q).liftQ (Λ ∘ₗ M.subtype) hker ∘ₗ q.quotKerEquivRange.symm.toLinearMap`.

Establish `hφ₀ : ∀ x : M, φ₀ ⟨q x, LinearMap.mem_range_self q x⟩ = Λ x`. Introduce `x`. Simplify using `only [φ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply, Submodule.coe_subtype]`. Take `⟨ext0, hext0⟩` from `LinearMap.exists_extend φ₀`. Set `Λ₀ : X →ₗ[ℂ] (G₁ → ℂ)` to `ext0 ∘ₗ P.mkQ`.

Establish `hΛ₀M : ∀ φ ∈ M, Λ₀ φ = Λ φ`. Introduce `φ hφ`. Use `congrArg (fun F => F ⟨q ⟨φ, hφ⟩, LinearMap.mem_range_self q _⟩) hext0` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this`. Rewrite `this` using `[hφ₀]`.

Conclude with `this`. Establish `hΛ₀P : ∀ φ ∈ P, Λ₀ φ = 0`. Introduce `φ hφ`. Simplify using `[Λ₀, (Submodule.Quotient.mk_eq_zero _).2 hφ]`. Set `H` to `ι.range`.

Set `r : G₁ → G₁` to `fun g => (QuotientGroup.mk g : G₁ ⧸ H).out`. Establish `hrmem : ∀ g, (r g)⁻¹ * g ∈ H`. Introduce `g`. Establish `: (QuotientGroup.mk (r g) : G₁ ⧸ H) = QuotientGroup.mk g` using `Quotient.out_eq' _`. Conclude with `QuotientGroup.eq.1 this`.

Set `hh : G₁ → GL (Fin m) k` to `fun g => (MonoidHom.ofInjective hι).symm ⟨_, hrmem g⟩`. Establish `hιh : ∀ g, ι (hh g) = (r g)⁻¹ * g`. Introduce `g`. Establish `h1` using `congrArg Subtype.val ((MonoidHom.ofInjective hι).apply_symm_apply ⟨_, hrmem g⟩)`. Rewrite `h1` using `[MonoidHom.ofInjective_apply]`.

Conclude with `h1`. Establish `hdec : ∀ g, r g * ι (hh g) = g`. Introduce `g`. Rewrite using `[hιh]`. Use `group`.

Establish `hr : ∀ g x, r (g * ι x) = r g`. Introduce `g x`. Use `show (QuotientGroup.mk (g * ι x) : G₁ ⧸ H).out = (QuotientGroup.mk g : G₁ ⧸ H).out`. Use `congr 1`. Conclude with `QuotientGroup.eq.2 (by rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact ⟨x⁻¹, map_inv ι x⟩)`.

Establish `hhm : ∀ g x, hh (g * ι x) = hh g * x`. Introduce `g x`. Apply `hι` to reduce the goal to its premises. Rewrite using `[hιh, map_mul, hιh, hr]`. Use `group`.

Set `Λ' : X →ₗ[ℂ] (G₁ → ℂ)` to `LinearMap.pi fun g => LinearMap.proj (r g) ∘ₗ Λ₀ ∘ₗ π (L (hh g))`. Establish `hΛ' : ∀ φ g, Λ' φ g = Λ₀ (π (L (hh g)) φ) (r g)` using `fun _ _ => rfl`. Establish `hrR : ∀ x (f : G₁ → ℂ) y, rightReg ℂ G₁ ℂ x f y = f (y * x)` using `fun _ _ _ => rfl`. Use `⟨Λ', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `φ hφ`.

Use function extensionality and compare the values at `g`. Rewrite using `[hΛ', hΛ₀M _ (hM _ _ hφ)]`. Use `congrFun (hequiv φ hφ (hh g)) (r g)` as an intermediate fact. Rewrite `this` using `[hrR, hdec]`. Conclude with `this`.

Introduce `φ hφ u hu`. Use function extensionality and compare the values at `g`. Rewrite using `[hΛ', hΛ']`. Establish `hl : L (hh g) ∈ Subgroup.normalizer (N : Set (GL (Fin n) k))` using `leviEmb_mem_normalizer k e _`. Establish `hn : L (hh g) * u * (L (hh g))⁻¹ ∈ N` using `(Subgroup.mem_normalizer_iff.1 hl u).1 hu`.

Establish `hdiff : π (L (hh g)) (π u φ) - π (L (hh g)) φ ∈ P`. Use `hgen _ hn (π (L (hh g)) φ) (hU _ _ hφ)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`.

Use `group`. Use `hΛ₀P _ hdiff` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Rewrite using `[this]`. Introduce `φ hφ x`.

Use function extensionality and compare the values at `g`. Rewrite using `[hΛ', hrR, hΛ', hhm, hr, map_mul L, map_mul π, Module.End.mul_apply]`. Both sides reduce to the same expression.
-/
theorem ext_sub_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (X G₁ : Type) [AddCommGroup X] [Module ℂ X] [Group G₁]
    (π : Representation ℂ (GL (Fin n) k) X) (ι : GL (Fin m) k →* G₁), Function.Injective ι →
    ∀ (U M : Submodule ℂ X) (Λ : X →ₗ[ℂ] (G₁ → ℂ)), M ≤ U → (∀ g, ∀ φ ∈ U, π g φ ∈ U) → (∀ g, ∀ φ ∈ M, π g φ ∈ M) →
      (∀ φ ∈ U, IsOpen {g | π g φ = φ}) →
      (∀ φ ∈ M, ∀ u ∈ unipRad k e, Λ (π u φ) = Λ φ) →
      (∀ φ ∈ M, ∀ h, Λ (π (leviEmb k e (midIncl k m h)) φ) = rightReg ℂ G₁ ℂ (ι h) (Λ φ)) →
      ∃ Λ' : X →ₗ[ℂ] (G₁ → ℂ), (∀ φ ∈ M, Λ' φ = Λ φ) ∧ (∀ φ ∈ U, ∀ u ∈ unipRad k e, Λ' (π u φ) = Λ' φ) ∧
        ∀ φ ∈ U, ∀ h, Λ' (π (leviEmb k e (midIncl k m h)) φ) = rightReg ℂ G₁ ℂ (ι h) (Λ' φ) := by
  intro k _ _ _ _ n m e X G₁ _ _ _ π ι hι U M Λ hMU hU hM hsm hNinv hequiv
  classical
  set N := unipRad k e with hNdef
  set L : GL (Fin m) k →* GL (Fin n) k := (leviEmb k e).comp (midIncl k m) with hLdef
  set σ := GlobalTheory.PRep.sub π U hU with hσ
  let P : Submodule ℂ X := (twKer σ N 1).map U.subtype
  have hgen : ∀ g ∈ N, ∀ ψ ∈ U, π g ψ - ψ ∈ P := by
    intro g hg ψ hψ
    refine ⟨σ g ⟨ψ, hψ⟩ - (((1 : N →* ℂˣ) ⟨g, hg⟩ : ℂˣ) : ℂ) • ⟨ψ, hψ⟩,
      Submodule.subset_span ⟨⟨g, hg⟩, ⟨ψ, hψ⟩, rfl⟩, ?_⟩
    simp [σ, GlobalTheory.PRep.sub]

  have hσsm : IsSmooth σ := by
    intro v
    have : {g | σ g v = v} = {g | π g (v : X) = v} := by
      ext g
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hsm v v.2
  have step1 : ∀ φ ∈ M, φ ∈ P → Λ φ = 0 := by
    intro φ hφM hφP
    obtain ⟨ψ, hψ, rfl⟩ := hφP
    have := GlobalTheory.MidJacquet.map_eq_zero_of_unipRad e hσsm (m := 1)
      (Λ ∘ₗ U.subtype ∘ₗ LinearMap.proj 0) (fun _ => ψ) (fun g hg => ?_) (fun _ => hψ)
    · simpa using this
    · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
      exact hNinv _ hφM g hg

  let q : M →ₗ[ℂ] X ⧸ P := P.mkQ ∘ₗ M.subtype
  have hker : LinearMap.ker q ≤ LinearMap.ker (Λ ∘ₗ M.subtype) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    exact step1 x x.2 ((Submodule.Quotient.mk_eq_zero _).1 hx)
  let φ₀ : LinearMap.range q →ₗ[ℂ] (G₁ → ℂ) :=
    (LinearMap.ker q).liftQ (Λ ∘ₗ M.subtype) hker ∘ₗ q.quotKerEquivRange.symm.toLinearMap
  have hφ₀ : ∀ x : M, φ₀ ⟨q x, LinearMap.mem_range_self q x⟩ = Λ x := by
    intro x
    simp only [φ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
      Submodule.coe_subtype]
  obtain ⟨ext0, hext0⟩ := LinearMap.exists_extend φ₀
  let Λ₀ : X →ₗ[ℂ] (G₁ → ℂ) := ext0 ∘ₗ P.mkQ
  have hΛ₀M : ∀ φ ∈ M, Λ₀ φ = Λ φ := by
    intro φ hφ
    have := congrArg (fun F => F ⟨q ⟨φ, hφ⟩, LinearMap.mem_range_self q _⟩) hext0
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [hφ₀] at this
    exact this
  have hΛ₀P : ∀ φ ∈ P, Λ₀ φ = 0 := by
    intro φ hφ
    simp [Λ₀, (Submodule.Quotient.mk_eq_zero _).2 hφ]

  let H := ι.range
  let r : G₁ → G₁ := fun g => (QuotientGroup.mk g : G₁ ⧸ H).out
  have hrmem : ∀ g, (r g)⁻¹ * g ∈ H := by
    intro g
    have : (QuotientGroup.mk (r g) : G₁ ⧸ H) = QuotientGroup.mk g := Quotient.out_eq' _
    exact QuotientGroup.eq.1 this
  let hh : G₁ → GL (Fin m) k := fun g => (MonoidHom.ofInjective hι).symm ⟨_, hrmem g⟩
  have hιh : ∀ g, ι (hh g) = (r g)⁻¹ * g := by
    intro g
    have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hι).apply_symm_apply ⟨_, hrmem g⟩)
    rw [MonoidHom.ofInjective_apply] at h1
    exact h1
  have hdec : ∀ g, r g * ι (hh g) = g := by
    intro g; rw [hιh]; group
  have hr : ∀ g x, r (g * ι x) = r g := by
    intro g x
    show (QuotientGroup.mk (g * ι x) : G₁ ⧸ H).out = (QuotientGroup.mk g : G₁ ⧸ H).out
    congr 1
    exact QuotientGroup.eq.2 (by rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact ⟨x⁻¹, map_inv ι x⟩)
  have hhm : ∀ g x, hh (g * ι x) = hh g * x := by
    intro g x
    apply hι
    rw [hιh, map_mul, hιh, hr]
    group
  let Λ' : X →ₗ[ℂ] (G₁ → ℂ) := LinearMap.pi fun g => LinearMap.proj (r g) ∘ₗ Λ₀ ∘ₗ π (L (hh g))
  have hΛ' : ∀ φ g, Λ' φ g = Λ₀ (π (L (hh g)) φ) (r g) := fun _ _ => rfl
  have hrR : ∀ x (f : G₁ → ℂ) y, rightReg ℂ G₁ ℂ x f y = f (y * x) := fun _ _ _ => rfl
  refine ⟨Λ', ?_, ?_, ?_⟩
  · intro φ hφ
    funext g
    rw [hΛ', hΛ₀M _ (hM _ _ hφ)]
    have := congrFun (hequiv φ hφ (hh g)) (r g)
    rw [hrR, hdec] at this
    exact this
  · intro φ hφ u hu
    funext g
    rw [hΛ', hΛ']
    have hl : L (hh g) ∈ Subgroup.normalizer (N : Set (GL (Fin n) k)) := leviEmb_mem_normalizer k e _
    have hn : L (hh g) * u * (L (hh g))⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 hl u).1 hu
    have hdiff : π (L (hh g)) (π u φ) - π (L (hh g)) φ ∈ P := by
      have := hgen _ hn (π (L (hh g)) φ) (hU _ _ hφ)
      convert this using 2
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    have := hΛ₀P _ hdiff
    rw [map_sub, sub_eq_zero] at this
    rw [this]
  · intro φ hφ x
    funext g
    rw [hΛ', hrR, hΛ', hhm, hr, map_mul L, map_mul π, Module.End.mul_apply]
    rfl

end GlobalTheory
