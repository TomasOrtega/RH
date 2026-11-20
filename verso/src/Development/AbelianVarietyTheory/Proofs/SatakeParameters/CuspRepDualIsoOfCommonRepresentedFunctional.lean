import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ContraPair

/- English proof (translation)
Introduce `E _ _ _ a π s₁ s₂ hs₁ hs₂ B₁ B₂ hl₁ hr₁ hf₁ hc₁ hL₁ hl₂ hr₂ hf₂ hc₂ hL₂ ψ₁ ψ₂ hψ₁ hψ`. Establish `irr : ∀ P : Submodule ℂ π.V, (∀ o, ∀ x ∈ P, π.op o x ∈ P) → P ≠ ⊥ → P = ⊤`. Introduce `P hP h0`. Establish `hst : IsStable (P.map π.V.subtype)`. Introduce and unpack `o _ ⟨x, hx, rfl⟩`.

Conclude with `⟨π.op o x, hP o x hx, rfl⟩`. Establish `e` using `Submodule.comap_map_eq_of_injective π.V.injective_subtype P`. Break down `π.irred _ (Submodule.map_subtype_le _ _) hst with h | h` into its components or cases. Conclude with `absurd (by rw [← e, h, Submodule.comap_bot, Submodule.ker_subtype]) h0`. Rewrite using `[← e, h, Submodule.comap_subtype_self]`.

Establish `hfin : ∀ k (φ : π.V), π.op (.fin k) (π.op (.fin k⁻¹) φ) = φ` using `fun k φ => Subtype.ext (by show (finRep E a k * finRep E a k⁻¹) φ.1 = φ.1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Use the proof step `rfl)`. Establish `hcpt : ∀ k (φ : π.V), π.op (.cpt k) (π.op (.cpt k⁻¹) φ) = φ` using `fun k φ => Subtype.ext (by show (cptRep E a k * cptRep E a k⁻¹) φ.1 = φ.1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`.

Use the proof step `rfl)`. Establish `key : ∀ o ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ∀ φ, B₁ φ (π.op (s₁ o) ψ) = B₂ φ (π.op (s₂ o) ψ')`. Introduce `o ψ ψ' h φ`. Consider the cases of `o with`. Consider the case `fin k`.

Establish `e1` using `hf₁ k (π.op (.fin k⁻¹) φ) ψ`. Establish `e2` using `hf₂ k (π.op (.fin k⁻¹) φ) ψ'`. Rewrite `e1`, `e2` using `[hfin]`. Rewrite using `[e1, e2, h]`. Consider the case `cpt k`.

Establish `e1` using `hc₁ k (π.op (.cpt k⁻¹) φ) ψ`. Establish `e2` using `hc₂ k (π.op (.cpt k⁻¹) φ) ψ'`. Rewrite `e1`, `e2` using `[hcpt]`. Rewrite using `[e1, e2, h]`. Consider the case `lie X`.

Establish `e1` using `hL₁ X φ ψ`. Establish `e2` using `hL₂ X φ ψ'`. Establish `e3` using `h (π.op (.lie X) φ)`. Take the linear combination `e1 - e2 - e3`. Establish `uniq : ∀ x y : π.V, (∀ φ, B₂ φ x = B₂ φ y) → x = y` using `fun x y h => sub_eq_zero.1 (hr₂ _ fun φ => by rw [map_sub, h, sub_self])`.

Establish `inj₂ : Function.Injective B₂.flip` using `fun x y h => uniq x y fun φ => by`. Simplify using `using LinearMap.congr_fun h φ`. Set `N : Submodule ℂ π.V` to `(LinearMap.range B₂.flip).comap B₁.flip`. Establish `memN : ∀ ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ψ ∈ N` using `fun ψ ψ' h => ⟨ψ', LinearMap.ext fun φ => by simpa using (h φ).symm⟩`. Establish `hN : N = ⊤`.

Use `irr N (fun o x hx => ?_) fun h => hψ₁ ((Submodule.eq_bot_iff _).1 h ψ₁ (memN _ _ hψ))` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx`. Establish `h : ∀ φ, B₁ φ x = B₂ φ y` using `fun φ => by simpa using (LinearMap.congr_fun hy φ).symm`. Use `key (s₁ o) x y h` as an intermediate fact. Rewrite `this` using `[hs₁ o]`.

Conclude with `memN _ _ this`. Establish `hmem : ∀ ψ, B₁.flip ψ ∈ LinearMap.range B₂.flip` using `fun ψ => (show ψ ∈ N from hN ▸ Submodule.mem_top)`. Set `T : π.V →ₗ[ℂ] π.V` to `(LinearEquiv.ofInjective B₂.flip inj₂).symm.toLinearMap ∘ₗ B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem`. Establish `hT : ∀ ψ φ, B₂ φ (T ψ) = B₁ φ ψ`. Introduce `ψ φ`.

Establish `h1` using `congrArg Subtype.val ((LinearEquiv.ofInjective B₂.flip inj₂).apply_symm_apply (B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem ψ))`. Rewrite `h1` using `[LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply]`. Establish `h2` using `LinearMap.congr_fun h1 φ`. Rewrite `h2` using `[LinearMap.flip_apply, LinearMap.flip_apply]`. Conclude with `h2`.

Establish `hTo : ∀ o φ, T (π.op (s₁ o) φ) = π.op (s₂ o) (T φ)` using `fun o φ => uniq _ _ fun χ => by rw [hT]; exact key o φ (T φ) (fun χ => (hT φ χ).symm) χ`. Establish `injT : Function.Injective T` using `fun x y h => sub_eq_zero.1 (hr₁ _ fun φ => by rw [map_sub, ← hT, ← hT, h, sub_self])`. Establish `hR : LinearMap.range T = ⊤`. Use `irr _ (fun o x hx => ?_) fun h => hψ₁ (injT ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hx`.

Use `⟨π.op (s₁ (s₂ o)) y, ?_⟩` and prove the remaining obligations. Rewrite using `[hTo, hs₂ o]`. Rewrite using `[map_zero]`. Conclude with `(Submodule.eq_bot_iff _).1 h _ ⟨ψ₁, rfl⟩`. Conclude with `⟨LinearEquiv.ofBijective T ⟨injT, LinearMap.range_eq_top.1 hR⟩, hTo⟩`.
-/
theorem iso_of_common_functional : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  intro E _ _ _ a π s₁ s₂ hs₁ hs₂ B₁ B₂ hl₁ hr₁ hf₁ hc₁ hL₁ hl₂ hr₂ hf₂ hc₂ hL₂ ψ₁ ψ₂ hψ₁ hψ

  have irr : ∀ P : Submodule ℂ π.V, (∀ o, ∀ x ∈ P, π.op o x ∈ P) → P ≠ ⊥ → P = ⊤ := by
    intro P hP h0
    have hst : IsStable (P.map π.V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨π.op o x, hP o x hx, rfl⟩
    have e := Submodule.comap_map_eq_of_injective π.V.injective_subtype P
    rcases π.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact absurd (by rw [← e, h, Submodule.comap_bot, Submodule.ker_subtype]) h0
    · rw [← e, h, Submodule.comap_subtype_self]
  have hfin : ∀ k (φ : π.V), π.op (.fin k) (π.op (.fin k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (finRep E a k * finRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)
  have hcpt : ∀ k (φ : π.V), π.op (.cpt k) (π.op (.cpt k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (cptRep E a k * cptRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)

  have key : ∀ o ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ∀ φ, B₁ φ (π.op (s₁ o) ψ) = B₂ φ (π.op (s₂ o) ψ') := by
    intro o ψ ψ' h φ
    cases o with
    | fin k =>
      have e1 := hf₁ k (π.op (.fin k⁻¹) φ) ψ
      have e2 := hf₂ k (π.op (.fin k⁻¹) φ) ψ'
      rw [hfin] at e1 e2
      rw [e1, e2, h]
    | cpt k =>
      have e1 := hc₁ k (π.op (.cpt k⁻¹) φ) ψ
      have e2 := hc₂ k (π.op (.cpt k⁻¹) φ) ψ'
      rw [hcpt] at e1 e2
      rw [e1, e2, h]
    | lie X =>
      have e1 := hL₁ X φ ψ
      have e2 := hL₂ X φ ψ'
      have e3 := h (π.op (.lie X) φ)
      linear_combination e1 - e2 - e3
  have uniq : ∀ x y : π.V, (∀ φ, B₂ φ x = B₂ φ y) → x = y := fun x y h =>
    sub_eq_zero.1 (hr₂ _ fun φ => by rw [map_sub, h, sub_self])
  have inj₂ : Function.Injective B₂.flip := fun x y h => uniq x y fun φ => by
    simpa using LinearMap.congr_fun h φ

  let N : Submodule ℂ π.V := (LinearMap.range B₂.flip).comap B₁.flip
  have memN : ∀ ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ψ ∈ N := fun ψ ψ' h =>
    ⟨ψ', LinearMap.ext fun φ => by simpa using (h φ).symm⟩
  have hN : N = ⊤ := by
    refine irr N (fun o x hx => ?_) fun h => hψ₁ ((Submodule.eq_bot_iff _).1 h ψ₁ (memN _ _ hψ))
    obtain ⟨y, hy⟩ := hx
    have h : ∀ φ, B₁ φ x = B₂ φ y := fun φ => by simpa using (LinearMap.congr_fun hy φ).symm
    have := key (s₁ o) x y h
    rw [hs₁ o] at this
    exact memN _ _ this
  have hmem : ∀ ψ, B₁.flip ψ ∈ LinearMap.range B₂.flip := fun ψ =>
    (show ψ ∈ N from hN ▸ Submodule.mem_top)
  let T : π.V →ₗ[ℂ] π.V := (LinearEquiv.ofInjective B₂.flip inj₂).symm.toLinearMap ∘ₗ
    B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem
  have hT : ∀ ψ φ, B₂ φ (T ψ) = B₁ φ ψ := by
    intro ψ φ
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective B₂.flip inj₂).apply_symm_apply
      (B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem ψ))
    rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h1
    have h2 := LinearMap.congr_fun h1 φ
    rw [LinearMap.flip_apply, LinearMap.flip_apply] at h2
    exact h2
  have hTo : ∀ o φ, T (π.op (s₁ o) φ) = π.op (s₂ o) (T φ) := fun o φ =>
    uniq _ _ fun χ => by rw [hT]; exact key o φ (T φ) (fun χ => (hT φ χ).symm) χ
  have injT : Function.Injective T := fun x y h =>
    sub_eq_zero.1 (hr₁ _ fun φ => by rw [map_sub, ← hT, ← hT, h, sub_self])
  have hR : LinearMap.range T = ⊤ := by
    refine irr _ (fun o x hx => ?_) fun h => hψ₁ (injT ?_)
    · obtain ⟨y, rfl⟩ := hx
      refine ⟨π.op (s₁ (s₂ o)) y, ?_⟩
      rw [hTo, hs₂ o]
    · rw [map_zero]
      exact (Submodule.eq_bot_iff _).1 h _ ⟨ψ₁, rfl⟩
  exact ⟨LinearEquiv.ofBijective T ⟨injT, LinearMap.range_eq_top.1 hR⟩, hTo⟩

end GlobalTheory.ContraPair
