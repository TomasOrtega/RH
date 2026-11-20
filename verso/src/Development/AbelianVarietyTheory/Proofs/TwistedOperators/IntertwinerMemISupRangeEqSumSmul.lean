import Mathlib

namespace GlobalTheory

open Representation

/- English proof (translation)
Set `Φ : (Fin m → N) →ₗ[ℂ] X` to `∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j`. Establish `hΦ : ∀ w, Φ w = ∑ j, φ j (w j)`. Introduce `w`. Simplify using `[Φ, LinearMap.sum_apply]`. Establish `hΦinj : Function.Injective Φ`.

Introduce `a b h`. Apply `hinj` to reduce the goal to its premises. Simplify `h` using `[hΦ]`. Establish `hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ`. Use `iSup_le fun j => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Use `⟨Pi.single j n, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules. Establish `hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ` using `fun n => hle (hψ ⟨n, rfl⟩)`. Set `e` to `LinearEquiv.ofInjective Φ hΦinj`.

Set `Wm : N →ₗ[ℂ] (Fin m → N)` to `e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem`. Establish `hW : ∀ n, Φ (Wm n) = ψ n`. Introduce `n`. Simplify using `only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Establish `h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩` using `e.apply_symm_apply _`.

Establish `h3` using `congrArg Subtype.val h2`. Express the relevant statement in the definitionally equal form `Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n`. Rewrite using `[← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]`. Conclude with `h3`. Establish `hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j)`.

Introduce `g n`. Apply `hΦinj` to reduce the goal to its premises. Rewrite using `[hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[(φ j).isIntertwining]`.

Establish `hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n`. Introduce `j`. Set `θ : π.IntertwiningMap π` to `(LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by`. Introduce `g v`. Simplify using `[hWg])`.

Take `⟨c, hc⟩` from `hS θ`. Use `⟨c, fun n => ?_⟩` and prove the remaining obligations. Establish `h1 : Wm n j = θ.toLinearMap n` using `rfl`. Rewrite using `[h1, hc]`. Simplify using the standard rewrite rules.

Use `choose c hc using hc`. Use `⟨c, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← hW, hΦ]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hc, map_smul]`.
-/
theorem intertwiner_mem_iSup_range_eq_sum_smul (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hS : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id)
    (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ)
    (hinj : Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)))
    (ψ : π.IntertwiningMap ρ)
    (hψ : LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap) :
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  classical
  let Φ : (Fin m → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
  have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by
    intro w; simp [Φ, LinearMap.sum_apply]
  have hΦinj : Function.Injective Φ := by
    intro a b h; apply hinj; simpa [hΦ] using h
  have hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Pi.single j n, ?_⟩
    rw [hΦ]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ := fun n =>
    hle (hψ ⟨n, rfl⟩)
  let e := LinearEquiv.ofInjective Φ hΦinj
  let Wm : N →ₗ[ℂ] (Fin m → N) := e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem
  have hW : ∀ n, Φ (Wm n) = ψ n := by
    intro n
    simp only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩ := e.apply_symm_apply _
    have h3 := congrArg Subtype.val h2
    change Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n
    rw [← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]
    exact h3
  have hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j) := by
    intro g n
    apply hΦinj
    rw [hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(φ j).isIntertwining]
  have hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n := by
    intro j
    let θ : π.IntertwiningMap π :=
      (LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by
        intro g v
        simp [hWg])
    obtain ⟨c, hc⟩ := hS θ
    refine ⟨c, fun n => ?_⟩
    have h1 : Wm n j = θ.toLinearMap n := rfl
    rw [h1, hc]
    simp
  choose c hc using hc
  refine ⟨c, fun n => ?_⟩
  rw [← hW, hΦ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, map_smul]

end GlobalTheory
