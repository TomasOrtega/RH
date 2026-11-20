import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

/- English proof (translation)
Introduce `F _ N N' r W φ e wv hT y'`. Take `⟨-, -, he_add, -, hc, hw0, -, hψ⟩` from `hT`. Use `⟨fun j => hc y' j, fun χ' => ?_⟩` and prove the remaining obligations. Simplify using `only [NumD.io_s, NumD.io_b]`. Set `U : N'.A → Fˣ` to `fun x => Units.mk0 (wv x) (hw0 x)`.

Establish `hU : ∀ x, wv x = (U x : F)` using `fun x => rfl`. Set `P : N'.X → Fˣ` to `fun a => ∏ i, ∏ j, N.τ (e a i) (e a j) ^ W i j`. Establish `hψ' : ∀ a, N'.ψ a * U 1 = U (N'.c a) * P a` using `fun a => Units.ext (by`. Simplify using `only [Units.val_mul, U, Units.val_mk0, P]`. Conclude with `hψ a)`.

Establish `key : ∀ i j, N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) / (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) * N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j))) = N.τ (e (y' + χ') i) (e (y' + χ') j) / N.τ (e y' i …`. Introduce `i j`. Rewrite using `[he_add y' χ' i, he_add y' χ' j, add_comm (e y' i), add_comm (e y' j)]`. Establish `h1` using `N.τ_add_left (e χ' i) (e y' i) (e χ' j + e y' j)`. Rewrite `h1` using `[N.c_add]`.

Establish `h2` using `N.τ_add_right (e χ' i) (e χ' j) (e y' j)`. Establish `h3` using `N.τ_add_right (e y' i) (e χ' j) (e y' j)`. Establish `h4` using `N.τ_symm (e y' j) (e χ' i)`. Use `replace h1 := congrArg Additive.ofMul h1`. Use `replace h2 := congrArg Additive.ofMul h2`.

Use `replace h3 := congrArg Additive.ofMul h3`. Use `replace h4 := congrArg Additive.ofMul h4`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div] at h1 h2 h3 h4 ⊢`. Take the linear combination `(norm := abel) h4 - h1 - h2 - h3`.

Establish `hQ : (∏ i, ∏ j, (N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) / (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) * N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j)))) ^ W i j : Fˣ) = P (y' + χ') / P y' / P χ'`. Simplify using `only [key, div_zpow, Finset.prod_div_distrib, P]`. Rewrite using `[hQ, hU, hU, hU, hU]`. Establish `hS` using `hψ' (y' + χ')`. Rewrite `hS` using `[N'.c_add y' χ', mul_comm (N'.c y')]`.

Establish `hy` using `hψ' y'`. Establish `hx` using `hψ' χ'`. Establish `E : N'.τ y' χ' * U (N'.c χ') * U (N'.c y') = P (y' + χ') / P y' / P χ' * U (N'.c χ' * N'.c y') * U 1`. Simplify using `only [NumD.τ]`. Use `replace hS := congrArg Additive.ofMul hS`.

Use `replace hy := congrArg Additive.ofMul hy`. Use `replace hx := congrArg Additive.ofMul hx`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div] at hS hy hx ⊢`. Take the linear combination `(norm := abel) hS - hy - hx`.

Use `congrArg Units.val E` as an intermediate fact. Simplify `this` using `only [Units.val_mul]`.
-/
theorem gtRelV_io : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ y' : N'.X, GtRelV W φ e wv (N'.io y') (fun j => N.io (e y' j)) := by
  intro F _ N N' r W φ e wv hT y'
  obtain ⟨-, -, he_add, -, hc, hw0, -, hψ⟩ := hT
  refine ⟨fun j => hc y' j, fun χ' => ?_⟩
  simp only [NumD.io_s, NumD.io_b]
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  let P : N'.X → Fˣ := fun a => ∏ i, ∏ j, N.τ (e a i) (e a j) ^ W i j
  have hψ' : ∀ a, N'.ψ a * U 1 = U (N'.c a) * P a := fun a => Units.ext (by
    simp only [Units.val_mul, U, Units.val_mk0, P]; exact hψ a)
  have key : ∀ i j, N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j))) =
      N.τ (e (y' + χ') i) (e (y' + χ') j) / N.τ (e y' i) (e y' j) / N.τ (e χ' i) (e χ' j) := by
    intro i j
    rw [he_add y' χ' i, he_add y' χ' j, add_comm (e y' i), add_comm (e y' j)]
    have h1 := N.τ_add_left (e χ' i) (e y' i) (e χ' j + e y' j)
    rw [N.c_add] at h1
    have h2 := N.τ_add_right (e χ' i) (e χ' j) (e y' j)
    have h3 := N.τ_add_right (e y' i) (e χ' j) (e y' j)
    have h4 := N.τ_symm (e y' j) (e χ' i)
    replace h1 := congrArg Additive.ofMul h1
    replace h2 := congrArg Additive.ofMul h2
    replace h3 := congrArg Additive.ofMul h3
    replace h4 := congrArg Additive.ofMul h4
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h1 h2 h3 h4 ⊢
    linear_combination (norm := abel) h4 - h1 - h2 - h3
  have hQ : (∏ i, ∏ j, (N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j)))) ^ W i j : Fˣ) =
      P (y' + χ') / P y' / P χ' := by
    simp only [key, div_zpow, Finset.prod_div_distrib, P]
  rw [hQ, hU, hU, hU, hU]
  have hS := hψ' (y' + χ')
  rw [N'.c_add y' χ', mul_comm (N'.c y')] at hS
  have hy := hψ' y'
  have hx := hψ' χ'
  have E : N'.τ y' χ' * U (N'.c χ') * U (N'.c y') = P (y' + χ') / P y' / P χ' * U (N'.c χ' * N'.c y') * U 1 := by
    simp only [NumD.τ]
    replace hS := congrArg Additive.ofMul hS
    replace hy := congrArg Additive.ofMul hy
    replace hx := congrArg Additive.ofMul hx
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at hS hy hx ⊢
    linear_combination (norm := abel) hS - hy - hx
  have := congrArg Units.val E
  simpa only [Units.val_mul] using this

end GlobalTheory.Mum.TensTor
