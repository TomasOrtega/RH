import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [dif, hι]`.
-/
theorem dif_comp_add (L : ℕ) (ι : ℤ × ℤ → ℤ × ℤ) (hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v)
    (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (ι y)) = fun x => dif L (ι v) F (ι x) := by
  funext x
  simp only [dif, hι]

/- English proof (translation)
Introduce `j L N v Φ τ τ' hN hτ`. Use `set ι : ℤ × ℤ → ℤ × ℤ := fun x => ((N : ℤ) * x.1, x.2) with hιdef`. Establish `hN' : (N : ℤ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hinj : Function.Injective ι`. Introduce `a b h`.

Simplify using `only [hιdef, Prod.mk.injEq] at h`. Conclude with `Prod.ext (mul_left_cancel₀ hN' h.1) h.2`. Establish `hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v`. Introduce `x v r`. Simplify using `only [hιdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk_add_mk, Prod.smul_mk]`.

Apply the tactic sequence `ext <;> simp only <;> ring`. Use `set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT`. Establish `hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) = fun y => T (ι y)`. Use function extensionality and compare the values at `y`. Simplify using `only [hT, hιdef, hτ]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hvι : ι v = ((N : ℤ) * v.1, v.2)` using `rfl`. Establish `hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) x = dif L (ι v) (dif L (ι v) T) (ι x)`.

Introduce `x`. Rewrite using `[hG, dif_comp_add L ι hι, dif_comp_add L ι hι]`. Use `set Ψ : ℤ × ℤ → ℂ := fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0 with hΨ`. Establish `hΨι : ∀ x, Ψ (ι x) = Φ x`. Introduce `x`.

Simplify using `only [hΨ, hιdef, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ hN']`. Unfold `lat`. Rewrite using `[← hvι]`. Repeatedly rewrite using `[hdd]`. Use `set D := dif L (ι v) (dif L (ι v) T) with hD`.

Establish `key : (fun x => Φ x * D (ι x)) = fun x => (fun y => Ψ y * D y) (ι x)`. Use function extensionality and compare the values at `x`. Simplify using `only [hΨι]`. Rewrite using `[key]`. Use `hinj.tsum_eq (f := fun y => Ψ y * D y) ?_` and prove the remaining obligations.

Introduce `y hy`. Simplify using `only [Function.mem_support] at hy`. Distinguish the cases in `h : (N : ℤ) ∣ y.1`. Take `⟨c, hc⟩` from `h`. Conclude with `⟨(c, y.2), by simp only [hιdef]; exact Prod.ext hc.symm rfl⟩`.

Conclude with `absurd (by simp only [hΨ, h, if_false, zero_mul]) hy`.
-/
theorem lat_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  intro j L N v Φ τ τ' hN hτ
  set ι : ℤ × ℤ → ℤ × ℤ := fun x => ((N : ℤ) * x.1, x.2) with hιdef
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective ι := by
    intro a b h
    simp only [hιdef, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.1) h.2
  have hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v := by
    intro x v r
    simp only [hιdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk_add_mk,
      Prod.smul_mk]
    ext <;> simp only <;> ring
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) = fun y => T (ι y) := by
    funext y
    simp only [hT, hιdef, hτ]
    congr 1
    push_cast
    ring
  have hvι : ι v = ((N : ℤ) * v.1, v.2) := rfl
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) x =
      dif L (ι v) (dif L (ι v) T) (ι x) := by
    intro x
    rw [hG, dif_comp_add L ι hι, dif_comp_add L ι hι]
  set Ψ : ℤ × ℤ → ℂ := fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0 with hΨ
  have hΨι : ∀ x, Ψ (ι x) = Φ x := by
    intro x
    simp only [hΨ, hιdef, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ hN']
  unfold lat
  rw [← hvι]
  simp_rw [hdd]
  set D := dif L (ι v) (dif L (ι v) T) with hD
  have key : (fun x => Φ x * D (ι x)) = fun x => (fun y => Ψ y * D y) (ι x) := by
    funext x; simp only [hΨι]
  rw [key]
  refine hinj.tsum_eq (f := fun y => Ψ y * D y) ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_cases h : (N : ℤ) ∣ y.1
  · obtain ⟨c, hc⟩ := h
    exact ⟨(c, y.2), by simp only [hιdef]; exact Prod.ext hc.symm rfl⟩
  · exact absurd (by simp only [hΨ, h, if_false, zero_mul]) hy

end GlobalTheory.EisM
