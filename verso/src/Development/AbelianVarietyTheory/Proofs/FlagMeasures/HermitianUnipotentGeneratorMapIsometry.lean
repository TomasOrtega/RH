import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.RowStab

/- English proof (translation)
Establish `heρ : ∀ a b, H.B (e a) (ρ b) = 0` using `fun a b => by rw [← H.herm, hρe, star_zero]`. Establish `hX : ∀ w y, H.B (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) y = ∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y)`. Introduce `w y`. Simplify using `[map_sum, LinearMap.sum_apply, mul_assoc]`. Establish `hXr : ∀ w y, H.B y (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) = star (∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y))`.

Introduce `w y`. Rewrite using `[← H.herm, hX]`. Establish `hρv : ∀ b, H.B (ρ b) v = star (H.B v (ρ b))` using `fun b => (H.herm _ _).symm`. Establish `hev : ∀ b, H.B (e b) v = star (H.B v (e b))` using `fun b => (H.herm _ _).symm`. Establish `hρu : ∀ b, H.B (ρ b) u = star (H.B u (ρ b))` using `fun b => (H.herm _ _).symm`.

Establish `heu : ∀ b, H.B (e b) u = star (H.B u (e b))` using `fun b => (H.herm _ _).symm`. Rewrite using `[GlobalTheory.RowStab.gen_apply, GlobalTheory.RowStab.gen_apply]`. Simplify using `only [map_add, LinearMap.add_apply, hX, hXr, hee, heρ, hρe, mul_zero, sub_zero, add_zero, Finset.sum_const_zero, star_zero, hρv, hev, hρu, heu, star_sum, star_add, star_sub, star_mul', star_star]`. Establish `hρρ : ∀ a b, star (H.B (ρ a) (ρ b)) = H.B (ρ b) (ρ a)` using `fun a b => H.herm _ _`. Simplify using `only [hρρ]`.

Establish `h2 : ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) = ∑ x ∈ J, ∑ x1 ∈ J, star (c x x1) * star (H.B v (e x1)) * H.B u (e x)` using `Finset.sum_comm`. Establish `hS : ∑ x ∈ J, ∑ x1 ∈ J, c x1 x * H.B u (e x) * star (H.B v (e x1)) + ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) + ∑ x ∈ J, H.B u (e x) * ∑ x1 ∈ J, star (H.B v (e x1)) * H.B (ρ x) (ρ x1) = 0`. Rewrite using `[h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x _`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x1 _`. Take the linear combination `(H.B u (e x) * star (H.B v (e x1))) * hc x x1`. Establish `hA : ∑ x ∈ J, star (H.B v (ρ x)) * H.B u (e x) = ∑ x ∈ J, H.B u (e x) * star (H.B v (ρ x))` using `Finset.sum_congr rfl (fun _ _ => mul_comm _ _)`.

Establish `hB : ∑ x ∈ J, star (H.B v (e x)) * H.B u (ρ x) = ∑ x ∈ J, H.B u (ρ x) * star (H.B v (e x))` using `Finset.sum_congr rfl (fun _ _ => mul_comm _ _)`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Take the linear combination `hS - hA + hB`.
-/
theorem gen_isometry {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (hee : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0) (hc : ∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) (u v : V) : H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  have hX : ∀ w y, H.B (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) y = ∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y) := by
    intro w y
    simp [map_sum, LinearMap.sum_apply, mul_assoc]
  have hXr : ∀ w y, H.B y (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) = star (∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y)) := by
    intro w y; rw [← H.herm, hX]
  have hρv : ∀ b, H.B (ρ b) v = star (H.B v (ρ b)) := fun b => (H.herm _ _).symm
  have hev : ∀ b, H.B (e b) v = star (H.B v (e b)) := fun b => (H.herm _ _).symm
  have hρu : ∀ b, H.B (ρ b) u = star (H.B u (ρ b)) := fun b => (H.herm _ _).symm
  have heu : ∀ b, H.B (e b) u = star (H.B u (e b)) := fun b => (H.herm _ _).symm
  rw [GlobalTheory.RowStab.gen_apply, GlobalTheory.RowStab.gen_apply]
  simp only [map_add, LinearMap.add_apply, hX, hXr, hee, heρ, hρe, mul_zero, sub_zero, add_zero, Finset.sum_const_zero, star_zero, hρv, hev, hρu, heu, star_sum, star_add, star_sub, star_mul', star_star]
  have hρρ : ∀ a b, star (H.B (ρ a) (ρ b)) = H.B (ρ b) (ρ a) := fun a b => H.herm _ _
  simp only [hρρ]
  have h2 : ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) = ∑ x ∈ J, ∑ x1 ∈ J, star (c x x1) * star (H.B v (e x1)) * H.B u (e x) := Finset.sum_comm
  have hS : ∑ x ∈ J, ∑ x1 ∈ J, c x1 x * H.B u (e x) * star (H.B v (e x1)) + ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) + ∑ x ∈ J, H.B u (e x) * ∑ x1 ∈ J, star (H.B v (e x1)) * H.B (ρ x) (ρ x1) = 0 := by
    rw [h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x1 _
    linear_combination (H.B u (e x) * star (H.B v (e x1))) * hc x x1
  have hA : ∑ x ∈ J, star (H.B v (ρ x)) * H.B u (e x) = ∑ x ∈ J, H.B u (e x) * star (H.B v (ρ x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hB : ∑ x ∈ J, star (H.B v (e x)) * H.B u (ρ x) = ∑ x ∈ J, H.B u (ρ x) * star (H.B v (e x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination hS - hA + hB

end GlobalTheory.RowStab
