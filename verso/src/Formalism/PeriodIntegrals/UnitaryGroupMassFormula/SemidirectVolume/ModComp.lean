import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable {D : Dat A n r}

/- English proof (translation)
Rewrite using `[L_apply, h_sub_right, h_add_right, h_sum_right, h_sum_right]`. Simplify using `only [h_smul_right, h_add_right, h_sum_right, H.ee, (hw' _).1, mul_zero, add_zero, Finset.sum_const_zero, sub_zero]`.
-/
theorem h_e_L (H : D.Hyp) {w' : Fin r → n → A} (s' : Fin r → Fin r → A)
    (hw' : ∀ a, IsW D (w' a)) (v : n → A) (c : Fin r) :
    D.h (D.e c) (D.L w' s' v) = D.h (D.e c) v := by
  rw [L_apply, h_sub_right, h_add_right, h_sum_right, h_sum_right]
  simp only [h_smul_right, h_add_right, h_sum_right, H.ee, (hw' _).1, mul_zero, add_zero,
    Finset.sum_const_zero, sub_zero]

/- English proof (translation)
Rewrite using `[L_apply, map_sub, map_add, map_sum, map_sum]`. Simplify using `only [map_smul, map_add, map_sum, pW_e H, pW_of_isW (hw' _), smul_zero, Finset.sum_const_zero, add_zero, sub_zero]`.
-/
theorem pW_L (H : D.Hyp) {w' : Fin r → n → A} (s' : Fin r → Fin r → A)
    (hw' : ∀ a, IsW D (w' a)) (v : n → A) :
    D.pW (D.L w' s' v) = D.pW v + ∑ d, D.h (D.e d) v • w' d := by
  rw [L_apply, map_sub, map_add, map_sum, map_sum]
  simp only [map_smul, map_add, map_sum, pW_e H, pW_of_isW (hw' _), smul_zero,
    Finset.sum_const_zero, add_zero, sub_zero]

/- English proof (translation)
Establish `_hw` using `hw`. Establish `h1 : ∀ c, D.h (D.e c) (D.L w' s' v) = D.h (D.e c) v` using `h_e_L H s' hw' v`. Establish `h3 : ∀ a, D.h (w a) (D.pW (D.L w' s' v)) = D.h (w a) (D.pW v) + ∑ d, D.h (D.e d) v * D.h (w a) (w' d)` using `fun a => by`. Rewrite using `[pW_L H s' hw', h_add_right, h_sum_right]`. Simplify using `only [h_smul_right]`.

Establish `hZ : ∑ b, D.h (D.e b) v • ∑ a, D.h (w a) (w' b) • D.e a = ∑ a, (∑ d, D.h (D.e d) v * D.h (w a) (w' d)) • D.e a`. Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Establish `hB : ∀ b, D.h (D.e b) v • ((w + w') b + ∑ a, (s a b + s' a b - D.h (w a) (w' b)) • D.e a) = D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) + D.h (D.e b) v • (w' b + ∑ a, s' a b • D.e a) - D.h (D.e b) v • ∑ a, D.h (w a) (w' b) • D.e a` using `fun b => by`. Simplify using `only [Pi.add_apply, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_add, smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `hA : ∀ a, D.h ((w + w') a) (D.pW v) • D.e a = D.h (w a) (D.pW v) • D.e a + D.h (w' a) (D.pW v) • D.e a` using `fun a => by`. Rewrite using `[Pi.add_apply, h_add_left, add_smul]`. Rewrite using `[L_apply D w s, L_apply D (w + w')]`. Simplify using `only [h1, h3, add_smul, Finset.sum_add_distrib]`.

Rewrite using `[L_apply D w' s']`. Simplify using `only [hB, hA, Finset.sum_add_distrib, Finset.sum_sub_distrib, hZ]`. Normalize the expressions using the abelian group laws.
-/
theorem L_comp (H : D.Hyp) {w w' : Fin r → n → A} (s s' : Fin r → Fin r → A)
    (hw : ∀ a, IsW D (w a)) (hw' : ∀ a, IsW D (w' a)) (v : n → A) :
    D.L w s (D.L w' s' v) =
      D.L (w + w') (fun a b => s a b + s' a b - D.h (w a) (w' b)) v := by
  have _hw := hw
  have h1 : ∀ c, D.h (D.e c) (D.L w' s' v) = D.h (D.e c) v := h_e_L H s' hw' v
  have h3 : ∀ a, D.h (w a) (D.pW (D.L w' s' v)) =
      D.h (w a) (D.pW v) + ∑ d, D.h (D.e d) v * D.h (w a) (w' d) := fun a => by
    rw [pW_L H s' hw', h_add_right, h_sum_right]
    simp only [h_smul_right]
  have hZ : ∑ b, D.h (D.e b) v • ∑ a, D.h (w a) (w' b) • D.e a =
      ∑ a, (∑ d, D.h (D.e d) v * D.h (w a) (w' d)) • D.e a := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hB : ∀ b, D.h (D.e b) v • ((w + w') b +
        ∑ a, (s a b + s' a b - D.h (w a) (w' b)) • D.e a) =
      D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) + D.h (D.e b) v • (w' b + ∑ a, s' a b • D.e a) -
        D.h (D.e b) v • ∑ a, D.h (w a) (w' b) • D.e a := fun b => by
    simp only [Pi.add_apply, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      smul_add, smul_sub]
    abel
  have hA : ∀ a, D.h ((w + w') a) (D.pW v) • D.e a =
      D.h (w a) (D.pW v) • D.e a + D.h (w' a) (D.pW v) • D.e a := fun a => by
    rw [Pi.add_apply, h_add_left, add_smul]
  rw [L_apply D w s, L_apply D (w + w')]
  simp only [h1, h3, add_smul, Finset.sum_add_distrib]
  rw [L_apply D w' s']
  simp only [hB, hA, Finset.sum_add_distrib, Finset.sum_sub_distrib, hZ]
  abel

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[L_apply]`. Simplify using `[h_zero_left]`.
-/
theorem L_zero : D.L 0 0 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [L_apply]
  simp [h_zero_left]

end Dat

end PI.VolSemiDirect.W.PG
