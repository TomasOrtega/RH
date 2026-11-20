import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdealPowers
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdealSheaf
universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
The claim follows from `| [], w, h => absurd h (by simp) | (a :: l), w, h => by show w ∣ Nat.lcm a (l.foldr Nat.lcm 1) rcases List.mem_cons.mp h with h | h · subst h exact Nat.dvd_lcm_left _ _ · exact dvd_trans (dvd_foldr_lcm l w h) (Nat.dvd_lcm_right _ _)`.
-/
private theorem dvd_foldr_lcm : ∀ (l : List ℕ) (w : ℕ), w ∈ l → w ∣ l.foldr Nat.lcm 1
  | [], w, h => absurd h (by simp)
  | (a :: l), w, h => by
      show w ∣ Nat.lcm a (l.foldr Nat.lcm 1)
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact Nat.dvd_lcm_left _ _
      · exact dvd_trans (dvd_foldr_lcm l w h) (Nat.dvd_lcm_right _ _)

/- English proof (translation)
The claim follows from `dvd_foldr_lcm _ w (List.mem_range'_1.mpr ⟨hw, by omega⟩)`.
-/
theorem dvd_lcmUpTo (m w : ℕ) (hw : 1 ≤ w) (hwm : w ≤ m) : w ∣ lcmUpTo m :=
  dvd_foldr_lcm _ w (List.mem_range'_1.mpr ⟨hw, by omega⟩)

/- English proof (translation)
The claim follows from `| 0, s, _ => Nat.one_pos | (n + 1), s, hs => by have h := foldr_lcm_consecutive_pos n (s + 1) (by omega) show 0 < Nat.lcm s ((List.range' (s + 1) n).foldr Nat.lcm 1) exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))`.
-/
private theorem foldr_lcm_consecutive_pos :
    ∀ (n s : ℕ), 0 < s → 0 < (List.range' s n).foldr Nat.lcm 1
  | 0, s, _ => Nat.one_pos
  | (n + 1), s, hs => by
      have h := foldr_lcm_consecutive_pos n (s + 1) (by omega)
      show 0 < Nat.lcm s ((List.range' (s + 1) n).foldr Nat.lcm 1)
      exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))

/- English proof (translation)
The claim follows from `foldr_lcm_consecutive_pos m 1 Nat.one_pos`.
-/
theorem lcmUpTo_pos (m : ℕ) : 0 < lcmUpTo m :=
  foldr_lcm_consecutive_pos m 1 Nat.one_pos

/- English proof (translation)
Break down `eq_or_ne a ⊤ with rfl | hne` into its components or cases. Conclude with `absurd le_top h`. Take `⟨n, rfl⟩` from `ENat.ne_top_iff_exists.mp hne`. Establish `hn : ¬ (s + 1 ≤ n)` using `fun hh => h (by exact_mod_cast hh)`. Establish `hns : n ≤ s` using `by omega`.

Conclude with `hns` after adjusting the coercions.
-/
private theorem le_of_not_natCast_succ_le {a : ℕ∞} {s : ℕ}
    (h : ¬ (((s + 1 : ℕ)) : ℕ∞) ≤ a) : a ≤ (s : ℕ∞) := by
  rcases eq_or_ne a ⊤ with rfl | hne
  · exact absurd le_top h
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hne
    have hn : ¬ (s + 1 ≤ n) := fun hh => h (by exact_mod_cast hh)
    have hns : n ≤ s := by omega
    exact_mod_cast hns

/- English proof (translation)
Introduce `k hk hchar hnoeth X p hsmooth hft I m hm hmax r t ht`. Use `Scheme.IdealSheafData.ext (funext ?_)` and prove the remaining obligations. Introduce `U`. Rewrite using `[Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, tunedSheaf_ideal, tunedSheaf_ideal, tunedSheaf_ideal]`. Conclude with `@tunedIdeal_mul_eq_tunedIdeal_add k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m) (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r t ht`.
-/
theorem tunedSheaf_mul_eq_add : TunedSheafMulEqAdd.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r t ht
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, tunedSheaf_ideal, tunedSheaf_ideal,
    tunedSheaf_ideal]
  exact @tunedIdeal_mul_eq_tunedIdeal_add k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m)
    (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r t ht

/- English proof (translation)
Introduce `k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr j hj`. Use `Scheme.IdealSheafData.ext (funext ?_)` and prove the remaining obligations. Introduce `U`. Rewrite using `[Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, tunedSheaf_ideal, tunedSheaf_ideal]`. Conclude with `@tunedIdeal_pow_eq_tunedIdeal_mul k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m) (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr j hj`.
-/
theorem tunedSheaf_pow_eq_mul : TunedSheafPowEqMul.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr j hj
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, tunedSheaf_ideal, tunedSheaf_ideal]
  exact @tunedIdeal_pow_eq_tunedIdeal_mul k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m)
    (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr j hj

/- English proof (translation)
Introduce `k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr i hi`. Use `Scheme.IdealSheafData.le_def.mpr ?_` and prove the remaining obligations. Introduce `U`. Rewrite using `[Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Pi.pow_apply, derivIdealSheafIterate_ideal, tunedSheaf_ideal]`. Conclude with `@derivIdealIterate_tunedIdeal_pow_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m) (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr i hi`.
-/
theorem isDerivBalanced_tunedSheaf_mul_lcmUpTo : IsDerivBalancedTunedSheafMulLcm.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr i hi
  refine Scheme.IdealSheafData.le_def.mpr ?_
  intro U
  rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Pi.pow_apply, derivIdealSheafIterate_ideal, tunedSheaf_ideal]
  exact @derivIdealIterate_tunedIdeal_pow_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m
    (lcmUpTo m) (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr i hi

/- English proof (translation)
Introduce `k hk hchar hnoeth X p hsmooth hft I m hm hmax s hs`. Establish `hC` using `maxContactIdealTunedSheafEq k X p I m hm hmax s hs`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hA` using `support_derivIdealSheafIterate_eq_orderAtLeastLocus k p (tunedSheaf k p I m s) hs`. Establish `hB` using `support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm`.

Rewrite using `[← hA, hC]`. Conclude with `hB`. Introduce `x`. Establish `hordI : orderAt I x ≤ (m : ℕ∞)` using `hmax.orderLE x`. Establish `hx2 : x ∉ orderAtLeastLocus I (m + 1)`.

Rewrite using `[mem_orderAtLeastLocus_iff]`. Introduce `hcon`. Establish `hle` using `le_trans hcon hordI`. Establish `hmm : m + 1 ≤ m` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers.

Establish `hcs : orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) I) ((m + 1) - (m - 1)) = orderAtLeastLocus I (m + 1)` using `orderAtLeastLocus_derivIdealSheafIterate k p I (by omega)`. Establish `ha : ¬ (((2 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k p (m - 1) I) x)`. Rewrite using `[← mem_orderAtLeastLocus_iff]`. Establish `h2 : (2 : ℕ) = (m + 1) - (m - 1)` using `by omega`. Rewrite using `[h2, hcs]`.

Conclude with `hx2`. Use `le_of_not_natCast_succ_le ?_` and prove the remaining obligations. Introduce `hcon`. Establish `he : 2 + (s - 1) = s + 1` using `by omega`. Establish `h1 : (((2 + (s - 1) : ℕ)) : ℕ∞) ≤ orderAt (tunedSheaf k p I m s) x`.

Rewrite using `[he]`. Conclude with `hcon`. Establish `h2` using `le_orderAt_derivIdealSheafIterate k p (tunedSheaf k p I m s) x 2 (s - 1) h1`. Rewrite `h2` using `[hC]`. Conclude with `ha h2`.
-/
theorem orderAtLeastLocus_tunedSheaf_eq_and_order_le : CoSupportTunedSheafEqAndOrderLE.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax s hs
  have hC := maxContactIdealTunedSheafEq k X p I m hm hmax s hs
  refine ⟨?_, ?_⟩
  · have hA := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p (tunedSheaf k p I m s) hs
    have hB := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
    rw [← hA, hC]
    exact hB
  · intro x
    have hordI : orderAt I x ≤ (m : ℕ∞) := hmax.orderLE x
    have hx2 : x ∉ orderAtLeastLocus I (m + 1) := by
      rw [mem_orderAtLeastLocus_iff]
      intro hcon
      have hle := le_trans hcon hordI
      have hmm : m + 1 ≤ m := by exact_mod_cast hle
      omega
    have hcs : orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) I) ((m + 1) - (m - 1))
        = orderAtLeastLocus I (m + 1) := orderAtLeastLocus_derivIdealSheafIterate k p I (by omega)
    have ha : ¬ (((2 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k p (m - 1) I) x) := by
      rw [← mem_orderAtLeastLocus_iff]
      have h2 : (2 : ℕ) = (m + 1) - (m - 1) := by omega
      rw [h2, hcs]
      exact hx2
    refine le_of_not_natCast_succ_le ?_
    intro hcon
    have he : 2 + (s - 1) = s + 1 := by omega
    have h1 : (((2 + (s - 1) : ℕ)) : ℕ∞) ≤ orderAt (tunedSheaf k p I m s) x := by
      rw [he]
      exact hcon
    have h2 := le_orderAt_derivIdealSheafIterate k p (tunedSheaf k p I m s) x 2 (s - 1) h1
    rw [hC] at h2
    exact ha h2

end FunctorialResolution.EmbeddedResolution
