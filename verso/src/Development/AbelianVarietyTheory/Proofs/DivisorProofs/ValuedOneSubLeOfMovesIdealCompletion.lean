import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

/- English proof (translation)
Use `⟨⟨Pi.single w x, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hu` to reduce the goal to its premises. Rewrite using `[Pi.single_eq_of_ne hne]`.

Conclude with `zero_mem _`. Conclude with `Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w x`. Introduce `u hu`. Conclude with `Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) hu x`.
-/
theorem exists_single_adele {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    ∃ s : FiniteAdeleRing (𝓞 E) E, s w = x ∧ ∀ u, u ≠ w → s u = 0 := by
  refine ⟨⟨Pi.single w x, ?_⟩, ?_, ?_⟩
  · refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu => ?_)
    by_contra hne
    apply hu
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  · exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w x
  · intro u hu
    exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) hu x

/- English proof (translation)
Establish `hC0 : 0 < C` using `zero_lt_one.trans hC`. Establish `hint : ∀ k, v (h k) ≤ 1`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨k₀, hk₀⟩` from `hcon`.

Take `⟨k, -, hk⟩` from `Finset.exists_max_image Finset.univ (fun k => v (h k)) ⟨k₀, Finset.mem_univ _⟩`. Establish `h1 : 1 < v (h k)` using `hk₀.trans_le (hk k₀ (Finset.mem_univ _))`. Establish `h0 : 0 < v (h k)` using `zero_lt_one.trans h1`. Take `⟨x, hx⟩` from `hv (C * (v (h k))⁻¹)`. Establish `hxk : v x * v (h k) = C` using `by rw [hx, mul_assoc, inv_mul_cancel₀ h0.ne', mul_one]`.

Establish `key` using `H x (by rw [← hxk]; exact le_mul_of_one_le_right' h1.le) (fun l => by rw [map_mul, ← hxk]; gcongr; exact hk l (Finset.mem_univ _)) k`. Rewrite `key` using `[map_mul, v.map_sub_eq_of_lt_right ((hδ k).trans_lt h1), hxk]`. Conclude with `absurd hC (not_lt.2 key)`. Take `⟨x, hx⟩` from `hv C`. Establish `key` using `H x hx.le (fun l => by rw [map_mul, hx]; exact mul_le_of_le_one_right' (hint l)) j`.

Rewrite `key` using `[map_mul, hx]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem row_bound {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hv : Function.Surjective v) {ι : Type} [Fintype ι] (δ h : ι → K) (hδ : ∀ k, v (δ k) ≤ 1) {C : Γ} (hC : 1 < C)
    (H : ∀ x, v x ≤ C → (∀ k, v (x * h k) ≤ C) → ∀ j, v (x * (δ j - h j)) ≤ 1) (j : ι) :
    v (δ j - h j) ≤ C⁻¹ := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hint : ∀ k, v (h k) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀⟩ := hcon
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => v (h k)) ⟨k₀, Finset.mem_univ _⟩
    have h1 : 1 < v (h k) := hk₀.trans_le (hk k₀ (Finset.mem_univ _))
    have h0 : 0 < v (h k) := zero_lt_one.trans h1
    obtain ⟨x, hx⟩ := hv (C * (v (h k))⁻¹)
    have hxk : v x * v (h k) = C := by rw [hx, mul_assoc, inv_mul_cancel₀ h0.ne', mul_one]
    have key := H x (by rw [← hxk]; exact le_mul_of_one_le_right' h1.le)
      (fun l => by rw [map_mul, ← hxk]; gcongr; exact hk l (Finset.mem_univ _)) k
    rw [map_mul, v.map_sub_eq_of_lt_right ((hδ k).trans_lt h1), hxk] at key
    exact absurd hC (not_lt.2 key)
  obtain ⟨x, hx⟩ := hv C
  have key := H x hx.le (fun l => by rw [map_mul, hx]; exact mul_le_of_le_one_right' (hint l)) j
  rw [map_mul, hx] at key
  calc v (δ j - h j) = C⁻¹ * (C * v (δ j - h j)) := by rw [← mul_assoc, inv_mul_cancel₀ hC0.ne', one_mul]
    _ ≤ C⁻¹ * 1 := by gcongr
    _ = C⁻¹ := mul_one _

/- English proof (translation)
Introduce `E _ _ I w c n a H hn hI hc hH i j`. Establish `hsub : ∀ l, (1 - H) i l w = (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w - H i l w` using `fun l => rfl`. Rewrite using `[hsub, WithZero.exp_neg]`. Use `row_bound Valued.v (w.valuedAdicCompletion_surjective E) (fun l => (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w) (fun l => H i l w) (fun k => ?_) ?_ ?_ j` and prove the remaining obligations. Distinguish the cases in `hik : i = k`.

Substitute `hik` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Establish `: (1 : FiniteAdeleRing (𝓞 E) E) w = 1` using `rfl`. Rewrite using `[this, map_one]`. Rewrite using `[Matrix.one_apply_ne hik]`.

Establish `: (0 : FiniteAdeleRing (𝓞 E) E) w = 0` using `rfl`. Rewrite using `[this, map_zero]`. Conclude with `zero_le`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.

Introduce `x hx hxh l`. Take `⟨s, hsw, hsu⟩` from `exists_single_adele w x`. Establish `h1 : InHat I s` using `fun u => by`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality.

Rewrite using `[hsw, hI, neg_neg]`. Conclude with `hx`. Rewrite using `[hsu u hu, map_zero]`. Conclude with `zero_le`. Establish `h2 : ∀ k, InHat I (s * H i k)` using `fun k u => by`.

Establish `: (s * H i k) u = s u * H i k u` using `rfl`. Rewrite using `[this]`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Rewrite using `[hsw, hI, neg_neg]`.

Conclude with `hxh k`. Rewrite using `[hsu u hu, zero_mul, map_zero]`. Conclude with `zero_le`. Establish `key` using `(inHat_one_iff _).1 (hH s i l h1 h2) w`. Establish `e : (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i l)) w = (n : w.adicCompletion E) * (s w * (1 - H) i l w)` using `rfl`.

Rewrite `key` using `[e, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hn, one_mul, hsw, hsub]`. Conclude with `key`.
-/
theorem valued_one_sub_le_of_moves_integral : ∀ {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (w : HeightOneSpectrum (𝓞 E)) (c : ℤ) (n : E)
  {a : ℕ} (H : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)), w.valuation E n = 1 → FractionalIdeal.count E w I = -c → 1 ≤ c →
  (∀ (s : FiniteAdeleRing (𝓞 E) E) (i j : Fin a), InHat I s → (∀ k, InHat I (s * H i k)) →
    InHat 1 (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i j))) →
  ∀ i j, Valued.v ((1 - H) i j w) ≤ WithZero.exp (-c) := by
  intro E _ _ I w c n a H hn hI hc hH i j
  have hsub : ∀ l, (1 - H) i l w = (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w - H i l w :=
    fun l => rfl
  rw [hsub, WithZero.exp_neg]
  refine row_bound Valued.v (w.valuedAdicCompletion_surjective E)
    (fun l => (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w) (fun l => H i l w) (fun k => ?_) ?_ ?_ j
  · by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq]
      have : (1 : FiniteAdeleRing (𝓞 E) E) w = 1 := rfl
      rw [this, map_one]
    · rw [Matrix.one_apply_ne hik]
      have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
      rw [this, map_zero]; exact zero_le
  · rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro x hx hxh l
    obtain ⟨s, hsw, hsu⟩ := exists_single_adele w x
    have h1 : InHat I s := fun u => by
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hx
      · rw [hsu u hu, map_zero]; exact zero_le
    have h2 : ∀ k, InHat I (s * H i k) := fun k u => by
      have : (s * H i k) u = s u * H i k u := rfl
      rw [this]
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hxh k
      · rw [hsu u hu, zero_mul, map_zero]; exact zero_le
    have key := (inHat_one_iff _).1 (hH s i l h1 h2) w
    have e : (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i l)) w =
        (n : w.adicCompletion E) * (s w * (1 - H) i l w) := rfl
    rw [e, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hn, one_mul, hsw, hsub] at key
    exact key

end GlobalTheory.CosetOrth
