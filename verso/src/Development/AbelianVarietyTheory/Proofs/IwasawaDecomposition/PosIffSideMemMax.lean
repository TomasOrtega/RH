import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

/- English proof (translation)
Establish `hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0))` using `(RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Establish `hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)), algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y`. Use `⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩` and prove the remaining obligations. Rewrite using `[← IsFractionRing.injective _ _ (h2.trans hy.symm)]`.

Conclude with `h1`. Establish `e1` using `h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])`. Simplify using `only [map_one, mul_one] at e1`. Rewrite using `[hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]`. Conclude with `⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩`.
-/
theorem pos_iff_side_mem_max {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0)
    (e : ↥D.LL0 →+* FractionRing (D.ntw.O0 (c.twI w)))
    (he : e = if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y = e (x : ↥D.LL0) := by
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have e1 := h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])
  simp only [map_one, mul_one] at e1
  rw [hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]
  exact ⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hq` using `D.what₂.places.resChar_prime w`. Establish `hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)`. Rewrite using `[D.what₂.places.val_resChar w]`. Conclude with `D.what₂.places.ramIdx_pos w` after adjusting the coercions.

Establish `hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)`. Take `⟨a, b, hab⟩` from `hc`. Establish `hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`. Conclude with `(D.what₂.places.val w).map_le_add ih (by simp)`. Establish `hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL)`.

Introduce `n`. Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Simplify using `using hnat m`. Rewrite using `[Int.cast_neg, AddValuation.map_neg]`. Simplify using `using hnat m`.

Establish `h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1`. Conclude with `congrArg (Int.cast : ℤ → D.what₂.LL) hab` after adjusting the coercions. Establish `h2 : 0 < D.what₂.places.val w 1`. Rewrite using `[← h1]`. Use `(D.what₂.places.val w).map_lt_add ?_ ?_` and prove the remaining obligations.

Rewrite using `[AddValuation.map_mul]`. Conclude with `hq0.trans_le (le_add_of_nonneg_left (hint a))`. Rewrite using `[AddValuation.map_mul]`. Conclude with `h.trans_le (le_add_of_nonneg_left (hint b))`. Simplify using `at h2`.
-/
theorem resChar_eq_of_pos {D : D7} (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hq := D.what₂.places.resChar_prime w
  have hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (D.what₂.places.val w).map_le_add ih (by simp)
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hnat m
  have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
  have h2 : 0 < D.what₂.places.val w 1 := by
    rw [← h1]
    refine (D.what₂.places.val w).map_lt_add ?_ ?_
    · rw [AddValuation.map_mul]; exact hq0.trans_le (le_add_of_nonneg_left (hint a))
    · rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b))
  simp at h2

/- English proof (translation)
Introduce and unpack `p hp w hw ⟨w', -, hw'⟩`. Use `⟨c.twI w', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[c.twI_l]`. Use `resChar_eq_of_pos w' hp ?_` and prove the remaining obligations. Simplify using `using (hw' _).1 hw`.

Consider the cases of `hs : c.sd w'`. Conclude with `Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))`. Conclude with `Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))`.
-/
theorem twCoverPair_of_tie (D : D7) (c : NChoice D) (h : NChTie D c) : TwCoverPair D := by
  rintro p hp w hw ⟨w', -, hw'⟩
  refine ⟨c.twI w', ?_, ?_⟩
  · rw [c.twI_l]
    refine resChar_eq_of_pos w' hp ?_
    simpa using (hw' _).1 hw
  · cases hs : c.sd w'
    · exact Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))
    · exact Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))

end GlobalTheory.Mem.Top

end
