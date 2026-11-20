import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ

open MvPolynomial

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

open Classical in

def blkWtZ (k : K) : (Σ k, ι k) → ℤ := fun q => if q.1 = k then 1 else 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[blkWtZ]`. Introduce `b _ hb`. Simplify using `[blkWtZ, hb]`. Simplify using the standard rewrite rules.
-/
theorem weight_blkWtZ (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blkWtZ (ι := ι) k) m = ∑ i, (m ⟨k, i⟩ : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blkWtZ]
  · intro b _ hb
    simp [blkWtZ, hb]
  · simp

/- English proof (translation)
Introduce `d hd`. Rewrite using `[weight_blkWtZ, ← h d (mem_support_iff.mpr hd) k]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem isWeightedHomogeneous_blkWtZ {f : MRingOver R ι} {a : K → ℕ} (h : IsMultiHomog f a)
    (k : K) : IsWeightedHomogeneous (blkWtZ (ι := ι) k) f (a k : ℤ) := by
  intro d hd
  rw [weight_blkWtZ, ← h d (mem_support_iff.mpr hd) k]
  push_cast
  rfl

/- English proof (translation)
Introduce `m hm k`. Establish `e` using `h k (mem_support_iff.mp hm)`. Rewrite `e` using `[weight_blkWtZ, ← Nat.cast_sum]`. Use `show _ = (n k).toNat`. Rewrite using `[← e, Int.toNat_natCast]`.
-/
theorem isMultiHomog_of_blkWtZ {f : MRingOver R ι} {n : K → ℤ}
    (h : ∀ k, IsWeightedHomogeneous (blkWtZ (ι := ι) k) f (n k)) :
    IsMultiHomog f (fun k => (n k).toNat) := by
  intro m hm k
  have e := h k (mem_support_iff.mp hm)
  rw [weight_blkWtZ, ← Nat.cast_sum] at e
  show _ = (n k).toNat
  rw [← e, Int.toNat_natCast]

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[coeff_pderiv]`. Establish `h1 : coeff (m + Finsupp.single q 1) f ≠ 0` using `fun h0 => hm (by rw [h0, zero_mul])`. Establish `h2` using `h h1`. Rewrite `h2` using `[map_add]`.

Establish `h3 : Finsupp.weight w (Finsupp.single q 1) = w q`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul]`. Rewrite `h2` using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isWeightedHomogeneous_pderiv_int {σ : Type*} {w : σ → ℤ} {f : MvPolynomial σ R} {d : ℤ}
    (h : IsWeightedHomogeneous w f d) (q : σ) :
    IsWeightedHomogeneous w (pderiv q f) (d - w q) := by
  classical
  intro m hm
  rw [coeff_pderiv] at hm
  have h1 : coeff (m + Finsupp.single q 1) f ≠ 0 := fun h0 => hm (by rw [h0, zero_mul])
  have h2 := h h1
  rw [map_add] at h2
  have h3 : Finsupp.weight w (Finsupp.single q 1) = w q := by
    rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul]
  rw [h3] at h2
  linarith

end ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
