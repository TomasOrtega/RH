import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Rewrite `hkj` using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`. Take `⟨q, hq⟩` from `hkj`. Establish `hj : j = k + (N : ℤ) * q` using `by linarith`. Rewrite using `[hj, zpow_add₀ h0, zpow_mul, zpow_natCast, h, one_zpow, mul_one]`.
-/
theorem zpow_eq_zpow_of_intCast_eq {K : Type} [Field K] {ξ : K} {N : ℕ} (h0 : ξ ≠ 0)
    (h : ξ ^ N = 1) {k j : ℤ} (hkj : (k : ZMod N) = (j : ZMod N)) : ξ ^ k = ξ ^ j := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkj
  obtain ⟨q, hq⟩ := hkj
  have hj : j = k + (N : ℤ) * q := by linarith
  rw [hj, zpow_add₀ h0, zpow_mul, zpow_natCast, h, one_zpow, mul_one]

/- English proof (translation)
Use `Finset.sum_nbij' (fun f => f.val) (fun v => (v : ZMod N)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `f _`. Simplify using `using ZMod.val_lt f`. Introduce `v _`. Simplify using the standard rewrite rules.

Introduce `f _`. Simplify using the standard rewrite rules. Introduce `v hv; exact ZMod.val_cast_of_lt (by simpa using hv)`. Introduce `f _`. Both sides reduce to the same expression.
-/
theorem sum_zmod_val_eq_sum_range {K : Type} [Field K] (N : ℕ) [NeZero N] (G : ℕ → K) :
    ∑ r : ZMod N, G r.val = ∑ k ∈ Finset.range N, G k := by
  refine Finset.sum_nbij' (fun f => f.val) (fun v => (v : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro f _; simpa using ZMod.val_lt f
  · intro v _; simp
  · intro f _; simp
  · intro v hv; exact ZMod.val_cast_of_lt (by simpa using hv)
  · intro f _; rfl

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ c ih`. Rewrite using `[Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[add_comm]`.
-/
theorem sum_range_mul_split {K : Type} [Field K] (G : ℕ → K) (b c : ℕ) :
    ∑ k ∈ Finset.range (b * c), G k = ∑ t ∈ Finset.range c, ∑ a ∈ Finset.range b, G (a + b * t) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [add_comm]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `K _ _ l m n _ _ ζ ψ hl hm hmn hζ hψ X`. Establish `hl0 : 0 < l` using `hl.pos`. Establish `hN : l ^ n = l ^ (n - m) * l ^ m` using `by rw [← pow_add, Nat.sub_add_cancel hmn]`. Establish `hN' : l ^ n = l ^ m * l ^ (n - m)` using `by rw [hN, mul_comm]`. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero (by positivity)`.

Use `set F : ℕ → K := fun k => ψ (k : ZMod (l ^ m)) * ζ ^ ((k : ℤ) * X) with hF`. Establish `h1 : ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X) = ∑ k ∈ Finset.range (l ^ n), F k` using `sum_zmod_val_eq_sum_range (l ^ n) F`. Use `set y : K := ζ ^ (((l ^ m : ℕ) : ℤ) * X) with hy`. Establish `h3 : ∀ a t : ℕ, F (a + l ^ m * t) = F a * y ^ t`. Introduce `a t`.

Simplify using `only [hF, hy]`. Establish `hc : ((a + l ^ m * t : ℕ) : ZMod (l ^ m)) = (a : ZMod (l ^ m))`. Rewrite using `[Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]`. Rewrite using `[hc, mul_assoc]`. Use `congr 1`.

Establish `he : ((a + l ^ m * t : ℕ) : ℤ) * X = (a : ℤ) * X + (((l ^ m : ℕ) : ℤ) * X) * (t : ℤ)` using `by push_cast; ring`. Rewrite using `[he, zpow_add₀ hζ0, zpow_mul ζ (((l ^ m : ℕ) : ℤ) * X) (t : ℤ), zpow_natCast]`. Establish `h2 : ∑ k ∈ Finset.range (l ^ n), F k = (∑ a ∈ Finset.range (l ^ m), F a) * ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t`. Rewrite using `[hN', sum_range_mul_split, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[h3]`. Establish `hω : IsPrimitiveRoot (ζ ^ (l ^ m)) (l ^ (n - m))` using `hζ.pow (by positivity) hN'`. Establish `hyω : y = (ζ ^ (l ^ m)) ^ X`.

Rewrite using `[hy, zpow_mul, zpow_natCast]`. Establish `h4 : ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t = if (l : ℤ) ^ (n - m) ∣ X then ((l : K) ^ (n - m)) else 0` using `by split_ifs with hd`. Establish `: y = 1`. Rewrite using `[hyω]; exact (hω.zpow_eq_one_iff_dvd X).2 (by exact_mod_cast hd)`. Simplify using `[this]`.

Establish `hy1 : y ≠ 1`. Rewrite using `[hyω]`. Introduce `h`. Conclude with `hd (by exact_mod_cast (hω.zpow_eq_one_iff_dvd X).1 h)`. Rewrite using `[geom_sum_eq hy1]`.

Establish `: y ^ (l ^ (n - m)) = 1`. Rewrite using `[hyω, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one, one_zpow]`. Rewrite using `[this, sub_self, zero_div]`. Establish `h5 : ∑ a ∈ Finset.range (l ^ m), F a = ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * X)`. Rewrite using `[← sum_zmod_val_eq_sum_range (l ^ m) F]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [hF, ZMod.natCast_zmod_val]`. Rewrite using `[h1, h2, h4, h5]`. Use `split_ifs with hd`. Take `⟨Y, rfl⟩` from `hd`.

Establish `hL0 : (l : ℤ) ^ (n - m) ≠ 0` using `by positivity`. Rewrite using `[Int.mul_ediv_cancel_left _ hL0]`. Establish `hξ : IsPrimitiveRoot (ζ ^ (l ^ (n - m))) (l ^ m)` using `hζ.pow (by positivity) hN`. Establish `hξ0 : ζ ^ (l ^ (n - m)) ≠ 0` using `pow_ne_zero _ hζ0`. Set `e : AddChar (ZMod (l ^ m)) K` to `AddChar.zmodChar (l ^ m) hξ.pow_eq_one`.

Establish `key` using `gaussSum_mulShift_of_isPrimitive e hψ (Y : ZMod (l ^ m))`. Establish `hG : gaussSum ψ e = ∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)`. Unfold `gaussSum`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.zmodChar_apply, pow_mul]`.

Establish `hS : ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y)) = gaussSum ψ (e.mulShift Y)`. Unfold `gaussSum`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.mulShift_apply, AddChar.zmodChar_apply]`. Use `congr 1`.

Establish `he : (a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y) = ((l ^ (n - m) : ℕ) : ℤ) * ((a.val : ℤ) * Y)` using `by push_cast; ring`. Rewrite using `[he, zpow_mul, zpow_natCast, ← zpow_natCast (ζ ^ l ^ (n - m)) ((Y : ZMod (l ^ m)) * a).val]`. Use `zpow_eq_zpow_of_intCast_eq hξ0 hξ.pow_eq_one ?_` and prove the remaining obligations. Use `push_cast`. Simplify using `[ZMod.natCast_val, ZMod.cast_id', mul_comm]`.

Rewrite using `[hS, key, ← hG]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem sum_primChar_mul_rootPow_mod_pow : ∀ (K : Type) [Field K] [CharZero K] (l m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)] (ζ : K) (ψ : DirichletCharacter K (l ^ m)), l.Prime → 1 ≤ m → m ≤ n → IsPrimitiveRoot ζ (l ^ n) → ψ.IsPrimitive → ∀ X : ℤ, ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X) = if (l : ℤ) ^ (n - m) ∣ X then (l : K) ^ (n - m) * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) * ψ⁻¹ ((X / (l : ℤ) ^ (n - m) : ℤ) : ZMod (l ^ m)) else 0 := by
  intro K _ _ l m n _ _ ζ ψ hl hm hmn hζ hψ X
  have hl0 : 0 < l := hl.pos
  have hN : l ^ n = l ^ (n - m) * l ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  have hN' : l ^ n = l ^ m * l ^ (n - m) := by rw [hN, mul_comm]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  set F : ℕ → K := fun k => ψ (k : ZMod (l ^ m)) * ζ ^ ((k : ℤ) * X) with hF
  have h1 : ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X)
      = ∑ k ∈ Finset.range (l ^ n), F k := sum_zmod_val_eq_sum_range (l ^ n) F
  set y : K := ζ ^ (((l ^ m : ℕ) : ℤ) * X) with hy
  have h3 : ∀ a t : ℕ, F (a + l ^ m * t) = F a * y ^ t := by
    intro a t
    simp only [hF, hy]
    have hc : ((a + l ^ m * t : ℕ) : ZMod (l ^ m)) = (a : ZMod (l ^ m)) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hc, mul_assoc]
    congr 1
    have he : ((a + l ^ m * t : ℕ) : ℤ) * X = (a : ℤ) * X + (((l ^ m : ℕ) : ℤ) * X) * (t : ℤ) := by
      push_cast; ring
    rw [he, zpow_add₀ hζ0, zpow_mul ζ (((l ^ m : ℕ) : ℤ) * X) (t : ℤ), zpow_natCast]
  have h2 : ∑ k ∈ Finset.range (l ^ n), F k
      = (∑ a ∈ Finset.range (l ^ m), F a) * ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t := by
    rw [hN', sum_range_mul_split, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3]
  have hω : IsPrimitiveRoot (ζ ^ (l ^ m)) (l ^ (n - m)) := hζ.pow (by positivity) hN'
  have hyω : y = (ζ ^ (l ^ m)) ^ X := by
    rw [hy, zpow_mul, zpow_natCast]
  have h4 : ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t
      = if (l : ℤ) ^ (n - m) ∣ X then ((l : K) ^ (n - m)) else 0 := by
    split_ifs with hd
    · have : y = 1 := by
        rw [hyω]; exact (hω.zpow_eq_one_iff_dvd X).2 (by exact_mod_cast hd)
      simp [this]
    · have hy1 : y ≠ 1 := by
        rw [hyω]; intro h
        exact hd (by exact_mod_cast (hω.zpow_eq_one_iff_dvd X).1 h)
      rw [geom_sum_eq hy1]
      have : y ^ (l ^ (n - m)) = 1 := by
        rw [hyω, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one,
          one_zpow]
      rw [this, sub_self, zero_div]
  have h5 : ∑ a ∈ Finset.range (l ^ m), F a = ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * X) := by
    rw [← sum_zmod_val_eq_sum_range (l ^ m) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hF, ZMod.natCast_zmod_val]
  rw [h1, h2, h4, h5]
  split_ifs with hd
  · obtain ⟨Y, rfl⟩ := hd
    have hL0 : (l : ℤ) ^ (n - m) ≠ 0 := by positivity
    rw [Int.mul_ediv_cancel_left _ hL0]
    have hξ : IsPrimitiveRoot (ζ ^ (l ^ (n - m))) (l ^ m) := hζ.pow (by positivity) hN
    have hξ0 : ζ ^ (l ^ (n - m)) ≠ 0 := pow_ne_zero _ hζ0
    let e : AddChar (ZMod (l ^ m)) K := AddChar.zmodChar (l ^ m) hξ.pow_eq_one
    have key := gaussSum_mulShift_of_isPrimitive e hψ (Y : ZMod (l ^ m))
    have hG : gaussSum ψ e = ∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.zmodChar_apply, pow_mul]
    have hS : ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y))
        = gaussSum ψ (e.mulShift Y) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.mulShift_apply, AddChar.zmodChar_apply]
      congr 1
      have he : (a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y) = ((l ^ (n - m) : ℕ) : ℤ) * ((a.val : ℤ) * Y) := by
        push_cast; ring
      rw [he, zpow_mul, zpow_natCast, ← zpow_natCast (ζ ^ l ^ (n - m)) ((Y : ZMod (l ^ m)) * a).val]
      refine zpow_eq_zpow_of_intCast_eq hξ0 hξ.pow_eq_one ?_
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id', mul_comm]
    rw [hS, key, ← hG]
    ring
  · simp
end GlobalTheory.EisM
