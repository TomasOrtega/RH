import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
/- English proof (translation)
Use function extensionality and compare the values at `k i`. Establish `hk` using `congrFun (congrFun hm k) i`. Simplify using `only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk`. Establish `hRq : (R : ℚ) ≠ 0` using `by positivity`. Rewrite `hk` using `[neg_add_eq_sub, ← sub_div, div_eq_iff hRq]`.

Establish `hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i`. Take the linear combination `hk`. Establish `hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i`. Conclude with `hzq` after adjusting the coercions. Establish `hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R` using `by exact_mod_cast (n' k i).isLt`.

Establish `ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R` using `by exact_mod_cast (n k i).isLt`. Establish `h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0`. Apply `Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩` to reduce the goal to its premises. Rewrite using `[abs_lt]`. Apply the tactic sequence `constructor <;>`.

Combine the linear relations using `[Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]`. Conclude with `Fin.ext (by omega)`.
-/
private theorem rep_eq_of_neg_rep_add_rep_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)

open Matrix Complex in
open scoped ComplexConjugate Real in
/- English proof (translation)
Take `⟨M, hM⟩` from `(_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx`. Establish `hRR : (0 : ℤ) < (R : ℤ) * R` using `by positivity`. Establish `hRq : (R : ℚ) ≠ 0` using `by positivity`. Use `⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩` and prove the remaining obligations. Establish `h1` using `Int.emod_nonneg (M k i) hRR.ne'`.

Establish `h2` using `Int.emod_lt_of_pos (M k i) hRR`. Establish `h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R`. Rewrite using `[Int.toNat_of_nonneg h1]`. Conclude with `h2`. Conclude with `h3` after adjusting the coercions.

Use extensionality with `k i`. Establish `hk` using `congrFun (congrFun hM k) i`. Simplify using `only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk`. Simplify using `only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]`. Establish `h1` using `Int.emod_nonneg (M k i) hRR.ne'`.

Establish `hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg h1]`. Establish `hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ)`. Use `Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)` as an intermediate fact. Establish `h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) + ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ)`.

Conclude with `this` after adjusting the coercions. Take the linear combination `h'`. Establish `hx' : x k i = (M k i : ℚ) / R`. Rewrite using `[eq_div_iff hRq]`. Take the linear combination `hk`.

Rewrite using `[hx', hn, ← hq, add_div]`. Use `congr 1`. Rewrite using `[mul_assoc, mul_div_cancel_left₀ _ hRq]`.
-/
private theorem exists_rep_add_natCast_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]

open Matrix Complex in
open scoped ComplexConjugate Real in

/- English proof (translation)
Introduce `κ ι _ _ _ _ R φ F hR hφ hsum`. Establish `hRq : (R : ℚ) ≠ 0` using `by positivity`. Establish `hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m = R • _root_.GlobalTheory.SW.FourierJ.zm m` using `fun m => Nat.cast_smul_eq_nsmul ℚ R _`. Set `e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ` to `fun p => _root_.GlobalTheory.SW.FourierJ.rep R p.1 + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm p.2`. Establish `he : Function.Injective e`.

Introduce and unpack `⟨n, m⟩ ⟨n', m'⟩ h`. Simplify using `only [e] at h`. Establish `hn : n = n'`. Apply `rep_eq_of_neg_rep_add_rep_eq_smul_zm hR (m - m')` to reduce the goal to its premises. Use extensionality with `k i`.

Establish `hk` using `congrFun (congrFun h k) i`. Simplify using `only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul, smul_eq_mul, Pi.sub_apply] at hk ⊢`. Use `push_cast`. Take the linear combination `-hk`. Substitute `hn` using the available equality.

Establish `hm : m = m'`. Use function extensionality and compare the values at `k i`. Establish `hk` using `congrFun (congrFun h k) i`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, smul_eq_mul, add_right_inj] at hk`. Conclude with `mul_left_cancel₀ hRq hk` after adjusting the coercions.

Rewrite using `[hm]`. Establish `hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e`. Introduce `x hx`. Establish `hφx : φ x ≠ 0` using `left_ne_zero_of_mul (Function.mem_support.mp hx)`. Take `⟨n, m, hnm⟩` from `exists_rep_add_natCast_smul_zm_of_intM_smul hR x (hφ.1 x hφx)`.

Conclude with `⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩`. Rewrite using `[← he.tsum_eq hsupp]`. Establish `hs2 : Summable fun p => φ (e p) * F (e p)` using `hsum.comp_injective he`. Rewrite using `[hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)), tsum_fintype]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Simplify using `only [e]`. Rewrite using `[hφ.2 _ _ ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]`.
-/
theorem _root_.GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    Summable (fun x => φ x * F x) → ∑' x, φ x * F x =
      ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) *
        ∑' m : κ → ι → ℤ, F (_root_.GlobalTheory.SW.FourierJ.rep R n +
          (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m) := by
  intro κ ι _ _ _ _ R φ F hR hφ hsum
  have hRq : (R : ℚ) ≠ 0 := by positivity
  have hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m = R • _root_.GlobalTheory.SW.FourierJ.zm m :=
    fun m => Nat.cast_smul_eq_nsmul ℚ R _
  let e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ := fun p =>
    _root_.GlobalTheory.SW.FourierJ.rep R p.1 + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm p.2
  have he : Function.Injective e := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ h
    simp only [e] at h
    have hn : n = n' := by
      apply rep_eq_of_neg_rep_add_rep_eq_smul_zm hR (m - m')
      ext k i
      have hk := congrFun (congrFun h k) i
      simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul, smul_eq_mul,
        Pi.sub_apply] at hk ⊢
      push_cast
      linear_combination -hk
    subst hn
    have hm : m = m' := by
      funext k i
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.add_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply,
        smul_eq_mul, add_right_inj] at hk
      exact_mod_cast mul_left_cancel₀ hRq hk
    rw [hm]
  have hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e := by
    intro x hx
    have hφx : φ x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hx)
    obtain ⟨n, m, hnm⟩ := exists_rep_add_natCast_smul_zm_of_intM_smul hR x (hφ.1 x hφx)
    exact ⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩
  rw [← he.tsum_eq hsupp]
  have hs2 : Summable fun p => φ (e p) * F (e p) := hsum.comp_injective he
  rw [hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)),
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [e]
  rw [hφ.2 _ _ ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]

end GlobalTheory.SW.FourierJ
