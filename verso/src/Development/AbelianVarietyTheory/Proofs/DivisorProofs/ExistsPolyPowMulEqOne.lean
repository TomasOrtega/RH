import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `s`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Consider the case `cons a s ih`.

Introduce `h`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']`. Conclude with `mul_dvd_mul (dvd_iff_isRoot.mpr (h a (Multiset.mem_cons_self a s))) (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))`.
-/
theorem prod_X_sub_C_dvd_pow_of_isRoot (g : ℂ[X]) :
    ∀ s : Multiset ℂ, (∀ a ∈ s, g.IsRoot a) →
      (s.map fun a => X - C a).prod ∣ g ^ Multiset.card s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact mul_dvd_mul (dvd_iff_isRoot.mpr (h a (Multiset.mem_cons_self a s)))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

/- English proof (translation)
Establish `hc : Multiset.card f.roots = f.natDegree` using `IsAlgClosed.card_roots_eq_natDegree`. Establish `key` using `prod_X_sub_C_dvd_pow_of_isRoot g f.roots h`. Rewrite `key` using `[hc]`. Establish `hf'` using `C_leadingCoeff_mul_prod_multiset_X_sub_C hc`. Rewrite `hf'` using `[hf.leadingCoeff, C_1, one_mul]`.

Rewrite `key` using `[hf']`. Then use the resulting hypothesis.
-/
theorem dvd_pow_natDegree_of_forall_isRoot (f g : ℂ[X]) (hf : f.Monic)
    (h : ∀ a ∈ f.roots, g.IsRoot a) : f ∣ g ^ f.natDegree := by
  have hc : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have key := prod_X_sub_C_dvd_pow_of_isRoot g f.roots h
  rw [hc] at key
  have hf' := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [hf.leadingCoeff, C_1, one_mul] at hf'
  rwa [hf'] at key

/- English proof (translation)
Introduce `n l B hl hB`. Take `⟨k, rfl⟩ : ∃ k, l = k + 1` from `⟨l - 1, by omega⟩`. Use `set f := B.charpoly with hf`. Establish `hfm : f.Monic` using `Matrix.charpoly_monic B`. Establish `hB0 : aeval B f = 0` using `Matrix.aeval_self_charpoly B`.

Establish `hdet : B.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero`. Establish `hroot0 : ∀ a ∈ f.roots, a ≠ 0`. Introduce `a ha h0`. Substitute `h0` using the available equality. Establish `h1 : f.eval 0 = 0` using `(mem_roots hfm.ne_zero).mp ha`.

Apply `hdet` to reduce the goal to its premises. Rewrite using `[Matrix.det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, ← hf, h1, mul_zero]`. Establish `hc : ∀ a : ℂ, ∃ c : ℂ, a ≠ 0 → c ^ (k + 1) * a = 1`. Introduce `a`. Distinguish the cases in `ha : a = 0`.

Conclude with `⟨0, fun h => (h ha).elim⟩`. Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.succ_pos k)`. Conclude with `⟨c, fun _ => by rw [hc, inv_mul_cancel₀ ha]⟩`. Use `choose c hc using hc`. Set `q : ℂ[X]` to `Lagrange.interpolate f.roots.toFinset id c`.

Establish `hq : ∀ a ∈ f.roots, q.eval a = c a`. Introduce `a ha`. Conclude with `Lagrange.eval_interpolate_at_node (s := f.roots.toFinset) (v := id) c (Set.injOn_id _) (Multiset.mem_toFinset.mpr ha)`. Set `g : ℂ[X]` to `X * q ^ (k + 1) - 1`. Establish `hg : ∀ a ∈ f.roots, g.IsRoot a`.

Introduce `a ha`. Use `hc a (hroot0 a ha)` as an intermediate fact. Simplify using `only [g, IsRoot, eval_sub, eval_mul, eval_X, eval_pow, eval_one, hq a ha]`. Rewrite using `[mul_comm, this, sub_self]`. Establish `hdvd : f ∣ g ^ f.natDegree` using `dvd_pow_natDegree_of_forall_isRoot f g hfm hg`.

Set `r : AdjoinRoot f` to `AdjoinRoot.root f`. Set `x : AdjoinRoot f` to `AdjoinRoot.mk f q`. Set `P : (AdjoinRoot f)[X]` to `C r * X ^ (k + 1) - 1`. Establish `hPx : ∀ z, aeval z P = r * z ^ (k + 1) - 1` using `by intro z; simp [P]`. Establish `hmk : r * x ^ (k + 1) - 1 = AdjoinRoot.mk f g`.

Simplify using `[r, x, g, map_sub, map_mul, map_pow, AdjoinRoot.mk_X]`. Establish `hnil : IsNilpotent (aeval x P)`. Use `⟨f.natDegree, ?_⟩` and prove the remaining obligations. Rewrite using `[hPx, hmk, ← map_pow, AdjoinRoot.mk_eq_zero]`. Conclude with `hdvd`.

Establish `hunit : IsUnit (r * x ^ (k + 1))`. Use `hnil.isUnit_add_one` as an intermediate fact. Rewrite `this` using `[hPx, sub_add_cancel]`. Then use the resulting hypothesis. Establish `hunit' : IsUnit (r * x ^ k)`. Rewrite `hunit` using `[pow_succ, ← mul_assoc]`.

Conclude with `isUnit_of_mul_isUnit_left hunit`. Establish `hl : IsUnit ((k + 1 : ℕ) : AdjoinRoot f)`. Establish `: IsUnit ((k + 1 : ℕ) : ℂ)` using `isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))`. Simplify using `using this.map (algebraMap ℂ (AdjoinRoot f))`. Establish `hder : IsUnit (aeval x (derivative P))`.

Establish `h1 : aeval x (derivative P) = ((k + 1 : ℕ) : AdjoinRoot f) * (r * x ^ k)`. Simplify using `[P]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Conclude with `hl.mul hunit'`.

Take `⟨y, ⟨_, hy⟩, _⟩` from `existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hder`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective y`. Use `⟨p, ?_⟩` and prove the remaining obligations. Establish `e : (AdjoinRoot.mk f p) ^ (k + 1) * r = 1`. Rewrite using `[mul_comm]`.

Rewrite `hy` using `[hPx]`. Conclude with `sub_eq_zero.mp hy`. Establish `e2 : AdjoinRoot.mk f (p ^ (k + 1) * X - 1) = 0`. Rewrite using `[map_sub, map_mul, map_pow, AdjoinRoot.mk_X, map_one]`. Conclude with `sub_eq_zero.mpr e`.

Take `⟨b, hb⟩` from `AdjoinRoot.mk_eq_zero.mp e2`. Establish `h2` using `congrArg (aeval B) hb`. Rewrite `h2` using `[map_mul, hB0, zero_mul, map_sub, map_mul, map_pow, aeval_X, map_one]`. Conclude with `sub_eq_zero.mp h2`.
-/
theorem exists_poly_pow_mul_eq_one : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B →
    ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  intro n l B hl hB
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  set f := B.charpoly with hf
  have hfm : f.Monic := Matrix.charpoly_monic B
  have hB0 : aeval B f = 0 := Matrix.aeval_self_charpoly B
  have hdet : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero
  have hroot0 : ∀ a ∈ f.roots, a ≠ 0 := by
    intro a ha h0
    subst h0
    have h1 : f.eval 0 = 0 := (mem_roots hfm.ne_zero).mp ha
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, ← hf, h1, mul_zero]
  have hc : ∀ a : ℂ, ∃ c : ℂ, a ≠ 0 → c ^ (k + 1) * a = 1 := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => (h ha).elim⟩
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.succ_pos k)
      exact ⟨c, fun _ => by rw [hc, inv_mul_cancel₀ ha]⟩
  choose c hc using hc
  let q : ℂ[X] := Lagrange.interpolate f.roots.toFinset id c
  have hq : ∀ a ∈ f.roots, q.eval a = c a := by
    intro a ha
    exact Lagrange.eval_interpolate_at_node (s := f.roots.toFinset) (v := id) c
      (Set.injOn_id _) (Multiset.mem_toFinset.mpr ha)
  let g : ℂ[X] := X * q ^ (k + 1) - 1
  have hg : ∀ a ∈ f.roots, g.IsRoot a := by
    intro a ha
    have := hc a (hroot0 a ha)
    simp only [g, IsRoot, eval_sub, eval_mul, eval_X, eval_pow, eval_one, hq a ha]
    rw [mul_comm, this, sub_self]
  have hdvd : f ∣ g ^ f.natDegree := dvd_pow_natDegree_of_forall_isRoot f g hfm hg
  let r : AdjoinRoot f := AdjoinRoot.root f
  let x : AdjoinRoot f := AdjoinRoot.mk f q
  let P : (AdjoinRoot f)[X] := C r * X ^ (k + 1) - 1
  have hPx : ∀ z, aeval z P = r * z ^ (k + 1) - 1 := by intro z; simp [P]
  have hmk : r * x ^ (k + 1) - 1 = AdjoinRoot.mk f g := by
    simp [r, x, g, map_sub, map_mul, map_pow, AdjoinRoot.mk_X]
  have hnil : IsNilpotent (aeval x P) := by
    refine ⟨f.natDegree, ?_⟩
    rw [hPx, hmk, ← map_pow, AdjoinRoot.mk_eq_zero]
    exact hdvd
  have hunit : IsUnit (r * x ^ (k + 1)) := by
    have := hnil.isUnit_add_one
    rwa [hPx, sub_add_cancel] at this
  have hunit' : IsUnit (r * x ^ k) := by
    rw [pow_succ, ← mul_assoc] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  have hl : IsUnit ((k + 1 : ℕ) : AdjoinRoot f) := by
    have : IsUnit ((k + 1 : ℕ) : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    simpa using this.map (algebraMap ℂ (AdjoinRoot f))
  have hder : IsUnit (aeval x (derivative P)) := by
    have h1 : aeval x (derivative P) = ((k + 1 : ℕ) : AdjoinRoot f) * (r * x ^ k) := by
      simp [P]
      ring
    rw [h1]
    exact hl.mul hunit'
  obtain ⟨y, ⟨_, hy⟩, _⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hder
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨p, ?_⟩
  have e : (AdjoinRoot.mk f p) ^ (k + 1) * r = 1 := by
    rw [mul_comm]
    rw [hPx] at hy
    exact sub_eq_zero.mp hy
  have e2 : AdjoinRoot.mk f (p ^ (k + 1) * X - 1) = 0 := by
    rw [map_sub, map_mul, map_pow, AdjoinRoot.mk_X, map_one]
    exact sub_eq_zero.mpr e
  obtain ⟨b, hb⟩ := AdjoinRoot.mk_eq_zero.mp e2
  have h2 := congrArg (aeval B) hb
  rw [map_mul, hB0, zero_mul, map_sub, map_mul, map_pow, aeval_X, map_one] at h2
  exact sub_eq_zero.mp h2

end GlobalTheory
