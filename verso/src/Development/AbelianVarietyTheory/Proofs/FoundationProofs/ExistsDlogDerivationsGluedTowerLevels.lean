import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ

noncomputable section

namespace GlobalTheory.LevGlue

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, p ^ j = k + 1` from `⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩`. Establish `h1` using `hD.pow hS hx k`. Rewrite `h1` using `[← hk]`. Establish `e : c * x ^ (p ^ j) / (p : Ω) ^ m = ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j))`. Establish `e1 : x ^ (p ^ j) = x ^ k * x` using `by rw [hk, pow_succ]`.

Establish `e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j` using `by push_cast; ring`. Rewrite using `[e1, e2, pow_add]`. Clear the denominators using the available nonvanishing facts. Use `int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_` and prove the remaining obligations. Take the linear combination `(-1 : Ω) * e`.
-/
theorem der_pow_val {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) (hp : (p : Ω) ≠ 0) {x c : Ω} {m j : ℕ} (hx : x ∈ S)
    (h : IsInt p (D x - c * x / (p : Ω) ^ (m + j))) :
    IsInt p (D (x ^ (p ^ j)) - c * x ^ (p ^ j) / (p : Ω) ^ m) := by
  obtain ⟨k, hk⟩ : ∃ k, p ^ j = k + 1 := ⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩
  have h1 := hD.pow hS hx k
  rw [← hk] at h1
  have e : c * x ^ (p ^ j) / (p : Ω) ^ m =
      ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j)) := by
    have e1 : x ^ (p ^ j) = x ^ k * x := by rw [hk, pow_succ]
    have e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j := by push_cast; ring
    rw [e1, e2, pow_add]
    field_simp
  refine int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_
  linear_combination (-1 : Ω) * e

/- English proof (translation)
The claim follows from `IsDer.adjoin (t := {T.ζ m, T.qq m}) (IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m) (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m]) (by rintro x (rfl | rfl); exacts [hz, hq])`.
-/
theorem compat_gen (T : Tower p Ω) {m n : ℕ} (hmn : m ≤ n) {D D' : Ω → Ω}
    (hD : IsDer (Lev T n) D) (hD' : IsDer (Lev T m) D')
    (hz : IsInt p (D (T.ζ m) - D' (T.ζ m))) (hq : IsInt p (D (T.qq m) - D' (T.qq m))) :
    ∀ x ∈ Lev T m, IsInt p (D x - D' x) :=
  IsDer.adjoin (t := {T.ζ m, T.qq m}) (IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m)
    (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m])
    (by rintro x (rfl | rfl); exacts [hz, hq])

/- English proof (translation)
Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Establish `hS` using `Lev_int T (m + j)`. Establish `zm` using `zeta_mem_Lev T (m + j)`. Establish `qm` using `qq_mem_Lev T (m + j)`. Establish `z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt p (D x) → IsInt p (D x - 0 * x / (p : Ω) ^ (m + j))` using `fun h => int_congr h (by ring)`.

Establish `z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt p (D y - 0 * y / (p : Ω) ^ m) → IsInt p (D y)` using `fun h => int_congr h (by ring)`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `der_pow_val hz hS hp zm hv.1` as an intermediate fact. Rewrite `this` using `[zeta_pow]`. Then use the resulting hypothesis. Use `z1 (der_pow_val hz hS hp qm (z0 hv.2.1))` as an intermediate fact.

Rewrite `this` using `[qq_pow]`. Then use the resulting hypothesis. Use `z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))` as an intermediate fact. Rewrite `this` using `[zeta_pow]`. Then use the resulting hypothesis. Use `der_pow_val hq hS hp qm hv.2.2.2` as an intermediate fact. Rewrite `this` using `[qq_pow]`. Then use the resulting hypothesis.
-/
theorem vals_down (T : Tower p Ω) (hp : (p : Ω) ≠ 0) {m n : ℕ} (hmn : m ≤ n) {dz dq : Ω → Ω}
    (hz : IsDer (Lev T n) dz) (hq : IsDer (Lev T n) dq) (hv : Vals T n dz dq) : Vals T m dz dq := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hS := Lev_int T (m + j)
  have zm := zeta_mem_Lev T (m + j)
  have qm := qq_mem_Lev T (m + j)
  have z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt p (D x) → IsInt p (D x - 0 * x / (p : Ω) ^ (m + j)) :=
    fun h => int_congr h (by ring)
  have z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt p (D y - 0 * y / (p : Ω) ^ m) → IsInt p (D y) :=
    fun h => int_congr h (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := der_pow_val hz hS hp zm hv.1
    rwa [zeta_pow] at this
  · have := z1 (der_pow_val hz hS hp qm (z0 hv.2.1))
    rwa [qq_pow] at this
  · have := z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))
    rwa [zeta_pow] at this
  · have := der_pow_val hq hS hp qm hv.2.2.2
    rwa [qq_pow] at this

/- English proof (translation)
Set `M : Ω → ℕ` to `fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0`. Establish `hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (F (M x) x - F m x)`. Introduce `m x hx`. Establish `h : ∃ m, x ∈ Lev T (m + 1)` using `⟨m, hx⟩`. Establish `hM : M x = Classical.choose h` using `dif_pos h`.

Establish `ha` using `Classical.choose_spec h`. Rewrite using `[hM]`. Establish `h1` using `hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha`. Establish `h2` using `hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx`. Conclude with `int_congr (int_sub h2 h1) (by ring)`.

Use `⟨fun x => F (M x) x, hG, fun S hS => ?_⟩` and prove the remaining obligations. Establish `two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1)`. Introduce `x hx y hy`. Take `⟨a, ha⟩` from `hS x hx`. Take `⟨b, hb⟩` from `hS y hy`.

Conclude with `⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩`. Use `⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩` and prove the remaining obligations. Take `⟨n, hxn, hyn⟩` from `two x hx y hy`. Use `int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn) (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Take `⟨n, hxn, hyn⟩` from `two x hx y hy`. Establish `ix` using `Lev_int T _ x hxn`. Establish `iy` using `Lev_int T _ y hyn`. Use `int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn) (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hm` using `(Lev T (0 + 1)).algebraMap_mem c`. Conclude with `int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)`.
-/
theorem glue_fam (T : Tower p Ω) (F : ℕ → Ω → Ω) (hF : ∀ m, IsDer (Lev T (m + 1)) (F m))
    (hc : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (F n x - F m x)) :
    ∃ G : Ω → Ω, (∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (G x - F m x)) ∧
      ∀ S : Subalgebra (O0 p) Ω, (∀ x ∈ S, ∃ m, x ∈ Lev T m) → IsDer S G := by
  classical
  let M : Ω → ℕ := fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0
  have hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (F (M x) x - F m x) := by
    intro m x hx
    have h : ∃ m, x ∈ Lev T (m + 1) := ⟨m, hx⟩
    have hM : M x = Classical.choose h := dif_pos h
    have ha := Classical.choose_spec h
    rw [hM]
    have h1 := hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha
    have h2 := hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx
    exact int_congr (int_sub h2 h1) (by ring)
  refine ⟨fun x => F (M x) x, hG, fun S hS => ?_⟩
  have two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1) := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hS x hx
    obtain ⟨b, hb⟩ := hS y hy
    exact ⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    refine int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn)
      (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_
    ring
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    have ix := Lev_int T _ x hxn
    have iy := Lev_int T _ y hyn
    refine int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn)
      (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_
    ring
  · have hm := (Lev T (0 + 1)).algebraMap_mem c
    exact int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)

/- English proof (translation)
Introduce `p _ Ω _ _ hclo T B hB hlev`. Use `haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo`. Establish `hp : (p : Ω) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Establish `h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, IsDer (Lev T (m + 1)) dz ∧ IsDer (Lev T (m + 1)) dq ∧ Vals T (m + 1) dz dq` using `fun m => hlev (m + 1) (by omega)`. Use `choose Z Q hZ hQ hV using h'`.

Establish `cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Z n x - Z m x)`. Introduce `m n hmn`. Establish `v` using `vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)`. Conclude with `compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m) (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))`. Establish `cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Q n x - Q m x)`.

Introduce `m n hmn`. Establish `v` using `vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)`. Conclude with `compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m) (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring)) (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))`. Take `⟨dz, hdz, hdzB⟩` from `glue_fam T Z hZ cZ`. Take `⟨dq, hdq, hdqB⟩` from `glue_fam T Q hQ cQ`.

Use `⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `v` using `hV k`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)`.

Conclude with `int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)`. Conclude with `int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)`. Conclude with `int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)`.
-/
theorem glue : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
    (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
    ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  intro p _ Ω _ _ hclo T B hB hlev
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, IsDer (Lev T (m + 1)) dz ∧ IsDer (Lev T (m + 1)) dq ∧
      Vals T (m + 1) dz dq := fun m => hlev (m + 1) (by omega)
  choose Z Q hZ hQ hV using h'
  have cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Z n x - Z m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m)
      (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))
  have cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Q n x - Q m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m)
      (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring))
      (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))
  obtain ⟨dz, hdz, hdzB⟩ := glue_fam T Z hZ cZ
  obtain ⟨dq, hdq, hdqB⟩ := glue_fam T Q hQ cQ
  refine ⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have v := hV k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)
  · exact int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)

end GlobalTheory.LevGlue
