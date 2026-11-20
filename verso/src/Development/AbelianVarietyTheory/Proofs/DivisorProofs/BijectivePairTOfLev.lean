import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.TatePerfect

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, pow_zero, Tate.lev_zero]`. Consider the case `succ k ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]`.
-/
theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (k n : ℕ) :
    (k • t).lev n = t.lev n ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

/- English proof (translation)
Establish `e : t = t' + (t - t')` using `by abel`. Establish `h3 : (t - t').lev n = 1`. Use `congrArg (·.lev n) e` as an intermediate fact. Simplify using `only [Tate.lev_add] at this`. Rewrite `this` using `[h]`.

Conclude with `left_eq_mul.1 this`. Take `⟨s, hs⟩` from `(h2 n _).1 h3`. Rewrite using `[e, hs, map_add, map_smul, Tate.lev_add, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, lev_nsmul, Tate.lev_pow, _root_.mul_one]`.
-/
theorem lev_congr {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (h2 : ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s)
    (φ : Tate p M →ₗ[ℤ_[p]] Tate p M') {n : ℕ} {t t' : Tate p M} (h : t.lev n = t'.lev n) :
    (φ t).lev n = (φ t').lev n := by
  have e : t = t' + (t - t') := by abel
  have h3 : (t - t').lev n = 1 := by
    have := congrArg (·.lev n) e
    simp only [Tate.lev_add] at this
    rw [h] at this
    exact left_eq_mul.1 this
  obtain ⟨s, hs⟩ := (h2 n _).1 h3
  rw [e, hs, map_add, map_smul, Tate.lev_add, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, lev_nsmul,
    Tate.lev_pow, _root_.mul_one]

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  (A : Out.PolAV (Sp C))

/- English proof (translation)
Use `choose! τ hτ using h1`. Set `κ : ℕ → GlobalTheory.ChTor.Pts A.A → Cˣ` to `fun n x => (φ (τ n x)).lev n`. Establish `hκ : ∀ n (t : TateA A p), κ n (t.lev n) = (φ t).lev n` using `fun n t => lev_congr h2 φ (hτ n _ (t.lev_pow n))`. Establish `hm : ∀ n z z', z ^ p ^ n = 1 → z' ^ p ^ n = 1 → κ n (z * z') = κ n z * κ n z'`. Introduce `n z z' hz hz'`.

Establish `e : z * z' = (τ n z + τ n z').lev n` using `by rw [Tate.lev_add, hτ n z hz, hτ n z' hz']`. Rewrite using `[e, hκ, map_add, Tate.lev_add]`. Establish `hp` using `fun n => weil_perfect (A := A) (one_le_ppow p n) (κ n) (hm n)`. Use `choose s hs hu using hp`. Establish `hc : ∀ n, s (n + 1) ^ p = s n`.

Introduce `n`. Use `hu n _ ⟨?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_succ']`. Conclude with `(hs (n + 1)).1`. Establish `hz' : z ^ p ^ (n + 1) = 1` using `by rw [pow_succ, pow_mul, hz, one_pow]`.

Rewrite using `[← weil_level (one_le_ppow p n) (Fact.out : p.Prime).pos hz (by rw [← pow_succ]; exact (hs (n + 1)).1), ← pow_succ, (hs (n + 1)).2 z hz']`. Establish `e : z = (p • τ n z).lev (n + 1)` using `by rw [lev_nsmul, Tate.lev_succ, hτ n z hz]`. Use `conv_lhs => rw [e, hκ, map_nsmul, lev_nsmul, Tate.lev_succ]`. Use `⟨Tate.mk s fun n => ⟨(hs n).1, hc n⟩, fun t => Tate.ext fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[lev_weilT, Tate.lev_mk, (hs n).2 _ (t.lev_pow n), hκ]`.
-/
theorem weilT_flip_surjective
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (h2 : ∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s)
    (φ : TateA A p →ₗ[ℤ_[p]] Tate p Cˣ) : ∃ s : TateA A p, ∀ t, weilT A p t s = φ t := by
  choose! τ hτ using h1
  let κ : ℕ → GlobalTheory.ChTor.Pts A.A → Cˣ := fun n x => (φ (τ n x)).lev n
  have hκ : ∀ n (t : TateA A p), κ n (t.lev n) = (φ t).lev n := fun n t =>
    lev_congr h2 φ (hτ n _ (t.lev_pow n))
  have hm : ∀ n z z', z ^ p ^ n = 1 → z' ^ p ^ n = 1 → κ n (z * z') = κ n z * κ n z' := by
    intro n z z' hz hz'
    have e : z * z' = (τ n z + τ n z').lev n := by rw [Tate.lev_add, hτ n z hz, hτ n z' hz']
    rw [e, hκ, map_add, Tate.lev_add]
  have hp := fun n => weil_perfect (A := A) (one_le_ppow p n) (κ n) (hm n)
  choose s hs hu using hp
  have hc : ∀ n, s (n + 1) ^ p = s n := by
    intro n
    refine hu n _ ⟨?_, fun z hz => ?_⟩
    · rw [← pow_mul, ← pow_succ']; exact (hs (n + 1)).1
    · have hz' : z ^ p ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hz, one_pow]
      rw [← weil_level (one_le_ppow p n) (Fact.out : p.Prime).pos hz
        (by rw [← pow_succ]; exact (hs (n + 1)).1), ← pow_succ, (hs (n + 1)).2 z hz']
      have e : z = (p • τ n z).lev (n + 1) := by rw [lev_nsmul, Tate.lev_succ, hτ n z hz]
      conv_lhs => rw [e, hκ, map_nsmul, lev_nsmul, Tate.lev_succ]
  refine ⟨Tate.mk s fun n => ⟨(hs n).1, hc n⟩, fun t => Tate.ext fun n => ?_⟩
  rw [lev_weilT, Tate.lev_mk, (hs n).2 _ (t.lev_pow n), hκ]

/- English proof (translation)
Use `Tate.ext fun n => ?_` and prove the remaining obligations. Establish `hp` using `weil_perfect (A := A) (one_le_ppow p n) (fun _ => 1) (fun _ _ _ _ => (_root_.mul_one _).symm)`. Use `hp.unique ⟨s.lev_pow n, fun z hz => ?_⟩ ⟨(0 : TateA A p).lev_pow n, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `h1 n z hz`. Rewrite using `[← lev_weilT, hs, Tate.lev_zero]`.

Take `⟨t, rfl⟩` from `h1 n z hz`. Rewrite using `[← lev_weilT, map_zero, Tate.lev_zero]`.
-/
theorem eq_zero_of_weilT
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (s : TateA A p) (hs : ∀ t, weilT A p t s = 0) : s = 0 := by
  refine Tate.ext fun n => ?_
  have hp := weil_perfect (A := A) (one_le_ppow p n) (fun _ => 1) (fun _ _ _ _ => (_root_.mul_one _).symm)
  refine hp.unique ⟨s.lev_pow n, fun z hz => ?_⟩ ⟨(0 : TateA A p).lev_pow n, fun z hz => ?_⟩
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, hs, Tate.lev_zero]
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, map_zero, Tate.lev_zero]

end GlobalTheory.HTLat.TatePerfect

namespace GlobalTheory.HTLat

/- English proof (translation)
Introduce `p _ C _ _ _ A ε h1 h2`. Establish `hb : Function.Bijective (pairT A ε).flip`. Prove the components needed by the constructor for the conclusion. Use `(injective_iff_map_eq_zero _).2 fun s hs => TatePerfect.eq_zero_of_weilT A h1 s fun t => ?_` and prove the remaining obligations. Establish `: ε.equiv.symm (weilT A p t s) = 0` using `LinearMap.congr_fun hs t`.

Conclude with `ε.equiv.symm.map_eq_zero_iff.1 this`. Introduce `l`. Take `⟨s, hs⟩` from `TatePerfect.weilT_flip_surjective A h1 h2 (ε.equiv.toLinearMap ∘ₗ l)`. Use `⟨s, LinearMap.ext fun t => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ε.equiv.symm (weilT A p t s) = l t`.

Rewrite using `[hs]`. Conclude with `ε.equiv.symm_apply_apply _`. Use `⟨hb, ?_⟩` and prove the remaining obligations. Establish `e : ⇑(pairT A ε) = Neg.neg ∘ ⇑(pairT A ε).flip`. Use function extensionality and compare the values at `s`.

Conclude with `LinearMap.ext fun t => ((isAlt_pairT A ε).neg_eq t s).symm`. Rewrite using `[e]`. Conclude with `(Equiv.neg _).bijective.comp hb`.
-/
theorem bijective_pairT_of_lev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) (ε : Eps p C), (∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x) → (∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s) → Function.Bijective (pairT A ε).flip ∧ Function.Bijective (pairT A ε) := by
  intro p _ C _ _ _ A ε h1 h2
  have hb : Function.Bijective (pairT A ε).flip := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun s hs => TatePerfect.eq_zero_of_weilT A h1 s fun t => ?_
      have : ε.equiv.symm (weilT A p t s) = 0 := LinearMap.congr_fun hs t
      exact ε.equiv.symm.map_eq_zero_iff.1 this
    · intro l
      obtain ⟨s, hs⟩ := TatePerfect.weilT_flip_surjective A h1 h2 (ε.equiv.toLinearMap ∘ₗ l)
      refine ⟨s, LinearMap.ext fun t => ?_⟩
      change ε.equiv.symm (weilT A p t s) = l t
      rw [hs]
      exact ε.equiv.symm_apply_apply _
  refine ⟨hb, ?_⟩
  have e : ⇑(pairT A ε) = Neg.neg ∘ ⇑(pairT A ε).flip := by
    funext s
    exact LinearMap.ext fun t => ((isAlt_pairT A ε).neg_eq t s).symm
  rw [e]
  exact (Equiv.neg _).bijective.comp hb

end GlobalTheory.HTLat
