import Mathlib

namespace GlobalTheory.CoordinateBasisBounds

open NumberField

/- English proof (translation)
Establish `hx : IsAlgebraic ℤ x` using `IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ x)`. Take `⟨m, s, hm, h⟩` from `IsAlgebraic.exists_nsmul_eq (𝓞 E) hx`. Conclude with `⟨m, Nat.pos_of_ne_zero hm, s, by rw [← h, nsmul_eq_mul]⟩`.
-/
theorem nat_mul_integral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ o : 𝓞 E, (m : E) * x = algebraMap (𝓞 E) E o := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E) hx
  exact ⟨m, Nat.pos_of_ne_zero hm, s, by rw [← h, nsmul_eq_mul]⟩

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Establish `key : ∀ v ∈ S, ∃ m : ℕ, 0 < m ∧ ∀ i : Fin n, ∃ o : 𝓞 E, (m : E) * v i = algebraMap (𝓞 E) E o`. Introduce `v _`. Use `choose m hm o ho using fun i : Fin n => nat_mul_integral (v i)`. Use `⟨∏ i, m i, Finset.prod_pos (fun i _ => hm i), fun i => ?_⟩` and prove the remaining obligations.

Establish `hd : m i ∣ ∏ j, m j` using `Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Take `⟨k, hk⟩` from `hd`. Use `⟨(k : 𝓞 E) * o i, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, map_mul, ← ho i, map_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `choose! m hm hv using key`. Use `⟨∏ v ∈ S, m v, Finset.prod_pos (fun v hv' => hm v hv'), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← hS]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem v hvS`. Introduce `i`. Take `⟨o, ho⟩` from `hv v hvS i`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem m hvS`.

Use `⟨(k : 𝓞 E) * o, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, map_mul, ← ho, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => intro i; exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Take `⟨b, hb⟩` from `hy i`. Conclude with `⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]; ring⟩`.

Consider the case `smul c x _ hx`. Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Use `⟨c * a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coord_bound {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, ∀ i : Fin n, ∃ o : 𝓞 E, (N : E) * x i = algebraMap (𝓞 E) E o := by
  obtain ⟨S, hS⟩ := hL
  have key : ∀ v ∈ S, ∃ m : ℕ, 0 < m ∧ ∀ i : Fin n, ∃ o : 𝓞 E, (m : E) * v i = algebraMap (𝓞 E) E o := by
    intro v _
    choose m hm o ho using fun i : Fin n => nat_mul_integral (v i)
    refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm i), fun i => ?_⟩
    have hd : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hd
    refine ⟨(k : 𝓞 E) * o i, ?_⟩
    rw [hk, map_mul, ← ho i, map_natCast]; push_cast; ring
  classical
  choose! m hm hv using key
  refine ⟨∏ v ∈ S, m v, Finset.prod_pos (fun v hv' => hm v hv'), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem v hvS =>
    intro i
    obtain ⟨o, ho⟩ := hv v hvS i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hvS
    refine ⟨(k : 𝓞 E) * o, ?_⟩
    rw [hk, map_mul, ← ho, map_natCast]; push_cast; ring
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]; ring⟩
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    refine ⟨c * a, ?_⟩
    rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]; ring

/- English proof (translation)
Establish `hy : y ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hspan]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem v hv => exact ⟨1, one_pos, by simpa using hv⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Establish `e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y)`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul, smul_add]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)`. Consider the case `smul c x _ hx`.

Take `⟨d, hd, hdx⟩` from `hx`. Take `⟨m, hm, o, ho⟩` from `nat_mul_integral c`. Use `⟨m * d, Nat.mul_pos hm hd, ?_⟩` and prove the remaining obligations. Establish `e : ((m * d : ℕ) : E) • (c • x) = o • ((d : E) • x)`. Rewrite using `[← algebraMap_smul E o, ← ho, smul_smul, smul_smul]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `L.smul_mem o hdx`.
-/
theorem basis_bound {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hspan]; trivial
  induction hy using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, by simpa using hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul, smul_add]
      push_cast; ring_nf
    rw [e]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨m, hm, o, ho⟩ := nat_mul_integral c
    refine ⟨m * d, Nat.mul_pos hm hd, ?_⟩
    have e : ((m * d : ℕ) : E) • (c • x) = o • ((d : E) • x) := by
      rw [← algebraMap_smul E o, ← ho, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact L.smul_mem o hdx

/- English proof (translation)
Introduce `E _ _ n L hL hspan`. Take `⟨M, hM, hcoord⟩` from `GlobalTheory.CoordinateBasisBounds.coord_bound L hL`. Use `choose d hd hdL using fun j : Fin n => GlobalTheory.CoordinateBasisBounds.basis_bound L hspan (Pi.single j (1 : E))`. Use `⟨M * ∏ j, d j, Nat.mul_pos hM (Finset.prod_pos fun j _ => hd j), ?_, ?_⟩` and prove the remaining obligations. Introduce `j`.

Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem d (Finset.mem_univ j)`. Establish `e : ((M * ∏ j, d j : ℕ) : E) • Pi.single j (1 : E) = (M * k) • ((d j : E) • Pi.single j (1 : E))`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, smul_smul, hk]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[e]`. Conclude with `nsmul_mem (hdL j) _`. Introduce `x hx i`. Take `⟨o, ho⟩` from `hcoord x hx i`. Use `⟨((∏ j, d j : ℕ) : 𝓞 E) * o, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ← ho, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∃ (N : ℕ), (0 : ℕ) < N ∧ (∀ (j : Fin n), (↑N : E) • Pi.single j (1 : E) ∈ L) ∧ ∀ x ∈ L, ∀ (i : Fin n), ∃ (o : NumberField.RingOfIntegers E), (↑N : E) * x i = (Algebra.algebraMap (NumberField.RingOfIntegers E) E : NumberField.RingOfIntegers E → E) o := by
  intro E _ _ n L hL hspan
  obtain ⟨M, hM, hcoord⟩ := GlobalTheory.CoordinateBasisBounds.coord_bound L hL
  choose d hd hdL using fun j : Fin n => GlobalTheory.CoordinateBasisBounds.basis_bound L hspan (Pi.single j (1 : E))
  refine ⟨M * ∏ j, d j, Nat.mul_pos hM (Finset.prod_pos fun j _ => hd j), ?_, ?_⟩
  · intro j
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    have e : ((M * ∏ j, d j : ℕ) : E) • Pi.single j (1 : E) = (M * k) • ((d j : E) • Pi.single j (1 : E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hk]; push_cast; ring_nf
    rw [e]
    exact nsmul_mem (hdL j) _
  · intro x hx i
    obtain ⟨o, ho⟩ := hcoord x hx i
    refine ⟨((∏ j, d j : ℕ) : 𝓞 E) * o, ?_⟩
    rw [map_mul, ← ho, map_natCast]; push_cast; ring

end GlobalTheory.CoordinateBasisBounds
