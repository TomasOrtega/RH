import Development.EtaleCohomology.KummerTheory.AdicLimPfKer

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.CokPf

variable (l : ℕ) [Fact l.Prime]

def T (E : Spc) (n i : ℤ) (k : ℕ) : Submodule ℤ_[l] (Hl l E n i) :=
  LinearMap.ker (((l : ℤ_[l]) ^ k) • (LinearMap.id : Hl l E n i →ₗ[ℤ_[l]] Hl l E n i))

/- English proof (translation)
Introduce `a b hab x hx`. Simplify using `only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Rewrite using `[pow_add, mul_comm, mul_smul, hx, smul_zero]`.
-/
theorem T_mono (E : Spc) (n i : ℤ) : Monotone (T l E n i) := by
  intro a b hab x hx
  simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

/- English proof (translation)
Establish `: IsNoetherian ℤ_[l] (Hl l E n i)` using `inferInstance`. Take `⟨K, hK⟩` from `monotone_stabilizes_iff_noetherian.mpr this ⟨T l E n i, T_mono l E n i⟩`. Use `⟨K, fun m => ?_⟩` and prove the remaining obligations. Break down `le_total m K with h | h` into its components or cases. Conclude with `T_mono l E n i h`.

Conclude with `(hK m h).symm.le`.
-/
theorem stab (E : Spc) (n i : ℤ) [Module.Finite ℤ_[l] (Hl l E n i)] :
    ∃ K : ℕ, ∀ m, T l E n i m ≤ T l E n i K := by
  have : IsNoetherian ℤ_[l] (Hl l E n i) := inferInstance
  obtain ⟨K, hK⟩ := monotone_stabilizes_iff_noetherian.mpr this ⟨T l E n i, T_mono l E n i⟩
  refine ⟨K, fun m => ?_⟩
  rcases le_total m K with h | h
  · exact T_mono l E n i h
  · exact (hK m h).symm.le

/- English proof (translation)
Establish `hl : NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Take `⟨K, hK⟩` from `stab l E (n + 1) i`. Use `⟨l ^ K, pow_pos (Fact.out : l.Prime).pos K, fun k z => ?_⟩` and prove the remaining obligations. Take `⟨u, d, h⟩` from `hB k`. Set `D : Hl l E (n + 1) i` to `⟨fun a => d a n z, fun a => (h a n).2.2.2.2.1 z⟩`.

Establish `hD : D ∈ T l E (n + 1) i k`. Simplify using `only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a`.

Express the relevant statement in the definitionally equal form `(l ^ k) • d a n z = 0`. Rewrite using `[← map_nsmul, KerPf.smul_zero_of l E n i k k le_rfl, map_zero]`. Establish `hD'` using `hK k hD`. Simplify using `only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hD'`. Rewrite `hD'` using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`.

Establish `hz : ∀ a, d a n ((l ^ K) • z) = 0` using `fun a => by`. Use `congrArg (fun v : Hl l E (n + 1) i => v.1 a) hD'` as an intermediate fact. Express the relevant statement in the definitionally equal form `(l ^ K) • d a n z = 0 at this`. Rewrite using `[map_nsmul]`. Conclude with `this`.

Set `S : ℕ → Type 1` to `fun a => {w : Ht (l ^ (k + a)) E n i // red (l ^ (k + a)) (l ^ k) E n i w = (l ^ K) • z}`. Establish `hS : ∀ a, Finite (S a)` using `fun a => by have := hFin (k + a) n; exact Subtype.finite`. Establish `hN : ∀ a, Nonempty (S a)` using `fun a => by`. Take `⟨w, hw⟩` from `((h a n).2.1 ((l ^ K) • z)).1 (hz a)`. Conclude with `⟨⟨w, hw⟩⟩`.

Set `t : ∀ a, S (a + 1) → S a` to `fun a w => ⟨red (l ^ (k + (a + 1))) (l ^ (k + a)) E n i w.1, by`. Rewrite using `[(@hA (l ^ (k + (a + 1))) (l ^ (k + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ k) (pow_dvd_pow l (by omega)) n i w.1]`. Conclude with `w.2⟩`. Take `⟨s, hs⟩` from `KerPf.seqSec S t`. Set `x : Hl l E n i` to `⟨fun j => red (l ^ (k + j)) (l ^ j) E n i (s j).1, fun j => by`.

Establish `A` using `(@hA (l ^ (k + (j + 1))) (l ^ (j + 1)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j) (pow_dvd_pow l (by omega)) n i (s (j + 1)).1`. Establish `B` using `(@hA (l ^ (k + (j + 1))) (l ^ (k + j)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j) (pow_dvd_pow l (by omega)) n i (s (j + 1)).1`. Conclude with `A.trans (B.symm.trans (congrArg (fun w : S j => red (l ^ (k + j)) (l ^ j) E n i w.1) (hs j)))⟩`. Conclude with `⟨x, (s k).2⟩`.
-/
theorem cok (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) [Module.Finite ℤ_[l] (Hl l E (n + 1) i)] :
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨K, hK⟩ := stab l E (n + 1) i
  refine ⟨l ^ K, pow_pos (Fact.out : l.Prime).pos K, fun k z => ?_⟩
  obtain ⟨u, d, h⟩ := hB k
  let D : Hl l E (n + 1) i := ⟨fun a => d a n z, fun a => (h a n).2.2.2.2.1 z⟩
  have hD : D ∈ T l E (n + 1) i k := by
    simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext; funext a
    change (l ^ k) • d a n z = 0
    rw [← map_nsmul, KerPf.smul_zero_of l E n i k k le_rfl, map_zero]
  have hD' := hK k hD
  simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hD'
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hD'
  have hz : ∀ a, d a n ((l ^ K) • z) = 0 := fun a => by
    have := congrArg (fun v : Hl l E (n + 1) i => v.1 a) hD'
    change (l ^ K) • d a n z = 0 at this
    rw [map_nsmul]; exact this
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ (k + a)) E n i // red (l ^ (k + a)) (l ^ k) E n i w = (l ^ K) • z}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin (k + a) n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).2.1 ((l ^ K) • z)).1 (hz a)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (k + (a + 1))) (l ^ (k + a)) E n i w.1, by
    rw [(@hA (l ^ (k + (a + 1))) (l ^ (k + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ k)
      (pow_dvd_pow l (by omega)) n i w.1]
    exact w.2⟩
  obtain ⟨s, hs⟩ := KerPf.seqSec S t
  let x : Hl l E n i := ⟨fun j => red (l ^ (k + j)) (l ^ j) E n i (s j).1, fun j => by
    have A := (@hA (l ^ (k + (j + 1))) (l ^ (j + 1)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j)
      (pow_dvd_pow l (by omega)) n i (s (j + 1)).1
    have B := (@hA (l ^ (k + (j + 1))) (l ^ (k + j)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j)
      (pow_dvd_pow l (by omega)) n i (s (j + 1)).1
    exact A.trans (B.symm.trans (congrArg (fun w : S j => red (l ^ (k + j)) (l ^ j) E n i w.1) (hs j)))⟩
  exact ⟨x, (s k).2⟩

end LateralTheory.KummerTheory.CokPf

namespace LateralTheory.KummerTheory

/- English proof (translation)
Introduce `hA l _ E i hB hFin n _` and use `CokPf.cok l hA E i hB hFin n`.
-/
theorem AdicCok_holds : AdicCok := fun hA l _ E i hB hFin n _ => CokPf.cok l hA E i hB hFin n

end LateralTheory.KummerTheory
