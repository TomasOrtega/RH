import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def qcOm (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [shapeDeg, qcOm, Pi.add_apply, Finset.card_filter]`. Rewrite using `[Fin.sum_univ_succ]`.
-/
theorem qc_shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) :
    (shapeDeg sz : Fin n → ℕ) = qcOm n (sz 0) + shapeDeg (fun k : Fin K => sz k.succ) := by
  funext t
  simp only [shapeDeg, qcOm, Pi.add_apply, Finset.card_filter]
  rw [Fin.sum_univ_succ]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `[shapeDeg]`.
-/
theorem qc_shapeDeg_zero {n : ℕ} (sz : Fin 0 → ℕ) : (shapeDeg sz : Fin n → ℕ) = 0 := by
  funext t
  simp [shapeDeg]

/- English proof (translation)
Establish `h` using `bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)`. Establish `h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs`. Simplify using `[bideterminant]`. Establish `h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = qcOm n s`. Use function extensionality and compare the values at `t`.

Simplify using `only [shapeDeg, qcOm, Finset.card_filter]`. Simplify using the standard rewrite rules. Rewrite `h` using `[h1, h2]`. Conclude with `h`.
-/
theorem qc_initMinor_mem (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (qcOm n s) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = qcOm n s := by
    funext t
    simp only [shapeDeg, qcOm, Finset.card_filter]
    simp
  rw [h1, h2] at h
  exact h

/- English proof (translation)
Unfold `bideterminant`. Rewrite using `[Fin.prod_univ_succ]`.
-/
theorem qc_bidet_succ (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin (K + 1) → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    bideterminant R sz hsz I = initMinor R (I 0) (hsz 0) *
      bideterminant R (fun k : Fin K => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) := by
  unfold bideterminant
  rw [Fin.prod_univ_succ]

/- English proof (translation)
Simplify using `[bideterminant]`.
-/
theorem qc_bidet_zero (R : Type) [CommRing R] {r n : ℕ} (sz : Fin 0 → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : bideterminant R sz hsz I = 1 := by
  simp [bideterminant]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, zero_smul]`. Conclude with `one_mem_dualWeyl R r n`. Consider the case `succ k ih => rw [pow_succ, succ_nsmul]`. Conclude with `dualWeyl_mul R r n _ _ ih hy`.
-/
theorem qc_pow_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (y : MvPolynomial (Fin r × Fin n) R)
    (hy : y ∈ dualWeyl R r n ν) (k : ℕ) : y ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_dualWeyl R r n
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul R r n _ _ ih hy

/- English proof (translation)
Substitute `h` using the available equality. Establish `hid : I = id`. Conclude with `(StrictMono.range_inj hI strictMono_id).1 (by rw [Set.range_id]; exact (Finite.injective_iff_surjective.1 hI.injective).range_eq)`. Substitute `hid` using the available equality. Both sides reduce to the same expression.
-/
theorem qc_full_minor (A : Type) [CommRing A] (r s : ℕ) (hs : s ≤ r) (I : Fin s → Fin r) (hI : StrictMono I)
    (h : s = r) : initMinor A I hs = detY A r := by
  subst h
  have hid : I = id := by
    exact (StrictMono.range_inj hI strictMono_id).1
      (by rw [Set.range_id]; exact (Finite.injective_iff_surjective.1 hI.injective).range_eq)
  subst hid
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Unfold `initMinor`. Conclude with `Matrix.det_isEmpty`.
-/
theorem qc_empty_minor (A : Type) [CommRing A] {r n : ℕ} (s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r) (h : s = 0) :
    initMinor A I hs = 1 := by
  subst h
  unfold initMinor
  exact Matrix.det_isEmpty

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `[qcOm]`.
-/
theorem qcOm_zero (n : ℕ) : qcOm n 0 = 0 := by
  funext t
  simp [qcOm]

/- English proof (translation)
Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Introduce `sz hsz I _`. Conclude with `⟨0, 0, 1, by intro t; rw [qc_shapeDeg_zero]; rfl, fun _ _ => rfl, one_mem_dualWeyl A r r, by rw [qc_bidet_zero, pow_zero, one_mul]⟩`.

Consider the case `succ K ih`. Introduce `sz hsz I hI`. Take `⟨n, γ, u₀, h1, h2, h3, h4⟩` from `ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) (fun k => hI k.succ)`. Distinguish the cases in `hr : sz 0 = r`. Use `⟨n + 1, γ, u₀, ?_, h2, h3, ?_⟩` and prove the remaining obligations.

Introduce `t`. Rewrite using `[qc_shapeDeg_succ, Pi.add_apply, h1 t]`. Establish `: qcOm r (sz 0) t = 1`. Unfold `qcOm`. Rewrite using `[if_pos (by rw [hr]; exact t.isLt)]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[qc_bidet_succ, h4, qc_full_minor A r _ (hsz 0) (I 0) (hI 0) hr]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨n, qcOm r (sz 0) + γ, initMinor A (I 0) (hsz 0) * u₀, ?_, ?_, dualWeyl_mul A r r _ _ (qc_initMinor_mem A (I 0) (hsz 0)) h3, ?_⟩` and prove the remaining obligations. Introduce `t`.

Rewrite using `[qc_shapeDeg_succ, Pi.add_apply, Pi.add_apply, h1 t]`. Use linear arithmetic over natural numbers and integers. Introduce `t ht`. Rewrite using `[Pi.add_apply, h2 t ht, add_zero]`. Unfold `qcOm`.

Rewrite using `[if_neg]`. Use `hsz 0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[qc_bidet_succ, h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qc_detDiv_bidet (A : Type) [CommRing A] (r : ℕ) : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r)
    (I : ∀ k, Fin (sz k) → Fin r), (∀ k, StrictMono (I k)) →
    ∃ (n : ℕ) (γ : Fin r → ℕ) (u₀ : MvPolynomial (Fin r × Fin r) A), (∀ t, shapeDeg sz t = γ t + n) ∧
      (∀ t : Fin r, t.val + 1 = r → γ t = 0) ∧ u₀ ∈ dualWeyl A r r γ ∧ bideterminant A sz hsz I = detY A r ^ n * u₀ := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I _
    exact ⟨0, 0, 1, by intro t; rw [qc_shapeDeg_zero]; rfl, fun _ _ => rfl, one_mem_dualWeyl A r r,
      by rw [qc_bidet_zero, pow_zero, one_mul]⟩
  | succ K ih =>
    intro sz hsz I hI
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ :=
      ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) (fun k => hI k.succ)
    by_cases hr : sz 0 = r
    · refine ⟨n + 1, γ, u₀, ?_, h2, h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, h1 t]
        have : qcOm r (sz 0) t = 1 := by
          unfold qcOm
          rw [if_pos (by rw [hr]; exact t.isLt)]
        omega
      · rw [qc_bidet_succ, h4, qc_full_minor A r _ (hsz 0) (I 0) (hI 0) hr]
        ring
    · refine ⟨n, qcOm r (sz 0) + γ, initMinor A (I 0) (hsz 0) * u₀, ?_, ?_,
        dualWeyl_mul A r r _ _ (qc_initMinor_mem A (I 0) (hsz 0)) h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, Pi.add_apply, h1 t]
        omega
      · intro t ht
        rw [Pi.add_apply, h2 t ht, add_zero]
        unfold qcOm
        rw [if_neg]
        have := hsz 0
        omega
      · rw [qc_bidet_succ, h4]
        ring

/- English proof (translation)
Introduce `A _ _ r Q β hr hβ u hu`. Take `⟨b, ⟨-, hspan, -⟩, hb⟩` from `sSBasis A r r (fun j => β j + Q)`. Rewrite `hu` using `[← hspan]`. Use `Submodule.span_induction (p := fun u _ => ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`.

Take `⟨-, -, K, sz, hsz, I, hsh, hI, hbm⟩` from `hb m`. Take `⟨n, γ, u₀, h1, h2, h3, h4⟩` from `qc_detDiv_bidet A r K sz hsz I hI`. Establish `h1' : ∀ t, β t + Q = γ t + n`. Introduce `t`. Use `h1 t` as an intermediate fact.

Rewrite `this` using `[hsh]`. Then use the resulting hypothesis. Establish `hl : γ ⟨r - 1, by omega⟩ = 0` using `h2 _ (by show r - 1 + 1 = r; omega)`. Establish `hn : Q ≤ n`. Use `h1' ⟨r - 1, by omega⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨detY A r ^ (n - Q) * u₀, ?_, ?_⟩` and prove the remaining obligations. Establish `hd : detY A r ∈ dualWeyl A r r (qcOm r r)`. Rewrite using `[← qc_full_minor A r r le_rfl id strictMono_id rfl]`. Conclude with `qc_initMinor_mem A id le_rfl`. Establish `h5` using `dualWeyl_mul A r r _ _ (qc_pow_mem A r r _ _ hd (n - Q)) h3`.

Establish `e : (n - Q) • qcOm r r + γ = β`. Use function extensionality and compare the values at `t`. Use `h1' t` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.smul_apply, qcOm, t.isLt, if_true, smul_eq_mul, mul_one]`. Use linear arithmetic over natural numbers and integers.

Rewrite `h5` using `[e]`. Then use the resulting hypothesis. Rewrite using `[hbm, h4, ← mul_assoc, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩`.

Introduce and unpack `x y _ _ ⟨a, ha, rfl⟩ ⟨b', hb', rfl⟩`. Conclude with `⟨a + b', Submodule.add_mem _ ha hb', by rw [mul_add]⟩`. Introduce and unpack `c x _ ⟨a, ha, rfl⟩`. Conclude with `⟨c • a, Submodule.smul_mem _ _ ha, by rw [mul_smul_comm]⟩`.
-/
theorem detDivP : DetDivP := by
  intro A _ _ r Q β hr hβ u hu
  obtain ⟨b, ⟨-, hspan, -⟩, hb⟩ := sSBasis A r r (fun j => β j + Q)
  rw [← hspan] at hu
  refine Submodule.span_induction (p := fun u _ => ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨m, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hsh, hI, hbm⟩ := hb m
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ := qc_detDiv_bidet A r K sz hsz I hI
    have h1' : ∀ t, β t + Q = γ t + n := by
      intro t
      have := h1 t
      rwa [hsh] at this
    have hl : γ ⟨r - 1, by omega⟩ = 0 := h2 _ (by show r - 1 + 1 = r; omega)
    have hn : Q ≤ n := by
      have := h1' ⟨r - 1, by omega⟩
      omega
    refine ⟨detY A r ^ (n - Q) * u₀, ?_, ?_⟩
    · have hd : detY A r ∈ dualWeyl A r r (qcOm r r) := by
        rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
        exact qc_initMinor_mem A id le_rfl
      have h5 := dualWeyl_mul A r r _ _ (qc_pow_mem A r r _ _ hd (n - Q)) h3
      have e : (n - Q) • qcOm r r + γ = β := by
        funext t
        have := h1' t
        simp only [Pi.add_apply, Pi.smul_apply, qcOm, t.isLt, if_true, smul_eq_mul, mul_one]
        omega
      rwa [e] at h5
    · rw [hbm, h4, ← mul_assoc, ← pow_add]
      congr 2
      omega
  · exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
  · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b', hb', rfl⟩
    exact ⟨a + b', Submodule.add_mem _ ha hb', by rw [mul_add]⟩
  · rintro c x _ ⟨a, ha, rfl⟩
    exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [mul_smul_comm]⟩

end Formalism.MainNotions.flipOneThree.Pf

end
