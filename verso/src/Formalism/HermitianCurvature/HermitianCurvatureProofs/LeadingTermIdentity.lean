import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlMonoConst

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Establish `hm : StrictMono τ` using `fun a b hab => Fin.lt_def.mpr (h hab)`. Establish `hinv : StrictMono τ.symm`. Introduce `a b hab`. Assume the negation of the conclusion as `hc`. Establish `h'` using `hm.monotone (not_lt.mp hc)`.

Rewrite `h'` using `[Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Conclude with `absurd hab (not_lt.mpr h')`. Use `Equiv.ext fun l => ?_` and prove the remaining obligations. Establish `h1 : l ≤ τ l` using `hm.le_apply`. Establish `h2 : l ≤ τ.symm l` using `hinv.le_apply`.

Establish `h3` using `hm.monotone h2`. Rewrite `h3` using `[Equiv.apply_symm_apply]`. Rewrite using `[Equiv.Perm.one_apply]`. Conclude with `le_antisymm h3 h1`.
-/
theorem perm_id_of_mono {m : ℕ} (τ : Equiv.Perm (Fin m)) (h : StrictMono (fun l => (τ l).val)) : τ = 1 := by
  have hm : StrictMono τ := fun a b hab => Fin.lt_def.mpr (h hab)
  have hinv : StrictMono τ.symm := by
    intro a b hab
    by_contra hc
    have h' := hm.monotone (not_lt.mp hc)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
    exact absurd hab (not_lt.mpr h')
  refine Equiv.ext fun l => ?_
  have h1 : l ≤ τ l := hm.le_apply
  have h2 : l ≤ τ.symm l := hinv.le_apply
  have h3 := hm.monotone h2
  rw [Equiv.apply_symm_apply] at h3
  rw [Equiv.Perm.one_apply]
  exact le_antisymm h3 h1

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single 1]`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, σ k ≠ k := by`. Assume the negation of the conclusion as `H`.

Conclude with `hσ (Equiv.ext fun l => by simpa using not_not.mp (fun h => H ⟨l, h⟩))`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (ha.ne hk)), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem top_self {m N : ℕ} (a : Fin m → Fin N) (ha : Function.Injective a) :
    (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = a k then (1 : ℂ) else 0)) = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra H
      exact hσ (Equiv.ext fun l => by simpa using not_not.mp (fun h => H ⟨l, h⟩))
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (ha.ne hk)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `k`. Assume the negation of the conclusion as `hk`. Conclude with `h (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk))`.
-/
theorem prod_ne_zero_imp {m N : ℕ} (a b : Fin m → Fin N) (σ : Equiv.Perm (Fin m))
    (h : ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0) ≠ 0) : ∀ k, a (σ k) = b k := by
  intro k
  by_contra hk
  exact h (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk))

/- English proof (translation)
Establish `hP : PolyLe m (fun u => ∑ c, if P c then algebraMap ℂ A (d c) * (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0)`. Use `pl_sum Finset.univ (fun c u => if P c then algebraMap ℂ A (d c) * (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : P c`. Simplify using `only [hc, if_true]`. Conclude with `pl_lmul _ (qminor_poly E (fa c) (fb c) s0)`.

Simplify using `only [hc, if_false]`. Conclude with `pl_zero m`. Take `⟨C, hC⟩` from `hP`. Use `⟨C, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← hC u]`.

Use `beta_reduce`. Establish `hsplit : ∀ c, (if P c then algebraMap ℂ A (d c) * (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) = (if P c then d c • qminor E (fa c) (fb c) (u + s0) …`. Introduce `c`. Use `split_ifs`. Rewrite using `[mul_sub, Algebra.smul_def, ← map_mul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hsecond : (∑ c, if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) = algebraMap ℂ A (u ^ m * d c0)`. Rewrite using `[Finset.sum_eq_single c0]`.

Rewrite using `[if_pos h0, h1, mul_one]`. Introduce `c _ hc split_ifs with hPc`. Rewrite using `[hz c hPc hc, mul_zero, mul_zero, map_zero]`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_sub_distrib, hsecond]`. Normalize the expressions using the abelian group laws.
-/
private theorem leading_term_identity_lemma {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (P : (Fin m → Fin n) → Prop) [DecidablePred P] (d : (Fin m → Fin n) → ℂ)
    (fa fb : (Fin m → Fin n) → Fin m → Fin n) (s0 : ℂ) (c0 : Fin m → Fin n) (h0 : P c0)
    (h1 : ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c0 (σ k) = fb c0 k then (1 : ℂ) else 0) = 1)
    (hz : ∀ c, P c → c ≠ c0 → ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0) = 0) :
    ∃ C : Fin m → A, ∀ u : ℂ, (∑ c, if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) =
      algebraMap ℂ A (u ^ m * d c0) + ∑ l : Fin m, algebraMap ℂ A (u ^ (l : ℕ)) * C l := by
  have hP : PolyLe m (fun u => ∑ c, if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    refine pl_sum Finset.univ (fun c u => if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0)
      fun c _ => ?_
    by_cases hc : P c
    · simp only [hc, if_true]
      exact pl_lmul _ (qminor_poly E (fa c) (fb c) s0)
    · simp only [hc, if_false]
      exact pl_zero m
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun u => ?_⟩
  rw [← hC u]
  beta_reduce
  have hsplit : ∀ c, (if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      (if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) -
        (if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    intro c
    split_ifs
    · rw [mul_sub, Algebra.smul_def, ← map_mul]
      congr 2
      ring
    · simp
  have hsecond : (∑ c, if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      algebraMap ℂ A (u ^ m * d c0) := by
    rw [Finset.sum_eq_single c0]
    · rw [if_pos h0, h1, mul_one]
    · intro c _ hc
      split_ifs with hPc
      · rw [hz c hPc hc, mul_zero, mul_zero, map_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_sub_distrib, hsecond]
  abel

/- English proof (translation)
Introduce `A _ _ k r E xi m hm`. Establish `hxv : ∀ l, (xR k r m hm l).val = l.val` using `fun l => rfl`. Establish `hxinj : Function.Injective (xR k r m hm)` using `fun a b h => Fin.ext (by rw [← hxv a, ← hxv b, h])`. Establish `hxm : StrictMono (xR k r m hm)` using `fun a b hab => Fin.lt_def.mpr (by rw [hxv, hxv]; exact hab)`. Take `⟨C, hC⟩` from `leading_term_identity_lemma E (fun c => StrictMono c) (fun c => (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det) (fun _ => xR k r m hm) id 0 (xR k r m hm) hxm (top_self _ hxinj) (by`.

Introduce `c hc hne`. Assume the negation of the conclusion as `hs`. Take `⟨σ, -, hσ⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hs`. Establish `heq` using `prod_ne_zero_imp (xR k r m hm) c σ (right_ne_zero_of_mul hσ)`. Establish `hσm : StrictMono (fun l => (σ l).val)`.

Introduce `a b hab`. Establish `h1 : c a < c b` using `hc hab`. Rewrite `h1` using `[← heq a, ← heq b, Fin.lt_def, hxv, hxv]`. Conclude with `h1`. Establish `hσ1` using `perm_id_of_mono σ hσm`.

Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `l`. Rewrite using `[← heq l, hσ1]`. Use the proof step `rfl)`. Use `⟨C, fun u => ?_⟩` and prove the remaining obligations.

Establish `h` using `hC u`. Simplify using `only [id, add_zero] at h`. Unfold `AAx`. Conclude with `h`.
-/
theorem leading_term_identity : LeadAA := by
  intro A _ _ k r E xi m hm
  classical
  have hxv : ∀ l, (xR k r m hm l).val = l.val := fun l => rfl
  have hxinj : Function.Injective (xR k r m hm) := fun a b h => Fin.ext (by rw [← hxv a, ← hxv b, h])
  have hxm : StrictMono (xR k r m hm) := fun a b hab => Fin.lt_def.mpr (by rw [hxv, hxv]; exact hab)
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun c => StrictMono c)
    (fun c => (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det)
    (fun _ => xR k r m hm) id 0 (xR k r m hm) hxm (top_self _ hxinj) (by
      intro c hc hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp (xR k r m hm) c σ (right_ne_zero_of_mul hσ)
      have hσm : StrictMono (fun l => (σ l).val) := by
        intro a b hab
        have h1 : c a < c b := hc hab
        rw [← heq a, ← heq b, Fin.lt_def, hxv, hxv] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ hσm
      apply hne
      funext l
      rw [← heq l, hσ1]
      rfl)
  refine ⟨C, fun u => ?_⟩
  have h := hC u
  simp only [id, add_zero] at h
  unfold AAx
  exact h

/- English proof (translation)
Introduce `A _ _ k r E y m hm`. Establish `hkey : ∀ l, keyS k r (sR k r m hm l) = l.val`. Introduce `l`. Establish `hl` using `l.isLt`. Establish `hv : (sR k r m hm l).val = 2 * r + k - l.val` using `rfl`.

Unfold `keyS`. Rewrite using `[hv]`. Use `split_ifs with h`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Establish `hsinj : Function.Injective (sR k r m hm)` using `fun a b h => Fin.ext (by rw [← hkey a, ← hkey b, h])`. Establish `hsm : StrictMono (fun l => keyS k r (sR k r m hm l))` using `fun a b hab => by`. Simplify using `only [hkey]`. Conclude with `hab`. Take `⟨C, hC⟩` from `leading_term_identity_lemma E (fun B => StrictMono (fun l => keyS k r (B l))) (fun B => (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) (B l)).det) id (fun _ => sR k r m hm) ((m : ℂ) - 1) (sR k r m hm) hsm (top_self _ hsinj) (by`.

Introduce `B hB hne`. Assume the negation of the conclusion as `hs`. Take `⟨σ, -, hσ⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hs`. Establish `heq` using `prod_ne_zero_imp B (sR k r m hm) σ (right_ne_zero_of_mul hσ)`. Establish `hB' : ∀ l, B l = sR k r m hm (σ.symm l)`.

Introduce `l`. Use `heq (σ.symm l)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hσm : StrictMono (fun l => (σ.symm l).val)`. Introduce `a b hab`.

Establish `h1` using `hB hab`. Simplify using `only [hB', hkey] at h1`. Conclude with `h1`. Establish `hσ1` using `perm_id_of_mono σ.symm hσm`. Apply `hne` to reduce the goal to its premises.

Use function extensionality and compare the values at `l`. Rewrite using `[hB' l, hσ1]`. Use the proof step `rfl)`. Use `⟨C, fun ell => ?_⟩` and prove the remaining obligations. Establish `h` using `hC ell`.

Simplify using `only [id] at h`. Unfold `AAv`. Rewrite using `[show ell + (m : ℂ) - 1 = ell + ((m : ℂ) - 1) by ring]`. Conclude with `h`.
-/
theorem leading_term_vector_identity : LeadAAv := by
  intro A _ _ k r E y m hm
  classical
  have hkey : ∀ l, keyS k r (sR k r m hm l) = l.val := by
    intro l
    have hl := l.isLt
    have hv : (sR k r m hm l).val = 2 * r + k - l.val := rfl
    unfold keyS
    rw [hv]
    split_ifs with h
    · omega
    · omega
  have hsinj : Function.Injective (sR k r m hm) := fun a b h =>
    Fin.ext (by rw [← hkey a, ← hkey b, h])
  have hsm : StrictMono (fun l => keyS k r (sR k r m hm l)) := fun a b hab => by
    simp only [hkey]
    exact hab
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun B => StrictMono (fun l => keyS k r (B l)))
    (fun B => (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) (B l)).det)
    id (fun _ => sR k r m hm) ((m : ℂ) - 1) (sR k r m hm) hsm (top_self _ hsinj) (by
      intro B hB hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp B (sR k r m hm) σ (right_ne_zero_of_mul hσ)
      have hB' : ∀ l, B l = sR k r m hm (σ.symm l) := by
        intro l
        have := heq (σ.symm l)
        rwa [Equiv.apply_symm_apply] at this
      have hσm : StrictMono (fun l => (σ.symm l).val) := by
        intro a b hab
        have h1 := hB hab
        simp only [hB', hkey] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ.symm hσm
      apply hne
      funext l
      rw [hB' l, hσ1]
      rfl)
  refine ⟨C, fun ell => ?_⟩
  have h := hC ell
  simp only [id] at h
  unfold AAv
  rw [show ell + (m : ℂ) - 1 = ell + ((m : ℂ) - 1) by ring]
  exact h

end Formalism.FourierDecayAlt.P.SignAntidiagonal
