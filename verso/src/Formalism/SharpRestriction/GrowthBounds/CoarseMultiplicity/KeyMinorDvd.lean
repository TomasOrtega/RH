import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.SelfDualLatticesOneOrbit
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Apply `(Ideal.Quotient.eq_zero_iff_dvd w _).mp` to reduce the goal to its premises. Use `set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ`. Establish `hw0 : φ w = 0` using `(Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl`. Establish `hp0 : φ (p : A) = 0` using `by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]`. Establish `hu0 : ∀ b, b ≠ 0 → φ (u b) = 0` using `fun b hb => (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hu b hb)`.

Establish `hv0' : φ (v 0) = 0` using `(Ideal.Quotient.eq_zero_iff_dvd w _).mpr hv0`. Establish `hrow : ∀ a, φ (∑ b, u b * M b a) = φ (u 0) * φ (M 0 a)`. Introduce `a`. Establish `hz : ∀ i : Fin k, φ (u i.succ) = 0` using `fun i => hu0 _ (Fin.succ_ne_zero _)`. Rewrite using `[map_sum, Fin.sum_univ_succ, map_mul]`.

Simplify using `[hz]`. Establish `hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a)`. Introduce `a`. Take `⟨T, hT⟩` from `hMN 0 a`. Rewrite using `[← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]`.

Establish `hδ : ∀ b', ∑ a, φ (N' 0 a) * φ (N a b') = if (0 : Fin (k + 1)) = b' then 1 else 0`. Introduce `b'`. Establish `h` using `congrArg φ (hinv 0 b')`. Rewrite `h` using `[map_sum]`. Rewrite `h` using `[map_mul]`.

Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[map_mul, map_pow, hrow, mul_pow, hpow, map_sum, map_mul]`. Establish `e : ∑ a, φ (u 0) ^ (p ^ e) * φ (N' 0 a) * ∑ b', φ (v b') * φ (N a b') = φ (u 0) ^ (p ^ e) * ∑ b', φ (v b') * ∑ a, φ (N' 0 a) * φ (N a b')`.

Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Repeatedly rewrite using `[hδ]`. Simplify using `[hv0']`.
-/
theorem key_pow_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u v : Fin (k + 1) → A) (M N' N : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hv0 : w ∣ v 0) :
    w ∣ ∑ a, (∑ b, u b * M b a) ^ (p ^ e) * (∑ b', v b' * N a b') := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hu0 : ∀ b, b ≠ 0 → φ (u b) = 0 := fun b hb => (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hu b hb)
  have hv0' : φ (v 0) = 0 := (Ideal.Quotient.eq_zero_iff_dvd w _).mpr hv0
  have hrow : ∀ a, φ (∑ b, u b * M b a) = φ (u 0) * φ (M 0 a) := by
    intro a
    have hz : ∀ i : Fin k, φ (u i.succ) = 0 := fun i => hu0 _ (Fin.succ_ne_zero _)
    rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]
  have hδ : ∀ b', ∑ a, φ (N' 0 a) * φ (N a b') = if (0 : Fin (k + 1)) = b' then 1 else 0 := by
    intro b'
    have h := congrArg φ (hinv 0 b')
    rw [map_sum] at h
    simp_rw [map_mul] at h
    rw [h]
    split_ifs <;> simp
  rw [map_sum]
  simp_rw [map_mul, map_pow, hrow, mul_pow, hpow, map_sum, map_mul]
  have e : ∑ a, φ (u 0) ^ (p ^ e) * φ (N' 0 a) * ∑ b', φ (v b') * φ (N a b') =
      φ (u 0) ^ (p ^ e) * ∑ b', φ (v b') * ∑ a, φ (N' 0 a) * φ (N a b') := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  simp_rw [hδ]
  simp [hv0']

/- English proof (translation)
Unfold `sigPow`. Rewrite using `[Int.emod_emod]`.
-/
theorem sigPow_mod' (p f : ℕ) [Fact p.Prime] (s : ℤ) : sigPow p f s = sigPow p f (s % (f : ℤ)) := by
  unfold sigPow
  rw [Int.emod_emod]

/- English proof (translation)
Simplify using `only [segPos, posAdd]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem segPos_val (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    (((segPos X.TT j i).val : ℕ) : ℤ) = (((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get i : ℤ)) % (X.n' : ℤ) := by
  simp only [segPos, posAdd]
  push_cast
  rfl

/- English proof (translation)
Establish `hp : X.p.Prime` using `hD.1`. Establish `hf : 1 ≤ X.n'` using `by have := hD.2.2.1; omega`. Use `set d := (segDists X.TT j).get i with hd`. Use `set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0`. Use `set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1`.

Set `xs : X.TT × Bool` to `(topStart X j, true)`. Set `y : X.TT × Bool` to `(topOdd X j i, false)`. Set `A` to `MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O`. Set `u : Fin (X.m + 1) → A` to `fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)`. Set `v : Fin (X.m + 1) → A` to `fun b => C (dW O S.w (hhLetters X.TT) 1 y b) * MvPolynomial.X (y, b)`.

Set `M : Fin (X.m + 1) → Fin (X.m + 1) → A` to `fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))`. Set `N' : Fin (X.m + 1) → Fin (X.m + 1) → A` to `fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))`. Set `N : Fin (X.m + 1) → Fin (X.m + 1) → A` to `fun a b => C (psiO X.p X.n' O s1 (g a b))`. Establish `hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) = MvPolynomial.map (algebraMap O (KK O)) (∑ a, (∑ b, u b * M b a) ^ (X.p ^ d) * (∑ b', v b' * N a b'))`. Unfold `kSkey`.

Simplify using `only [map_sum, map_mul, map_pow]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs a rfl, liftSubst_X_cov X.p X.n' O S.w (hhLetters X.TT) 1 g y a rfl]`. Simplify using `only [u, v, M, N, map_sum, map_mul, map_C, map_X, sigMat_apply]`. Both sides reduce to the same expression.

Establish `hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T`. Introduce `b a`. Take `⟨τ, hτ⟩` from `frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)`. Establish `e1 : (s0 + d - s0).toNat = d` using `by omega`. Rewrite `hτ` using `[e1]`.

Establish `e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1`. Rewrite using `[sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]`. Use `congr 1`. Simplify using `only [hs0, hs1, topStart, topOdd]`. Rewrite using `[segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]`.

Rewrite `hτ` using `[e2]`. Use `⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩` and prove the remaining obligations. Use `congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ` as an intermediate fact. Simplify using `only [map_sub, map_pow, map_mul, map_natCast] at this`. Simplify using `only [M, N', psiO, RingHom.comp_apply]`.

Take the linear combination `this`. Establish `hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0`. Introduce `b b'`. Establish `h1 : ∑ a, N' b a * N a b' = C (psiO X.p X.n' O s1 ((g⁻¹ * g) b b'))`. Simplify using `only [N', N, ← map_mul, ← map_sum, Matrix.mul_apply]`.

Rewrite using `[h1, Matrix.nonsing_inv_mul g hg, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hw : (C S.w : A) ^ 2 = (X.p : A)` using `by rw [← map_pow, hsq, map_natCast]`. Establish `hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b`. Introduce `b hb`.

Establish `: dW O S.w (hhLetters X.TT) 1 xs b = S.w`. Establish `: 1 ≤ (b : ℕ)` using `Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))`. Simplify using `[dW, hhLetters, xs, this]`. Conclude with `⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩`. Establish `hv0 : (C S.w : A) ∣ v 0`.

Establish `: dW O S.w (hhLetters X.TT) 1 y (0 : Fin (X.m + 1)) = S.w` using `by simp [dW, hhLetters, y]`. Conclude with `⟨MvPolynomial.X (y, 0), by simp only [v, this]⟩`. Take `⟨Q, hQ⟩` from `key_pow_dvd X.p hp (C S.w : A) hw X.m d u v M N' N hMN hinv hu hv0`. Unfold `InWjRg`. Rewrite using `[hlift, hQ]`.

Introduce `m`. Use `⟨Q.coeff m, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_C_mul, pow_one, map_mul]`.
-/
theorem kS_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let y : X.TT × Bool := (topOdd X j i, false)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let v : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 y b) * MvPolynomial.X (y, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  let N : Fin (X.m + 1) → Fin (X.m + 1) → A := fun a b => C (psiO X.p X.n' O s1 (g a b))

  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) =
      MvPolynomial.map (algebraMap O (KK O)) (∑ a, (∑ b, u b * M b a) ^ (X.p ^ d) * (∑ b', v b' * N a b')) := by
    unfold kSkey
    simp only [map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs a rfl,
      liftSubst_X_cov X.p X.n' O S.w (hhLetters X.TT) 1 g y a rfl]
    simp only [u, v, M, N, map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl

  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this

  have hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0 := by
    intro b b'
    have h1 : ∑ a, N' b a * N a b' = C (psiO X.p X.n' O s1 ((g⁻¹ * g) b b')) := by
      simp only [N', N, ← map_mul, ← map_sum, Matrix.mul_apply]
    rw [h1, Matrix.nonsing_inv_mul g hg, Matrix.one_apply]
    split_ifs <;> simp
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hv0 : (C S.w : A) ∣ v 0 := by
    have : dW O S.w (hhLetters X.TT) 1 y (0 : Fin (X.m + 1)) = S.w := by simp [dW, hhLetters, y]
    exact ⟨MvPolynomial.X (y, 0), by simp only [v, this]⟩
  obtain ⟨Q, hQ⟩ := key_pow_dvd X.p hp (C S.w : A) hw X.m d u v M N' N hMN hinv hu hv0
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

/- English proof (translation)
Apply `(Ideal.Quotient.eq_zero_iff_dvd w _).mp` to reduce the goal to its premises. Use `set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ`. Establish `hw0 : φ w = 0` using `(Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl`. Establish `hp0 : φ (p : A) = 0` using `by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]`. Establish `hrow : ∀ (x : Fin (k + 1) → A) (Q : Fin (k + 1) → Fin (k + 1) → A), (∀ b, b ≠ 0 → w ∣ x b) → ∀ a, φ (∑ b, x b * Q b a) = φ (x 0) * φ (Q 0 a)`.

Introduce `x Q hx a`. Establish `hz : ∀ i : Fin k, φ (x i.succ) = 0` using `fun i => (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hx _ (Fin.succ_ne_zero _))`. Rewrite using `[map_sum, Fin.sum_univ_succ, map_mul]`. Simplify using `[hz]`. Establish `hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a)`.

Introduce `a`. Take `⟨T, hT⟩` from `hMN 0 a`. Rewrite using `[← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]`. Rewrite using `[map_sub, map_mul, map_mul, map_pow, map_pow, hrow u' N' hu' c, hrow u M hu 0, hrow u' N' hu' 0, hrow u M hu c, mul_pow, mul_pow, hpow 0, hpow c]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key_minor_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u u' : Fin (k + 1) → A) (M N' : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hu' : ∀ b, b ≠ 0 → w ∣ u' b) (c : Fin (k + 1)) :
    w ∣ (∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (p ^ e) - (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (p ^ e) := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hrow : ∀ (x : Fin (k + 1) → A) (Q : Fin (k + 1) → Fin (k + 1) → A), (∀ b, b ≠ 0 → w ∣ x b) →
      ∀ a, φ (∑ b, x b * Q b a) = φ (x 0) * φ (Q 0 a) := by
    intro x Q hx a
    have hz : ∀ i : Fin k, φ (x i.succ) = 0 := fun i =>
      (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hx _ (Fin.succ_ne_zero _))
    rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, hrow u' N' hu' c, hrow u M hu 0, hrow u' N' hu' 0,
    hrow u M hu c, mul_pow, mul_pow, hpow 0, hpow c]
  ring

/- English proof (translation)
Establish `hp : X.p.Prime` using `hD.1`. Establish `hf : 1 ≤ X.n'` using `by have := hD.2.2.1; omega`. Use `set d := (segDists X.TT j).get i with hd`. Use `set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0`. Use `set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1`.

Set `xs : X.TT × Bool` to `(topStart X j, true)`. Set `z : X.TT × Bool` to `(topOdd X j i, true)`. Set `A` to `MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O`. Set `u : Fin (X.m + 1) → A` to `fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)`. Set `u' : Fin (X.m + 1) → A` to `fun b => C (dW O S.w (hhLetters X.TT) 1 z b) * MvPolynomial.X (z, b)`.

Set `M : Fin (X.m + 1) → Fin (X.m + 1) → A` to `fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))`. Set `N' : Fin (X.m + 1) → Fin (X.m + 1) → A` to `fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))`. Establish `hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) = MvPolynomial.map (algebraMap O (KK O)) ((∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (X.p ^ d) - (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (X.p ^ d))`. Unfold `kWkey`. Simplify using `only [map_sub, map_mul, map_pow]`.

Rewrite using `[liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z c rfl, liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs 0 rfl, liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z 0 rfl, liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs c rfl]`. Simplify using `only [u, u', M, N', map_sum, map_mul, map_C, map_X, sigMat_apply]`. Both sides reduce to the same expression. Establish `hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T`. Introduce `b a`.

Take `⟨τ, hτ⟩` from `frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)`. Establish `e1 : (s0 + d - s0).toNat = d` using `by omega`. Rewrite `hτ` using `[e1]`. Establish `e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1`. Rewrite using `[sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]`.

Use `congr 1`. Simplify using `only [hs0, hs1, topStart, topOdd]`. Rewrite using `[segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]`. Rewrite `hτ` using `[e2]`. Use `⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩` and prove the remaining obligations.

Use `congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ` as an intermediate fact. Simplify using `only [map_sub, map_pow, map_mul, map_natCast] at this`. Simplify using `only [M, N', psiO, RingHom.comp_apply]`. Take the linear combination `this`. Establish `hw : (C S.w : A) ^ 2 = (X.p : A)` using `by rw [← map_pow, hsq, map_natCast]`.

Establish `hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b`. Introduce `b hb`. Establish `: dW O S.w (hhLetters X.TT) 1 xs b = S.w`. Establish `: 1 ≤ (b : ℕ)` using `Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))`. Simplify using `[dW, hhLetters, xs, this]`.

Conclude with `⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩`. Establish `hu' : ∀ b, b ≠ 0 → (C S.w : A) ∣ u' b`. Introduce `b hb`. Establish `: dW O S.w (hhLetters X.TT) 1 z b = S.w`. Establish `: 1 ≤ (b : ℕ)` using `Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))`.

Simplify using `[dW, hhLetters, z, this]`. Conclude with `⟨MvPolynomial.X (z, b), by simp only [u', this]⟩`. Take `⟨Q, hQ⟩` from `key_minor_dvd X.p hp (C S.w : A) hw X.m d u u' M N' hMN hu hu' c`. Unfold `InWjRg`. Rewrite using `[hlift, hQ]`.

Introduce `m`. Use `⟨Q.coeff m, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_C_mul, pow_one, map_mul]`.
-/
theorem kW_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (c : Fin (X.m + 1)) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let z : X.TT × Bool := (topOdd X j i, true)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let u' : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 z b) * MvPolynomial.X (z, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) =
      MvPolynomial.map (algebraMap O (KK O)) ((∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (X.p ^ d) -
        (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (X.p ^ d)) := by
    unfold kWkey
    simp only [map_sub, map_mul, map_pow]
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z c rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs c rfl]
    simp only [u, u', M, N', map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl
  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hu' : ∀ b, b ≠ 0 → (C S.w : A) ∣ u' b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 z b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, z, this]
    exact ⟨MvPolynomial.X (z, b), by simp only [u', this]⟩
  obtain ⟨Q, hQ⟩ := key_minor_dvd X.p hp (C S.w : A) hw X.m d u u' M N' hMN hu hu' c
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

/- English proof (translation)
Introduce `X _ O _ _ _ _ S hsq hD j i g hg`. Conclude with `⟨kS_ord X O S hsq hD j i g hg, fun c => kW_ord X O S hsq hD j i g hg c.succ⟩`.
-/
theorem key3Ord : CoarseMultiplicityOrderBound := by
  intro X _ O _ _ _ _ S hsq hD j i g hg
  exact ⟨kS_ord X O S hsq hD j i g hg, fun c => kW_ord X O S hsq hD j i g hg c.succ⟩

/- English proof (translation)
The claim follows from `third_key_of_order key3Ord`.
-/
theorem key3At : CoarseMultiplicityBoundAtIdentity := third_key_of_order key3Ord

end Formalism.MainNotions.ColumnSystems.Pf
