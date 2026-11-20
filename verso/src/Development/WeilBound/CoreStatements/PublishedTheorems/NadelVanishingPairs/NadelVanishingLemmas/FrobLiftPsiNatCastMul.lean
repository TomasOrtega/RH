import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehlerStatement

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DI

section FrobDiff

variable {K : Type} [CommRing K]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add P Q hP hQ => simp [hP, hQ, add_smul, Finset.sum_add_distrib]`. Consider the case `mul_X P i hP`. Simplify using `only [map_mul, aeval_X, Derivation.leibniz, hP, Finset.smul_sum, smul_smul, Derivation.leibniz, pderiv_X, Fin.sum_univ_two]`.

Apply the tactic sequence `fin_cases i <;> simp [add_smul, mul_comm, smul_smul, Pi.single_apply] <;> abel`.
-/
theorem kaehlerD_aeval_fin_two (x : Fin 2 → K) (P : MvPolynomial (Fin 2) ℤ) :
    KaehlerDifferential.D ℤ K (aeval x P) =
      ∑ i, aeval x (pderiv i P) • KaehlerDifferential.D ℤ K (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hP, Finset.smul_sum, smul_smul,
      Derivation.leibniz, pderiv_X, Fin.sum_univ_two]
    fin_cases i <;> simp [add_smul, mul_comm, smul_smul, Pi.single_apply] <;> abel

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add P Q hP hQ => simp [hP, hQ]`. Consider the case `mul_X P j hP => simp [hP]`.
-/
theorem ringHom_aeval_fin_two {Kt : Type} [CommRing Kt] (π : Kt →+* K) (x : Fin 2 → Kt)
    (P : MvPolynomial (Fin 2) ℤ) : π (aeval x P) = aeval (fun i => π (x i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP => simp [hP]

variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)

/- English proof (translation)
Take `⟨w, hw⟩` from `(hL.ker (F z - z ^ p)).1 (by rw [map_sub, hF, map_pow, sub_self])`. Conclude with `⟨w, by rw [← hw]; ring⟩`.
-/
theorem frobLift_exists_w (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    ∃ w, F z = z ^ p + p * w := by
  obtain ⟨w, hw⟩ := (hL.ker (F z - z ^ p)).1 (by rw [map_sub, hF, map_pow, sub_self])
  exact ⟨w, by rw [← hw]; ring⟩

/- English proof (translation)
Establish `e : (p : Kt) * (w - w') = 0`. Use `h.symm.trans h'` as an intermediate fact. Rewrite using `[mul_sub, sub_eq_zero]`. Conclude with `add_left_cancel this`. Establish `e2` using `(hL.ann _).mp e`.

Rewrite `e2` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem frobLift_w_unique (hL : IsFlatLift p π) {z w w' : Kt} (h : F z = z ^ p + p * w)
    (h' : F z = z ^ p + p * w') : π w = π w' := by
  have e : (p : Kt) * (w - w') = 0 := by
    have := h.symm.trans h'
    rw [mul_sub, sub_eq_zero]
    exact add_left_cancel this
  have e2 := (hL.ann _).mp e
  rwa [map_sub, sub_eq_zero] at e2

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]`.
-/
theorem kaehlerD_pow_char (x : K) : KaehlerDifferential.D ℤ K (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

def frobLiftPsi (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) : Ω[K⁄ℤ] :=
  π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
    KaehlerDifferential.D ℤ K (π (frobLift_exists_w p π F hL hF z).choose)

variable {p π F}

/- English proof (translation)
Unfold `frobLiftPsi`. Rewrite using `[frobLift_w_unique p π F hL (frobLift_exists_w p π F hL hF z).choose_spec h]`.
-/
theorem frobLiftPsi_spec (hL : IsFlatLift p π) (hF : IsFrob p π F) {z w : Kt}
    (h : F z = z ^ p + p * w) :
    frobLiftPsi p π F hL hF z = π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
      KaehlerDifferential.D ℤ K (π w) := by
  unfold frobLiftPsi
  rw [frobLift_w_unique p π F hL (frobLift_exists_w p π F hL hF z).choose_spec h]

/- English proof (translation)
Take `⟨w, hw⟩` from `frobLift_exists_w p π F hL hF z`. Take `⟨w', hw'⟩` from `frobLift_exists_w p π F hL hF z'`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp.out (X 0 : MvPolynomial (Fin 2) ℤ) (X 1)`. Establish `hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0` using `Nat.cast_ne_zero.mpr hp.out.ne_zero`. Take `⟨C, hC0⟩ : ∃ C : MvPolynomial (Fin 2) ℤ, (p : MvPolynomial (Fin 2) ℤ) * C = (X 0 + X 1) ^ p - X 0 ^ p - X 1 ^ p` from `⟨X 0 * X 1 * r, by rw [hr]; ring⟩`.

Establish `hpd0 : pderiv 0 C = (X 0 + X 1) ^ (p - 1) - X 0 ^ (p - 1)`. Use `congrArg (pderiv 0) hC0` as an intermediate fact. Simplify using `[Derivation.leibniz_pow] at this`. Conclude with `mul_left_cancel₀ hp0 (by rw [this]; ring)`. Establish `hpd1 : pderiv 1 C = (X 0 + X 1) ^ (p - 1) - X 1 ^ (p - 1)`.

Use `congrArg (pderiv 1) hC0` as an intermediate fact. Simplify using `[Derivation.leibniz_pow] at this`. Conclude with `mul_left_cancel₀ hp0 (by rw [this]; ring)`. Establish `hc : (z + z') ^ p = z ^ p + z' ^ p + p * aeval ![z, z'] C`. Use `congrArg (aeval ![z, z']) hC0` as an intermediate fact.

Simplify using `at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw', frobLiftPsi_spec hL hF (w := w + w' - aeval ![z, z'] C) (by rw [map_add, hw, hw', hc]; ring)]`. Establish `hD : KaehlerDifferential.D ℤ K (π (aeval ![z, z'] C)) = ((π z + π z') ^ (p - 1) - π z ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z) + ((π z + π z') ^ (p - 1) - π z' ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z')`.

Rewrite using `[ringHom_aeval_fin_two, kaehlerD_aeval_fin_two, Fin.sum_univ_two, hpd0, hpd1]`. Simplify using the standard rewrite rules. Simplify using `only [map_add, map_sub, hD, smul_add, sub_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem frobLiftPsi_add (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z + z') = frobLiftPsi p π F hL hF z + frobLiftPsi p π F hL hF z' := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X 0 : MvPolynomial (Fin 2) ℤ) (X 1)
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨C, hC0⟩ : ∃ C : MvPolynomial (Fin 2) ℤ,
      (p : MvPolynomial (Fin 2) ℤ) * C = (X 0 + X 1) ^ p - X 0 ^ p - X 1 ^ p :=
    ⟨X 0 * X 1 * r, by rw [hr]; ring⟩
  have hpd0 : pderiv 0 C = (X 0 + X 1) ^ (p - 1) - X 0 ^ (p - 1) := by
    have := congrArg (pderiv 0) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hpd1 : pderiv 1 C = (X 0 + X 1) ^ (p - 1) - X 1 ^ (p - 1) := by
    have := congrArg (pderiv 1) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hc : (z + z') ^ p = z ^ p + z' ^ p + p * aeval ![z, z'] C := by
    have := congrArg (aeval ![z, z']) hC0
    simp at this
    rw [this]
    ring
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w + w' - aeval ![z, z'] C) (by rw [map_add, hw, hw', hc]; ring)]
  have hD : KaehlerDifferential.D ℤ K (π (aeval ![z, z'] C)) =
      ((π z + π z') ^ (p - 1) - π z ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z) +
      ((π z + π z') ^ (p - 1) - π z' ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z') := by
    rw [ringHom_aeval_fin_two, kaehlerD_aeval_fin_two, Fin.sum_univ_two, hpd0, hpd1]
    simp
  simp only [map_add, map_sub, hD, smul_add, sub_smul]
  abel

/- English proof (translation)
Take `⟨w, hw⟩` from `frobLift_exists_w p π F hL hF z`. Take `⟨w', hw'⟩` from `frobLift_exists_w p π F hL hF z'`. Establish `hp1 : 1 ≤ p` using `hp.out.one_lt.le`. Establish `hpK : (p : K) = 0` using `CharP.cast_eq_zero K p`. Rewrite using `[frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw', frobLiftPsi_spec hL hF (w := w * z' ^ p + z ^ p * w' + p * w * w') (by rw [map_mul, hw, hw']; ring)]`.

Simplify using `only [map_add, map_mul, map_pow, map_natCast, hpK, zero_mul, add_zero, Derivation.leibniz, kaehlerD_pow_char p, smul_zero, zero_add]`. Establish `e1 : (π z * π z') ^ (p - 1) * π z = π z ^ p * π z' ^ (p - 1)`. Rewrite using `[mul_pow, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp1]`. Establish `e2 : (π z * π z') ^ (p - 1) * π z' = π z' ^ p * π z ^ (p - 1)`. Rewrite using `[mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, mul_comm]`.

Simplify using `only [smul_add, smul_smul, e1, e2]`. Normalize the expressions using the abelian group laws.
-/
theorem frobLiftPsi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z * z') =
      π z ^ p • frobLiftPsi p π F hL hF z' + π z' ^ p • frobLiftPsi p π F hL hF z := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w * z' ^ p + z ^ p * w' + p * w * w')
      (by rw [map_mul, hw, hw']; ring)]
  simp only [map_add, map_mul, map_pow, map_natCast, hpK, zero_mul, add_zero, Derivation.leibniz,
    kaehlerD_pow_char p, smul_zero, zero_add]
  have e1 : (π z * π z') ^ (p - 1) * π z = π z ^ p * π z' ^ (p - 1) := by
    rw [mul_pow, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp1]
  have e2 : (π z * π z') ^ (p - 1) * π z' = π z' ^ p * π z ^ (p - 1) := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, mul_comm]
  simp only [smul_add, smul_smul, e1, e2]
  abel

/- English proof (translation)
Establish `hp1 : 1 ≤ p` using `hp.out.one_lt.le`. Establish `hp2 : p - 1 ≠ 0` using `by have := hp.out.two_le; omega`. Establish `hpK : (p : K) = 0` using `CharP.cast_eq_zero K p`. Establish `e : (p : Kt) * (p : Kt) ^ (p - 1) = (p : Kt) ^ p`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hp1]`.

Rewrite using `[frobLiftPsi_spec hL hF (w := F y - (p : Kt) ^ (p - 1) * y ^ p) (by rw [map_mul, map_natCast, mul_pow]; linear_combination (y ^ p) * e)]`. Simplify using `[hpK, hF y, kaehlerD_pow_char p, zero_pow hp2]`.
-/
theorem frobLiftPsi_natCast_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (y : Kt) :
    frobLiftPsi p π F hL hF ((p : Kt) * y) = 0 := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp2 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have e : (p : Kt) * (p : Kt) ^ (p - 1) = (p : Kt) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [frobLiftPsi_spec hL hF (w := F y - (p : Kt) ^ (p - 1) * y ^ p)
    (by rw [map_mul, map_natCast, mul_pow]; linear_combination (y ^ p) * e)]
  simp [hpK, hF y, kaehlerD_pow_char p, zero_pow hp2]

/- English proof (translation)
Take `⟨y, hy⟩` from `(hL.ker (z - z')).1 (by rw [map_sub, h, sub_self])`. Rewrite using `[show z = z' + (p : Kt) * y by rw [← hy]; ring, frobLiftPsi_add, frobLiftPsi_natCast_mul, add_zero]`.
-/
theorem frobLiftPsi_congr (hL : IsFlatLift p π) (hF : IsFrob p π F) {z z' : Kt} (h : π z = π z') :
    frobLiftPsi p π F hL hF z = frobLiftPsi p π F hL hF z' := by
  obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, h, sub_self])
  rw [show z = z' + (p : Kt) * y by rw [← hy]; ring, frobLiftPsi_add, frobLiftPsi_natCast_mul, add_zero]

def frobLiftPhi (hL : IsFlatLift p π) (hF : IsFrob p π F) : K →+ Ω[K⁄ℤ] where
  toFun a := frobLiftPsi p π F hL hF (Function.surjInv hL.surj a)
  map_zero' := by
    have h0 : frobLiftPsi p π F hL hF 0 = 0 := by
      have := frobLiftPsi_add hL hF (0 : Kt) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [frobLiftPsi_congr hL hF (z' := 0) (by rw [Function.surjInv_eq hL.surj, map_zero]), h0]
  map_add' a b := by
    rw [← frobLiftPsi_add, frobLiftPsi_congr hL hF (z' := Function.surjInv hL.surj a + Function.surjInv hL.surj b)
      (by rw [map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])]

/- English proof (translation)
The claim follows from `frobLiftPsi_congr hL hF (Function.surjInv_eq hL.surj _)`.
-/
theorem frobLiftPhi_apply (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    frobLiftPhi hL hF (π z) = frobLiftPsi p π F hL hF z :=
  frobLiftPsi_congr hL hF (Function.surjInv_eq hL.surj _)

/- English proof (translation)
Take `⟨z, rfl⟩` from `hL.surj a`. Take `⟨z', rfl⟩` from `hL.surj b`. Rewrite using `[← map_mul, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPsi_mul]`.
-/
theorem frobLiftPhi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (a b : K) :
    frobLiftPhi hL hF (a * b) = a ^ p • frobLiftPhi hL hF b + b ^ p • frobLiftPhi hL hF a := by
  obtain ⟨z, rfl⟩ := hL.surj a
  obtain ⟨z', rfl⟩ := hL.surj b
  rw [← map_mul, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPsi_mul]

/- English proof (translation)
Introduce `K Kt _ _ p _ _ π F hL hF`. Establish `univ : ∀ (M : Type) [AddCommGroup M] [Module K M] (D' : K →+ M), (∀ a b, D' (a * b) = a • D' b + b • D' a) → ∃ g : Ω[K⁄ℤ] →+ M, (∀ a, g (KaehlerDifferential.D ℤ K a) = D' a) ∧ ∀ (c : K) (v : Ω[K⁄ℤ]), g (c • v) = c • g v`. Introduce `M _ _ D' hD'`. Set `Dv : Derivation ℤ K M` to `Derivation.mk' D'.toIntLinearMap hD'`. Conclude with `⟨Dv.liftKaehlerDifferential.toAddMonoidHom, fun a => Dv.liftKaehlerDifferential_comp_D a, fun c v => Dv.liftKaehlerDifferential.map_smul c v⟩`.

Establish `hmul : ∀ a b : K, frobLiftPhi hL hF (a * b) = frobenius K p a • frobLiftPhi hL hF b + frobenius K p b • frobLiftPhi hL hF a`. Introduce `a b`. Rewrite using `[frobenius_def p a, frobenius_def p b]`. Conclude with `frobLiftPhi_mul hL hF a b`. Take `⟨g, hg, hsm⟩` from `@univ (Ω[K⁄ℤ]) _ (Module.compHom _ (frobenius K p)) (frobLiftPhi hL hF) hmul`.

Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Introduce `c v`. Establish `h0 : g (c • v) = frobenius K p c • g v` using `hsm c v`. Rewrite `h0` using `[frobenius_def p c]`. Conclude with `h0`.

Introduce `z w hzw`. Use `hg (π z)` as an intermediate fact. Rewrite `this` using `[frobLiftPhi_apply, frobLiftPsi_spec hL hF hzw]`. Conclude with `this`.
-/
theorem exists_isF_of_flatLift : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → ∃ f, IsF p π F f := by
  intro K Kt _ _ p _ _ π F hL hF
  have univ : ∀ (M : Type) [AddCommGroup M] [Module K M] (D' : K →+ M),
      (∀ a b, D' (a * b) = a • D' b + b • D' a) →
      ∃ g : Ω[K⁄ℤ] →+ M, (∀ a, g (KaehlerDifferential.D ℤ K a) = D' a) ∧
        ∀ (c : K) (v : Ω[K⁄ℤ]), g (c • v) = c • g v := by
    intro M _ _ D' hD'
    let Dv : Derivation ℤ K M := Derivation.mk' D'.toIntLinearMap hD'
    exact ⟨Dv.liftKaehlerDifferential.toAddMonoidHom,
      fun a => Dv.liftKaehlerDifferential_comp_D a,
      fun c v => Dv.liftKaehlerDifferential.map_smul c v⟩
  have hmul : ∀ a b : K, frobLiftPhi hL hF (a * b) =
      frobenius K p a • frobLiftPhi hL hF b + frobenius K p b • frobLiftPhi hL hF a := by
    intro a b
    rw [frobenius_def p a, frobenius_def p b]
    exact frobLiftPhi_mul hL hF a b
  obtain ⟨g, hg, hsm⟩ :=
    @univ (Ω[K⁄ℤ]) _ (Module.compHom _ (frobenius K p)) (frobLiftPhi hL hF) hmul
  refine ⟨g, ?_, ?_⟩
  · intro c v
    have h0 : g (c • v) = frobenius K p c • g v := hsm c v
    rw [frobenius_def p c] at h0
    exact h0
  · intro z w hzw
    have := hg (π z)
    rw [frobLiftPhi_apply, frobLiftPsi_spec hL hF hzw] at this
    exact this

end FrobDiff

end GlobalTheory.DI
