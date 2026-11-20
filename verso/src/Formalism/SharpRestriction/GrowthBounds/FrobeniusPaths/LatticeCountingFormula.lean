import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnOrder

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Frob

variable (p f : ℕ) [Fact p.Prime]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ']`. Express the relevant statement in the definitionally equal form `WittVector.constantCoeff (WittVector.frobenius (((WittVector.frobenius : WF p f →+* WF p f) ^ n) x)) = _`.

Rewrite using `[WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP, ← WittVector.constantCoeff_apply, ih, ← pow_mul, ← pow_succ]`.
-/
lemma cc_frob_pow (n : ℕ) (x : WF p f) :
    WittVector.constantCoeff (((WittVector.frobenius : WF p f →+* WF p f) ^ n) x) =
      (WittVector.constantCoeff x) ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change WittVector.constantCoeff (WittVector.frobenius
      (((WittVector.frobenius : WF p f →+* WF p f) ^ n) x)) = _
    rw [WittVector.constantCoeff_apply,
      WittVector.coeff_frobenius_charP, ← WittVector.constantCoeff_apply, ih, ← pow_mul, ← pow_succ]

/- English proof (translation)
Set `_ : Fintype (GaloisField p f)` to `Fintype.ofFinite _`. Rewrite using `[pow_mul, ← GaloisField.card p f hf, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]`.
-/
lemma gf_pow (hf : f ≠ 0) (x : GaloisField p f) (t : ℕ) : x ^ (p ^ (f * t)) = x := by
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  rw [pow_mul, ← GaloisField.card p f hf, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

/- English proof (translation)
Introduce `s s' hss β`. Establish `hf0 : f ≠ 0` using `by omega`. Establish `hfz : (0 : ℤ) < f` using `by exact_mod_cast hf`. Establish `ha_z : (((s % (f : ℤ)).toNat : ℕ) : ℤ) = s % f` using `Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')`. Establish `ha'_z : (((s' % (f : ℤ)).toNat : ℕ) : ℤ) = s' % f` using `Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')`.

Establish `hd_z : (((s' - s).toNat : ℕ) : ℤ) = s' - s` using `Int.toNat_of_nonneg (by linarith)`. Establish `hq : s / f ≤ s' / f` using `Int.ediv_le_ediv hfz hss`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : ℕ, (s % (f : ℤ)).toNat + (s' - s).toNat = (s' % (f : ℤ)).toNat + f * t := by`. Use `⟨(s' / f - s / f).toNat, ?_⟩` and prove the remaining obligations. Establish `ht_z : (((s' / f - s / f).toNat : ℕ) : ℤ) = s' / f - s / f` using `Int.toNat_of_nonneg (by linarith)`.

Establish `e1` using `Int.emod_add_mul_ediv s f`. Establish `e2` using `Int.emod_add_mul_ediv s' f`. Use `zify`. Rewrite using `[ha_z, ha'_z, hd_z, ht_z]`. Take the linear combination `e1 - e2`.

Establish `hz0 : ((sigPow p f s β) ^ (p ^ (s' - s).toNat) - sigPow p f s' β).coeff 0 = 0`. Rewrite using `[← WittVector.constantCoeff_apply, map_sub, map_pow]`. Simplify using `only [sigPow]`. Rewrite using `[cc_frob_pow, cc_frob_pow, ← pow_mul, ← pow_add, ht, pow_add, pow_mul, gf_pow p f hf0, sub_self]`. Establish `hmem` using `(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).2 hz0`.

Take `⟨τ, hτ⟩` from `Ideal.mem_span_singleton.1 hmem`. Conclude with `⟨τ, hτ⟩`.
-/
theorem frobCong (hf : 1 ≤ f) : FrobCong p f := by
  intro s s' hss β
  have hf0 : f ≠ 0 := by omega
  have hfz : (0 : ℤ) < f := by exact_mod_cast hf
  have ha_z : (((s % (f : ℤ)).toNat : ℕ) : ℤ) = s % f := Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')
  have ha'_z : (((s' % (f : ℤ)).toNat : ℕ) : ℤ) = s' % f :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')
  have hd_z : (((s' - s).toNat : ℕ) : ℤ) = s' - s := Int.toNat_of_nonneg (by linarith)
  have hq : s / f ≤ s' / f := Int.ediv_le_ediv hfz hss
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (s % (f : ℤ)).toNat + (s' - s).toNat = (s' % (f : ℤ)).toNat + f * t := by
    refine ⟨(s' / f - s / f).toNat, ?_⟩
    have ht_z : (((s' / f - s / f).toNat : ℕ) : ℤ) = s' / f - s / f := Int.toNat_of_nonneg (by linarith)
    have e1 := Int.emod_add_mul_ediv s f
    have e2 := Int.emod_add_mul_ediv s' f
    zify
    rw [ha_z, ha'_z, hd_z, ht_z]
    linear_combination e1 - e2
  have hz0 : ((sigPow p f s β) ^ (p ^ (s' - s).toNat) - sigPow p f s' β).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_pow]
    simp only [sigPow]
    rw [cc_frob_pow, cc_frob_pow, ← pow_mul, ← pow_add, ht, pow_add, pow_mul, gf_pow p f hf0, sub_self]
  have hmem := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).2 hz0
  obtain ⟨τ, hτ⟩ := Ideal.mem_span_singleton.1 hmem
  exact ⟨τ, hτ⟩

end Frob

end Formalism.MainNotions.LemmaBAlt
