import Mathlib
open scoped NNReal

namespace GlobalTheory.WittMapUniq

open WittVector

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro r; exact ⟨r, by simp⟩`. Consider the case `succ n ih`. Introduce `r`.

Take `⟨t, ht⟩` from `surjective_frobenius R l r`. Take `⟨s, hs⟩` from `ih t`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, pow_mul, hs, ← ht, frobenius_def]`.
-/
theorem exists_pow_pow_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] : ∀ (n : ℕ) (r : R), ∃ s : R, s ^ l ^ n = r := by
  intro n
  induction n with
  | zero => intro r; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r
    obtain ⟨t, ht⟩ := surjective_frobenius R l r
    obtain ⟨s, hs⟩ := ih t
    refine ⟨s, ?_⟩
    rw [pow_succ, pow_mul, hs, ← ht, frobenius_def]

/- English proof (translation)
Introduce `l _ R O _ _ _ _ _ _ F ψ hF`. Establish `hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x`. Introduce `x`. Rewrite using `[← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]`. Establish `h` using `(WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)`.

Simplify using `only [WittVector.constantCoeff_apply] at h`. Rewrite using `[h, hF, WittVector.map_coeff, sub_self]`. Establish `hteich : ∀ (n : ℕ) (r : R), (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r)`. Introduce `n r`. Take `⟨s, rfl⟩` from `exists_pow_pow_eq l R n r`.

Establish `h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s)`. Use `hdiff (teichmuller l s)` as an intermediate fact. Rewrite `this` using `[WittVector.map_teichmuller]`. Then use the resulting hypothesis. Establish `h2` using `dvd_sub_pow_of_dvd_sub h1 n`. Rewrite using `[map_pow, map_pow, map_pow, map_pow]`.

Conclude with `h2`. Use extensionality with `x m`. Establish `key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)}`. Introduce `n`. Set `I : Ideal (WittVector l O)` to `Ideal.span {((l : WittVector l O) ^ n)}`.

Establish `hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ)`. Use `WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span rfl`. Introduce `r`.

Simplify using `only [RingHom.comp_apply, WittVector.map_teichmuller]`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)`. Use `congrArg (fun f => f x) hfg` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`.

Conclude with `Ideal.Quotient.eq.mp this`. Establish `h` using `(mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))`. Establish `h'` using `(le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h`. Conclude with `h' m (Nat.lt_succ_self m)`.
-/
theorem eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  intro l _ R O _ _ _ _ _ _ F ψ hF
  have hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x := by
    intro x
    rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
    have h := (WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hF, WittVector.map_coeff, sub_self]
  have hteich : ∀ (n : ℕ) (r : R),
      (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r) := by
    intro n r
    obtain ⟨s, rfl⟩ := exists_pow_pow_eq l R n r
    have h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s) := by
      have := hdiff (teichmuller l s)
      rwa [WittVector.map_teichmuller] at this
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [map_pow, map_pow, map_pow, map_pow]
    exact h2
  ext x m
  have key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)} := by
    intro n
    let I : Ideal (WittVector l O) := Ideal.span {((l : WittVector l O) ^ n)}
    have hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ) := by
      refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_
      · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · intro r
        simp only [RingHom.comp_apply, WittVector.map_teichmuller]
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)
    have := congrArg (fun f => f x) hfg
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.mp this
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))
  have h' := (le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h
  exact h' m (Nat.lt_succ_self m)

end GlobalTheory.WittMapUniq
