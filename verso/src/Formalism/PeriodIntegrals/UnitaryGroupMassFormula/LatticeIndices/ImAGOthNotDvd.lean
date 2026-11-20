import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGNonunit

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D)

open Classical in

def gOth (p : TypX X) : ℕ := if ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal then D.host.g 1 else D.host.g 0

/- English proof (translation)
Rewrite using `[X.g_eq]`. Unfold `gOf gOth`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `mul_comm _ _`.
-/
theorem imA_g_eq_mul (p : TypX X) : X.B.g = gOf p * gOth X p := by
  rw [X.g_eq]; unfold gOf gOth; split_ifs
  · rfl
  · exact mul_comm _ _

/- English proof (translation)
Establish `h0` using `D.host.g_prime 0`. Establish `h1` using `D.host.g_prime 1`. Establish `hne` using `D.host.g_ne`. Unfold `gOth gOf`. Use `split_ifs`.

Conclude with `(Nat.coprime_primes h0 h1).2 hne`. Conclude with `(Nat.coprime_primes h1 h0).2 hne.symm`.
-/
private theorem gOf_coprime_gOth (p : TypX X) : Nat.Coprime (gOf p) (gOth X p) := by
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  have hne := D.host.g_ne
  unfold gOth gOf
  split_ifs
  · exact (Nat.coprime_primes h0 h1).2 hne
  · exact (Nat.coprime_primes h1 h0).2 hne.symm

/- English proof (translation)
Establish `h0` using `D.host.g_prime 0`. Establish `h1` using `D.host.g_prime 1`. Establish `hne` using `D.host.g_ne`. Unfold `gOth gOf`. Use `split_ifs`.

Introduce `h`. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq h0 h1).1 h)`. Introduce `h`. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq h1 h0).1 h).symm`.
-/
theorem imA_gOth_not_dvd (p : TypX X) : ¬ gOf p ∣ gOth X p := by
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  have hne := D.host.g_ne
  unfold gOth gOf
  split_ifs
  · intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq h0 h1).1 h)
  · intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq h1 h0).1 h).symm

/- English proof (translation)
Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Conclude with `zero_le'`. Rewrite `h`, the goal using `[← WithZero.exp_log hy]`. Rewrite `h` using `[WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem le_exp_sub_one_of_lt_exp' (y : WithZero (Multiplicative ℤ)) (k : ℤ) (h : y < WithZero.exp k) :
    y ≤ WithZero.exp (k - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_le'
  · rw [← WithZero.exp_log hy] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Establish `hy : y ≠ 0` using `(lt_of_le_of_lt zero_le' h).ne'`. Rewrite `h`, the goal using `[← WithZero.exp_log hy]`. Rewrite `h` using `[WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exp_add_one_le_of_exp_lt (y : WithZero (Multiplicative ℤ)) (k : ℤ) (h : WithZero.exp k < y) :
    WithZero.exp (k + 1) ≤ y := by
  have hy : y ≠ 0 := (lt_of_le_of_lt zero_le' h).ne'
  rw [← WithZero.exp_log hy] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

/- English proof (translation)
Take `⟨-, hmem, hnot⟩` from `resArith_holds X p`. Establish `hvg : Valued.v (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) = p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F)`. Establish `e : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) = (((gOf p : ℕ) : X.B.I.F) : p.1.adicCompletion X.B.I.F)`. Simplify using `only [map_natCast]`. Use `first`.

Consider the case `rfl`. Consider the case `exact (map_natCast (algebraMap X.B.I.F (p.1.adicCompletion X.B.I.F)) (gOf p)).symm`. Consider the case `norm_cast`. Consider the case `simp`. Rewrite using `[e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 X.B.I.F) X.B.I.F) (gOf p), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`.

Establish `hle1 : p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) ≤ WithZero.exp (-1 : ℤ)`. Use `(IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1 ((gOf p : ℕ) : 𝓞 X.B.I.F) 1).2 (by simpa using hmem)` as an intermediate fact. Simplify using `using this`. Establish `hgt2 : WithZero.exp (-2 : ℤ) < p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F)`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hnot ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1 ((gOf p : ℕ) : 𝓞 X.B.I.F) 2).1 (by simpa using hc))`. Establish `hge1 : WithZero.exp (-1 : ℤ) ≤ p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F)`. Use `exp_add_one_le_of_exp_lt _ (-2) hgt2` as an intermediate fact. Evaluate the numerical expressions using `at this`.

Conclude with `this`. Establish `hg0 : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) ≠ 0`. Introduce `h`. Establish `h'` using `hvg`. Rewrite `h'` using `[h, map_zero]`.

Conclude with `(lt_of_le_of_lt zero_le' hgt2).ne' h'.symm`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ReciprocityTheory.Aut.mem_maxIdeal_iff, hvg]`. Use `lt_of_le_of_lt hle1 ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Evaluate the numerical expressions. Introduce `x hx`. Rewrite `hx` using `[ReciprocityTheory.Aut.mem_maxIdeal_iff]`. Rewrite using `[Ideal.mem_span_singleton]`. Establish `hx1 : Valued.v (x : p.1.adicCompletion X.B.I.F) ≤ WithZero.exp (-1 : ℤ)`.

Use `le_exp_sub_one_of_lt_exp' _ 0 (by rwa [WithZero.exp_zero])` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`. Establish `hq : Valued.v ((x : p.1.adicCompletion X.B.I.F) / (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F)) ≤ 1`. Rewrite using `[map_div₀, hvg, div_le_one₀ (lt_of_le_of_lt zero_le' hgt2)]`.

Conclude with `hx1.trans hge1`. Use `⟨⟨(x : p.1.adicCompletion X.B.I.F) / (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F), (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hq⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (x : p.1.adicCompletion X.B.I.F) = (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) * ((x : p.1.adicCompletion X.B.I.F) / (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F))`. Clear the denominators using the available nonvanishing facts.
-/
theorem imA_span_g_max (p : TypX X) :
    Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} =
      IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F) := by
  obtain ⟨-, hmem, hnot⟩ := resArith_holds X p
  have hvg : Valued.v (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) =
      p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    have e : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) =
        (((gOf p : ℕ) : X.B.I.F) : p.1.adicCompletion X.B.I.F) := by
      simp only [map_natCast]
      first
        | rfl
        | exact (map_natCast (algebraMap X.B.I.F (p.1.adicCompletion X.B.I.F)) (gOf p)).symm
        | norm_cast
        | simp
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← map_natCast (algebraMap (𝓞 X.B.I.F) X.B.I.F) (gOf p),
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) ≤ WithZero.exp (-1 : ℤ) := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1
      ((gOf p : ℕ) : 𝓞 X.B.I.F) 1).2 (by simpa using hmem)
    simpa using this
  have hgt2 : WithZero.exp (-2 : ℤ) < p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    by_contra hc
    push_neg at hc
    exact hnot ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1
      ((gOf p : ℕ) : 𝓞 X.B.I.F) 2).1 (by simpa using hc))
  have hge1 : WithZero.exp (-1 : ℤ) ≤ p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    have := exp_add_one_le_of_exp_lt _ (-2) hgt2
    norm_num at this
    exact this
  have hg0 : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) ≠ 0 := by
    intro h
    have h' := hvg
    rw [h, map_zero] at h'
    exact (lt_of_le_of_lt zero_le' hgt2).ne' h'.symm
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ReciprocityTheory.Aut.mem_maxIdeal_iff, hvg]
    refine lt_of_le_of_lt hle1 ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · intro x hx
    rw [ReciprocityTheory.Aut.mem_maxIdeal_iff] at hx
    rw [Ideal.mem_span_singleton]
    have hx1 : Valued.v (x : p.1.adicCompletion X.B.I.F) ≤ WithZero.exp (-1 : ℤ) := by
      have := le_exp_sub_one_of_lt_exp' _ 0 (by rwa [WithZero.exp_zero])
      norm_num at this
      exact this
    have hq : Valued.v ((x : p.1.adicCompletion X.B.I.F) /
        (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F)) ≤ 1 := by
      rw [map_div₀, hvg, div_le_one₀ (lt_of_le_of_lt zero_le' hgt2)]
      exact hx1.trans hge1
    refine ⟨⟨(x : p.1.adicCompletion X.B.I.F) /
        (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F),
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hq⟩, ?_⟩
    apply Subtype.ext
    show (x : p.1.adicCompletion X.B.I.F) =
      (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) *
        ((x : p.1.adicCompletion X.B.I.F) /
          (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F))
    field_simp

/- English proof (translation)
Assume the negation of the conclusion as `hnu`. Establish `hm : ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) ∈ IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F)` using `(IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)`. Rewrite `hm` using `[← imA_span_g_max X p, Ideal.mem_span_singleton]`. Establish `hc : IsCoprime ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)`. Establish `hz : IsCoprime ((gOf p : ℕ) : ℤ) ((gOth X p : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 (gOf_coprime_gOth X p)`.

Simplify using `using hz.map (Int.castRingHom (p.1.adicCompletionIntegers X.B.I.F))`. Establish `hu : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)` using `hc.isUnit_of_dvd' dvd_rfl hm`. Establish `htop` using `(IsLocalRing.maximalIdeal.isMaximal (p.1.adicCompletionIntegers X.B.I.F)).ne_top`. Rewrite `htop` using `[← imA_span_g_max X p, Ne, Ideal.span_singleton_eq_top]`. Conclude with `htop hu`.
-/
theorem imA_gOth_unit (p : TypX X) : IsUnit ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  by_contra hnu
  have hm : ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) ∈
      IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F) :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  rw [← imA_span_g_max X p, Ideal.mem_span_singleton] at hm
  have hc : IsCoprime ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)
      ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
    have hz : IsCoprime ((gOf p : ℕ) : ℤ) ((gOth X p : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (gOf_coprime_gOth X p)
    simpa using hz.map (Int.castRingHom (p.1.adicCompletionIntegers X.B.I.F))
  have hu : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := hc.isUnit_of_dvd' dvd_rfl hm
  have htop := (IsLocalRing.maximalIdeal.isMaximal (p.1.adicCompletionIntegers X.B.I.F)).ne_top
  rw [← imA_span_g_max X p, Ne, Ideal.span_singleton_eq_top] at htop
  exact htop hu

/- English proof (translation)
Rewrite using `[imA_g_eq_mul X p, Nat.cast_mul]`. Conclude with `Ideal.span_singleton_mul_right_unit (imA_gOth_unit X p) _`.
-/
theorem imA_span_Bg (p : TypX X) :
    Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} =
      Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} := by
  rw [imA_g_eq_mul X p, Nat.cast_mul]
  exact Ideal.span_singleton_mul_right_unit (imA_gOth_unit X p) _

end MassDataIdxSteps
