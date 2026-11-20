import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← WithZero.exp_log hx, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exp_neg_le_of_natAbs_log_le {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) {n : ℕ}
    (h : (WithZero.log x).natAbs ≤ n) : WithZero.exp (-(n : ℤ)) ≤ x := by
  rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
  omega

/- English proof (translation)
Introduce `F _ _ ι _ w hw y c hc`. Establish `hb : ∀ i, ∃ b : F, Valued.v (algebraMap F ((w i).adicCompletion F) b - y i) ≤ Valued.v (algebraMap F ((w i).adicCompletion F) c)`. Introduce `i`. Set `c' : (w i).adicCompletion F` to `algebraMap F ((w i).adicCompletion F) c⁻¹`. Establish `hcc : c' * algebraMap F ((w i).adicCompletion F) c = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hc, map_one]`. Establish `ho : IsOpen ((fun z => (z - y i) * c') ⁻¹' ((Valued.v : Valuation ((w i).adicCompletion F) (WithZero (Multiplicative ℤ))).integer : Set ((w i).adicCompletion F)))` using `(Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)`. Take `⟨b, hb⟩` from `(HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w i)).exists_mem_open ho ⟨y i, by`. Simplify using `only [Set.mem_preimage, sub_self, zero_mul, SetLike.mem_coe]`. Conclude with `zero_mem _⟩`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Establish `h1 : Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') ≤ 1` using `(Valuation.mem_integer_iff _ _).1 hb`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul, mul_assoc, hcc, mul_one]`. Use `_ ≤ 1 * Valued.v (algebraMap F ((w i).adicCompletion F) c) := by gcongr`.

Use `_ = _ := one_mul _`. Use `choose b hbv using hb`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 F)) (Finset.univ : Finset ι) b`. Establish `hd' : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (d : 𝓞 F) • b i` using `fun i => hd i (Finset.mem_univ i)`. Use `choose r hr using hd'`.

Establish `hd0 : algebraMap (𝓞 F) F d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2`. Establish `ht : algebraMap (𝓞 F) F d * c ≠ 0` using `mul_ne_zero hd0 hc`. Take `⟨s0, hs0⟩` from `exists_forall_sub_mem_ideal (s := Finset.univ) (fun i => (w i).asIdeal) (fun i => (WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs) (fun i _ => (w i).prime) (fun i _ j _ hij h => hij (hw (HeightOneSpectrum.ext h))) (fun i => r i.1)`. Use `⟨algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d, fun i => ?_⟩` and prove the remaining obligations. Establish `hloc : (w i).valuation F (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i) ≤ (w i).valuation F c`.

Establish `e1 : algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i = algebraMap (𝓞 F) F (s0 - r i) / algebraMap (𝓞 F) F d`. Rewrite using `[map_sub, hr i, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts. Establish `e2 : c = algebraMap (𝓞 F) F d * c / algebraMap (𝓞 F) F d`. Clear the denominators using the available nonvanishing facts.

Establish `hint : (w i).intValuation (s0 - r i) ≤ WithZero.exp (-((WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs : ℤ))` using `((w i).intValuation_le_pow_iff_mem _ _).2 (hs0 i (Finset.mem_univ i))`. Establish `hv : (w i).valuation F (algebraMap (𝓞 F) F (s0 - r i)) ≤ (w i).valuation F (algebraMap (𝓞 F) F d * c)`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `hint.trans (exp_neg_le_of_natAbs_log_le ((Valuation.ne_zero_iff _).2 ht) le_rfl)`. Rewrite using `[e1]`.

Use `conv_rhs => rw [e2]`. Rewrite using `[map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]`. Use `gcongr`. Establish `e3 : ∀ x : F, Valued.v (algebraMap F ((w i).adicCompletion F) x) = (w i).valuation F x` using `fun x => (w i).valuedAdicCompletion_eq_valuation' x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[sub_add_sub_cancel]`. Use `_ ≤ max _ _ := Valuation.map_add _ _ _`. Use `_ ≤ _ := max_le (by rw [← map_sub, e3, e3]; exact hloc) (hbv i)`.
-/
theorem exists_approx_finite_places :
    ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)),
      Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 →
      ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
        Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  intro F _ _ ι _ w hw y c hc
  classical
  have hb : ∀ i, ∃ b : F, Valued.v (algebraMap F ((w i).adicCompletion F) b - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
    intro i
    let c' : (w i).adicCompletion F := algebraMap F ((w i).adicCompletion F) c⁻¹
    have hcc : c' * algebraMap F ((w i).adicCompletion F) c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have ho : IsOpen ((fun z => (z - y i) * c') ⁻¹'
        ((Valued.v : Valuation ((w i).adicCompletion F) (WithZero (Multiplicative ℤ))).integer : Set ((w i).adicCompletion F))) :=
      (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
    obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w i)).exists_mem_open ho ⟨y i, by
      simp only [Set.mem_preimage, sub_self, zero_mul, SetLike.mem_coe]
      exact zero_mem _⟩
    refine ⟨b, ?_⟩
    have h1 : Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') ≤ 1 :=
      (Valuation.mem_integer_iff _ _).1 hb
    calc Valued.v (algebraMap F ((w i).adicCompletion F) b - y i)
        = Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') *
            Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
          rw [← map_mul, mul_assoc, hcc, mul_one]
      _ ≤ 1 * Valued.v (algebraMap F ((w i).adicCompletion F) c) := by gcongr
      _ = _ := one_mul _
  choose b hbv using hb
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 F))
    (Finset.univ : Finset ι) b
  have hd' : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (d : 𝓞 F) • b i :=
    fun i => hd i (Finset.mem_univ i)
  choose r hr using hd'
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have ht : algebraMap (𝓞 F) F d * c ≠ 0 := mul_ne_zero hd0 hc
  obtain ⟨s0, hs0⟩ := exists_forall_sub_mem_ideal (s := Finset.univ) (fun i => (w i).asIdeal)
    (fun i => (WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs)
    (fun i _ => (w i).prime) (fun i _ j _ hij h => hij (hw (HeightOneSpectrum.ext h)))
    (fun i => r i.1)
  refine ⟨algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d, fun i => ?_⟩
  have hloc : (w i).valuation F (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i) ≤
      (w i).valuation F c := by
    have e1 : algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i =
        algebraMap (𝓞 F) F (s0 - r i) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hr i, Algebra.smul_def]
      field_simp
    have e2 : c = algebraMap (𝓞 F) F d * c / algebraMap (𝓞 F) F d := by
      field_simp
    have hint : (w i).intValuation (s0 - r i) ≤ WithZero.exp
        (-((WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs : ℤ)) :=
      ((w i).intValuation_le_pow_iff_mem _ _).2 (hs0 i (Finset.mem_univ i))
    have hv : (w i).valuation F (algebraMap (𝓞 F) F (s0 - r i)) ≤
        (w i).valuation F (algebraMap (𝓞 F) F d * c) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hint.trans (exp_neg_le_of_natAbs_log_le ((Valuation.ne_zero_iff _).2 ht) le_rfl)
    rw [e1]
    conv_rhs => rw [e2]
    rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
    gcongr
  have e3 : ∀ x : F, Valued.v (algebraMap F ((w i).adicCompletion F) x) = (w i).valuation F x :=
    fun x => (w i).valuedAdicCompletion_eq_valuation' x
  calc Valued.v (algebraMap F ((w i).adicCompletion F)
        (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) - y i)
      = Valued.v ((algebraMap F ((w i).adicCompletion F)
          (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) -
            algebraMap F ((w i).adicCompletion F) (b i)) +
          (algebraMap F ((w i).adicCompletion F) (b i) - y i)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ _ := max_le (by rw [← map_sub, e3, e3]; exact hloc) (hbv i)

end GlobalTheory
