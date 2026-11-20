import Mathlib

noncomputable section

namespace PI.WAU.B

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem natCast_mul_apply (n : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((n : FiniteAdeleRing (𝓞 F) F) * a) v = (n : v.adicCompletion F) * a v := rfl

/- English proof (translation)
Take `⟨b, hb, hxb⟩` from `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Establish `hN : Ideal.absNorm (Ideal.span {b}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `hb0`. Use `⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero hN, ?_⟩` and prove the remaining obligations. Establish `key : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F) = (c : v.adicCompletion F) * (b : v.adicCompletion F)`. Establish `h3` using `congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc.symm`. Rewrite `h3` using `[map_natCast, map_mul]`.

Conclude with `h3`. Rewrite using `[key, mul_assoc, mul_comm (b : v.adicCompletion F) x]`. Conclude with `mul_mem (coe_mem_adicCompletionIntegers v c) hxb`.
-/
theorem exists_nat_local (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hxb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  have hN : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero hN, ?_⟩
  have key : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F) =
      (c : v.adicCompletion F) * (b : v.adicCompletion F) := by
    have h3 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc.symm
    rw [map_natCast, map_mul] at h3
    exact h3
  rw [key, mul_assoc, mul_comm (b : v.adicCompletion F) x]
  exact mul_mem (coe_mem_adicCompletionIntegers v c) hxb

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.1 a.2`. Use `choose N hNpos hN using fun v => exists_nat_local v (a v)`. Use `⟨∏ v ∈ hfin.toFinset, N v, Finset.prod_pos fun v _ => hNpos v, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[natCast_mul_apply]`. Distinguish the cases in `hv : v ∈ hfin.toFinset`.

Rewrite using `[← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, mul_comm ((N v : ℕ) : v.adicCompletion F), mul_assoc]`. Conclude with `mul_mem (natCast_mem _ _) (hN v)`. Establish `hav : a v ∈ v.adicCompletionIntegers F`. Assume the negation of the conclusion as `hc`. Conclude with `hv (hfin.mem_toFinset.2 hc)`.

Conclude with `mul_mem (natCast_mem _ _) hav`.
-/
theorem exists_nat_adele (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ ∀ v, ((n : FiniteAdeleRing (𝓞 F) F) * a) v ∈ v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 a.2
  choose N hNpos hN using fun v => exists_nat_local v (a v)
  refine ⟨∏ v ∈ hfin.toFinset, N v, Finset.prod_pos fun v _ => hNpos v, fun v => ?_⟩
  rw [natCast_mul_apply]
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, mul_comm ((N v : ℕ) : v.adicCompletion F),
      mul_assoc]
    exact mul_mem (natCast_mem _ _) (hN v)
  · have hav : a v ∈ v.adicCompletionIntegers F := by
      by_contra hc
      exact hv (hfin.mem_toFinset.2 hc)
    exact mul_mem (natCast_mem _ _) hav

/- English proof (translation)
Conclude with `(Module.finBasis ℚ K).equivFun.injective.countable`.
-/
theorem countable_field (K : Type) [Field K] [NumberField K] : Countable K := by
  exact (Module.finBasis ℚ K).equivFun.injective.countable

/- English proof (translation)
Establish `hopen : IsOpen {y : v.adicCompletion F | algebraMap F (v.adicCompletion F) c * (x - y) ∈ v.adicCompletionIntegers F}` using `(Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage (continuous_const.mul (continuous_const.sub continuous_id))`. Take `⟨k, hk⟩` from `(denseRange_algebraMap F v).exists_mem_open hopen ⟨x, by simp⟩`. Conclude with `⟨k, hk⟩`.
-/
theorem exists_close (v : HeightOneSpectrum (𝓞 F)) (c : F) (x : v.adicCompletion F) :
    ∃ k : F, algebraMap F (v.adicCompletion F) c * (x - algebraMap F (v.adicCompletion F) k) ∈
      v.adicCompletionIntegers F := by
  have hopen : IsOpen {y : v.adicCompletion F |
      algebraMap F (v.adicCompletion F) c * (x - y) ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F v).exists_mem_open hopen ⟨x, by simp⟩
  exact ⟨k, hk⟩

abbrev Bad (F : Type) [Field F] [NumberField F] (M : ℕ) : Set (HeightOneSpectrum (𝓞 F)) :=
  HeightOneSpectrum.Support (𝓞 F) ((M : F)⁻¹)

def cls (M : ℕ) (a : FiniteAdeleRing (𝓞 F) F) : Bad F M → F :=
  fun v => (exists_close v.1 ((M : F)⁻¹) (a v.1)).choose

/- English proof (translation)
Use `haveI : Finite (Bad F M) := (HeightOneSpectrum.Support.finite (𝓞 F) ((M : F)⁻¹)).to_subtype`. Use `haveI : Countable F := countable_field F`. Use `infer_instance`.
-/
theorem countable_cls (M : ℕ) : Countable (Bad F M → F) := by
  haveI : Finite (Bad F M) := (HeightOneSpectrum.Support.finite (𝓞 F) ((M : F)⁻¹)).to_subtype
  haveI : Countable F := countable_field F
  infer_instance

/- English proof (translation)
Establish `hM0 : (M : F) ≠ 0` using `Nat.cast_ne_zero.2 hM.ne'`. Use `⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : F)⁻¹) * (a - a'), fun v => ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - a' v) ∈ v.adicCompletionIntegers F`. Distinguish the cases in `hv : v ∈ Bad F M`. Establish `hk` using `congrFun h ⟨v, hv⟩`.

Establish `h1` using `(exists_close v ((M : F)⁻¹) (a v)).choose_spec`. Establish `h2` using `(exists_close v ((M : F)⁻¹) (a' v)).choose_spec`. Simplify using `only [cls] at hk`. Rewrite `h1` using `[hk]`. Establish `hsplit : algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - a' v) = algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - algebraMap F (v.adicCompletion F) (exists_close v ((M : F)⁻¹) (a' v)).choose) - algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a' v - algebraMap F (v.a …`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Conclude with `sub_mem h1 h2`. Establish `hint : algebraMap F (v.adicCompletion F) ((M : F)⁻¹) ∈ v.adicCompletionIntegers F`. Rewrite using `[mem_adicCompletionIntegers]`.

Use `erw [valuedAdicCompletion_eq_valuation']`. Simplify `hv` using `[Bad, HeightOneSpectrum.Support]`. Conclude with `mul_mem hint (sub_mem (ha v) (ha' v))`. Rewrite using `[← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]`.
-/
theorem cls_eq {M : ℕ} (hM : 0 < M) {a a' : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (ha' : ∀ v, a' v ∈ v.adicCompletionIntegers F)
    (h : cls M a = cls M a') :
    ∃ b : FiniteAdeleRing (𝓞 F) F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      a - a' = (M : FiniteAdeleRing (𝓞 F) F) * b := by
  classical
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : F)⁻¹) * (a - a'), fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - a' v) ∈ v.adicCompletionIntegers F
    by_cases hv : v ∈ Bad F M
    · have hk := congrFun h ⟨v, hv⟩
      have h1 := (exists_close v ((M : F)⁻¹) (a v)).choose_spec
      have h2 := (exists_close v ((M : F)⁻¹) (a' v)).choose_spec
      simp only [cls] at hk
      rw [hk] at h1
      have hsplit : algebraMap F (v.adicCompletion F) ((M : F)⁻¹) * (a v - a' v) =
          algebraMap F (v.adicCompletion F) ((M : F)⁻¹) *
            (a v - algebraMap F (v.adicCompletion F) (exists_close v ((M : F)⁻¹) (a' v)).choose) -
          algebraMap F (v.adicCompletion F) ((M : F)⁻¹) *
            (a' v - algebraMap F (v.adicCompletion F) (exists_close v ((M : F)⁻¹) (a' v)).choose) := by
        ring
      rw [hsplit]
      exact sub_mem h1 h2
    · have hint : algebraMap F (v.adicCompletion F) ((M : F)⁻¹) ∈ v.adicCompletionIntegers F := by
        rw [mem_adicCompletionIntegers]
        erw [valuedAdicCompletion_eq_valuation']
        simpa [Bad, HeightOneSpectrum.Support] using hv
      exact mul_mem hint (sub_mem (ha v) (ha' v))
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul,
      mul_inv_cancel₀ hM0, map_one, one_mul]

end PI.WAU.B
