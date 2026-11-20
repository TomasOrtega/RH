import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open TensorProduct Formalism.UG Formalism.UG.P

noncomputable section

namespace GlobalTheory.SuppIdele

section Base

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `ha' : (a : F) ≠ 0` using `by simpa using ha`. Use `⟨(a : F)⁻¹ • z, fun w => ?_, by rw [smul_smul, mul_inv_cancel₀ ha', one_smul]⟩` and prove the remaining obligations. Rewrite using `[afsplit_smul_apply, HeightOneSpectrum.mem_adicCompletionIntegers, Algebra.smul_def, map_mul, map_inv₀, map_inv₀]`. Establish `h1 : Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a`. Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := F)]`.

Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)`. Rewrite using `[h1, inv_mul_le_iff₀ (zero_lt_iff.2 (w.intValuation_ne_zero a ha)), mul_one]`. Conclude with `hz w`.
-/
theorem exists_int_mul (a : 𝓞 F) (ha : a ≠ 0) (z : FiniteAdeleRing (𝓞 F) F)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (z w) ≤ w.intValuation a) :
    ∃ x ∈ intAd F, z = (a : F) • x := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  refine ⟨(a : F)⁻¹ • z, fun w => ?_, by rw [smul_smul, mul_inv_cancel₀ ha', one_smul]⟩
  rw [afsplit_smul_apply, HeightOneSpectrum.mem_adicCompletionIntegers, Algebra.smul_def, map_mul, map_inv₀, map_inv₀]
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)
  rw [h1, inv_mul_le_iff₀ (zero_lt_iff.2 (w.intValuation_ne_zero a ha)), mul_one]
  exact hz w

/- English proof (translation)
Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := F)]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)`.
-/
theorem val_algebraMap (w : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)

/- English proof (translation)
The claim follows from `le_antisymm (w.intValuation_le_one a) (not_lt.1 fun h' => h ((w.intValuation_lt_one_iff_mem a).1 h'))`.
-/
theorem intVal_eq_one (w : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F} (h : a ∉ w.asIdeal) : w.intValuation a = 1 :=
  le_antisymm (w.intValuation_le_one a) (not_lt.1 fun h' => h ((w.intValuation_lt_one_iff_mem a).1 h'))

/- English proof (translation)
Assume the negation of the conclusion as `H`. Use `push Not at H`. Conclude with `h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top H))`.
-/
theorem exists_notMem {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : ∃ c ∈ w.asIdeal, c ∉ v.asIdeal := by
  by_contra H
  push Not at H
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top H))

/- English proof (translation)
Use `exists_int_mul c (by rintro rfl; exact hc (zero_mem _)) _ fun w => ?_` and prove the remaining obligations. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[afsplitI_self, map_one, intVal_eq_one w hc]`. Rewrite using `[afsplitI_ne v w h, map_zero]`.

Conclude with `zero_le`.
-/
theorem eps_dvd (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ x ∈ intAd F, afsplitI v 1 = (c : F) • x := by
  refine exists_int_mul c (by rintro rfl; exact hc (zero_mem _)) _ fun w => ?_
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, map_one, intVal_eq_one w hc]
  · rw [afsplitI_ne v w h, map_zero]
    exact zero_le

/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero 2 v.ne_bot)`. Use `haveI := v.isMaximal`. Take `⟨Q, hQ, hI⟩` from `Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {a}) (by simpa using ha0) v.asIdeal`. Establish `hc : IsCoprime (v.asIdeal ^ 2) Q` using `(Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left`. Take `⟨r, hr, q, hq, hrq⟩` from `Ideal.isCoprime_iff_exists.1 hc`.

Take `⟨x, hx, hxe⟩` from `exists_int_mul a ha0 ((q : F) • (1 - afsplitI v 1)) fun w => by`. Rewrite using `[afsplit_smul_apply, afsplit_sub_apply, afsplit_one_apply]`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[afsplitI_self, sub_self, smul_zero, map_zero]`.

Conclude with `zero_le`. Rewrite using `[afsplitI_ne v w h, sub_zero, Algebra.smul_def, mul_one, val_algebraMap]`. Take `⟨t, ht, htw⟩` from `exists_notMem (Ne.symm h)`. Establish `hm` using `Ideal.mul_mem_mul (Ideal.pow_mem_pow ht (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})))) hq`. Rewrite `hm` using `[← hI, Ideal.mem_span_singleton']`.

Take `⟨s, hs⟩` from `hm`. Use `congrArg w.intValuation hs` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_pow, intVal_eq_one w htw, one_pow, one_mul]`. Rewrite using `[← this]`. Conclude with `mul_le_of_le_one_left' (w.intValuation_le_one s)`.

Use `⟨a, ha, r, hr, x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[← hxe, ← add_smul]`. Establish `: (q : F) + (r : F) = 1`. Rewrite using `[add_comm]`. Conclude with `congrArg (fun t : 𝓞 F => (t : F)) hrq` after adjusting the coercions.

Rewrite using `[this, one_smul]`.
-/
theorem one_sub_eps (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ v.asIdeal ^ 2, ∃ r ∈ v.asIdeal ^ 2, ∃ x ∈ intAd F,
      1 - afsplitI v 1 = (a : F) • x + (r : F) • (1 - afsplitI v 1) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero 2 v.ne_bot)
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {a}) (by simpa using ha0) v.asIdeal
  have hc : IsCoprime (v.asIdeal ^ 2) Q := (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left
  obtain ⟨r, hr, q, hq, hrq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨x, hx, hxe⟩ := exists_int_mul a ha0 ((q : F) • (1 - afsplitI v 1)) fun w => by
    rw [afsplit_smul_apply, afsplit_sub_apply, afsplit_one_apply]
    by_cases h : w = v
    · subst h
      rw [afsplitI_self, sub_self, smul_zero, map_zero]
      exact zero_le
    · rw [afsplitI_ne v w h, sub_zero, Algebra.smul_def, mul_one, val_algebraMap]
      obtain ⟨t, ht, htw⟩ := exists_notMem (Ne.symm h)
      have hm := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht
        (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})))) hq
      rw [← hI, Ideal.mem_span_singleton'] at hm
      obtain ⟨s, hs⟩ := hm
      have := congrArg w.intValuation hs
      rw [map_mul, map_mul, map_pow, intVal_eq_one w htw, one_pow, one_mul] at this
      rw [← this]
      exact mul_le_of_le_one_left' (w.intValuation_le_one s)
  refine ⟨a, ha, r, hr, x, hx, ?_⟩
  rw [← hxe, ← add_smul]
  have : (q : F) + (r : F) = 1 := by
    rw [add_comm]; exact_mod_cast congrArg (fun t : 𝓞 F => (t : F)) hrq
  rw [this, one_smul]

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

def ofInt (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) : RInt F E :=
  ⟨(1 : E) ⊗ₜ[F] x, Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toRInt (b : 𝓞 E) : (toRInt F E b : AfE F E) = (b : E) ⊗ₜ[F] 1 := rfl

/- English proof (translation)
Rewrite using `[Subring.coe_mul, coe_toRInt, ofInt, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]`. Both sides reduce to the same expression.
-/
theorem tmul_smul_eq (a : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) :
    (1 : E) ⊗ₜ[F] ((a : F) • x) = ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx : RInt F E) : AfE F E) := by
  rw [Subring.coe_mul, coe_toRInt, ofInt, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rfl

/- English proof (translation)
The claim follows from `afsplitI_mem_intAd v 1 (one_mem _)`.
-/
theorem eps_int (v : HeightOneSpectrum (𝓞 F)) : afsplitI v 1 ∈ intAd F := afsplitI_mem_intAd v 1 (one_mem _)

/- English proof (translation)
Take `⟨p, hp, q, hq, hpq⟩` from `Ideal.isCoprime_iff_exists.1 h`. Establish `h1 : b * q + p - b ∈ I`. Establish `: b * q + p - b = (1 - b) * p` using `by linear_combination b * hpq`. Rewrite using `[this]`. Conclude with `I.mul_mem_left _ hp`.

Establish `h2 : b * q + p - 1 ∈ Q`. Establish `: b * q + p - 1 = (b - 1) * q` using `by linear_combination hpq`. Rewrite using `[this]`. Conclude with `Q.mul_mem_left _ hq`. Distinguish the cases in `h0 : b * q + p = 0`.

Take `⟨t, ht, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (mul_ne_zero hI hQ)`. Rewrite `h1`, `h2` using `[h0]`. Use `⟨t, ht0, ?_, ?_⟩` and prove the remaining obligations. Establish `h3 : t ∈ I` using `Ideal.mul_le_inf ht |>.1`. Rewrite using `[show t - b = t + (0 - b) by ring]`.

Conclude with `I.add_mem h3 h1`. Establish `h3 : t ∈ Q` using `Ideal.mul_le_inf ht |>.2`. Rewrite using `[show t - 1 = t + (0 - 1) by ring]`. Conclude with `Q.add_mem h3 h2`. Conclude with `⟨_, h0, h1, h2⟩`.
-/
theorem exists_crt (I Q : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hQ : Q ≠ ⊥) (h : IsCoprime I Q) (b : 𝓞 E) :
    ∃ b' : 𝓞 E, b' ≠ 0 ∧ b' - b ∈ I ∧ b' - 1 ∈ Q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 h
  have h1 : b * q + p - b ∈ I := by
    have : b * q + p - b = (1 - b) * p := by linear_combination b * hpq
    rw [this]; exact I.mul_mem_left _ hp
  have h2 : b * q + p - 1 ∈ Q := by
    have : b * q + p - 1 = (b - 1) * q := by linear_combination hpq
    rw [this]; exact Q.mul_mem_left _ hq
  by_cases h0 : b * q + p = 0
  · obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mul_ne_zero hI hQ)
    rw [h0] at h1 h2
    refine ⟨t, ht0, ?_, ?_⟩
    · have h3 : t ∈ I := Ideal.mul_le_inf ht |>.1
      rw [show t - b = t + (0 - b) by ring]
      exact I.add_mem h3 h1
    · have h3 : t ∈ Q := Ideal.mul_le_inf ht |>.2
      rw [show t - 1 = t + (0 - 1) by ring]
      exact Q.add_mem h3 h2
  · exact ⟨_, h0, h1, h2⟩

/- English proof (translation)
Use `haveI := P.isMaximal`. Establish `hv0 : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥`. Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `v.ne_bot`. Take `⟨Q, hQ, hI⟩` from `Ideal.eq_prime_pow_mul_coprime hv0 P.asIdeal`.

Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hv0 (by rw [hI, Ideal.mul_bot])`. Take `⟨b', hb0, hb1, hb2⟩` from `exists_crt (P.asIdeal ^ 2) Q (pow_ne_zero 2 P.ne_bot) hQ0 (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left b`. Establish `hb0' : (b' : E) ≠ 0` using `by simpa using hb0`.

Use `set e : RInt F E := ofInt E (afsplitI v 1) (eps_int v) with he`. Establish `hee : (e : AfE F E) = afsplitEps E v` using `rfl`. Use `set ι := inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι`. Establish `hid` using `afsplit_eps_idem (E := E) v`. Establish `hinv : ι b' * ι (b' : E)⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel₀ hb0', map_one]`.

Establish `hmul : (1 + (ι b' - 1) * afsplitEps E v) * (1 + (ι (b' : E)⁻¹ - 1) * afsplitEps E v) = 1`. Take the linear combination `(ι b' - 1) * (ι (b' : E)⁻¹ - 1) * hid + afsplitEps E v * hinv`. Use `⟨⟨_, _, hmul, by rw [mul_comm, hmul]⟩, 1 + (toRInt F E b' - 1) * e, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]`. Introduce `w hw`.

Apply `Units.ext` to reduce the goal to its premises. Use `show prV (E := E) w (1 + (ι b' - 1) * afsplitEps E v) = 1`. Rewrite using `[map_add, map_mul, afsplit_prV_eps_ne v w hw, mul_zero, add_zero, map_one]`. Take `⟨a, ha, r, hr, x, hx, hxe⟩` from `one_sub_eps v`. Establish `hle : ∀ c ∈ v.asIdeal ^ 2, toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) ∈ (P.asIdeal ^ 2).map (toRInt F E)`.

Introduce `c hc`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Establish `h1` using `Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hc`. Rewrite `h1` using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ 2 h1` and prove the remaining obligations.

Rewrite using `[← hPv]`. Conclude with `Ideal.map_comap_le`. Establish `hx' : 1 - afsplitI v 1 ∈ intAd F` using `sub_mem (one_mem _) (eps_int v)`. Establish `h1 : 1 - e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx + toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ofInt E _ hx'`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subring.coe_add, ← tmul_smul_eq, ← tmul_smul_eq, ← TensorProduct.tmul_add, ← hxe, TensorProduct.tmul_sub]`. Both sides reduce to the same expression. Establish `h2 : 1 - e ∈ (P.asIdeal ^ 2).map (toRInt F E)`. Rewrite using `[h1]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (hle a ha)) (Ideal.mul_mem_right _ _ (hle r hr))`.

Establish `h3 : 1 + (toRInt F E b' - 1) * e - toRInt F E b = toRInt F E (b' - b) + (1 - toRInt F E b') * (1 - e)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `add_mem (Ideal.mem_map_of_mem _ hb1) (Ideal.mul_mem_left _ _ h2)`.

Introduce `P' hP'`. Rewrite using `[add_sub_cancel_left]`. Distinguish the cases in `hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P'.asIdeal`. Rewrite `hle` using `[hI]`. Establish `hQP : Q ≤ P'.asIdeal`.

Break down `P'.isPrime.mul_le.1 hle with h | h` into its components or cases. Use `haveI := P'.isPrime`. Conclude with `absurd (HeightOneSpectrum.ext (P.isMaximal.eq_of_le P'.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le h))).symm hP'`. Conclude with `h`. Use `Ideal.mem_map_of_mem (toRInt F E) (hQP hb2)` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one]`. Conclude with `Ideal.mul_mem_right _ _ this`. Establish `hc : ∃ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ∈ P'.asIdeal ∧ c ∉ v.asIdeal`. Assume the negation of the conclusion as `H`. Use `push Not at H`.

Use `haveI := P'.isMaximal`. Establish `hm : (P'.asIdeal.under (𝓞 F)).IsMaximal` using `inferInstance`. Apply `hle` to reduce the goal to its premises. Rewrite using `[← hm.eq_of_le v.isPrime.ne_top (fun c hc => H c hc)]`. Conclude with `Ideal.map_comap_le`.

Take `⟨c, hc1, hc2⟩` from `hc`. Take `⟨x, hx, hxe⟩` from `eps_dvd v c hc2`. Establish `h1 : e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) * ofInt E x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← tmul_smul_eq, ← hxe]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc1))`.
-/
theorem exists_supported_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ (y : (AfE F E)ˣ) (y₀ : RInt F E), (y₀ : AfE F E) = (y : AfE F E) ∧ y ∈ suppAt E v ∧
      y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  haveI := P.isMaximal
  have hv0 : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hv0 P.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hv0 (by rw [hI, Ideal.mul_bot])
  obtain ⟨b', hb0, hb1, hb2⟩ := exists_crt (P.asIdeal ^ 2) Q (pow_ne_zero 2 P.ne_bot) hQ0
    (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left b
  have hb0' : (b' : E) ≠ 0 := by simpa using hb0
  set e : RInt F E := ofInt E (afsplitI v 1) (eps_int v) with he
  have hee : (e : AfE F E) = afsplitEps E v := rfl
  set ι := inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hid := afsplit_eps_idem (E := E) v
  have hinv : ι b' * ι (b' : E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hb0', map_one]
  have hmul : (1 + (ι b' - 1) * afsplitEps E v) * (1 + (ι (b' : E)⁻¹ - 1) * afsplitEps E v) = 1 := by
    linear_combination (ι b' - 1) * (ι (b' : E)⁻¹ - 1) * hid + afsplitEps E v * hinv
  refine ⟨⟨_, _, hmul, by rw [mul_comm, hmul]⟩, 1 + (toRInt F E b' - 1) * e, rfl, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w hw
    apply Units.ext
    show prV (E := E) w (1 + (ι b' - 1) * afsplitEps E v) = 1
    rw [map_add, map_mul, afsplit_prV_eps_ne v w hw, mul_zero, add_zero, map_one]
  · obtain ⟨a, ha, r, hr, x, hx, hxe⟩ := one_sub_eps v
    have hle : ∀ c ∈ v.asIdeal ^ 2, toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      intro c hc
      apply Ideal.mem_map_of_mem
      have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hc
      rw [Ideal.map_pow] at h1
      refine Ideal.pow_right_mono ?_ 2 h1
      rw [← hPv]; exact Ideal.map_comap_le
    have hx' : 1 - afsplitI v 1 ∈ intAd F := sub_mem (one_mem _) (eps_int v)
    have h1 : 1 - e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx +
        toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ofInt E _ hx' := by
      apply Subtype.ext
      rw [Subring.coe_add, ← tmul_smul_eq, ← tmul_smul_eq, ← TensorProduct.tmul_add, ← hxe, TensorProduct.tmul_sub]
      rfl
    have h2 : 1 - e ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      rw [h1]
      exact add_mem (Ideal.mul_mem_right _ _ (hle a ha)) (Ideal.mul_mem_right _ _ (hle r hr))
    have h3 : 1 + (toRInt F E b' - 1) * e - toRInt F E b = toRInt F E (b' - b) + (1 - toRInt F E b') * (1 - e) := by
      rw [map_sub]; ring
    rw [h3]
    exact add_mem (Ideal.mem_map_of_mem _ hb1) (Ideal.mul_mem_left _ _ h2)
  · intro P' hP'
    rw [add_sub_cancel_left]
    by_cases hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P'.asIdeal
    · rw [hI] at hle
      have hQP : Q ≤ P'.asIdeal := by
        rcases P'.isPrime.mul_le.1 hle with h | h
        · haveI := P'.isPrime
          exact absurd (HeightOneSpectrum.ext (P.isMaximal.eq_of_le P'.isPrime.ne_top
            (Ideal.IsPrime.le_of_pow_le h))).symm hP'
        · exact h
      have := Ideal.mem_map_of_mem (toRInt F E) (hQP hb2)
      rw [map_sub, map_one] at this
      exact Ideal.mul_mem_right _ _ this
    · have hc : ∃ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ∈ P'.asIdeal ∧ c ∉ v.asIdeal := by
        by_contra H
        push Not at H
        haveI := P'.isMaximal
        have hm : (P'.asIdeal.under (𝓞 F)).IsMaximal := inferInstance
        apply hle
        rw [← hm.eq_of_le v.isPrime.ne_top (fun c hc => H c hc)]
        exact Ideal.map_comap_le
      obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨x, hx, hxe⟩ := eps_dvd v c hc2
      have h1 : e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) * ofInt E x hx := by
        apply Subtype.ext
        rw [← tmul_smul_eq, ← hxe]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc1))

end GlobalTheory.SuppIdele
