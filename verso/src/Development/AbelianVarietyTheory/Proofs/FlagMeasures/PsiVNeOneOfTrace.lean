import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.StdCharTotReal

section Local

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `one_ne_zero`. Establish `hD` using `FractionalIdeal.dual_ne_zero ℤ ℚ h1`. Establish `hd : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔ a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)`. Rewrite using `[FractionalIdeal.mem_dual h1]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp hx`. Take `⟨k, hk⟩` from `h b`. Conclude with `⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩`. Introduce `h r`.

Take `⟨k, hk⟩` from `h (algebraMap _ F r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)`. Conclude with `⟨k, by rw [Algebra.traceForm_apply] at hk; simpa using hk.symm⟩`. Rewrite using `[hd, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)), FractionalIdeal.mem_inv_iff (inv_ne_zero hD), ← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]`. Prove the components needed by the constructor for the conclusion. Introduce `h d hd`.

Conclude with `(FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))`. Introduce `h y hy`. Take `⟨d, hd, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hy`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr (h d hd)`.
-/
theorem trace_int_iff (a : F) : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ r : 𝓞 F, (r : F) = a * d := by
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ h1
  have hd : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
      a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual h1]
    constructor
    · intro h x hx
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨k, hk⟩ := h b
      exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩
    · intro h r
      obtain ⟨k, hk⟩ := h (algebraMap _ F r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
      exact ⟨k, by rw [Algebra.traceForm_apply] at hk; simpa using hk.symm⟩
  rw [hd, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)),
    FractionalIdeal.mem_inv_iff (inv_ne_zero hD), ← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr (h d hd)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hx` using `(GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h`. Rewrite `hx` using `[GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F), FractionalIdeal.mem_one_iff]`. Then use the resulting hypothesis. Introduce and unpack `⟨r, rfl⟩ v`.

Conclude with `HeightOneSpectrum.coe_mem_adicCompletionIntegers v r`.
-/
theorem integral_iff (x : F) : (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) x v ∈ v.adicCompletionIntegers F) ↔
    ∃ r : 𝓞 F, (r : F) = x := by
  constructor
  · intro h
    have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
    rwa [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
      FractionalIdeal.mem_one_iff] at hx
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

/- English proof (translation)
Establish `hone : ∀ a : F, χ (algebraMap F (Af F) a) = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ F a = k`. Introduce `a`. Rewrite using `[hrat, Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`.

Use `⟨-n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, map_neg]`. Establish `: -Algebra.trace ℚ F a = (n : ℚ)` using `by exact_mod_cast hn`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨k, hk⟩`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hO : ∀ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) (r : F) v ∈ v.adicCompletionIntegers F` using `fun r => (integral_iff _).2 ⟨r, rfl⟩`. Establish `hint : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ t = 1` using `fun t ht => GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ y = 1}) (isClosed_eq hc continuous_const) (fun r => (hone _).2 (by simpa using (trace_int_iff (1 : F)).2 (fun d _ => ⟨d, (one_mul _).symm⟩) r)) t ht`. Take `⟨a, s, hs, hz⟩` from `GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos z`. Rewrite `hz` using `[one_smul]`. Establish `hmul : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = χ (algebraMap F (Af F) a * t)`.

Introduce `t ht`. Rewrite using `[hz, add_mul, hadd, hint (s * t) (fun v => mul_mem (hs v) (ht v)), mul_one]`. Establish `h1 : (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔ ∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k`. Prove the components needed by the constructor for the conclusion. Introduce `h r`.

Rewrite using `[← hone, map_mul, ← hmul _ (hO r)]`. Conclude with `h _ (hO r)`. Introduce `h t ht`. Rewrite using `[hmul t ht]`. Conclude with `GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ (algebraMap F (Af F) a * y) = 1}) (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const) (fun r => by show χ _ = 1`.

Rewrite using `[← map_mul, hone]`. Conclude with `h r) t ht`. Rewrite using `[h1, trace_int_iff]`. Use `forall₂_congr fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_iff, hz, add_mul, map_mul]`.

Use `forall_congr' fun v => ?_` and prove the remaining obligations. Establish `h2 : (s * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F` using `mul_mem (hs v) (hO d v)`. Conclude with `⟨fun h => add_mem h h2, fun h => (add_mem_cancel_right h2).1 h⟩`.
-/
theorem fin_conductor (χ : Af F → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hrat : ∀ a : F, χ (algebraMap F (Af F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (-a) : ℚ) : ℂ))) (z : Af F) :
    (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 F), ∀ v : HeightOneSpectrum (𝓞 F), (z * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := by
  have hone : ∀ a : F, χ (algebraMap F (Af F) a) = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ F a = k := by
    intro a
    rw [hrat, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, map_neg] at hn
      have : -Algebra.trace ℚ F a = (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      rw [map_neg, hk]
      push_cast
      ring
  have hO : ∀ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) (r : F) v ∈ v.adicCompletionIntegers F :=
    fun r => (integral_iff _).2 ⟨r, rfl⟩
  have hint : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ t = 1 := fun t ht =>
    GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ y = 1}) (isClosed_eq hc continuous_const)
      (fun r => (hone _).2 (by simpa using (trace_int_iff (1 : F)).2 (fun d _ => ⟨d, (one_mul _).symm⟩) r)) t ht
  obtain ⟨a, s, hs, hz⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos z
  rw [one_smul] at hz
  have hmul : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = χ (algebraMap F (Af F) a * t) := by
    intro t ht
    rw [hz, add_mul, hadd, hint (s * t) (fun v => mul_mem (hs v) (ht v)), mul_one]
  have h1 : (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k := by
    constructor
    · intro h r
      rw [← hone, map_mul, ← hmul _ (hO r)]
      exact h _ (hO r)
    · intro h t ht
      rw [hmul t ht]
      exact GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ (algebraMap F (Af F) a * y) = 1})
        (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const)
        (fun r => by
          show χ _ = 1
          rw [← map_mul, hone]
          exact h r) t ht
  rw [h1, trace_int_iff]
  refine forall₂_congr fun d _ => ?_
  rw [← integral_iff, hz, add_mul, map_mul]
  refine forall_congr' fun v => ?_
  have h2 : (s * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := mul_mem (hs v) (hO d v)
  exact ⟨fun h => add_mem h h2, fun h => (add_mem_cancel_right h2).1 h⟩

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y`.
-/
theorem single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : singleV F v y v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw`.
-/
theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    singleV F v y w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

/- English proof (translation)
Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `singleV F v y w * t w = singleV F v (y * t v) w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[single_same, single_same]`.

Rewrite using `[single_ne v _ hw, single_ne v _ hw, zero_mul]`.
-/
theorem single_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (t : Af F) :
    singleV F v y * t = singleV F v (y * t v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change singleV F v y w * t w = singleV F v (y * t v) w
  by_cases hw : w = v
  · subst hw; rw [single_same, single_same]
  · rw [single_ne v _ hw, single_ne v _ hw, zero_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))`. Establish `hd1 : algebraMap F (Fv F v) (d : F) ≠ 0`. Rewrite using `[Ne, map_eq_zero]`.

Conclude with `hd0` after adjusting the coercions. Take `⟨z, hz⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)`. Establish `key` using `(fin_conductor (fun y => ψ (pairA F 0 y)) (h.1.comp (Continuous.prodMk continuous_const continuous_id)) (fun a b => by`. Rewrite using `[← AddChar.map_add_eq_mul]`. Conclude with `congrArg ψ (Prod.ext (add_zero _).symm rfl))`.

Use the proof step `(fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹))).1`. Use the proof step `(fun t _ => by rw [single_mul]; exact hn _) d hd v`. Establish `h1 : (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹) * algebraMap F (Af F) (d : F)) v = z`. Rewrite using `[single_mul, single_same]`. Use `show z * (algebraMap F (Fv F v) (d : F))⁻¹ * algebraMap F (Fv F v) (d : F) = z`.

Rewrite using `[inv_mul_cancel_right₀ hd1]`. Rewrite `key` using `[h1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem psiV_ne_one_of_trace {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have key := (fin_conductor (fun y => ψ (pairA F 0 y))
    (h.1.comp (Continuous.prodMk continuous_const continuous_id))
    (fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext (add_zero _).symm rfl))
    (fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹))).1
    (fun t _ => by rw [single_mul]; exact hn _) d hd v
  have h1 : (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹) * algebraMap F (Af F) (d : F)) v = z := by
    rw [single_mul, single_same]
    show z * (algebraMap F (Fv F v) (d : F))⁻¹ * algebraMap F (Fv F v) (d : F) = z
    rw [inv_mul_cancel_right₀ hd1]
  rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at key
  omega

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun τ => τ x) _ fun τ => rfl]`. Establish `hr : ∀ τ : F →+* ℂ, (InfinitePlace.mk τ).embedding = τ` using `fun τ => InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))`. Use `push_cast`.

Use `Fintype.sum_bijective (fun w : InfinitePlace F => w.embedding) ⟨fun a b hab => ?_, fun τ => ⟨_, hr τ⟩⟩ _ _ fun w => ?_` and prove the remaining obligations. Rewrite using `[← InfinitePlace.mk_embedding a, ← InfinitePlace.mk_embedding b]`. Conclude with `congrArg InfinitePlace.mk hab`. Use `InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)` as an intermediate fact. Conclude with `Complex.conj_eq_iff_re.1 (RingHom.congr_fun this x)`.
-/
theorem sum_places_eq_trace [IsTotallyReal F] (x : F) :
    (((∑ w : InfinitePlace F, (w.embedding x).re : ℝ)) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun τ => τ x) _ fun τ => rfl]
  have hr : ∀ τ : F →+* ℂ, (InfinitePlace.mk τ).embedding = τ := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  push_cast
  refine Fintype.sum_bijective (fun w : InfinitePlace F => w.embedding) ⟨fun a b hab => ?_, fun τ => ⟨_, hr τ⟩⟩ _ _
    fun w => ?_
  · rw [← InfinitePlace.mk_embedding a, ← InfinitePlace.mk_embedding b]
    exact congrArg InfinitePlace.mk hab
  · have := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
    exact Complex.conj_eq_iff_re.1 (RingHom.congr_fun this x)

end Local

/- English proof (translation)
Introduce `F _ _ hF ψ hψ hinf v`. Use `psiV_ne_one_of_trace hψ (fun a => ?_) v` and prove the remaining obligations. Rewrite using `[hinf, ← sum_places_eq_trace]`. Use `congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)` and prove the remaining obligations. Conclude with `InfinitePlace.Completion.extensionEmbedding_coe w _`.
-/
theorem exists_psiV_ne_one : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ r, psiV F ψ v r ≠ 1 := by
  intro F _ _ hF ψ hψ hinf v
  refine psiV_ne_one_of_trace hψ (fun a => ?_) v
  rw [hinf, ← sum_places_eq_trace]
  refine congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

end GlobalTheory.StdCharTotReal
