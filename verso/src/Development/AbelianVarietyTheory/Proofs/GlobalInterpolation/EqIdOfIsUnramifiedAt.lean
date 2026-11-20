import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnramifiedDiscriminant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
/- English proof (translation)
Take `⟨-, hE, -, hτ⟩` from `h`. Introduce `hσ`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Establish `hc` using `hE.isComplex (InfinitePlace.mk τ)`. Rewrite `hc` using `[InfinitePlace.isComplex_mk_iff]`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Establish `hx` using `hτ τ x`.

Rewrite `hx` using `[hσ, AlgHom.id_apply]`. Conclude with `hx.symm`.
-/
private lemma isCMExt_conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨-, hE, -, hτ⟩ := h
  intro hσ
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hc := hE.isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx := hτ τ x
  rw [hσ, AlgHom.id_apply] at hx
  exact hx.symm

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
/- English proof (translation)
Establish `hprime : (Module.finrank F E).Prime` using `by rw [h.2.2.1]; exact Nat.prime_two`. Use `haveI := Subalgebra.isSimpleOrder_of_finrank_prime F E hprime`. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h1` into its components or cases. Establish `hmem : x ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `hx`. Rewrite `hmem` using `[h0]`.

Conclude with `Algebra.mem_bot.mp hmem`. It suffices to derive a contradiction. Apply `isCMExt_conj_ne_id h` to reduce the goal to its premises. Use extensionality with `y`. Establish `hmem : y ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `h1 ▸ Algebra.mem_top`.

Conclude with `hmem`.
-/
private lemma isCMExt_mem_range_of_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hprime : (Module.finrank F E).Prime := by rw [h.2.2.1]; exact Nat.prime_two
  haveI := Subalgebra.isSimpleOrder_of_finrank_prime F E hprime
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h1
  · have hmem : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h0] at hmem
    exact Algebra.mem_bot.mp hmem
  · exfalso
    apply isCMExt_conj_ne_id h
    ext y
    have hmem : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    exact hmem

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in

/- English proof (translation)
Take `⟨f, hf⟩` from `isCMExt_mem_range_of_conj_fixed h ha`. Establish `hint : IsIntegral ℤ f`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap F E).injective, hf]`. Conclude with `RingOfIntegers.isIntegral_coe a`. Use `⟨⟨f, hint⟩, ?_⟩` and prove the remaining obligations.

Use `ext`. Conclude with `hf`.
-/
theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (a : 𝓞 E) (ha : σ a = a) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t = a := by
  obtain ⟨f, hf⟩ := isCMExt_mem_range_of_conj_fixed h ha
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hf]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨⟨f, hint⟩, ?_⟩
  ext
  exact hf

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
/- English proof (translation)
Take `⟨-, -, -, hτ⟩` from `h`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hτ, hτ, star_star]`.
-/
private lemma isCMExt_conj_conj (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E))` using `FaithfulSMul.algebraMap_injective _ _`. Take `⟨P, -, hPp, hPv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)`. Establish `hPne : P ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[← hPv, Ideal.comap_bot_of_injective _ hinj]`. Use `haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩`. Use `haveI : Algebra.IsUnramifiedAt (𝓞 F) P := hv ⟨P, hPp, hPne⟩ ⟨hPv.symm⟩`. Set `σ' : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ (Function.Involutive.bijective (isCMExt_conj_conj h))`. Use `haveI : IsGalois F E := by`.

Use `IsGalois.of_fixedField_eq_bot F E (eq_bot_iff.mpr fun x hx => ?_)` and prove the remaining obligations. Conclude with `IntermediateField.mem_bot.mpr (isCMExt_mem_range_of_conj_fixed h ((IntermediateField.mem_fixedField_iff _ _).mp hx σ' (Subgroup.mem_top _)))`. Establish `hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = 1`. Rewrite using `[Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]`. Conclude with `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : 𝓞 E, σ' • x - x ∉ P := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hmem : σ' ∈ P.inertia (E ≃ₐ[F] E)` using `hcon`. Use `haveI := (Nat.card_eq_one_iff_unique.mp hcard).1`.

Establish `h1 : σ' = 1` using `congrArg Subtype.val (Subsingleton.elim (⟨σ', hmem⟩ : P.inertia _) 1)`. Apply `isCMExt_conj_ne_id h` to reduce the goal to its premises. Use extensionality with `z`. Conclude with `DFunLike.congr_fun h1 z`. Use `set y : 𝓞 E := σ' • x`.

Establish `hy : (y : E) = σ x` using `rfl`. Take `⟨t, ht⟩` from `_root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x + y) (by show σ ((x : E) + σ x) = (x : E) + σ x`. Rewrite using `[map_add, isCMExt_conj_conj h, add_comm])`. Take `⟨n, hn⟩` from `_root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x * y) (by show σ ((x : E) * σ x) = (x : E) * σ x`. Rewrite using `[map_mul, isCMExt_conj_conj h, mul_comm])`.

Use `⟨x, t, n, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `(congrArg (fun z : 𝓞 E => (z : E)) ht).symm`. Rewrite using `[← hy]`. Conclude with `(congrArg (fun z : 𝓞 E => (z : E)) hn).symm`.

Introduce `hmem`. Establish `hP : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) ∈ P`. Rewrite `hmem` using `[← hPv]`. Conclude with `Ideal.mem_comap.mp hmem`. Establish `heq : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (y - x) ^ 2`.

Rewrite using `[map_sub, map_pow, map_mul, ht, hn, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hP` using `[heq]`. Conclude with `hx (hPp.mem_of_pow_mem 2 hP)`.
-/
theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v) :
    ∃ (w : E) (t n : 𝓞 F), w + σ w = algebraMap F E (t : F) ∧ w * σ w = algebraMap F E (n : F) ∧
      t ^ 2 - 4 * n ∉ v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨P, -, hPp, hPv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hPv, Ideal.comap_bot_of_injective _ hinj]
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 F) P := hv ⟨P, hPp, hPne⟩ ⟨hPv.symm⟩
  let σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Function.Involutive.bijective (isCMExt_conj_conj h))
  haveI : IsGalois F E := by
    refine IsGalois.of_fixedField_eq_bot F E (eq_bot_iff.mpr fun x hx => ?_)
    exact IntermediateField.mem_bot.mpr (isCMExt_mem_range_of_conj_fixed h
      ((IntermediateField.mem_fixedField_iff _ _).mp hx σ' (Subgroup.mem_top _)))
  have hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, σ' • x - x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hmem : σ' ∈ P.inertia (E ≃ₐ[F] E) := hcon
    haveI := (Nat.card_eq_one_iff_unique.mp hcard).1
    have h1 : σ' = 1 := congrArg Subtype.val (Subsingleton.elim (⟨σ', hmem⟩ : P.inertia _) 1)
    apply isCMExt_conj_ne_id h
    ext z
    exact DFunLike.congr_fun h1 z
  set y : 𝓞 E := σ' • x
  have hy : (y : E) = σ x := rfl
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x + y) (by
    show σ ((x : E) + σ x) = (x : E) + σ x
    rw [map_add, isCMExt_conj_conj h, add_comm])
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x * y) (by
    show σ ((x : E) * σ x) = (x : E) * σ x
    rw [map_mul, isCMExt_conj_conj h, mul_comm])
  refine ⟨x, t, n, ?_, ?_, ?_⟩
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) ht).symm
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) hn).symm
  · intro hmem
    have hP : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) ∈ P := by
      rw [← hPv] at hmem
      exact Ideal.mem_comap.mp hmem
    have heq : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (y - x) ^ 2 := by
      rw [map_sub, map_pow, map_mul, ht, hn, map_ofNat]
      ring
    rw [heq] at hP
    exact hx (hPp.mem_of_pow_mem 2 hP)

end GlobalTheory.UnramifiedDiscriminant
