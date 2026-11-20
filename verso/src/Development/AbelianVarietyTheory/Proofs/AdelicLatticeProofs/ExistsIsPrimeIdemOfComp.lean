import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

noncomputable section

open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CMPrimeIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem conj_conj {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Use `haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1`. Use `haveI := h.2.1`. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h1 | h1` into its components or cases. Establish `: x ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `hx`. Rewrite `this` using `[h1]`.

Conclude with `Algebra.mem_bot.1 this`. It suffices to derive a contradiction. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `y`. Establish `hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `h1 ▸ Algebra.mem_top`. Establish `hy' : σ y = y` using `hy`. Use `h.2.2.2 τ y` as an intermediate fact. Rewrite `this` using `[hy']`.

Conclude with `this.symm`.
-/
theorem exists_of_conj_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  haveI := h.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h1 | h1
  · have : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h1] at this
    exact Algebra.mem_bot.1 this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    have hy' : σ y = y := hy
    have := h.2.2.2 τ y
    rw [hy'] at this
    exact this.symm

variable (F E) in

def infPart : AE F E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F) : AF F →ₐ[F] Ainf F) (AlgHom.id F E)).toRingHom

variable (F E) in

def swapAf : Af F ⊗[F] E →+* E ⊗[F] Af F := (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv.toRingHom

def Comp (Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E) : Prop :=
  (∀ z, infPart F E z = 0 → Φ z = 0 → z = 0) ∧
  (∀ s, ∃ z, infPart F E z = 0 ∧ Φ z = s) ∧
  (∀ x, Φ (incA F E x) = algebraMap _ _ x) ∧
  (∀ z, finPart F E z ∈ intAE F E ↔ ∀ Q, Φ z Q ∈ Q.adicCompletionIntegers E) ∧
  ∀ (a : AF F) Q, Φ (algebraMap _ _ a) Q = GlobalTheory.AdeleBaseChange.locMap F Q (a.2 (Q.under (𝓞 F)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `: intAE F E ≤ (Formalism.L2.DIV.RInt F E).toAddSubgroup.comap (swapAf F E).toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, rfl⟩`.

Conclude with `Formalism.UG.P.levelaf_tmul_mem x ha`. Conclude with `this hz`. Introduce `hz`. Take `⟨m, g, hg⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Take `⟨r, hr, e⟩` from `Formalism.UG.P.levelaf_decomp g hg hz`.

Establish `: z = ∑ j, r j ⊗ₜ[F] (g j : E)`. Apply `(Algebra.TensorProduct.comm F (Af F) E).injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Conclude with `e`. Rewrite using `[this]`.

Conclude with `sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩`.
-/
theorem mem_intAE_iff (z : Af F ⊗[F] E) :
    z ∈ intAE F E ↔ swapAf F E z ∈ Formalism.L2.DIV.RInt F E := by
  constructor
  · intro hz
    have : intAE F E ≤ (Formalism.L2.DIV.RInt F E).toAddSubgroup.comap (swapAf F E).toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, x, rfl⟩
      exact Formalism.UG.P.levelaf_tmul_mem x ha
    exact this hz
  · intro hz
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg hz
    have : z = ∑ j, r j ⊗ₜ[F] (g j : E) := by
      apply (Algebra.TensorProduct.comm F (Af F) E).injective
      rw [map_sum]
      exact e
    rw [this]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩

variable (F E) in
/- English proof (translation)
Take `⟨ι, hι⟩` from `GlobalTheory.AdeleBaseChange.exists_toAd F E`. Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv F E`. Establish `he1 : ∀ z, (e z).1 = infPart F E z` using `fun z => (he z).1`. Establish `he2 : ∀ z, (e z).2 = finPart F E z` using `fun z => (he z).2`. Establish `hb : Function.Bijective (swapAf F E)` using `(Algebra.TensorProduct.comm F (Af F) E).bijective`.

Use `⟨ι.comp ((swapAf F E).comp (finPart F E)), fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩` and prove the remaining obligations. Establish `h3 : finPart F E z = 0` using `hb.1 (GlobalTheory.AdeleBaseChange.map_injective hι (by`. Rewrite using `[map_zero, map_zero]`. Conclude with `h2))`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)`. Take `⟨y, rfl⟩` from `GlobalTheory.AdeleBaseChange.map_surjective hι s`. Take `⟨y, rfl⟩` from `hb.2 y`. Take `⟨z, hz⟩` from `e.surjective (0, y)`.

Use `⟨z, by rw [← he1, hz], ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (swapAf F E (finPart F E z)) = _`. Rewrite using `[← he2, hz]`. Conclude with `GlobalTheory.AdeleBaseChange.map_tmul_one hι x`. Rewrite using `[mem_intAE_iff]`.

Conclude with `⟨fun h => GlobalTheory.AdeleBaseChange.map_mem_int hι h, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι h⟩`. Express the relevant statement in the definitionally equal form `ι ((1 : E) ⊗ₜ[F] a.2) Q = _`. Rewrite using `[hι, map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem exists_comp : ∃ Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E, Comp Φ := by
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have he1 : ∀ z, (e z).1 = infPart F E z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart F E z := fun z => (he z).2
  have hb : Function.Bijective (swapAf F E) := (Algebra.TensorProduct.comm F (Af F) E).bijective
  refine ⟨ι.comp ((swapAf F E).comp (finPart F E)), fun z h1 h2 => ?_, fun s => ?_, fun x => ?_,
    fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart F E z = 0 := hb.1 (GlobalTheory.AdeleBaseChange.map_injective hι (by
      rw [map_zero, map_zero]; exact h2))
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)
  · obtain ⟨y, rfl⟩ := GlobalTheory.AdeleBaseChange.map_surjective hι s
    obtain ⟨y, rfl⟩ := hb.2 y
    obtain ⟨z, hz⟩ := e.surjective (0, y)
    refine ⟨z, by rw [← he1, hz], ?_⟩
    change ι (swapAf F E (finPart F E z)) = _
    rw [← he2, hz]
  · exact GlobalTheory.AdeleBaseChange.map_tmul_one hι x
  · rw [mem_intAE_iff]
    exact ⟨fun h => GlobalTheory.AdeleBaseChange.map_mem_int hι h, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι h⟩
  · change ι ((1 : E) ⊗ₜ[F] a.2) Q = _
    rw [hι, map_one, one_mul]
    rfl

def IsDelta (Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) (e : AE F E) : Prop :=
  infPart F E e = 0 ∧ Φ e P = 1 ∧ ∀ Q, Q ≠ P → Φ e Q = 0

def Comparison₂ (P : HeightOneSpectrum (𝓞 E)) (e : AE F E) : Prop :=
  ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)

def cO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom σ.toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cO_coe (σ : E →ₐ[F] E) (x : 𝓞 E) : (cO σ x : E) = σ (x : E) := rfl

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)`.
-/
theorem eq_of_le {P Q : HeightOneSpectrum (𝓞 E)} (h : P.asIdeal ≤ Q.asIdeal) : P = Q :=
  HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)

variable {σ : E →ₐ[F] E}

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[cO_coe, cO_coe, conj_conj h]`.
-/
theorem cO_cO (h : IsCMExt F E σ) (x : 𝓞 E) : cO σ (cO σ x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, conj_conj h]

def cP (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  HeightOneSpectrum.comap (cO σ) (fun x => ⟨cO σ x, cO_cO h x⟩) P

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_cP (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    x ∈ (cP h P).asIdeal ↔ cO σ x ∈ P.asIdeal := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_incA (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a x`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] σ (σ x) = _`. Rewrite using `[conj_conj h]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[F] σ (σ x) = _
    rw [conj_conj h]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, and_self]`. Consider the case `tmul a x => exact ⟨rfl, rfl⟩`. Consider the case `add a b ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, and_self]`.
-/
theorem parts_cA (z : AE F E) :
    infPart F E (cA σ z) = sigR (Ainf F) σ (infPart F E z) ∧
    finPart F E (cA σ z) = sigR (Af F) σ (finPart F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, and_self]
  | tmul a x => exact ⟨rfl, rfl⟩
  | add a b ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, and_self]

/- English proof (translation)
Rewrite using `[(parts_cA z).2]`. Establish `: intAE F E ≤ (intAE F E).comap (sigR (Af F) σ).toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, cO σ x, rfl⟩`.

Conclude with `this hz`.
-/
theorem finPart_cA_mem {z : AE F E} (hz : finPart F E z ∈ intAE F E) :
    finPart F E (cA σ z) ∈ intAE F E := by
  rw [(parts_cA z).2]
  have : intAE F E ≤ (intAE F E).comap (sigR (Af F) σ).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, cO σ x, rfl⟩
  exact this hz

/- English proof (translation)
Introduce `x hx`. Establish `e1 : cA σ (e * incA F E ((cO σ x : E)⁻¹)) = cA σ e * incA F E ((x : E)⁻¹)`. Rewrite using `[map_mul, cA_incA, cO_coe, map_inv₀ σ, conj_conj hσ]`. Establish `hx' : cO σ x ≠ 0` using `fun h0 => hx (by rw [← cO_cO hσ x, h0, map_zero])`. Rewrite using `[mem_cP, h _ hx', ← e1]`.

Use `not_congr ⟨finPart_cA_mem, fun h => ?_⟩` and prove the remaining obligations. Use `finPart_cA_mem (σ := σ) h` as an intermediate fact. Rewrite `this` using `[cA_cA hσ]`. Then use the resulting hypothesis.
-/
theorem Comparison₂.conj (hσ : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (h : Comparison₂ P e) :
    Comparison₂ (cP hσ P) (cA σ e) := by
  intro x hx
  have e1 : cA σ (e * incA F E ((cO σ x : E)⁻¹)) = cA σ e * incA F E ((x : E)⁻¹) := by
    rw [map_mul, cA_incA, cO_coe, map_inv₀ σ, conj_conj hσ]
  have hx' : cO σ x ≠ 0 := fun h0 => hx (by rw [← cO_cO hσ x, h0, map_zero])
  rw [mem_cP, h _ hx', ← e1]
  refine not_congr ⟨finPart_cA_mem, fun h => ?_⟩
  have := finPart_cA_mem (σ := σ) h
  rwa [cA_cA hσ] at this

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), not_lt]`. Use `inv_le_one₀ (zero_lt_iff.2 ?_)` and prove the remaining obligations. Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `hx` after adjusting the coercions.
-/
theorem inv_mem_iff (Q : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    algebraMap E (Q.adicCompletion E) ((x : E)⁻¹) ∈ Q.adicCompletionIntegers E ↔ x ∉ Q.asIdeal := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), not_lt]
  refine inv_le_one₀ (zero_lt_iff.2 ?_)
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hx

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Establish `: cO σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[cO_coe]`. Conclude with `σ.commutes (x : F)`.

Express the relevant statement in the definitionally equal form `cO σ (algebraMap (𝓞 F) (𝓞 E) x) ∈ P.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal`. Rewrite using `[this]`.
-/
theorem under_cP (hσ : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    (cP hσ P).under (𝓞 F) = P.under (𝓞 F) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have : cO σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x := by
    apply RingOfIntegers.ext
    rw [cO_coe]
    exact σ.commutes (x : F)
  change cO σ (algebraMap (𝓞 F) (𝓞 E) x) ∈ P.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal
  rw [this]

/- English proof (translation)
Establish `hle : (Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (cP hσ P).asIdeal`. Introduce `x hx`. Take `⟨t, ht⟩` from `exists_of_conj_eq hσ (x := (x : E) * σ (x : E)) (by rw [map_mul, conj_conj hσ, mul_comm])`. Establish `hint : IsIntegral ℤ t`. Rewrite using `[← isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective]`.

Express the relevant statement in the definitionally equal form `IsIntegral ℤ (algebraMap F E t)`. Rewrite using `[ht]`. Conclude with `(x * cO σ x).isIntegral_coe`. Establish `e : algebraMap (𝓞 F) (𝓞 E) ⟨t, hint⟩ = x * cO σ x` using `RingOfIntegers.ext ht`. Establish `h1 : (⟨t, hint⟩ : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal`.

Express the relevant statement in the definitionally equal form `algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ hx`. Rewrite `h1` using `[h]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 F) (𝓞 E) _ ∈ P.asIdeal at h1`.

Rewrite `h1` using `[e]`. Conclude with `P.isPrime.mem_or_mem h1`. Conclude with `(Ideal.subset_union.1 hle).imp eq_of_le eq_of_le`.
-/
theorem eq_or_eq_cP (hσ : IsCMExt F E σ) {P Q : HeightOneSpectrum (𝓞 E)}
    (h : Q.under (𝓞 F) = P.under (𝓞 F)) : Q = P ∨ Q = cP hσ P := by
  have hle : (Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (cP hσ P).asIdeal := by
    intro x hx
    obtain ⟨t, ht⟩ := exists_of_conj_eq hσ (x := (x : E) * σ (x : E))
      (by rw [map_mul, conj_conj hσ, mul_comm])
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective]
      change IsIntegral ℤ (algebraMap F E t)
      rw [ht]
      exact (x * cO σ x).isIntegral_coe
    have e : algebraMap (𝓞 F) (𝓞 E) ⟨t, hint⟩ = x * cO σ x := RingOfIntegers.ext ht
    have h1 : (⟨t, hint⟩ : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal := by
      change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    change algebraMap (𝓞 F) (𝓞 E) _ ∈ P.asIdeal at h1
    rw [e] at h1
    exact P.isPrime.mem_or_mem h1
  exact (Ideal.subset_union.1 hle).imp eq_of_le eq_of_le

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.UG.P.afsplitF v 1, Formalism.UG.P.afsplitF_self v 1, fun w hw => Formalism.UG.P.afsplitF_ne v w hw 1⟩`.
-/
theorem exists_single (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ α : FiniteAdeleRing (𝓞 K) K, α v = 1 ∧ ∀ w, w ≠ v → α w = 0 :=
  ⟨Formalism.UG.P.afsplitF v 1, Formalism.UG.P.afsplitF_self v 1, fun w hw => Formalism.UG.P.afsplitF_ne v w hw 1⟩

/- English proof (translation)
Take `⟨α, h1, h0⟩` from `exists_single F v`. Conclude with `⟨_, α, rfl, h1, h0⟩`.
-/
theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 F)) : ∃ ε, IsPlaceIdem F v ε := by
  obtain ⟨α, h1, h0⟩ := exists_single F v
  exact ⟨_, α, rfl, h1, h0⟩

section

variable {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem ev_mul (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a * b) Q = Φ a Q * Φ b Q := by
  rw [map_mul]; rfl

/- English proof (translation)
Rewrite using `[map_add]`. Both sides reduce to the same expression.
-/
theorem ev_add (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a + b) Q = Φ a Q + Φ b Q := by
  rw [map_add]; rfl

/- English proof (translation)
Rewrite using `[map_zero]`. Both sides reduce to the same expression.
-/
theorem ev_zero (Q : HeightOneSpectrum (𝓞 E)) : Φ 0 Q = 0 := by rw [map_zero]; rfl

variable (hΦ : Comp Φ)
include hΦ

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `hΦ.1 _ (by rw [RingHom.map_sub, h1, sub_self]) ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `FiniteAdeleRing.ext _ h2`.
-/
theorem Comp.ext' {a b : AE F E} (h1 : infPart F E a = infPart F E b) (h2 : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  rw [← sub_eq_zero]
  refine hΦ.1 _ (by rw [RingHom.map_sub, h1, sub_self]) ?_
  rw [map_sub, sub_eq_zero]
  exact FiniteAdeleRing.ext _ h2

/- English proof (translation)
Take `⟨α, h1, h0⟩` from `exists_single E P`. Take `⟨z, h2, rfl⟩` from `hΦ.2.1 α`. Conclude with `⟨z, h2, h1, h0⟩`.
-/
theorem exists_delta (P : HeightOneSpectrum (𝓞 E)) : ∃ e, IsDelta Φ P e := by
  obtain ⟨α, h1, h0⟩ := exists_single E P
  obtain ⟨z, h2, rfl⟩ := hΦ.2.1 α
  exact ⟨z, h2, h1, h0⟩

/- English proof (translation)
Use `hΦ.ext' (h.1.trans h'.1.symm) fun Q => ?_` and prove the remaining obligations. Distinguish the cases in `hQ : Q = P`. Rewrite using `[hQ, h.2.1, h'.2.1]`. Rewrite using `[h.2.2 Q hQ, h'.2.2 Q hQ]`.
-/
theorem delta_unique {P : HeightOneSpectrum (𝓞 E)} {e e' : AE F E} (h : IsDelta Φ P e)
    (h' : IsDelta Φ P e') : e = e' := by
  refine hΦ.ext' (h.1.trans h'.1.symm) fun Q => ?_
  by_cases hQ : Q = P
  · rw [hQ, h.2.1, h'.2.1]
  · rw [h.2.2 Q hQ, h'.2.2 Q hQ]

/- English proof (translation)
Use `delta_unique hΦ ⟨by rw [map_mul, h.1, zero_mul], by rw [ev_mul, h.2.1, one_mul], fun Q hQ => ?_⟩ h` and prove the remaining obligations. Rewrite using `[ev_mul, h.2.2 Q hQ, zero_mul]`.
-/
theorem delta_idem {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (h : IsDelta Φ P e) : e * e = e := by
  refine delta_unique hΦ ⟨by rw [map_mul, h.1, zero_mul], by rw [ev_mul, h.2.1, one_mul], fun Q hQ => ?_⟩ h
  rw [ev_mul, h.2.2 Q hQ, zero_mul]

/- English proof (translation)
Rewrite using `[hΦ.2.2.2.1, not_forall]`. Use `exists_congr fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_mul, hΦ.2.2.1]`. Distinguish the cases in `h0 : Φ e Q = 0`. Rewrite using `[h0, zero_mul]`.

Conclude with `iff_of_false (fun h => h (zero_mem _)) (fun h => h.1 rfl)`. Establish `h1 : Φ e Q = 1` using `mul_left_cancel₀ h0 (by rw [← ev_mul, he, mul_one])`. Rewrite using `[h1, one_mul]`. Conclude with `((inv_mem_iff Q hx).not.trans not_not).trans (and_iff_right one_ne_zero).symm`.
-/
theorem not_int_iff {e : AE F E} (he : e * e = e) {x : 𝓞 E} (hx : x ≠ 0) :
    finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E ↔ ∃ Q, Φ e Q ≠ 0 ∧ x ∈ Q.asIdeal := by
  rw [hΦ.2.2.2.1, not_forall]
  refine exists_congr fun Q => ?_
  rw [ev_mul, hΦ.2.2.1]
  by_cases h0 : Φ e Q = 0
  · rw [h0, zero_mul]
    exact iff_of_false (fun h => h (zero_mem _)) (fun h => h.1 rfl)
  · have h1 : Φ e Q = 1 := mul_left_cancel₀ h0 (by rw [← ev_mul, he, mul_one])
    rw [h1, one_mul]
    exact ((inv_mem_iff Q hx).not.trans not_not).trans (and_iff_right one_ne_zero).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ∀ Q, Φ e Q ≠ 0 → Q = P` using `fun Q hQ => eq_of_le fun x hx => by`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`.

Conclude with `zero_mem _`. Conclude with `(h x hx0).2 ((not_int_iff hΦ he hx0).2 ⟨Q, hQ, hx⟩)`. Use `⟨h0, ?_, fun Q hQ => by_contra fun h2 => hQ (h1 Q h2)⟩` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Take `⟨Q, hQ, -⟩` from `(not_int_iff hΦ he hx0).1 ((h x hx0).1 hx)`.

Rewrite `hQ` using `[h1 Q hQ]`. Conclude with `mul_left_cancel₀ hQ (by rw [← ev_mul, he, mul_one])`. Introduce `h x hx`. Rewrite using `[not_int_iff hΦ he hx]`. Use `⟨fun hP => ⟨P, by rw [h.2.1]; exact one_ne_zero, hP⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨Q, h1, h2⟩`. Establish `: Q = P` using `by_contra fun h3 => h1 (h.2.2 Q h3)`. Conclude with `this ▸ h2`.
-/
theorem tie_iff {e : AE F E} (he : e * e = e) (h0 : infPart F E e = 0)
    (P : HeightOneSpectrum (𝓞 E)) : Comparison₂ P e ↔ IsDelta Φ P e := by
  constructor
  · intro h
    have h1 : ∀ Q, Φ e Q ≠ 0 → Q = P := fun Q hQ => eq_of_le fun x hx => by
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem _
      · exact (h x hx0).2 ((not_int_iff hΦ he hx0).2 ⟨Q, hQ, hx⟩)
    refine ⟨h0, ?_, fun Q hQ => by_contra fun h2 => hQ (h1 Q h2)⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (not_int_iff hΦ he hx0).1 ((h x hx0).1 hx)
    rw [h1 Q hQ] at hQ
    exact mul_left_cancel₀ hQ (by rw [← ev_mul, he, mul_one])
  · intro h x hx
    rw [not_int_iff hΦ he hx]
    refine ⟨fun hP => ⟨P, by rw [h.2.1]; exact one_ne_zero, hP⟩, ?_⟩
    rintro ⟨Q, h1, h2⟩
    have : Q = P := by_contra fun h3 => h1 (h.2.2 Q h3)
    exact this ▸ h2

/- English proof (translation)
Establish `he` using `delta_idem hΦ h`. Use `(tie_iff hΦ (by rw [← map_mul, he]) (by rw [(parts_cA e).1, h.1, map_zero]) _).1 ?_` and prove the remaining obligations. Conclude with `((tie_iff hΦ he h.1 P).2 h).conj hσ`.
-/
theorem delta_conj (hσ : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (h : IsDelta Φ P e) :
    IsDelta Φ (cP hσ P) (cA σ e) := by
  have he := delta_idem hΦ h
  refine (tie_iff hΦ (by rw [← map_mul, he]) (by rw [(parts_cA e).1, h.1, map_zero]) _).1 ?_
  exact ((tie_iff hΦ he h.1 P).2 h).conj hσ

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Use `⟨TensorProduct.zero_tmul _ _, fun Q hQ => ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Substitute `hQ` using the available equality. Rewrite using `[hΦ.2.2.2.2]`. Conclude with `(congrArg _ h1).trans (map_one _)`.

Rewrite using `[hΦ.2.2.2.2]`. Conclude with `(congrArg _ (h0 _ hQ)).trans (map_zero _)`.
-/
theorem place_comp {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε) :
    infPart F E (algebraMap _ (AE F E) ε) = 0 ∧
    (∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → Φ (algebraMap _ _ ε) Q = 1) ∧
    (∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) ≠ v → Φ (algebraMap _ _ ε) Q = 0) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine ⟨TensorProduct.zero_tmul _ _, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · subst hQ
    rw [hΦ.2.2.2.2]
    exact (congrArg _ h1).trans (map_one _)
  · rw [hΦ.2.2.2.2]
    exact (congrArg _ (h0 _ hQ)).trans (map_zero _)

/- English proof (translation)
Take `⟨e, he⟩` from `exists_delta hΦ P`. Take `⟨ε, hε⟩` from `exists_placeIdem (P.under (𝓞 F))`. Take `⟨h0, h1, h2⟩` from `place_comp hΦ hε`. Establish `hi` using `delta_idem hΦ he`. Establish `ht` using `(tie_iff hΦ hi he.1 P).2 he`.

Distinguish the cases in `hc : cP hσ P = P`. Use `⟨e, e, hi, Or.inr ⟨rfl, ⟨_, ε, hε, delta_unique hΦ he ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => ?_⟩⟩, ht⟩⟩` and prove the remaining obligations. Conclude with `(eq_or_eq_cP hσ h).elim hQ fun h => hQ (h.trans hc)`. Establish `he'` using `delta_conj hΦ hσ he`. Use `⟨e, _, hi, Or.inl ⟨⟨⟨hi, ?_, _, ε, hε, ?_⟩, ht⟩, rfl⟩⟩` and prove the remaining obligations.

Use `hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_mul, ev_zero]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[he'.2.2 Q (Ne.symm hc), mul_zero]`.

Rewrite using `[he.2.2 Q hQ, zero_mul]`. Use `hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_add]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality.

Rewrite using `[he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]`. Distinguish the cases in `hQ' : Q = cP hσ P`. Substitute `hQ'` using the available equality. Rewrite using `[he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP hσ P)]`. Rewrite using `[he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP hσ h).elim hQ hQ']`.
-/
theorem exists_isPrimeIdem_of_comp (hσ : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ e f, e * e = e ∧ IsPrimeIdem σ P e f := by
  obtain ⟨e, he⟩ := exists_delta hΦ P
  obtain ⟨ε, hε⟩ := exists_placeIdem (P.under (𝓞 F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hi := delta_idem hΦ he
  have ht := (tie_iff hΦ hi he.1 P).2 he
  by_cases hc : cP hσ P = P
  · refine ⟨e, e, hi, Or.inr ⟨rfl, ⟨_, ε, hε,
      delta_unique hΦ he ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => ?_⟩⟩, ht⟩⟩
    exact (eq_or_eq_cP hσ h).elim hQ fun h => hQ (h.trans hc)
  · have he' := delta_conj hΦ hσ he
    refine ⟨e, _, hi, Or.inl ⟨⟨⟨hi, ?_, _, ε, hε, ?_⟩, ht⟩, rfl⟩⟩
    · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
      rw [ev_mul, ev_zero]
      by_cases hQ : Q = P
      · subst hQ
        rw [he'.2.2 Q (Ne.symm hc), mul_zero]
      · rw [he.2.2 Q hQ, zero_mul]
    · refine hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_
      rw [ev_add]
      by_cases hQ : Q = P
      · subst hQ
        rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
      · by_cases hQ' : Q = cP hσ P
        · subst hQ'
          rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP hσ P)]
        · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP hσ h).elim hQ hQ']

end

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `exists_comp F E`. Conclude with `exists_isPrimeIdem_of_comp hΦ hσ P`.
-/
theorem exists_isPrimeIdem (hσ : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ e f, e * e = e ∧ IsPrimeIdem σ P e f := by
  obtain ⟨Φ, hΦ⟩ := exists_comp F E
  exact exists_isPrimeIdem_of_comp hΦ hσ P

/- English proof (translation)
Take `⟨e, f, he, h⟩` from `exists_isPrimeIdem hσ P`. Take `⟨ϖ, h1, h2⟩` from `Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1`. Rewrite `h1` using `[pow_one]`. Establish `h0 : (ϖ : E) ≠ 0` using `fun h0 => h2 (by`. Establish `: ϖ = 0` using `RingOfIntegers.ext h0`.

Rewrite using `[this]`. Conclude with `zero_mem _)`. Establish `hm : incA F E (ϖ : E) * incA F E (ϖ : E)⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ h0, map_one]`. Establish `hu : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1`.

Generalize the expression as in `incA F E (ϖ : E) = a at hm ⊢`. Generalize the expression as in `incA F E (ϖ : E)⁻¹ = b at hm ⊢`. Take the linear combination `e * e * hm + (2 - a - b) * he`. Conclude with `⟨Units.mkOfMulEqOne _ _ hu, e, f, ϖ, h, h1, h2, rfl⟩`.
-/
theorem exists_isUnifIdele (hσ : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ x, IsUnifIdele σ P x := by
  obtain ⟨e, f, he, h⟩ := exists_isPrimeIdem hσ P
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
  rw [pow_one] at h1
  have h0 : (ϖ : E) ≠ 0 := fun h0 => h2 (by
    have : ϖ = 0 := RingOfIntegers.ext h0
    rw [this]; exact zero_mem _)
  have hm : incA F E (ϖ : E) * incA F E (ϖ : E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  have hu : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1 := by
    generalize incA F E (ϖ : E) = a at hm ⊢
    generalize incA F E (ϖ : E)⁻¹ = b at hm ⊢
    linear_combination e * e * hm + (2 - a - b) * he
  exact ⟨Units.mkOfMulEqOne _ _ hu, e, f, ϖ, h, h1, h2, rfl⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ P`. Take `⟨e, f, -, h⟩` from `exists_isPrimeIdem hσ P`. Unfold `chiAt`. Rewrite using `[dif_pos ⟨⟨e, f, h, fun _ _ _ _ => rfl⟩, exists_isUnifIdele hσ P⟩]`. Both sides reduce to the same expression.
-/
theorem chiAt_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), chiAt σ (1 : (AE F E)ˣ →* Circle) P = 1 := by
  intro F E _ _ _ _ _ σ hσ P
  obtain ⟨e, f, -, h⟩ := exists_isPrimeIdem hσ P
  unfold chiAt
  rw [dif_pos ⟨⟨e, f, h, fun _ _ _ _ => rfl⟩, exists_isUnifIdele hσ P⟩]
  rfl

end GlobalTheory.CMPrimeIdele
