import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
open NumberField IsDedekindDomain

namespace GlobalTheory.QNorm

/- English proof (translation)
Assemble the required witnesses or components as `⟨{ toFun := fun x => x.2 v map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩`.
-/
theorem exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Establish `hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ)`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal` using `⟨_, hφ, rfl⟩`.

Use `⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩` and prove the remaining obligations. Establish `he` using `InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)`. Use `he.trans ?_` and prove the remaining obligations. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]`.

Simplify using the standard rewrite rules.
-/
theorem exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

open Classical in

noncomputable def adeleOn (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) : AdeleRing (𝓞 F) F :=
  (algebraMap F (InfiniteAdeleRing F) z,
    (⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) z else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := hv
      simp only [if_neg hv', SetLike.mem_coe]
      exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
The claim follows from `if_pos hv`.
-/
theorem adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv

/- English proof (translation)
The claim follows from `if_neg hv`.
-/
theorem adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := if_neg hv

/- English proof (translation)
Use `Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ hz, map_one]`. Express the relevant statement in the definitionally equal form `(adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1`. Distinguish the cases in `hv : v ∈ S`.

Rewrite using `[adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul, mul_inv_cancel₀ hz, map_one]`. Rewrite using `[adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]`.
-/
theorem adeleOn_mul_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]

/- English proof (translation)
Use `⟨a, b, ?_⟩` and prove the remaining obligations. Establish `ht : φ (t : F) ≠ 0` using `by simp`. Rewrite using `[Units.val_div_eq_div_val, map_div₀, h]`. Clear the denominators using the available nonvanishing facts.
-/
theorem div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp

/- English proof (translation)
Introduce `F _ _ δ hsq`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Conclude with `hsq IsSquare.zero`. Take `⟨S, hS, hδ, hadj⟩` from `GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq`.

Establish `hne` using `sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq`. Simplify using `only [Units.val_mk0] at hadj hne`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hne (Subgroup.eq_top_iff' _ |>.2 hcon)`. Use `⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩` and prove the remaining obligations. Use `replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`.

Rewrite `h` using `[map_zero, zero_mul]`. Establish `h1 : algebraMap F (InfiniteAdeleRing F) z = 0` using `congrArg Prod.fst h`. Conclude with `z.ne_zero ((map_eq_zero _).1 h1)`. Establish `hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t * (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2)`. Introduce `v`.

Take `⟨e, he, he'⟩` from `exists_adele_finite_component F v`. Use `⟨e x, e y, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']`. Establish `h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S`. Use `sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)` and prove the remaining obligations.

Take `⟨a, b, hab⟩` from `hfin v`. Rewrite `hab` using `[adeleOn_snd_of_notMem F S _ hv]`. Establish `h2` using `div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b (by simpa using hab)`. Rewrite `h2` using `[one_div, inv_mem_iff]`. Then use the resulting hypothesis. Establish `h2 : z / Units.mk0 t ht ∈ locNorm F δ S`.

Use `⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_, Subgroup.mem_iInf.2 fun σ => ?_⟩` and prove the remaining obligations. Take `⟨a, b, hab⟩` from `hfin v`. Rewrite `hab` using `[adeleOn_snd_of_mem F S _ hv]`. Conclude with `div_mem_normSub _ δ z (Units.mk0 t ht) a b hab`. Take `⟨e, he⟩` from `exists_infiniteAdele_real_component F σ`.

Use `div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_` and prove the remaining obligations. Establish `h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t * (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2)` using `congrArg Prod.fst h`. Establish `h4` using `congrArg e h3`. Rewrite `h4` using `[map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he]`. Then use the resulting hypothesis. Establish `h3` using `mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1`.

Rewrite `h3` using `[div_mul_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_idele_not_mul_norm : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3

end GlobalTheory.QNorm
