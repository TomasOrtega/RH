import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global MulAction NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Complex

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/- English proof (translation)
The claim follows from `NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1 (NumberField.InfinitePlace.isUnramified_iff.2 (Or.inr hw))`.
-/
theorem stabilizer_eq_bot_of_isComplex {w : NumberField.InfinitePlace L}
    (hw : (w.comap (algebraMap K L)).IsComplex) : MulAction.stabilizer (L ≃ₐ[K] L) w = ⊥ :=
  NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1
    (NumberField.InfinitePlace.isUnramified_iff.2 (Or.inr hw))

/- English proof (translation)
The claim follows from `NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1 (NumberField.InfinitePlace.isUnramified_iff.2 (Or.inl hw))`.
-/
theorem stabilizer_eq_bot_of_isReal {w : NumberField.InfinitePlace L} (hw : w.IsReal) :
    MulAction.stabilizer (L ≃ₐ[K] L) w = ⊥ :=
  NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1
    (NumberField.InfinitePlace.isUnramified_iff.2 (Or.inl hw))

end Complex

section InfPlace

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1} (L : FiniteSubfield) [Fact (K ≤ L)]

/- English proof (translation)
Use `set w₀ := infPlaceOfEmbedding ι L`. Establish `hcomap : (w₀ : NumberField.InfinitePlace L.1).comap ((τ : L.1 ≃+* L.1) : L.1 →+* L.1) = τ⁻¹ • (w₀ : NumberField.InfinitePlace L.1)` using `AdeleBaseChange.comap_eq_inv_smul τ w₀`. Establish `hu : ((w₀ : NumberField.InfinitePlace L.1).comap ((τ : L.1 ≃+* L.1) : L.1 →+* L.1)).LiesOver v`. Rewrite using `[GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap, GroundTheory.Global.InfinitePlace.comap_smul_algebraMap, ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]`. Conclude with `w₀.2`.

Set `u : v.placesOver L.1` to `⟨_, hu⟩`. Set `j : (u : NumberField.InfinitePlace L.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion` to `(infCompletionEmbedding ι L).comp { AdeleBaseChange.infiniteCompletionMap (τ : L.1 ≃+* L.1) w₀ with commutes' := infiniteCompletionMap_algebraMap_completion L τ w₀ }`. Establish `hj : ∀ x : L.1, j (algebraMap L.1 _ x) = ι' x`. Introduce `x`. Express the relevant statement in the definitionally equal form `infCompletionEmbedding ι L (AdeleBaseChange.infiniteCompletionMap (τ : L.1 ≃+* L.1) w₀ (algebraMap L.1 _ x)) = ι' x`.

Rewrite using `[AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap, AlgEquiv.coe_ringEquiv, h x]`. Establish `e` using `congrArg Subtype.val (eq_infPlaceOfEmbedding ι' L j hj)`. Rewrite using `[← e]`. Conclude with `hcomap`.
-/
theorem infPlaceOfEmbedding_eq_inv_smul (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (τ : L.1 ≃ₐ[K.1] L.1) (h : ∀ x : L.1, ι' x = ι (τ x)) :
    (infPlaceOfEmbedding ι' L : NumberField.InfinitePlace L.1) =
      τ⁻¹ • (infPlaceOfEmbedding ι L : NumberField.InfinitePlace L.1) := by
  set w₀ := infPlaceOfEmbedding ι L
  have hcomap : (w₀ : NumberField.InfinitePlace L.1).comap ((τ : L.1 ≃+* L.1) : L.1 →+* L.1) =
      τ⁻¹ • (w₀ : NumberField.InfinitePlace L.1) :=
    AdeleBaseChange.comap_eq_inv_smul τ w₀
  have hu : ((w₀ : NumberField.InfinitePlace L.1).comap
      ((τ : L.1 ≃+* L.1) : L.1 →+* L.1)).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap,
      GroundTheory.Global.InfinitePlace.comap_smul_algebraMap,
      ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact w₀.2
  let u : v.placesOver L.1 := ⟨_, hu⟩
  let j : (u : NumberField.InfinitePlace L.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion :=
    (infCompletionEmbedding ι L).comp
      { AdeleBaseChange.infiniteCompletionMap (τ : L.1 ≃+* L.1) w₀ with
        commutes' := infiniteCompletionMap_algebraMap_completion L τ w₀ }
  have hj : ∀ x : L.1, j (algebraMap L.1 _ x) = ι' x := by
    intro x
    change infCompletionEmbedding ι L (AdeleBaseChange.infiniteCompletionMap
      (τ : L.1 ≃+* L.1) w₀ (algebraMap L.1 _ x)) = ι' x
    rw [AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap,
      AlgEquiv.coe_ringEquiv, h x]
  have e := congrArg Subtype.val (eq_infPlaceOfEmbedding ι' L j hj)
  rw [← e]
  exact hcomap

end InfPlace

section Real

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : NumberField.InfinitePlace K.1 // v.IsReal},
    ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {L : FiniteSubfield} [Fact (K ≤ L)] [IsGalois K.1 L.1]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

/- English proof (translation)
Rewrite using `[show ((gsRestrictGal hL (gsRealFamily S ιr v g) x : L.1) : ℚ̄) = ((gsEmbedding hL (gsRestrictGal hL (gsRealFamily S ιr v g) x) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) from rfl, gsEmbedding_gsRestrictGal, gsRealFamily_apply]`. Both sides reduce to the same expression.
-/
theorem apply_gsRestrictGal_gsRealFamily (v : {v : NumberField.InfinitePlace K.1 // v.IsReal})
    (g : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (x : L.1) :
    ιr v ((gsRestrictGal hL (gsRealFamily S ιr v g) x : L.1) : ℚ̄) = g (ιr v (x : ℚ̄)) := by
  rw [show ((gsRestrictGal hL (gsRealFamily S ιr v g) x : L.1) : ℚ̄) =
      ((gsEmbedding hL (gsRestrictGal hL (gsRealFamily S ιr v g) x) :
        maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) from rfl, gsEmbedding_gsRestrictGal, gsRealFamily_apply]
  rfl

/- English proof (translation)
Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[mem_stabilizer_iff]`. Use `set τ := gsRestrictGal hL (gsRealFamily S ιr v g)`. Establish `e1` using `infPlaceOfEmbedding_eq_inv_smul L (ιr v) (((g : AlgebraicClosure v.1.Completion ≃ₐ[v.1.Completion] AlgebraicClosure v.1.Completion).toAlgHom.restrictScalars K.1).comp (ιr v)) τ fun x => (apply_gsRestrictGal_gsRealFamily S ιr hL v g x).symm`. Rewrite `e1` using `[infPlaceOfEmbedding_gal_comp]`.

Express the relevant statement in the definitionally equal form `τ • (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) = _`. Use `conv_lhs => rw [e1]`. Conclude with `smul_inv_smul τ _`.
-/
theorem gsRealDecompGroup_le_stabilizer (v : {v : NumberField.InfinitePlace K.1 // v.IsReal}) :
    gsRealDecompGroup S ιr hL v ≤
      MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) := by
  rintro _ ⟨g, rfl⟩
  rw [mem_stabilizer_iff]
  set τ := gsRestrictGal hL (gsRealFamily S ιr v g)
  have e1 := infPlaceOfEmbedding_eq_inv_smul L (ιr v)
    (((g : AlgebraicClosure v.1.Completion ≃ₐ[v.1.Completion] AlgebraicClosure v.1.Completion).toAlgHom.restrictScalars
      K.1).comp (ιr v)) τ fun x => (apply_gsRestrictGal_gsRealFamily S ιr hL v g x).symm
  rw [infPlaceOfEmbedding_gal_comp] at e1
  change τ • (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) = _
  conv_lhs => rw [e1]
  exact smul_inv_smul τ _

/- English proof (translation)
Use `set w₀ : NumberField.InfinitePlace L.1 := (infPlaceOfEmbedding (ιr v) L).1`. Establish `hle` using `gsRealDecompGroup_le_stabilizer S ιr hL v`. Distinguish the cases in `hw : w₀.IsReal`. Rewrite `hle`, the goal using `[stabilizer_eq_bot_of_isReal hw]`. Conclude with `(le_bot_iff.1 hle).symm`.

Establish `hcomap : w₀.comap (algebraMap K.1 L.1) = v.1`. Use `(infPlaceOfEmbedding (ιr v) L).2` as an intermediate fact. Conclude with `NumberField.InfinitePlace.LiesOver.comap_eq _ _`. Establish `hram : ¬ NumberField.InfinitePlace.IsUnramified K.1 w₀`. Rewrite using `[NumberField.InfinitePlace.isUnramified_iff, hcomap]`.

Conclude with `not_or.2 ⟨hw, NumberField.InfinitePlace.not_isComplex_iff_isReal.2 v.2⟩`. Establish `h2` using `NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram`. Establish `hne : gsRealDecompGroup S ιr hL v ≠ ⊥`. Introduce `hbot`. Apply `hw` to reduce the goal to its premises.

Use `(isReal_infPlaceOfEmbedding_iff L v.2 (ιr v)).2 fun g x => ?_` and prove the remaining obligations. Establish `h1 : gsRestrictGal hL (gsRealFamily S ιr v g) = 1`. Establish `hmem : gsRestrictGal hL (gsRealFamily S ιr v g) ∈ gsRealDecompGroup S ιr hL v` using `⟨g, rfl⟩`. Rewrite `hmem` using `[hbot]`. Conclude with `hmem`.

Rewrite using `[← apply_gsRestrictGal_gsRealFamily S ιr hL v g x, h1]`. Both sides reduce to the same expression. Establish `hfin : Finite (gsRealDecompGroup S ιr hL v)` using `inferInstance`. Establish `h1` using `(Subgroup.one_lt_card_iff_ne_bot _).2 hne`. Use `symm`.

Conclude with `Subgroup.eq_of_le_of_card_ge hle (by omega)`.
-/
theorem stabilizer_infPlaceOfEmbedding (v : {v : NumberField.InfinitePlace K.1 // v.IsReal}) :
    MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) =
      gsRealDecompGroup S ιr hL v := by
  set w₀ : NumberField.InfinitePlace L.1 := (infPlaceOfEmbedding (ιr v) L).1
  have hle := gsRealDecompGroup_le_stabilizer S ιr hL v
  by_cases hw : w₀.IsReal
  · rw [stabilizer_eq_bot_of_isReal hw] at hle ⊢
    exact (le_bot_iff.1 hle).symm
  · have hcomap : w₀.comap (algebraMap K.1 L.1) = v.1 := by
      have := (infPlaceOfEmbedding (ιr v) L).2
      exact NumberField.InfinitePlace.LiesOver.comap_eq _ _
    have hram : ¬ NumberField.InfinitePlace.IsUnramified K.1 w₀ := by
      rw [NumberField.InfinitePlace.isUnramified_iff, hcomap]
      exact not_or.2 ⟨hw, NumberField.InfinitePlace.not_isComplex_iff_isReal.2 v.2⟩
    have h2 := NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hne : gsRealDecompGroup S ιr hL v ≠ ⊥ := by
      intro hbot
      apply hw
      refine (isReal_infPlaceOfEmbedding_iff L v.2 (ιr v)).2 fun g x => ?_
      have h1 : gsRestrictGal hL (gsRealFamily S ιr v g) = 1 := by
        have hmem : gsRestrictGal hL (gsRealFamily S ιr v g) ∈ gsRealDecompGroup S ιr hL v := ⟨g, rfl⟩
        rw [hbot] at hmem
        exact hmem
      rw [← apply_gsRestrictGal_gsRealFamily S ιr hL v g x, h1]
      rfl
    have hfin : Finite (gsRealDecompGroup S ιr hL v) := inferInstance
    have h1 := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    symm
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)

variable {k N : Type*} [Field k] [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  (σN : Representation k (L.1 ≃ₐ[K.1] L.1) N)

omit [FiniteDimensional k N] [IsGalois K.1 L.1] in

/- English proof (translation)
Establish `htop : Representation.invariants (σN.comp (⊥ : Subgroup (L.1 ≃ₐ[K.1] L.1)).subtype) = ⊤`. Use `eq_top_iff.2 fun x _ g => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `g`. Rewrite `hg` using `[Subgroup.mem_bot]`. Substitute `hg` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[htop, finrank_top]`.
-/
theorem finrank_invariants_comp_bot :
    Module.finrank k (Representation.invariants (σN.comp (⊥ : Subgroup (L.1 ≃ₐ[K.1] L.1)).subtype)) =
      Module.finrank k N := by
  have htop : Representation.invariants (σN.comp (⊥ : Subgroup (L.1 ≃ₐ[K.1] L.1)).subtype) = ⊤ := by
    refine eq_top_iff.2 fun x _ g => ?_
    obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  rw [htop, finrank_top]

open Classical in

/- English proof (translation)
Set `_` to `Fintype.ofFinite (orbitRel.Quotient (L.1 ≃ₐ[K.1] L.1) (NumberField.InfinitePlace L.1))`. Rewrite using `[finrank_invariants_funPermRep_tprod]`. Use `set e := NumberField.InfinitePlace.orbitRelEquiv (k := K.1) (K := L.1)`. Use `set f : orbitRel.Quotient (L.1 ≃ₐ[K.1] L.1) (NumberField.InfinitePlace L.1) → ℕ := fun ω => Module.finrank k (Representation.invariants (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) ω.out).subtype))`. Rewrite using `[← e.symm.sum_comp f, ← Fintype.sum_subtype_add_sum_subtype (fun v : NumberField.InfinitePlace K.1 => v.IsReal)]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `hv : e.symm v.1 = Quotient.mk'' (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1)`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[Equiv.apply_symm_apply, NumberField.InfinitePlace.orbitRelEquiv_apply_mk'']`.

Use `(infPlaceOfEmbedding (ιr v) L).2` as an intermediate fact. Conclude with `(NumberField.InfinitePlace.LiesOver.comap_eq _ _).symm`. Express the relevant statement in the definitionally equal form `f (e.symm v.1) = _`. Rewrite using `[hv, ← stabilizer_infPlaceOfEmbedding S ιr hL v]`. Establish `h1` using `orbitMover_smul (Γ := L.1 ≃ₐ[K.1] L.1) (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1)`.

Express the relevant statement in the definitionally equal form `Module.finrank k (Representation.invariants (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (Quotient.mk (orbitRel _ _) (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1)).out).subtype)) = _`. Use `conv_rhs => rw [← h1]`. Rewrite using `[finrank_invariants_stabilizer_smul]`. Establish `hc : ∀ v : {v : NumberField.InfinitePlace K.1 // ¬ v.IsReal}, f (e.symm v.1) = Module.finrank k N`. Introduce `v`.

Establish `hcx : ((e.symm v.1).out.comap (algebraMap K.1 L.1)).IsComplex`. Establish `h` using `e.apply_symm_apply v.1`. Use `conv_lhs at h => rw [← Quotient.out_eq (e.symm v.1)]`. Rewrite `h` using `[← Quotient.mk''_eq_mk, NumberField.InfinitePlace.orbitRelEquiv_apply_mk'']`. Rewrite using `[h]`.

Conclude with `NumberField.InfinitePlace.not_isReal_iff_isComplex.1 v.2`. Express the relevant statement in the definitionally equal form `Module.finrank k (Representation.invariants (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (e.symm v.1).out).subtype)) = _`. Rewrite using `[stabilizer_eq_bot_of_isComplex hcx, finrank_invariants_comp_bot]`. Rewrite using `[Finset.sum_congr rfl fun v _ => hc v, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Use `congr 1`.

Conclude with `Fintype.card_congr (Equiv.subtypeEquivRight fun v => NumberField.InfinitePlace.not_isReal_iff_isComplex)`.
-/
theorem finrank_invariants_funPermRep_infinitePlace :
    Module.finrank k ((funPermRep k (L.1 ≃ₐ[K.1] L.1)
        (NumberField.InfinitePlace L.1)).tprod σN).invariants =
      ∑ v : {v : NumberField.InfinitePlace K.1 // v.IsReal},
          Module.finrank k (Representation.invariants (σN.comp (gsRealDecompGroup S ιr hL v).subtype)) +
        Fintype.card {v : NumberField.InfinitePlace K.1 // v.IsComplex} * Module.finrank k N := by
  classical
  let _ := Fintype.ofFinite
    (orbitRel.Quotient (L.1 ≃ₐ[K.1] L.1) (NumberField.InfinitePlace L.1))
  rw [finrank_invariants_funPermRep_tprod]
  set e := NumberField.InfinitePlace.orbitRelEquiv (k := K.1) (K := L.1)
  set f : orbitRel.Quotient (L.1 ≃ₐ[K.1] L.1) (NumberField.InfinitePlace L.1) → ℕ := fun ω =>
    Module.finrank k (Representation.invariants
      (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) ω.out).subtype))
  rw [← e.symm.sum_comp f, ← Fintype.sum_subtype_add_sum_subtype (fun v : NumberField.InfinitePlace K.1 => v.IsReal)]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    have hv : e.symm v.1 = Quotient.mk'' (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) := by
      apply e.injective
      rw [Equiv.apply_symm_apply, NumberField.InfinitePlace.orbitRelEquiv_apply_mk'']
      have := (infPlaceOfEmbedding (ιr v) L).2
      exact (NumberField.InfinitePlace.LiesOver.comap_eq _ _).symm
    change f (e.symm v.1) = _
    rw [hv, ← stabilizer_infPlaceOfEmbedding S ιr hL v]
    have h1 := orbitMover_smul (Γ := L.1 ≃ₐ[K.1] L.1)
      (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1)
    change Module.finrank k (Representation.invariants (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1)
      (Quotient.mk (orbitRel _ _) (infPlaceOfEmbedding (ιr v) L :
        NumberField.InfinitePlace L.1)).out).subtype)) = _
    conv_rhs => rw [← h1]
    rw [finrank_invariants_stabilizer_smul]
  · have hc : ∀ v : {v : NumberField.InfinitePlace K.1 // ¬ v.IsReal}, f (e.symm v.1) = Module.finrank k N := by
      intro v
      have hcx : ((e.symm v.1).out.comap (algebraMap K.1 L.1)).IsComplex := by
        have h := e.apply_symm_apply v.1
        conv_lhs at h => rw [← Quotient.out_eq (e.symm v.1)]
        rw [← Quotient.mk''_eq_mk, NumberField.InfinitePlace.orbitRelEquiv_apply_mk''] at h
        rw [h]
        exact NumberField.InfinitePlace.not_isReal_iff_isComplex.1 v.2
      change Module.finrank k (Representation.invariants
        (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (e.symm v.1).out).subtype)) = _
      rw [stabilizer_eq_bot_of_isComplex hcx, finrank_invariants_comp_bot]
    rw [Finset.sum_congr rfl fun v _ => hc v, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun v =>
      NumberField.InfinitePlace.not_isReal_iff_isComplex)

end Real

end

end GroundTheory.ProfCoh
