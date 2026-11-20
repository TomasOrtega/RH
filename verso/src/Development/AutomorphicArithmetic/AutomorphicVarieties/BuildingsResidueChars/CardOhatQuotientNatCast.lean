import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

/- English proof (translation)
Establish `h` using `Ideal.absNorm_span_singleton (N : 𝓞 F)`. Rewrite `h` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite using `[h, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]`.
-/
private theorem card_int_mod (F : Type) [Field F] [NumberField F] (N : ℕ) :
    Nat.card (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) = N ^ Module.finrank ℚ F := by
  have h := Ideal.absNorm_span_singleton (N : 𝓞 F)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow,
    Int.natAbs_natCast]

/- English proof (translation)
Introduce `F _ _ N hN`. Establish `hm : ∀ x : Af F, x ∈ Ohat F ↔ x ∈ Formalism.UG.intAd F` using `fun x => by`. Rewrite using `[Ohat, Subring.mem_iInf]`. Both sides reduce to the same expression. Set `f : 𝓞 F →+* ↥(Ohat F)` to `((algebraMap F (Af F)).comp (algebraMap (𝓞 F) F)).codRestrict (Ohat F) fun a => mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a)`.

Set `g : (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) →+* (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))})` to `Ideal.quotientMap _ f (by`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _)`. Establish `hg : Function.Surjective g`. Introduce `q`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨s, c, hc, e⟩` from `Formalism.MainNotions.BridgeLevelGenB.dense_mod N hN y.1 ((hm _).1 y.2)`. Use `⟨Ideal.Quotient.mk _ s, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (f s) = _`. Use `(Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨c, (hm _).2 hc⟩, Subtype.ext ?_⟩)).symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y.1 - algebraMap F (Af F) (algebraMap (𝓞 F) F s) = (N : Af F) * c`. Conclude with `sub_eq_of_eq_add' e`. Use `haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) := Nat.finite_of_card_ne_zero (by rw [card_int_mod]; exact pow_ne_zero _ (by omega))`. Conclude with `⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans (card_int_mod F N).le⟩`.
-/
theorem UpperTheory.card_ohat_quotient_natCast :
    UpperTheory.V.Af.CohB.CardOhat := by
  intro F _ _ N hN
  have hm : ∀ x : Af F, x ∈ Ohat F ↔ x ∈ Formalism.UG.intAd F := fun x => by
    rw [Ohat, Subring.mem_iInf]
    rfl
  let f : 𝓞 F →+* ↥(Ohat F) :=
    ((algebraMap F (Af F)).comp (algebraMap (𝓞 F) F)).codRestrict (Ohat F) fun a =>
      mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a)
  let g : (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) →+* (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))}) :=
    Ideal.quotientMap _ f (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨s, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod N hN y.1 ((hm _).1 y.2)
    refine ⟨Ideal.Quotient.mk _ s, ?_⟩
    change Ideal.Quotient.mk _ (f s) = _
    refine (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨c, (hm _).2 hc⟩, Subtype.ext ?_⟩)).symm
    change y.1 - algebraMap F (Af F) (algebraMap (𝓞 F) F s) = (N : Af F) * c
    exact sub_eq_of_eq_add' e
  haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Nat.finite_of_card_ne_zero (by rw [card_int_mod]; exact pow_ne_zero _ (by omega))
  exact ⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans (card_int_mod F N).le⟩
