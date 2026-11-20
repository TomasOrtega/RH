import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTraceStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory

/- English proof (translation)
Establish `hnil : Group.IsNilpotent P` using `hP.isNilpotent`. Establish `hN : K.Normal` using `Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK`. Establish `hQ : IsPGroup p (P ⧸ K)` using `hP.to_quotient K`. Establish `hidx : K.index ≠ 1` using `fun h => hK.1 (Subgroup.index_eq_one.1 h)`. Establish `hdvd : p ∣ Nat.card (P ⧸ K)`.

Take `⟨n, hn⟩` from `IsPGroup.iff_card.1 hQ`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hidx (by rw [Subgroup.index_eq_card, hn, pow_zero])`. Rewrite using `[hn]`.

Conclude with `dvd_pow_self p hn0`. Take `⟨x, hx⟩` from `exists_prime_orderOf_dvd_card' p hdvd`. Establish `hx1 : x ≠ 1`. Introduce and unpack `rfl`. Rewrite `hx` using `[orderOf_one]`.

Conclude with `hp.out.one_lt.ne hx`. Establish `htop : (Subgroup.zpowers x).comap (QuotientGroup.mk' K) = ⊤`. Apply `hK.2` to reduce the goal to its premises. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Introduce `k hk`.

Establish `: QuotientGroup.mk' K k = 1` using `(QuotientGroup.eq_one_iff k).2 hk`. Rewrite using `[Subgroup.mem_comap, this]`. Conclude with `one_mem _`. Introduce `h`. Take `⟨y, rfl⟩` from `QuotientGroup.mk'_surjective K x`.

Establish `: y ∈ K`. Rewrite using `[h, Subgroup.mem_comap]`. Conclude with `Subgroup.mem_zpowers _`. Conclude with `hx1 ((QuotientGroup.eq_one_iff y).2 this)`. Establish `hz : Subgroup.zpowers x = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `z _`. Take `⟨y, rfl⟩` from `QuotientGroup.mk'_surjective K z`. Establish `: y ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K)`. Rewrite using `[htop]`.

Conclude with `Subgroup.mem_top _`. Conclude with `this`. Establish `hcard : Nat.card (P ⧸ K) = p`. Rewrite using `[← hx, ← Nat.card_zpowers, hz, Subgroup.card_top]`. Conclude with `⟨hN, by rw [Subgroup.index_eq_card, hcard]⟩`.
-/
theorem isPGroup_coatom_normal_index_eq {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (K : Subgroup P) (hK : IsCoatom K) :
    K.Normal ∧ K.index = p := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  have hQ : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hidx : K.index ≠ 1 := fun h => hK.1 (Subgroup.index_eq_one.1 h)
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hidx (by rw [Subgroup.index_eq_card, hn, pow_zero])
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have htop : (Subgroup.zpowers x).comap (QuotientGroup.mk' K) = ⊤ := by
    apply hK.2
    refine lt_of_le_of_ne ?_ ?_
    · intro k hk
      have : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [Subgroup.mem_comap, this]
      exact one_mem _
    · intro h
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
      have : y ∈ K := by
        rw [h, Subgroup.mem_comap]
        exact Subgroup.mem_zpowers _
      exact hx1 ((QuotientGroup.eq_one_iff y).2 this)
  have hz : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
    have : y ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← hx, ← Nat.card_zpowers, hz, Subgroup.card_top]
  exact ⟨hN, by rw [Subgroup.index_eq_card, hcard]⟩

/- English proof (translation)
Introduce `l hl F L _ _ _ _ _ hP hζ W hW`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Set `D : Subgroup (L ≃ₐ[F] L)` to `{ carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W} mul_mem' := by`. Introduce `a b ha hb x`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Rewrite using `[AlgEquiv.mul_apply, ha, hb]`. Use the proof step `one_mem' := by intro x; simp`. Use the proof step `inv_mem' := by`. Introduce `a ha x`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Rewrite using `[← ha (a⁻¹ x)]`. Simplify using `}`. It suffices to establish `hD : D = ⊤ by`. Introduce `τ x`. Establish `hτ : τ ∈ D` using `hD ▸ Subgroup.mem_top τ`.

Conclude with `hτ x`. Assume the negation of the conclusion as `hD`. Take `⟨H, hH, hDH⟩` from `(eq_top_or_exists_le_coatom D).resolve_left hD`. Take `⟨hHn, hHi⟩` from `isPGroup_coatom_normal_index_eq hP H hH`. Use `haveI : IsGalois F (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H`.

Establish `hfr : Module.finrank F (IntermediateField.fixedField H) = l`. Establish `h1` using `Module.finrank_mul_finrank F (IntermediateField.fixedField H) L`. Rewrite `h1` using `[IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L, ← H.card_mul_index, hHi, mul_comm (Nat.card H)]`. Conclude with `Nat.eq_of_mul_eq_mul_right Nat.card_pos h1`. Use `haveI : IsCyclic (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H) := isCyclic_of_prime_card (p := l) (by rw [IsGalois.card_aut_eq_finrank, hfr])`.

Take `⟨ζ, hζ⟩` from `hζ`. Establish `hK : (primitiveRoots (Module.finrank F (IntermediateField.fixedField H)) F).Nonempty` using `⟨ζ, by rw [hfr, mem_primitiveRoots hl.pos]; exact hζ⟩`. Take `⟨α, ⟨δ, hδ⟩, hα⟩` from `exists_root_adjoin_eq_top_of_isCyclic F (IntermediateField.fixedField H) hK`. Rewrite `hδ` using `[hfr]`. Establish `hα0 : α ≠ 0`.

Introduce and unpack `rfl`. Establish `h1 : (⊤ : IntermediateField F (IntermediateField.fixedField H)) = ⊥`. Rewrite using `[← hα]`. Conclude with `IntermediateField.adjoin_simple_eq_bot_iff.2 (zero_mem _)`. Establish `h2` using `congrArg (fun E : IntermediateField F (IntermediateField.fixedField H) => Module.finrank F E) h1`.

Simplify using `only [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h2`. Conclude with `hl.one_lt.ne' (hfr ▸ h2)`. Establish `hθ0 : (α : L) ≠ 0` using `fun h => hα0 (Subtype.ext h)`. Establish `hθl : (α : L) ^ l ∈ (algebraMap F L).range`. Use `⟨δ, ?_⟩` and prove the remaining obligations.

Use `congrArg (fun y : IntermediateField.fixedField H => (y : L)) hδ` as an intermediate fact. Simplify using `using this`. Establish `hKθ : ∀ x ∈ IntermediateField.fixedField H, x ∈ IntermediateField.adjoin F {(α : L)}`. Introduce `x hx`. Establish `hm : x ∈ (IntermediateField.adjoin F {α}).map (IntermediateField.fixedField H).val` using `⟨⟨x, hx⟩, by rw [hα]; trivial, rfl⟩`.

Rewrite `hm` using `[IntermediateField.adjoin_map, Set.image_singleton]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, τ ∉ H := by`. Assume the negation of the conclusion as `h`. Conclude with `hH.1 (eq_top_iff.2 fun g _ => by_contra fun hg => h ⟨g, hg⟩)`. Take `⟨σ, hσ⟩` from `GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (IntermediateField.fixedField H) L W (W.comap (τ : L →+* L)) (fun a => (hW α hθ0 hθl τ a (hKθ a a.2)).symm)`.

Establish `hη : σ.restrictScalars F ∈ H`. Use `(IntermediateField.fixingSubgroup_fixedField H).le ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `σ.commutes ⟨x, hx⟩`.

Establish `hτη : τ * σ.restrictScalars F ∈ D` using `fun x => hσ x`. Conclude with `hτ ((H.mul_mem_cancel_right hη).1 (hDH hτη))`.
-/
theorem valuationSubring_galois_stable_of_kummer : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  intro l hl F L _ _ _ _ _ hP hζ W hW
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  let D : Subgroup (L ≃ₐ[F] L) :=
    { carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W}
      mul_mem' := by
        intro a b ha hb x
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AlgEquiv.mul_apply, ha, hb]
      one_mem' := by intro x; simp
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (a⁻¹ x)]
        simp }
  suffices hD : D = ⊤ by
    intro τ x
    have hτ : τ ∈ D := hD ▸ Subgroup.mem_top τ
    exact hτ x
  by_contra hD
  obtain ⟨H, hH, hDH⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  obtain ⟨hHn, hHi⟩ := isPGroup_coatom_normal_index_eq hP H hH
  haveI : IsGalois F (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  have hfr : Module.finrank F (IntermediateField.fixedField H) = l := by
    have h1 := Module.finrank_mul_finrank F (IntermediateField.fixedField H) L
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L,
      ← H.card_mul_index, hHi, mul_comm (Nat.card H)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  haveI : IsCyclic (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H) :=
    isCyclic_of_prime_card (p := l) (by rw [IsGalois.card_aut_eq_finrank, hfr])
  obtain ⟨ζ, hζ⟩ := hζ
  have hK : (primitiveRoots (Module.finrank F (IntermediateField.fixedField H)) F).Nonempty :=
    ⟨ζ, by rw [hfr, mem_primitiveRoots hl.pos]; exact hζ⟩
  obtain ⟨α, ⟨δ, hδ⟩, hα⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic F (IntermediateField.fixedField H) hK
  rw [hfr] at hδ
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 : (⊤ : IntermediateField F (IntermediateField.fixedField H)) = ⊥ := by
      rw [← hα]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 (zero_mem _)
    have h2 := congrArg
      (fun E : IntermediateField F (IntermediateField.fixedField H) => Module.finrank F E) h1
    simp only [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h2
    exact hl.one_lt.ne' (hfr ▸ h2)
  have hθ0 : (α : L) ≠ 0 := fun h => hα0 (Subtype.ext h)
  have hθl : (α : L) ^ l ∈ (algebraMap F L).range := by
    refine ⟨δ, ?_⟩
    have := congrArg (fun y : IntermediateField.fixedField H => (y : L)) hδ
    simpa using this
  have hKθ : ∀ x ∈ IntermediateField.fixedField H, x ∈ IntermediateField.adjoin F {(α : L)} := by
    intro x hx
    have hm : x ∈ (IntermediateField.adjoin F {α}).map (IntermediateField.fixedField H).val :=
      ⟨⟨x, hx⟩, by rw [hα]; trivial, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at hm
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∉ H := by
    by_contra h
    exact hH.1 (eq_top_iff.2 fun g _ => by_contra fun hg => h ⟨g, hg⟩)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (IntermediateField.fixedField H) L W (W.comap (τ : L →+* L))
    (fun a => (hW α hθ0 hθl τ a (hKθ a a.2)).symm)
  have hη : σ.restrictScalars F ∈ H := by
    refine (IntermediateField.fixingSubgroup_fixedField H).le ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have hτη : τ * σ.restrictScalars F ∈ D := fun x => hσ x
  exact hτ ((H.mul_mem_cancel_right hη).1 (hDH hτη))

end GlobalTheory
