import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexFormulaNormsInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardPlacesLeCardOverQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardInfinitePlaceLeQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsPlacesOverAndQuadraticConjStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberFieldStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Unfold `Subgroup.relIndex`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf, powMonoidHom_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, y.2, by simp⟩`. Introduce and unpack `⟨y, hy, h⟩`. Conclude with `⟨⟨y, hy⟩, Subtype.ext (by simpa using h)⟩`.
-/
private theorem index_sqs_top_eq {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs (⊤ : Subgroup U)).index = (sqs U).relIndex U := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf,
    powMonoidHom_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using h)⟩

/- English proof (translation)
Rewrite using `[← Subgroup.index_comap]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap, powMonoidHom_apply, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨y, rfl⟩, h⟩`. Conclude with `⟨y, hj (by simpa using h)⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨j y, ⟨y, rfl⟩, by simp⟩`.
-/
private theorem relIndex_sqs_range_eq {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    (sqs j.range).relIndex j.range = (sqs (⊤ : Subgroup U)).index := by
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

/- English proof (translation)
Establish `hn : n ≠ 0`. Introduce and unpack `rfl`. Establish `: 0 < (2 ^ s) ^ 2` using `by positivity`. Use linear arithmetic over natural numbers and integers. Use `⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩` and prove the remaining obligations.

Establish `hmn : m ≤ n` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd`. Establish `h1 : 2 ^ e * (2 * n) ≤ 2 ^ e * 2 ^ t`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 2 * n ≤ 2 ^ t` using `Nat.le_of_mul_le_mul_left h1 (by positivity)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem arith_first_ineq (m n e s t : ℕ) (hd : m ∣ n) (h : 2 * 2 ^ e * n = (2 ^ s) ^ 2)
    (hs : 2 * s ≤ e + t) : m ≠ 0 ∧ 2 * m ≤ 2 ^ t := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 0 < (2 ^ s) ^ 2 := by positivity
    omega
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h1 : 2 ^ e * (2 * n) ≤ 2 ^ e * 2 ^ t := by
    calc 2 ^ e * (2 * n) = (2 ^ s) ^ 2 := by rw [← h]; ring
      _ = 2 ^ (2 * s) := by ring
      _ ≤ 2 ^ (e + t) := Nat.pow_le_pow_right (by norm_num) hs
      _ = 2 ^ e * 2 ^ t := pow_add _ _ _
  have h2 : 2 * n ≤ 2 ^ t := Nat.le_of_mul_le_mul_left h1 (by positivity)
  omega

/- English proof (translation)
Introduce `F _ _ δ S hS hδ hns`. Take `⟨E, _, _, _, θ, σ, hq⟩` from `GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square F δ hns`. Take `⟨SE, hSE⟩` from `(GlobalTheory.T.heightOneSpectrum_places_over_finite_set F E).1 S`. Take `⟨hinv, hfix, -, hnorm, -, -, -⟩` from `GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ hq`. Take `⟨hup, hσ⟩` from `GlobalTheory.T.sUnits_places_over_and_quadratic_conj F E δ θ σ hq S SE hSE`.

Establish `h90` using `GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm F E δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)`. Establish `hcf` using `GlobalTheory.T.two_mul_card_places_le_card_over_quadratic F E δ θ σ hq S SE hSE`. Establish `hci` using `GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic F E δ θ σ hq`. Set `τ : sUnits E SE →* sUnits E SE` to `((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ y y.2)`. Establish `hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E)` using `fun _ => rfl`.

Set `j : sUnits F S →* sUnits E SE` to `((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _ (fun y => (hup y).2 y.2)`. Establish `hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F)` using `fun _ => rfl`. Establish `hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b` using `fun a b h => Subtype.ext (Units.ext h)`. Establish `hjinj : Function.Injective j`. Introduce `a b h`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[← hj, ← hj, h]`. Establish `hm : (-1 : Eˣ) ∈ sUnits E SE`.

Rewrite using `[mem_sUnits]`. Introduce `v _`. Simplify using the standard rewrite rules. Establish `hrange : τ.eqLocus (MonoidHom.id _) = j.range`. Use extensionality with `y`.

Rewrite using `[MonoidHom.mem_range]`. Express the relevant statement in the definitionally equal form `τ y = y ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha⟩` from `hfix ((y : Eˣ) : E) (by rw [← hτ, h])`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `(y : Eˣ).ne_zero (by simpa using ha)`. Establish `hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y` using `Units.ext (by simpa using ha.symm)`. Use `⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩` and prove the remaining obligations.

Rewrite using `[hj, ha]`. Both sides reduce to the same expression. Introduce and unpack `⟨x, rfl⟩`. Apply `hext` to reduce the goal to its premises. Rewrite using `[hτ, hj, AlgEquiv.commutes]`.

Establish `key` using `GlobalTheory.T.index_formula_norms_involution (sUnits E SE) τ ⟨-1, hm⟩ (fun a => hext _ _ (by rw [hτ, hτ, hinv])) (fun a ha => by`. Establish `h1 : ((a : Eˣ) : E) * σ ((a : Eˣ) : E) = 1`. Rewrite using `[← hτ]`. Use `congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha` as an intermediate fact. Simplify using `using this`.

Take `⟨y, hy, h⟩` from `h90 a a.2 h1`. Use `⟨⟨y, hy⟩, hext _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[h, Subgroup.coe_div, Units.val_div_eq_div_val, hτ])`. Use the proof step `(fun h => by`. Use `congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) h` as an intermediate fact.

Simplify using `only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this`. Evaluate the numerical expressions using `at this)`. Use the proof step `(hext _ _ (by simp))`. Use the proof step `(hext _ _ (by rw [hτ]; simp))`. Use the proof step `(fun a ha => by`.

Establish `h1 : ((a : Eˣ) : E) ^ 2 = 1`. Use `congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha` as an intermediate fact. Simplify using `using this`. Break down `sq_eq_one_iff.1 h1 with h | h` into its components or cases. Conclude with `Or.inl (hext _ _ (by simpa using h))`.

Conclude with `Or.inr (hext _ _ (by simpa using h)))`. Rewrite `key` using `[hrange, relIndex_sqs_range_eq j hjinj, index_sqs_top_eq, index_sqs_top_eq, GlobalTheory.T.relIndex_squares_sUnitsNumberField E SE, GlobalTheory.T.relIndex_squares_sUnitsNumberField F S, ← Subgroup.index_comap]`. Use `arith_first_ineq _ _ _ _ _ ?_ key (by omega)` and prove the remaining obligations. Apply `Subgroup.index_dvd_of_le` to reduce the goal to its premises. Introduce and unpack `x ⟨y, hy⟩`.

Rewrite using `[Subgroup.mem_subgroupOf, mem_normSub]`. Take `⟨a, b, hab⟩` from `hnorm ((y : Eˣ) : E)`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Simplify using `only [RingHom.id_apply]`.

Rewrite using `[← hab, ← hj, ← hy, ← hτ]`. Simplify using the standard rewrite rules.
-/
theorem first_inequality_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
      admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) →
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤
          2 ^ (tFin F δ S + tReal F δ) := by
  intro F _ _ δ S hS hδ hns
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square F δ hns
  obtain ⟨SE, hSE⟩ := (GlobalTheory.T.heightOneSpectrum_places_over_finite_set F E).1 S
  obtain ⟨hinv, hfix, -, hnorm, -, -, -⟩ := GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ hq
  obtain ⟨hup, hσ⟩ := GlobalTheory.T.sUnits_places_over_and_quadratic_conj F E δ θ σ hq S SE hSE
  have h90 := GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm F E δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := GlobalTheory.T.two_mul_card_places_le_card_over_quadratic F E δ θ σ hq S SE hSE
  have hci := GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic F E δ θ σ hq
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hm : (-1 : Eˣ) ∈ sUnits E SE := by
    rw [mem_sUnits]
    intro v _
    simp
  have hrange : τ.eqLocus (MonoidHom.id _) = j.range := by
    ext y
    rw [MonoidHom.mem_range]
    change τ y = y ↔ _
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have key := GlobalTheory.T.index_formula_norms_involution (sUnits E SE) τ ⟨-1, hm⟩
    (fun a => hext _ _ (by rw [hτ, hτ, hinv]))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) * σ ((a : Eˣ) : E) = 1 := by
        rw [← hτ]
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      obtain ⟨y, hy, h⟩ := h90 a a.2 h1
      refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
      rw [h, Subgroup.coe_div, Units.val_div_eq_div_val, hτ])
    (fun h => by
      have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) h
      simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
      norm_num at this)
    (hext _ _ (by simp))
    (hext _ _ (by rw [hτ]; simp))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) ^ 2 = 1 := by
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      rcases sq_eq_one_iff.1 h1 with h | h
      · exact Or.inl (hext _ _ (by simpa using h))
      · exact Or.inr (hext _ _ (by simpa using h)))
  rw [hrange, relIndex_sqs_range_eq j hjinj, index_sqs_top_eq, index_sqs_top_eq,
    GlobalTheory.T.relIndex_squares_sUnitsNumberField E SE, GlobalTheory.T.relIndex_squares_sUnitsNumberField F S, ← Subgroup.index_comap] at key
  refine arith_first_ineq _ _ _ _ _ ?_ key (by omega)
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, mem_normSub]
  obtain ⟨a, b, hab⟩ := hnorm ((y : Eˣ) : E)
  refine ⟨a, b, ?_⟩
  apply (algebraMap F E).injective
  simp only [RingHom.id_apply]
  rw [← hab, ← hj, ← hy, ← hτ]
  simp

end GlobalTheory.QNorm
