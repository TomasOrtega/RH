import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotExtend

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R _ _ κ _ x hx`. Take `⟨s, y, -, hs, hc⟩` from `cotInd_extend R κ x hx`. Rewrite `hs` using `[Set.Sum.elim_range]`. Establish `hd : ringKrullDim R = ((Fintype.card κ + s : ℕ) : WithBot ℕ∞)`. Rewrite using `[hc, IsRegularLocalRing.spanFinrank_maximalIdeal]`.

Use `set I := Ideal.span (Set.range x) with hI`. Establish `hle : I ≤ maximalIdeal R`. Rewrite using `[← hs]`. Conclude with `Ideal.span_mono Set.subset_union_left`. Establish `hne : I ≠ ⊤` using `fun h => Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))`.

Establish `: Nontrivial (R ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hne`. Establish `: IsLocalRing (R ⧸ I)` using `.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Establish `hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I)` using `map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (y i)) = maximalIdeal (R ⧸ I)`. Rewrite using `[← hmax, ← hs, Ideal.span_union, Ideal.map_sup, ← hI, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hfin : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (s : ℕ)`. Rewrite using `[← hspan]`. Establish `h1` using `Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I) (Set.finite_range fun i => Ideal.Quotient.mk I (y i))`. Establish `h2 : (Set.range fun i => Ideal.Quotient.mk I (y i)).ncard ≤ s`.

Rewrite using `[← Set.image_univ]`. Conclude with `(Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])`. Conclude with `h1.trans h2` after adjusting the coercions. Establish `hdim : ((s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I)`. Establish `h1` using `ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range x) (by`.

Rewrite using `[IsLocalRing.ringJacobson_eq_maximalIdeal]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hx.mem k)`. Rewrite `h1` using `[hd]`. Establish `h2 : (Set.range x).encard ≤ (Fintype.card κ : ℕ∞)`.

Rewrite using `[← Set.image_univ]`. Use `(Set.encard_image_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Set.encard_univ, ENat.card_eq_coe_fintype_card]`. Establish `hnb : ringKrullDim (R ⧸ I) ≠ ⊥` using `ringKrullDim_ne_bot`. Take `⟨n, hn⟩` from `WithBot.ne_bot_iff_exists.mp hnb`.

Rewrite `h1`, the goal using `[← hn]`. Establish `h3 : (Fintype.card κ : ℕ∞) + (s : ℕ∞) ≤ n + (Set.range x).encard`. Conclude with `h1` after adjusting the coercions. Establish `h4 : (s : ℕ∞) + (Fintype.card κ : ℕ∞) ≤ n + (Fintype.card κ : ℕ∞)`. Rewrite using `[add_comm]`.

Conclude with `h3.trans (by gcongr)`. Establish `h5 : (s : ℕ∞) ≤ n` using `(ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4`. Conclude with `h5` after adjusting the coercions. Establish `hreg : IsRegularLocalRing (R ⧸ I)` using `.of_spanFinrank_maximalIdeal_le _ (hfin.trans hdim)`. Establish `heq : ringKrullDim (R ⧸ I) = (s : ℕ)` using `le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hfin) hdim`.

Use `⟨hreg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, hd, add_comm]`. Use `push_cast`. Both sides reduce to the same expression. Conclude with `(Ideal.Quotient.isDomain_iff_prime I).1 (GlobalTheory.isDomain_of_isRegularLocalRing _)`.
-/
theorem UpperTheory.V.AlgebraTools.regular_quotient_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range x)) + (Fintype.card κ : ℕ) = ringKrullDim R ∧
      (Ideal.span (Set.range x)).IsPrime := by
  intro R _ _ κ _ x hx
  classical
  obtain ⟨s, y, -, hs, hc⟩ := cotInd_extend R κ x hx
  rw [Set.Sum.elim_range] at hs
  have hd : ringKrullDim R = ((Fintype.card κ + s : ℕ) : WithBot ℕ∞) := by
    rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]
  set I := Ideal.span (Set.range x) with hI
  have hle : I ≤ maximalIdeal R := by
    rw [← hs]
    exact Ideal.span_mono Set.subset_union_left
  have hne : I ≠ ⊤ := fun h => Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (y i)) = maximalIdeal (R ⧸ I) := by
    rw [← hmax, ← hs, Ideal.span_union, Ideal.map_sup, ← hI, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hfin : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (s : ℕ) := by
    rw [← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (y i))
    have h2 : (Set.range fun i => Ideal.Quotient.mk I (y i)).ncard ≤ s := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hdim : ((s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range x)
      (by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        rintro _ ⟨k, rfl⟩
        exact hx.mem k)
    rw [hd] at h1
    have h2 : (Set.range x).encard ≤ (Fintype.card κ : ℕ∞) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    have hnb : ringKrullDim (R ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hnb
    rw [← hn] at h1 ⊢
    have h3 : (Fintype.card κ : ℕ∞) + (s : ℕ∞) ≤ n + (Set.range x).encard := by
      exact_mod_cast h1
    have h4 : (s : ℕ∞) + (Fintype.card κ : ℕ∞) ≤ n + (Fintype.card κ : ℕ∞) := by
      rw [add_comm]
      exact h3.trans (by gcongr)
    have h5 : (s : ℕ∞) ≤ n := (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4
    exact_mod_cast h5
  have hreg : IsRegularLocalRing (R ⧸ I) := .of_spanFinrank_maximalIdeal_le _ (hfin.trans hdim)
  have heq : ringKrullDim (R ⧸ I) = (s : ℕ) :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hfin) hdim
  refine ⟨hreg, ?_, ?_⟩
  · rw [heq, hd, add_comm]
    push_cast
    rfl
  · exact (Ideal.Quotient.isDomain_iff_prime I).1 (GlobalTheory.isDomain_of_isRegularLocalRing _)
