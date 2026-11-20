import Mathlib

open IsLocalRing Matrix

namespace GlobalTheory.RegularQuotient

open IsLocalRing Matrix in

/- English proof (translation)
Use `set I := Ideal.span (Set.range z) with hIdef`. Establish `hIm : I ≤ maximalIdeal Λ`. Rewrite using `[Ideal.span_le, ← hs]`. Conclude with `(Set.subset_union_right).trans Ideal.subset_span`. Establish `hItop : I ≠ ⊤` using `ne_top_of_le_ne_top (maximalIdeal.isMaximal Λ).ne_top hIm`.

Use `haveI : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop`. Use `haveI : IsLocalRing (Λ ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective`. Establish `hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal Λ) = maximalIdeal (Λ ⧸ I)`. Establish `hc : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (Λ ⧸ I)) = maximalIdeal Λ` using `IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)`. Rewrite using `[← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`.

Establish `hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (t i)) = maximalIdeal (Λ ⧸ I)`. Rewrite using `[← hmap, ← hs, Ideal.span_union, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hgen : ((maximalIdeal (Λ ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (Fintype.card ι : ℕ)`. Rewrite using `[← hspan]`.

Establish `h` using `Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ ⧸ I) (Set.finite_range fun i => Ideal.Quotient.mk I (t i))`. Establish `h' : (Set.range fun i => Ideal.Quotient.mk I (t i)).ncard ≤ Fintype.card ι`. Rewrite using `[← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)`. Conclude with `h.trans h'` after adjusting the coercions. Establish `hle : ringKrullDim (Λ ⧸ I) ≤ (Fintype.card ι : ℕ)` using `(ringKrullDim_le_spanFinrank_maximalIdeal _).trans hgen`.

Establish `hI : (I.spanFinrank : WithBot ℕ∞) ≤ (Fintype.card κ : ℕ)`. Establish `h` using `Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ) (Set.finite_range z)`. Establish `h' : (Set.range z).ncard ≤ Fintype.card κ`. Rewrite using `[← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)`. Conclude with `h.trans h'` after adjusting the coercions.

Establish `hge` using `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)`. Rewrite `hge` using `[hd]`. Establish `h1 : ((Fintype.card ι + Fintype.card κ : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Λ ⧸ I) + (Fintype.card κ : ℕ)` using `hge.trans (add_le_add le_rfl hI)`. Establish `hdim : ringKrullDim (Λ ⧸ I) = (Fintype.card ι : ℕ)`. Generalize the expression as in `ringKrullDim (Λ ⧸ I) = e at h1 hle ⊢`.

Proceed by induction on `e using WithBot.recBotCoe with`. Consider the case `bot => simp at h1`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top => exact absurd hle (by exact_mod_cast (not_le.mpr (ENat.coe_lt_top _)))`.

Consider the case `coe n`. Normalize the coercions in `at h1 hle ⊢`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hgen.trans hdim.ge), hmap, hspan, hdim⟩`.
-/
theorem _root_.GlobalTheory.RegularQuotient.quot_regular (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (t : ι → Λ) (z : κ → Λ)
    (hs : Ideal.span (Set.range t ∪ Set.range z) = maximalIdeal Λ)
    (hd : ringKrullDim Λ = ((Fintype.card ι + Fintype.card κ : ℕ) : ℕ)) :
    ∃ _ : IsRegularLocalRing (Λ ⧸ Ideal.span (Set.range z)),
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range z))) (maximalIdeal Λ) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range z)) (t i)) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      ringKrullDim (Λ ⧸ Ideal.span (Set.range z)) = (Fintype.card ι : ℕ) := by
  set I := Ideal.span (Set.range z) with hIdef
  have hIm : I ≤ maximalIdeal Λ := by
    rw [Ideal.span_le, ← hs]
    exact (Set.subset_union_right).trans Ideal.subset_span
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal Λ).ne_top hIm
  haveI : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (Λ ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal Λ) = maximalIdeal (Λ ⧸ I) := by
    have hc : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (Λ ⧸ I)) = maximalIdeal Λ :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (t i)) =
      maximalIdeal (Λ ⧸ I) := by
    rw [← hmap, ← hs, Ideal.span_union, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hgen : ((maximalIdeal (Λ ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (Fintype.card ι : ℕ) := by
    rw [← hspan]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (t i))
    have h' : (Set.range fun i => Ideal.Quotient.mk I (t i)).ncard ≤ Fintype.card ι := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hle : ringKrullDim (Λ ⧸ I) ≤ (Fintype.card ι : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans hgen
  have hI : (I.spanFinrank : WithBot ℕ∞) ≤ (Fintype.card κ : ℕ) := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ) (Set.finite_range z)
    have h' : (Set.range z).ncard ≤ Fintype.card κ := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hge := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)
  rw [hd] at hge
  have h1 : ((Fintype.card ι + Fintype.card κ : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Λ ⧸ I) + (Fintype.card κ : ℕ) :=
    hge.trans (add_le_add le_rfl hI)
  have hdim : ringKrullDim (Λ ⧸ I) = (Fintype.card ι : ℕ) := by
    generalize ringKrullDim (Λ ⧸ I) = e at h1 hle ⊢
    induction e using WithBot.recBotCoe with
    | bot => simp at h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (by exact_mod_cast (not_le.mpr (ENat.coe_lt_top _)))
      | coe n =>
        norm_cast at h1 hle ⊢
        omega
  exact ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hgen.trans hdim.ge), hmap, hspan,
    hdim⟩

open IsLocalRing Matrix in

/- English proof (translation)
Use `set N : Submodule (ResidueField Λ) (CotangentSpace Λ) := Submodule.span (ResidueField Λ) (Set.range fun i => (maximalIdeal Λ).toCotangent (τ i)) with hN`. Set `b` to `Module.finBasis (ResidueField Λ) (CotangentSpace Λ ⧸ N)`. Establish `hsurj : Function.Surjective fun y : maximalIdeal Λ => N.mkQ ((maximalIdeal Λ).toCotangent y)` using `(Submodule.mkQ_surjective N).comp (maximalIdeal Λ).toCotangent_surjective`. Use `choose s hs using fun j => hsurj (b j)`. Use `⟨Fin (Module.finrank (ResidueField Λ) (CotangentSpace Λ ⧸ N)), inferInstance, fun j => (s j : Λ), ?_, ?_⟩` and prove the remaining obligations.

Establish `htop : Submodule.span (ResidueField Λ) ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ)) = ⊤` using `by set P := Submodule.span (ResidueField Λ) ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ))`. Establish `hNP : N ≤ P`. Rewrite using `[hN, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨τ i, Or.inr ⟨i, rfl⟩, rfl⟩`.

Establish `hmap : Submodule.map N.mkQ P = ⊤`. Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨_, Submodule.subset_span ⟨s j, Or.inl ⟨j, rfl⟩, rfl⟩, hs j⟩`. Rewrite `hmap` using `[Submodule.map_mkQ_eq_top, sup_eq_right.mpr hNP]`.

Conclude with `hmap`. Rewrite `htop` using `[IsLocalRing.CotangentSpace.span_image_eq_top_iff]`. Establish `key` using `congrArg (Submodule.map (maximalIdeal Λ).subtype) htop`. Rewrite `key` using `[← Submodule.span_image, Submodule.map_subtype_top, Set.image_union, ← Set.range_comp, ← Set.range_comp]`. Conclude with `key`.

Rewrite using `[← (IsRegularLocalRing.iff_finrank_cotangentSpace Λ).mp inferInstance, Fintype.card_fin, ← finrank_span_eq_card hτ, ← hN, Submodule.finrank_quotient_add_finrank]`.
-/
theorem _root_.GlobalTheory.RegularQuotient.exists_extend (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι : Type} [Fintype ι]
    (τ : ι → maximalIdeal Λ)
    (hτ : LinearIndependent (ResidueField Λ) (fun i => (maximalIdeal Λ).toCotangent (τ i))) :
    ∃ (J : Type) (_ : Fintype J) (t : J → Λ),
      Ideal.span (Set.range t ∪ Set.range fun i => (τ i : Λ)) = maximalIdeal Λ ∧
      ringKrullDim Λ = ((Fintype.card J + Fintype.card ι : ℕ) : ℕ) := by
  set N : Submodule (ResidueField Λ) (CotangentSpace Λ) :=
    Submodule.span (ResidueField Λ) (Set.range fun i => (maximalIdeal Λ).toCotangent (τ i))
    with hN
  let b := Module.finBasis (ResidueField Λ) (CotangentSpace Λ ⧸ N)
  have hsurj : Function.Surjective
      fun y : maximalIdeal Λ => N.mkQ ((maximalIdeal Λ).toCotangent y) :=
    (Submodule.mkQ_surjective N).comp (maximalIdeal Λ).toCotangent_surjective
  choose s hs using fun j => hsurj (b j)
  refine ⟨Fin (Module.finrank (ResidueField Λ) (CotangentSpace Λ ⧸ N)), inferInstance,
    fun j => (s j : Λ), ?_, ?_⟩
  · have htop : Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ)) = ⊤ := by
      set P := Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ))
      have hNP : N ≤ P := by
        rw [hN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨τ i, Or.inr ⟨i, rfl⟩, rfl⟩
      have hmap : Submodule.map N.mkQ P = ⊤ := by
        rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨_, Submodule.subset_span ⟨s j, Or.inl ⟨j, rfl⟩, rfl⟩, hs j⟩
      rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hNP] at hmap
      exact hmap
    rw [IsLocalRing.CotangentSpace.span_image_eq_top_iff] at htop
    have key := congrArg (Submodule.map (maximalIdeal Λ).subtype) htop
    rw [← Submodule.span_image, Submodule.map_subtype_top, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at key
    exact key
  · rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace Λ).mp inferInstance, Fintype.card_fin,
      ← finrank_span_eq_card hτ, ← hN, Submodule.finrank_quotient_add_finrank]

open IsLocalRing Matrix in
/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `choose a ha using fun j => IsLocalRing.residue_surjective (g j)`. Establish `hmem : (∑ j, a j * x j) ∈ maximalIdeal A` using `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)`. Establish `hsum : (∑ j, a j * x j) ∈ maximalIdeal A ^ 2`.

Rewrite using `[← Ideal.toCotangent_eq_zero (maximalIdeal A) ⟨_, hmem⟩]`. Establish `he : (⟨∑ j, a j * x j, hmem⟩ : maximalIdeal A) = ∑ j, a j • (⟨x j, hx j⟩ : maximalIdeal A)` using `by ext; simp [Submodule.coe_sum, smul_eq_mul]`. Rewrite using `[he, map_sum, ← hg]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← ha j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]`.

Rewrite using `[← ha i, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hind a hsum i`.
-/
private theorem linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq (A : Type) [CommRing A]
    [IsRegularLocalRing A] (k : ℕ) (x : Fin k → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hind : ∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun i => (maximalIdeal A).toCotangent (⟨x i, hx i⟩ : maximalIdeal A)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => IsLocalRing.residue_surjective (g j)
  have hmem : (∑ j, a j * x j) ∈ maximalIdeal A :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)
  have hsum : (∑ j, a j * x j) ∈ maximalIdeal A ^ 2 := by
    rw [← Ideal.toCotangent_eq_zero (maximalIdeal A) ⟨_, hmem⟩]
    have he : (⟨∑ j, a j * x j, hmem⟩ : maximalIdeal A) =
        ∑ j, a j • (⟨x j, hx j⟩ : maximalIdeal A) := by
      ext; simp [Submodule.coe_sum, smul_eq_mul]
    rw [he, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← ha j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  rw [← ha i, IsLocalRing.residue_eq_zero_iff]
  exact hind a hsum i

open IsLocalRing Matrix in

/- English proof (translation)
Introduce `A _ _ d k x hd hx hind`. Take `⟨J, _, t, hspan, hdim⟩` from `_root_.GlobalTheory.RegularQuotient.exists_extend A (fun i => (⟨x i, hx i⟩ : maximalIdeal A)) (linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq A k x hx hind)`. Establish `hJ : Fintype.card J = d`. Rewrite `hdim` using `[hd, Fintype.card_fin]`. Establish `h : d + k = Fintype.card J + k` using `by exact_mod_cast hdim`.

Use linear arithmetic over natural numbers and integers. Establish `hspan' : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal A` using `hspan`. Establish `hdim' : ringKrullDim A = ((Fintype.card J + Fintype.card (Fin k) : ℕ) : ℕ)`. Rewrite using `[hd, Fintype.card_fin, hJ]`. Take `⟨hreg, -, -, hq⟩` from `_root_.GlobalTheory.RegularQuotient.quot_regular A t x hspan' hdim'`.

Conclude with `⟨hreg, by rw [hq, hJ]⟩`.
-/
theorem _root_.GlobalTheory.RegularQuotient.quotient_span_range : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d k : ℕ)
    (x : Fin k → A),
    ringKrullDim A = ((d + k : ℕ) : WithBot ℕ∞) → (∀ i, x i ∈ maximalIdeal A) →
    (∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) →
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (A ⧸ Ideal.span (Set.range x)) = (d : WithBot ℕ∞) := by
  intro A _ _ d k x hd hx hind
  obtain ⟨J, _, t, hspan, hdim⟩ := _root_.GlobalTheory.RegularQuotient.exists_extend A
    (fun i => (⟨x i, hx i⟩ : maximalIdeal A))
    (linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq A k x hx hind)
  have hJ : Fintype.card J = d := by
    rw [hd, Fintype.card_fin] at hdim
    have h : d + k = Fintype.card J + k := by exact_mod_cast hdim
    omega
  have hspan' : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal A := hspan
  have hdim' : ringKrullDim A = ((Fintype.card J + Fintype.card (Fin k) : ℕ) : ℕ) := by
    rw [hd, Fintype.card_fin, hJ]
  obtain ⟨hreg, -, -, hq⟩ := _root_.GlobalTheory.RegularQuotient.quot_regular A t x hspan' hdim'
  exact ⟨hreg, by rw [hq, hJ]⟩

end GlobalTheory.RegularQuotient
