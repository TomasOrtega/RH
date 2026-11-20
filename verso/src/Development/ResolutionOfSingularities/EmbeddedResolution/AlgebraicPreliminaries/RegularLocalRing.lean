import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
namespace IsRegularLocalRing

open IsLocalRing

universe u

/- English proof (translation)
Establish `h2 : (Ideal.span (s : Set R)).FG` using `Submodule.fg_span s.finite_toSet`. Establish `h1 : (Ideal.span (s : Set R)).spanRank ≤ Cardinal.mk ((s : Set R))` using `Submodule.spanRank_span_le_card _`. Rewrite `h1` using `[Submodule.FG.spanRank_eq_spanFinrank h2]`. Establish `h3 : Cardinal.mk ((s : Set R)) = (s.card : Cardinal)` using `by simp`. Rewrite `h1` using `[h3]`.

Conclude with `h1` after adjusting the coercions.
-/
private theorem spanFinrank_span_finset_le_card {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  have h2 : (Ideal.span (s : Set R)).FG := Submodule.fg_span s.finite_toSet
  have h1 : (Ideal.span (s : Set R)).spanRank ≤ Cardinal.mk ((s : Set R)) :=
    Submodule.spanRank_span_le_card _
  rw [Submodule.FG.spanRank_eq_spanFinrank h2] at h1
  have h3 : Cardinal.mk ((s : Set R)) = (s.card : Cardinal) := by simp
  rw [h3] at h1
  exact_mod_cast h1

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h0 : b.repr v = 0`. Use extensionality with `j`. Simplify using `[h j]`.

Apply `hv` to reduce the goal to its premises. Establish `h1` using `congrArg (b.repr.symm) h0`. Simplify using `using h1`.
-/
private theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : b.repr v = 0 := by
    ext j
    simp [h j]
  apply hv
  have h1 := congrArg (b.repr.symm) h0
  simpa using h1

/- English proof (translation)
Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `only [SetLike.mem_coe]`. Distinguish the cases in `hij : i = j`. Rewrite using `[hij]`.

Establish `hmem1 : v ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j)))` using `Submodule.subset_span (Set.mem_insert _ _)`. Establish `hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j)))`. Use `Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩)`. Establish `hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = b.repr v j • b j`.

Rewrite using `[Finset.sum_erase_eq_sub (Finset.mem_univ j), b.sum_repr v]`. Normalize the expressions using the abelian group laws. Establish `hkey : b.repr v j • b j ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j)))`. Rewrite using `[← hsub]`. Conclude with `Submodule.sub_mem _ hmem1 hmem2`.

Establish `h2` using `Submodule.smul_mem _ (b.repr v j)⁻¹ hkey`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hj, one_smul]`. Then use the resulting hypothesis. Conclude with `Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩)`.
-/
private theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe]
  by_cases hij : i = j
  · rw [hij]
    have hmem1 : v ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩)
    have hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = b.repr v j • b j := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), b.sum_repr v]
      abel
    have hkey : b.repr v j • b j ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      rw [← hsub]
      exact Submodule.sub_mem _ hmem1 hmem2
    have h2 := Submodule.smul_mem _ (b.repr v j)⁻¹ hkey
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩)

/- English proof (translation)
Establish `hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hx`. Establish `hIne : Ideal.span ({x} : Set R) ≠ ⊤`. Introduce `h`.

Rewrite `hIle` using `[h, top_le_iff]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle`. Establish `hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0`. Introduce `h`. Establish `h1 : (1 : R) ∈ Ideal.span ({x} : Set R)`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_one]` and apply the resulting hypothesis. Conclude with `hIne ((Ideal.eq_top_iff_one _).mpr h1)`. Establish `: Nontrivial (R ⧸ Ideal.span ({x} : Set R))` using `⟨⟨1, 0, hone⟩⟩`. Conclude with `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`.
-/
private theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hIne : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0 := by
    intro h
    have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hIne ((Ideal.eq_top_iff_one _).mpr h1)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/- English proof (translation)
Establish `hv0 : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0`. Rewrite using `[Ne, Ideal.toCotangent_eq_zero]`. Conclude with `hx2`. Take `⟨j, hj⟩` from `exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hv0`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) → (maximalIdeal R), ∀ i, (maximalIdeal R).toCotangent (z i) = Module.finBasis (ResidueField R) (CotangentSpace R) i := by`.

Establish `hsurj : Function.Surjective (maximalIdeal R).toCotangent` using `Ideal.toCotangent_surjective _`. Use `choose z hz using fun i => hsurj (Module.finBasis (ResidueField R) (CotangentSpace R) i)`. Conclude with `⟨z, hz⟩`. Use `set s : Set (maximalIdeal R) := insert (⟨x, hx⟩ : maximalIdeal R) (z '' ↑(Finset.univ.erase j)) with hsdef`. Establish `htop : Submodule.span R s = ⊤`.

Rewrite using `[← IsLocalRing.CotangentSpace.span_image_eq_top_iff]`. Establish `himg : (maximalIdeal R).toCotangent '' s = insert ((maximalIdeal R).toCotangent ⟨x, hx⟩) (⇑(Module.finBasis (ResidueField R) (CotangentSpace R)) '' ↑(Finset.univ.erase j))`. Rewrite using `[hsdef, Set.image_insert_eq, Set.image_image]`. Simplify using `[hz]`. Rewrite using `[himg]`.

Conclude with `span_insert_image_erase_eq_top _ _ hj`. Establish `hmspan : Ideal.span ((Subtype.val : maximalIdeal R → R) '' s) = maximalIdeal R`. Establish `h` using `congrArg (Submodule.map (maximalIdeal R).subtype) htop`. Rewrite `h` using `[Submodule.map_span, Submodule.map_subtype_top]`. Simplify using `using h`.

Establish `hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hx`. Establish `hmapS : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) = Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (maximalIdeal R)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `y hy`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hr`. Rewrite `hr` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`.

Rewrite `hy` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hy (hr.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))))`. Use `IsLocalRing.le_maximalIdeal ?_` and prove the remaining obligations. Introduce `h`. Rewrite `h` using `[Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]`.

Take `⟨r, hrm, hr1⟩` from `h`. Establish `h2 : r - 1 ∈ Ideal.span ({x} : Set R)`. Rewrite using `[← Ideal.Quotient.eq]`. Simplify using `using hr1`. Establish `h3 : (1 : R) ∈ maximalIdeal R`.

Establish `h4` using `sub_mem hrm (hIle h2)`. Simplify using `at h4`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)`. Establish `hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)`. Establish `himg : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) '' ((Subtype.val : maximalIdeal R → R) '' s) = insert 0 ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) '' ↑(Finset.univ.erase j))`.

Rewrite using `[hsdef, Set.image_image, Set.image_insert_eq, Set.image_image]`. Simplify using `[hx0]`. Establish `hquot : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) = Ideal.span ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) '' ↑(Finset.univ.erase j))`. Rewrite using `[hmapS]`. Use `conv_lhs => rw [← hmspan]`.

Rewrite using `[Ideal.map_span, himg]`. Conclude with `Submodule.span_insert_zero`. Establish `hcard : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) ≤ (Finset.univ.erase j).card`. Rewrite using `[hquot, ← Finset.coe_image]`. Conclude with `le_trans (spanFinrank_span_finset_le_card _) Finset.card_image_le`.

Establish `hjpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R)` using `Fin.pos j`. Establish `hcard2 : (Finset.univ.erase j).card = Module.finrank (ResidueField R) (CotangentSpace R) - 1`. Rewrite using `[Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem spanFinrank_maximalIdeal_quotient_add_one_le_finrank (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hv0 : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hx2
  obtain ⟨j, hj⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hv0
  obtain ⟨z, hz⟩ : ∃ z : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) →
      (maximalIdeal R), ∀ i, (maximalIdeal R).toCotangent (z i) =
        Module.finBasis (ResidueField R) (CotangentSpace R) i := by
    have hsurj : Function.Surjective (maximalIdeal R).toCotangent :=
      Ideal.toCotangent_surjective _
    choose z hz using fun i => hsurj (Module.finBasis (ResidueField R) (CotangentSpace R) i)
    exact ⟨z, hz⟩
  set s : Set (maximalIdeal R) :=
    insert (⟨x, hx⟩ : maximalIdeal R) (z '' ↑(Finset.univ.erase j)) with hsdef
  have htop : Submodule.span R s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff]
    have himg : (maximalIdeal R).toCotangent '' s =
        insert ((maximalIdeal R).toCotangent ⟨x, hx⟩)
          (⇑(Module.finBasis (ResidueField R) (CotangentSpace R)) ''
            ↑(Finset.univ.erase j)) := by
      rw [hsdef, Set.image_insert_eq, Set.image_image]
      simp [hz]
    rw [himg]
    exact span_insert_image_erase_eq_top _ _ hj
  have hmspan : Ideal.span ((Subtype.val : maximalIdeal R → R) '' s) = maximalIdeal R := by
    have h := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    rw [Submodule.map_span, Submodule.map_subtype_top] at h
    simpa using h
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hmapS : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (maximalIdeal R) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine Ideal.mem_map_of_mem _ ?_
      by_contra hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
      exact hy (hr.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))))
    · refine IsLocalRing.le_maximalIdeal ?_
      intro h
      rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
      obtain ⟨r, hrm, hr1⟩ := h
      have h2 : r - 1 ∈ Ideal.span ({x} : Set R) := by
        rw [← Ideal.Quotient.eq]
        simpa using hr1
      have h3 : (1 : R) ∈ maximalIdeal R := by
        have h4 := sub_mem hrm (hIle h2)
        simp at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have himg : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) ''
      ((Subtype.val : maximalIdeal R → R) '' s) =
      insert 0 ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hsdef, Set.image_image, Set.image_insert_eq, Set.image_image]
    simp [hx0]
  have hquot : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.span ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hmapS]
    conv_lhs => rw [← hmspan]
    rw [Ideal.map_span, himg]
    exact Submodule.span_insert_zero
  have hcard : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) ≤
      (Finset.univ.erase j).card := by
    rw [hquot, ← Finset.coe_image]
    exact le_trans (spanFinrank_span_finset_le_card _) Finset.card_image_le
  have hjpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := Fin.pos j
  have hcard2 : (Finset.univ.erase j).card =
      Module.finrank (ResidueField R) (CotangentSpace R) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  omega

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, rfl⟩ : ∃ m : ℕ, a = ((m : ℕ) : WithBot ℕ∞) := by`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Rewrite `h1` using `[WithBot.bot_add, le_bot_iff]`.

Conclude with `WithBot.natCast_ne_bot n h1`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction.

Establish `h2' : (⊤ : ℕ∞) ≤ (d : ℕ∞)` using `by exact_mod_cast h2`. Simplify using `at h2'`. Consider the case `coe m => exact ⟨m, by norm_cast⟩`. Establish `hmd : m ≤ d` using `by exact_mod_cast h2`. Establish `hnm : n ≤ m + 1` using `by exact_mod_cast h1`.

Establish `hm : m = d` using `by omega`. Establish `hn : n = m + 1` using `by omega`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Rewrite using `[hn]`.

Use `norm_cast`.
-/
private theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = ((m : ℕ) : WithBot ℕ∞) := by
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      rw [WithBot.bot_add, le_bot_iff] at h1
      exact WithBot.natCast_ne_bot n h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h2' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast h2
        simp at h2'
      | coe m => exact ⟨m, by norm_cast⟩
  have hmd : m ≤ d := by exact_mod_cast h2
  have hnm : n ≤ m + 1 := by exact_mod_cast h1
  have hm : m = d := by omega
  have hn : n = m + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [hm]
  · rw [hn]
    norm_cast

/- English proof (translation)
Establish `hdn` using `spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2`. Establish `hRdim : ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞) = ringKrullDim R`. Rewrite using `[← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Conclude with `IsRegularLocalRing.spanFinrank_maximalIdeal` after adjusting the coercions. Establish `hdimQuot : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤ ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)`.

Conclude with `ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))` after adjusting the coercions. Establish `hIj : Ideal.span ({x} : Set R) ≤ Ring.jacobson R`. Use `le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hx`.

Establish `hdimLe` using `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span ({x} : Set R)) hIj`. Establish `h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1`. Establish `h` using `spanFinrank_span_finset_le_card ({x} : Finset R)`. Simplify using `using h`. Establish `hcast : ((Submodule.spanFinrank (Ideal.span ({x} : Set R)) : ℕ) : WithBot ℕ∞) ≤ 1`.

Conclude with `h1` after adjusting the coercions. Establish `hdimSucc : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1` using `hdimLe.trans (add_le_add le_rfl hcast)`. Take `⟨hA, hB⟩` from `eq_natCast_and_add_one_eq_of_le (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R)))) (n := Module.finrank (ResidueField R) (CotangentSpace R)) (by rw [hRdim]; exact hdimSucc) hdimQuot hdn`. Use `⟨hA.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[hB, hRdim]`.
-/
private theorem spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hdn := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
  have hRdim : ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞)
      = ringKrullDim R := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal
  have hdimQuot : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤
      ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) :
        WithBot ℕ∞) := by
    exact_mod_cast ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  have hIj : Ideal.span ({x} : Set R) ≤ Ring.jacobson R := by
    refine le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hdimLe := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      (Ideal.span ({x} : Set R)) hIj
  have h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1 := by
    have h := spanFinrank_span_finset_le_card ({x} : Finset R)
    simpa using h
  have hcast : ((Submodule.spanFinrank (Ideal.span ({x} : Set R)) : ℕ) : WithBot ℕ∞) ≤ 1 := by
    exact_mod_cast h1
  have hdimSucc : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 :=
    hdimLe.trans (add_le_add le_rfl hcast)
  obtain ⟨hA, hB⟩ := eq_natCast_and_add_one_eq_of_le
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Module.finrank (ResidueField R) (CotangentSpace R))
    (by rw [hRdim]; exact hdimSucc) hdimQuot hdn
  refine ⟨hA.symm, ?_⟩
  rw [hB, hRdim]

/- English proof (translation)
The claim follows from `hp.1.1`.
-/
private theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1

/- English proof (translation)
The claim follows from `hp.2 ⟨hq, bot_le⟩ hle`.
-/
private theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle

/- English proof (translation)
Establish `hp : (maximalIdeal R).IsPrime` using `(maximalIdeal.isMaximal R).isPrime`. Rewrite `hp` using `[h]`. Use `hp` as an intermediate fact. Conclude with `IsDomain.of_bot_isPrime R`.
-/
private theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hp : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R

/- English proof (translation)
Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R) (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)` and prove the remaining obligations. Use `show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R`. Rewrite using `[← pow_two]`. Conclude with `h`.
-/
private theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R
  rw [← pow_two]
  exact h

/- English proof (translation)
Take `⟨t, ht⟩` from `(minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hsub : (maximalIdeal R : Set R) ⊆ ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R)`. Introduce `y hy`.

Break down `em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2` into its components or cases. Conclude with `Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2`. Take `⟨p, hp, hyp⟩` from `hcon y hy hm2`. Establish `hpt : p ∈ insert (maximalIdeal R ^ 2) t`. Apply `Finset.mem_insert_of_mem` to reduce the goal to its premises.

Rewrite using `[← Finset.mem_coe, ht]`. Conclude with `hp`. Conclude with `Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp`. Establish `hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)), i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime`. Introduce `i hi h1 _`.

Establish `hit : i ∈ t`. Break down `Finset.mem_insert.mp hi with hh | hh` into its components or cases. Conclude with `absurd hh h1`. Conclude with `hh`. Use `isPrime_of_mem_minimalPrimes ?_` and prove the remaining obligations.

Rewrite using `[← ht]`. Conclude with `Finset.mem_coe.mpr hit`. Take `⟨i, hi, hle⟩` from `(Ideal.subset_union_prime _ _ hp).mp hsub`. Break down `Finset.mem_insert.mp hi with hh | hh` into its components or cases. Substitute `hh` using the available equality.

Conclude with `hsq hle`. Use `hmin ⟨i, ?_, hle⟩` and prove the remaining obligations. Rewrite using `[← ht]`. Conclude with `Finset.mem_coe.mpr hh`.
-/
private theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2
    · obtain ⟨p, hp, hyp⟩ := hcon y hy hm2
      have hpt : p ∈ insert (maximalIdeal R ^ 2) t := by
        apply Finset.mem_insert_of_mem
        rw [← Finset.mem_coe, ht]
        exact hp
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by
      rcases Finset.mem_insert.mp hi with hh | hh
      · exact absurd hh h1
      · exact hh
    refine isPrime_of_mem_minimalPrimes ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with hh | hh
  · subst hh
    exact hsq hle
  · refine hmin ⟨i, ?_, hle⟩
    rw [← ht]
    exact Finset.mem_coe.mpr hh

/- English proof (translation)
Use `isLocalRing_quotient_span_singleton hx` as an intermediate fact. Rewrite using `[isRegularLocalRing_iff]`. Conclude with `(spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).1` after adjusting the coercions.
-/
theorem isRegularLocalRing_quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).1

/- English proof (translation)
Use `isLocalRing_quotient_span_singleton hx` as an intermediate fact. Conclude with `(spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).2`.
-/
theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).2

/- English proof (translation)
Distinguish the cases in `hsq : maximalIdeal R ≤ maximalIdeal R ^ 2`. Conclude with `isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)`. Distinguish the cases in `hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p`. It suffices to derive a contradiction. Take `⟨p, hp, hple⟩` from `hmin`.

Establish `hpp : p.IsPrime` using `isPrime_of_mem_minimalPrimes hp`. Establish `hpm : p = maximalIdeal R` using `le_antisymm (IsLocalRing.le_maximalIdeal hpp.ne_top) hple`. Establish `hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R`. Introduce `q hq`. Use `le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_` and prove the remaining obligations.

Rewrite using `[← hpm]`. Conclude with `le_of_le_of_mem_minimalPrimes hp hq (by rw [hpm]; exact IsLocalRing.le_maximalIdeal hq.ne_top)`. Establish `h2 : ringKrullDim R ≤ 0`. Establish `hPQ : ∀ P Q : PrimeSpectrum R, P = Q`. Introduce `P Q`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Rewrite using `[hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]`. Establish `: Subsingleton (PrimeSpectrum R)` using `⟨hPQ⟩`. Conclude with `Order.krullDim_nonpos_of_subsingleton`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hsq fun y hy => hc y hy`. Use `isLocalRing_quotient_span_singleton hx` as an intermediate fact. Establish `hpos` using `spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2`.

Establish `hdim : ringKrullDim R = (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞)` using `((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm`. Rewrite `h2` using `[hdim]`. Establish `hle0 : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 0` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, hx2, hxp⟩` from `exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin`.

Use `isLocalRing_quotient_span_singleton hx` as an intermediate fact. Establish `hrq : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R))` using `isRegularLocalRing_quotient_span_singleton hx hx2`. Establish `hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) < Submodule.spanFinrank (maximalIdeal R)`. Establish `h1` using `spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2`. Establish `h2 : Submodule.spanFinrank (maximalIdeal R) = Module.finrank (ResidueField R) (CotangentSpace R)`.

Rewrite using `[IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Use linear arithmetic over natural numbers and integers. Establish `hdom` using `IH (R ⧸ Ideal.span ({x} : Set R)) hlt`. Establish `hprime : (Ideal.span ({x} : Set R)).IsPrime` using `(Ideal.Quotient.isDomain_iff_prime _).mp hdom`. Take `⟨p, hp, hple⟩` from `Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R))`.

Establish `hpp : p.IsPrime` using `isPrime_of_mem_minimalPrimes hp`. Establish `hpbot : p = ⊥`. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p (IsNoetherian.noetherian p) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)` and prove the remaining obligations. Introduce `y hy`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton.mp (hple hy)`.

Establish `ha : a ∈ p`. Break down `hpp.mem_or_mem hy with hh | hh` into its components or cases. Conclude with `absurd hh (hxp p hp)`. Conclude with `hh`. Conclude with `Ideal.mul_mem_mul hx ha`.

Rewrite `hpp` using `[hpbot]`. Use `hpp` as an intermediate fact. Conclude with `IsDomain.of_bot_isPrime R`.
-/
private theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hple⟩ := hmin
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpm : p = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpp.ne_top) hple
    have hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R := by
      intro q hq
      refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_
      rw [← hpm]
      exact le_of_le_of_mem_minimalPrimes hp hq
        (by rw [hpm]; exact IsLocalRing.le_maximalIdeal hq.ne_top)
    have h2 : ringKrullDim R ≤ 0 := by
      have hPQ : ∀ P Q : PrimeSpectrum R, P = Q := by
        intro P Q
        apply PrimeSpectrum.ext
        rw [hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]
      have : Subsingleton (PrimeSpectrum R) := ⟨hPQ⟩
      exact Order.krullDim_nonpos_of_subsingleton
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have := isLocalRing_quotient_span_singleton hx
    have hpos := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
    have hdim : ringKrullDim R =
        (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
      ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm
    rw [hdim] at h2
    have hle0 : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 0 := by exact_mod_cast h2
    omega
  · obtain ⟨x, hx, hx2, hxp⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
    have := isLocalRing_quotient_span_singleton hx
    have hrq : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
      isRegularLocalRing_quotient_span_singleton hx hx2
    have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) <
        Submodule.spanFinrank (maximalIdeal R) := by
      have h1 := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
      have h2 : Submodule.spanFinrank (maximalIdeal R)
          = Module.finrank (ResidueField R) (CotangentSpace R) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
      omega
    have hdom := IH (R ⧸ Ideal.span ({x} : Set R)) hlt
    have hprime : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hp, hple⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R))
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpbot : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp (hple hy)
      have ha : a ∈ p := by
        rcases hpp.mem_or_mem hy with hh | hh
        · exact absurd hh (hxp p hp)
        · exact hh
      exact Ideal.mul_mem_mul hx ha
    rw [hpbot] at hpp
    have := hpp
    exact IsDomain.of_bot_isPrime R

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `R _ _ h`. Use `isDomain_of_forall_spanFinrank_lt R ?_` and prove the remaining obligations.

Introduce `S _ _ hS`. Conclude with `absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)`. Consider the case `succ n IH`. Introduce `R _ _ h`. Use `isDomain_of_forall_spanFinrank_lt R ?_` and prove the remaining obligations.

Introduce `S _ _ hS`. Conclude with `IH S (by omega)`.
-/
private theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact IH S (by omega)

/- English proof (translation)
The claim follows from `isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl`.
-/
theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

/- English proof (translation)
Establish `key : ∑ k ∈ ({i, j} : Finset ι), (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0`. Rewrite using `[Finset.sum_pair hij]`. Simplify using `[Ne.symm hij, he]`. Establish `h2` using `linearIndependent_iff'.mp h {i, j} (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)`. Simplify using `[Ne.symm hij] at h2`.
-/
private theorem false_of_eq_smul_of_linearIndependent {K M : Type*} {ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0 := by
    rw [Finset.sum_pair hij]
    simp [Ne.symm hij, he]
  have h2 := linearIndependent_iff'.mp h {i, j}
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)
  simp [Ne.symm hij] at h2

/- English proof (translation)
Establish `h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R) = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R)` using `Subtype.ext rfl`. Rewrite using `[algebraMap_smul, h1, map_smul]`.
-/
private theorem toCotangent_mul_eq_smul {R : Type*} [CommRing R] [IsLocalRing R] (r a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hra : r * a ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R).toCotangent ⟨r * a, hra⟩ : IsLocalRing.CotangentSpace R) =
      algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩ : IsLocalRing.CotangentSpace R) := by
  have h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R)
      = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R) := Subtype.ext rfl
  rw [algebraMap_smul, h1, map_smul]

/- English proof (translation)
Introduce `hmem`. Establish `h0 : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ : IsLocalRing.CotangentSpace R) = 0`. Rewrite using `[Ideal.toCotangent_eq_zero]`. Conclude with `hmem`. Conclude with `hli.ne_zero i h0`.
-/
theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : x i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  have h0 : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
      IsLocalRing.CotangentSpace R) = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    exact hmem
  exact hli.ne_zero i h0

/- English proof (translation)
Establish `: IsRegularLocalRing (R ⧸ Ideal.span ({x i} : Set R))` using `isRegularLocalRing_quotient_span_singleton (hx i) (notMem_maximalIdeal_sq x hx hli i)`. Rewrite using `[← Ideal.Quotient.isDomain_iff_prime]`. Conclude with `IsRegularLocalRing.isDomain _`.
-/
theorem isPrime_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : (Ideal.span ({x i} : Set R)).IsPrime := by
  have : IsRegularLocalRing (R ⧸ Ideal.span ({x i} : Set R)) :=
    isRegularLocalRing_quotient_span_singleton (hx i) (notMem_maximalIdeal_sq x hx hli i)
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact IsRegularLocalRing.isDomain _

/- English proof (translation)
Introduce `hmem`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[hr]`. Conclude with `hx j`.

Establish `key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ : IsLocalRing.CotangentSpace R) = algebraMap R (IsLocalRing.ResidueField R) r • ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ : IsLocalRing.CotangentSpace R)`. Establish `hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩` using `Subtype.ext hr.symm`. Rewrite using `[hsub]`. Conclude with `toCotangent_mul_eq_smul r (x i) (hx i) hmem2`. Conclude with `false_of_eq_smul_of_linearIndependent hli hij _ key`.
-/
theorem notMem_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R := by
    rw [hr]
    exact hx j
  have key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ :
      IsLocalRing.CotangentSpace R)
      = algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
          IsLocalRing.CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩ :=
      Subtype.ext hr.symm
    rw [hsub]
    exact toCotangent_mul_eq_smul r (x i) (hx i) hmem2
  exact false_of_eq_smul_of_linearIndependent hli hij _ key

/- English proof (translation)
Conclude with `FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ (fun i _ => isPrime_span_singleton x hx hli i) (fun i _ j _ hij => notMem_span_singleton x hx hli hij)`.
-/
theorem isRadical_span_singleton_prod {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)

end IsRegularLocalRing
