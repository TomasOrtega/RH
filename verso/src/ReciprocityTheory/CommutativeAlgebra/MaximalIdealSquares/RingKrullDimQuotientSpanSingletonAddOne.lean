import Mathlib

namespace ReciprocityTheory.CA.AB.RegA

namespace IsRegularLocalRing

open IsLocalRing

universe u

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem spanFinrank_span_finset_le {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  calc Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ (s : Set R).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet
    _ = s.card := Set.ncard_coe_finset s

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv (b.repr.map_eq_zero_iff.mp (Finsupp.ext fun j => by simpa using h j))`.
-/
theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push_neg at h
  exact hv (b.repr.map_eq_zero_iff.mp (Finsupp.ext fun j => by simpa using h j))

/- English proof (translation)
Use `set W := Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) with hW`. Establish `hbi : ∀ i, i ≠ j → b i ∈ W` using `fun i hi => Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hi], rfl⟩)`. Establish `hvW : v ∈ W` using `Submodule.subset_span (Set.mem_insert _ _)`. Establish `hbj : b j ∈ W`. Establish `hsum` using `b.sum_repr v`.

Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ j)]`. Establish `h2 : (∑ i ∈ Finset.univ.erase j, b.repr v i • b i) ∈ W` using `Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hbi i (Finset.ne_of_mem_erase hi))`. Establish `h3 : b.repr v j • b j ∈ W`. Rewrite using `[eq_sub_of_add_eq hsum]`. Conclude with `Submodule.sub_mem _ hvW h2`.

Establish `h4` using `Submodule.smul_mem W (b.repr v j)⁻¹ h3`. Rewrite `h4` using `[smul_smul, inv_mul_cancel₀ hj, one_smul]`. Then use the resulting hypothesis. Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `hi : i = j`.

Rewrite using `[hi]`. Conclude with `hbj`. Conclude with `hbi i hi`.
-/
theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  classical
  set W := Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) with hW
  have hbi : ∀ i, i ≠ j → b i ∈ W := fun i hi =>
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hi], rfl⟩)
  have hvW : v ∈ W := Submodule.subset_span (Set.mem_insert _ _)
  have hbj : b j ∈ W := by
    have hsum := b.sum_repr v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
    have h2 : (∑ i ∈ Finset.univ.erase j, b.repr v i • b i) ∈ W :=
      Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hbi i (Finset.ne_of_mem_erase hi))
    have h3 : b.repr v j • b j ∈ W := by
      rw [eq_sub_of_add_eq hsum]
      exact Submodule.sub_mem _ hvW h2
    have h4 := Submodule.smul_mem W (b.repr v j)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h4
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = j
  · rw [hi]; exact hbj
  · exact hbi i hi

/- English proof (translation)
Establish `hI : Ideal.span ({x} : Set R) ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Conclude with `(IsLocalRing.mem_maximalIdeal x).mp hx`. Establish `: Nontrivial (R ⧸ Ideal.span ({x} : Set R))` using `by first`. Consider the case `exact Ideal.Quotient.nontrivial_iff.mpr hI`.

Consider the case `exact ⟨⟨0, 1, fun h => hI ((Ideal.eq_top_iff_one _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_one]; exact h.symm)))⟩⟩`. Conclude with `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`.
-/
theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hI : Ideal.span ({x} : Set R) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.mpr hI
    | exact ⟨⟨0, 1, fun h => hI ((Ideal.eq_top_iff_one _).mpr
        (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_one]; exact h.symm)))⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/- English proof (translation)
Establish `hne : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0` using `fun h => hx2 ((Ideal.toCotangent_eq_zero _ _).mp h)`. Take `⟨j, hj⟩` from `exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hne`. Establish `hspan` using `span_insert_image_erase_eq_top (Module.finBasis (ResidueField R) (CotangentSpace R)) _ hj`. Use `choose y hy using fun i => Ideal.toCotangent_surjective (maximalIdeal R) (Module.finBasis (ResidueField R) (CotangentSpace R) i)`. Establish `htop : Submodule.span R (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j))) = ⊤`.

Apply `IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp` to reduce the goal to its premises. Rewrite using `[Set.image_insert_eq, Set.image_image]`. Simplify using `only [hy]`. Conclude with `hspan`. Establish `hm : Ideal.span (Subtype.val '' (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) = maximalIdeal R`.

Establish `h1` using `congrArg (Submodule.map (maximalIdeal R).subtype) htop`. Use `first`. Consider the case `rw [Submodule.map_span, Submodule.map_subtype_top] at h1`. Consider the case `rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h1`. Use `first`.

Consider the case `exact h1`. Consider the case `simpa using h1`. Establish `hcomap : (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))).comap (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = maximalIdeal R` using `IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)`. Establish `hmax : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) = Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (Ideal.span (Subtype.val '' (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))))`. Rewrite using `[hm, ← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`.

Establish `hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)`. Establish `hset : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) '' (Subtype.val '' (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) = insert 0 (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Se …`. Simplify using `only [Set.image_insert_eq, Set.image_image, Finset.coe_image, Subtype.coe_mk, hx0]`. Rewrite using `[hmax, Ideal.map_span, hset]`. Establish `hz : Ideal.span (insert (0 : (R ⧸ Ideal.span ({x} : Set R))) (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R)))) = Ideal.span (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.spa …` using `Submodule.span_insert_zero`.

Rewrite using `[hz]`. Establish `h1` using `spanFinrank_span_finset_le ((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R)))`. Establish `h2` using `Finset.card_image_le (s := Finset.univ.erase j) (f := fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))`. Establish `h3` using `Finset.card_erase_of_mem (Finset.mem_univ j)`. Rewrite `h3` using `[Finset.card_univ, Fintype.card_fin]`.

Establish `h4` using `j.pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem spanFinrank_maximalIdeal_quotient_succ_le (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hne : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := fun h =>
    hx2 ((Ideal.toCotangent_eq_zero _ _).mp h)
  obtain ⟨j, hj⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hne
  have hspan := span_insert_image_erase_eq_top
    (Module.finBasis (ResidueField R) (CotangentSpace R)) _ hj
  choose y hy using fun i => Ideal.toCotangent_surjective (maximalIdeal R)
    (Module.finBasis (ResidueField R) (CotangentSpace R) i)
  have htop : Submodule.span R
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j))) = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [Set.image_insert_eq, Set.image_image]
    simp only [hy]
    exact hspan
  have hm : Ideal.span (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) = maximalIdeal R := by
    have h1 := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    first
    | rw [Submodule.map_span, Submodule.map_subtype_top] at h1
    | rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h1
    first
    | exact h1
    | simpa using h1
  have hcomap : (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))).comap (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmax : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) = Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (Ideal.span (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j))))) := by
    rw [hm, ← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have hset : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) '' (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) =
      insert 0 (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R))) := by
    simp only [Set.image_insert_eq, Set.image_image, Finset.coe_image, Subtype.coe_mk, hx0]
  rw [hmax, Ideal.map_span, hset]
  have hz : Ideal.span (insert (0 : (R ⧸ Ideal.span ({x} : Set R)))
      (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R)))) =
      Ideal.span (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R))) :=
    Submodule.span_insert_zero
  rw [hz]
  have h1 := spanFinrank_span_finset_le ((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R)))
  have h2 := Finset.card_image_le (s := Finset.univ.erase j) (f := fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))
  have h3 := Finset.card_erase_of_mem (Finset.mem_univ j)
  rw [Finset.card_univ, Fintype.card_fin] at h3
  have h4 := j.pos
  omega

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => first`. Consider the case `simp at h1`. Consider the case `exact absurd h1 (by simp)`. Consider the case `coe e`.

Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction. Establish `h2' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞)` using `h2`. Conclude with `absurd (WithBot.coe_le_coe.mp h2') (not_le.mpr (ENat.coe_lt_top d))`.

Consider the case `coe m`. Establish `h1' : n ≤ m + 1` using `by first`. Consider the case `exact_mod_cast h1`. Consider the case `(have h1'' := WithBot.coe_le_coe.mp h1; exact_mod_cast h1'')`. Establish `h2' : m ≤ d` using `by first`.

Consider the case `exact_mod_cast h2`. Consider the case `(have h2'' := WithBot.coe_le_coe.mp h2; exact_mod_cast h2'')`. Establish `hm : m = d` using `by omega`. Establish `hn : m + 1 = n` using `by omega`. Substitute `hm` using the available equality.

Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `first | rfl | norm_cast | simp`. Apply the tactic sequence `rw [← hn] first | rfl | norm_cast | simp`.
-/
theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    first
    | simp at h1
    | exact absurd h1 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := h2
      exact absurd (WithBot.coe_le_coe.mp h2') (not_le.mpr (ENat.coe_lt_top d))
    | coe m =>
      have h1' : n ≤ m + 1 := by
        first
        | exact_mod_cast h1
        | (have h1'' := WithBot.coe_le_coe.mp h1; exact_mod_cast h1'')
      have h2' : m ≤ d := by
        first
        | exact_mod_cast h2
        | (have h2'' := WithBot.coe_le_coe.mp h2; exact_mod_cast h2'')
      have hm : m = d := by omega
      have hn : m + 1 = n := by omega
      subst hm
      constructor
      · first | rfl | norm_cast | simp
      · rw [← hn]
        first | rfl | norm_cast | simp

/- English proof (translation)
Establish `hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R` using `by first`. Consider the case `exact IsRegularLocalRing.spanFinrank_maximalIdeal`. Consider the case `exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm`. Establish `hlink : Submodule.spanFinrank (maximalIdeal R) = Module.finrank (ResidueField R) (CotangentSpace R)` using `by first`. Consider the case `exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`.

Consider the case `exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)`. Consider the case `exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm`. Establish `h5` using `spanFinrank_maximalIdeal_quotient_succ_le R hx hx2`. Establish `hxj : (((({x} : Finset R)) : Set R)) ⊆ (Ring.jacobson R : Set R)`. Introduce `z hz`.

Establish `hz' : z = x` using `by simpa using hz`. Rewrite using `[hz']`. Use `first`. Consider the case `exact (Ideal.jacobson_bot (R := R)) ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥ hx`. Consider the case `exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx`.

Consider the case `(rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx)`. Consider the case `(rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hx)`. Establish `hd` using `ringKrullDim_le_ringKrullDim_quotient_add_card ({x} : Finset R) hxj`. Simplify using `only [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at hd`. Establish `hle` using `ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))`.

Take `⟨e1, e2⟩` from `eq_natCast_and_add_one_eq_of_le (a := ringKrullDim (R ⧸ Ideal.span ({x} : Set R))) (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R)))) (n := Submodule.spanFinrank (maximalIdeal R)) (by`. Rewrite using `[hreg]`. Use `first`. Consider the case `exact hd`. Consider the case `(rw [Finset.coe_singleton] at hd; exact hd)`.

Consider the case `(convert hd using 3 <;> simp)) hle (by omega)`. Conclude with `⟨e1.symm, e2.trans hreg⟩`.
-/
theorem spanFinrank_quotient_eq_and_ringKrullDim_add_one (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    first
    | exact IsRegularLocalRing.spanFinrank_maximalIdeal
    | exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlink : Submodule.spanFinrank (maximalIdeal R) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    first
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    | exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm
  have h5 := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have hxj : (((({x} : Finset R)) : Set R)) ⊆ (Ring.jacobson R : Set R) := by
    intro z hz
    have hz' : z = x := by simpa using hz
    rw [hz']
    first
    | exact (Ideal.jacobson_bot (R := R)) ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥ hx
    | exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx
    | (rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx)
    | (rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hx)
  have hd := ringKrullDim_le_ringKrullDim_quotient_add_card ({x} : Finset R) hxj
  simp only [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at hd
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  obtain ⟨e1, e2⟩ := eq_natCast_and_add_one_eq_of_le (a := ringKrullDim (R ⧸ Ideal.span ({x} : Set R)))
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Submodule.spanFinrank (maximalIdeal R)) (by
      rw [hreg]
      first
      | exact hd
      | (rw [Finset.coe_singleton] at hd; exact hd)
      | (convert hd using 3 <;> simp)) hle (by omega)
  exact ⟨e1.symm, e2.trans hreg⟩

/- English proof (translation)
Use `first`. Consider the case `exact Ideal.minimalPrimes_isPrime hp`. Consider the case `exact hp.1.1`.
-/
theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := by
  first
  | exact Ideal.minimalPrimes_isPrime hp
  | exact hp.1.1

/- English proof (translation)
Use `first`. Consider the case `exact hp.2 ⟨hq, bot_le⟩ hle`. Consider the case `exact Minimal.le_of_le hp ⟨hq, bot_le⟩ hle`.
-/
theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q := by
  first
  | exact hp.2 ⟨hq, bot_le⟩ hle
  | exact Minimal.le_of_le hp ⟨hq, bot_le⟩ hle

/- English proof (translation)
Establish `: NoZeroDivisors R` using `⟨fun {a b} hab => by`. Establish `h2 : a * b ∈ (⊥ : Ideal R)` using `by rw [hab]; exact Submodule.zero_mem _`. Break down `h.mem_or_mem h2 with h3 | h3` into its components or cases. Conclude with `Or.inl (Ideal.mem_bot.mp h3)`. Conclude with `Or.inr (Ideal.mem_bot.mp h3)⟩`.

Conclude with `NoZeroDivisors.to_isDomain R`.
-/
private theorem isDomain_of_bot_isPrime {R : Type*} [CommRing R] [Nontrivial R]
    (h : (⊥ : Ideal R).IsPrime) : IsDomain R := by
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    have h2 : a * b ∈ (⊥ : Ideal R) := by rw [hab]; exact Submodule.zero_mem _
    rcases h.mem_or_mem h2 with h3 | h3
    · exact Or.inl (Ideal.mem_bot.mp h3)
    · exact Or.inr (Ideal.mem_bot.mp h3)⟩
  exact NoZeroDivisors.to_isDomain R

/- English proof (translation)
Establish `hbot : (⊥ : Ideal R).IsPrime`. Rewrite using `[← h]`. Use `infer_instance`. Conclude with `isDomain_of_bot_isPrime hbot`.
-/
theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hbot : (⊥ : Ideal R).IsPrime := by
    rw [← h]
    infer_instance
  exact isDomain_of_bot_isPrime hbot

/- English proof (translation)
Establish `hfg : (maximalIdeal R).FG` using `IsNoetherian.noetherian _`. Establish `hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R`. Rewrite using `[Ideal.smul_eq_mul, ← sq]`. Conclude with `h`. Establish `hjac : maximalIdeal R ≤ Ideal.jacobson ⊥` using `by first`.

Consider the case `exact IsLocalRing.maximalIdeal_le_jacobson ⊥`. Consider the case `exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge`. Conclude with `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac`.
-/
theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := by
    rw [Ideal.smul_eq_mul, ← sq]
    exact h
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    first
    | exact IsLocalRing.maximalIdeal_le_jacobson ⊥
    | exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac

/- English proof (translation)
Establish `hfin : (minimalPrimes R).Finite` using `by first`. Consider the case `exact minimalPrimes.finite_of_isNoetherianRing R`. Consider the case `exact minimalPrimes.finite_of_isNoetherianRing (R := R)`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hsub : ((maximalIdeal R : Set R)) ⊆ ⋃ i ∈ (↑(insert (maximalIdeal R ^ 2) hfin.toFinset) : Set (Ideal R)), (i : Set R)`. Introduce `z hz`. Simplify using `only [Set.mem_iUnion]`. Distinguish the cases in `h2 : z ∈ maximalIdeal R ^ 2`. Conclude with `⟨maximalIdeal R ^ 2, by simp, h2⟩`.

Take `⟨p, hp, hzp⟩` from `hcon z hz h2`. Conclude with `⟨p, by simp [hp], hzp⟩`. Take `⟨i, hi, hle⟩` from `(Ideal.subset_union_prime (f := fun i : Ideal R => i) (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) (by`. Introduce `i hi hne _`. Rewrite `hi` using `[Finset.mem_insert, Set.Finite.mem_toFinset]`.

Conclude with `isPrime_of_mem_minimalPrimes (hi.resolve_left hne))).mp hsub`. Rewrite `hi` using `[Finset.mem_insert, Set.Finite.mem_toFinset]`. Break down `hi with rfl | hi` into its components or cases. Conclude with `hsq hle`. Conclude with `hmin ⟨i, hi, hle⟩`.
-/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hfin : (minimalPrimes R).Finite := by
    first
    | exact minimalPrimes.finite_of_isNoetherianRing R
    | exact minimalPrimes.finite_of_isNoetherianRing (R := R)
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal R : Set R)) ⊆ ⋃ i ∈ (↑(insert (maximalIdeal R ^ 2) hfin.toFinset) :
      Set (Ideal R)), (i : Set R) := by
    intro z hz
    simp only [Set.mem_iUnion]
    by_cases h2 : z ∈ maximalIdeal R ^ 2
    · exact ⟨maximalIdeal R ^ 2, by simp, h2⟩
    · obtain ⟨p, hp, hzp⟩ := hcon z hz h2
      exact ⟨p, by simp [hp], hzp⟩
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := fun i : Ideal R => i)
    (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) (by
      intro i hi hne _
      rw [Finset.mem_insert, Set.Finite.mem_toFinset] at hi
      exact isPrime_of_mem_minimalPrimes (hi.resolve_left hne))).mp hsub
  rw [Finset.mem_insert, Set.Finite.mem_toFinset] at hi
  rcases hi with rfl | hi
  · exact hsq hle
  · exact hmin ⟨i, hi, hle⟩

/- English proof (translation)
Use `haveI := isLocalRing_quotient_span_singleton hx`. Establish `h` using `(spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).1`. Use `first`. Consider the case `exact ⟨h⟩`. Consider the case `exact { spanFinrank_maximalIdeal := h }`.

Consider the case `exact ⟨inferInstance, inferInstance, h⟩`. Consider the case `constructor`.
-/
theorem quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  haveI := isLocalRing_quotient_span_singleton hx
  have h := (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).1
  first
  | exact ⟨h⟩
  | exact { spanFinrank_maximalIdeal := h }
  | exact ⟨inferInstance, inferInstance, h⟩
  | constructor

/- English proof (translation)
Use `haveI := isLocalRing_quotient_span_singleton hx`. Conclude with `(spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2`.
-/
theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  haveI := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2

/- English proof (translation)
Introduce `z hz`. Assume the negation of the conclusion as `hz2`. Establish `hne : (maximalIdeal R).toCotangent ⟨z, hz⟩ ≠ 0` using `fun h' => hz2 ((Ideal.toCotangent_eq_zero _ _).mp h')`. Take `⟨j, _⟩` from `exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hne`. Conclude with `(Fin.cast h j).elim0`.
-/
private theorem maximalIdeal_le_sq_of_finrank_cotangent_zero (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : Module.finrank (ResidueField R) (CotangentSpace R) = 0) :
    maximalIdeal R ≤ maximalIdeal R ^ 2 := by
  intro z hz
  by_contra hz2
  have hne : (maximalIdeal R).toCotangent ⟨z, hz⟩ ≠ 0 := fun h' =>
    hz2 ((Ideal.toCotangent_eq_zero _ _).mp h')
  obtain ⟨j, _⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hne
  exact (Fin.cast h j).elim0

/- English proof (translation)
Distinguish the cases in `hsq : maximalIdeal R ≤ maximalIdeal R ^ 2`. Conclude with `isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)`. Establish `hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R` using `by first`. Consider the case `exact IsRegularLocalRing.spanFinrank_maximalIdeal`. Consider the case `exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm`.

Establish `hlink : Submodule.spanFinrank (maximalIdeal R) = Module.finrank (ResidueField R) (CotangentSpace R)` using `by first`. Consider the case `exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`. Consider the case `exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)`. Consider the case `exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm`. Distinguish the cases in `hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p`.

It suffices to derive a contradiction. Take `⟨p, hp, hle⟩` from `hmin`. Establish `hall : ∀ q : PrimeSpectrum R, q.asIdeal = maximalIdeal R` using `fun q => by`. Establish `h1 : q.asIdeal ≤ maximalIdeal R` using `IsLocalRing.le_maximalIdeal q.isPrime.ne_top`. Establish `h2 : p ≤ q.asIdeal` using `le_of_le_of_mem_minimalPrimes hp q.isPrime (h1.trans hle)`.

Conclude with `le_antisymm h1 (hle.trans h2)`. Establish `hdim : ringKrullDim R ≤ 0` using `by first`. Consider the case `apply iSup_le`. Consider the case `(unfold ringKrullDim Order.krullDim; apply iSup_le)`. Introduce `l`.

Establish `hl : l.length = 0`. Assume the negation of the conclusion as `hl`. Establish `hpos : 0 < l.length` using `Nat.pos_of_ne_zero hl`. Establish `hs` using `l.step ⟨0, hpos⟩`. Establish `he : l.toFun (Fin.castSucc ⟨0, hpos⟩) = l.toFun (Fin.succ ⟨0, hpos⟩)` using `PrimeSpectrum.ext ((hall _).trans (hall _).symm)`.

Conclude with `(ne_of_lt hs) he`. Simplify using `[hl]`. Establish `h0' : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) ≤ 0`. Rewrite using `[hreg]`. Conclude with `hdim`.

Establish `h0 : Submodule.spanFinrank (maximalIdeal R) = 0` using `by first`. Consider the case `exact Nat.le_zero.mp (by exact_mod_cast h0')`. Consider the case `(norm_cast at h0'; omega)`. Consider the case `simpa using h0'`. Conclude with `hsq (maximalIdeal_le_sq_of_finrank_cotangent_zero R (hlink.symm.trans h0))`.

Take `⟨x, hx, hx2, hxmin⟩` from `exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin`. Use `haveI hR' : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := quotient_span_singleton hx hx2`. Establish `h7` using `spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2`. Establish `hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) < Submodule.spanFinrank (maximalIdeal R)`. Establish `e : ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞) + 1 = ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞)`.

Rewrite using `[h7.1, h7.2, hreg]`. Establish `e' : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 = Submodule.spanFinrank (maximalIdeal R)`. Conclude with `e` after adjusting the coercions. Use linear arithmetic over natural numbers and integers. Establish `hdom : IsDomain (R ⧸ Ideal.span ({x} : Set R))` using `IH _ hlt`.

Establish `hprime : (Ideal.span ({x} : Set R)).IsPrime` using `(Ideal.Quotient.isDomain_iff_prime _).mp hdom`. Use `haveI := hprime`. Take `⟨p, hp, hple⟩` from `Ideal.exists_minimalPrimes_le (I := ⊥) (J := Ideal.span ({x} : Set R)) bot_le`. Establish `hpp : p.IsPrime` using `isPrime_of_mem_minimalPrimes hp`. Establish `hxp : x ∉ p` using `hxmin p hp`.

Establish `hle : p ≤ Ideal.span ({x} : Set R) • p`. Introduce `z hz`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.mp (hple hz)`. Establish `hw : w ∈ p` using `(hpp.mem_or_mem hz).resolve_right hxp`. Rewrite using `[mul_comm]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hw`. Establish `hjac : Ideal.span ({x} : Set R) ≤ Ideal.jacobson ⊥`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Use `first`. Consider the case `exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx`.

Consider the case `exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm ▸ hx`. Establish `hbot : p = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian p) hle hjac`. Rewrite `hpp` using `[hbot]`. Conclude with `isDomain_of_bot_isPrime hpp`.
-/
theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  have hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    first
    | exact IsRegularLocalRing.spanFinrank_maximalIdeal
    | exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlink : Submodule.spanFinrank (maximalIdeal R) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    first
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    | exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hle⟩ := hmin
    have hall : ∀ q : PrimeSpectrum R, q.asIdeal = maximalIdeal R := fun q => by
      have h1 : q.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal q.isPrime.ne_top
      have h2 : p ≤ q.asIdeal := le_of_le_of_mem_minimalPrimes hp q.isPrime (h1.trans hle)
      exact le_antisymm h1 (hle.trans h2)
    have hdim : ringKrullDim R ≤ 0 := by
      first
      | apply iSup_le
      | (unfold ringKrullDim Order.krullDim; apply iSup_le)
      intro l
      have hl : l.length = 0 := by
        by_contra hl
        have hpos : 0 < l.length := Nat.pos_of_ne_zero hl
        have hs := l.step ⟨0, hpos⟩
        have he : l.toFun (Fin.castSucc ⟨0, hpos⟩) = l.toFun (Fin.succ ⟨0, hpos⟩) :=
          PrimeSpectrum.ext ((hall _).trans (hall _).symm)
        exact (ne_of_lt hs) he
      simp [hl]
    have h0' : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) ≤ 0 := by
      rw [hreg]; exact hdim
    have h0 : Submodule.spanFinrank (maximalIdeal R) = 0 := by
      first
      | exact Nat.le_zero.mp (by exact_mod_cast h0')
      | (norm_cast at h0'; omega)
      | simpa using h0'
    exact hsq (maximalIdeal_le_sq_of_finrank_cotangent_zero R (hlink.symm.trans h0))
  obtain ⟨x, hx, hx2, hxmin⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
  haveI hR' : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := quotient_span_singleton hx hx2
  have h7 := spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2
  have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) < Submodule.spanFinrank (maximalIdeal R) := by
    have e : ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞) + 1 =
        ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) := by
      rw [h7.1, h7.2, hreg]
    have e' : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 =
        Submodule.spanFinrank (maximalIdeal R) := by
      exact_mod_cast e
    omega
  have hdom : IsDomain (R ⧸ Ideal.span ({x} : Set R)) := IH _ hlt
  have hprime : (Ideal.span ({x} : Set R)).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  haveI := hprime
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Ideal.span ({x} : Set R)) bot_le
  have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
  have hxp : x ∉ p := hxmin p hp
  have hle : p ≤ Ideal.span ({x} : Set R) • p := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp (hple hz)
    have hw : w ∈ p := (hpp.mem_or_mem hz).resolve_right hxp
    rw [mul_comm]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hw
  have hjac : Ideal.span ({x} : Set R) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_singleton_le_iff_mem]
    first
    | exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx
    | exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm ▸ hx
  have hbot : p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian p) hle hjac
  rw [hbot] at hpp
  exact isDomain_of_bot_isPrime hpp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `R _ _ h`. Conclude with `isDomain_of_forall_spanFinrank_lt R (fun S _ _ hS => absurd hS (by omega))`.

Consider the case `succ n ih`. Introduce `R _ _ h`. Conclude with `isDomain_of_forall_spanFinrank_lt R (fun S _ _ hS => ih S (by omega))`.
-/
theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    exact isDomain_of_forall_spanFinrank_lt R (fun S _ _ hS => absurd hS (by omega))
  | succ n ih =>
    intro R _ _ h
    exact isDomain_of_forall_spanFinrank_lt R (fun S _ _ hS => ih S (by omega))

/- English proof (translation)
The claim follows from `isDomain_of_spanFinrank_le _ R le_rfl`.
-/
theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R := isDomain_of_spanFinrank_le _ R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

end IsRegularLocalRing

end ReciprocityTheory.CA.AB.RegA
