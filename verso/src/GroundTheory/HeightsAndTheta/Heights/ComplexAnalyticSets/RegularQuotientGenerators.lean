import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing Ideal

universe u

/- English proof (translation)
Take `⟨t, htc, hts⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal (R ⧸ I)))`. Use `choose g hg using fun y : R ⧸ I => Ideal.Quotient.mk_surjective y`. Use `set s : Finset R := t.image g with hs`. Establish `hmk : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk I a ∈ maximalIdeal (R ⧸ I)`. Introduce `a ha`.

Establish `h` using `Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha`. Rewrite `h` using `[map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]`. Then use the resulting hypothesis. Establish `hsm : (s : Set R) ⊆ maximalIdeal R`. Introduce `a ha`. Simplify using `only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha`.

Take `⟨y, hy, rfl⟩` from `ha`. Establish `hy' : y ∈ maximalIdeal (R ⧸ I)` using `hts ▸ Submodule.subset_span hy`. Assume the negation of the conclusion as `hn`. Establish `hu : IsUnit (g y)` using `not_not.mp fun h => hn ((mem_maximalIdeal _).mpr h)`. Conclude with `(mem_maximalIdeal _).mp hy' (hg y ▸ hu.map (Ideal.Quotient.mk I))`.

Establish `hmap : (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I)`. Rewrite using `[Ideal.map_span, hs, Finset.coe_image, ← Set.image_comp, show (Ideal.Quotient.mk I) ∘ g = id from funext hg, Set.image_id]`. Conclude with `hts`. Establish `hle : maximalIdeal R ≤ Ideal.span (s : Set R) ⊔ maximalIdeal R • maximalIdeal R`. Introduce `a ha`.

Establish `h1 : Ideal.Quotient.mk I a ∈ (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I)` using `hmap ▸ hmk a ha`. Rewrite `h1` using `[← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]`. Conclude with `sup_le_sup_left (hI.trans (le_of_eq (by rw [pow_two, Ideal.smul_eq_mul]))) _ h1`. Establish `hm : maximalIdeal R = Ideal.span (s : Set R)` using `le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle) (Ideal.span_le.mpr hsm)`. Rewrite using `[hm, ← htc]`.

Use `(Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet).trans ?_` and prove the remaining obligations. Rewrite using `[Set.ncard_coe_finset]`. Conclude with `Finset.card_image_le`.
-/
theorem spanFinrank_maximalIdeal_le_quotient_of_le_sq {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ I)] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
  classical
  obtain ⟨t, htc, hts⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (R ⧸ I)))
  choose g hg using fun y : R ⧸ I => Ideal.Quotient.mk_surjective y
  set s : Finset R := t.image g with hs
  have hmk : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk I a ∈ maximalIdeal (R ⧸ I) := by
    intro a ha
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha
    rwa [map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective] at h
  have hsm : (s : Set R) ⊆ maximalIdeal R := by
    intro a ha
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hy' : y ∈ maximalIdeal (R ⧸ I) := hts ▸ Submodule.subset_span hy
    by_contra hn
    have hu : IsUnit (g y) := not_not.mp fun h => hn ((mem_maximalIdeal _).mpr h)
    exact (mem_maximalIdeal _).mp hy' (hg y ▸ hu.map (Ideal.Quotient.mk I))
  have hmap : (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
    rw [Ideal.map_span, hs, Finset.coe_image, ← Set.image_comp,
      show (Ideal.Quotient.mk I) ∘ g = id from funext hg, Set.image_id]
    exact hts
  have hle : maximalIdeal R ≤ Ideal.span (s : Set R) ⊔ maximalIdeal R • maximalIdeal R := by
    intro a ha
    have h1 : Ideal.Quotient.mk I a ∈ (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) :=
      hmap ▸ hmk a ha
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker] at h1
    exact sup_le_sup_left (hI.trans (le_of_eq (by rw [pow_two, Ideal.smul_eq_mul]))) _ h1
  have hm : maximalIdeal R = Ideal.span (s : Set R) :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle) (Ideal.span_le.mpr hsm)
  rw [hm, ← htc]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `R _ _ I _ hd`. Use `⟨Fin.elim0, fun j => j.elim0, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.range_eq_empty, Ideal.span_empty]`.

Use `GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := R)` as an intermediate fact. Assume the negation of the conclusion as `hI`. Take `⟨y, hyI, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Establish `h1` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hy0)`. Establish `h2 : ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ Ideal.span {y})` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).mpr hyI)) (Ideal.Quotient.factor_surjective _)`.

Establish `hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞)` using `((isRegularLocalRing_iff R).mp inferInstance).symm`. Rewrite `hd` using `[Nat.cast_zero, add_zero]`. Establish `h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) + 1 ≤ (maximalIdeal R).spanFinrank`. Rewrite using `[← hR]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h4 : (maximalIdeal R).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `R _ _ I _ hd`. Establish `hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞)` using `((isRegularLocalRing_iff R).mp inferInstance).symm`.

Establish `hRI : ringKrullDim (R ⧸ I) = ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞)` using `((isRegularLocalRing_iff (R ⧸ I)).mp inferInstance).symm`. Establish `hdd : (maximalIdeal R).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + (n + 1)`. Rewrite `hd` using `[hR, hRI]`. Conclude with `hd` after adjusting the coercions. Establish `hItop : I ≠ ⊤` using `Ideal.Quotient.nontrivial_iff.mp inferInstance`.

Establish `hIm : I ≤ maximalIdeal R` using `le_maximalIdeal hItop`. Choose the witnesses or unpack the hypotheses as in `⟨x, hxI, hx2⟩ : ∃ x ∈ I, x ∉ maximalIdeal R ^ 2 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `spanFinrank_maximalIdeal_le_quotient_of_le_sq (I := I) h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hxm : x ∈ maximalIdeal R` using `hIm hxI`. Establish `hxI' : Ideal.span {x} ≤ I` using `(Ideal.span_singleton_le_iff_mem I).mpr hxI`. Establish `hne : Ideal.span {x} ≠ ⊤` using `fun h => hItop (top_le_iff.mp (h ▸ hxI'))`. Establish `: Nontrivial (R ⧸ Ideal.span {x})` using `Ideal.Quotient.nontrivial_iff.mpr hne`.

Establish `: IsLocalRing (R ⧸ Ideal.span {x})` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Take `⟨hreg, hdim⟩` from `GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient hxm hx2`. Use `hreg` as an intermediate fact. Set `e` to `DoubleQuot.quotQuotEquivQuotOfLE hxI'`. Establish `: IsRegularLocalRing ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x})))` using `IsRegularLocalRing.of_ringEquiv e.symm`.

Establish `hR' : ringKrullDim (R ⧸ Ideal.span {x}) = ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)` using `((isRegularLocalRing_iff _).mp inferInstance).symm`. Establish `hd' : ringKrullDim (R ⧸ Ideal.span {x}) = ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) + n`. Rewrite using `[ringKrullDim_eq_of_ringEquiv e, hRI, hR']`. Rewrite `hdim` using `[hR, hR']`. Establish `h5 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank`.

Conclude with `hdim` after adjusting the coercions. Establish `h6 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + n`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h6]`. Use `push_cast`.

Both sides reduce to the same expression. Take `⟨f', hf'I, hf'⟩` from `ih _ _ hd'`. Establish `hlift : ∀ j, ∃ a ∈ I, Ideal.Quotient.mk (Ideal.span {x}) a = f' j` using `fun j => (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hf'I j)`. Use `choose g hgI hg using hlift`. Use `⟨(Fin.cons x g : Fin (n + 1) → R), Fin.forall_fin_succ.mpr ⟨by simpa using hxI, fun i => by simpa using hgI i⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.range_cons, Ideal.span_insert]`. Establish `hcomap : I = (I.map (Ideal.Quotient.mk (Ideal.span {x}))).comap (Ideal.Quotient.mk (Ideal.span {x}))`. Rewrite using `[Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hxI']`. Establish `hrange : Set.range f' = Ideal.Quotient.mk (Ideal.span {x}) '' Set.range g`. Rewrite using `[← Set.range_comp]`.

Conclude with `congrArg Set.range (funext hg).symm`. Rewrite using `[hcomap, hf', hrange, ← Ideal.map_span, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]`.
-/
theorem exists_span_eq_of_isRegularLocalRing_quotient (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ringKrullDim R = ringKrullDim (R ⧸ I) + n →
        ∃ f : Fin n → R, (∀ j, f j ∈ I) ∧ I = Ideal.span (Set.range f) := by
  induction n with
  | zero =>
    intro R _ _ I _ hd
    refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := R)
    by_contra hI
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hy0)
    have h2 : ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ Ideal.span {y}) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).mpr hyI))
        (Ideal.Quotient.factor_surjective _)
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    rw [Nat.cast_zero, add_zero] at hd
    have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) + 1 ≤ (maximalIdeal R).spanFinrank := by
      rw [← hR]
      calc ringKrullDim R + 1 = ringKrullDim (R ⧸ I) + 1 := by rw [hd]
        _ ≤ ringKrullDim (R ⧸ Ideal.span {y}) + 1 := by gcongr
        _ ≤ ringKrullDim R := h1
    have h4 : (maximalIdeal R).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by exact_mod_cast h3
    omega
  | succ n ih =>
    intro R _ _ I _ hd
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    have hRI : ringKrullDim (R ⧸ I) = ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff (R ⧸ I)).mp inferInstance).symm
    have hdd : (maximalIdeal R).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + (n + 1) := by
      rw [hR, hRI] at hd
      exact_mod_cast hd
    have hItop : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
    have hIm : I ≤ maximalIdeal R := le_maximalIdeal hItop
    obtain ⟨x, hxI, hx2⟩ : ∃ x ∈ I, x ∉ maximalIdeal R ^ 2 := by
      by_contra h
      push Not at h
      have := spanFinrank_maximalIdeal_le_quotient_of_le_sq (I := I) h
      omega
    have hxm : x ∈ maximalIdeal R := hIm hxI
    have hxI' : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
    have hne : Ideal.span {x} ≠ ⊤ := fun h => hItop (top_le_iff.mp (h ▸ hxI'))
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient hxm hx2
    have := hreg
    let e := DoubleQuot.quotQuotEquivQuotOfLE hxI'
    have : IsRegularLocalRing ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
      IsRegularLocalRing.of_ringEquiv e.symm
    have hR' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff _).mp inferInstance).symm
    have hd' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) + n := by
      rw [ringKrullDim_eq_of_ringEquiv e, hRI, hR']
      rw [hR, hR'] at hdim
      have h5 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
        exact_mod_cast hdim
      have h6 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + n := by
        omega
      rw [h6]
      push_cast
      rfl
    obtain ⟨f', hf'I, hf'⟩ := ih _ _ hd'
    have hlift : ∀ j, ∃ a ∈ I, Ideal.Quotient.mk (Ideal.span {x}) a = f' j := fun j =>
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hf'I j)
    choose g hgI hg using hlift
    refine ⟨(Fin.cons x g : Fin (n + 1) → R), Fin.forall_fin_succ.mpr ⟨by simpa using hxI, fun i => by simpa using hgI i⟩, ?_⟩
    rw [Fin.range_cons, Ideal.span_insert]
    have hcomap : I = (I.map (Ideal.Quotient.mk (Ideal.span {x}))).comap (Ideal.Quotient.mk (Ideal.span {x})) := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hxI']
    have hrange : Set.range f' = Ideal.Quotient.mk (Ideal.span {x}) '' Set.range g := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hg).symm
    rw [hcomap, hf', hrange, ← Ideal.map_span, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_comm]

end GroundTheory.Heights₂.Heights
