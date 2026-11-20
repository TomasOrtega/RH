import Mathlib

namespace GlobalTheory.MultipleMembershipForAll

open IsLocalRing

/- English proof (translation)
Take `⟨s, hs⟩` from `hQ`. It suffices to establish `H : ∀ s' : Finset S, (s' : Set S) ⊆ Q → ∃ g ∉ Q, ∀ x ∈ Ideal.span (s' : Set S), g * x ∈ I by`. Take `⟨g, hg, hgI⟩` from `H s (by rw [← hs]; exact Submodule.subset_span)`. Conclude with `⟨g, hg, fun x hx => hgI x (by rw [hs]; exact hx)⟩`. Introduce `s'`.

Proceed by induction on `s' using Finset.induction_on with`. Consider the case `empty`. Introduce `_`. Use `⟨1, fun h1 => hQp.ne_top ((Ideal.eq_top_iff_one Q).mpr h1), fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[Finset.coe_empty, Ideal.span_empty, Ideal.mem_bot]`.

Simplify using `[hx]`. Consider the case `insert a s' ha ih`. Introduce `hsub`. Rewrite `hsub` using `[Finset.coe_insert]`. Take `⟨g, hg, hgI⟩` from `ih ((Set.subset_insert _ _).trans hsub)`.

Take `⟨ga, hga, hgaI⟩` from `h a (hsub (Set.mem_insert _ _))`. Use `⟨ga * g, fun hm => (hQp.mem_or_mem hm).elim hga hg, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[Finset.coe_insert, Ideal.span_insert, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `hx`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`.

Establish `e1 : ga * g * (r * a + z) = (r * g) * (ga * a) + ga * (g * z)` using `by ring`. Rewrite using `[e1]`. Conclude with `I.add_mem (I.mul_mem_left _ hgaI) (I.mul_mem_left _ (hgI z hz))`.
-/
theorem exists_mul_mem_of_forall {S : Type} [CommRing S] (Q I : Ideal S) [hQp : Q.IsPrime]
    (hQ : Q.FG) (h : ∀ x ∈ Q, ∃ g ∉ Q, g * x ∈ I) : ∃ g ∉ Q, ∀ x ∈ Q, g * x ∈ I := by
  classical
  obtain ⟨s, hs⟩ := hQ

  suffices H : ∀ s' : Finset S, (s' : Set S) ⊆ Q →
      ∃ g ∉ Q, ∀ x ∈ Ideal.span (s' : Set S), g * x ∈ I by
    obtain ⟨g, hg, hgI⟩ := H s (by rw [← hs]; exact Submodule.subset_span)
    exact ⟨g, hg, fun x hx => hgI x (by rw [hs]; exact hx)⟩
  intro s'
  induction s' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨1, fun h1 => hQp.ne_top ((Ideal.eq_top_iff_one Q).mpr h1), fun x hx => ?_⟩
    rw [Finset.coe_empty, Ideal.span_empty, Ideal.mem_bot] at hx
    simp [hx]
  | insert a s' ha ih =>
    intro hsub
    rw [Finset.coe_insert] at hsub
    obtain ⟨g, hg, hgI⟩ := ih ((Set.subset_insert _ _).trans hsub)
    obtain ⟨ga, hga, hgaI⟩ := h a (hsub (Set.mem_insert _ _))
    refine ⟨ga * g, fun hm => (hQp.mem_or_mem hm).elim hga hg, fun x hx => ?_⟩
    rw [Finset.coe_insert, Ideal.span_insert, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e1 : ga * g * (r * a + z) = (r * g) * (ga * a) + ga * (g * z) := by ring
    rw [e1]
    exact I.add_mem (I.mul_mem_left _ hgaI) (I.mul_mem_left _ (hgI z hz))

/- English proof (translation)
Introduce `S _ _ Q _`. Set `R` to `Localization.AtPrime Q`. Establish `: IsNoetherianRing R` using `IsLocalization.isNoetherianRing Q.primeCompl R inferInstance`. Take `⟨t, htcard, htspan⟩` from `(IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank`. Establish `hsurj : ∀ y : R, ∃ p : S × Q.primeCompl, IsLocalization.mk' R p.1 p.2 = y` using `fun y => by`.

Take `⟨p, hp⟩` from `IsLocalization.mk'_surjective Q.primeCompl y`. Conclude with `⟨p, hp⟩`. Use `choose p hxs using hsurj`. Set `x : R → S` to `fun y => (p y).1`. Set `e : Fin t.card → R` to `fun j => (t.equivFin.symm j : R)`.

Set `f : Fin t.card → S` to `fun j => x (e j)`. Establish `he : ∀ j, e j ∈ IsLocalRing.maximalIdeal R` using `fun j => by`. Rewrite using `[← htspan]`. Conclude with `Submodule.subset_span (t.equivFin.symm j).2`. Establish `hfQ : ∀ j, f j ∈ Q` using `fun j => by`.

Establish `h` using `he j`. Rewrite `h` using `[← hxs (e j)]`. Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff R Q _ _).mp h`. Establish `hspan : Ideal.span (Set.range fun j => algebraMap S R (f j)) = IsLocalRing.maximalIdeal R`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr (hfQ j)`. Rewrite using `[← htspan]`. Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations.

Establish `hy' : y = e (t.equivFin ⟨y, hy⟩)` using `by simp [e]`. Rewrite using `[hy', ← hxs (e _), IsLocalization.mk'_eq_mul_mk'_one]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)`. Establish `hloc : ∀ y ∈ Q, ∃ g ∉ Q, g * y ∈ Ideal.span (Set.range f)`. Introduce `y hy`.

Establish `hmem : algebraMap S R y ∈ (Ideal.span (Set.range f)).map (algebraMap S R)`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Express the relevant statement in the definitionally equal form `algebraMap S R y ∈ Ideal.span (Set.range fun j => algebraMap S R (f j))`. Rewrite using `[hspan]`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr hy`.

Take `⟨g, hg, hgy⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl R _ _).mp hmem`. Conclude with `⟨g, hg, hgy⟩`. Take `⟨g, hg, hgQ⟩` from `exists_mul_mem_of_forall Q _ (IsNoetherian.noetherian Q) hloc`. Use `⟨t.card, f, g, hg, hfQ, hgQ, htcard, ?_⟩` and prove the remaining obligations. Introduce `a u hu hsum j0`.

Assume the negation of the conclusion as `hj0`. Use `set E : Fin t.card → R := fun j => algebraMap S R (f j) with hE`. Use `set m := IsLocalRing.maximalIdeal R with hm`. Establish `hA : IsUnit (algebraMap S R (a j0))` using `(IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hj0`. Establish `hU : IsUnit (algebraMap S R u)` using `(IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hu`.

Establish `hsq : ∑ j, algebraMap S R (a j) * E j ∈ m ^ 2`. Establish `h1 : algebraMap S R (u * ∑ j, a j * f j) ∈ m ^ 2`. Rewrite using `[hm, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hsum`. Simplify using `only [map_mul, map_sum] at h1`.

Take `⟨v, hv⟩` from `hU.exists_left_inv`. Establish `h2` using `Ideal.mul_mem_left _ v h1`. Rewrite `h2` using `[← mul_assoc, hv, one_mul]`. Then use the resulting hypothesis. Set `N : Ideal R` to `Ideal.span (((Finset.univ.erase j0).image E : Finset R) : Set R)`. Establish `hEN : ∀ j, j ≠ j0 → E j ∈ N` using `fun j hj => Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem E (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)))`.

Establish `hrest : ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j ∈ N` using `Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hEN j (Finset.ne_of_mem_erase hj))`. Establish `hj0mem : E j0 ∈ N ⊔ m * m`. Establish `hsplit` using `Finset.add_sum_erase Finset.univ (fun j => algebraMap S R (a j) * E j) (Finset.mem_univ j0)`. Establish `h2 : algebraMap S R (a j0) * E j0 ∈ N ⊔ m * m`. Establish `h3 : algebraMap S R (a j0) * E j0 = ∑ j, algebraMap S R (a j) * E j - ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j`.

Rewrite using `[← hsplit]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_right (by rwa [← sq])) (Ideal.mem_sup_left hrest)`. Take `⟨v, hv⟩` from `hA.exists_left_inv`.

Establish `h4` using `Ideal.mul_mem_left _ v h2`. Rewrite `h4` using `[← mul_assoc, hv, one_mul]`. Then use the resulting hypothesis. Establish `hle : m ≤ N ⊔ m • m`. Rewrite using `[Ideal.smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality. Conclude with `hj0mem`.

Conclude with `Ideal.mem_sup_left (hEN j hj)`. Establish `hmN : m ≤ N` using `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle`. Establish `hNm : N ≤ m`. Rewrite using `[Ideal.span_le]`. Introduce `y hy`.

Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp hy`. Rewrite using `[← hspan]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`. Establish `hcard : m.spanFinrank ≤ t.card - 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]`. Establish `hpos : 0 < t.card` using `j0.pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem main : ∀ (S : Type) [inst : CommRing S] [IsNoetherianRing S] (Q : Ideal S)
    [inst_2 : Ideal.IsPrime Q], ∃ (h : ℕ) (f : Fin h → S), ∃ g ∉ Q, (∀ (j : Fin h), f j ∈ Q) ∧
    (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
    h = Submodule.spanFinrank (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
    ∀ (a : Fin h → S), ∀ u ∉ Q, u * ∑ j : Fin h, a j * f j ∈ Q ^ (2 : ℕ) →
      ∀ (j : Fin h), a j ∈ Q := by
  intro S _ _ Q _
  classical
  let R := Localization.AtPrime Q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  obtain ⟨t, htcard, htspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank

  have hsurj : ∀ y : R, ∃ p : S × Q.primeCompl, IsLocalization.mk' R p.1 p.2 = y := fun y => by
    obtain ⟨p, hp⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    exact ⟨p, hp⟩
  choose p hxs using hsurj
  let x : R → S := fun y => (p y).1
  let e : Fin t.card → R := fun j => (t.equivFin.symm j : R)
  let f : Fin t.card → S := fun j => x (e j)
  have he : ∀ j, e j ∈ IsLocalRing.maximalIdeal R := fun j => by
    rw [← htspan]; exact Submodule.subset_span (t.equivFin.symm j).2
  have hfQ : ∀ j, f j ∈ Q := fun j => by
    have h := he j
    rw [← hxs (e j)] at h
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff R Q _ _).mp h

  have hspan : Ideal.span (Set.range fun j => algebraMap S R (f j)) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr (hfQ j)
    · rw [← htspan]
      refine Submodule.span_le.mpr fun y hy => ?_
      have hy' : y = e (t.equivFin ⟨y, hy⟩) := by simp [e]
      rw [hy', ← hxs (e _), IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)

  have hloc : ∀ y ∈ Q, ∃ g ∉ Q, g * y ∈ Ideal.span (Set.range f) := by
    intro y hy
    have hmem : algebraMap S R y ∈ (Ideal.span (Set.range f)).map (algebraMap S R) := by
      rw [Ideal.map_span, ← Set.range_comp]
      change algebraMap S R y ∈ Ideal.span (Set.range fun j => algebraMap S R (f j))
      rw [hspan]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr hy
    obtain ⟨g, hg, hgy⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl R _ _).mp hmem
    exact ⟨g, hg, hgy⟩
  obtain ⟨g, hg, hgQ⟩ := exists_mul_mem_of_forall Q _ (IsNoetherian.noetherian Q) hloc
  refine ⟨t.card, f, g, hg, hfQ, hgQ, htcard, ?_⟩

  intro a u hu hsum j0
  by_contra hj0
  set E : Fin t.card → R := fun j => algebraMap S R (f j) with hE
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : IsUnit (algebraMap S R (a j0)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hj0
  have hU : IsUnit (algebraMap S R u) := (IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hu
  have hsq : ∑ j, algebraMap S R (a j) * E j ∈ m ^ 2 := by
    have h1 : algebraMap S R (u * ∑ j, a j * f j) ∈ m ^ 2 := by
      rw [hm, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hsum
    simp only [map_mul, map_sum] at h1
    obtain ⟨v, hv⟩ := hU.exists_left_inv
    have h2 := Ideal.mul_mem_left _ v h1
    rwa [← mul_assoc, hv, one_mul] at h2
  let N : Ideal R := Ideal.span (((Finset.univ.erase j0).image E : Finset R) : Set R)
  have hEN : ∀ j, j ≠ j0 → E j ∈ N := fun j hj =>
    Ideal.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image_of_mem E (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)))
  have hrest : ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j ∈ N :=
    Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hEN j (Finset.ne_of_mem_erase hj))
  have hj0mem : E j0 ∈ N ⊔ m * m := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => algebraMap S R (a j) * E j)
      (Finset.mem_univ j0)
    have h2 : algebraMap S R (a j0) * E j0 ∈ N ⊔ m * m := by
      have h3 : algebraMap S R (a j0) * E j0 = ∑ j, algebraMap S R (a j) * E j -
          ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j := by
        rw [← hsplit]; ring
      rw [h3]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (by rwa [← sq])) (Ideal.mem_sup_left hrest)
    obtain ⟨v, hv⟩ := hA.exists_left_inv
    have h4 := Ideal.mul_mem_left _ v h2
    rwa [← mul_assoc, hv, one_mul] at h4
  have hle : m ≤ N ⊔ m • m := by
    rw [Ideal.smul_eq_mul]
    calc m = Ideal.span (Set.range E) := hspan.symm
      _ ≤ N ⊔ m * m := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        by_cases hj : j = j0
        · subst hj; exact hj0mem
        · exact Ideal.mem_sup_left (hEN j hj)
  have hmN : m ≤ N := Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  have hNm : N ≤ m := by
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hspan]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hcard : m.spanFinrank ≤ t.card - 1 := by
    calc m.spanFinrank = N.spanFinrank := by rw [le_antisymm hmN hNm]
      _ ≤ (((Finset.univ.erase j0).image E : Finset R) : Set R).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
      _ = ((Finset.univ.erase j0).image E).card := Set.ncard_coe_finset _
      _ ≤ (Finset.univ.erase j0).card := Finset.card_image_le
      _ = t.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hpos : 0 < t.card := j0.pos
  omega

end GlobalTheory.MultipleMembershipForAll
