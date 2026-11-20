import Mathlib
open Filter
open scoped Classical

namespace GlobalTheory.DoubleCosetEuler

/- English proof (translation)
Establish `h1 : ∀ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), q ≠ DoubleCoset.mk TH KH 1 → f (Quotient.out q) = 0`. Introduce `q hq`. Rewrite using `[hf, if_neg]`. Introduce and unpack `⟨t, ht, k, hk, he⟩`. Apply `hq` to reduce the goal to its premises.

Rewrite using `[← DoubleCoset.out_eq' TH KH q, DoubleCoset.eq]`. Conclude with `⟨t⁻¹, inv_mem ht, k⁻¹, inv_mem hk, by rw [he]; group⟩`. Rewrite using `[finsum_eq_single _ (DoubleCoset.mk TH KH 1) h1, hf, if_pos]`. Take `⟨a, b, ha, hb, he⟩` from `DoubleCoset.mk_out_eq_mul TH KH (1 : H)`. Conclude with `⟨a, ha, b, hb, by rw [he, mul_one]⟩`.
-/
theorem finsum_doubleCoset_trivial_eq_one (H : Type) [Group H] (TH KH : Subgroup H) (f : H → ℂ)
    (hf : ∀ x, f x = if ∃ t ∈ TH, ∃ k ∈ KH, x = t * k then 1 else 0) :
    ∑ᶠ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), f (Quotient.out q) = 1 := by
  have h1 : ∀ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), q ≠ DoubleCoset.mk TH KH 1 →
      f (Quotient.out q) = 0 := by
    intro q hq
    rw [hf, if_neg]
    rintro ⟨t, ht, k, hk, he⟩
    apply hq
    rw [← DoubleCoset.out_eq' TH KH q, DoubleCoset.eq]
    exact ⟨t⁻¹, inv_mem ht, k⁻¹, inv_mem hk, by rw [he]; group⟩
  rw [finsum_eq_single _ (DoubleCoset.mk TH KH 1) h1, hf, if_pos]
  obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul TH KH (1 : H)
  exact ⟨a, ha, b, hb, by rw [he, mul_one]⟩

/- English proof (translation)
Establish `hR : ∀ j, ∑ᶠ a, f j a = ∑ a ∈ (hf j).toFinset, f j a` using `fun j => finsum_eq_sum_of_support_subset _ (by simp)`. Repeatedly rewrite using `[hR]`. Rewrite using `[Finset.prod_univ_sum]`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `y hy`.

Rewrite `hy` using `[Function.mem_support, Finset.prod_ne_zero_iff]`. Rewrite using `[Finset.mem_coe, Fintype.mem_piFinset]`. Introduce `j`. Simplify using `using hy j (Finset.mem_univ j)`.
-/
theorem finsum_pi_prod_eq_prod_finsum (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℂ)
    (hf : ∀ j, (Function.support (f j)).Finite) :
    ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∏ j, ∑ᶠ a, f j a := by
  have hR : ∀ j, ∑ᶠ a, f j a = ∑ a ∈ (hf j).toFinset, f j a := fun j =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  apply finsum_eq_sum_of_support_subset
  intro y hy
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hy
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro j
  simpa using hy j (Finset.mem_univ j)

/- English proof (translation)
Rewrite using `[hprod]`. Establish `hfin : {i | p i g ∉ KH i}.Finite` using `Filter.eventually_cofinite.mp (hcof g)`. Use `set B : Finset ι := S0 ∪ hfin.toFinset with hB`. Establish `hone : ∀ i ∉ B, s' i (p i g) = 1`. Introduce `i hi`.

Simplify using `only [B, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi`. Rewrite using `[hS0 i hi.1, if_pos ⟨1, (TH i).one_mem, p i g, hi.2, (one_mul _).symm⟩]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (f := fun i => s' i (p i g)) (s := B) (fun i hi => by by_contra h; exact hi (hone i h))]`. Use `split_ifs with hgood`. Use `symm`.

Apply `Finset.prod_subset Finset.subset_union_left` to reduce the goal to its premises. Introduce `i _ hi`. Rewrite using `[hS0 i hi, if_pos (hgood i hi)]`. Use `push_neg at hgood`. Take `⟨i, hi, hbad⟩` from `hgood`.

Apply `Finset.prod_eq_zero (i := i)` to reduce the goal to its premises. Use `Finset.mem_union_right _ ?_` and prove the remaining obligations. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Introduce `hk`. Conclude with `hbad 1 (TH i).one_mem (p i g) hk (one_mul _).symm`.

Rewrite using `[hS0 i hi, if_neg (by push_neg; exact hbad)]`.
-/
theorem eval_eq_ite_prod_of_finprod (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ) (S0 : Finset ι)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0)
    (hprod : ∀ g, s g = ∏ᶠ i, s' i (p i g)) (g : G) :
    s g = if ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k then ∏ i ∈ S0, s' i (p i g) else 0 := by
  rw [hprod]
  have hfin : {i | p i g ∉ KH i}.Finite := Filter.eventually_cofinite.mp (hcof g)
  set B : Finset ι := S0 ∪ hfin.toFinset with hB
  have hone : ∀ i ∉ B, s' i (p i g) = 1 := by
    intro i hi
    simp only [B, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    rw [hS0 i hi.1, if_pos ⟨1, (TH i).one_mem, p i g, hi.2, (one_mul _).symm⟩]
  rw [finprod_eq_prod_of_mulSupport_subset (f := fun i => s' i (p i g)) (s := B) (fun i hi => by by_contra h; exact hi (hone i h))]
  split_ifs with hgood
  · symm
    apply Finset.prod_subset Finset.subset_union_left
    intro i _ hi
    rw [hS0 i hi, if_pos (hgood i hi)]
  · push_neg at hgood
    obtain ⟨i, hi, hbad⟩ := hgood
    apply Finset.prod_eq_zero (i := i)
    · refine Finset.mem_union_right _ ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hk
      exact hbad 1 (TH i).one_mem (p i g) hk (one_mul _).symm
    · rw [hS0 i hi, if_neg (by push_neg; exact hbad)]

/- English proof (translation)
Establish `hloc : ∀ i, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * p i g * k ∧ (p i g ∈ KH i → p i g' ∈ KH i → t = 1)`. Introduce `i`. Distinguish the cases in `hk : p i g ∈ KH i ∧ p i g' ∈ KH i`. Conclude with `⟨1, (TH i).one_mem, (p i g)⁻¹ * p i g', mul_mem (inv_mem hk.1) hk.2, by group, fun _ _ => rfl⟩`. Distinguish the cases in `hi : i ∈ S0`.

Take `⟨t, ht, k, hk', he⟩` from `(DoubleCoset.eq _ _ _ _).1 (h i hi)`. Conclude with `⟨t, ht, k, hk', he, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩`. Take `⟨a, ha, b, hb, hab⟩` from `hg i hi`. Take `⟨a', ha', b', hb', hab'⟩` from `hg' i hi`. Use `⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), b⁻¹ * b', mul_mem (inv_mem hb) hb', ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩` and prove the remaining obligations.

Rewrite using `[hab, hab']`. Use `group`. Use `choose t ht k hk he h1 using hloc`. Take `⟨x, hx⟩` from `hsurj t (by filter_upwards [hcof g, hcof g'] with i hi hi'`. Rewrite using `[h1 i hi hi']`.

Conclude with `(KH i).one_mem)`. Rewrite using `[DoubleCoset.eq]`. Use `⟨x, (hT x).2 (fun i => by rw [hx]; exact ht i), g⁻¹ * x⁻¹ * g', (hK _).2 (fun i => ?_), by group⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, map_inv, hx, he i]`. Use `hk i using 1` and compare the differences between its conclusion and the goal.

Use `group`.
-/
theorem doubleCoset_mk_eq_of_local (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (S0 : Finset ι)
    (hsurj : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (g g' : G) (hg : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k)
    (hg' : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * k)
    (h : ∀ i ∈ S0, DoubleCoset.mk (TH i) (KH i) (p i g) = DoubleCoset.mk (TH i) (KH i) (p i g')) :
    DoubleCoset.mk T K g = DoubleCoset.mk T K g' := by
  have hloc : ∀ i, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * p i g * k ∧
      (p i g ∈ KH i → p i g' ∈ KH i → t = 1) := by
    intro i
    by_cases hk : p i g ∈ KH i ∧ p i g' ∈ KH i
    · exact ⟨1, (TH i).one_mem, (p i g)⁻¹ * p i g', mul_mem (inv_mem hk.1) hk.2, by group,
        fun _ _ => rfl⟩
    · by_cases hi : i ∈ S0
      · obtain ⟨t, ht, k, hk', he⟩ := (DoubleCoset.eq _ _ _ _).1 (h i hi)
        exact ⟨t, ht, k, hk', he, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := hg i hi
        obtain ⟨a', ha', b', hb', hab'⟩ := hg' i hi
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), b⁻¹ * b', mul_mem (inv_mem hb) hb', ?_,
          fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
        rw [hab, hab']; group
  choose t ht k hk he h1 using hloc
  obtain ⟨x, hx⟩ := hsurj t (by
    filter_upwards [hcof g, hcof g'] with i hi hi'
    rw [h1 i hi hi']; exact (KH i).one_mem)
  rw [DoubleCoset.eq]
  refine ⟨x, (hT x).2 (fun i => by rw [hx]; exact ht i), g⁻¹ * x⁻¹ * g', (hK _).2 (fun i => ?_), by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, hx, he i]
  convert hk i using 1
  group

/- English proof (translation)
Introduce `ι G _ H _ p T K TH KH s s' hsurj hcof hK hT hinv hfin hgood hprod`. Establish `hS0fin` using `Filter.eventually_cofinite.mp hgood`. Use `set S0 : Finset ι := hS0fin.toFinset with hS0def`. Establish `hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0`. Introduce `i hi`.

Simplify `hi` using `[S0]`. Establish `hloc : ∀ i (x : H i), s' i (Quotient.out (DoubleCoset.mk (TH i) (KH i) x)) = s' i x`. Introduce `i x`. Take `⟨a, b, ha, hb, he⟩` from `DoubleCoset.mk_out_eq_mul (TH i) (KH i) x`. Rewrite using `[he, hinv i a ha b hb]`.

Establish `hR : ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) = ∏ i : S0, ∑ᶠ q : DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)), s' i.1 (Quotient.out q)`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := S0)]`. Conclude with `(Finset.prod_coe_sort S0 (fun i => ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q))).symm`. Introduce `i hi`. Assume the negation of the conclusion as `h`.

Conclude with `hi (finsum_doubleCoset_trivial_eq_one (H i) (TH i) (KH i) (s' i) (hS0 i h))`. Rewrite using `[hR, ← finsum_pi_prod_eq_prod_finsum S0 (fun i : S0 => DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1))) (fun i q => s' i.1 (Quotient.out q)) (fun i => hfin i.1)]`. Take `⟨A, hAdef⟩ : ∃ A : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)), ∀ q, q ∈ A ↔ ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k` from `⟨{q | ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k}, fun q => Iff.rfl⟩`. Take `⟨Φ, hΦ⟩ : ∃ Φ : DoubleCoset.Quotient (T : Set G) (K : Set G) → ∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)), ∀ q i, Φ q i = DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q))` from `⟨fun q i => DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)), fun _ _ => rfl⟩`. Establish `hLHS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∑ᶠ (_ : q ∈ A), ∏ i : S0, s' i.1 (Quotient.out (Φ q i))`.

Introduce `q`. Rewrite using `[finsum_eq_if, eval_eq_ite_prod_of_finprod ι G H p TH KH s s' S0 hcof hS0 hprod (Quotient.out q)]`. Distinguish the cases in `hq : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k`. Rewrite using `[if_pos hq, if_pos ((hAdef q).2 hq), ← Finset.prod_coe_sort S0]`. Simplify using `only [hΦ, hloc]`.

Rewrite using `[if_neg hq, if_neg (fun h => hq ((hAdef q).1 h))]`. Use `(finsum_congr hLHS).trans ?_` and prove the remaining obligations. Use `(finsum_mem_eq_of_bijOn (t := Set.univ) (g := fun y : (∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1))) => ∏ j : S0, s' j.1 (Quotient.out (y j))) Φ ?_ (fun q _ => rfl)).trans (finsum_mem_univ _)` and prove the remaining obligations. Use `⟨fun q _ => Set.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq q' hq' he`.

Rewrite using `[← DoubleCoset.out_eq' T K q, ← DoubleCoset.out_eq' T K q']`. Use `doubleCoset_mk_eq_of_local ι G H p T K TH KH S0 hsurj hcof hK hT _ _ ((hAdef q).1 hq) ((hAdef q').1 hq') (fun i hi => ?_)` and prove the remaining obligations. Use `congrFun he ⟨i, hi⟩` as an intermediate fact. Rewrite `this` using `[hΦ, hΦ]`. Then use the resulting hypothesis. Introduce `y _`.

Take `⟨g, hg⟩` from `hsurj (fun i => if hi : i ∈ S0 then Quotient.out (y ⟨i, hi⟩) else 1) (by filter_upwards [S0.finite_toSet.compl_mem_cofinite] with i hi`. Rewrite using `[dif_neg (by simpa using hi)]; exact (KH i).one_mem)`. Take `⟨a, b, ha, hb, he⟩` from `DoubleCoset.mk_out_eq_mul T K g`. Use `⟨DoubleCoset.mk T K g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hAdef]`.

Introduce `i hi`. Use `⟨p i a, (hT a).1 ha i, p i b, (hK b).1 hb i, ?_⟩` and prove the remaining obligations. Rewrite using `[he, map_mul, map_mul, hg i, dif_neg hi, mul_one]`. Use function extensionality and compare the values at `i`. Rewrite using `[hΦ, he, map_mul, map_mul, hg i.1, dif_pos i.2]`.

Use `show DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) = y i`. Establish `h1 : DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) = DoubleCoset.mk (TH i.1) (KH i.1) (Quotient.out (y i))` using `(DoubleCoset.eq _ _ _ _).2 ⟨(p i.1 a)⁻¹, inv_mem ((hT a).1 ha i.1), (p i.1 b)⁻¹, inv_mem ((hK b).1 hb i.1), by group⟩`. Rewrite using `[h1, DoubleCoset.out_eq']`.
-/
theorem finsum_doubleCoset_eq_finprod_local : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  intro ι G _ H _ p T K TH KH s s' hsurj hcof hK hT hinv hfin hgood hprod
  have hS0fin := Filter.eventually_cofinite.mp hgood
  set S0 : Finset ι := hS0fin.toFinset with hS0def
  have hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0 := by
    intro i hi
    simpa [S0] using hi
  have hloc : ∀ i (x : H i), s' i (Quotient.out (DoubleCoset.mk (TH i) (KH i) x)) = s' i x := by
    intro i x
    obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul (TH i) (KH i) x
    rw [he, hinv i a ha b hb]
  have hR : ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q)
      = ∏ i : S0, ∑ᶠ q : DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)), s' i.1 (Quotient.out q) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S0)]
    · exact (Finset.prod_coe_sort S0 (fun i => ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q))).symm
    · intro i hi
      by_contra h
      exact hi (finsum_doubleCoset_trivial_eq_one (H i) (TH i) (KH i) (s' i) (hS0 i h))
  rw [hR, ← finsum_pi_prod_eq_prod_finsum S0 (fun i : S0 => DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)))
    (fun i q => s' i.1 (Quotient.out q)) (fun i => hfin i.1)]
  obtain ⟨A, hAdef⟩ : ∃ A : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)),
      ∀ q, q ∈ A ↔ ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k :=
    ⟨{q | ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k}, fun q => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : DoubleCoset.Quotient (T : Set G) (K : Set G) →
      ∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)),
      ∀ q i, Φ q i = DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)) :=
    ⟨fun q i => DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)), fun _ _ => rfl⟩
  have hLHS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) =
      ∑ᶠ (_ : q ∈ A), ∏ i : S0, s' i.1 (Quotient.out (Φ q i)) := by
    intro q
    rw [finsum_eq_if, eval_eq_ite_prod_of_finprod ι G H p TH KH s s' S0 hcof hS0 hprod (Quotient.out q)]
    by_cases hq : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k
    · rw [if_pos hq, if_pos ((hAdef q).2 hq), ← Finset.prod_coe_sort S0]
      simp only [hΦ, hloc]
    · rw [if_neg hq, if_neg (fun h => hq ((hAdef q).1 h))]
  refine (finsum_congr hLHS).trans ?_
  refine (finsum_mem_eq_of_bijOn (t := Set.univ)
    (g := fun y : (∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1))) =>
      ∏ j : S0, s' j.1 (Quotient.out (y j))) Φ ?_ (fun q _ => rfl)).trans (finsum_mem_univ _)
  refine ⟨fun q _ => Set.mem_univ _, ?_, ?_⟩
  · intro q hq q' hq' he
    rw [← DoubleCoset.out_eq' T K q, ← DoubleCoset.out_eq' T K q']
    refine doubleCoset_mk_eq_of_local ι G H p T K TH KH S0 hsurj hcof hK hT _ _ ((hAdef q).1 hq) ((hAdef q').1 hq') (fun i hi => ?_)
    have := congrFun he ⟨i, hi⟩
    rwa [hΦ, hΦ] at this
  · intro y _
    obtain ⟨g, hg⟩ := hsurj (fun i => if hi : i ∈ S0 then Quotient.out (y ⟨i, hi⟩) else 1) (by
      filter_upwards [S0.finite_toSet.compl_mem_cofinite] with i hi
      rw [dif_neg (by simpa using hi)]; exact (KH i).one_mem)
    obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul T K g
    refine ⟨DoubleCoset.mk T K g, ?_, ?_⟩
    · rw [hAdef]
      intro i hi
      refine ⟨p i a, (hT a).1 ha i, p i b, (hK b).1 hb i, ?_⟩
      rw [he, map_mul, map_mul, hg i, dif_neg hi, mul_one]
    · funext i
      rw [hΦ, he, map_mul, map_mul, hg i.1, dif_pos i.2]
      show DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) = y i
      have h1 : DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) =
          DoubleCoset.mk (TH i.1) (KH i.1) (Quotient.out (y i)) :=
        (DoubleCoset.eq _ _ _ _).2 ⟨(p i.1 a)⁻¹, inv_mem ((hT a).1 ha i.1), (p i.1 b)⁻¹,
          inv_mem ((hK b).1 hb i.1), by group⟩
      rw [h1, DoubleCoset.out_eq']

end GlobalTheory.DoubleCosetEuler
