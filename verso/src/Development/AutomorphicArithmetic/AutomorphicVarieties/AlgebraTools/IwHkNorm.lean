import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Establish `h : (((a : G) * x : G) : G ⧸ I) = (y : G ⧸ I)` using `ha`. Rewrite `h` using `[QuotientGroup.eq]`. Conclude with `⟨a, a.2, _, h, by group⟩`.

Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.mk_mul_of_mem _ hb]`. Both sides reduce to the same expression.
-/
private theorem hkNorm_mem {G : Type} [Group G] (I : Subgroup G) (x y : G) :
    (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, y = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have h : (((a : G) * x : G) : G ⧸ I) = (y : G ⧸ I) := ha
    rw [QuotientGroup.eq] at h
    exact ⟨a, a.2, _, h, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl

/- English proof (translation)
Use `⟨(Set.Finite.toFinset h).image Quotient.out, fun y hy => ?_, fun q hq => ?_⟩` and prove the remaining obligations. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[QuotientGroup.out_eq']`. Conclude with `(Set.Finite.mem_toFinset h).1 hq`. Use `⟨q.out, ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset h).2 hq), QuotientGroup.out_eq' q⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨hy, rfl⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[QuotientGroup.out_eq']`.
-/
private theorem hkNorm_reps {G : Type} [Group G] (I : Subgroup G) (x : G) (h : FinOrb I I x) :
    ∃ s : Finset G, (∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I)) ∧
      ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q := by
  classical
  refine ⟨(Set.Finite.toFinset h).image Quotient.out, fun y hy => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']
    exact (Set.Finite.mem_toFinset h).1 hq
  · refine ⟨q.out, ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset h).2 hq), QuotientGroup.out_eq' q⟩, ?_⟩
    rintro y ⟨hy, rfl⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']

/- English proof (translation)
Establish `cu : ∀ a ∈ I, u * a * u⁻¹ ∈ I` using `fun a ha => (Subgroup.mem_normalizer_iff.1 hu a).1 ha`. Establish `cu' : ∀ a ∈ I, u⁻¹ * a * u ∈ I` using `fun a ha => (Subgroup.mem_normalizer_iff''.1 hu a).1 ha`. Establish `cw : ∀ a ∈ I, w * a * w⁻¹ ∈ I` using `fun a ha => (Subgroup.mem_normalizer_iff.1 hw a).1 ha`. Establish `cw' : ∀ a ∈ I, w⁻¹ * a * w ∈ I` using `fun a ha => (Subgroup.mem_normalizer_iff''.1 hw a).1 ha`. Establish `key` using `(hkApply A G M ρ I I (u * x * w) (hI _)).2.1 (s.image fun y => u * y * w) ?_ ?_ v`.

Rewrite `key` using `[Finset.sum_image (fun a _ b _ h => by simpa using h)]`. Conclude with `key`. Introduce `y hy`. Take `⟨z, hz, rfl⟩` from `Finset.mem_image.1 hy`. Take `⟨a, ha, b, hb, rfl⟩` from `(hkNorm_mem I x z).1 (h1 z hz)`.

Conclude with `(hkNorm_mem I _ _).2 ⟨_, cu a ha, _, cw' b hb, by group⟩`. Introduce `q hq`. Take `⟨z, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨a, ha, b, hb, rfl⟩` from `(hkNorm_mem I _ z).1 hq`. Take `⟨y, ⟨hy, hyq⟩, huniq⟩` from `h2 ((u⁻¹ * a * u * x : G) : G ⧸ I) ((hkNorm_mem I _ _).2 ⟨_, cu' a ha, 1, one_mem _, by group⟩)`.

Use `⟨u * y * w, ⟨Finset.mem_image_of_mem _ hy, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite `hyq`, the goal using `[QuotientGroup.eq]`. Use `mul_mem (cw' _ hyq) hb using 1` and compare the differences between its conclusion and the goal. Use `group`. Introduce and unpack `y' ⟨hy', h⟩`.

Take `⟨z, hz, rfl⟩` from `Finset.mem_image.1 hy'`. Rewrite using `[huniq z ⟨hz, ?_⟩]`. Rewrite `h`, the goal using `[QuotientGroup.eq]`. Use `cw _ (mul_mem h (inv_mem hb)) using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
private theorem hkNorm_tr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x u w : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (hw : w ∈ Subgroup.normalizer (I : Set G))
    (s : Finset G) (h1 : ∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I))
    (h2 : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q) (v : fixd ρ I) :
    (hk ρ I (u * x * w) v : M) = ∑ y ∈ s, ρ (u * y * w) v := by
  classical
  have cu : ∀ a ∈ I, u * a * u⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hu a).1 ha
  have cu' : ∀ a ∈ I, u⁻¹ * a * u ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hu a).1 ha
  have cw : ∀ a ∈ I, w * a * w⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hw a).1 ha
  have cw' : ∀ a ∈ I, w⁻¹ * a * w ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hw a).1 ha
  have key := (hkApply A G M ρ I I (u * x * w) (hI _)).2.1 (s.image fun y => u * y * w) ?_ ?_ v
  · rw [Finset.sum_image (fun a _ b _ h => by simpa using h)] at key
    exact key
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I x z).1 (h1 z hz)
    exact (hkNorm_mem I _ _).2 ⟨_, cu a ha, _, cw' b hb, by group⟩
  · intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    obtain ⟨y, ⟨hy, hyq⟩, huniq⟩ := h2 ((u⁻¹ * a * u * x : G) : G ⧸ I)
      ((hkNorm_mem I _ _).2 ⟨_, cu' a ha, 1, one_mem _, by group⟩)
    refine ⟨u * y * w, ⟨Finset.mem_image_of_mem _ hy, ?_⟩, ?_⟩
    · rw [QuotientGroup.eq] at hyq ⊢
      convert mul_mem (cw' _ hyq) hb using 1
      group
    · rintro y' ⟨hy', h⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      rw [huniq z ⟨hz, ?_⟩]
      rw [QuotientGroup.eq] at h ⊢
      convert cw _ (mul_mem h (inv_mem hb)) using 1
      group

/- English proof (translation)
Establish `h` using `hkNorm_tr ρ I hI 1 u 1 hu (one_mem _) {1} (by simp) (fun q hq => by`. Take `⟨z, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨a, ha, b, hb, rfl⟩` from `(hkNorm_mem I _ z).1 hq`. Use `⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.eq]`.

Simplify using `using mul_mem ha hb) v`. Simplify using `using h`.
-/
private theorem hkNorm_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (v : fixd ρ I) : (hk ρ I u v : M) = ρ u v := by
  have h := hkNorm_tr ρ I hI 1 u 1 hu (one_mem _) {1} (by simp) (fun q hq => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    refine ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩
    rw [QuotientGroup.eq]
    simpa using mul_mem ha hb) v
  simpa using h

/- English proof (translation)
Take `⟨s, h1, h2⟩` from `hkNorm_reps I x (hI x)`. Establish `h0` using `hkNorm_tr ρ I hI x 1 1 (one_mem _) (one_mem _) s h1 h2`. Establish `hl` using `hkNorm_tr ρ I hI x u 1 hu (one_mem _) s h1 h2`. Establish `hr` using `hkNorm_tr ρ I hI x 1 u (one_mem _) hu s h1 h2`. Simplify using `only [one_mul, mul_one] at h0 hl hr`.

Prove the components needed by the constructor for the conclusion. Use extensionality with `v`. Rewrite using `[hl, Module.End.mul_apply, hkNorm_one ρ I hI u hu, h0, map_sum]`. Simplify using `only [map_mul, Module.End.mul_apply]`. Use extensionality with `v`.

Rewrite using `[hr, Module.End.mul_apply, h0, hkNorm_one ρ I hI u hu]`. Simplify using `only [map_mul, Module.End.mul_apply]`.
-/
private theorem hkNorm_mul {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  obtain ⟨s, h1, h2⟩ := hkNorm_reps I x (hI x)
  have h0 := hkNorm_tr ρ I hI x 1 1 (one_mem _) (one_mem _) s h1 h2
  have hl := hkNorm_tr ρ I hI x u 1 hu (one_mem _) s h1 h2
  have hr := hkNorm_tr ρ I hI x 1 u (one_mem _) hu s h1 h2
  simp only [one_mul, mul_one] at h0 hl hr
  constructor
  · ext v
    rw [hl, Module.End.mul_apply, hkNorm_one ρ I hI u hu, h0, map_sum]
    simp only [map_mul, Module.End.mul_apply]
  · ext v
    rw [hr, Module.End.mul_apply, h0, hkNorm_one ρ I hI u hu]
    simp only [map_mul, Module.End.mul_apply]

/- English proof (translation)
Introduce `A G M _ _ _ _ ρ I u hI hu`. Establish `h1 : hk ρ I 1 = 1`. Use extensionality with `v`. Rewrite using `[hkNorm_one ρ I hI 1 (one_mem _)]`. Simplify using the standard rewrite rules.

Use `⟨hkNorm_one ρ I hI u hu, h1, ⟨⟨hk ρ I u, hk ρ I u⁻¹, ?_, ?_⟩, rfl⟩, hkNorm_mul ρ I hI u hu⟩` and prove the remaining obligations. Rewrite using `[← (hkNorm_mul ρ I hI u hu u⁻¹).1, mul_inv_cancel, h1]`. Rewrite using `[← (hkNorm_mul ρ I hI u hu u⁻¹).2, inv_mul_cancel, h1]`.
-/
theorem UpperTheory.V.AlgebraTools.hkNorm :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (u : G), HeckePair I → u ∈ Subgroup.normalizer (I : Set G) → (∀ v : fixd ρ I, (hk ρ I u v : M) = ρ u v) ∧ hk ρ I 1 = 1 ∧ IsUnit (hk ρ I u) ∧ ∀ x : G, hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  intro A G M _ _ _ _ ρ I u hI hu
  have h1 : hk ρ I 1 = 1 := by
    ext v
    rw [hkNorm_one ρ I hI 1 (one_mem _)]
    simp
  refine ⟨hkNorm_one ρ I hI u hu, h1, ⟨⟨hk ρ I u, hk ρ I u⁻¹, ?_, ?_⟩, rfl⟩, hkNorm_mul ρ I hI u hu⟩
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).1, mul_inv_cancel, h1]
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).2, inv_mul_cancel, h1]
