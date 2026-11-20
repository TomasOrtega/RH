import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `O B A _ _ _ _ _ _ _ _ _ _ N hinj hc hN _ _`. Establish `hdec : ∀ a : A, ∃ b : B, ∃ n ∈ N, a = algebraMap B A b + n`. Introduce `a`. Establish `ha : a ∈ (1 : Submodule B A) ⊔ N` using `by rw [hc.sup_eq_top]; trivial`. Take `⟨u, hu, n, hn, rfl⟩` from `Submodule.mem_sup.mp ha`.

Take `⟨b, rfl⟩` from `Submodule.mem_one.mp hu`. Conclude with `⟨b, n, hn, rfl⟩`. Set `S : Set A` to `{a | ∃ b ∈ maximalIdeal B, ∃ n ∈ N, a = algebraMap B A b + n}`. Establish `hSmul : ∀ x a, a ∈ S → x * a ∈ S`. Introduce and unpack `x a ⟨b, hb, n, hn, rfl⟩`.

Take `⟨b', n', hn', rfl⟩` from `hdec x`. Take `⟨c, hc', hcn⟩` from `hN n' hn' n hn`. Use `⟨b' * b + c, Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) hc', b' • n + b • n', N.add_mem (N.smul_mem _ hn) (N.smul_mem _ hn'), ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_add, map_mul, ← hcn]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hSadd : ∀ a a', a ∈ S → a' ∈ S → a + a' ∈ S`. Introduce and unpack `a a' ⟨b, hb, n, hn, rfl⟩ ⟨b', hb', n', hn', rfl⟩`. Conclude with `⟨b + b', Ideal.add_mem _ hb hb', n + n', N.add_mem hn hn', by rw [map_add]; ring⟩`. Establish `h1 : (1 : A) ∉ S`. Introduce and unpack `⟨b, hb, n, hn, e⟩`.

Establish `hn1 : n ∈ (1 : Submodule B A)` using `Submodule.mem_one.mpr ⟨1 - b, by rw [map_sub, map_one, e]; ring⟩`. Establish `hn0 : n = 0`. Establish `hmem : n ∈ (1 : Submodule B A) ⊓ N` using `⟨hn1, hn⟩`. Rewrite `hmem` using `[hc.inf_eq_bot]`. Conclude with `(Submodule.mem_bot B).mp hmem`.

Rewrite `e` using `[hn0, add_zero, ← map_one (algebraMap B A)]`. Establish `hb1` using `hinj e`. Rewrite `hb` using `[← hb1]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hb isUnit_one`. Establish `hnon : ∀ a : A, a ∈ S → ¬IsUnit a`.

Introduce and unpack `a ha ⟨u, rfl⟩`. Apply `h1` to reduce the goal to its premises. Use `hSmul (↑u⁻¹) _ ha` as an intermediate fact. Rewrite `this` using `[Units.inv_mul]`. Then use the resulting hypothesis. Establish `hunit : ∀ a : A, a ∉ S → IsUnit a`.

Introduce `a ha`. Take `⟨b, n, hn, rfl⟩` from `hdec a`. Establish `hb : b ∉ maximalIdeal B` using `fun hb => ha ⟨b, hb, n, hn, rfl⟩`. Take `⟨c, hcm, hcn⟩` from `hN n hn n hn`. Establish `hu : IsUnit (b * b - c)`.

Assume the negation of the conclusion as `h`. Apply `hb` to reduce the goal to its premises. Establish `h' : b * b - c ∈ maximalIdeal B` using `(IsLocalRing.mem_maximalIdeal _).mpr h`. Establish `hbb : b * b ∈ maximalIdeal B` using `by simpa using Ideal.add_mem _ h' hcm`. Conclude with `((IsLocalRing.maximalIdeal.isMaximal B).isPrime.mem_or_mem hbb).elim id id`.

Establish `hprod : (algebraMap B A b + n) * (algebraMap B A b - n) = algebraMap B A (b * b - c)`. Rewrite using `[map_sub, map_mul, ← hcn]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `isUnit_of_mul_isUnit_left (by rw [hprod]; exact hu.map _)`. Use `haveI : Nontrivial A := hinj.nontrivial`.

Use `haveI hloc : IsLocalRing A := by`. Apply `IsLocalRing.of_nonunits_add` to reduce the goal to its premises. Introduce `a a' ha ha'`. Establish `hS' : ∀ x : A, x ∈ nonunits A → x ∈ S` using `fun x hx => by`. Assume the negation of the conclusion as `h`.

Conclude with `hx (hunit x h)`. Conclude with `hnon _ (hSadd _ _ (hS' _ ha) (hS' _ ha'))`. Establish `hmemS : ∀ a : A, a ∈ maximalIdeal A ↔ a ∈ S`. Introduce `a`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `⟨fun h => by by_contra h'; exact h (hunit a h'), hnon a⟩`. Establish `hM : ∀ a : A, a ∈ S ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A)`. Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, n, hn, rfl⟩`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb)) (Ideal.mem_sup_right (Ideal.subset_span hn))`. Introduce `ha`. Use `(hmemS a).mp ?_` and prove the remaining obligations. Establish `hle : (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) ≤ maximalIdeal A`. Use `sup_le (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) (Ideal.span_le.mpr fun n hn => ?_)` and prove the remaining obligations.

Conclude with `(hmemS _).mpr ⟨b, hb, 0, N.zero_mem, by simp⟩`. Conclude with `(hmemS _).mpr ⟨0, zero_mem _, n, hn, by simp⟩`. Conclude with `hle ha`. Use `haveI hco : IsCO O A := co_finite O B A (fun x => by`. Take `⟨b, n, hn, rfl⟩` from `hdec x`.

Take `⟨o, ho⟩` from `IsCO.res_surj (O := O) b`. Use `⟨o, (hmemS _).mpr ⟨b - algebraMap O B o, ho, n, hn, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply O B A, map_sub]`. Use the proof step `ring)`. Use `⟨hco, fun a => (hmemS a).trans (hM a), ?_⟩` and prove the remaining obligations.

Use `Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `b ⟨x, hx, y, hy, e⟩`. Use `show algebraMap B A b ∈ maximalIdeal A ^ 2`. Rewrite using `[← e, pow_two]`. Conclude with `Ideal.mul_mem_mul ((hmemS x).mpr ⟨0, zero_mem _, x, hx, by simp⟩) ((hmemS y).mpr ⟨0, zero_mem _, y, hy, by simp⟩)`.
-/
theorem UpperTheory.V.Pa.aaCO :
    ∀ (O B A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra B A] [Module.Finite B A] (N : Submodule B A), Function.Injective (algebraMap B A) → _root_.IsCompl (1 : Submodule B A) N → (∀ a ∈ N, ∀ b ∈ N, ∃ c ∈ maximalIdeal B, a * b = algebraMap B A c) → ∀ [Algebra O A] [IsScalarTower O B A], ∃ _ : IsCO O A, (∀ a, a ∈ maximalIdeal A ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A)) ∧ (ired N).map (algebraMap B A) ≤ maximalIdeal A ^ 2 := by
  intro O B A _ _ _ _ _ _ _ _ _ _ N hinj hc hN _ _
  have hdec : ∀ a : A, ∃ b : B, ∃ n ∈ N, a = algebraMap B A b + n := by
    intro a
    have ha : a ∈ (1 : Submodule B A) ⊔ N := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hu
    exact ⟨b, n, hn, rfl⟩
  let S : Set A := {a | ∃ b ∈ maximalIdeal B, ∃ n ∈ N, a = algebraMap B A b + n}
  have hSmul : ∀ x a, a ∈ S → x * a ∈ S := by
    rintro x a ⟨b, hb, n, hn, rfl⟩
    obtain ⟨b', n', hn', rfl⟩ := hdec x
    obtain ⟨c, hc', hcn⟩ := hN n' hn' n hn
    refine ⟨b' * b + c, Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) hc', b' • n + b • n',
      N.add_mem (N.smul_mem _ hn) (N.smul_mem _ hn'), ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_add, map_mul, ← hcn]
    ring
  have hSadd : ∀ a a', a ∈ S → a' ∈ S → a + a' ∈ S := by
    rintro a a' ⟨b, hb, n, hn, rfl⟩ ⟨b', hb', n', hn', rfl⟩
    exact ⟨b + b', Ideal.add_mem _ hb hb', n + n', N.add_mem hn hn', by rw [map_add]; ring⟩
  have h1 : (1 : A) ∉ S := by
    rintro ⟨b, hb, n, hn, e⟩
    have hn1 : n ∈ (1 : Submodule B A) :=
      Submodule.mem_one.mpr ⟨1 - b, by rw [map_sub, map_one, e]; ring⟩
    have hn0 : n = 0 := by
      have hmem : n ∈ (1 : Submodule B A) ⊓ N := ⟨hn1, hn⟩
      rw [hc.inf_eq_bot] at hmem
      exact (Submodule.mem_bot B).mp hmem
    rw [hn0, add_zero, ← map_one (algebraMap B A)] at e
    have hb1 := hinj e
    rw [← hb1] at hb
    exact (IsLocalRing.mem_maximalIdeal _).mp hb isUnit_one
  have hnon : ∀ a : A, a ∈ S → ¬IsUnit a := by
    rintro a ha ⟨u, rfl⟩
    apply h1
    have := hSmul (↑u⁻¹) _ ha
    rwa [Units.inv_mul] at this
  have hunit : ∀ a : A, a ∉ S → IsUnit a := by
    intro a ha
    obtain ⟨b, n, hn, rfl⟩ := hdec a
    have hb : b ∉ maximalIdeal B := fun hb => ha ⟨b, hb, n, hn, rfl⟩
    obtain ⟨c, hcm, hcn⟩ := hN n hn n hn
    have hu : IsUnit (b * b - c) := by
      by_contra h
      apply hb
      have h' : b * b - c ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h
      have hbb : b * b ∈ maximalIdeal B := by simpa using Ideal.add_mem _ h' hcm
      exact ((IsLocalRing.maximalIdeal.isMaximal B).isPrime.mem_or_mem hbb).elim id id
    have hprod : (algebraMap B A b + n) * (algebraMap B A b - n) = algebraMap B A (b * b - c) := by
      rw [map_sub, map_mul, ← hcn]
      ring
    exact isUnit_of_mul_isUnit_left (by rw [hprod]; exact hu.map _)
  haveI : Nontrivial A := hinj.nontrivial
  haveI hloc : IsLocalRing A := by
    apply IsLocalRing.of_nonunits_add
    intro a a' ha ha'
    have hS' : ∀ x : A, x ∈ nonunits A → x ∈ S := fun x hx => by
      by_contra h
      exact hx (hunit x h)
    exact hnon _ (hSadd _ _ (hS' _ ha) (hS' _ ha'))
  have hmemS : ∀ a : A, a ∈ maximalIdeal A ↔ a ∈ S := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hunit a h'), hnon a⟩
  have hM : ∀ a : A, a ∈ S ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) := by
    intro a
    constructor
    · rintro ⟨b, hb, n, hn, rfl⟩
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb))
        (Ideal.mem_sup_right (Ideal.subset_span hn))
    · intro ha
      refine (hmemS a).mp ?_
      have hle : (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) ≤ maximalIdeal A := by
        refine sup_le (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) (Ideal.span_le.mpr fun n hn => ?_)
        · exact (hmemS _).mpr ⟨b, hb, 0, N.zero_mem, by simp⟩
        · exact (hmemS _).mpr ⟨0, zero_mem _, n, hn, by simp⟩
      exact hle ha
  haveI hco : IsCO O A := co_finite O B A (fun x => by
    obtain ⟨b, n, hn, rfl⟩ := hdec x
    obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
    refine ⟨o, (hmemS _).mpr ⟨b - algebraMap O B o, ho, n, hn, ?_⟩⟩
    rw [IsScalarTower.algebraMap_apply O B A, map_sub]
    ring)
  refine ⟨hco, fun a => (hmemS a).trans (hM a), ?_⟩
  refine Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)
  rintro b ⟨x, hx, y, hy, e⟩
  show algebraMap B A b ∈ maximalIdeal A ^ 2
  rw [← e, pow_two]
  exact Ideal.mul_mem_mul ((hmemS x).mpr ⟨0, zero_mem _, x, hx, by simp⟩)
    ((hmemS y).mpr ⟨0, zero_mem _, y, hy, by simp⟩)
