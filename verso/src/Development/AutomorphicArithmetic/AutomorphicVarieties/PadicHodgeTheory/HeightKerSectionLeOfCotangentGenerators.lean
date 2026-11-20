import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

open IsLocalRing UpperTheory.V.Alg

/- English proof (translation)
Introduce `O S _ _ _ _ _ x n t ht hx`. Use `set P := RingHom.ker x with hPdef`. Use `haveI hP : P.IsPrime := RingHom.ker_isPrime x`. Use `set L := Localization.AtPrime P`. Use `set T : Ideal L := Ideal.span ((Finset.univ.image (fun i => algebraMap S L (t i)) : Finset L) : Set L) with hT`.

Establish `hTm : T ≤ maximalIdeal L`. Rewrite using `[hT, Ideal.span_le]`. Introduce `y hy`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy`. Take `⟨i, rfl⟩` from `hy`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `Ideal.mem_map_of_mem _ (ht i)`. Establish `key : Ideal.map (algebraMap S L) P ≤ T ⊔ maximalIdeal L • maximalIdeal L`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`.

Take `⟨e, o, he, hmem⟩` from `hx a ha`. Establish `hunit : IsUnit (algebraMap S L (algebraMap O S e))`. Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff L P]`. Introduce `hin`. Apply `he` to reduce the goal to its premises.

Establish `: x (algebraMap O S e) = 0` using `hin`. Simplify using `using this`. Rewrite using `[Ideal.mem_comap]`. Establish `h2 : algebraMap S L (e • a - ∑ i, o i • t i) ∈ maximalIdeal L • maximalIdeal L`. Rewrite using `[smul_eq_mul, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_mul, ← pow_two]`.

Conclude with `Ideal.mem_map_of_mem _ hmem`. Establish `h3 : algebraMap S L (∑ i, o i • t i) ∈ T`. Rewrite using `[map_sum]`. Use `Ideal.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`.

Use `Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h4 : algebraMap S L (algebraMap O S e) * algebraMap S L a ∈ T ⊔ maximalIdeal L • maximalIdeal L`. Establish `: algebraMap S L (algebraMap O S e) * algebraMap S L a = algebraMap S L (∑ i, o i • t i) + algebraMap S L (e • a - ∑ i, o i • t i)`. Rewrite using `[← map_mul, ← Algebra.smul_def, ← map_add]`.

Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right h2)`. Take `⟨u, hu⟩` from `hunit`.

Establish `: algebraMap S L a = ((u⁻¹ : Lˣ) : L) * (algebraMap S L (algebraMap O S e) * algebraMap S L a)`. Rewrite using `[← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ h4`. Establish `hmT : maximalIdeal L ≤ T ⊔ maximalIdeal L • maximalIdeal L`.

Rewrite `key` using `[Localization.AtPrime.map_eq_maximalIdeal]`. Then use the resulting hypothesis. Establish `hmle : maximalIdeal L ≤ T` using `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson ⊥) hmT`. Establish `heq : T = maximalIdeal L` using `le_antisymm hTm hmle`. Establish `hmin : maximalIdeal L ∈ T.minimalPrimes`. Rewrite using `[heq]`.

Conclude with `⟨⟨inferInstance, le_rfl⟩, fun q hq _ => hq.2⟩`. Establish `hh` using `Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin`. Establish `hPL : P.height = (maximalIdeal L).height`. Rewrite using `[← IsLocalization.height_under P.primeCompl (maximalIdeal L), Localization.AtPrime.under_maximalIdeal]`. Rewrite using `[hPL]`.

Use `hh.trans ?_` and prove the remaining obligations. Establish `hc : (Finset.univ.image (fun i => algebraMap S L (t i))).card ≤ n`. Simplify using `using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => algebraMap S L (t i)))`. Conclude with `hc` after adjusting the coercions.
-/
theorem UpperTheory.height_ker_section_le_of_cotangent_generators :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (x : S →ₐ[O] O) (n : ℕ) (t : Fin n → S), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2) → (RingHom.ker x).height ≤ (n : ℕ∞) := by
  classical
  intro O S _ _ _ _ _ x n t ht hx
  set P := RingHom.ker x with hPdef
  haveI hP : P.IsPrime := RingHom.ker_isPrime x
  set L := Localization.AtPrime P
  set T : Ideal L := Ideal.span ((Finset.univ.image (fun i => algebraMap S L (t i)) : Finset L) : Set L) with hT
  have hTm : T ≤ maximalIdeal L := by
    rw [hT, Ideal.span_le]
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (ht i)
  have key : Ideal.map (algebraMap S L) P ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨e, o, he, hmem⟩ := hx a ha
    have hunit : IsUnit (algebraMap S L (algebraMap O S e)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L P]
      intro hin
      apply he
      have : x (algebraMap O S e) = 0 := hin
      simpa using this
    rw [Ideal.mem_comap]
    have h2 : algebraMap S L (e • a - ∑ i, o i • t i) ∈ maximalIdeal L • maximalIdeal L := by
      rw [smul_eq_mul, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_mul, ← pow_two]
      exact Ideal.mem_map_of_mem _ hmem
    have h3 : algebraMap S L (∑ i, o i • t i) ∈ T := by
      rw [map_sum]
      refine Ideal.sum_mem _ (fun i _ => ?_)
      rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      simp
    have h4 : algebraMap S L (algebraMap O S e) * algebraMap S L a ∈ T ⊔ maximalIdeal L • maximalIdeal L := by
      have : algebraMap S L (algebraMap O S e) * algebraMap S L a = algebraMap S L (∑ i, o i • t i) + algebraMap S L (e • a - ∑ i, o i • t i) := by
        rw [← map_mul, ← Algebra.smul_def, ← map_add]
        congr 1
        abel
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right h2)
    obtain ⟨u, hu⟩ := hunit
    have : algebraMap S L a = ((u⁻¹ : Lˣ) : L) * (algebraMap S L (algebraMap O S e) * algebraMap S L a) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h4
  have hmT : maximalIdeal L ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rwa [Localization.AtPrime.map_eq_maximalIdeal] at key
  have hmle : maximalIdeal L ≤ T :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hmT
  have heq : T = maximalIdeal L := le_antisymm hTm hmle
  have hmin : maximalIdeal L ∈ T.minimalPrimes := by
    rw [heq]
    exact ⟨⟨inferInstance, le_rfl⟩, fun q hq _ => hq.2⟩
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hPL : P.height = (maximalIdeal L).height := by
    rw [← IsLocalization.height_under P.primeCompl (maximalIdeal L), Localization.AtPrime.under_maximalIdeal]
  rw [hPL]
  refine hh.trans ?_
  have hc : (Finset.univ.image (fun i => algebraMap S L (t i))).card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => algebraMap S L (t i)))
  exact_mod_cast hc
