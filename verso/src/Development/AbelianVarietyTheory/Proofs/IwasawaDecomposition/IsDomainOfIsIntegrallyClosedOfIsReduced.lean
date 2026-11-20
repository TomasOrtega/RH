import Mathlib

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Establish `: y ∈ nilradical R`. Rewrite using `[nilradical_eq_sInf, Submodule.mem_sInf]`. Introduce `J hJ`. Use `haveI : Ideal.IsPrime J := hJ`. Take `⟨p, hp, hpJ⟩` from `Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le`.

Conclude with `hpJ (hy p hp)`. Rewrite `this` using `[nilradical_eq_zero]`. Simplify using `using this`.
-/
theorem eq_zero_of_mem_minimalPrimes {R : Type} [CommRing R] [IsReduced R] {y : R}
    (hy : ∀ P ∈ minimalPrimes R, y ∈ P) : y = 0 := by
  have : y ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le
    exact hpJ (hy p hp)
  rw [nilradical_eq_zero] at this
  simpa using this

/- English proof (translation)
Introduce `R _ _ _ _ hic`. It suffices to establish `hbot : (⊥ : Ideal R).IsPrime by haveI : NoZeroDivisors R` using `⟨fun {x y} h => by`. Establish `: x * y ∈ (⊥ : Ideal R)` using `by simp [h]`. Simplify using `using hbot.mem_or_mem this⟩`. Conclude with `NoZeroDivisors.to_isDomain R`.

Establish `hfin` using `minimalPrimes.finite_of_isNoetherianRing R`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP⟩ : ∃ P, P ∈ minimalPrimes R := by`. Take `⟨p, hp, -⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := IsLocalRing.maximalIdeal R) bot_le`. Conclude with `⟨p, hp⟩`. Establish `hPprime : P.IsPrime` using `hP.1.1`.

Establish `minle : ∀ {A B : Ideal R}, A ∈ minimalPrimes R → B ∈ minimalPrimes R → A ≤ B → A = B` using `fun {A B} hA hB hAB => le_antisymm hAB (hB.2 hA.1 hAB)`. Use `set T : Finset (Ideal R) := hfin.toFinset with hT`. Establish `memT : ∀ Q, Q ∈ T ↔ Q ∈ minimalPrimes R` using `fun Q => by simp [T]`. Use `set Q : Ideal R := (T.erase P).inf id with hQ`. Establish `hQle : ∀ P' ∈ T.erase P, Q ≤ P'` using `fun P' h => Finset.inf_le (f := id) h`.

Distinguish the cases in `hone : T.erase P = ∅`. Establish `hPbot : P = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Establish `: y = 0` using `eq_zero_of_mem_minimalPrimes (fun P' hP' => by`.

Distinguish the cases in `h : P' = P`. Conclude with `h ▸ hy`. Establish `: P' ∈ T.erase P` using `Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩`. Simplify using `[hone] at this)`. Simplify using `[this]`.

Conclude with `hPbot ▸ hPprime`. It suffices to derive a contradiction. Take `⟨P₂, hP₂⟩` from `Finset.nonempty_iff_ne_empty.2 hone`. Establish `hnot : ¬ ((P ⊔ Q : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑T : Set (Ideal R)), (i : Set R)`. Introduce `hsub`.

Take `⟨P', hP'T, hle⟩` from `(Ideal.subset_union_prime (f := id) P P (fun i hi _ _ => ((memT i).1 hi).1.1)).1 hsub`. Establish `hle' : P ⊔ Q ≤ P'` using `hle`. Establish `h1 : P = P'` using `minle hP ((memT P').1 hP'T) (le_sup_left.trans hle')`. Establish `hQP : Q ≤ P`. Establish `h2 : Q ≤ P'` using `le_sup_right.trans hle'`.

Rewrite `h2` using `[← h1]`. Conclude with `h2`. Take `⟨P'', hP''e, hP''le⟩` from `(Ideal.IsPrime.inf_le' (s := T.erase P) (f := id) hPprime).1 hQP`. Establish `: P'' = P` using `minle ((memT P'').1 (Finset.mem_of_mem_erase hP''e)) hP hP''le`. Conclude with `Finset.ne_of_mem_erase hP''e this`.

Take `⟨s, hsPQ, hsout⟩` from `Set.not_subset.1 hnot`. Establish `hsnot : ∀ P' ∈ minimalPrimes R, s ∉ P'` using `fun P' hP' hs => hsout (Set.mem_biUnion (x := P') (by simpa [memT] using hP') hs)`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 hsPQ`. Establish `hsnzd : ∀ y : R, y * s = 0 → y = 0` using `fun y hy => eq_zero_of_mem_minimalPrimes (fun P' hP' => by`. Establish `: y * s ∈ P'` using `by simp [hy]`.

Conclude with `(hP'.1.1.mem_or_mem this).resolve_right (hsnot P' hP'))`. Establish `hab0 : a * b = 0` using `eq_zero_of_mem_minimalPrimes (fun P' hP' => by`. Distinguish the cases in `h : P' = P`. Conclude with `h ▸ P.mul_mem_right b ha`. Conclude with `P'.mul_mem_left a (hQle P' (Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩) hb))`.

Establish `hs : s ∈ nonZeroDivisors R` using `mem_nonZeroDivisors_iff_right.2 hsnzd`. Set `K` to `FractionRing R`. Use `set e : K := IsLocalization.mk' K a ⟨s, hs⟩ with he_def`. Establish `hspec : e * algebraMap R K s = algebraMap R K a` using `IsLocalization.mk'_spec K a ⟨s, hs⟩`. Establish `ht : IsUnit (algebraMap R K s)` using `IsLocalization.map_units K (⟨s, hs⟩ : nonZeroDivisors R)`.

Establish `has : a * s = a * a` using `by rw [← hab, mul_add, hab0, add_zero]`. Establish `hee : e * e = e`. Use `(ht.mul ht).mul_left_inj.1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hint : IsIntegral R e`.

Use `⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)`. Simplify using `[Polynomial.eval₂_sub, sq, hee]`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Establish `hinj` using `IsFractionRing.injective R K`.

Establish `hrr : r * r = r` using `hinj (by rw [map_mul, hr, hee])`. Establish `hrs : r * s = a` using `hinj (by rw [map_mul, hr, hspec])`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu` into its components or cases. Establish `hr1 : r = 1` using `hu.mul_left_cancel (by rw [hrr, mul_one])`. Rewrite `hrs` using `[hr1, one_mul]`.

Conclude with `hsnot P hP (hrs ▸ ha)`. Establish `hr0 : r = 0`. Establish `: (1 - r) * r = 0` using `by rw [sub_mul, one_mul, hrr, sub_self]`. Conclude with `(hu.mul_right_eq_zero).1 this`. Rewrite `hrs` using `[hr0, zero_mul]`.

Establish `hsb : s = b` using `by rw [← hab, ← hrs, zero_add]`. Conclude with `hsnot P₂ ((memT P₂).1 (Finset.mem_of_mem_erase hP₂)) (hsb ▸ hQle P₂ hP₂ hb)`.
-/
theorem isDomain_of_isIntegrallyClosed_of_isReduced :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R],
      IsIntegrallyClosed R → IsDomain R := by
  intro R _ _ _ _ hic
  classical
  suffices hbot : (⊥ : Ideal R).IsPrime by
    haveI : NoZeroDivisors R := ⟨fun {x y} h => by
      have : x * y ∈ (⊥ : Ideal R) := by simp [h]
      simpa using hbot.mem_or_mem this⟩
    exact NoZeroDivisors.to_isDomain R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  obtain ⟨P, hP⟩ : ∃ P, P ∈ minimalPrimes R := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := IsLocalRing.maximalIdeal R) bot_le
    exact ⟨p, hp⟩
  have hPprime : P.IsPrime := hP.1.1
  have minle : ∀ {A B : Ideal R}, A ∈ minimalPrimes R → B ∈ minimalPrimes R → A ≤ B → A = B :=
    fun {A B} hA hB hAB => le_antisymm hAB (hB.2 hA.1 hAB)
  set T : Finset (Ideal R) := hfin.toFinset with hT
  have memT : ∀ Q, Q ∈ T ↔ Q ∈ minimalPrimes R := fun Q => by simp [T]
  set Q : Ideal R := (T.erase P).inf id with hQ
  have hQle : ∀ P' ∈ T.erase P, Q ≤ P' := fun P' h => Finset.inf_le (f := id) h
  by_cases hone : T.erase P = ∅
  ·
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
        by_cases h : P' = P
        · exact h ▸ hy
        · have : P' ∈ T.erase P := Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩
          simp [hone] at this)
      simp [this]
    exact hPbot ▸ hPprime
  exfalso
  obtain ⟨P₂, hP₂⟩ := Finset.nonempty_iff_ne_empty.2 hone

  have hnot : ¬ ((P ⊔ Q : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑T : Set (Ideal R)), (i : Set R) := by
    intro hsub
    obtain ⟨P', hP'T, hle⟩ := (Ideal.subset_union_prime (f := id) P P
      (fun i hi _ _ => ((memT i).1 hi).1.1)).1 hsub
    have hle' : P ⊔ Q ≤ P' := hle
    have h1 : P = P' := minle hP ((memT P').1 hP'T) (le_sup_left.trans hle')
    have hQP : Q ≤ P := by
      have h2 : Q ≤ P' := le_sup_right.trans hle'
      rw [← h1] at h2
      exact h2
    obtain ⟨P'', hP''e, hP''le⟩ := (Ideal.IsPrime.inf_le' (s := T.erase P) (f := id) hPprime).1 hQP
    have : P'' = P := minle ((memT P'').1 (Finset.mem_of_mem_erase hP''e)) hP hP''le
    exact Finset.ne_of_mem_erase hP''e this
  obtain ⟨s, hsPQ, hsout⟩ := Set.not_subset.1 hnot
  have hsnot : ∀ P' ∈ minimalPrimes R, s ∉ P' := fun P' hP' hs =>
    hsout (Set.mem_biUnion (x := P') (by simpa [memT] using hP') hs)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsPQ
  have hsnzd : ∀ y : R, y * s = 0 → y = 0 := fun y hy =>
    eq_zero_of_mem_minimalPrimes (fun P' hP' => by
      have : y * s ∈ P' := by simp [hy]
      exact (hP'.1.1.mem_or_mem this).resolve_right (hsnot P' hP'))
  have hab0 : a * b = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
    by_cases h : P' = P
    · exact h ▸ P.mul_mem_right b ha
    · exact P'.mul_mem_left a (hQle P' (Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩) hb))
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.2 hsnzd
  let K := FractionRing R
  set e : K := IsLocalization.mk' K a ⟨s, hs⟩ with he_def
  have hspec : e * algebraMap R K s = algebraMap R K a := IsLocalization.mk'_spec K a ⟨s, hs⟩
  have ht : IsUnit (algebraMap R K s) := IsLocalization.map_units K (⟨s, hs⟩ : nonZeroDivisors R)
  have has : a * s = a * a := by rw [← hab, mul_add, hab0, add_zero]
  have hee : e * e = e := by
    refine (ht.mul ht).mul_left_inj.1 ?_
    calc e * e * (algebraMap R K s * algebraMap R K s)
        = (e * algebraMap R K s) * (e * algebraMap R K s) := by ring
      _ = algebraMap R K (a * a) := by rw [hspec, map_mul]
      _ = algebraMap R K (a * s) := by rw [has]
      _ = (e * algebraMap R K s) * algebraMap R K s := by rw [hspec, map_mul]
      _ = e * (algebraMap R K s * algebraMap R K s) := by ring
  have hint : IsIntegral R e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, sq, hee]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj := IsFractionRing.injective R K
  have hrr : r * r = r := hinj (by rw [map_mul, hr, hee])
  have hrs : r * s = a := hinj (by rw [map_mul, hr, hspec])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
  · have hr1 : r = 1 := hu.mul_left_cancel (by rw [hrr, mul_one])
    rw [hr1, one_mul] at hrs

    exact hsnot P hP (hrs ▸ ha)
  · have hr0 : r = 0 := by
      have : (1 - r) * r = 0 := by rw [sub_mul, one_mul, hrr, sub_self]
      exact (hu.mul_right_eq_zero).1 this
    rw [hr0, zero_mul] at hrs

    have hsb : s = b := by rw [← hab, ← hrs, zero_add]
    exact hsnot P₂ ((memT P₂).1 (Finset.mem_of_mem_erase hP₂)) (hsb ▸ hQle P₂ hP₂ hb)

end GlobalTheory
