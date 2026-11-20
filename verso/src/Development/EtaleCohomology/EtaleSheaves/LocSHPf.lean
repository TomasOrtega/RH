import Development.EtaleCohomology.EtaleSheaves.ZarLocalPf

noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.E.LocSHPf

/- English proof (translation)
Introduce `P hP hd`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (P.natDegree + 1)).image P.coeff)`. Use `set s : R := algebraMap S R (b : S) with hs`. Establish `hlift : P.scaleRoots s ∈ lifts (algebraMap S R)`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `i`. Rewrite using `[coeff_scaleRoots]`. Break down `lt_trichotomy i P.natDegree with hi | hi | hi` into its components or cases. Take `⟨y, hy⟩` from `hb (P.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)`. Take `⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1` from `⟨P.natDegree - i - 1, by omega⟩`.

Use `⟨y * (b : S) ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hy, hk, pow_succ, Algebra.smul_def, ← hs]`. Expand and normalize the polynomial expressions, which then agree. Substitute `hi` using the available equality. Rewrite using `[Nat.sub_self, pow_zero, mul_one]`.

Conclude with `⟨1, by rw [map_one]; exact hP.symm⟩`. Rewrite using `[coeff_eq_zero_of_natDegree_lt hi, zero_mul]`. Conclude with `⟨0, map_zero _⟩`. Establish `hmon : (P.scaleRoots s).Monic`. Rewrite using `[Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]`.

Conclude with `hP`. Take `⟨Q, hQ, hQd, hQm⟩` from `lifts_and_natDegree_eq_and_monic hlift hmon`. Take `⟨a, ha⟩` from `hS Q hQm (by rw [hQd, natDegree_scaleRoots]; exact hd)`. Establish `hu : IsUnit s` using `IsLocalization.map_units R b`. Use `⟨hu.unit⁻¹ * algebraMap S R a, ?_⟩` and prove the remaining obligations.

Establish `h1` using `scaleRoots_eval₂_mul (p := P) (RingHom.id R) (hu.unit⁻¹ * algebraMap S R a) s`. Establish `h2 : s * (hu.unit⁻¹ * algebraMap S R a) = algebraMap S R a`. Rewrite using `[← mul_assoc, hu.mul_val_inv, one_mul]`. Rewrite `h1` using `[RingHom.id_apply, h2, ← eval, ← eval, ← hQ, eval_map, eval₂_hom, ha, map_zero]`. Use `(hu.pow P.natDegree).mul_right_eq_zero.1 h1.symm` as an intermediate fact.

Conclude with `this`.
-/
theorem aic_localization (S : Type) [CommRing S] (hS : AIC S) (M : Submonoid S) (R : Type) [CommRing R]
    [Algebra S R] [IsLocalization M R] : AIC R := by
  intro P hP hd
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (P.natDegree + 1)).image P.coeff)
  set s : R := algebraMap S R (b : S) with hs
  have hlift : P.scaleRoots s ∈ lifts (algebraMap S R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨y, hy⟩ := hb (P.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      refine ⟨y * (b : S) ^ k, ?_⟩
      rw [map_mul, map_pow, hy, hk, pow_succ, Algebra.smul_def, ← hs]
      ring
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by rw [map_one]; exact hP.symm⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact ⟨0, map_zero _⟩
  have hmon : (P.scaleRoots s).Monic := by
    rw [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]; exact hP
  obtain ⟨Q, hQ, hQd, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  obtain ⟨a, ha⟩ := hS Q hQm (by rw [hQd, natDegree_scaleRoots]; exact hd)
  have hu : IsUnit s := IsLocalization.map_units R b
  refine ⟨hu.unit⁻¹ * algebraMap S R a, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := P) (RingHom.id R) (hu.unit⁻¹ * algebraMap S R a) s
  have h2 : s * (hu.unit⁻¹ * algebraMap S R a) = algebraMap S R a := by
    rw [← mul_assoc, hu.mul_val_inv, one_mul]
  rw [RingHom.id_apply, h2, ← eval, ← eval, ← hQ, eval_map, eval₂_hom, ha, map_zero] at h1
  have := (hu.pow P.natDegree).mul_right_eq_zero.1 h1.symm
  exact this

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `f hn hf he`. Rewrite `he` using `[eq_one_of_monic_natDegree_zero hf hn, eval_one]`.

Conclude with `absurd he (Ideal.IsMaximal.ne_top inferInstance |> fun h => fun h1 => h ((Ideal.eq_top_iff_one _).2 h1))`. Consider the case `succ n ih`. Introduce `f hn hf he`. Take `⟨a, ha⟩` from `hR f hf (by omega)`. Establish `hfac` using `(mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 ha`.

Establish `hgm : (f /ₘ (X - C a)).Monic` using `(monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hf)`. Establish `hgd : (f /ₘ (X - C a)).natDegree = n`. Rewrite using `[natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Rewrite `he` using `[← hfac, eval_mul, eval_sub, eval_X, eval_C]`.

Break down `Ideal.IsPrime.mem_or_mem (inferInstance : (maximalIdeal R).IsPrime) he with h | h` into its components or cases. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_sub]`. Conclude with `(Ideal.neg_mem_iff _).2 h`. Take `⟨b, hb, hb'⟩` from `ih _ hgd hgm h`.

Use `⟨b, ?_, hb'⟩` and prove the remaining obligations. Rewrite using `[← hfac, IsRoot, eval_mul, hb.eq_zero, mul_zero]`.
-/
theorem root_near (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) (a₀ : R) :
    ∀ n : ℕ, ∀ f : R[X], f.natDegree = n → f.Monic → f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hn hf he
    rw [eq_one_of_monic_natDegree_zero hf hn, eval_one] at he
    exact absurd he (Ideal.IsMaximal.ne_top inferInstance |> fun h => fun h1 => h ((Ideal.eq_top_iff_one _).2 h1))
  | succ n ih =>
    intro f hn hf he
    obtain ⟨a, ha⟩ := hR f hf (by omega)
    have hfac := (mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 ha
    have hgm : (f /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hf)
    have hgd : (f /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at he
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : (maximalIdeal R).IsPrime) he with h | h
    · refine ⟨a, ha, ?_⟩
      rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h
    · obtain ⟨b, hb, hb'⟩ := ih _ hgd hgm h
      refine ⟨b, ?_, hb'⟩
      rw [← hfac, IsRoot, eval_mul, hb.eq_zero, mul_zero]

/- English proof (translation)
The claim follows from `root_near R hR a₀ _ f rfl hf he`.
-/
theorem henselian_of_aic (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : HenselianLocalRing R where
  is_henselian f hf a₀ he _ := root_near R hR a₀ _ f rfl hf he

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun p hp hirr => ?_` and prove the remaining obligations. Establish `hl : p ∈ lifts (residue R)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `residue_surjective _`.

Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hl hp`. Establish `hpos : 0 < p.natDegree` using `natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)`. Take `⟨a, ha⟩` from `hR q hqm (by omega)`. Conclude with `⟨residue R a, by rw [← hq, eval_map, eval₂_hom, ha, map_zero]⟩`.
-/
theorem residue_algClosed (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hl : p ∈ lifts (residue R) := by
    rw [lifts_iff_coeff_lifts]; intro n; exact residue_surjective _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  have hpos : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  obtain ⟨a, ha⟩ := hR q hqm (by omega)
  exact ⟨residue R a, by rw [← hq, eval_map, eval₂_hom, ha, map_zero]⟩

/- English proof (translation)
Introduce `S _ hS p`. Establish `hA` using `aic_localization S hS p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)`. Use `residue_algClosed _ hA` as an intermediate fact. Conclude with `⟨henselian_of_aic _ hA, inferInstance⟩`.
-/
theorem LocSH_of : LateralTheory.E.ZarLocalPf.LocSH := by
  intro S _ hS p
  have hA := aic_localization S hS p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  have := residue_algClosed _ hA
  exact ⟨henselian_of_aic _ hA, inferInstance⟩

end LateralTheory.E.LocSHPf
