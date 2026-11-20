import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

open GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Use `set y : Fin D → K := fun j => x j.succ / x 0 with hydef`. Use `letI : Algebra k K := ι.toAlgebra`. Establish `hyk : AlgebraicIndependent k y` using `hy.extendScalars_of_isIntegral k`. Establish `hinj : Function.Injective (MvPolynomial.eval₂Hom ι y)` using `hyk`. Use `⟨?_, hinj⟩` and prove the remaining obligations.

Use `haveI : CharZero k := ι.charZero`. Use `haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'`. Use `set F : Subfield K := ratF x with hF`. Establish `hyF : ∀ j, y j ∈ F` using `fun j => Subfield.subset_closure ⟨j, rfl⟩`. Use `set n := Module.finrank ℤ k with hn`.

Set `b` to `Module.finBasis ℤ k`. Use `set R : Subring K := Subring.closure (Set.range y) with hRdef`. Establish `hR : R ≤ (MvPolynomial.eval₂Hom (Int.castRingHom K) y).range` using `(Subring.closure_le).2 (by rintro _ ⟨j, rfl⟩; exact ⟨MvPolynomial.X j, by simp⟩)`. Establish `hli : LinearIndependent F (fun i => ι (b i))`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i₀`. Establish `hg' : ∑ i, (g i : K) * ι (b i) = 0` using `hg`. Establish `hfrac : ∀ i, ∃ a ∈ R, ∃ c ∈ R, c ≠ 0 ∧ (g i : K) = a / c`. Introduce `i`. Take `⟨a, ha, c, hc, e⟩` from `Subfield.mem_closure_iff.1 (g i).2`.

Distinguish the cases in `h0 : c = 0`. Conclude with `⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by rw [← e, h0, div_zero, zero_div]⟩`. Conclude with `⟨a, ha, c, hc, h0, e.symm⟩`. Use `choose a ha c hc hc0 hgac using hfrac`. Use `set Q : K := ∏ j, c j with hQdef`.

Establish `hQ : Q ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hc0 j`. Establish `hp : ∀ i, Q * (g i : K) = a i * ∏ j ∈ Finset.univ.erase i, c j`. Introduce `i`. Rewrite using `[hgac i, hQdef, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]`. Clear denominators, using `[hc0 i]` for the nonvanishing conditions.

Establish `hpR : ∀ i, Q * (g i : K) ∈ R` using `fun i => by`. Rewrite using `[hp i]`. Conclude with `R.mul_mem (ha i) (Subring.prod_mem _ fun j _ => hc j)`. Use `choose P hP using fun i => hR (hpR i)`. Establish `hsum : ∑ i, Q * (g i : K) * ι (b i) = 0`.

Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum, hg', mul_zero]`. Establish `hcomp : ι.comp (Int.castRingHom k) = Int.castRingHom K` using `RingHom.ext_int _ _`. Establish `hev : MvPolynomial.eval₂Hom ι y (∑ i, MvPolynomial.C (b i) * MvPolynomial.map (Int.castRingHom k) (P i)) = 0`. Simplify using `only [map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_map_hom, hcomp, hP]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hP0` using `hinj (hev.trans (map_zero _).symm)`. Establish `hPi : ∀ i, P i = 0`. Introduce `i`. Use extensionality with `m`.

Establish `hm` using `congrArg (MvPolynomial.coeff m) hP0`. Simplify using `only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero, eq_intCast] at hm`. Establish `hm' : ∑ j, MvPolynomial.coeff m (P j) • b j = 0`. Rewrite using `[← hm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[zsmul_eq_mul, mul_comm]`. Rewrite using `[MvPolynomial.coeff_zero]`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent _ hm' i`. Establish `h1 : Q * (g i₀ : K) = 0` using `by rw [← hP i₀, hPi i₀, map_zero]`. Conclude with `Subtype.ext ((mul_eq_zero.1 h1).resolve_left hQ)`.

Establish `hV : Module.finrank F (Submodule.span F (Set.range fun i => ι (b i))) = n`. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin]`. Set `E : IntermediateField F K` to `IntermediateField.adjoin F (Set.range ι)`. Establish `halg : ∀ z ∈ Set.range ι, IsAlgebraic F z`. Introduce and unpack `_ ⟨a, rfl⟩`.

Establish `h1 : IsIntegral ℤ (ι a)` using `(Algebra.IsIntegral.isIntegral (R := ℤ) a).map ι.toIntAlgHom`. Conclude with `(h1.tower_top (A := F)).isAlgebraic`. Establish `hEsub : Subalgebra.toSubmodule E.toSubalgebra = Submodule.span F (Set.range fun i => ι (b i))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Algebra.adjoin_eq_span]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hcl : Submonoid.closure (Set.range ι) ≤ MonoidHom.mrange ι` using `Submonoid.closure_le.2 (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)`. Take `⟨a, rfl⟩` from `hcl hz`. Establish `hsr` using `b.sum_repr a`.

Express the relevant statement in the definitionally equal form `ι a ∈ _`. Rewrite using `[← hsr, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Conclude with `zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => ι (b i)) i)) _`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `IntermediateField.subset_adjoin F _ ⟨b i, rfl⟩`. Establish `hEF : Module.finrank F E = n`. Establish `: Module.finrank F E = Module.finrank F (Subalgebra.toSubmodule E.toSubalgebra)` using `rfl`.

Rewrite using `[this, hEsub, hV]`. Establish `hsub : E.toSubfield = Subfield.closure (Set.range ι ∪ Set.range y)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_toSubfield]`. Use `Subfield.closure_le.2 (Set.union_subset ?_ ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `(Subfield.closure_le.2 (Set.subset_union_right.trans Subfield.subset_closure)) z.2`. Conclude with `Set.subset_union_left.trans Subfield.subset_closure`. Use `Subfield.closure_le.2 (Set.union_subset ?_ ?_)` and prove the remaining obligations. Conclude with `fun z hz => IntermediateField.subset_adjoin F _ hz`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `E.algebraMap_mem ⟨y j, hyF j⟩`. Establish `htow` using `Module.finrank_mul_finrank F E K`. Establish `hEK : Module.finrank E.toSubfield K = Module.finrank E K` using `rfl`. Rewrite using `[← hsub, hEK, ← htow, hEF, mul_comm]`.
-/
theorem finrank_ratF_eq_mul_rank (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K]
    (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K) (hι : Function.Injective ι)
    (hy : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  classical
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  letI : Algebra k K := ι.toAlgebra
  have hyk : AlgebraicIndependent k y := hy.extendScalars_of_isIntegral k
  have hinj : Function.Injective (MvPolynomial.eval₂Hom ι y) := hyk
  refine ⟨?_, hinj⟩
  haveI : CharZero k := ι.charZero
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  set F : Subfield K := ratF x with hF
  have hyF : ∀ j, y j ∈ F := fun j => Subfield.subset_closure ⟨j, rfl⟩
  set n := Module.finrank ℤ k with hn
  let b := Module.finBasis ℤ k
  set R : Subring K := Subring.closure (Set.range y) with hRdef
  have hR : R ≤ (MvPolynomial.eval₂Hom (Int.castRingHom K) y).range :=
    (Subring.closure_le).2 (by rintro _ ⟨j, rfl⟩; exact ⟨MvPolynomial.X j, by simp⟩)
  have hli : LinearIndependent F (fun i => ι (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i₀
    have hg' : ∑ i, (g i : K) * ι (b i) = 0 := hg
    have hfrac : ∀ i, ∃ a ∈ R, ∃ c ∈ R, c ≠ 0 ∧ (g i : K) = a / c := by
      intro i
      obtain ⟨a, ha, c, hc, e⟩ := Subfield.mem_closure_iff.1 (g i).2
      by_cases h0 : c = 0
      · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by rw [← e, h0, div_zero, zero_div]⟩
      · exact ⟨a, ha, c, hc, h0, e.symm⟩
    choose a ha c hc hc0 hgac using hfrac
    set Q : K := ∏ j, c j with hQdef
    have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hc0 j
    have hp : ∀ i, Q * (g i : K) = a i * ∏ j ∈ Finset.univ.erase i, c j := by
      intro i
      rw [hgac i, hQdef, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
      field_simp [hc0 i]
    have hpR : ∀ i, Q * (g i : K) ∈ R := fun i => by
      rw [hp i]; exact R.mul_mem (ha i) (Subring.prod_mem _ fun j _ => hc j)
    choose P hP using fun i => hR (hpR i)
    have hsum : ∑ i, Q * (g i : K) * ι (b i) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hg', mul_zero]
    have hcomp : ι.comp (Int.castRingHom k) = Int.castRingHom K := RingHom.ext_int _ _
    have hev : MvPolynomial.eval₂Hom ι y
        (∑ i, MvPolynomial.C (b i) * MvPolynomial.map (Int.castRingHom k) (P i)) = 0 := by
      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_map_hom, hcomp, hP]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
      ring
    have hP0 := hinj (hev.trans (map_zero _).symm)
    have hPi : ∀ i, P i = 0 := by
      intro i
      ext m
      have hm := congrArg (MvPolynomial.coeff m) hP0
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
        MvPolynomial.coeff_zero, eq_intCast] at hm
      have hm' : ∑ j, MvPolynomial.coeff m (P j) • b j = 0 := by
        rw [← hm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [zsmul_eq_mul, mul_comm]
      rw [MvPolynomial.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hm' i
    have h1 : Q * (g i₀ : K) = 0 := by rw [← hP i₀, hPi i₀, map_zero]
    exact Subtype.ext ((mul_eq_zero.1 h1).resolve_left hQ)
  have hV : Module.finrank F (Submodule.span F (Set.range fun i => ι (b i))) = n := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  let E : IntermediateField F K := IntermediateField.adjoin F (Set.range ι)
  have halg : ∀ z ∈ Set.range ι, IsAlgebraic F z := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsIntegral ℤ (ι a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map ι.toIntAlgHom
    exact (h1.tower_top (A := F)).isAlgebraic
  have hEsub : Subalgebra.toSubmodule E.toSubalgebra = Submodule.span F (Set.range fun i => ι (b i)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Algebra.adjoin_eq_span]
      refine Submodule.span_le.2 ?_
      intro z hz
      have hcl : Submonoid.closure (Set.range ι) ≤ MonoidHom.mrange ι :=
        Submonoid.closure_le.2 (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)
      obtain ⟨a, rfl⟩ := hcl hz
      have hsr := b.sum_repr a
      change ι a ∈ _
      rw [← hsr, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => ι (b i)) i)) _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin F _ ⟨b i, rfl⟩
  have hEF : Module.finrank F E = n := by
    have : Module.finrank F E = Module.finrank F (Subalgebra.toSubmodule E.toSubalgebra) := rfl
    rw [this, hEsub, hV]
  have hsub : E.toSubfield = Subfield.closure (Set.range ι ∪ Set.range y) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨z, rfl⟩
        exact (Subfield.closure_le.2 (Set.subset_union_right.trans Subfield.subset_closure)) z.2
      · exact Set.subset_union_left.trans Subfield.subset_closure
    · refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · exact fun z hz => IntermediateField.subset_adjoin F _ hz
      · rintro _ ⟨j, rfl⟩; exact E.algebraMap_mem ⟨y j, hyF j⟩
  have htow := Module.finrank_mul_finrank F E K
  have hEK : Module.finrank E.toSubfield K = Module.finrank E K := rfl
  rw [← hsub, hEK, ← htow, hEF, mul_comm]

end GlobalTheory.HSAmp
