import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Establish `hne : J ≠ ⊤` using `fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hle))`. Use `haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne`. Use `haveI : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Use `set π := Ideal.Quotient.mk J with hπ`. Establish `hsurj : Function.Surjective π` using `Ideal.Quotient.mk_surjective`.

Use `haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj`. Take `⟨s, hs, hcard⟩` from `Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ J))`. Use `choose g hg using hsurj`. Establish `hrad : maximalIdeal (S ⧸ J) ≤ (Ideal.span (s : Set (S ⧸ J))).radical`. Rewrite using `[Ideal.radical_eq_sInf, le_sInf_iff]`.

Introduce and unpack `J ⟨hJ, hJ'⟩`. Conclude with `hs.2 ⟨hJ', hJ⟩ (le_maximalIdeal hJ'.ne_top)`. Use `⟨s.card, fun i => g (s.equivFin.symm i), fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : π (g (s.equivFin.symm i)) ∈ maximalIdeal (S ⧸ J)`. Rewrite using `[hg]`.

Conclude with `hs.1.2 (Ideal.subset_span (s.equivFin.symm i).2)`. Rewrite `h1`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun h => h1 (h.map π)`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]`. Both sides reduce to the same expression.

Introduce `y hy`. Take `⟨N, hN⟩` from `hrad (map_nonunit π y hy)`. Establish `h2 : Ideal.span (s : Set (S ⧸ J)) ≤ (Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π`. Rewrite using `[Ideal.span_le]`. Introduce `y hy`.

Rewrite using `[← hg y]`. Use `Ideal.mem_map_of_mem π (Ideal.subset_span ⟨s.equivFin ⟨y, hy⟩, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `h3 : y ^ N ∈ ((Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π).comap π`.

Rewrite using `[Ideal.mem_comap, map_pow]`. Conclude with `h2 hN`. Rewrite `h3` using `[Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker]`. Then use the resulting hypothesis.
-/
private theorem sop_mod (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (J : Ideal S)
    (hle : J ≤ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧ ringKrullDim (S ⧸ J) = n ∧
      maximalIdeal S ≤ (Ideal.span (Set.range x) ⊔ J).radical := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ J))
  choose g hg using hsurj
  have hrad : maximalIdeal (S ⧸ J) ≤ (Ideal.span (s : Set (S ⧸ J))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro J ⟨hJ, hJ'⟩
    exact hs.2 ⟨hJ', hJ⟩ (le_maximalIdeal hJ'.ne_top)
  refine ⟨s.card, fun i => g (s.equivFin.symm i), fun i => ?_, ?_, ?_⟩
  · have h1 : π (g (s.equivFin.symm i)) ∈ maximalIdeal (S ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (s.equivFin.symm i).2)
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    rfl
  · intro y hy
    obtain ⟨N, hN⟩ := hrad (map_nonunit π y hy)
    have h2 : Ideal.span (s : Set (S ⧸ J)) ≤
        (Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π := by
      rw [Ideal.span_le]
      intro y hy
      rw [← hg y]
      refine Ideal.mem_map_of_mem π (Ideal.subset_span ⟨s.equivFin ⟨y, hy⟩, ?_⟩)
      simp
    refine ⟨N, ?_⟩
    have h3 : y ^ N ∈ ((Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π).comap π := by
      rw [Ideal.mem_comap, map_pow]
      exact h2 hN
    rwa [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker] at h3

/- English proof (translation)
Use `haveI : IsDomain A := NoZeroDivisors.to_isDomain A`. Use `letI := φ.toAlgebra`. Use `haveI : Module.Finite A B := h`. Conclude with `inj_dim A B d hA hB`.
-/
private theorem inj_of_finite {A B : Type} [CommRing A] [Nontrivial A] [NoZeroDivisors A] [CommRing B] (φ : A →+* B)
    (h : φ.Finite) (d : ℕ) (hA : ringKrullDim A = d) (hB : ringKrullDim B = d) :
    Function.Injective φ := by
  haveI : IsDomain A := NoZeroDivisors.to_isDomain A
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h
  exact inj_dim A B d hA hB

/- English proof (translation)
Use `haveI := h.noeth`. Take `⟨d, x, hx, hd, hrad⟩` from `sop_mod R ⊥ bot_le`. Use `haveI : IsAdicComplete (maximalIdeal k) k := by`. Rewrite using `[maximalIdeal_eq_bot]`. Use `infer_instance`.

Take `⟨φ, -, hfin, hloc⟩` from `cl_mvps k R h (Fin d) x hx (hrad.trans (Ideal.radical_mono (sup_le_sup_left bot_le _)))`. Establish `hR : ringKrullDim R = d`. Rewrite using `[← hd]`. Conclude with `(ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).symm`. Conclude with `⟨d, φ, inj_of_finite φ.toRingHom hfin d (cl_cm.2 k d).2 hR, hfin, hloc, hR⟩`.
-/
private theorem nn_field (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] [IsLocalRing R]
    (h : IsCL k R) : ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) k →ₐ[k] R),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d := by
  haveI := h.noeth
  obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R ⊥ bot_le
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]; infer_instance
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps k R h (Fin d) x hx
    (hrad.trans (Ideal.radical_mono (sup_le_sup_left bot_le _)))
  have hR : ringKrullDim R = d := by
    rw [← hd]; exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).symm
  exact ⟨d, φ, inj_of_finite φ.toRingHom hfin d (cl_cm.2 k d).2 hR, hfin, hloc, hR⟩

/- English proof (translation)
The claim follows from `h.noeth complete := h.complete isLocalHom := inferInstance res_fin := by haveI := h.res_fin exact Module.Finite.of_restrictScalars_finite O k (ResidueField R)`.
-/
private theorem isCL_field (O k R : Type) [CommRing O] [Field k] [CommRing R] [IsLocalRing R]
    [Algebra O k] [Algebra O R] [Algebra k R] [IsScalarTower O k R] (h : IsCL O R) : IsCL k R where
  noeth := h.noeth
  complete := h.complete
  isLocalHom := inferInstance
  res_fin := by
    haveI := h.res_fin
    exact Module.Finite.of_restrictScalars_finite O k (ResidueField R)

/- English proof (translation)
Introduce `O _ _ _ _ R _ _ _ _ h`. Use `haveI := h.noeth`. Use `haveI := h.isLocalHom`. Use `⟨fun hinj => ?_, fun hninj => ?_⟩` and prove the remaining obligations. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`.

Establish `hm : maximalIdeal O = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Establish `ha : algebraMap O R ϖ ∈ maximalIdeal R` using `map_nonunit _ _ hϖ.not_isUnit`. Establish `ha0 : algebraMap O R ϖ ≠ 0` using `(map_ne_zero_iff _ hinj).2 hϖ.ne_zero`. Take `⟨d, x, hx, hd, hrad⟩` from `sop_mod R (Ideal.span {algebraMap O R ϖ}) ((Ideal.span_singleton_le_iff_mem _).2 ha)`. Take `⟨φ, -, hfin, hloc⟩` from `cl_mvps O R h (Fin d) x hx (by rwa [hm, Ideal.map_span, Set.image_singleton])`.

Establish `hR : ringKrullDim R = (d + 1 : ℕ)`. Rewrite using `[← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0) ha, hd]`. Both sides reduce to the same expression. Conclude with `⟨d, φ, inj_of_finite φ.toRingHom hfin (d + 1) (cl_cm.1 O d).2 hR, hfin, hloc, hR⟩`. Establish `hk0 : RingHom.ker (algebraMap O R) ≠ ⊥` using `fun e => hninj ((RingHom.injective_iff_ker_eq_bot _).2 e)`.

Establish `hk : RingHom.ker (algebraMap O R) = maximalIdeal O` using `eq_maximalIdeal (Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hk0)`. Set `ψ : ResidueField O →+* R` to `Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R) (fun a ha => by rwa [← hk] at ha)`. Use `letI : Algebra (ResidueField O) R := ψ.toAlgebra`. Use `haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `h' : IsCL (ResidueField O) R` using `isCL_field O (ResidueField O) R h`.

Take `⟨d, φ, h1, h2, h3, h4⟩` from `nn_field (ResidueField O) R h'`. Conclude with `⟨d, φ.restrictScalars O, h1, h2, ⟨fun a ha => h3.1 a ha⟩, h4⟩`.
-/
theorem UpperTheory.V.CA.cl_nn :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] [IsDomain R], IsCL O R → (Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) O →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = (d + 1 : ℕ)) ∧ (¬ Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) (ResidueField O) →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d) := by
  intro O _ _ _ _ R _ _ _ _ h
  haveI := h.noeth
  haveI := h.isLocalHom
  refine ⟨fun hinj => ?_, fun hninj => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have ha : algebraMap O R ϖ ∈ maximalIdeal R := map_nonunit _ _ hϖ.not_isUnit
    have ha0 : algebraMap O R ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R (Ideal.span {algebraMap O R ϖ})
      ((Ideal.span_singleton_le_iff_mem _).2 ha)
    obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R h (Fin d) x hx
      (by rwa [hm, Ideal.map_span, Set.image_singleton])
    have hR : ringKrullDim R = (d + 1 : ℕ) := by
      rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ha0) ha, hd]
      rfl
    exact ⟨d, φ, inj_of_finite φ.toRingHom hfin (d + 1) (cl_cm.1 O d).2 hR, hfin, hloc, hR⟩
  · have hk0 : RingHom.ker (algebraMap O R) ≠ ⊥ := fun e =>
      hninj ((RingHom.injective_iff_ker_eq_bot _).2 e)
    have hk : RingHom.ker (algebraMap O R) = maximalIdeal O :=
      eq_maximalIdeal (Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hk0)
    let ψ : ResidueField O →+* R := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R)
      (fun a ha => by rwa [← hk] at ha)
    letI : Algebra (ResidueField O) R := ψ.toAlgebra
    haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h' : IsCL (ResidueField O) R := isCL_field O (ResidueField O) R h
    obtain ⟨d, φ, h1, h2, h3, h4⟩ := nn_field (ResidueField O) R h'
    exact ⟨d, φ.restrictScalars O, h1, h2, ⟨fun a ha => h3.1 a ha⟩, h4⟩
