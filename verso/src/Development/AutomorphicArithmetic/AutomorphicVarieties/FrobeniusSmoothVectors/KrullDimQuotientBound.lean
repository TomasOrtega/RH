import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `R _ _ _ I K ι _ t ht hP`. Establish `hjac : (Set.range fun a => Ideal.Quotient.mk I (t a)) ⊆ Ring.jacobson (R ⧸ I)`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[SetLike.mem_coe, Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]`. Introduce `m hm`.

Establish `hm' : m.IsMaximal` using `hm`. Establish `h1 : (m.comap (Ideal.Quotient.mk I)).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h2` using `IsLocalRing.eq_maximalIdeal h1`. Establish `h3 : t a ∈ m.comap (Ideal.Quotient.mk I)` using `h2 ▸ ht a`. Conclude with `h3`.

Establish `h1` using `ringKrullDim_le_ringKrullDim_quotient_add_encard _ hjac`. Establish `hspan : Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `h2 : ringKrullDim ((R ⧸ I) ⧸ Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a))) = ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t)))`.

Rewrite using `[hspan]`. Conclude with `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)`. Establish `h3 : ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) ≤ ringKrullDim (R ⧸ K)`. Rewrite using `[ringKrullDim_quotient, ringKrullDim_quotient]`. Establish `hsub : PrimeSpectrum.zeroLocus (R` using `R) ((I ⊔ Ideal.span (Set.range t) : Ideal R) : Set R) ⊆ PrimeSpectrum.zeroLocus (R := R) (K : Set R) := by`.

Introduce `p hp`. Establish `hp' : I ⊔ Ideal.span (Set.range t) ≤ p.asIdeal` using `hp`. Use `hP p.asIdeal p.isPrime (le_sup_left.trans hp') fun a => ?_` and prove the remaining obligations. Conclude with `(le_sup_right.trans hp') (Ideal.subset_span ⟨a, rfl⟩)`. Conclude with `Order.krullDim_le_of_strictMono (Set.inclusion hsub) fun _ _ h => h`.

Establish `h4 : (Set.range fun a => Ideal.Quotient.mk I (t a)).encard ≤ (Fintype.card ι : ℕ)`. Rewrite using `[← Set.image_univ]`. Use `(Set.encard_image_le _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[h2]`. Use `add_le_add h3 ?_` and prove the remaining obligations. Conclude with `h4` after adjusting the coercions.
-/
theorem UpperTheory.V.Fr.krull_dim_quotient_bound :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I K : Ideal R) {ι : Type} [Fintype ι] (t : ι → R), (∀ a, t a ∈ maximalIdeal R) → (∀ P : Ideal R, P.IsPrime → I ≤ P → (∀ a, t a ∈ P) → K ≤ P) → ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ K) + (Fintype.card ι : ℕ) := by
  intro R _ _ _ I K ι _ t ht hP
  classical
  have hjac : (Set.range fun a => Ideal.Quotient.mk I (t a)) ⊆ Ring.jacobson (R ⧸ I) := by
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]
    intro m hm
    have hm' : m.IsMaximal := hm
    have h1 : (m.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : t a ∈ m.comap (Ideal.Quotient.mk I) := h2 ▸ ht a
    exact h3
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hjac
  have hspan : Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a))
      = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have h2 : ringKrullDim ((R ⧸ I) ⧸ Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a)))
      = ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) := by
    rw [hspan]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)
  have h3 : ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) ≤ ringKrullDim (R ⧸ K) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient]
    have hsub : PrimeSpectrum.zeroLocus (R := R) ((I ⊔ Ideal.span (Set.range t) : Ideal R) : Set R)
        ⊆ PrimeSpectrum.zeroLocus (R := R) (K : Set R) := by
      intro p hp
      have hp' : I ⊔ Ideal.span (Set.range t) ≤ p.asIdeal := hp
      refine hP p.asIdeal p.isPrime (le_sup_left.trans hp') fun a => ?_
      exact (le_sup_right.trans hp') (Ideal.subset_span ⟨a, rfl⟩)
    exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) fun _ _ h => h
  have h4 : (Set.range fun a => Ideal.Quotient.mk I (t a)).encard ≤ (Fintype.card ι : ℕ) := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  refine h1.trans ?_
  rw [h2]
  refine add_le_add h3 ?_
  exact_mod_cast h4
