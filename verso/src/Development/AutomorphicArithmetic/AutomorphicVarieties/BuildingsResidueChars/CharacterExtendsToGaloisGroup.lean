import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Use `choose p hp using hall`. Establish `huniq : ∀ g s, (i s = g ∨ i s = g * c) → p g = s`. Introduce `g s hs`. Apply the tactic sequence `rcases hp g with h | h <;> rcases hs with h' | h'`. Conclude with `hi (h.trans h'.symm)`.

Conclude with `absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc ((p g)⁻¹ * s))`. Conclude with `absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc (s⁻¹ * p g))`. Conclude with `hi (h.trans h'.symm)`. Use `⟨MonoidHom.mk' (fun g => δ (p g)) fun g g' => ?_, MonoidHom.ext fun s => ?_, ?_⟩` and prove the remaining obligations. Break down `hp g with h | h` into its components or cases.

Rewrite using `[huniq (g * g') (p g * p g') (by`. Rewrite using `[map_mul, h]`. Break down `hp g' with h' | h'` into its components or cases. Conclude with `Or.inl (by rw [h'])`. Conclude with `Or.inr (by rw [h', mul_assoc])), map_mul]`.

Take `⟨t, ht, hδ⟩` from `hinv (p g')`. Rewrite using `[huniq (g * g') (p g * t) (by`. Rewrite using `[map_mul, h, ht, mul_assoc g c, mul_assoc c (i _), ← mul_assoc c c, hcc, one_mul]`. Break down `hp g' with h' | h'` into its components or cases. Conclude with `Or.inr (by rw [h', mul_assoc])`.

Conclude with `Or.inl (by rw [h', mul_assoc g', hcc, mul_one])), map_mul, hδ]`. Express the relevant statement in the definitionally equal form `δ (p (i s)) = δ s`. Rewrite using `[huniq _ s (Or.inl rfl)]`. Express the relevant statement in the definitionally equal form `δ (p c) = 1`. Rewrite using `[huniq c 1 (Or.inr (by rw [map_one, hcc])), map_one]`.
-/
private theorem ext_two {Γ H A : Type} [Group Γ] [Group H] [CommGroup A] (i : H →* Γ) (hi : Function.Injective i)
    (δ : H →* A) (c : Γ) (hcc : c * c = 1) (hc : ∀ s, i s ≠ c) (hall : ∀ g, ∃ s, i s = g ∨ i s = g * c)
    (hinv : ∀ s, ∃ t, i t = c * i s * c ∧ δ t = δ s) :
    ∃ δ' : Γ →* A, δ'.comp i = δ ∧ δ' c = 1 := by
  choose p hp using hall
  have huniq : ∀ g s, (i s = g ∨ i s = g * c) → p g = s := by
    intro g s hs
    rcases hp g with h | h <;> rcases hs with h' | h'
    · exact hi (h.trans h'.symm)
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc ((p g)⁻¹ * s))
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc (s⁻¹ * p g))
    · exact hi (h.trans h'.symm)
  refine ⟨MonoidHom.mk' (fun g => δ (p g)) fun g g' => ?_, MonoidHom.ext fun s => ?_, ?_⟩
  · rcases hp g with h | h
    · rw [huniq (g * g') (p g * p g') (by
        rw [map_mul, h]
        rcases hp g' with h' | h'
        · exact Or.inl (by rw [h'])
        · exact Or.inr (by rw [h', mul_assoc])), map_mul]
    · obtain ⟨t, ht, hδ⟩ := hinv (p g')
      rw [huniq (g * g') (p g * t) (by
        rw [map_mul, h, ht, mul_assoc g c, mul_assoc c (i _), ← mul_assoc c c, hcc, one_mul]
        rcases hp g' with h' | h'
        · exact Or.inr (by rw [h', mul_assoc])
        · exact Or.inl (by rw [h', mul_assoc g', hcc, mul_one])), map_mul, hδ]
  · change δ (p (i s)) = δ s
    rw [huniq _ s (Or.inl rfl)]
  · change δ (p c) = 1
    rw [huniq c 1 (Or.inr (by rw [map_one, hcc])), map_one]

/- English proof (translation)
Take `⟨j, hj⟩` from `hc`. Use `j.injective ?_` and prove the remaining obligations. Rewrite using `[hj]`. Conclude with `(IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm`.
-/
private theorem conj_on {F M Ω : Type} [Field F] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra F Ω]
    [Algebra M Ω] {c : G F Ω} (hc : IsConjEl c) (x : M) :
    c (algebraMap M Ω x) = algebraMap M Ω (IsCMField.complexConj M x) := by
  obtain ⟨j, hj⟩ := hc
  refine j.injective ?_
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm

/- English proof (translation)
Set `φ : M →+* ℂ` to `Classical.choice inferInstance`. Use `φ.injective ?_` and prove the remaining obligations. Rewrite using `[IsCMField.complexEmbedding_complexConj]`. Conclude with `(IsCMField.complexEmbedding_complexConj M (φ.comp (σ : M →+* M)) x).symm`.
-/
private theorem conj_comm {K M : Type} [Field K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    (σ : M ≃ₐ[K] M) (x : M) : IsCMField.complexConj M (σ x) = σ (IsCMField.complexConj M x) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  refine φ.injective ?_
  rw [IsCMField.complexEmbedding_complexConj]
  exact (IsCMField.complexEmbedding_complexConj M (φ.comp (σ : M →+* M)) x).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hg, AlgEquiv.ext fun _ => rfl⟩`.
-/
private theorem lift_fix {F M Ω : Type} [Field F] [Field M] [Field Ω] [Algebra F M] [Algebra F Ω] [Algebra M Ω]
    [IsScalarTower F M Ω] (g : G F Ω) (hg : ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) :
    ∃ s : G M Ω, resG F M Ω s = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hg, AlgEquiv.ext fun _ => rfl⟩

/- English proof (translation)
Use `haveI : IsAlgClosure (maximalRealSubfield K) Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩`. Set `φ : K →+* ℂ` to `Classical.choice inferInstance`. Use `letI : Algebra K ℂ := φ.toAlgebra`. Set `j : Ω →+* ℂ` to `(IsAlgClosed.lift (R := K) (S := Ω) (M := ℂ)).toRingHom`. Take `⟨σ, hσ⟩` from `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := maximalRealSubfield K) j (ComplexEmbedding.conjugate j) (RingHom.ext fun x => ((mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))).symm)`.

Conclude with `⟨σ.symm, j, fun x => DFunLike.congr_fun hσ x⟩`.
-/
private theorem ex_conj (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ c : G (maximalRealSubfield K) Ω, IsConjEl c := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  let φ : K →+* ℂ := Classical.choice inferInstance
  letI : Algebra K ℂ := φ.toAlgebra
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := K) (S := Ω) (M := ℂ)).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := maximalRealSubfield K) j
    (ComplexEmbedding.conjugate j) (RingHom.ext fun x =>
      ((mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))).symm)
  exact ⟨σ.symm, j, fun x => DFunLike.congr_fun hσ x⟩

/- English proof (translation)
Introduce `K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ`. Establish `kill : ∀ t : G K Ω, (∀ x : M, t (algebraMap M Ω x) = algebraMap M Ω x) → δ t = 1` using `fun t ht => by`. Take `⟨s, rfl⟩` from `lift_fix t ht`. Conclude with `DFunLike.congr_fun hδ s`. Take `⟨c, hc⟩` from `ex_conj K Ω`.

Establish `hcc : c * c = 1`. Take `⟨j, hj⟩` from `hc`. Conclude with `AlgEquiv.ext fun x => j.injective (by`. Rewrite using `[AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply])`. Establish `hKM : ∀ (g : G (maximalRealSubfield K) Ω), (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → ∃ s : G K Ω, resG (maximalRealSubfield K) K Ω s = g ∧ δ s = 1` using `fun g hg => by`.

Take `⟨s, rfl⟩` from `lift_fix (M := K) g fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply K M Ω, hg]`. Conclude with `⟨s, rfl, kill s hg⟩`. Take `⟨δ', h1, h2⟩` from `ext_two (resG (maximalRealSubfield K) K Ω) (AlgEquiv.restrictScalars_injective _) δ c hcc (fun s hs => IsCMField.complexConj_ne_one K (AlgEquiv.ext fun x => (algebraMap K Ω).injective (by`. Rewrite using `[← conj_on hc, ← hs]`.

Conclude with `s.commutes x)))`. Use the proof step `(fun g => by`. Establish `h2 : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2` using `(Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K) ▸ IsGalois.card_aut_eq_finrank (maximalRealSubfield K) K`. Rewrite `h2` using `[Nat.card_eq_two_iff' 1]`. Distinguish the cases in `hg : g.restrictNormal K = 1`.

Take `⟨s, hs⟩` from `lift_fix (M := K) g fun x => by`. Rewrite using `[← AlgEquiv.restrictNormal_commutes, hg, AlgEquiv.one_apply]`. Conclude with `⟨s, Or.inl hs⟩`. Establish `hg'` using `h2.unique hg (IsCMField.complexConj_ne_one K)`. Take `⟨s, hs⟩` from `lift_fix (M := K) (g * c) fun x => by`.

Rewrite using `[AlgEquiv.mul_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes, hg', IsCMField.complexConj_apply_apply]`. Conclude with `⟨s, Or.inr hs⟩)`. Use the proof step `(fun s => by`. Take `⟨t, ht, hδt⟩` from `hKM (c * resG _ K Ω s * c * (resG _ K Ω s)⁻¹) fun x => by`. Take `⟨y, rfl⟩` from `(s.restrictNormal M).surjective x`.

Express the relevant statement in the definitionally equal form `c (s (c (s.symm _))) = _`. Rewrite using `[AlgEquiv.restrictNormal_commutes, s.symm_apply_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes, conj_on hc, conj_comm, IsCMField.complexConj_apply_apply, AlgEquiv.restrictNormal_commutes]`. Conclude with `⟨t * s, by rw [map_mul, ht, inv_mul_cancel_right], by rw [map_mul, hδt, one_mul]⟩)`. Establish `h3 : ∀ g : G (maximalRealSubfield K) Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → δ' g = 1` using `fun g hg => by`. Take `⟨s, rfl, hs⟩` from `hKM g hg`.

Conclude with `(DFunLike.congr_fun h1 s).trans hs`. Use `⟨δ', h1, fun d hd => ?_, ?_⟩` and prove the remaining obligations. Establish `h4` using `h3 (d * c) fun x => by`. Rewrite using `[AlgEquiv.mul_apply, conj_on hc, conj_on hd, IsCMField.complexConj_apply_apply]`. Rewrite `h4` using `[map_mul, h2, mul_one]`. Then use the resulting hypothesis.

Set `f : M →ₐ[maximalRealSubfield K] Ω` to `IsScalarTower.toAlgHom (maximalRealSubfield K) M Ω haveI : FiniteDimensional (maximalRealSubfield K) f.fieldRange := (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional`. Use `Subgroup.isOpen_mono (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen f.fieldRange)` and prove the remaining obligations. Conclude with `h3 g fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩`.
-/
theorem UpperTheory.character_extends_to_galois_group :
    UpperTheory.V.Af.Sol.ExtChar := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
  have kill : ∀ t : G K Ω, (∀ x : M, t (algebraMap M Ω x) = algebraMap M Ω x) → δ t = 1 := fun t ht => by
    obtain ⟨s, rfl⟩ := lift_fix t ht
    exact DFunLike.congr_fun hδ s
  obtain ⟨c, hc⟩ := ex_conj K Ω
  have hcc : c * c = 1 := by
    obtain ⟨j, hj⟩ := hc
    exact AlgEquiv.ext fun x => j.injective (by
      rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply])
  have hKM : ∀ (g : G (maximalRealSubfield K) Ω), (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) →
      ∃ s : G K Ω, resG (maximalRealSubfield K) K Ω s = g ∧ δ s = 1 := fun g hg => by
    obtain ⟨s, rfl⟩ := lift_fix (M := K) g fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω, hg]
    exact ⟨s, rfl, kill s hg⟩
  obtain ⟨δ', h1, h2⟩ := ext_two (resG (maximalRealSubfield K) K Ω) (AlgEquiv.restrictScalars_injective _) δ c hcc
    (fun s hs => IsCMField.complexConj_ne_one K (AlgEquiv.ext fun x => (algebraMap K Ω).injective (by
      rw [← conj_on hc, ← hs]
      exact s.commutes x)))
    (fun g => by
      have h2 : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2 :=
        (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K) ▸
          IsGalois.card_aut_eq_finrank (maximalRealSubfield K) K
      rw [Nat.card_eq_two_iff' 1] at h2
      by_cases hg : g.restrictNormal K = 1
      · obtain ⟨s, hs⟩ := lift_fix (M := K) g fun x => by
          rw [← AlgEquiv.restrictNormal_commutes, hg, AlgEquiv.one_apply]
        exact ⟨s, Or.inl hs⟩
      · have hg' := h2.unique hg (IsCMField.complexConj_ne_one K)
        obtain ⟨s, hs⟩ := lift_fix (M := K) (g * c) fun x => by
          rw [AlgEquiv.mul_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes, hg',
            IsCMField.complexConj_apply_apply]
        exact ⟨s, Or.inr hs⟩)
    (fun s => by
      obtain ⟨t, ht, hδt⟩ := hKM (c * resG _ K Ω s * c * (resG _ K Ω s)⁻¹) fun x => by
        obtain ⟨y, rfl⟩ := (s.restrictNormal M).surjective x
        change c (s (c (s.symm _))) = _
        rw [AlgEquiv.restrictNormal_commutes, s.symm_apply_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes,
          conj_on hc, conj_comm, IsCMField.complexConj_apply_apply, AlgEquiv.restrictNormal_commutes]
      exact ⟨t * s, by rw [map_mul, ht, inv_mul_cancel_right], by rw [map_mul, hδt, one_mul]⟩)
  have h3 : ∀ g : G (maximalRealSubfield K) Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → δ' g = 1 :=
    fun g hg => by
      obtain ⟨s, rfl, hs⟩ := hKM g hg
      exact (DFunLike.congr_fun h1 s).trans hs
  refine ⟨δ', h1, fun d hd => ?_, ?_⟩
  · have h4 := h3 (d * c) fun x => by
      rw [AlgEquiv.mul_apply, conj_on hc, conj_on hd, IsCMField.complexConj_apply_apply]
    rwa [map_mul, h2, mul_one] at h4
  · let f : M →ₐ[maximalRealSubfield K] Ω := IsScalarTower.toAlgHom (maximalRealSubfield K) M Ω
    haveI : FiniteDimensional (maximalRealSubfield K) f.fieldRange :=
      (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen f.fieldRange)
    exact h3 g fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩
