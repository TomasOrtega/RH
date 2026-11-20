import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

open NumberField UpperTheory.V.Af.Sol

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hlt : 1 < Nat.card G`. Use `Nat.card_pos (α := G)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hlt`. Use `haveI : IsSimpleGroup G := { eq_bot_or_eq_top_of_normal := fun N hN => by`. Distinguish the cases in `h : N = ⊥`. Conclude with `Or.inl h`. Conclude with `Or.inr (hne N hN h) }`.

Establish `hc` using `(IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hs`. Use `letI : CommGroup G := { ‹Group G› with mul_comm := hc }`. Conclude with `hp (CommGroup.is_simple_iff_prime_card.1 ‹IsSimpleGroup G›)`.
-/
private theorem exists_proper_nontrivial_normal_of_solvable_not_prime_card (G : Type) [Group G] [Finite G] (hs : IsSolvable G)
    (h1 : Nat.card G ≠ 1) (hp : ¬ (Nat.card G).Prime) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hne
  push_neg at hne
  have hlt : 1 < Nat.card G := by
    have := Nat.card_pos (α := G)
    omega
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hlt
  haveI : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN => by
        by_cases h : N = ⊥
        · exact Or.inl h
        · exact Or.inr (hne N hN h) }
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hs
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  exact hp (CommGroup.is_simple_iff_prime_card.1 ‹IsSimpleGroup G›)

/- English proof (translation)
Establish `hext : ∀ φ : K →+* ℂ, ∃ Φ : M →+* ℂ, ∀ x : K, Φ x = φ x`. Introduce `φ`. Use `letI : Algebra K ℂ := φ.toAlgebra`. Use `⟨(IsAlgClosed.lift : M →ₐ[K] ℂ).toRingHom, fun x => ?_⟩` and prove the remaining obligations. Conclude with `(IsAlgClosed.lift : M →ₐ[K] ℂ).commutes x`.

Set `τ : K ≃+* K` to `{ toFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩ invFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩ left_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x) right_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x) map_mul' := fun x …`. Set `σ : Gal(K/ℚ)` to `τ.toRatAlgEquiv`. Establish `hσ : ∀ x : K, ((σ x : K) : M) = IsCMField.complexConj M x` using `fun x => rfl`. Establish `hconj : ∀ φ : K →+* ℂ, ComplexEmbedding.IsConj φ σ`. Introduce `φ`.

Take `⟨Φ, hΦ⟩` from `hext φ`. Unfold `ComplexEmbedding.IsConj`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hΦ]`. Use `show _ = φ (σ x)`.

Rewrite using `[← hΦ, hσ, IsCMField.complexEmbedding_complexConj]`. Distinguish the cases in `h1 : σ = 1`. Use `left`. Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`.

Use `hconj w.embedding` as an intermediate fact. Rewrite `this` using `[h1]`. Unfold `ComplexEmbedding.IsConj at this`. Rewrite using `[this]`. Both sides reduce to the same expression.

Use `right haveI : IsTotallyComplex K := ⟨fun w => InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff (hconj _)).1 h1)⟩`. Take `⟨φ0⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `hord : Nat.card (Subgroup.zpowers σ) = 2`. Rewrite using `[Nat.card_zpowers]`. Conclude with `ComplexEmbedding.orderOf_isConj_two_of_ne_one (hconj φ0) h1`.

Use `haveI : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)`. Use `haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _`. Set `L : IntermediateField ℚ K` to `FixedPoints.intermediateField (Subgroup.zpowers σ)`. Establish `hfix : ∀ x : L, σ (x : K) = x` using `fun x => x.2 ⟨σ, Subgroup.mem_zpowers σ⟩`. Use `haveI : IsTotallyReal L := ⟨fun w => by`.

Take `⟨W, rfl⟩` from `w.comap_surjective (K := K)`. Simplify using `only`. Rewrite using `[← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Establish `h` using `RingHom.congr_fun (hconj W.embedding) (x : K)`.

Rewrite `h`, the goal using `[ComplexEmbedding.conjugate_coe_eq]`. Simplify using `only [RingHom.comp_apply] at h ⊢`. Rewrite using `[show algebraMap L K x = (x : K) from rfl, h]`. Conclude with `congrArg W.embedding (hfix x)⟩`. Use `haveI : Algebra.IsQuadraticExtension L K := ⟨by`.

Rewrite `hord` using `[Nat.card_eq_fintype_card]`. Rewrite using `[← hord]`. Conclude with `FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩`. Conclude with `IsCMField.ofCMExtension L K`.
-/
private theorem rc_of_intermediateField_stable_under_complexConj {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    [IsCMField M] (K : IntermediateField F M)
    (hK : ∀ x ∈ K, IsCMField.complexConj M x ∈ K) : RC K := by
  have hext : ∀ φ : K →+* ℂ, ∃ Φ : M →+* ℂ, ∀ x : K, Φ x = φ x := by
    intro φ
    letI : Algebra K ℂ := φ.toAlgebra
    refine ⟨(IsAlgClosed.lift : M →ₐ[K] ℂ).toRingHom, fun x => ?_⟩
    exact (IsAlgClosed.lift : M →ₐ[K] ℂ).commutes x
  let τ : K ≃+* K :=
    { toFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      invFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      left_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      right_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      map_mul' := fun x y => Subtype.ext (by simp [map_mul])
      map_add' := fun x y => Subtype.ext (by simp [map_add]) }
  let σ : Gal(K/ℚ) := τ.toRatAlgEquiv
  have hσ : ∀ x : K, ((σ x : K) : M) = IsCMField.complexConj M x := fun x => rfl
  have hconj : ∀ φ : K →+* ℂ, ComplexEmbedding.IsConj φ σ := by
    intro φ
    obtain ⟨Φ, hΦ⟩ := hext φ
    unfold ComplexEmbedding.IsConj
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hΦ]
    show _ = φ (σ x)
    rw [← hΦ, hσ, IsCMField.complexEmbedding_complexConj]
  by_cases h1 : σ = 1
  · left
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    have := hconj w.embedding
    rw [h1] at this
    unfold ComplexEmbedding.IsConj at this
    rw [this]
    rfl
  · right
    haveI : IsTotallyComplex K :=
      ⟨fun w => InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff (hconj _)).1 h1)⟩
    obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hord : Nat.card (Subgroup.zpowers σ) = 2 := by
      rw [Nat.card_zpowers]
      exact ComplexEmbedding.orderOf_isConj_two_of_ne_one (hconj φ0) h1
    haveI : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)
    haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    let L : IntermediateField ℚ K := FixedPoints.intermediateField (Subgroup.zpowers σ)
    have hfix : ∀ x : L, σ (x : K) = x := fun x => x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    haveI : IsTotallyReal L := ⟨fun w => by
      obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
      dsimp only
      rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
        ComplexEmbedding.isReal_iff]
      ext x
      have h := RingHom.congr_fun (hconj W.embedding) (x : K)
      rw [ComplexEmbedding.conjugate_coe_eq] at h ⊢
      simp only [RingHom.comp_apply] at h ⊢
      rw [show algebraMap L K x = (x : K) from rfl, h]
      exact congrArg W.embedding (hfix x)⟩
    haveI : Algebra.IsQuadraticExtension L K :=
      ⟨by
        rw [Nat.card_eq_fintype_card] at hord
        rw [← hord]
        exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
    exact IsCMField.ofCMExtension L K

/- English proof (translation)
Introduce `F M _ _ _ _ _ _ hs hF hM h1 hp`. Take `⟨N, hN, hbot, htop⟩` from `exists_proper_nontrivial_normal_of_solvable_not_prime_card Gal(M/F) hs (by rwa [IsGalois.card_aut_eq_finrank]) (by rwa [IsGalois.card_aut_eq_finrank])`. Use `⟨IntermediateField.fixedField N, ?_, ?_, IsGalois.of_fixedField_normal_subgroup N, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `htop` to reduce the goal to its premises.

Rewrite using `[← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_bot]`. Introduce `h`. Apply `hbot` to reduce the goal to its premises. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_top]`. Break down `hM with hM | hM` into its components or cases.

Use `left`. Conclude with `IsTotallyReal.of_algebra (IntermediateField.fixedField N) M`. Apply `rc_of_intermediateField_stable_under_complexConj` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx`, the goal using `[IntermediateField.mem_fixedField_iff]`.

Introduce `n hn`. Take `⟨Φ⟩ : Nonempty (M →+* ℂ)` from `inferInstance`. Apply `Φ.injective` to reduce the goal to its premises. Establish `h2` using `IsCMField.complexEmbedding_complexConj M (Φ.comp n.toRingHom) x`. Express the relevant statement in the definitionally equal form `Φ (n (IsCMField.complexConj M x)) = (starRingEnd ℂ) (Φ (n x)) at h2`.

Rewrite using `[h2, hx n hn, IsCMField.complexEmbedding_complexConj]`.
-/
theorem UpperTheory.solvable_cm_extension_tower :
    UpperTheory.V.Af.Sol.Tower := by
  intro F M _ _ _ _ _ _ hs hF hM h1 hp
  obtain ⟨N, hN, hbot, htop⟩ := exists_proper_nontrivial_normal_of_solvable_not_prime_card Gal(M/F) hs
    (by rwa [IsGalois.card_aut_eq_finrank]) (by rwa [IsGalois.card_aut_eq_finrank])
  refine ⟨IntermediateField.fixedField N, ?_, ?_, IsGalois.of_fixedField_normal_subgroup N, ?_⟩
  · intro h
    apply htop
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_bot]
  · intro h
    apply hbot
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_top]
  · rcases hM with hM | hM
    · left
      exact IsTotallyReal.of_algebra (IntermediateField.fixedField N) M
    · apply rc_of_intermediateField_stable_under_complexConj
      intro x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      intro n hn
      obtain ⟨Φ⟩ : Nonempty (M →+* ℂ) := inferInstance
      apply Φ.injective
      have h2 := IsCMField.complexEmbedding_complexConj M (Φ.comp n.toRingHom) x
      change Φ (n (IsCMField.complexConj M x)) = (starRingEnd ℂ) (Φ (n x)) at h2
      rw [h2, hx n hn, IsCMField.complexEmbedding_complexConj]
