import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Kum UpperTheory.V.B3

open CompanionTheory.PlaceDict in
/- English proof (translation)
Establish `: Algebra.IsIntegral (𝓞 L) (𝓞 Ω)` using `⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩`. Use `w.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hw⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]`. Conclude with `bot_le)`.

Take `⟨A, rfl⟩` from `exists_cen Q`. Conclude with `⟨A, hQ, hw⟩`.
-/
private theorem exists_over {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [Algebra.IsAlgebraic E Ω] (L : IntermediateField E Ω) [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ A : ValuationSubring Ω, (cen A).IsMaximal ∧ (cen A).under (𝓞 L) = w.asIdeal := by
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have := w.isMaximal
  obtain ⟨Q, hQ, hw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]
    exact bot_le)
  obtain ⟨A, rfl⟩ := exists_cen Q
  exact ⟨A, hQ, hw⟩

open CompanionTheory.PlaceDict in
/- English proof (translation)
Take `⟨A, hm, hw⟩` from `exists_over L w`. Take `⟨φ, h1, h2⟩` from `lift L (cen A) τ (RingHom.id _) fun x => by`. Rewrite using `[RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]`. Conclude with `(hw.ge (hτ x) :)`. Take `⟨h3, h4⟩` from `of_cong A φ one_ne_zero fun b => by`.

Rewrite using `[pow_one]`. Conclude with `Ideal.Quotient.eq.1 (h2 b)`. Conclude with `⟨A, φ, h1, h3, fun x hx => by`. Simplify using `using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩`.
-/
private theorem lift_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[E] L)) :
    ∃ (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := E) A := by
  obtain ⟨A, hm, hw⟩ := exists_over L w
  obtain ⟨φ, h1, h2⟩ := lift L (cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact (hw.ge (hτ x) :)
  obtain ⟨h3, h4⟩ := of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  exact ⟨A, φ, h1, h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩

open scoped nonZeroDivisors Pointwise in
/- English proof (translation)
Use `set F : IntermediateField ℚ M := IntermediateField.fixedField S with hF`. Establish `h1 : Module.finrank ℚ F = 1`. Assume the negation of the conclusion as `hne`. Take `⟨Q, hQ, hram⟩` from `NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hne`. Apply `hram` to reduce the goal to its premises.

Take `⟨⟨P, hP1, hP2⟩⟩` from `(inferInstance : Nonempty (Q.primesOver (𝓞 M)))`. Establish `hPmax : P.IsMaximal` using `Ideal.IsMaximal.of_liesOver_isMaximal P Q`. Establish `hG : IsGaloisGroup S F M` using `IsGaloisGroup.subgroup (M ≃ₐ[ℚ] M) ℚ M S`. Establish `hG' : IsGaloisGroup S (𝓞 F) (𝓞 M)` using `IsGaloisGroup.of_isFractionRing S _ _ F M`. Establish `hG0 : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ M`.

Establish `e1` using `Ideal.card_inertia_eq_ramificationIdxIn (G := S) Q P`. Establish `e2` using `Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) (P.under ℤ) P`. Rewrite `e1` using `[Ideal.ramificationIdxIn_eq_ramificationIdx Q P S]`. Rewrite `e2` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[ℚ] M)]`. Establish `e3 : Nat.card (P.inertia S) = Nat.card (P.inertia (M ≃ₐ[ℚ] M))`.

Rewrite using `[← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h P hPmax)).toEquiv]`. Both sides reduce to the same expression. Establish `e4 : P.ramificationIdx ℤ = Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F)` using `Ideal.ramificationIdx_tower Q P`. Establish `e5 : 0 < P.ramificationIdx (𝓞 F)` using `P.ramificationIdx_pos _`. Rewrite using `[← Ideal.ramificationIdx_eq_one_iff]`.

Establish `e6 : Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) = 1 * P.ramificationIdx (𝓞 F)`. Rewrite using `[← e4, ← e2, ← e3, e1, one_mul]`. Conclude with `Nat.eq_of_mul_eq_mul_right e5 e6`. Establish `h2 : F = ⊥` using `IntermediateField.finrank_eq_one_iff.mp h1`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField S, ← hF, h2, IntermediateField.fixingSubgroup_bot]`.
-/
private theorem finite_case (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    (S : Subgroup (M ≃ₐ[ℚ] M))
    (h : ∀ P : Ideal (𝓞 M), P.IsMaximal → P.inertia (M ≃ₐ[ℚ] M) ≤ S) : S = ⊤ := by
  set F : IntermediateField ℚ M := IntermediateField.fixedField S with hF
  have h1 : Module.finrank ℚ F = 1 := by
    by_contra hne
    obtain ⟨Q, hQ, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hne
    apply hram
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 M)))
    have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P Q
    have hG : IsGaloisGroup S F M := IsGaloisGroup.subgroup (M ≃ₐ[ℚ] M) ℚ M S
    have hG' : IsGaloisGroup S (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing S _ _ F M
    have hG0 : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
    have e1 := Ideal.card_inertia_eq_ramificationIdxIn (G := S) Q P
    have e2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) (P.under ℤ) P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P S] at e1
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[ℚ] M)] at e2
    have e3 : Nat.card (P.inertia S) = Nat.card (P.inertia (M ≃ₐ[ℚ] M)) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h P hPmax)).toEquiv]
      rfl
    have e4 : P.ramificationIdx ℤ = Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
      Ideal.ramificationIdx_tower Q P
    have e5 : 0 < P.ramificationIdx (𝓞 F) := P.ramificationIdx_pos _
    rw [← Ideal.ramificationIdx_eq_one_iff]
    have e6 : Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) = 1 * P.ramificationIdx (𝓞 F) := by
      rw [← e4, ← e2, ← e3, e1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right e5 e6
  have h2 : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  rw [← IntermediateField.fixingSubgroup_fixedField S, ← hF, h2, IntermediateField.fixingSubgroup_bot]

open IntermediateField in
/- English proof (translation)
Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Set `Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω)` to `⟨H, H.isClosed_of_isOpen ho⟩`. Establish `hfix : (fixedField H).fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField Hc`. Generalize the expression as in `fixedField H = L at hfix`. Substitute `hfix` using the available equality.

Establish `: FiniteDimensional E L` using `(InfiniteGalois.isOpen_iff_finite _).1 ho`. Establish `: IsGalois E L` using `(InfiniteGalois.normal_iff_isGalois _).1 hn`. Establish `: NumberField L` using `NumberField.of_module_finite E _`. Establish `hb : (⊥ : Subgroup (L ≃ₐ[E] L)) = ⊤` using `hE L ⊥ fun P hP τ hτ => by`. Set `w : HeightOneSpectrum (𝓞 L)` to `⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField L)⟩`.

Take `⟨A, φ, h1, h2⟩` from `lift_ine L w τ hτ`. Rewrite using `[Subgroup.mem_bot, ← h1, ← MonoidHom.mem_ker, restrictNormalHom_ker]`. Conclude with `hI A h2`. Rewrite using `[eq_top_iff, ← restrictNormalHom_ker]`. Introduce `g _`.

Rewrite using `[MonoidHom.mem_ker, ← Subgroup.mem_bot, hb]`. Discharge the goal by the elementary cases of `trivial`.
-/
private theorem general {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ (M : Type) [Field M] [NumberField M] [Algebra E M] [IsGalois E M] (S : Subgroup (M ≃ₐ[E] M)),
      (∀ P : Ideal (𝓞 M), P.IsMaximal → P.inertia (M ≃ₐ[E] M) ≤ S) → S = ⊤)
    (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal) (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ A : ValuationSubring Ω, Ine (F := E) A ≤ H) : H = ⊤ := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hfix : (fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  generalize fixedField H = L at hfix
  subst hfix
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite _).1 ho
  have : IsGalois E L := (InfiniteGalois.normal_iff_isGalois _).1 hn
  have : NumberField L := NumberField.of_module_finite E _
  have hb : (⊥ : Subgroup (L ≃ₐ[E] L)) = ⊤ := hE L ⊥ fun P hP τ hτ => by
    let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField L)⟩
    obtain ⟨A, φ, h1, h2⟩ := lift_ine L w τ hτ
    rw [Subgroup.mem_bot, ← h1, ← MonoidHom.mem_ker, restrictNormalHom_ker]
    exact hI A h2
  rw [eq_top_iff, ← restrictNormalHom_ker]
  intro g _
  rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, hb]
  trivial

/- English proof (translation)
Introduce `Ω _ _ _ N hn ho hI`. Use `general (fun M _ _ inst hG S hS => ?_) N hn ho hI` and prove the remaining obligations. Take `rfl : inst = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Conclude with `finite_case M S hS`.
-/
theorem UpperTheory.V.B3.minkowski :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)), N.Normal → IsOpen (N : Set (G ℚ Ω)) →
    (∀ B : ValuationSubring Ω, Ine (F := ℚ) B ≤ N) → N = ⊤ := by
  intro Ω _ _ _ N hn ho hI
  refine general (fun M _ _ inst hG S hS => ?_) N hn ho hI
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact finite_case M S hS
