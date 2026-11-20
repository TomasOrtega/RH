import Mathlib

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericValue

open MvPolynomial

variable {K : Type} [Field K]

/- English proof (translation)
Set `A` to `Algebra.adjoin K (Set.range v)`. Set `g : A →ₐ[K] Ω` to `(aeval T).comp hv.1.aevalEquiv.symm.toAlgHom`. Establish `hg : Function.Injective g` using `fun p q h => hv.1.aevalEquiv.symm.injective (algebraicIndependent_iff_injective_aeval.1 hT h)`. Use `letI : Algebra A Ω := g.toRingHom.toAlgebra`. Use `haveI : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm`.

Use `haveI : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).2 hg`. Use `haveI := hv.isAlgebraic`. Set `j : E →ₐ[A] Ω` to `IsAlgClosed.lift`. Use `⟨j.restrictScalars K, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `j.commutes (hv.1.aevalEquiv (X i))`.

Establish `e : algebraMap A E (hv.1.aevalEquiv (X i)) = v i`. Rewrite using `[hv.1.algebraMap_aevalEquiv, aeval_X]`. Rewrite `h` using `[e]`. Use `h.trans ?_` and prove the remaining obligations. Use `show aeval T (hv.1.aevalEquiv.symm (hv.1.aevalEquiv (X i))) = T i`.

Rewrite using `[AlgEquiv.symm_apply_apply, aeval_X]`.
-/
theorem exists_algHom_of_isTranscendenceBasis {E Ω ι : Type} [Field E] [Algebra K E] [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {v : ι → E} (hv : IsTranscendenceBasis K v) {T : ι → Ω} (hT : AlgebraicIndependent K T) :
    ∃ j : E →ₐ[K] Ω, ∀ i, j (v i) = T i := by
  let A := Algebra.adjoin K (Set.range v)
  let g : A →ₐ[K] Ω := (aeval T).comp hv.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := fun p q h =>
    hv.1.aevalEquiv.symm.injective (algebraicIndependent_iff_injective_aeval.1 hT h)
  letI : Algebra A Ω := g.toRingHom.toAlgebra
  haveI : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  haveI : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).2 hg
  haveI := hv.isAlgebraic
  let j : E →ₐ[A] Ω := IsAlgClosed.lift
  refine ⟨j.restrictScalars K, fun i => ?_⟩
  have h := j.commutes (hv.1.aevalEquiv (X i))
  have e : algebraMap A E (hv.1.aevalEquiv (X i)) = v i := by
    rw [hv.1.algebraMap_aevalEquiv, aeval_X]
  rw [e] at h
  refine h.trans ?_
  show aeval T (hv.1.aevalEquiv.symm (hv.1.aevalEquiv (X i))) = T i
  rw [AlgEquiv.symm_apply_apply, aeval_X]

/- English proof (translation)
Establish `h₁ : AlgebraicIndependent K fun i : ι => (X i + 1 : MvPolynomial ι K)`. Use `AlgebraicIndependent.of_comp (aeval fun i : ι => (X i - 1 : MvPolynomial ι K)) ?_` and prove the remaining obligations. Use `algebraicIndependent_X ι K using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Use `h₁.map' (algebraicIndependent_iff_injective_aeval.1 hv) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem algebraicIndependent_add_one {E ι : Type} [CommRing E] [Algebra K E] {v : ι → E}
    (hv : AlgebraicIndependent K v) : AlgebraicIndependent K fun i => v i + 1 := by
  have h₁ : AlgebraicIndependent K fun i : ι => (X i + 1 : MvPolynomial ι K) := by
    refine AlgebraicIndependent.of_comp (aeval fun i : ι => (X i - 1 : MvPolynomial ι K)) ?_
    convert algebraicIndependent_X ι K using 1
    funext i
    simp
  convert h₁.map' (algebraicIndependent_iff_injective_aeval.1 hv) using 1
  funext i
  simp

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `ht : Transcendental K a` using `fun hal => ha <| by`. Use `minpoly.mem_range_of_degree_eq_one K a (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hal.isIntegral))` as an intermediate fact. Conclude with `this`. Establish `hi : AlgebraicIndepOn K id ({a} : Set Ω)`.

Unfold `AlgebraicIndepOn`. Conclude with `(algebraicIndependent_singleton_iff (⟨a, rfl⟩ : ({a} : Set Ω))).2 ht`. Take `⟨t, hst, hb⟩` from `exists_isTranscendenceBasis_superset hi`. Take `⟨j, hj⟩` from `exists_algHom_of_isTranscendenceBasis hb (algebraicIndependent_add_one hb.1)`. Use `(h j).symm.trans (hj ⟨a, hst rfl⟩)` as an intermediate fact.

Simplify using `at this`.
-/
theorem mem_range_of_fixed [IsAlgClosed K] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (a : Ω)
    (h : ∀ j : Ω →ₐ[K] Ω, j a = a) : a ∈ Set.range (algebraMap K Ω) := by
  by_contra ha
  have ht : Transcendental K a := fun hal => ha <| by
    have := minpoly.mem_range_of_degree_eq_one K a
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hal.isIntegral))
    exact this
  have hi : AlgebraicIndepOn K id ({a} : Set Ω) := by
    unfold AlgebraicIndepOn
    exact (algebraicIndependent_singleton_iff (⟨a, rfl⟩ : ({a} : Set Ω))).2 ht
  obtain ⟨t, hst, hb⟩ := exists_isTranscendenceBasis_superset hi
  obtain ⟨j, hj⟩ := exists_algHom_of_isTranscendenceBasis hb (algebraicIndependent_add_one hb.1)
  have := (h j).symm.trans (hj ⟨a, hst rfl⟩)
  simp at this

abbrev Gen (F I : Type) [Field F] : Type := AlgebraicClosure (FractionRing (MvPolynomial I F))

def genX (F I : Type) [Field F] : I → Gen F I := fun i => algebraMap (MvPolynomial I F) _ (X i)

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic (MvPolynomial I F) (FractionRing (MvPolynomial I F)) := IsLocalization.isAlgebraic _ (nonZeroDivisors _)`. Use `haveI : Algebra.IsAlgebraic (MvPolynomial I F) (Gen F I) := Algebra.IsAlgebraic.trans _ (FractionRing (MvPolynomial I F)) _`. Use `haveI : FaithfulSMul (MvPolynomial I F) (Gen F I) := (faithfulSMul_iff_algebraMap_injective _ _).2 <| by`. Rewrite using `[IsScalarTower.algebraMap_eq _ (FractionRing (MvPolynomial I F))]`. Conclude with `(algebraMap (FractionRing (MvPolynomial I F)) (Gen F I)).injective.comp (IsFractionRing.injective _ _)`.

Conclude with `(IsTranscendenceBasis.mvPolynomial I F).algebraMap_comp`.
-/
theorem isTranscendenceBasis_genX (F I : Type) [Field F] : IsTranscendenceBasis F (genX F I) := by
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (FractionRing (MvPolynomial I F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (Gen F I) :=
    Algebra.IsAlgebraic.trans _ (FractionRing (MvPolynomial I F)) _
  haveI : FaithfulSMul (MvPolynomial I F) (Gen F I) := (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq _ (FractionRing (MvPolynomial I F))]
    exact (algebraMap (FractionRing (MvPolynomial I F)) (Gen F I)).injective.comp (IsFractionRing.injective _ _)
  exact (IsTranscendenceBasis.mvPolynomial I F).algebraMap_comp

/- English proof (translation)
Set `Ω` to `Gen F I`. Set `P : I → Polynomial Ω` to `fun i => Polynomial.C (algebraMap F Ω (T i)) + Polynomial.C (genX F I i - algebraMap F Ω (T i)) * Polynomial.X`. Establish `hX : AlgebraicIndependent K (genX F I)` using `(isTranscendenceBasis_genX F I).1.restrictScalars (algebraMap K F).injective`. Establish `hP : AlgebraicIndependent K P`. Use `AlgebraicIndependent.of_comp ((Polynomial.aeval (1 : Ω)).restrictScalars K) ?_` and prove the remaining obligations.

Use `hX using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[P]`. Set `c : Polynomial Ω →ₐ[K] PowerSeries Ω` to `(Polynomial.coeToPowerSeries.algHom Ω).restrictScalars K`. Establish `hc : Function.Injective c`.

Introduce `p q h`. Apply `Polynomial.coe_injective Ω` to reduce the goal to its premises. Simplify `h` using `[c]`. Set `r : PowerSeries Ω →ₐ[K] Ω` to `{ PowerSeries.constantCoeff (R := Ω) with commutes' := fun a => by simp [PowerSeries.algebraMap_apply] }`. Use `⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, inferInstance, Ω, inferInstance, inferInstance, inferInstance, r, IsScalarTower.toAlgHom K F Ω, c ∘ P, ?_, hP.map' hc, ?_⟩` and prove the remaining obligations.

Conclude with `PowerSeries.ker_coeff_eq_max_ideal`. Use extensionality with `i`. Simplify using `[r, c, P]`.
-/
theorem exists_generization {F I : Type} [Field F] [Algebra K F] (T : I → F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra K O)
      (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra K Ω) (r : O →ₐ[K] Ω) (e : F →ₐ[K] Ω) (S : I → O),
      RingHom.ker r = IsLocalRing.maximalIdeal O ∧ AlgebraicIndependent K S ∧ r ∘ S = e ∘ T := by
  let Ω := Gen F I
  let P : I → Polynomial Ω := fun i => Polynomial.C (algebraMap F Ω (T i)) +
    Polynomial.C (genX F I i - algebraMap F Ω (T i)) * Polynomial.X
  have hX : AlgebraicIndependent K (genX F I) :=
    (isTranscendenceBasis_genX F I).1.restrictScalars (algebraMap K F).injective
  have hP : AlgebraicIndependent K P := by
    refine AlgebraicIndependent.of_comp ((Polynomial.aeval (1 : Ω)).restrictScalars K) ?_
    convert hX using 1
    ext i
    simp [P]
  let c : Polynomial Ω →ₐ[K] PowerSeries Ω := (Polynomial.coeToPowerSeries.algHom Ω).restrictScalars K
  have hc : Function.Injective c := by
    intro p q h
    apply Polynomial.coe_injective Ω
    simpa [c] using h
  let r : PowerSeries Ω →ₐ[K] Ω :=
    { PowerSeries.constantCoeff (R := Ω) with commutes' := fun a => by simp [PowerSeries.algebraMap_apply] }
  refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, inferInstance, Ω, inferInstance, inferInstance,
    inferInstance, r, IsScalarTower.toAlgHom K F Ω, c ∘ P, ?_, hP.map' hc, ?_⟩
  · exact PowerSeries.ker_coeff_eq_max_ideal
  · ext i
    simp [r, c, P]

/- English proof (translation)
Establish `hA : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω), AlgebraicIndependent K T → AlgebraicIndependent K T' → V Ω T a → V Ω T' a' → a = a'`. Introduce `Ω _ _ _ T T' a a' hT hT' h h'`. Set `j` to `IsScalarTower.toAlgHom K Ω (Gen Ω I)`. Establish `hX` using `(isTranscendenceBasis_genX Ω I).1`. Take `⟨b, hb⟩` from `ex (Gen Ω I) _ (hX.restrictScalars (algebraMap K Ω).injective)`.

Establish `key : ∀ (S : I → Ω) (c : Ω), AlgebraicIndependent K S → V Ω S c → b = j c` using `fun S c hS hc => gg (Gen Ω I) _ _ _ _ (hS.sumElim_comp hX) hb (bc Ω _ j S c hc)`. Conclude with `j.toRingHom.injective ((key T a hT h).symm.trans (key T' a' hT' h'))`. Establish `hB` using `isTranscendenceBasis_genX K I`. Take `⟨a₁, ha₁⟩` from `ex (Gen K I) _ hB.1`. Take `⟨κ, rfl⟩` from `mem_range_of_fixed (K := K) a₁ fun j => hA _ _ _ _ _ (hB.1.map' j.toRingHom.injective) hB.1 (bc _ _ j _ _ ha₁) ha₁`.

Use `⟨κ, fun F _ _ T a h => ?_, ha₁⟩` and prove the remaining obligations. Take `⟨O, _, _, _, _, Ω, _, _, _, r, e, S, hr, hS, hT⟩` from `exists_generization (K := K) T`. Establish `h₁` using `bc _ _ e T a h`. Rewrite `h₁` using `[← hT]`. Take `⟨O', _, _, _, _, j, r', u, hj, hr', hu⟩` from `lift O Ω r S _ hr h₁`.

Establish `h₂` using `bc _ _ r' _ _ hu`. Rewrite `h₂` using `[← Function.comp_assoc, ← AlgHom.coe_comp, hr']`. Establish `h₃` using `uniq _ _ _ _ h₁ h₂`. Set `Ω'` to `AlgebraicClosure (FractionRing O')`. Set `i` to `IsScalarTower.toAlgHom K O' Ω'`.

Establish `hi : Function.Injective i` using `by show Function.Injective (algebraMap O' Ω')`. Rewrite using `[IsScalarTower.algebraMap_eq _ (FractionRing O')]`. Conclude with `(algebraMap (FractionRing O') Ω').injective.comp (IsFractionRing.injective _ _)`. Take `⟨m, hm⟩` from `exists_algHom_of_isTranscendenceBasis hB ((hS.map' hj).map' hi)`. Establish `h₄` using `bc _ _ m _ _ ha₁`.

Rewrite `h₄` using `[show m ∘ genX K I = i ∘ j ∘ S from funext hm]`. Establish `h₅ : u = algebraMap K O' κ` using `hi ((uniq _ _ _ _ (bc _ _ i _ _ hu) h₄).trans (by simp))`. Apply `e.toRingHom.injective` to reduce the goal to its premises. Simplify `h₃` using `[h₅]`.
-/
theorem exists_value [IsAlgClosed K] {I : Type}
    (V : ∀ (R : Type) [CommRing R] [Algebra K R], (I → R) → R → Prop)
    (bc : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (T : I → R) (a : R), V R T a → V R' (j ∘ T) (j a))
    (uniq : ∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a a' : F), V F T a → V F T a' → a = a')
    (ex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T : I → Ω), AlgebraicIndependent K T → ∃ a, V Ω T a)
    (gg : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K (Sum.elim T T') → V Ω T a → V Ω T' a' → a = a')
    (lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω) (T : I → O) (a : Ω),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V Ω (r ∘ T) a →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
        (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧ V O' (j ∘ T) u) :
    ∃ κ : K, (∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a : F), V F T a → a = algebraMap K F κ) ∧
      V (Gen K I) (genX K I) (algebraMap K _ κ) := by
  have hA : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K T → AlgebraicIndependent K T' → V Ω T a → V Ω T' a' → a = a' := by
    intro Ω _ _ _ T T' a a' hT hT' h h'
    let j := IsScalarTower.toAlgHom K Ω (Gen Ω I)
    have hX := (isTranscendenceBasis_genX Ω I).1
    obtain ⟨b, hb⟩ := ex (Gen Ω I) _ (hX.restrictScalars (algebraMap K Ω).injective)
    have key : ∀ (S : I → Ω) (c : Ω), AlgebraicIndependent K S → V Ω S c → b = j c := fun S c hS hc =>
      gg (Gen Ω I) _ _ _ _ (hS.sumElim_comp hX) hb (bc Ω _ j S c hc)
    exact j.toRingHom.injective ((key T a hT h).symm.trans (key T' a' hT' h'))
  have hB := isTranscendenceBasis_genX K I
  obtain ⟨a₁, ha₁⟩ := ex (Gen K I) _ hB.1
  obtain ⟨κ, rfl⟩ := mem_range_of_fixed (K := K) a₁ fun j =>
    hA _ _ _ _ _ (hB.1.map' j.toRingHom.injective) hB.1 (bc _ _ j _ _ ha₁) ha₁
  refine ⟨κ, fun F _ _ T a h => ?_, ha₁⟩
  obtain ⟨O, _, _, _, _, Ω, _, _, _, r, e, S, hr, hS, hT⟩ := exists_generization (K := K) T
  have h₁ := bc _ _ e T a h
  rw [← hT] at h₁
  obtain ⟨O', _, _, _, _, j, r', u, hj, hr', hu⟩ := lift O Ω r S _ hr h₁
  have h₂ := bc _ _ r' _ _ hu
  rw [← Function.comp_assoc, ← AlgHom.coe_comp, hr'] at h₂
  have h₃ := uniq _ _ _ _ h₁ h₂
  let Ω' := AlgebraicClosure (FractionRing O')
  let i := IsScalarTower.toAlgHom K O' Ω'
  have hi : Function.Injective i := by
    show Function.Injective (algebraMap O' Ω')
    rw [IsScalarTower.algebraMap_eq _ (FractionRing O')]
    exact (algebraMap (FractionRing O') Ω').injective.comp (IsFractionRing.injective _ _)
  obtain ⟨m, hm⟩ := exists_algHom_of_isTranscendenceBasis hB ((hS.map' hj).map' hi)
  have h₄ := bc _ _ m _ _ ha₁
  rw [show m ∘ genX K I = i ∘ j ∘ S from funext hm] at h₄
  have h₅ : u = algebraMap K O' κ := hi ((uniq _ _ _ _ (bc _ _ i _ _ hu) h₄).trans (by simp))
  apply e.toRingHom.injective
  simpa [h₅] using h₃

end GlobalTheory.GenericValue
