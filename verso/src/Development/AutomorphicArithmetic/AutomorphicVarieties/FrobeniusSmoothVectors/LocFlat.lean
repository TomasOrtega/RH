import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocCpl
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightSpaceFinite

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `hk : (maximalIdeal R).comap f = RingHom.ker ((res O R).toRingHom.comp f)`. Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← res_eq_zero_iff O R]`. Both sides reduce to the same expression. Establish `hp : ((maximalIdeal R).comap f).IsPrime` using `Ideal.IsPrime.comap _`.

Rewrite `hp`, the goal using `[hk]`. Use `haveI : Finite (D ⧸ RingHom.ker ((res O R).toRingHom.comp f)) := Finite.of_injective _ (RingHom.kerLift_injective _)`. Conclude with `Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)`.
-/
private theorem max_of_fin {O D R : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (f : D →+* R) : ((maximalIdeal R).comap f).IsMaximal := by
  have hk : (maximalIdeal R).comap f = RingHom.ker ((res O R).toRingHom.comp f) := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← res_eq_zero_iff O R]
    rfl
  have hp : ((maximalIdeal R).comap f).IsPrime := Ideal.IsPrime.comap _
  rw [hk] at hp ⊢
  haveI : Finite (D ⧸ RingHom.ker ((res O R).toRingHom.comp f)) :=
    Finite.of_injective _ (RingHom.kerLift_injective _)
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O O')`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Assume the negation of the conclusion as `hne`. Establish `hp : (RingHom.ker (algebraMap O O')).IsPrime` using `RingHom.ker_isPrime _`. Establish `hm` using `eq_maximalIdeal (hp.isMaximal hne)`.

Use `IsDiscreteValuationRing.not_a_field O' ?_` and prove the remaining obligations. Rewrite using `[← h, ← hm, Ideal.map_eq_bot_iff_le_ker]`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `z ⟨⟨a, ha⟩, hz⟩`. Establish `h1 : algebraMap O O' a * z = 0` using `by rw [← Algebra.smul_def]; exact hz`.

Use `(mul_eq_zero.1 h1).resolve_left fun h2 => nonZeroDivisors.ne_zero ha (hinj ?_)` and prove the remaining obligations. Rewrite using `[h2, map_zero]`.
-/
private theorem flat_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (h : (maximalIdeal O).map (algebraMap O O') = maximalIdeal O') : Module.Flat O O' := by
  have hinj : Function.Injective (algebraMap O O') := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    have hp : (RingHom.ker (algebraMap O O')).IsPrime := RingHom.ker_isPrime _
    have hm := eq_maximalIdeal (hp.isMaximal hne)
    refine IsDiscreteValuationRing.not_a_field O' ?_
    rw [← h, ← hm, Ideal.map_eq_bot_iff_le_ker]
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro z ⟨⟨a, ha⟩, hz⟩
  have h1 : algebraMap O O' a * z = 0 := by rw [← Algebra.smul_def]; exact hz
  refine (mul_eq_zero.1 h1).resolve_left fun h2 => nonZeroDivisors.ne_zero ha (hinj ?_)
  rw [h2, map_zero]

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S x L`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hA : IsNoetherianRing S.A` using `(gr_A hF hn S).2.2.2.2.2.1`. Establish `hD : IsNoetherianRing (TensorProduct O L.O' S.A)`. Establish `h1 : IsNoetherianRing (TensorProduct O S.A L.O')` using `Algebra.FiniteType.isNoetherianRing S.A _`.

Conclude with `isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv`. Set `ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) L.ι fun _ _ => Commute.all _ _`. Establish `hι : ∀ a, ι' (1 ⊗ₜ a) = L.ι a` using `fun a => by simp [ι']`. Establish `hc` using `loc_cpl hF hn S x L ι' hι`. Use `haveI := max_of_fin (O := L.O') ι'.toRingHom`.

Establish `h1 : ι'.toRingHom.Flat` using `(@UpperTheory.V.CA.c3a _ _ _ _ _ ι'.toRingHom.toAlgebra _ _ _ hc).1`. Use `haveI : Module.Flat O L.O' := flat_dvr L.unr`. Establish `h2 : (Algebra.TensorProduct.includeRight (R` using `O) (A := L.O') (B := S.A)).toRingHom.Flat := by`. Establish `h3 : (algebraMap S.A (TensorProduct O S.A L.O')).Flat` using `RingHom.flat_algebraMap_iff.2 inferInstance`. Establish `h4` using `h3.comp (RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv.toRingHom) (Algebra.TensorProduct.comm O S.A L.O').bijective)`.

Conclude with `h4`. Establish `e : (L.ι : S.A →+* L.R) = ι'.toRingHom.comp (Algebra.TensorProduct.includeRight (R` using `O) (A := L.O') (B := S.A)).toRingHom := RingHom.ext fun a => (hι a).symm`. Rewrite using `[e]`. Conclude with `h2.comp h1`. Rewrite using `[← L.lies]`.

Conclude with `max_of_fin (O := L.O') _`. Take `⟨h, hm⟩` from `co_B hF hn S`. Establish `h1` using `max_of_fin (O := L.O') ((L.ι : S.A →+* L.R).comp (S.inc : S.B →+* S.A))`. Rewrite `h1` using `[← Ideal.comap_comap, L.lies]`. Rewrite using `[← hm]`.

Conclude with `(eq_maximalIdeal h1).ge`.
-/
theorem UpperTheory.V.Fr.loc_flat :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (L.ι : S.A →+* L.R).Flat ∧ x.IsMaximal ∧ S.mB ≤ S.π x := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  refine ⟨?_, ?_, ?_⟩
  · have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
    have hD : IsNoetherianRing (TensorProduct O L.O' S.A) := by
      have h1 : IsNoetherianRing (TensorProduct O S.A L.O') :=
        Algebra.FiniteType.isNoetherianRing S.A _
      exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv
    let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) L.ι fun _ _ => Commute.all _ _
    have hι : ∀ a, ι' (1 ⊗ₜ a) = L.ι a := fun a => by simp [ι']
    have hc := loc_cpl hF hn S x L ι' hι
    haveI := max_of_fin (O := L.O') ι'.toRingHom
    have h1 : ι'.toRingHom.Flat := (@UpperTheory.V.CA.c3a _ _ _ _ _ ι'.toRingHom.toAlgebra _ _ _ hc).1
    haveI : Module.Flat O L.O' := flat_dvr L.unr
    have h2 : (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom.Flat := by
      have h3 : (algebraMap S.A (TensorProduct O S.A L.O')).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
      have h4 := h3.comp (RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv.toRingHom)
        (Algebra.TensorProduct.comm O S.A L.O').bijective)
      exact h4
    have e : (L.ι : S.A →+* L.R) = ι'.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom :=
      RingHom.ext fun a => (hι a).symm
    rw [e]
    exact h2.comp h1
  · rw [← L.lies]
    exact max_of_fin (O := L.O') _
  · obtain ⟨h, hm⟩ := co_B hF hn S
    have h1 := max_of_fin (O := L.O') ((L.ι : S.A →+* L.R).comp (S.inc : S.B →+* S.A))
    rw [← Ideal.comap_comap, L.lies] at h1
    rw [← hm]
    exact (eq_maximalIdeal h1).ge
