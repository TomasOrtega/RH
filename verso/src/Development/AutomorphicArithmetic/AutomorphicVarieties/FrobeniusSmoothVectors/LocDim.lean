import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocCpl
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KTypesBoundedFinite

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Substitute `hη` using the available equality. Name the introduced variables `iBD iT iI hp`. Establish `hI : iBD = ((algebraMap A D).comp (algebraMap B A)).toAlgebra`. Apply `Algebra.algebra_ext` to reduce the goal to its premises. Introduce `r`.

Conclude with `IsScalarTower.algebraMap_apply B A D r`. Substitute `hI` using the available equality. Use `⟨(Ideal.comap_comap _ _).symm, ?_⟩` and prove the remaining obligations. Use `letI iBD' : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra`. Use `letI : Algebra (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (D ⧸ p) := (Ideal.quotientAlgebra : Algebra (B ⧸ Ideal.comap (algebraMap B D) p) (D ⧸ p))`.

Use `haveI : IsScalarTower (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) := by`. Apply `IsScalarTower.of_algebraMap_eq` to reduce the goal to its premises. Introduce `x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Both sides reduce to the same expression.

Use `haveI : FaithfulSMul (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (A ⧸ Ideal.comap (algebraMap A D) p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective`. Use `haveI : FaithfulSMul (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective`. Use `haveI : Algebra.IsAlgebraic (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) := Algebra.IsIntegral.isAlgebraic`. Establish `key` using `trdeg_add_eq (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (A ⧸ Ideal.comap (algebraMap A D) p) (A := D ⧸ p)`. Establish `h0 : Algebra.trdeg (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) = 0` using `trdeg_eq_zero`.

Rewrite `key` using `[h0, add_zero]`. Conclude with `key.symm`.
-/
private theorem td_fin {B A D : Type} [CommRing B] [CommRing A] [CommRing D] [Algebra B A] [Algebra A D]
    [Algebra B D] [IsScalarTower B A D] [Algebra.IsIntegral A D] (p : Ideal D) [p.IsPrime] (η : Ideal A)
    (hη : p.comap (algebraMap A D) = η) :
    p.comap (algebraMap B D) = η.comap (algebraMap B A) ∧
    Algebra.trdeg (B ⧸ p.comap (algebraMap B D)) (D ⧸ p) = Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  subst hη
  rename_i iBD iT iI hp
  have hI : iBD = ((algebraMap A D).comp (algebraMap B A)).toAlgebra := by
    apply Algebra.algebra_ext
    intro r
    exact IsScalarTower.algebraMap_apply B A D r
  subst hI
  refine ⟨(Ideal.comap_comap _ _).symm, ?_⟩
  letI iBD' : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra
  letI : Algebra (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (D ⧸ p) :=
    (Ideal.quotientAlgebra : Algebra (B ⧸ Ideal.comap (algebraMap B D) p) (D ⧸ p))
  haveI : IsScalarTower (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
      (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  haveI : FaithfulSMul (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
      (A ⧸ Ideal.comap (algebraMap A D) p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : FaithfulSMul (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : Algebra.IsAlgebraic (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) :=
    Algebra.IsIntegral.isAlgebraic
  have key := trdeg_add_eq (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
    (A ⧸ Ideal.comap (algebraMap A D) p) (A := D ⧸ p)
  have h0 : Algebra.trdeg (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at key
  exact key.symm

/- English proof (translation)
Use `haveI : IsNoetherianRing B := hB.noeth`. Use `haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing B A`. Use `haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D`. Use `haveI : IsNoetherianRing R := hR.noeth`. Use `letI : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra`.

Use `haveI : IsScalarTower B A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : Algebra.FiniteType B D := Algebra.FiniteType.trans (S := A) inferInstance inferInstance`. Use `haveI := hx`. Establish `hyc : Ideal.comap (algebraMap D R) (maximalIdeal R) = y`. Simplify using `using hR.comap_pow 1`.

Use `haveI hyP : y.IsPrime := by`. Rewrite using `[← hyc]`. Use `infer_instance`. Use `haveI hyM : y.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) y (by rw [hy]; exact hx)`. Establish `hyB : Ideal.comap (algebraMap B D) y = maximalIdeal B`.

Rewrite using `[IsScalarTower.algebraMap_eq B A D, ← Ideal.comap_comap, hy, hxB]`. Prove the components needed by the constructor for the conclusion. Introduce `P hP η hη t ht haveI := hP haveI hpDP : (P.comap (algebraMap D R)).IsPrime := Ideal.comap_isPrime _ _`. Establish `hpDy : P.comap (algebraMap D R) ≤ y`. Rewrite using `[← hyc]`.

Conclude with `Ideal.comap_mono (le_maximalIdeal hP.ne_top)`. Take `⟨t', ht'tr, ht'dim⟩` from `UpperTheory.V.CA.c3b O y hB hyB (P.comap (algebraMap D R)) hpDy`. Establish `htd` using `td_fin (B := B) (P.comap (algebraMap D R)) η hη`. Establish `h1` using `(UpperTheory.V.CA.c3c y hR).2 (P.comap (algebraMap D R)) P le_rfl`. Rewrite `h1` using `[ht'dim, htd.1]`.

Rewrite `ht'tr` using `[htd.2]`. Establish `hc : (t' : Cardinal) ≤ t` using `ht'tr ▸ ht`. Establish `htt : t' ≤ t` using `by exact_mod_cast hc`. Establish `hcast : ((t' : ℕ∞) : WithBot ℕ∞) ≤ ((t : ℕ∞) : WithBot ℕ∞)`. Conclude with `htt` after adjusting the coercions.

Conclude with `h1.trans (add_le_add le_rfl hcast)`. Introduce `η hη hηx t ht haveI := hη haveI : y.LiesOver x := ⟨hy.symm⟩`. Take `⟨pD, hpDy, hpD, hlo⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := η) (q := x) y hηx`. Establish `hηD : pD.comap (algebraMap A D) = η` using `(Ideal.over_def pD η).symm`. Establish `hmap : Ideal.map (algebraMap D R) pD ≤ maximalIdeal R`.

Rewrite using `[Ideal.map_le_iff_le_comap, hyc]`. Conclude with `hpDy`. Take `⟨q, hq, -⟩` from `Ideal.exists_minimalPrimes_le hmap`. Take `⟨hqdim, hqc⟩` from `UpperTheory.V.CA.c3d O y hB hyB hR pD hpDy q hq`. Take `⟨t', ht'tr, ht'dim⟩` from `UpperTheory.V.CA.c3b O y hB hyB pD hpDy`.

Establish `htd` using `td_fin (B := B) pD η hηD`. Use `⟨q, hq.1.1, by rw [hqc, hηD], ?_⟩` and prove the remaining obligations. Rewrite using `[hqdim, ht'dim, htd.1]`. Rewrite `ht'tr` using `[htd.2, ht]`. Establish `htt : t' = t` using `by exact_mod_cast ht'tr.symm`.

Rewrite using `[htt]`.
-/
private theorem dim_gen (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {B A D R : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing A]
    [CommRing D] [Algebra B A] [Algebra A D] [Algebra.FiniteType B A] [Module.Finite A D] [Module.Flat A D]
    [CommRing R] [IsLocalRing R] [Algebra D R] (hB : UpperTheory.V.CA.IsCL O B) (x : Ideal A) (hx : x.IsMaximal)
    (hxB : x.comap (algebraMap B A) = maximalIdeal B) (y : Ideal D) (hy : y.comap (algebraMap A D) = x)
    (hR : UpperTheory.V.CA.IsCplAt y R) :
    (∀ P : Ideal R, P.IsPrime → ∀ η : Ideal A, (P.comap (algebraMap D R)).comap (algebraMap A D) = η → ∀ t : ℕ,
      Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) ≤ t →
        ringKrullDim (R ⧸ P) ≤ ringKrullDim (B ⧸ η.comap (algebraMap B A)) + t) ∧
    ∀ η : Ideal A, η.IsPrime → η ≤ x → ∀ t : ℕ, Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) = t →
      ∃ P : Ideal R, P.IsPrime ∧ (P.comap (algebraMap D R)).comap (algebraMap A D) = η ∧
        ringKrullDim (R ⧸ P) = ringKrullDim (B ⧸ η.comap (algebraMap B A)) + t := by
  haveI : IsNoetherianRing B := hB.noeth
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing B A
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  haveI : IsNoetherianRing R := hR.noeth
  letI : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra
  haveI : IsScalarTower B A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType B D := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI := hx
  have hyc : Ideal.comap (algebraMap D R) (maximalIdeal R) = y := by
    simpa using hR.comap_pow 1
  haveI hyP : y.IsPrime := by
    rw [← hyc]
    infer_instance
  haveI hyM : y.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) y (by rw [hy]; exact hx)
  have hyB : Ideal.comap (algebraMap B D) y = maximalIdeal B := by
    rw [IsScalarTower.algebraMap_eq B A D, ← Ideal.comap_comap, hy, hxB]
  constructor
  · intro P hP η hη t ht
    haveI := hP
    haveI hpDP : (P.comap (algebraMap D R)).IsPrime := Ideal.comap_isPrime _ _
    have hpDy : P.comap (algebraMap D R) ≤ y := by
      rw [← hyc]
      exact Ideal.comap_mono (le_maximalIdeal hP.ne_top)
    obtain ⟨t', ht'tr, ht'dim⟩ := UpperTheory.V.CA.c3b O y hB hyB (P.comap (algebraMap D R)) hpDy
    have htd := td_fin (B := B) (P.comap (algebraMap D R)) η hη
    have h1 := (UpperTheory.V.CA.c3c y hR).2 (P.comap (algebraMap D R)) P le_rfl
    rw [ht'dim, htd.1] at h1
    rw [htd.2] at ht'tr
    have hc : (t' : Cardinal) ≤ t := ht'tr ▸ ht
    have htt : t' ≤ t := by exact_mod_cast hc
    have hcast : ((t' : ℕ∞) : WithBot ℕ∞) ≤ ((t : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast htt
    exact h1.trans (add_le_add le_rfl hcast)
  · intro η hη hηx t ht
    haveI := hη
    haveI : y.LiesOver x := ⟨hy.symm⟩
    obtain ⟨pD, hpDy, hpD, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := η) (q := x) y hηx
    have hηD : pD.comap (algebraMap A D) = η := (Ideal.over_def pD η).symm
    have hmap : Ideal.map (algebraMap D R) pD ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap, hyc]
      exact hpDy
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hmap
    obtain ⟨hqdim, hqc⟩ := UpperTheory.V.CA.c3d O y hB hyB hR pD hpDy q hq
    obtain ⟨t', ht'tr, ht'dim⟩ := UpperTheory.V.CA.c3b O y hB hyB pD hpDy
    have htd := td_fin (B := B) pD η hηD
    refine ⟨q, hq.1.1, by rw [hqc, hηD], ?_⟩
    rw [hqdim, ht'dim, htd.1]
    rw [htd.2, ht] at ht'tr
    have htt : t' = t := by exact_mod_cast ht'tr.symm
    rw [htt]

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hOk hn S x L`. Take `⟨hco, hmB⟩` from `co_B hOk hn S`. Use `haveI := hco`. Use `haveI : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)`. Establish `hB : UpperTheory.V.CA.IsCL O S.B` using `UpperTheory.V.CA.IsCL.of_isCO O S.B`.

Take `⟨-, -, -, -, hFT, -, -⟩` from `gr_A hOk hn S`. Use `haveI := hFT`. Take `⟨-, hxM, hmx⟩` from `loc_flat hOk hn S x L`. Establish `hxB : x.comap (algebraMap S.B S.A) = maximalIdeal S.B`. Use `le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ hxM.ne_top)) ?_` and prove the remaining obligations.

Rewrite using `[hmB]`. Conclude with `hmx`. Establish `hinj : Function.Injective (algebraMap O L.O')`. Distinguish the cases in `hK : RingHom.ker (algebraMap O L.O') = ⊥`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).mpr hK`.

It suffices to derive a contradiction. Establish `hKm : (RingHom.ker (algebraMap O L.O')).IsMaximal` using `Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hK`. Establish `hKeq` using `IsLocalRing.eq_maximalIdeal hKm`. Establish `hmap : Ideal.map (algebraMap O L.O') (maximalIdeal O) = ⊥` using `(Ideal.map_eq_bot_iff_le_ker _).mpr hKeq.ge`. Rewrite `hmap` using `[L.unr]`.

Conclude with `IsDiscreteValuationRing.not_a_field L.O' hmap`. Establish `htor : Submodule.torsion O L.O' = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Take `⟨⟨r, hr⟩, hrz⟩` from `(Submodule.mem_torsion_iff z).mp hz`.

Rewrite using `[Submodule.mem_bot]`. Establish `hr0 : algebraMap O L.O' r ≠ 0`. Introduce `h`. Apply `nonZeroDivisors.ne_zero hr` to reduce the goal to its premises. Conclude with `hinj (by rw [h, map_zero])`.

Express the relevant statement in the definitionally equal form `r • z = 0 at hrz`. Rewrite `hrz` using `[Algebra.smul_def]`. Conclude with `(mul_eq_zero.mp hrz).resolve_left hr0`. Use `haveI : Module.Flat O L.O' := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htor`. Use `letI : Algebra S.A (TensorProduct O L.O' S.A) := Algebra.TensorProduct.rightAlgebra`.

Set `e : (TensorProduct O S.A L.O') ≃ₐ[S.A] (TensorProduct O L.O' S.A)` to `AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv) (fun a => by`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`. Use the proof step `rfl)`. Use `haveI : Module.Finite S.A (TensorProduct O L.O' S.A) := Module.Finite.equiv e.toLinearEquiv`. Use `haveI : Module.Flat S.A (TensorProduct O L.O' S.A) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv`.

Set `ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R` to `Algebra.TensorProduct.lift (Algebra.ofId L.O' L.R) L.ι (fun _ _ => Commute.all _ _)`. Establish `hι' : ∀ a : S.A, ι' (TensorProduct.tmul O (1 : L.O') a) = L.ι a`. Introduce `a`. Simplify using `[ι']`. Establish `hR` using `loc_cpl hOk hn S x L ι' hι'`.

Use `letI : Algebra (TensorProduct O L.O' S.A) L.R := ι'.toRingHom.toAlgebra`. Establish `hcm : ∀ Q : Ideal L.R, (Q.comap (algebraMap (TensorProduct O L.O' S.A) L.R)).comap (algebraMap S.A (TensorProduct O L.O' S.A)) = L.im Q`. Introduce `Q`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `ι' (TensorProduct.tmul O (1 : L.O') a) ∈ Q ↔ L.ι a ∈ Q`.

Rewrite using `[hι']`. Establish `hy : (Ideal.comap ι'.toRingHom (maximalIdeal L.R)).comap (algebraMap S.A (TensorProduct O L.O' S.A)) = x`. Conclude with `(hcm (maximalIdeal L.R)).trans L.lies`. Establish `key` using `dim_gen O hB x hxM hxB _ hy hR`. Prove the components needed by the constructor for the conclusion.

Introduce `P hP t ht`. Conclude with `key.1 P hP (L.im P) (hcm P) t ht`. Introduce `η hη hηx t ht`. Take `⟨P, hP, hPη, hdim⟩` from `key.2 η hη hηx t ht`. Use `⟨P, hP, ?_, hdim⟩` and prove the remaining obligations.

Rewrite using `[← hcm P]`. Conclude with `hPη`.
-/
theorem UpperTheory.V.Fr.loc_dim :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∀ P : Ideal L.R, P.IsPrime → ∀ t : ℕ, S.td (L.im P) ≤ t → ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (S.B ⧸ L.π P) + t) ∧ ∀ η : Ideal S.A, η.IsPrime → η ≤ x → ∀ t : ℕ, S.td η = t → ∃ P : Ideal L.R, P.IsPrime ∧ L.im P = η ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ S.π η) + t := by
  intro l _ O _ _ _ _ F C₀ n hOk hn S x L
  obtain ⟨hco, hmB⟩ := co_B hOk hn S
  haveI := hco
  haveI : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  have hB : UpperTheory.V.CA.IsCL O S.B := UpperTheory.V.CA.IsCL.of_isCO O S.B
  obtain ⟨-, -, -, -, hFT, -, -⟩ := gr_A hOk hn S
  haveI := hFT
  obtain ⟨-, hxM, hmx⟩ := loc_flat hOk hn S x L
  have hxB : x.comap (algebraMap S.B S.A) = maximalIdeal S.B := by
    refine le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ hxM.ne_top)) ?_
    rw [hmB]
    exact hmx
  have hinj : Function.Injective (algebraMap O L.O') := by
    by_cases hK : RingHom.ker (algebraMap O L.O') = ⊥
    · exact (RingHom.injective_iff_ker_eq_bot _).mpr hK
    · exfalso
      have hKm : (RingHom.ker (algebraMap O L.O')).IsMaximal :=
        Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hK
      have hKeq := IsLocalRing.eq_maximalIdeal hKm
      have hmap : Ideal.map (algebraMap O L.O') (maximalIdeal O) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr hKeq.ge
      rw [L.unr] at hmap
      exact IsDiscreteValuationRing.not_a_field L.O' hmap
  have htor : Submodule.torsion O L.O' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨r, hr⟩, hrz⟩ := (Submodule.mem_torsion_iff z).mp hz
    rw [Submodule.mem_bot]
    have hr0 : algebraMap O L.O' r ≠ 0 := by
      intro h
      apply nonZeroDivisors.ne_zero hr
      exact hinj (by rw [h, map_zero])
    change r • z = 0 at hrz
    rw [Algebra.smul_def] at hrz
    exact (mul_eq_zero.mp hrz).resolve_left hr0
  haveI : Module.Flat O L.O' := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htor
  letI : Algebra S.A (TensorProduct O L.O' S.A) := Algebra.TensorProduct.rightAlgebra
  let e : (TensorProduct O S.A L.O') ≃ₐ[S.A] (TensorProduct O L.O' S.A) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv) (fun a => by
      simp [Algebra.TensorProduct.algebraMap_apply]
      rfl)
  haveI : Module.Finite S.A (TensorProduct O L.O' S.A) := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Flat S.A (TensorProduct O L.O' S.A) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
    Algebra.TensorProduct.lift (Algebra.ofId L.O' L.R) L.ι (fun _ _ => Commute.all _ _)
  have hι' : ∀ a : S.A, ι' (TensorProduct.tmul O (1 : L.O') a) = L.ι a := by
    intro a
    simp [ι']
  have hR := loc_cpl hOk hn S x L ι' hι'
  letI : Algebra (TensorProduct O L.O' S.A) L.R := ι'.toRingHom.toAlgebra
  have hcm : ∀ Q : Ideal L.R, (Q.comap (algebraMap (TensorProduct O L.O' S.A) L.R)).comap
      (algebraMap S.A (TensorProduct O L.O' S.A)) = L.im Q := by
    intro Q
    ext a
    change ι' (TensorProduct.tmul O (1 : L.O') a) ∈ Q ↔ L.ι a ∈ Q
    rw [hι']
  have hy : (Ideal.comap ι'.toRingHom (maximalIdeal L.R)).comap (algebraMap S.A (TensorProduct O L.O' S.A)) = x := by
    exact (hcm (maximalIdeal L.R)).trans L.lies
  have key := dim_gen O hB x hxM hxB _ hy hR
  constructor
  · intro P hP t ht
    exact key.1 P hP (L.im P) (hcm P) t ht
  · intro η hη hηx t ht
    obtain ⟨P, hP, hPη, hdim⟩ := key.2 η hη hηx t ht
    refine ⟨P, hP, ?_, hdim⟩
    rw [← hcm P]
    exact hPη
