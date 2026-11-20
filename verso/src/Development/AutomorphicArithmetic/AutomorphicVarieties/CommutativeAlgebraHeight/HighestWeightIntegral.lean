import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClCmquot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClQuot

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Establish `hsub : Algebra.algebraMapSubmonoid (C ⧸ p) x.primeCompl = (x.map (Ideal.Quotient.mk p)).primeCompl`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Conclude with `(Ideal.mem_quotient_iff_mem hp).mp h`. Introduce `hy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨a, fun ha => hy (Ideal.mem_map_of_mem _ ha), rfl⟩`.

Use `haveI : IsLocalization.AtPrime (Localization.AtPrime x ⧸ p.map (algebraMap C (Localization.AtPrime x))) (x.map (Ideal.Quotient.mk p)) := by`. Unfold `IsLocalization.AtPrime`. Rewrite using `[← hsub]`. Use `infer_instance`. Unfold `dimAt`.

Conclude with `IsLocalization.AtPrime.ringKrullDim_eq_height _ _`.
-/
private theorem UpperTheory.V.CA.localDimension_eq_height {C : Type} [CommRing C] (x : Ideal C) [x.IsPrime] (p : Ideal C)
    (hp : p ≤ x) [(x.map (Ideal.Quotient.mk p)).IsPrime] :
    dimAt x p = ((x.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  have hsub : Algebra.algebraMapSubmonoid (C ⧸ p) x.primeCompl = (x.map (Ideal.Quotient.mk p)).primeCompl := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      intro h
      apply hb
      exact (Ideal.mem_quotient_iff_mem hp).mp h
    · intro hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨a, fun ha => hy (Ideal.mem_map_of_mem _ ha), rfl⟩
  haveI : IsLocalization.AtPrime (Localization.AtPrime x ⧸ p.map (algebraMap C (Localization.AtPrime x)))
      (x.map (Ideal.Quotient.mk p)) := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    infer_instance
  unfold dimAt
  exact IsLocalization.AtPrime.ringKrullDim_eq_height _ _

/- English proof (translation)
Introduce `O _ _ _ _ B C _ _ _ _ _ _ x _ hCL hx p _ hp`. Use `set q := p.comap (algebraMap B C) with hq`. Establish `hqm : q ≤ maximalIdeal B`. Rewrite using `[← hx]`. Conclude with `Ideal.comap_mono hp`.

Use `haveI : IsLocalRing (B ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective`. Use `haveI : FaithfulSMul (B ⧸ q) (C ⧸ p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective`. Establish `hcm : IsCMQuot (B ⧸ q)` using `cl_cmquot O (B ⧸ q) (cl_quot O B (B ⧸ q) (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective hCL)`. Establish `hlt : Algebra.trdeg (B ⧸ q) (C ⧸ p) < Cardinal.aleph0` using `by open Algebra in exact trdeg_lt_aleph0_of_finiteType`. Use `set t := (Algebra.trdeg (B ⧸ q) (C ⧸ p)).toNat`.

Establish `ht : Algebra.trdeg (B ⧸ q) (C ⧸ p) = t` using `(Cardinal.cast_toNat_of_lt_aleph0 hlt).symm`. Establish `mapmax : ∀ {R : Type} [CommRing R] (I J : Ideal R), J.IsMaximal → I ≤ J → (J.map (Ideal.Quotient.mk I)).IsMaximal`. Introduce `R _ I J hJ hIJ`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hJ with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : Ideal.Quotient.mk I 1 ∈ J.map (Ideal.Quotient.mk I)`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Rewrite `h1` using `[Ideal.mem_quotient_iff_mem hIJ]`. Conclude with `hJ.ne_top ((Ideal.eq_top_iff_one J).mpr h1)`.

Conclude with `h`. Use `haveI hmax : (x.map (Ideal.Quotient.mk p)).IsMaximal := mapmax p x ‹x.IsMaximal› hp`. Establish `hmB : (maximalIdeal B).map (Ideal.Quotient.mk q) = maximalIdeal (B ⧸ q)` using `IsLocalRing.eq_maximalIdeal (mapmax q _ (IsLocalRing.maximalIdeal.isMaximal B) hqm)`. Establish `hcomap : (x.map (Ideal.Quotient.mk p)).comap (algebraMap (B ⧸ q) (C ⧸ p)) = maximalIdeal (B ⧸ q)`. Use extensionality with `b`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite using `[Ideal.mem_comap, ← hmB, Ideal.mem_quotient_iff_mem hqm]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk p (algebraMap B C b) ∈ _ ↔ _`. Rewrite using `[Ideal.mem_quotient_iff_mem hp, ← Ideal.mem_comap, hx]`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[UpperTheory.V.CA.localDimension_eq_height x p hp]`. Conclude with `g_dimform (B ⧸ q) (C ⧸ p) t hcm ht (x.map (Ideal.Quotient.mk p)) hcomap`.
-/
theorem UpperTheory.V.CA.c3b :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {B C : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing C] [Algebra B C] [Algebra.FiniteType B C] (x : Ideal C) [x.IsMaximal], IsCL O B → x.comap (algebraMap B C) = maximalIdeal B → ∀ (p : Ideal C) [p.IsPrime], p ≤ x → ∃ t : ℕ, Algebra.trdeg (B ⧸ p.comap (algebraMap B C)) (C ⧸ p) = t ∧ dimAt x p = ringKrullDim (B ⧸ p.comap (algebraMap B C)) + t := by
  intro O _ _ _ _ B C _ _ _ _ _ _ x _ hCL hx p _ hp
  set q := p.comap (algebraMap B C) with hq
  have hqm : q ≤ maximalIdeal B := by
    rw [← hx]
    exact Ideal.comap_mono hp
  haveI : IsLocalRing (B ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : FaithfulSMul (B ⧸ q) (C ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  have hcm : IsCMQuot (B ⧸ q) :=
    cl_cmquot O (B ⧸ q) (cl_quot O B (B ⧸ q) (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective hCL)
  have hlt : Algebra.trdeg (B ⧸ q) (C ⧸ p) < Cardinal.aleph0 := by
    open Algebra in exact trdeg_lt_aleph0_of_finiteType
  set t := (Algebra.trdeg (B ⧸ q) (C ⧸ p)).toNat
  have ht : Algebra.trdeg (B ⧸ q) (C ⧸ p) = t := (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm
  have mapmax : ∀ {R : Type} [CommRing R] (I J : Ideal R), J.IsMaximal → I ≤ J →
      (J.map (Ideal.Quotient.mk I)).IsMaximal := by
    intro R _ I J hJ hIJ
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hJ with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk I 1 ∈ J.map (Ideal.Quotient.mk I) := by
        rw [h]
        exact Submodule.mem_top
      rw [Ideal.mem_quotient_iff_mem hIJ] at h1
      exact hJ.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
    · exact h
  haveI hmax : (x.map (Ideal.Quotient.mk p)).IsMaximal := mapmax p x ‹x.IsMaximal› hp
  have hmB : (maximalIdeal B).map (Ideal.Quotient.mk q) = maximalIdeal (B ⧸ q) :=
    IsLocalRing.eq_maximalIdeal (mapmax q _ (IsLocalRing.maximalIdeal.isMaximal B) hqm)
  have hcomap : (x.map (Ideal.Quotient.mk p)).comap (algebraMap (B ⧸ q) (C ⧸ p)) = maximalIdeal (B ⧸ q) := by
    ext b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.mem_comap, ← hmB, Ideal.mem_quotient_iff_mem hqm]
    change Ideal.Quotient.mk p (algebraMap B C b) ∈ _ ↔ _
    rw [Ideal.mem_quotient_iff_mem hp, ← Ideal.mem_comap, hx]
  refine ⟨t, ht, ?_⟩
  rw [UpperTheory.V.CA.localDimension_eq_height x p hp]
  exact g_dimform (B ⧸ q) (C ⧸ p) t hcm ht (x.map (Ideal.Quotient.mk p)) hcomap
