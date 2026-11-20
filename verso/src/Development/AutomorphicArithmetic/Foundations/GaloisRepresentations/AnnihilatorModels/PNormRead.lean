import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Simplify using `[form, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_sum, map_sum, MvPolynomial.map_C, MvPolynomial.map_X]`.
-/
private theorem form_map' {B B' ι : Type} [CommRing B] [CommRing B'] [Fintype ι] (f : B →+* B') (c : ι → B) :
    (form c).map (MvPolynomial.map f) = form fun k => f (c k) := by
  simp [form, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_sum, map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

/- English proof (translation)
Establish `hj' : Function.Injective (j : B →+* B')` using `hj`. Apply `Polynomial.map_injective _ (MvPolynomial.map_injective _ hj')` to reduce the goal to its premises. Rewrite using `[Polynomial.map_prod]`. Establish `e : ∀ i, (form fun k => z i (s k)).map (MvPolynomial.map (j : B →+* B')) = form fun k => j (z i (s k))` using `fun i => form_map' _ _`. Simplify using `only [e]`.

Establish `hc : (MvPolynomial.map (σ` using `ι) (j : B →+* B')).comp (MvPolynomial.map (algebraMap R B)) = MvPolynomial.map (algebraMap R B') := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `i`.

Simplify using the standard rewrite rules. Rewrite using `[← h, mapP, Polynomial.map_map, hc]`.
-/
private theorem descend {R S B B' ι I : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing B']
    [Algebra R S] [Algebra R B] [Algebra R B'] [Fintype ι] [Fintype I]
    (j : B →ₐ[R] B') (hj : Function.Injective j) (N : Polynomial (MvPolynomial ι R)) (s : ι → S)
    (z : I → (S →ₐ[R] B))
    (h : mapP (algebraMap R B') N = ∏ i, form fun k => j (z i (s k))) :
    mapP (algebraMap R B) N = ∏ i, form fun k => z i (s k) := by
  have hj' : Function.Injective (j : B →+* B') := hj
  apply Polynomial.map_injective _ (MvPolynomial.map_injective _ hj')
  rw [Polynomial.map_prod]
  have e : ∀ i, (form fun k => z i (s k)).map (MvPolynomial.map (j : B →+* B'))
      = form fun k => j (z i (s k)) := fun i => form_map' _ _
  simp only [e]
  have hc : (MvPolynomial.map (σ := ι) (j : B →+* B')).comp (MvPolynomial.map (algebraMap R B))
      = MvPolynomial.map (algebraMap R B') := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp
  rw [← h, mapP, Polynomial.map_map, hc]

/- English proof (translation)
Introduce `hInt hEt hSF hVP l d R S _ _ _ hE hcl ι _ s`. Take `⟨N, hN⟩` from `hInt l d R S hE hcl ι s`. Use `⟨N, ?_, ?_⟩` and prove the remaining obligations. Introduce `B _ _ hl I _ z hz`. Establish `hinj : Function.Injective (algebraMap B (Localization.Away (l : B)))` using `IsLocalization.injective _ (Submonoid.powers_le.2 hl)`.

Establish `hu : IsUnit (l : Localization.Away (l : B))`. Use `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : B)) (l : B)` as an intermediate fact. Simplify using `using this`. Establish `h1` using `hN (Localization.Away (l : B)) hu I (fun i => (IsScalarTower.toAlgHom R B (Localization.Away (l : B))).comp (z i)) hz`. Conclude with `descend (IsScalarTower.toAlgHom R B (Localization.Away (l : B))) hinj N s z h1`.

Introduce `V _ _ _ _ _ hl`. Establish `hinj : Function.Injective (algebraMap V (FractionRing V))` using `IsFractionRing.injective V (FractionRing V)`. Establish `hlK : ((l : ℕ) : FractionRing V) ≠ 0`. Introduce `h0`. Apply `hl` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Simplify using `using h0`. Establish `hu : IsUnit ((l : ℕ) : FractionRing V)` using `hlK.isUnit`. Establish `het : Algebra.Etale (FractionRing V) (FractionRing V ⊗[R] S)` using `hEt l R S _ hE.et hu`. Take `⟨hfin, hsp⟩` from `hSF R S (FractionRing V) het`.

Use `haveI := hE.fin`. Establish `hb` using `hVP R S V`. Establish `hfinV : Finite (S →ₐ[R] V)` using `Finite.of_injective _ hb.1`. Use `⟨hfinV, fun I _ z hz => ?_⟩` and prove the remaining obligations. Use `letI := Fintype.ofFinite (S →ₐ[R] FractionRing V)`.

Establish `h1` using `hN (FractionRing V) hu (S →ₐ[R] FractionRing V) (fun z => z) hsp`. Use `descend (IsScalarTower.toAlgHom R V (FractionRing V)) hinj N s z ?_` and prove the remaining obligations. Rewrite using `[h1]`. Use `symm`. Conclude with `Fintype.prod_bijective (fun i => (IsScalarTower.toAlgHom R V (FractionRing V)).comp (z i)) (hb.comp hz) _ _ (fun i => rfl)`.
-/
theorem UpperTheory.Gal.crystallineComparison.normRead_of :
    NormInt → EtOfUnit → SplitsField → ValPts → NormRead := by
  intro hInt hEt hSF hVP l d R S _ _ _ hE hcl ι _ s
  obtain ⟨N, hN⟩ := hInt l d R S hE hcl ι s
  refine ⟨N, ?_, ?_⟩
  · intro B _ _ hl I _ z hz
    have hinj : Function.Injective (algebraMap B (Localization.Away (l : B))) :=
      IsLocalization.injective _ (Submonoid.powers_le.2 hl)
    have hu : IsUnit (l : Localization.Away (l : B)) := by
      have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : B)) (l : B)
      simpa using this
    have h1 := hN (Localization.Away (l : B)) hu I
      (fun i => (IsScalarTower.toAlgHom R B (Localization.Away (l : B))).comp (z i)) hz
    exact descend (IsScalarTower.toAlgHom R B (Localization.Away (l : B))) hinj N s z h1
  · intro V _ _ _ _ _ hl
    have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
      IsFractionRing.injective V (FractionRing V)
    have hlK : ((l : ℕ) : FractionRing V) ≠ 0 := by
      intro h0
      apply hl
      apply hinj
      simpa using h0
    have hu : IsUnit ((l : ℕ) : FractionRing V) := hlK.isUnit
    have het : Algebra.Etale (FractionRing V) (FractionRing V ⊗[R] S) := hEt l R S _ hE.et hu
    obtain ⟨hfin, hsp⟩ := hSF R S (FractionRing V) het
    haveI := hE.fin
    have hb := hVP R S V
    have hfinV : Finite (S →ₐ[R] V) := Finite.of_injective _ hb.1
    refine ⟨hfinV, fun I _ z hz => ?_⟩
    letI := Fintype.ofFinite (S →ₐ[R] FractionRing V)
    have h1 := hN (FractionRing V) hu (S →ₐ[R] FractionRing V) (fun z => z) hsp
    refine descend (IsScalarTower.toAlgHom R V (FractionRing V)) hinj N s z ?_
    rw [h1]
    symm
    exact Fintype.prod_bijective (fun i => (IsScalarTower.toAlgHom R V (FractionRing V)).comp (z i))
      (hb.comp hz) _ _ (fun i => rfl)
