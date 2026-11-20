import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSpecHomSpecMapAppTop
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinSchemeRank

/- English proof (translation)
Use `letI : Algebra R S := e.toRingHom.toAlgebra`. Set `f : R ≃ₗ[R] S` to `{ e with map_smul' := fun r x => by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }`. Rewrite using `[f.length_eq]`. Conclude with `Module.length_eq_of_surjective (S := R) (R := S) (M := S) e.surjective`.
-/
theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₗ[R] S :=
    { e with map_smul' := fun r x => by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  rw [f.length_eq]
  exact Module.length_eq_of_surjective (S := R) (R := S) (M := S) e.surjective

/- English proof (translation)
Use `haveI : IsLocalHom (algebraMap k A) := ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h => by simp [h] at ha⟩`. Use `haveI : Module.Finite k (IsLocalRing.ResidueField A) := Module.Finite.of_surjective (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)).toLinearMap IsLocalRing.residue_surjective`. Establish `hb : Function.Bijective (algebraMap k (IsLocalRing.ResidueField A))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Establish `h1 : Module.length k (IsLocalRing.ResidueField A) = 1`. Rewrite using `[Module.length_eq_finrank, ← (AlgEquiv.ofBijective (Algebra.ofId k _) hb).toLinearEquiv.finrank_eq, Module.finrank_self]`.

Both sides reduce to the same expression. Rewrite using `[← Module.length_eq_finrank, IsLocalRing.length_restrictScalars k A A, ← Module.length_eq_of_surjective (S := k) (R := IsLocalRing.ResidueField k) (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective, h1, _root_.mul_one]`.
-/
theorem finrank_eq_length_of_isLocalRing (k : Type*) [Field k] [IsAlgClosed k] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra k A] [Module.Finite k A] :
    (Module.finrank k A : ℕ∞) = Module.length A A := by
  haveI : IsLocalHom (algebraMap k A) :=
    ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h => by simp [h] at ha⟩
  haveI : Module.Finite k (IsLocalRing.ResidueField A) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)).toLinearMap
      IsLocalRing.residue_surjective
  have hb : Function.Bijective (algebraMap k (IsLocalRing.ResidueField A)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have h1 : Module.length k (IsLocalRing.ResidueField A) = 1 := by
    rw [Module.length_eq_finrank,
      ← (AlgEquiv.ofBijective (Algebra.ofId k _) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
    rfl
  rw [← Module.length_eq_finrank, IsLocalRing.length_restrictScalars k A A,
    ← Module.length_eq_of_surjective (S := k) (R := IsLocalRing.ResidueField k)
      (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective, h1, _root_.mul_one]

/- English proof (translation)
Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite k B`. Use `letI := Fintype.ofFinite (PrimeSpectrum B)`. Establish `h : ∀ p : PrimeSpectrum B, (Module.finrank k (Localization.AtPrime p.asIdeal) : ℕ∞) = m`. Introduce `p`. Use `haveI : Module.Finite k (Localization.AtPrime p.asIdeal) := Module.Finite.of_surjective (Algebra.algHom k B (Localization.AtPrime p.asIdeal)).toLinearMap (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))`.

Rewrite using `[← hm p, finrank_eq_length_of_isLocalRing k]`. Rewrite using `[IsArtinianRing.finrank_eq_sum_primeSpectrum B k, Nat.cast_sum]`. Simplify using `only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.
-/
theorem finrank_eq_card_mul (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] (m : ℕ∞)
    (hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m) :
    (Module.finrank k B : ℕ∞) = Nat.card (PrimeSpectrum B) * m := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI := Fintype.ofFinite (PrimeSpectrum B)
  have h : ∀ p : PrimeSpectrum B, (Module.finrank k (Localization.AtPrime p.asIdeal) : ℕ∞) = m := by
    intro p
    haveI : Module.Finite k (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective (Algebra.algHom k B (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
    rw [← hm p, finrank_eq_length_of_isLocalRing k]
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum B k, Nat.cast_sum]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/- English proof (translation)
Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite k B`. Set `F : (B →ₐ[k] k) → PrimeSpectrum B` to `fun φ => ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩`. Use `Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `φ ψ h`. Establish `h' : RingHom.ker φ = RingHom.ker ψ` using `congrArg PrimeSpectrum.asIdeal h`.

Use extensionality with `b`. Establish `: b - algebraMap k B (φ b) ∈ RingHom.ker φ` using `by simp [RingHom.mem_ker]`. Rewrite `this` using `[h', RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]`. Conclude with `this.symm`. Introduce `p haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal`.

Use `letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _`. Establish `hb : Function.Bijective (algebraMap k (B ⧸ p.asIdeal))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e` to `AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ p.asIdeal)) hb`. Use `⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k p.asIdeal), ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal`. Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem card_algHom_eq_card_primeSpectrum (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    Nat.card (B →ₐ[k] k) = Nat.card (PrimeSpectrum B) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  let F : (B →ₐ[k] k) → PrimeSpectrum B := fun φ => ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
  · intro φ ψ h
    have h' : RingHom.ker φ = RingHom.ker ψ := congrArg PrimeSpectrum.asIdeal h
    ext b
    have : b - algebraMap k B (φ b) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [h', RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact this.symm
  · intro p
    haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
    letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
    have hb : Function.Bijective (algebraMap k (B ⧸ p.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ p.asIdeal)) hb
    refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k p.asIdeal), ?_⟩
    ext x
    change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Introduce `k _ _ P q hq m hm z`. Use `haveI := hq`. Use `haveI : IsAffine P := isAffine_of_isAffineHom q`. Set `B : Type` to `Γ(P, ⊤)`. Use `letI : Algebra k B := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop).hom.toAlgebra`.

Set `q' : Spec (CommRingCat.of B) ⟶ Sp k` to `Spec.map (CommRingCat.ofHom (algebraMap k B))`. Establish `hq1 : P.isoSpec.hom ≫ q' = q` using `GlobalTheory.IwLevel.FiberCard.isoSpec_hom_specMap_appTop' q`. Establish `hq2 : q' = P.isoSpec.inv ≫ q` using `by rw [← hq1, Iso.inv_hom_id_assoc]`. Use `haveI : IsFinite q' := by rw [hq2]; infer_instance`. Use `haveI : Module.Finite k B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp (inferInstanceAs (IsFinite q')))`.

Use `haveI : Flat q' := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)`. Use `haveI : Flat q := by rw [← hq1]; infer_instance`. Establish `hrk : q.finrank z = Module.finrank k B`. Rewrite using `[← hq1, Scheme.Hom.finrank_comp_left_of_isIso]`. Use `(Scheme.Hom.finrank_SpecMap_algebraMap k B z).trans ?_` and prove the remaining obligations.

Rewrite using `[Module.rankAtStalk_eq_finrank_of_free]`. Both sides reduce to the same expression. Establish `hsec : Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} = Nat.card (B →ₐ[k] k)`. Set `F : {s : Sp k ⟶ P // s ≫ q = 𝟙 _} → (B →ₐ[k] k)` to `fun s => { (Spec.preimage (s.1 ≫ P.isoSpec.hom)).hom with commutes' := fun c => by`. Establish `h : CommRingCat.ofHom (algebraMap k B) ≫ Spec.preimage (s.1 ≫ P.isoSpec.hom) = 𝟙 _`.

Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc]`. Conclude with `(congrArg (s.1 ≫ ·) hq1).trans s.2`. Conclude with `congrArg (fun u => u.hom c) h }`. Use `Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)` and prove the remaining obligations.

Introduce `s₁ s₂ h`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : Spec.preimage (s₁.1 ≫ P.isoSpec.hom) = Spec.preimage (s₂.1 ≫ P.isoSpec.hom)`. Use extensionality with `c`. Conclude with `congrArg (fun u : B →ₐ[k] k => u c) h`.

Establish `h2` using `congrArg Spec.map h1`. Rewrite `h2` using `[Spec.map_preimage, Spec.map_preimage]`. Simplify using `using congrArg (· ≫ P.isoSpec.inv) h2`. Introduce `φ`. Set `s : Sp k ⟶ P` to `Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.isoSpec.inv`.

Establish `hs' : s ≫ P.isoSpec.hom = Spec.map (CommRingCat.ofHom φ.toRingHom)` using `by simp [s]`. Establish `hs : s ≫ q = 𝟙 _`. Rewrite using `[← hq1, ← Category.assoc, hs', ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `c`.

Conclude with `φ.commutes c`. Use `⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Express the relevant statement in the definitionally equal form `(Spec.preimage (s ≫ P.isoSpec.hom)).hom b = φ b`. Rewrite using `[hs', Spec.preimage_map]`.

Both sides reduce to the same expression. Establish `hstalk : ∀ p : PrimeSpectrum B, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m`. Introduce `p`. Establish `hU` using `isAffineOpen_top P`. Establish `hp : hU.fromSpec p ∈ (⊤ : P.Opens)` using `by simp`.

Use `letI : Algebra B (P.presheaf.stalk (hU.fromSpec p)) := TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨hU.fromSpec p, hp⟩`. Use `haveI : IsLocalization p.asIdeal.primeCompl (P.presheaf.stalk (hU.fromSpec p)) := hU.isLocalization_stalk' p hp`. Rewrite using `[← hm (hU.fromSpec p)]`. Conclude with `length_self_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (P.presheaf.stalk (hU.fromSpec p))).toRingEquiv`. Rewrite using `[hrk, hsec, card_algHom_eq_card_primeSpectrum k B]`.

Conclude with `finrank_eq_card_mul k B m hstalk`.
-/
theorem finrank_eq_card_sections_mul : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k),
    IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) →
    ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  intro k _ _ P q hq m hm z
  haveI := hq
  haveI : IsAffine P := isAffine_of_isAffineHom q
  let B : Type := Γ(P, ⊤)
  letI : Algebra k B := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop).hom.toAlgebra
  let q' : Spec (CommRingCat.of B) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k B))
  have hq1 : P.isoSpec.hom ≫ q' = q := GlobalTheory.IwLevel.FiberCard.isoSpec_hom_specMap_appTop' q
  have hq2 : q' = P.isoSpec.inv ≫ q := by rw [← hq1, Iso.inv_hom_id_assoc]
  haveI : IsFinite q' := by rw [hq2]; infer_instance
  haveI : Module.Finite k B :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp (inferInstanceAs (IsFinite q')))
  haveI : Flat q' := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Flat q := by rw [← hq1]; infer_instance
  have hrk : q.finrank z = Module.finrank k B := by
    rw [← hq1, Scheme.Hom.finrank_comp_left_of_isIso]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap k B z).trans ?_
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hsec : Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} = Nat.card (B →ₐ[k] k) := by
    let F : {s : Sp k ⟶ P // s ≫ q = 𝟙 _} → (B →ₐ[k] k) := fun s =>
      { (Spec.preimage (s.1 ≫ P.isoSpec.hom)).hom with
        commutes' := fun c => by
          have h : CommRingCat.ofHom (algebraMap k B) ≫ Spec.preimage (s.1 ≫ P.isoSpec.hom) = 𝟙 _ := by
            apply Spec.map_injective
            rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc]
            exact (congrArg (s.1 ≫ ·) hq1).trans s.2
          exact congrArg (fun u => u.hom c) h }
    refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
    · intro s₁ s₂ h
      apply Subtype.ext
      have h1 : Spec.preimage (s₁.1 ≫ P.isoSpec.hom) = Spec.preimage (s₂.1 ≫ P.isoSpec.hom) := by
        ext c
        exact congrArg (fun u : B →ₐ[k] k => u c) h
      have h2 := congrArg Spec.map h1
      rw [Spec.map_preimage, Spec.map_preimage] at h2
      simpa using congrArg (· ≫ P.isoSpec.inv) h2
    · intro φ
      let s : Sp k ⟶ P := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.isoSpec.inv
      have hs' : s ≫ P.isoSpec.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) := by simp [s]
      have hs : s ≫ q = 𝟙 _ := by
        rw [← hq1, ← Category.assoc, hs', ← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext c
        exact φ.commutes c
      refine ⟨⟨s, hs⟩, ?_⟩
      ext b
      change (Spec.preimage (s ≫ P.isoSpec.hom)).hom b = φ b
      rw [hs', Spec.preimage_map]
      rfl
  have hstalk : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m := by
    intro p
    have hU := isAffineOpen_top P
    have hp : hU.fromSpec p ∈ (⊤ : P.Opens) := by simp
    letI : Algebra B (P.presheaf.stalk (hU.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨hU.fromSpec p, hp⟩
    haveI : IsLocalization p.asIdeal.primeCompl (P.presheaf.stalk (hU.fromSpec p)) :=
      hU.isLocalization_stalk' p hp
    rw [← hm (hU.fromSpec p)]
    exact length_self_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (P.presheaf.stalk (hU.fromSpec p))).toRingEquiv
  rw [hrk, hsec, card_algHom_eq_card_primeSpectrum k B]
  exact finrank_eq_card_mul k B m hstalk

end GlobalTheory.FinSchemeRank
