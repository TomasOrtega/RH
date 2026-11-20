import Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafPrimCoverPf

/- English proof (translation)
Take `⟨h, hh⟩ : cyclotomic q A ∣ X ^ q - 1` from `cyclotomic.dvd_X_pow_sub_one q A`. Establish `hd` using `congrArg derivative hh`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd`. Take `⟨u, hu⟩` from `hq.exists_left_inv`. Use `⟨C u * (h * X), C u * (derivative h * X - C (q : A) * h), ?_⟩` and prove the remaining obligations.

Establish `hq0 : 0 < q` using `Nat.pos_of_neZero q`. Establish `e1 : (X : A[X]) ^ q = X ^ (q - 1) * X`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hq0]`. Establish `hc : (C (q : A) : A[X]) = (q : A[X])` using `map_natCast C q`. Establish `hcu : C u * C (q : A) = 1` using `by rw [← C_mul, hu, C_1]`.

Rewrite `hh` using `[e1]`. Take the linear combination `(-(C u * X)) * hd + (C u * C (q:A)) * hh + hcu`.
-/
theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = 1 := by
  obtain ⟨h, hh⟩ : cyclotomic q A ∣ X ^ q - 1 := cyclotomic.dvd_X_pow_sub_one q A
  have hd := congrArg derivative hh
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd
  obtain ⟨u, hu⟩ := hq.exists_left_inv
  refine ⟨C u * (h * X), C u * (derivative h * X - C (q : A) * h), ?_⟩
  have hq0 : 0 < q := Nat.pos_of_neZero q
  have e1 : (X : A[X]) ^ q = X ^ (q - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel hq0]
  have hc : (C (q : A) : A[X]) = (q : A[X]) := map_natCast C q
  have hcu : C u * C (q : A) = 1 := by rw [← C_mul, hu, C_1]
  rw [e1] at hh
  linear_combination (-(C u * X)) * hd + (C u * C (q:A)) * hh + hcu

def cycPair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := by
    obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq
    exact ⟨p₁, p₂, 0, by simpa using h⟩

/- English proof (translation)
Set `P` to `cycPair A q hq`. Set `e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g)` to `P.equivAwayAdjoinRoot`. Establish `hu : IsUnit (AdjoinRoot.mk P.f P.g)`. Rewrite using `[show P.g = 1 from rfl, map_one]`. Conclude with `isUnit_one`.

Set `e2 : AdjoinRoot P.f ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g)` to `(IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.mk P.f P.g) hu).restrictScalars A`. Conclude with `Algebra.Etale.of_equiv (e1.trans e2.symm)`.
-/
theorem etale_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  let P := cycPair A q hq
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := by
    rw [show P.g = 1 from rfl, map_one]; exact isUnit_one
  let e2 : AdjoinRoot P.f ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.mk P.f P.g) hu).restrictScalars A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

/- English proof (translation)
Set `b` to `AdjoinRoot.powerBasisAux' (cyclotomic.monic q A)`. Establish `hpos : 0 < (cyclotomic q A).natDegree`. Rewrite using `[natDegree_cyclotomic]`. Conclude with `Nat.totient_pos.2 (Nat.pos_of_neZero q)`. Establish `: Nonempty (Fin (cyclotomic q A).natDegree)` using `⟨⟨0, hpos⟩⟩`.

Conclude with `Module.FaithfullyFlat.of_linearEquiv _ _ b.repr`.
-/
theorem ff_adjoin (A : Type) [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Module.FaithfullyFlat A (AdjoinRoot (cyclotomic q A)) := by
  let b := AdjoinRoot.powerBasisAux' (cyclotomic.monic q A)
  have hpos : 0 < (cyclotomic q A).natDegree := by
    rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_neZero q)
  have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hpos⟩⟩
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

/- English proof (translation)
The claim follows from `U.toSpecΓ`.
-/
example (U : Scheme.{0}) : U ⟶ Spec Γ(U, ⊤) := U.toSpecΓ

/- English proof (translation)
Use `⟨⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), ?_⟩⟩` and prove the remaining obligations. Establish `h0 : aeval (AdjoinRoot.root (cyclotomic q A)) (cyclotomic q A) = 0`. Rewrite using `[AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]`. Rewrite using `[← aeval_map_algebraMap A, map_cyclotomic]`. Conclude with `h0`.
-/
theorem prim_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Nonempty (Prim q (AdjoinRoot (cyclotomic q A))) := by
  refine ⟨⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), ?_⟩⟩
  have h0 : aeval (AdjoinRoot.root (cyclotomic q A)) (cyclotomic q A) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← aeval_map_algebraMap A, map_cyclotomic]
  exact h0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x`. Conclude with `absurd (Subsingleton.elim _ _) x.isPrime.ne_top`.
-/
theorem spec_surj (A B : CommRingCat.{0}) (φ : A ⟶ B) (hA : Subsingleton A) : Surjective (Spec.map φ) := by
  constructor
  intro x
  exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

/- English proof (translation)
Introduce `q _ U hq`. Set `A : Type` to `Γ(U, ⊤)`. Set `B : Type` to `AdjoinRoot (cyclotomic q A)`. Set `φ : Γ(U, ⊤) ⟶ CommRingCat.of B` to `CommRingCat.ofHom (algebraMap A B)`. Establish `hEt : Etale (Spec.map φ)`.

Use `etale_adjoin A q hq` as an intermediate fact. Conclude with `(HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr this)`. Establish `hSu : Surjective (Spec.map φ)`. Break down `subsingleton_or_nontrivial A with h | h` into its components or cases. Conclude with `spec_surj _ _ φ h`.

Use `ff_adjoin A q` as an intermediate fact. Conclude with `((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2`. Set `f` to `pullback.fst U.toSpecΓ (Spec.map φ)`. Use `⟨Sieve.generate (Presieve.singleton f), ?_, ?_⟩` and prove the remaining obligations. Apply `Precoverage.generate_mem_toGrothendieck` to reduce the goal to its premises.

Conclude with `(Scheme.singleton_mem_precoverage_iff (P := @Etale) f).2 ⟨Surjective.surj, inferInstance⟩`. Introduce and unpack `V g ⟨W, h, k, hk, rfl⟩`. Consider the cases of `hk`. Take `⟨ζ⟩` from `prim_adjoin A q hq`. Conclude with `⟨Prim.map (h.appTop.hom.comp ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) ζ⟩`.
-/
theorem leafPrimCover_pf : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := by
  intro q _ U hq
  let A : Type := Γ(U, ⊤)
  let B : Type := AdjoinRoot (cyclotomic q A)
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hEt : Etale (Spec.map φ) := by
    have := etale_adjoin A q hq
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr this)
  have hSu : Surjective (Spec.map φ) := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact spec_surj _ _ φ h
    · have := ff_adjoin A q
      exact ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2
  let f := pullback.fst U.toSpecΓ (Spec.map φ)
  refine ⟨Sieve.generate (Presieve.singleton f), ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    exact (Scheme.singleton_mem_precoverage_iff (P := @Etale) f).2 ⟨Surjective.surj, inferInstance⟩
  · rintro V g ⟨W, h, k, hk, rfl⟩
    cases hk
    obtain ⟨ζ⟩ := prim_adjoin A q hq
    exact ⟨Prim.map (h.appTop.hom.comp ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) ζ⟩

/- English proof (translation)
The claim follows from `leafPrimCover_pf`.
-/
theorem LeafPrimCover_of : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := leafPrimCover_pf

end LateralTheory.E.LeafPrimCoverPf
