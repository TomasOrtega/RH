import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.E8.TwSec

/- English proof (translation)
Establish `hm` using `cyclotomic.monic q A`. Use `Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis` as an intermediate fact. Establish `: Module.Finite A (AdjoinRoot (cyclotomic q A))` using `Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis`. Introduce `p`. Establish `: Nontrivial A`.

Break down `subsingleton_or_nontrivial A with h | h` into its components or cases. Conclude with `absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top`. Conclude with `h`. Establish `: Nontrivial (AdjoinRoot (cyclotomic q A))`. Establish `hd : 0 < (cyclotomic q A).natDegree`.

Rewrite using `[natDegree_cyclotomic]`. Conclude with `Nat.totient_pos.2 (NeZero.pos q)`. Establish `: Nonempty (Fin (cyclotomic q A).natDegree)` using `⟨⟨0, hd⟩⟩`. Conclude with `(AdjoinRoot.powerBasisAux' hm).repr.symm.injective.nontrivial`. Conclude with `Algebra.IsIntegral.comap_surjective A _ p`.
-/
theorem twAdj_comap_surj (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyclotomic q A)))) := by
  have hm := cyclotomic.monic q A
  have := Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have : Module.Finite A (AdjoinRoot (cyclotomic q A)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis
  intro p
  have : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top
    · exact h
  have : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
    have hd : 0 < (cyclotomic q A).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q)
    have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hd⟩⟩
    exact (AdjoinRoot.powerBasisAux' hm).repr.symm.injective.nontrivial
  exact Algebra.IsIntegral.comap_surjective A _ p

/- English proof (translation)
Establish `hsep : (cyclotomic q A).Separable` using `(separable_X_pow_sub_C_unit (1 : Aˣ) hq).of_dvd (by simpa using cyclotomic.dvd_X_pow_sub_one q A)`. Take `⟨a, b, hab⟩` from `hsep`. Set `P : StandardEtalePair A` to `⟨cyclotomic q A, cyclotomic.monic q A, 1, ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩⟩`. Set `e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1)` to `P.equivAwayAdjoinRoot`. Set `e2 : AdjoinRoot (cyclotomic q A) ≃ₐ[AdjoinRoot (cyclotomic q A)] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1)` to `IsLocalization.atUnit _ _ (AdjoinRoot.mk (cyclotomic q A) 1) (by rw [map_one]; exact isUnit_one)`.

Use `Algebra.IsStandardEtale.of_equiv (e1.trans (e2.symm.restrictScalars A))` as an intermediate fact. Use `infer_instance`.
-/
theorem twAdj_etale (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  have hsep : (cyclotomic q A).Separable :=
    (separable_X_pow_sub_C_unit (1 : Aˣ) hq).of_dvd (by simpa using cyclotomic.dvd_X_pow_sub_one q A)
  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair A := ⟨cyclotomic q A, cyclotomic.monic q A, 1,
    ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩⟩
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) := P.equivAwayAdjoinRoot
  let e2 : AdjoinRoot (cyclotomic q A) ≃ₐ[AdjoinRoot (cyclotomic q A)]
      Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) :=
    IsLocalization.atUnit _ _ (AdjoinRoot.mk (cyclotomic q A) 1) (by rw [map_one]; exact isUnit_one)
  have := Algebra.IsStandardEtale.of_equiv (e1.trans (e2.symm.restrictScalars A))
  infer_instance

/- English proof (translation)
Introduce `q _ U u hq`. Take `⟨R, f, hf, ⟨x, rfl⟩, -⟩` from `Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := u) (U := ⊤) (by simp)`. Establish `hqR : IsUnit ((q : ℕ) : R)`. Simplify using `using (hq.map f.appTop.hom).map (Scheme.ΓSpecIso R).hom.hom`. Use `twAdj_etale R q hqR` as an intermediate fact.

Set `φ : R ⟶ CommRingCat.of (AdjoinRoot (cyclotomic q R))` to `CommRingCat.ofHom (algebraMap R (AdjoinRoot (cyclotomic q R)))`. Establish `hφ : Etale (Spec.map φ)` using `HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)`. Use `⟨Spec (.of (AdjoinRoot (cyclotomic q R))), Spec.map φ ≫ f, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `twAdj_comap_surj R q x`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Substitute `hy` using the available equality. Both sides reduce to the same expression. Set `ψ` to `(Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyclotomic q R)))).inv.hom`. Use `⟨⟨ψ (AdjoinRoot.root _), ?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `using (hqR.map (algebraMap R (AdjoinRoot (cyclotomic q R)))).map ψ`.

Establish `h0 : aeval (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ) = 0`. Rewrite using `[← aeval_map_algebraMap R, map_cyclotomic, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]`. Use `aeval_algHom_apply ψ.toIntAlgHom (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ)` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this`.
-/
theorem LeafTwAdj_of : LeafTwAdj := by
  intro q _ U u hq
  obtain ⟨R, f, hf, ⟨x, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := u) (U := ⊤) (by simp)
  have hqR : IsUnit ((q : ℕ) : R) := by
    simpa using (hq.map f.appTop.hom).map (Scheme.ΓSpecIso R).hom.hom
  have := twAdj_etale R q hqR
  let φ : R ⟶ CommRingCat.of (AdjoinRoot (cyclotomic q R)) :=
    CommRingCat.ofHom (algebraMap R (AdjoinRoot (cyclotomic q R)))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  refine ⟨Spec (.of (AdjoinRoot (cyclotomic q R))), Spec.map φ ≫ f, inferInstance, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := twAdj_comap_surj R q x
    refine ⟨y, ?_⟩
    subst hy
    rfl
  · let ψ := (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyclotomic q R)))).inv.hom
    refine ⟨⟨ψ (AdjoinRoot.root _), ?_, ?_⟩⟩
    · simpa using (hqR.map (algebraMap R (AdjoinRoot (cyclotomic q R)))).map ψ
    · have h0 : aeval (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ) = 0 := by
        rw [← aeval_map_algebraMap R, map_cyclotomic, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have := aeval_algHom_apply ψ.toIntAlgHom (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ)
      rw [h0, map_zero] at this
      exact this

end LateralTheory.E.E8.TwSec
