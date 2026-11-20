import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HartTensorOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfGaloisTraceRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisComparisonMapInjectiveOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisElementDvdOfFormallyUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfLowHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulDvdOfLocalizationAtPrimeTensorStatement

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

/- English proof (translation)
Introduce `A R C O _ _ _ _ _ _ _ _ hσ hTF a ha v hv`. Take `⟨σ⟩` from `hσ`. Establish `hRO : Function.Injective (algebraMap R O)` using `RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)`. Establish `hreg : IsSMulRegular R (algebraMap A R a)`. Introduce `r s hrs`.

Simplify using `only [smul_eq_mul] at hrs`. Establish `h0 : algebraMap A R a * (r - s) = 0` using `by rw [mul_sub, hrs, sub_self]`. Establish `h1 : algebraMap A R a • algebraMap R C (r - s) = 0`. Rewrite using `[Algebra.smul_def, ← map_mul, h0, map_zero]`. Establish `h2` using `hTF a ha _ h1`.

Establish `h3 : algebraMap R O (r - s) = 0`. Rewrite using `[← σ.commutes, h2, map_zero]`. Conclude with `sub_eq_zero.mp (hRO (by rw [h3, map_zero]))`. Establish `hO : IsSMulRegular O (algebraMap R O (algebraMap A R a))` using `IsSMulRegular.of_flat hreg`. Apply `hO` to reduce the goal to its premises.

Simplify using `only [smul_eq_mul, mul_zero]`. Conclude with `hv`.
-/
theorem noTorsion_of_faithfullyFlat_point : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O],
    Nonempty (C →ₐ[R] O) → GlobalTheory.GoodEtale.TorsionFreeOver A R C →
    ∀ (a : A), a ≠ 0 → ∀ v : O, algebraMap R O (algebraMap A R a) * v = 0 → v = 0 := by
  intro A R C O _ _ _ _ _ _ _ _ hσ hTF a ha v hv
  obtain ⟨σ⟩ := hσ
  have hRO : Function.Injective (algebraMap R O) :=
    RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hreg : IsSMulRegular R (algebraMap A R a) := by
    intro r s hrs
    simp only [smul_eq_mul] at hrs
    have h0 : algebraMap A R a * (r - s) = 0 := by rw [mul_sub, hrs, sub_self]
    have h1 : algebraMap A R a • algebraMap R C (r - s) = 0 := by
      rw [Algebra.smul_def, ← map_mul, h0, map_zero]
    have h2 := hTF a ha _ h1
    have h3 : algebraMap R O (r - s) = 0 := by
      rw [← σ.commutes, h2, map_zero]
    exact sub_eq_zero.mp (hRO (by rw [h3, map_zero]))
  have hO : IsSMulRegular O (algebraMap R O (algebraMap A R a)) := IsSMulRegular.of_flat hreg
  apply hO
  simp only [smul_eq_mul, mul_zero]
  exact hv

/- English proof (translation)
Introduce `A O M _ _ _ _ _ hH a ha m hloc`. Apply `hH a ha m` to reduce the goal to its premises. Introduce `p hp hpht`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Set `J : Ideal O` to `{ carrier := {o | ∃ m' : M, o • m = algebraMap A O a • m'} add_mem' := by`. Introduce and unpack `x y ⟨m₁, h₁⟩ ⟨m₂, h₂⟩`. Conclude with `⟨m₁ + m₂, by rw [add_smul, h₁, h₂, smul_add]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c x ⟨m₁, h₁⟩`. Use `⟨c • m₁, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_smul, h₁, smul_comm] }`. Establish `hdisj : Disjoint (J : Set O) ((p.primeCompl.map (algebraMap A O) : Submonoid O) : Set O)`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨m', hm'⟩ ⟨u, hu, rfl⟩`. Conclude with `hcon u hu m' hm'`. Take `⟨Q, hQ, hJQ, hQd⟩` from `Ideal.exists_le_prime_disjoint J _ hdisj`. Establish `hle : Q.comap (algebraMap A O) ≤ p`.

Introduce `u hu`. Assume the negation of the conclusion as `hup`. Conclude with `Set.disjoint_left.mp hQd hu ⟨u, hup, rfl⟩`. Take `⟨s, hs, m', hm'⟩` from `hloc Q hQ ((Ideal.height_mono hle).trans hpht)`. Conclude with `hs (hJQ ⟨m', hm'⟩)`.
-/
theorem hart_of_local : ∀ (A O M : Type) [CommRing A] [CommRing O] [Algebra A O] [AddCommGroup M] [Module O M],
    GlobalTheory.GoodEtale.Hart A O M → ∀ (a : A), a ≠ 0 → ∀ m : M,
    (∀ Q : Ideal O, Q.IsPrime → (Q.comap (algebraMap A O)).height ≤ 1 →
      ∃ s ∉ Q, ∃ m' : M, s • m = algebraMap A O a • m') →
    ∃ m' : M, m = algebraMap A O a • m' := by
  intro A O M _ _ _ _ _ hH a ha m hloc
  apply hH a ha m
  intro p hp hpht
  by_contra hcon
  push_neg at hcon
  let J : Ideal O :=
    { carrier := {o | ∃ m' : M, o • m = algebraMap A O a • m'}
      add_mem' := by
        rintro x y ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
        exact ⟨m₁ + m₂, by rw [add_smul, h₁, h₂, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨m₁, h₁⟩
        refine ⟨c • m₁, ?_⟩
        simp only [smul_eq_mul]
        rw [mul_smul, h₁, smul_comm] }
  have hdisj : Disjoint (J : Set O) ((p.primeCompl.map (algebraMap A O) : Submonoid O) : Set O) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m', hm'⟩ ⟨u, hu, rfl⟩
    exact hcon u hu m' hm'
  obtain ⟨Q, hQ, hJQ, hQd⟩ := Ideal.exists_le_prime_disjoint J _ hdisj
  have hle : Q.comap (algebraMap A O) ≤ p := by
    intro u hu
    by_contra hup
    exact Set.disjoint_left.mp hQd hu ⟨u, hup, rfl⟩
  obtain ⟨s, hs, m', hm'⟩ := hloc Q hQ ((Ideal.height_mono hle).trans hpht)
  exact hs (hJQ ⟨m', hm'⟩)

/- English proof (translation)
Introduce `A R C O _ _ _ _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy hTF hH hE hσ`. Take `⟨σ⟩` from `hσ`. Use `⟨GlobalTheory.T.finite_of_galois_trace_relation A R C G act T hT a ha n x y hxy hTF, ?_⟩` and prove the remaining obligations. Use `letI : Algebra A O := ((algebraMap R O).comp (algebraMap A R)).toAlgebra`. Use `haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Establish `hHO : Hart A O (O ⊗[R] C)` using `GlobalTheory.T.hart_baseChange_of_flat A R C O hH`. Use `set b := algebraMap A R a with hb`. Establish `hdiv : ∀ h : G, ∃ m' : O ⊗[R] C, galElt act σ x y h = algebraMap R O b • m'`. Introduce `h`. Use `hart_of_local A O (O ⊗[R] C) hHO a ha (galElt act σ x y h) ?_` and prove the remaining obligations.

Introduce `Q hQ hht`. Use `haveI := hQ`. Apply the tactic sequence `haveI : Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height A R C O Q hE (by first | exact hht | (rw [Ideal.comap_comap]; exact hht))`. Set `σQ : C →ₐ[R] Localization.AtPrime Q` to `(IsScalarTower.toAlgHom R O _).comp σ`. Establish `hinj` using `GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C (Localization.AtPrime Q) G act T hT a ha n x y hxy hTF σQ`.

Take `⟨m'', hm''⟩` from `GlobalTheory.T.galoisElement_dvd_of_formallyUnramified R C (Localization.AtPrime Q) G act b n x y hxy σQ hinj h`. Establish `hcomp : (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C (galElt act σ x y h) = galElt act σQ x y h`. Simplify using `[galElt, map_sum, σQ]`. Take `⟨s, hs, m', hm'⟩` from `GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' R C O Q b _ ⟨m'', hcomp.trans hm''⟩`. Conclude with `⟨s, hs, m', hm'⟩`.

Establish `key : ∀ h, ∃ m, galMap act σ m = Pi.single h 1`. Introduce `h`. Take `⟨m', hm'⟩` from `hdiv h`. Use `⟨m', ?_⟩` and prove the remaining obligations. Establish `h1` using `galMap_galElt act σ x y b (by simpa [hb] using hxy) h`.

Rewrite `h1` using `[hm', map_smul]`. Use function extensionality and compare the values at `g`. Establish `h2` using `congrFun h1 g`. Use `sub_eq_zero.mp (noTorsion_of_faithfullyFlat_point A R C O ⟨σ⟩ hTF a ha _ ?_)` and prove the remaining obligations. Rewrite using `[mul_sub]`.

Distinguish the cases in `hg : g = h`. Substitute `hg` using the available equality. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h2 ⊢`. Rewrite using `[h2]`. Simplify using `[hb]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hg] at h2 ⊢`. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Establish `hsurj : Function.Surjective (galMap act σ)`. Introduce `v`.

Use `choose m hm using key`. Use `⟨∑ h, v h • m h, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [map_smul, hm]`. Use function extensionality and compare the values at `g`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Set `e` to `AlgEquiv.ofBijective (galMap act σ) ⟨GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C O G act T hT a ha n x y hxy hTF σ, hsurj⟩`. Use `haveI : Algebra.Etale O (O ⊗[R] C) := Algebra.Etale.of_equiv e.symm`. Conclude with `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat O`.
-/
theorem descent_finiteEtale : ∀ (A R C O : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → GlobalTheory.GoodEtale.Hart A R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    Nonempty (C →ₐ[R] O) →
    Module.Finite R C ∧ Algebra.Etale R C := by
  intro A R C O _ _ _ _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy hTF hH hE hσ
  obtain ⟨σ⟩ := hσ
  refine ⟨GlobalTheory.T.finite_of_galois_trace_relation A R C G act T hT a ha n x y hxy hTF, ?_⟩
  letI : Algebra A O := ((algebraMap R O).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hHO : Hart A O (O ⊗[R] C) := GlobalTheory.T.hart_baseChange_of_flat A R C O hH
  set b := algebraMap A R a with hb
  have hdiv : ∀ h : G, ∃ m' : O ⊗[R] C, galElt act σ x y h = algebraMap R O b • m' := by
    intro h
    refine hart_of_local A O (O ⊗[R] C) hHO a ha (galElt act σ x y h) ?_
    intro Q hQ hht
    haveI := hQ
    haveI : Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) :=
      GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height A R C O Q hE (by first | exact hht | (rw [Ideal.comap_comap]; exact hht))
    let σQ : C →ₐ[R] Localization.AtPrime Q := (IsScalarTower.toAlgHom R O _).comp σ
    have hinj := GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C (Localization.AtPrime Q) G act T hT a ha n x y hxy hTF σQ
    obtain ⟨m'', hm''⟩ := GlobalTheory.T.galoisElement_dvd_of_formallyUnramified R C (Localization.AtPrime Q) G act b n x y hxy σQ hinj h
    have hcomp : (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C
        (galElt act σ x y h) = galElt act σQ x y h := by
      simp [galElt, map_sum, σQ]
    obtain ⟨s, hs, m', hm'⟩ := GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' R C O Q b _ ⟨m'', hcomp.trans hm''⟩
    exact ⟨s, hs, m', hm'⟩
  have key : ∀ h, ∃ m, galMap act σ m = Pi.single h 1 := by
    intro h
    obtain ⟨m', hm'⟩ := hdiv h
    refine ⟨m', ?_⟩
    have h1 := galMap_galElt act σ x y b (by simpa [hb] using hxy) h
    rw [hm', map_smul] at h1
    funext g
    have h2 := congrFun h1 g
    refine sub_eq_zero.mp (noTorsion_of_faithfullyFlat_point A R C O ⟨σ⟩ hTF a ha _ ?_)
    rw [mul_sub]
    by_cases hg : g = h
    · subst hg; simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h2 ⊢; rw [h2]; simp [hb]
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hg] at h2 ⊢; rw [h2]; simp
  have hsurj : Function.Surjective (galMap act σ) := by
    intro v
    choose m hm using key
    refine ⟨∑ h, v h • m h, ?_⟩
    rw [map_sum]
    simp only [map_smul, hm]
    funext g
    simp [Finset.sum_apply, Pi.single_apply]
  let e := AlgEquiv.ofBijective (galMap act σ)
    ⟨GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C O G act T hT a ha n x y hxy hTF σ, hsurj⟩
  haveI : Algebra.Etale O (O ⊗[R] C) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat O

end GlobalTheory.GoodEtale
