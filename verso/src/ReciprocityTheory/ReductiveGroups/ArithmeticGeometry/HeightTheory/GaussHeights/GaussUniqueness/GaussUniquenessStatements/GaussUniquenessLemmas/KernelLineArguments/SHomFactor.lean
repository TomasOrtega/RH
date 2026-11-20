import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ImgRSuccAbove

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

/- English proof (translation)
Rewrite using `[Fin.sum_univ_succAbove _ jc]`. Simplify using `only [sImg, GaussValuationUniqueness.sac_same, GaussValuationUniqueness.sac_succAbove, if_neg hi, hb, map_one, mul_one]`. Simplify using `only [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N), MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum, ← map_add, neg_add_cancel, map_zero]`.
-/
theorem sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (jc : Fin (N + 1)) (b : Fin (N + 1) → Ω)
    (hb : b jc = 1) (i : Fin (D + 1)) (hi : i ≠ 0) :
    ∑ j, sImg (D := D) jc (fun k => b (jc.succAbove k)) (i, j) *
      algebraMap Ω (OmS Ω D N) (b j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc]
  simp only [sImg, GaussValuationUniqueness.sac_same, GaussValuationUniqueness.sac_succAbove, if_neg hi, hb, map_one,
    mul_one]
  simp only [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum, ← map_add, neg_add_cancel, map_zero]

noncomputable def eS {Ω : Type} [Field Ω] {D N : ℕ} (jc j0 : Fin (N + 1)) (x : Fin N → Ω) :
    SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun ik => sImg jc x (ik.1, j0.succAbove ik.2))

section Fac

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_apply (y : vRing v) : (vRing v).subtype y = (y : Ω) := rfl

/- English proof (translation)
Establish `key : ((sHom (K` using `K) jc x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) : MvPolynomial (TVar D N) K →+* OmS Ω D N) = (MvPolynomial.eval₂Hom ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) (eS jc j0 x)).comp (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, sHom, MvPolynomial.aeval_C, psiT, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]`. Rewrite using `[IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N), IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N), MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`.

Both sides reduce to the same expression. Introduce and unpack `⟨i, j⟩`. Break down `Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩` into its components or cases. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Simplify using `[sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same]`. Establish `h` using `hrel i hi`. Rewrite `h` using `[Fin.sum_univ_succAbove _ j, ha0, map_one, mul_one]`. Simplify using `[sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same, hi, GaussValuationUniqueness.sub_apply]`. Take the linear combination `h`.

Simplify using `[sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_succAbove]`. Conclude with `RingHom.congr_fun key f`.
-/
theorem sHom_factor (hv : IsTrivOn K v) (jc j0 : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → Ω) (ha : ∀ j, a j ∈ vRing v) (ha0 : a j0 = 1)
    (hrel : ∀ i : Fin (D + 1), i ≠ 0 →
      ∑ j, sImg jc x (i, j) * algebraMap Ω (OmS Ω D N) (a j) = 0) (f : MvPolynomial (TVar D N) K) :
    sHom (K := K) jc x f = MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
      (eS jc j0 x) (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) := by
  have key : ((sHom (K := K) jc x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) :
      MvPolynomial (TVar D N) K →+* OmS Ω D N) =
      (MvPolynomial.eval₂Hom ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
        (eS jc j0 x)).comp (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, sHom,
        MvPolynomial.aeval_C, psiT, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rfl
    · rintro ⟨i, j⟩
      rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same]
        · have h := hrel i hi
          rw [Fin.sum_univ_succAbove _ j, ha0, map_one, mul_one] at h
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same, hi, GaussValuationUniqueness.sub_apply]
          linear_combination h
      · simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_succAbove]
  exact RingHom.congr_fun key f

end Fac

end GaussValuationUniqueness
