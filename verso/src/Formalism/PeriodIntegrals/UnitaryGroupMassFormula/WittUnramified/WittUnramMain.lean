import Mathlib
import Formalism.PeriodIntegrals.WittUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.GhostComponentG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.PsiStep

noncomputable section

namespace PI.WittUnramWork

open WittVector

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
private theorem map_frobenius' {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : WittVector p R) :
    WittVector.map g (WittVector.frobenius x) = WittVector.frobenius (WittVector.map g x) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Equip the data with the indicated structure.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Equip the data with the indicated structure.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem wittUnram_main : PI.WittUnram := by
  intro p f _ W Qq _ _ _ _ _ σ hfrac hirr hcard hcomp hσ
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hF : ∀ x : W, ∃ y : W, sigW hinj σ hσ x = x ^ p + (p : W) * y := sigW_lift hinj σ hσ
  set I : Ideal W := Ideal.span {(p : W)} with hI
  haveI hmax : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ I) := Ideal.Quotient.field I
  have hp0 : ((p : ℕ) : W ⧸ I) = 0 := by
    have h : Ideal.Quotient.mk I (p : W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rwa [map_natCast] at h
  haveI hchar : CharP (W ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  haveI hfin : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨e⟩ : Nonempty ((W ⧸ I) ≃+* GaloisField p f) := by
    letI : Algebra (ZMod p) (W ⧸ I) := (ZMod.castHom (dvd_refl p) (W ⧸ I)).toAlgebra
    exact ⟨(GaloisField.algEquivGaloisField p f hcard).toRingEquiv⟩
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq) p]
    exact fun h => hirr.ne_zero (hinj (h.trans (map_zero _).symm))
  letI : Invertible ((p : ℕ) : Qq) := invertibleOfNonzero hpQ
  let ψ : W →+* WittVector p (W ⧸ I) :=
    (WittVector.map (Ideal.Quotient.mk I)).comp (sHom p Qq (sigW hinj σ hσ) hF hinj)
  have h0 : ∀ x, (ψ x).coeff 0 = Ideal.Quotient.mk I x := by
    intro x
    show (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj x)).coeff 0 = _
    rw [WittVector.map_coeff, sHom_coeff_zero]
  have hψi : Function.Injective ψ := psi_injective ψ hirr
  have hψs : Function.Surjective ψ :=
    psi_surjective ψ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective h0 hcomp
  let χ : W →+* WittVector p (GaloisField p f) := (WittVector.map (e : (W ⧸ I) →+* GaloisField p f)).comp ψ
  have hχ : Function.Bijective χ :=
    ⟨(WittVector.map_injective _ e.injective).comp hψi, (WittVector.map_surjective _ e.surjective).comp hψs⟩
  have hφ : ∀ w, (RingEquiv.ofBijective χ hχ).symm (χ w) = w := by
    intro w
    have h := (RingEquiv.ofBijective χ hχ).symm_apply_apply w
    rwa [RingEquiv.ofBijective_apply] at h
  have hfrob : ∀ w, WittVector.frobenius (χ w) = χ (sigW hinj σ hσ w) := by
    intro w
    show _ = WittVector.map (e : (W ⧸ I) →+* GaloisField p f)
      (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj (sigW hinj σ hσ w)))
    rw [sHom_frob, map_frobenius', map_frobenius']
    rfl
  refine ⟨(RingEquiv.ofBijective χ hχ).symm, ?_⟩
  intro x
  obtain ⟨w, rfl⟩ := hχ.2 x
  rw [hfrob, hφ, hφ]
  exact (sigW_spec hinj σ hσ w).symm

end PI.WittUnramWork
