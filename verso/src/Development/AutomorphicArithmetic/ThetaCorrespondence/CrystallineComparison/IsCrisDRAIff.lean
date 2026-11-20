import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {A B P D : Type} [CommRing A] [CommRing B] [CommRing P] [CommRing D]
  [Algebra A B] [Algebra P D]

def IsCrisDRA (ι : A →+* P) (f : B →+* D) : Prop :=
  ∀ x : A, f (algebraMap A B x) = algebraMap P D (ι x)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf x6`. Take `⟨x, rfl⟩` from `cA.surjective x6`. Establish `h1 : cBc.symm (Formalism.Per6.cB l (cA x)) = algebraMap A B x`. Rewrite using `[← hB x, RingEquiv.symm_apply_apply]`.

Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`. Rewrite using `[h1, hf x, hD, hι]`. Introduce `hf x`. Apply `cD.injective` to reduce the goal to its premises. Establish `h2` using `hf (cA x)`.

Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h2`. Rewrite `h2` using `[← hB x, RingEquiv.symm_apply_apply]`. Rewrite using `[h2, hD, hι]`.
-/
theorem isCrisDRA_iff (cA : A ≃+* ACris.ACris ℂ_[l] l) (cBc : B ≃+* Formalism.Per6.Bcris l) (cP : P ≃+* Formalism.Per6.BdRp l)
    (cD : D ≃+* Formalism.Per6.BdR l) (ι : A →+* P)
    (hB : ∀ x : A, cBc (algebraMap A B x) = Formalism.Per6.cB l (cA x))
    (hD : ∀ y : P, cD (algebraMap P D y) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP y))
    (hι : ∀ x : A, cP (ι x) = ACris.iota ℂ_[l] l (cA x)) (f : B →+* D) :
    IsCrisDRA ι f ↔ Formalism.Per6.IsCrisDR l ((cD.toRingHom.comp f).comp cBc.symm.toRingHom) := by
  constructor
  · intro hf x6
    obtain ⟨x, rfl⟩ := cA.surjective x6
    have h1 : cBc.symm (Formalism.Per6.cB l (cA x)) = algebraMap A B x := by
      rw [← hB x, RingEquiv.symm_apply_apply]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [h1, hf x, hD, hι]
  · intro hf x
    apply cD.injective
    have h2 := hf (cA x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h2
    rw [← hB x, RingEquiv.symm_apply_apply] at h2
    rw [h2, hD, hι]

end Formalism.BasicNotions.CmpTie.Incl
