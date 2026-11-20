import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Substitute `hde` using the available equality. Establish `hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f = DirichletCharacter.changeLevel hd (φ.ringHomComp f)`. Use extensionality with `u`. Simplify using `[MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]`. Establish `hψ : ψ = φ.ringHomComp f` using `DirichletCharacter.changeLevel_injective hd (h.trans hc)`.

Substitute `hψ` using the available equality. Simplify using `[MulChar.ringHomComp_apply]`.
-/
private theorem change_level_value_eq {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S)
    {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N) (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f) (a : ℕ) :
    ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst hde
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f = DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ : ψ = φ.ringHomComp f := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  subst hψ
  simp [MulChar.ringHomComp_apply]

/- English proof (translation)
Introduce `R S _ _ N _ f hf χ`. Establish `hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker`. Use extensionality with `u`. Simplify using `only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `hf (h.trans (map_one f).symm)`. Introduce `h`. Rewrite using `[h, map_one]`. Establish `hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet`.

Use extensionality with `d`. Simplify using `only [DirichletCharacter.mem_conductorSet_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `(DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h`.

Rewrite `h'` using `[hker]`. Conclude with `(DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'`. Introduce `h`. Establish `h'` using `(DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h`. Rewrite `h'` using `[← hker]`.

Conclude with `(DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'`. Establish `hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor`. Unfold `DirichletCharacter.conductor`. Rewrite using `[hset]`. Use `⟨hcond, ?_, hker⟩` and prove the remaining obligations.

Introduce `a`. Unfold `primVal`. Conclude with `change_level_value_eq f hcond χ.conductor_dvd_level (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f)) χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f)) (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_ …`.
-/
theorem UpperTheory.V.Bern.b_condmap :
    ∀ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ χ : DirichletCharacter R N, DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor ∧ (∀ a : ℕ, primVal (χ.ringHomComp f) a = f (primVal χ a)) ∧ (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  intro R S _ _ N _ f hf χ
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [← hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
  have hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
    unfold DirichletCharacter.conductor
    rw [hset]
  refine ⟨hcond, ?_, hker⟩
  intro a
  unfold primVal
  exact change_level_value_eq f hcond χ.conductor_dvd_level (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f))
    χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f))
    (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_primitiveCharacter]) a
