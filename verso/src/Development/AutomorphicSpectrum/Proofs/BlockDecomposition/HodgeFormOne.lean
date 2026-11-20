import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.HodgeFormUnit

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[CrystallineSemistableComparison.Onto.form, oneOm]`.
-/
theorem gForm_one {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) :
    CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0 = oneOm K (Sec q ⊤) := by
  apply Subtype.ext
  simp [CrystallineSemistableComparison.Onto.form, oneOm]

/- English proof (translation)
Set `Λ : CrystallineSemistableComparison.Om.L2.LiftsT q` to `{ v := fun T g => Function.surjInv Ideal.Quotient.mk_surjective (CrystallineSemistableComparison.Pb.ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (CrystallineSemistableComparison.Om.L2.inTop q T) g) hv := fun T g => Function.surjInv_eq _ _ }`. Take `⟨f, hf, hc, hz⟩` from `h 1 Fin.elim0 Λ`. Establish `hf' : f = (CrystallineSemistableComparison.Pb.toSq (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (0 : ℕ)) (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (((0 : ℕ) : ℤ) + 1)) fun T => T.pdPow_zero).pull …`. Use function extensionality and compare the values at `s`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `(hz s).trans ?_` and prove the remaining obligations. Establish `hv : (Λ.form 1 Fin.elim0 s : (s.obj (Fin.last 0)).B) = Λ.v _ 1`. Simplify using `[CrystallineSemistableComparison.Om.L2.LiftsT.form]`. Establish `hJ : Λ.v (s.obj (Fin.last 0)) 1 - 1 ∈ (s.obj (Fin.last 0)).J` using `Ideal.Quotient.eq.1 ((Λ.hv _ 1).trans ((map_one _).trans (map_one _).symm))`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Λ.form 1 Fin.elim0 s - 1 ∈ (s.obj (Fin.last 0)).pdPow 1`. Rewrite using `[hv]`. Conclude with `(s.obj (Fin.last 0)).J_le_pdPow_one hJ`. Establish `h1 : CrystallineSemistableComparison.HT.oneH q = e.symm (CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0)`. Use `Eq.trans ?_ hc.symm` and prove the remaining obligations.

Conclude with `congrArg Submodule.Quotient.mk (Subtype.ext hf'.symm)`. Rewrite using `[h1, LinearEquiv.apply_symm_apply, gForm_one]`.
-/
theorem e_oneH {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0) (h : CrystallineSemistableComparison.Om.L2.IsOmT q 0 e) :
    e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  let Λ : CrystallineSemistableComparison.Om.L2.LiftsT q :=
    { v := fun T g => Function.surjInv Ideal.Quotient.mk_surjective
        (CrystallineSemistableComparison.Pb.ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (CrystallineSemistableComparison.Om.L2.inTop q T) g)
      hv := fun T g => Function.surjInv_eq _ _ }
  obtain ⟨f, hf, hc, hz⟩ := h 1 Fin.elim0 Λ
  have hf' : f = (CrystallineSemistableComparison.Pb.toSq (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (0 : ℕ)) (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (((0 : ℕ) : ℤ) + 1))
      fun T => T.pdPow_zero).pullC 0 (fun s => (1 : (CrystallineSemistableComparison.Pb.thA (CrystallineSemistableComparison.smFun X q)).obj (s.obj (Fin.last 0)))) := by
    funext s
    apply Subtype.ext
    refine (hz s).trans ?_
    have hv : (Λ.form 1 Fin.elim0 s : (s.obj (Fin.last 0)).B) = Λ.v _ 1 := by
      simp [CrystallineSemistableComparison.Om.L2.LiftsT.form]
    have hJ : Λ.v (s.obj (Fin.last 0)) 1 - 1 ∈ (s.obj (Fin.last 0)).J :=
      Ideal.Quotient.eq.1 ((Λ.hv _ 1).trans ((map_one _).trans (map_one _).symm))
    refine Ideal.Quotient.eq.2 ?_
    change Λ.form 1 Fin.elim0 s - 1 ∈ (s.obj (Fin.last 0)).pdPow 1
    rw [hv]
    exact (s.obj (Fin.last 0)).J_le_pdPow_one hJ
  have h1 : CrystallineSemistableComparison.HT.oneH q = e.symm (CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0) := by
    refine Eq.trans ?_ hc.symm
    exact congrArg Submodule.Quotient.mk (Subtype.ext hf'.symm)
  rw [h1, LinearEquiv.apply_symm_apply, gForm_one]

end GlobalTheory.CompanionTheory.HodgeFormUnit
