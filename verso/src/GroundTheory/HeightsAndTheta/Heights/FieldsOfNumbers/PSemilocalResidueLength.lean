import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalResidueLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocResidue
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocalize
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW`. Use `hP'.isPrime` as an intermediate fact. Introduce `W' hW'`. Use `hW'.1.isPrime` as an intermediate fact. Use `haveI hfin := (hFR F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1`.

Establish `h𝒲` using `FibreFinite.proof F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW`. Take `⟨-, hPW', hc⟩` from `id hW'`. Substitute `hc` using the available equality. Take `⟨ρO, hρOv, hρOk, hρOr⟩` from `hRes F K' ι' P' W' hPW'`. Take `⟨ρA, hρAv, -, hρAr⟩` from `hRes F K (fun k => ι' (j k)) (contractPrime j P') _ hPW`.

Establish `hLE` using `map_homFracDegZero_le j ι' W'`. Establish `hBO` using `degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')`. Set `L` to `(homFracDegZero (contractPrime j W')).map (contractFracMap j W')`. Set `M` to `IntermediateField.extendScalars hLE`. Set `τ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →+* M` to `(ρO.comp (Subalgebra.inclusion hBO).toRingHom).codRestrict M (fun b => (hρOr _).mpr ⟨_, rfl⟩)`.

Set `σ : degZeroLoc (contractPrime j P') {contractPrime j W'} →+* L` to `((contractFracMap j W').toRingHom.comp ρA).codRestrict L (fun a => ⟨ρA a, (hρAr _).mpr ⟨a, rfl⟩, rfl⟩)`. Establish `hσs : Function.Surjective σ`. Introduce and unpack `⟨z, hz⟩`. Take `⟨w, hw, rfl⟩` from `hz`. Take `⟨a, rfl⟩` from `(hρAr w).mp hw`.

Conclude with `⟨a, rfl⟩`. Use `letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) L := σ.toAlgebra`. Use `letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) M := ((algebraMap L M).comp σ).toAlgebra`. Use `haveI : IsScalarTower (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hcomp : ∀ a : degZeroLoc (contractPrime j P') {contractPrime j W'}, τ (algebraMap _ _ a) = algebraMap _ M a`.

Introduce `a`. Take `⟨b, f, g, hf, hg, -, hgW, hx⟩` from `DegZeroLocQuot.proof F K (fun k => ι' (j k)) (contractPrime j P') {contractPrime j W'} (fun V hV => by rw [hV]; infer_instance) a.1 a.2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρO ⟨contractFracMap j P' a, _⟩ = contractFracMap j W' (ρA a)`. Rewrite using `[hρAv a b f g hf hg (hgW _ rfl) hx, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]`.

Apply `hρOv _ _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg) (hgW _ rfl)` to reduce the goal to its premises. Use `show contractFracMap j P' a = _`. Rewrite using `[hx, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]`. Set `τA : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M` to `{ τ with commutes' := hcomp }`. Establish `hmem : ∀ l : L, algebraMap L M l ∈ τ.rangeS`.

Introduce `l`. Take `⟨a, rfl⟩` from `hσs l`. Conclude with `⟨_, hcomp a⟩`. Set `R : Subalgebra L M` to `{ τ.rangeS with algebraMap_mem' := hmem }`. Establish `hsurj : Function.Surjective τ`.

Introduce and unpack `⟨z, hz⟩`. Take `⟨y, rfl⟩` from `(hρOr z).mp hz`. Take `⟨b, hb, s, hs, ⟨t, ht, hst⟩, hys⟩` from `hLoc F K' ι' P' hP' _ h𝒲 (fun V hV => ⟨hV.1, hV.2.1⟩) W' hW' y.1 y.2`. Establish `hs0 : τ ⟨s, hs⟩ ≠ 0`. Introduce `h0`.

Establish `h1 : ρO ⟨s, hBO hs⟩ * ρO ⟨t, ht⟩ = 1`. Rewrite using `[← map_mul, ← map_one ρO]`. Conclude with `congrArg ρO (Subtype.ext hst)`. Rewrite `h1` using `[show ρO ⟨s, hBO hs⟩ = 0 from congrArg Subtype.val h0, zero_mul]`. Conclude with `zero_ne_one h1`.

Establish `hint : IsIntegral L (τ ⟨s, hs⟩)` using `((Algebra.IsIntegral.isIntegral (R := degZeroLoc (contractPrime j P') {contractPrime j W'}) (⟨s, hs⟩ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')))).map τA).tower_top`. Take `⟨c, hc⟩` from `hint.inv_mem (A := R) ⟨⟨s, hs⟩, rfl⟩`. Establish `hbys : τ ⟨b, hb⟩ = ⟨ρO y, hz⟩ * τ ⟨s, hs⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρO ⟨b, hBO hb⟩ = ρO y * ρO ⟨s, hBO hs⟩`.

Rewrite using `[← map_mul]`. Conclude with `congrArg ρO (Subtype.ext hys.symm)`. Use `⟨⟨b, hb⟩ * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc, hbys, mul_inv_cancel_right₀ hs0]`. Use `⟨RingHom.ker τ, fun x => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]`. Conclude with `hρOk ⟨x, hBO x.2⟩`. Set `e : (degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) ⧸ RingHom.ker τ) ≃ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M` to `AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hsurj) (fun a => by`. Rewrite using `[← Ideal.Quotient.mk_algebraMap, RingHom.quotientKerEquivOfSurjective_apply_mk]`. Conclude with `hcomp a)`.

Use `haveI : Module.Finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) M := Module.Finite.of_surjective τA.toLinearMap hsurj`. Use `haveI : Module.Finite L M := Module.Finite.of_restrictScalars_finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M`. Use `e.toLinearEquiv.length_eq.trans ?_` and prove the remaining obligations. Rewrite using `[Module.length_eq_of_surjective (R := L) hσs, Module.length_eq_finrank, relDeg, IntermediateField.relfinrank_eq_finrank_of_le hLE]`.
-/
theorem SemilocalResidueLength.proof (hRes : DegZeroLocResidue.Statement.{u})
    (hFR : SemilocalFiniteRank.Statement.{u}) (hLoc : DegZeroLocLocalize.Statement.{u}) :
    SemilocalResidueLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  intro W' hW'
  have := hW'.1.isPrime
  haveI hfin := (hFR F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have h𝒲 := FibreFinite.proof F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  obtain ⟨-, hPW', hc⟩ := id hW'
  subst hc
  obtain ⟨ρO, hρOv, hρOk, hρOr⟩ := hRes F K' ι' P' W' hPW'
  obtain ⟨ρA, hρAv, -, hρAr⟩ := hRes F K (fun k => ι' (j k)) (contractPrime j P') _ hPW
  have hLE := map_homFracDegZero_le j ι' W'
  have hBO := degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
  let L := (homFracDegZero (contractPrime j W')).map (contractFracMap j W')
  let M := IntermediateField.extendScalars hLE
  let τ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →+* M :=
    (ρO.comp (Subalgebra.inclusion hBO).toRingHom).codRestrict M (fun b => (hρOr _).mpr ⟨_, rfl⟩)
  let σ : degZeroLoc (contractPrime j P') {contractPrime j W'} →+* L :=
    ((contractFracMap j W').toRingHom.comp ρA).codRestrict L
      (fun a => ⟨ρA a, (hρAr _).mpr ⟨a, rfl⟩, rfl⟩)
  have hσs : Function.Surjective σ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨a, rfl⟩ := (hρAr w).mp hw
    exact ⟨a, rfl⟩
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) L := σ.toAlgebra
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
    ((algebraMap L M).comp σ).toAlgebra
  haveI : IsScalarTower (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hcomp : ∀ a : degZeroLoc (contractPrime j P') {contractPrime j W'}, τ (algebraMap _ _ a) = algebraMap _ M a := by
    intro a
    obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K (fun k => ι' (j k))
      (contractPrime j P') {contractPrime j W'} (fun V hV => by rw [hV]; infer_instance) a.1 a.2
    apply Subtype.ext
    show ρO ⟨contractFracMap j P' a, _⟩ = contractFracMap j W' (ρA a)
    rw [hρAv a b f g hf hg (hgW _ rfl) hx, map_div₀, contractFracMap_algebraMap,
      contractFracMap_algebraMap]
    apply hρOv _ _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg) (hgW _ rfl)
    show contractFracMap j P' a = _
    rw [hx, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  let τA : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
    { τ with commutes' := hcomp }

  have hmem : ∀ l : L, algebraMap L M l ∈ τ.rangeS := by
    intro l
    obtain ⟨a, rfl⟩ := hσs l
    exact ⟨_, hcomp a⟩
  let R : Subalgebra L M := { τ.rangeS with algebraMap_mem' := hmem }
  have hsurj : Function.Surjective τ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (hρOr z).mp hz
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hys⟩ := hLoc F K' ι' P' hP' _ h𝒲
      (fun V hV => ⟨hV.1, hV.2.1⟩) W' hW' y.1 y.2
    have hs0 : τ ⟨s, hs⟩ ≠ 0 := by
      intro h0
      have h1 : ρO ⟨s, hBO hs⟩ * ρO ⟨t, ht⟩ = 1 := by
        rw [← map_mul, ← map_one ρO]
        exact congrArg ρO (Subtype.ext hst)
      rw [show ρO ⟨s, hBO hs⟩ = 0 from congrArg Subtype.val h0, zero_mul] at h1
      exact zero_ne_one h1
    have hint : IsIntegral L (τ ⟨s, hs⟩) :=
      ((Algebra.IsIntegral.isIntegral (R := degZeroLoc (contractPrime j P') {contractPrime j W'})
        (⟨s, hs⟩ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')))).map τA).tower_top
    obtain ⟨c, hc⟩ := hint.inv_mem (A := R) ⟨⟨s, hs⟩, rfl⟩
    have hbys : τ ⟨b, hb⟩ = ⟨ρO y, hz⟩ * τ ⟨s, hs⟩ := by
      apply Subtype.ext
      show ρO ⟨b, hBO hb⟩ = ρO y * ρO ⟨s, hBO hs⟩
      rw [← map_mul]
      exact congrArg ρO (Subtype.ext hys.symm)
    refine ⟨⟨b, hb⟩ * c, ?_⟩
    rw [map_mul, hc, hbys, mul_inv_cancel_right₀ hs0]
  refine ⟨RingHom.ker τ, fun x => ?_, ?_⟩
  · rw [RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]
    exact hρOk ⟨x, hBO x.2⟩
  · let e : (degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) ⧸ RingHom.ker τ) ≃ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
      AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hsurj) (fun a => by
        rw [← Ideal.Quotient.mk_algebraMap, RingHom.quotientKerEquivOfSurjective_apply_mk]
        exact hcomp a)
    haveI : Module.Finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
      Module.Finite.of_surjective τA.toLinearMap hsurj
    haveI : Module.Finite L M :=
      Module.Finite.of_restrictScalars_finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M
    refine e.toLinearEquiv.length_eq.trans ?_
    rw [Module.length_eq_of_surjective (R := L) hσs, Module.length_eq_finrank, relDeg,
      IntermediateField.relfinrank_eq_finrank_of_le hLE]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
