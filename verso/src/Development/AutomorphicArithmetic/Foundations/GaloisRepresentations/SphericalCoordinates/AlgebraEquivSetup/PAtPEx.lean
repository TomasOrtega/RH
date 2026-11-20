import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `hK hU hO hL E _ _ _ A p _ hs`. Take `⟨Kq, hω, hKq, hgen⟩` from `hK E A`. Take `⟨s, iotaC, hsC⟩` from `hL E A.τ₀`. Use `haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective`. Use `haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by`.

Use `(AlgebraicClosure.isAlgebraic ℚ)` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Conclude with `Subsingleton.elim _ _`. Set `iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p` to `IsAlgClosed.lift`. Set `iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p` to `iotaA.toRingHom`.

Set `τ₁ : E →+* PadicAlgCl p` to `iotaP.comp s`. Take `⟨u, ρ, hover, hρ⟩` from `hU E A p hs Kq hω hgen τ₁`. Take `⟨m, emb, w, hw, hov, hinj, hall⟩` from `hO E p Kq u τ₁ hover`. Conclude with `⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall, iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w, s_P := fun x => by rw [hw]; rfl }⟩`.
-/
theorem UpperTheory.Gal.W2.Seed.pAtPEx :
    KqEx → UEx → OrbEx → LiftEx → AtPEx := by
  intro hK hU hO hL E _ _ _ A p _ hs
  obtain ⟨Kq, hω, hKq, hgen⟩ := hK E A
  obtain ⟨s, iotaC, hsC⟩ := hL E A.τ₀
  haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.isAlgebraic ℚ)
    · rfl
    · exact Subsingleton.elim _ _
  let iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  let iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p := iotaA.toRingHom
  let τ₁ : E →+* PadicAlgCl p := iotaP.comp s
  obtain ⟨u, ρ, hover, hρ⟩ := hU E A p hs Kq hω hgen τ₁
  obtain ⟨m, emb, w, hw, hov, hinj, hall⟩ := hO E p Kq u τ₁ hover
  exact ⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall,
           iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w,
           s_P := fun x => by rw [hw]; rfl }⟩
