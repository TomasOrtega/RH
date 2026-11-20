import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFinPart

/- English proof (translation)
Establish `key` using `GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)`. Take `⟨y, rfl⟩` from `GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx`. Rewrite using `[map_pow]`. Conclude with `key y`.
-/
theorem eq_one_of_finPart_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (h : ChrEq c χ)
    {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [map_pow]
  exact key y

/- English proof (translation)
Unfold `IsDetRoot at *`. Rewrite using `[Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]`. Use `conv_lhs => rw [hx, hx']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isDetRoot_mul' {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

/- English proof (translation)
Take `⟨y, hyi, hyf⟩` from `GlobalTheory.PlaceIdem.parts_surj D (infPart D (z : AE D)) 1`. Take `⟨y', hyi', hyf'⟩` from `GlobalTheory.PlaceIdem.parts_surj D (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1`. Establish `hyy : y * y' = 1` using `GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, hyi, hyi', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one]) (by rw [RingHom.map_mul, hyf, hyf', mul_one, RingHom.map_one])`. Establish `hc : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w)` using `fun w => GlobalTheory.PlaceIdem.infPart_cA D w`. Establish `hf : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w)` using `fun w => GlobalTheory.PlaceIdem.finPart_cA D w`.

Establish `e2 : finPart D (matHom V a).1.det = 1`. Establish `e : finPart D (matHom V a).1.det = (finHom V a).1.det` using `(finPart D).map_det _`. Rewrite using `[e, ha]`. Simplify using the standard rewrite rules. Use `⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, hyf, ?_⟩` and prove the remaining obligations.

Use `show y = (matHom V a).1.det * sigR (AF D.host.F) D.sp.cm.sig y`. Use `GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_` and prove the remaining obligations. Establish `h1` using `congrArg (infPart D) hz`. Unfold `IsDetRoot at h1`. Rewrite `h1` using `[RingHom.map_mul, hc]`.

Rewrite using `[RingHom.map_mul, hc, hyi]`. Conclude with `h1`. Rewrite using `[RingHom.map_mul, hf, hyf, e2, RingHom.map_one, one_mul]`.
-/
theorem exists_isDetRoot_finPart_one {D : D7} (V : HSp D) (a : GA D V) (ha : finHom V a = 1) (z : (AE D)ˣ)
    (hz : IsDetRoot V a z) : ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot V a y := by
  obtain ⟨y, hyi, hyf⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D (z : AE D)) 1
  obtain ⟨y', hyi', hyf'⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1
  have hyy : y * y' = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, hyi, hyi', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
    (by rw [RingHom.map_mul, hyf, hyf', mul_one, RingHom.map_one])
  have hc : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) := fun w => GlobalTheory.PlaceIdem.infPart_cA D w
  have hf : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := fun w => GlobalTheory.PlaceIdem.finPart_cA D w
  have e2 : finPart D (matHom V a).1.det = 1 := by
    have e : finPart D (matHom V a).1.det = (finHom V a).1.det := (finPart D).map_det _
    rw [e, ha]
    simp
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, hyf, ?_⟩
  show y = (matHom V a).1.det * sigR (AF D.host.F) D.sp.cm.sig y
  refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
  · have h1 := congrArg (infPart D) hz
    unfold IsDetRoot at h1
    rw [RingHom.map_mul, hc] at h1
    rw [RingHom.map_mul, hc, hyi]
    exact h1
  · rw [RingHom.map_mul, hf, hyf, e2, RingHom.map_one, one_mul]

/- English proof (translation)
Establish `ha : finHom V (h⁻¹ * h') = 1` using `by rw [map_mul, map_inv, hh, inv_mul_cancel]`. Take `⟨x, hx⟩` from `hd.1 h`. Take `⟨z, hz⟩` from `hd.1 (h⁻¹ * h')`. Take `⟨y, hy1, hy⟩` from `exists_isDetRoot_finPart_one V _ ha z hz`. Establish `hxy` using `isDetRoot_mul' V h (h⁻¹ * h') x y hx hy`.

Rewrite `hxy` using `[mul_inv_cancel_left]`. Rewrite using `[hd.2 h x hx, hd.2 h' _ hxy, map_mul, hχ y hy1, mul_one]`.
-/
theorem eq_of_finHom_of_triv {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hχ : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → χ y = 1) (dd : GA D V → ℂ) (hd : MuVal V χ dd)
    (h h' : GA D V) (hh : finHom V h = finHom V h') : dd h = dd h' := by
  have ha : finHom V (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
  obtain ⟨x, hx⟩ := hd.1 h
  obtain ⟨z, hz⟩ := hd.1 (h⁻¹ * h')
  obtain ⟨y, hy1, hy⟩ := exists_isDetRoot_finPart_one V _ ha z hz
  have hxy := isDetRoot_mul' V h (h⁻¹ * h') x y hx hy
  rw [mul_inv_cancel_left] at hxy
  rw [hd.2 h x hx, hd.2 h' _ hxy, map_mul, hχ y hy1, mul_one]

/- English proof (translation)
Introduce `D V pd k _ σ δ δc hT dd hdd h h' hh`. Take `⟨hc, ⟨n, hn, ho⟩, -⟩` from `hT`. Establish `h1 : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → δc y = 1` using `eq_one_of_finPart_eq_one D δc δ hc hn ho`. Break down `hdd with hd | hd` into its components or cases. Conclude with `eq_of_finHom_of_triv V δc h1 dd hd h h' hh`.

Conclude with `eq_of_finHom_of_triv V δc⁻¹ (fun y hy => by rw [MonoidHom.inv_apply, h1 y hy, inv_one]) dd hd h h' hh`.
-/
theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ)
    (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ,
    (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := by
  intro D V pd k _ σ δ δc hT dd hdd h h' hh
  obtain ⟨hc, ⟨n, hn, ho⟩, -⟩ := hT
  have h1 : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → δc y = 1 := eq_one_of_finPart_eq_one D δc δ hc hn ho
  rcases hdd with hd | hd
  · exact eq_of_finHom_of_triv V δc h1 dd hd h h' hh
  · exact eq_of_finHom_of_triv V δc⁻¹ (fun y hy => by rw [MonoidHom.inv_apply, h1 y hy, inv_one]) dd hd h h' hh

end GlobalTheory.TwistFinPart
