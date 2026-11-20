import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc

variable {D : D7}

/- English proof (translation)
Use `sub_eq_zero.1 (hΦ.ext (a - b) (by rw [RingHom.map_sub, hi, sub_self]) (FiniteAdeleRing.ext _ fun Q => ?_))` and prove the remaining obligations. Rewrite using `[ev_sub, hf Q, sub_self]`. Both sides reduce to the same expression.
-/
theorem eq_of_ev {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {a b : AE D}
    (hi : infPart D a = infPart D b) (hf : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  refine sub_eq_zero.1 (hΦ.ext (a - b) (by rw [RingHom.map_sub, hi, sub_self]) (FiniteAdeleRing.ext _ fun Q => ?_))
  rw [ev_sub, hf Q, sub_self]
  rfl

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart h) (GlobalTheory.LFun.finPart_of_isPrimeIdem h) x hx`. Establish `hy' : ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) = GlobalTheory.LFun.compAt D.host.F w (finPart D ((GlobalTheory.LFun.locIdele D.host.F w y)⁻¹ : (AE D)ˣ))`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[hy, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Establish `a1 : Valued.v (y : w.adicCompletion D.host.E) ≤ 1`.

Rewrite using `[hy]`. Conclude with `(GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h1 w`. Establish `a2 : Valued.v ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) ≤ 1`. Rewrite using `[hy']`. Conclude with `(GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h2 w`.

Establish `hun : Formalism.L2.Host.IsUnitAt w y` using `GlobalTheory.UnramOver.val_eq_one_of_unit Valued.v (RingHom.id _) y a1 a2`. Use `hu y hun` as an intermediate fact. Conclude with `Circle.ext (congrArg Units.val this)`.
-/
theorem eq_one_of_supp {w : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {χ : (AE D)ˣ →* Circle}
    (h : Formalism.IndefR.Mult.IsPrimeIdem w e f) (hu : GlobalTheory.LFun.UnrAt χ w) (x : (AE D)ˣ)
    (hx : e * ((x : AE D) - 1) = (x : AE D) - 1) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : χ x = 1 := by
  obtain ⟨y, hy, rfl⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart h)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem h) x hx
  have hy' : ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) =
      GlobalTheory.LFun.compAt D.host.F w (finPart D ((GlobalTheory.LFun.locIdele D.host.F w y)⁻¹ : (AE D)ˣ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have a1 : Valued.v (y : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy]; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h1 w
  have a2 : Valued.v ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy']; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h2 w
  have hun : Formalism.L2.Host.IsUnitAt w y :=
    GlobalTheory.UnramOver.val_eq_one_of_unit Valued.v (RingHom.id _) y a1 a2
  have := hu y hun
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.UnramFromOnePrime

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ν _ hR v ε hε w hw hu x hx h1 h2`. Take `⟨Φ, hΦ⟩` from `exists_comp D`. Take `⟨e, f, hp⟩` from `exists_isPrimeIdem hΦ w`. Take `⟨hd, ε', hε', hf⟩` from `of_isPrimeIdem hΦ hp`. Rewrite `hε'` using `[hw]`.

Establish `pc` using `place_comp hΦ hε`. Establish `pc'` using `place_comp hΦ hε'`. Establish `hfε : f = algebraMap (AF D.host.F) (AE D) ε`. Rewrite using `[hf]`. Use `eq_of_ev hΦ (by rw [pc.1, pc'.1]) fun Q => ?_` and prove the remaining obligations.

Distinguish the cases in `hQ : Q.under (𝓞 D.host.F) = v`. Rewrite using `[pc.2.1 Q hQ, pc'.2.1 Q hQ]`. Rewrite using `[pc.2.2 Q hQ, pc'.2.2 Q hQ]`. Establish `hev : ∀ Q, Φ e Q = if Q = w then 1 else 0` using `fun Q => by split_ifs with hQ`. Rewrite using `[hQ]`.

Conclude with `hd.2.1`. Conclude with `hd.2.2 Q hQ`. Establish `hee : e * e = e` using `eq_of_ev hΦ (by rw [RingHom.map_mul, hd.1, zero_mul]) fun Q => by`. Rewrite using `[ev_mul, hev Q]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `key : (1 - e) * (1 - cA D e) * f = 0`. Break down `hp with ⟨-, hfe⟩ | ⟨hfe, -, -⟩` into its components or cases. Establish `hc2 : cA D e * cA D e = cA D e` using `by rw [← RingHom.map_mul, hee]`. Rewrite using `[hfe]`. Take the linear combination `(cA D e - 1) * hee + (e - 1) * hc2`.

Rewrite using `[hfe]`. Take the linear combination `(cA D e - 1) * hee`. Establish `hfc : cA D f = f` using `by rw [hfε]; exact cA_algebraMap ε`. Establish `hx' : f * ((x : AE D) - 1) = (x : AE D) - 1` using `by rw [hfε]; exact hx`. Establish `int1 : ∀ Q, Φ (x : AE D) Q ∈ Q.adicCompletionIntegers D.host.E` using `(hΦ.int _).1 h1`.

Establish `int2 : ∀ Q, Φ ((x⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E` using `(hΦ.int _).1 h2`. Take `⟨y, hy, hys⟩` from `GlobalTheory.UnrOffLevels.exists_glue hee x`. Establish `hxx : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1` using `Units.mul_inv x`. Establish `hyi : ((y⁻¹ : (AE D)ˣ) : AE D) = e * ((x⁻¹ : (AE D)ˣ) : AE D) + (1 - e)`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations.

Rewrite using `[hy]`. Take the linear combination `(e * e) * hxx + (2 - (x : AE D) - ((x⁻¹ : (AE D)ˣ) : AE D)) * hee`. Establish `cut_int : ∀ z : AE D, (∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E) → ∀ Q, Φ (e * z + (1 - e)) Q ∈ Q.adicCompletionIntegers D.host.E` using `fun z hz Q => by`. Rewrite using `[ev_add, ev_mul, ev_sub, ev_one, hev Q]`. Use `split_ifs`.

Rewrite using `[one_mul, sub_self, add_zero]`. Conclude with `hz Q`. Rewrite using `[zero_mul, sub_zero, zero_add]`. Conclude with `one_mem _`. Establish `iy1 : ∀ Q, Φ (y : AE D) Q ∈ Q.adicCompletionIntegers D.host.E` using `by rw [hy]; exact cut_int _ int1`.

Establish `iy2 : ∀ Q, Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E`. Rewrite using `[hyi]`. Conclude with `cut_int _ int2`. Establish `hνy : ν y = 1` using `eq_one_of_supp hp hu y hys ((hΦ.int _).2 iy1) ((hΦ.int _).2 iy2)`. Take `⟨z, hzdef⟩ : ∃ z : (AE D)ˣ, z = x * y⁻¹` from `⟨_, rfl⟩`.

Establish `iz1 : finPart D (z : AE D) ∈ intAE D` using `(hΦ.int _).2 fun Q => by`. Rewrite using `[hzdef, Units.val_mul, ev_mul]`. Conclude with `mul_mem (int1 Q) (iy2 Q)`. Establish `iz2 : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D` using `(hΦ.int _).2 fun Q => by`. Establish `hzi : (z⁻¹ : (AE D)ˣ) = y * x⁻¹` using `by rw [hzdef, _root_.mul_inv_rev, inv_inv y]`.

Rewrite using `[hzi, Units.val_mul, ev_mul]`. Conclude with `mul_mem (iy1 Q) (int2 Q)`. Establish `hz1 : (z : AE D) - 1 = (1 - e) * f * ((x : AE D) - 1)`. Establish `hzv : (z : AE D) = (x : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D)` using `by rw [hzdef, Units.val_mul]`. Rewrite using `[hzv, hyi]`.

Take the linear combination `e * hxx - (1 - e) * hx'`. Establish `hcz : cA D (z : AE D) - 1 = (1 - cA D e) * f * (cA D (x : AE D) - 1)`. Use `congrArg (cA D) hz1` as an intermediate fact. Simplify using `only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, hfc] at this`. Conclude with `this`.

Establish `hconj : ν (Units.map (cA D : AE D →* AE D) z) = (ν z)⁻¹` using `GlobalTheory.ConjAdjWeil.chi_conj hR z`. Take `⟨cz, hczdef⟩ : ∃ cz : (AE D)ˣ, cz = Units.map (cA D : AE D →* AE D) z` from `⟨_, rfl⟩`. Rewrite `hconj` using `[← hczdef]`. Establish `hcv : (cz : AE D) = cA D (z : AE D)` using `by rw [hczdef]; rfl`. Establish `hcvi : ((cz⁻¹ : (AE D)ˣ) : AE D) = cA D ((z⁻¹ : (AE D)ˣ) : AE D)` using `by rw [hczdef, ← map_inv]; rfl`.

Establish `hνcz : ν cz = 1`. Use `eq_one_of_supp hp hu cz ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hcv, hcz]`. Take the linear combination `(-(cA D (x : AE D) - 1)) * key`. Rewrite using `[hcv]`.

Conclude with `finPart_cA_mem iz1`. Rewrite using `[hcvi]`. Conclude with `finPart_cA_mem iz2`. Establish `hνz : ν z = 1` using `inv_eq_one.1 (hconj.symm.trans hνcz)`. Establish `hxyz : x = y * z` using `by rw [hzdef, mul_comm x, mul_inv_cancel_left]`.

Rewrite using `[hxyz, map_mul, hνy, hνz, one_mul]`.
-/
theorem unramAt_of_unrAt_one : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  classical
  intro D ν _ hR v ε hε w hw hu x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  obtain ⟨hd, ε', hε', hf⟩ := of_isPrimeIdem hΦ hp
  rw [hw] at hε'
  have pc := place_comp hΦ hε
  have pc' := place_comp hΦ hε'
  have hfε : f = algebraMap (AF D.host.F) (AE D) ε := by
    rw [hf]
    refine eq_of_ev hΦ (by rw [pc.1, pc'.1]) fun Q => ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [pc.2.1 Q hQ, pc'.2.1 Q hQ]
    · rw [pc.2.2 Q hQ, pc'.2.2 Q hQ]
  have hev : ∀ Q, Φ e Q = if Q = w then 1 else 0 := fun Q => by
    split_ifs with hQ
    · rw [hQ]; exact hd.2.1
    · exact hd.2.2 Q hQ
  have hee : e * e = e := eq_of_ev hΦ (by rw [RingHom.map_mul, hd.1, zero_mul]) fun Q => by
    rw [ev_mul, hev Q]
    split_ifs <;> simp
  have key : (1 - e) * (1 - cA D e) * f = 0 := by
    rcases hp with ⟨-, hfe⟩ | ⟨hfe, -, -⟩
    · have hc2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
      rw [hfe]
      linear_combination (cA D e - 1) * hee + (e - 1) * hc2
    · rw [hfe]
      linear_combination (cA D e - 1) * hee
  have hfc : cA D f = f := by rw [hfε]; exact cA_algebraMap ε
  have hx' : f * ((x : AE D) - 1) = (x : AE D) - 1 := by rw [hfε]; exact hx
  have int1 : ∀ Q, Φ (x : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h1
  have int2 : ∀ Q, Φ ((x⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h2
  obtain ⟨y, hy, hys⟩ := GlobalTheory.UnrOffLevels.exists_glue hee x
  have hxx : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv x
  have hyi : ((y⁻¹ : (AE D)ˣ) : AE D) = e * ((x⁻¹ : (AE D)ˣ) : AE D) + (1 - e) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy]
    linear_combination (e * e) * hxx + (2 - (x : AE D) - ((x⁻¹ : (AE D)ˣ) : AE D)) * hee
  have cut_int : ∀ z : AE D, (∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E) →
      ∀ Q, Φ (e * z + (1 - e)) Q ∈ Q.adicCompletionIntegers D.host.E := fun z hz Q => by
    rw [ev_add, ev_mul, ev_sub, ev_one, hev Q]
    split_ifs
    · rw [one_mul, sub_self, add_zero]; exact hz Q
    · rw [zero_mul, sub_zero, zero_add]; exact one_mem _
  have iy1 : ∀ Q, Φ (y : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by rw [hy]; exact cut_int _ int1
  have iy2 : ∀ Q, Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by
    rw [hyi]; exact cut_int _ int2
  have hνy : ν y = 1 := eq_one_of_supp hp hu y hys ((hΦ.int _).2 iy1) ((hΦ.int _).2 iy2)
  obtain ⟨z, hzdef⟩ : ∃ z : (AE D)ˣ, z = x * y⁻¹ := ⟨_, rfl⟩
  have iz1 : finPart D (z : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    rw [hzdef, Units.val_mul, ev_mul]; exact mul_mem (int1 Q) (iy2 Q)
  have iz2 : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    have hzi : (z⁻¹ : (AE D)ˣ) = y * x⁻¹ := by rw [hzdef, _root_.mul_inv_rev, inv_inv y]
    rw [hzi, Units.val_mul, ev_mul]; exact mul_mem (iy1 Q) (int2 Q)
  have hz1 : (z : AE D) - 1 = (1 - e) * f * ((x : AE D) - 1) := by
    have hzv : (z : AE D) = (x : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) := by rw [hzdef, Units.val_mul]
    rw [hzv, hyi]
    linear_combination e * hxx - (1 - e) * hx'
  have hcz : cA D (z : AE D) - 1 = (1 - cA D e) * f * (cA D (x : AE D) - 1) := by
    have := congrArg (cA D) hz1
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, hfc] at this
    exact this
  have hconj : ν (Units.map (cA D : AE D →* AE D) z) = (ν z)⁻¹ := GlobalTheory.ConjAdjWeil.chi_conj hR z
  obtain ⟨cz, hczdef⟩ : ∃ cz : (AE D)ˣ, cz = Units.map (cA D : AE D →* AE D) z := ⟨_, rfl⟩
  rw [← hczdef] at hconj
  have hcv : (cz : AE D) = cA D (z : AE D) := by rw [hczdef]; rfl
  have hcvi : ((cz⁻¹ : (AE D)ˣ) : AE D) = cA D ((z⁻¹ : (AE D)ˣ) : AE D) := by rw [hczdef, ← map_inv]; rfl
  have hνcz : ν cz = 1 := by
    refine eq_one_of_supp hp hu cz ?_ ?_ ?_
    · rw [hcv, hcz]
      linear_combination (-(cA D (x : AE D) - 1)) * key
    · rw [hcv]; exact finPart_cA_mem iz1
    · rw [hcvi]; exact finPart_cA_mem iz2
  have hνz : ν z = 1 := inv_eq_one.1 (hconj.symm.trans hνcz)
  have hxyz : x = y * z := by rw [hzdef, mul_comm x, mul_inv_cancel_left]
  rw [hxyz, map_mul, hνy, hνz, one_mul]

end GlobalTheory.UnramFromOnePrime

end
