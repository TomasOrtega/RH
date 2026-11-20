import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `haveI := v.isMaximal`. Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`. Use `letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _`. Conclude with `CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _`.
-/
theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `ringChar.Nat.cast_ringChar`.
-/
theorem residueCharacteristic_mem (v : HeightOneSpectrum (𝓞 F)) : ((resP v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

/- English proof (translation)
Take `⟨j, hj⟩` from `GlobalTheory.PlaceBridge.exists_embedding (l := p) F (AlgebraicClosure F) v ε.O hv (GlobalTheory.TrueGeo.ExtConj.lies_over ε)`. Establish `h : ∃ io : AlgebraicClosure F →+* ℂ_[p], ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O` using `⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp j, fun a => by`. Rewrite using `[hj, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]⟩`. Conclude with `Classical.epsilon_spec h`.
-/
theorem ioOf_le_one_iff (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (hv : (p : 𝓞 F) ∈ v.asIdeal) (ε : Ext v) :
    ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F (AlgebraicClosure F) v ε.O hv
    (GlobalTheory.TrueGeo.ExtConj.lies_over ε)
  have h : ∃ io : AlgebraicClosure F →+* ℂ_[p], ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O :=
    ⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp j, fun a => by
      rw [hj, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]⟩
  exact Classical.epsilon_spec h

/- English proof (translation)
Set `u : AbsoluteValue (AlgebraicClosure F) ℝ` to `(NormedField.toAbsoluteValue ℂ_[p]).comp io.injective`. Establish `hu (x) : u x = ‖io x‖` using `rfl`. Establish `he : u.IsEquiv ε.w` using `AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules.

Establish `h1 : u x⁻¹ ≤ 1 ↔ ε.w x⁻¹ ≤ 1` using `by rw [hu, h, ε.mem_O]`. Rewrite `h1` using `[map_inv₀, map_inv₀, inv_le_one₀ (u.pos hx), inv_le_one₀ (ε.w.pos hx)]`. Rewrite using `[← not_le, ← not_le, h1]`. Take `⟨c, hc, hce⟩` from `AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he`. Establish `hw (x) : Real.log (ε.w x) = c * Real.log ‖io x‖`.

Rewrite using `[← congrFun hce x, hu]`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `[Real.zero_rpow hc.ne']`. Conclude with `Real.log_rpow (norm_pos_iff.2 ((map_ne_zero io).2 hx)) c`. Establish `hn : ‖io p‖ = (p : ℝ)⁻¹`.

Rewrite using `[map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']`. Simplify using the standard rewrite rules. Establish `hl : Real.log p ≠ 0` using `(Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'`. Rewrite using `[hw, hw, hn, Real.log_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_w_eq (p : ℕ) [hp : Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (io : AlgebraicClosure F →+* ℂ_[p]) (h : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (a : AlgebraicClosure F) :
    Real.log (ε.w a) = (-Real.log (ε.w p) / Real.log p) * Real.log ‖io a‖ := by
  let u : AbsoluteValue (AlgebraicClosure F) ℝ := (NormedField.toAbsoluteValue ℂ_[p]).comp io.injective
  have hu (x) : u x = ‖io x‖ := rfl
  have he : u.IsEquiv ε.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have h1 : u x⁻¹ ≤ 1 ↔ ε.w x⁻¹ ≤ 1 := by rw [hu, h, ε.mem_O]
      rw [map_inv₀, map_inv₀, inv_le_one₀ (u.pos hx), inv_le_one₀ (ε.w.pos hx)] at h1
      rw [← not_le, ← not_le, h1]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hw (x) : Real.log (ε.w x) = c * Real.log ‖io x‖ := by
    rw [← congrFun hce x, hu]
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hc.ne']
    · exact Real.log_rpow (norm_pos_iff.2 ((map_ne_zero io).2 hx)) c
  have hn : ‖io p‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [hw, hw, hn, Real.log_inv]
  field_simp

/- English proof (translation)
The claim follows from `Fact.mk hp; (∀ a, ‖ioOf (resP v) ε a‖ ≤ 1 ↔ a ∈ ε.O) ∧ ∀ a, Real.log (ε.w a) = (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log ‖ioOf (resP v) ε a‖ := fun _ _ _ v ε => ⟨residueCharacteristic_prime v, by haveI := Fact.mk (residueCharacteristic_prime v) exact ⟨ioOf_le_one_ …`.
-/
theorem ioOf_spec : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v), ∃ hp : (resP v).Prime, haveI := Fact.mk hp; (∀ a, ‖ioOf (resP v) ε a‖ ≤ 1 ↔ a ∈ ε.O) ∧ ∀ a, Real.log (ε.w a) = (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log ‖ioOf (resP v) ε a‖ := fun _ _ _ v ε =>
  ⟨residueCharacteristic_prime v, by
    haveI := Fact.mk (residueCharacteristic_prime v)
    exact ⟨ioOf_le_one_iff _ (residueCharacteristic_mem v) ε, log_w_eq _ ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)⟩⟩

end GlobalTheory.ShFam.Pad
