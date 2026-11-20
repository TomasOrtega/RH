import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero

noncomputable section

open Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ChiGrid
open GlobalTheory.SqTop (twPl Qn)
open GlobalTheory.Square (IsAwayUnit)
open GlobalTheory.RowTest (LocIn NumbersIn)

namespace GlobalTheory.KappaArith

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isAwayUnit_of_pow_eq_one {K : Type} [Field K] (m : ℕ) {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsAwayUnit m z := by
  have hint : IsIntegral ℤ z :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hz]⟩
  let a : 𝓞 K := ⟨z, hint⟩
  have ha : (a : K) = z := rfl
  refine ⟨a, 0, 0, ⟨a ^ (n - 1), ?_⟩, by simp [ha]⟩
  rw [pow_zero]
  apply RingOfIntegers.ext
  have e1 : ((a * a ^ (n - 1) : 𝓞 K) : K) = z * z ^ (n - 1) := by rw [← ha]; norm_cast
  rw [e1, ← pow_succ', Nat.sub_add_cancel hn, hz]
  rfl

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)

def AwayIm (D : D7) (m : ℕ) (z : ℂ) : Prop := ∃ ζ : D.what₂.LL, IsAwayUnit m ζ ∧ D.what₂.embLL ζ = z

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem awayIm_one (m : ℕ) : AwayIm D m 1 := ⟨1, IsAwayUnit.one m, map_one _⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem AwayIm.mul {m : ℕ} {z z' : ℂ} (h : AwayIm D m z) (h' : AwayIm D m z') : AwayIm D m (z * z') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AwayIm.prod {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, AwayIm D m (f i)) :
    AwayIm D m (∏ i ∈ s, f i) :=
  Finset.prod_induction f (AwayIm D m) (fun _ _ => AwayIm.mul) (awayIm_one m) h

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem awayIm_val {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (w.adicCompletion D.host.E)ˣ) :
    AwayIm D m ((Lc.xiH t).loc w x : ℂ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨ζ, hζ⟩ := hx w x
  have h1 : ((Lc.xiH t).loc w x) ^ n = 1 := by
    have : ((Lc.xiH t) ^ n).loc w x = 1 := by rw [show (Lc.xiH t) ^ n = 1 from ho]; rfl
    exact this
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.KappaArith

end
