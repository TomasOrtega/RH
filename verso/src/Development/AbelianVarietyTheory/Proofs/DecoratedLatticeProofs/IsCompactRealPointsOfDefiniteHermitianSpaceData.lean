import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

open scoped ComplexOrder

/- English proof (translation)
Break down `hG with hG | hG` into its components or cases. Conclude with `Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef hG h)`. Use `right`. Take `⟨hn, Q, hQ⟩` from `Formalism.UG.P.sig_data G p q h`. Establish `hp : p = 0`.

Assume the negation of the conclusion as `hp`. Establish `i : Fin p` using `⟨0, Nat.pos_of_ne_zero hp⟩`. Establish `h1` using `(hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl i)`. Rewrite `h1` using `[Matrix.mul_neg, Matrix.neg_mul, hQ]`. Simplify using `[Formalism.UG.Jpq] at h1`.

Conclude with `absurd h1 (by norm_num)`. Substitute `hp` using the available equality. Simplify using `at hn`. Rewrite using `[hn]`.
-/
theorem sig_eq_of_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) ∨ (p, q) = (0, n) := by
  rcases hG with hG | hG
  · exact Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef hG h)
  · right
    obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
    have hp : p = 0 := by
      by_contra hp
      have i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
      have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl i)
      rw [Matrix.mul_neg, Matrix.neg_mul, hQ] at h1
      simp [Formalism.UG.Jpq] at h1
      exact absurd h1 (by norm_num)
    subst hp
    simp at hn
    rw [hn]

/- English proof (translation)
Establish `hτ : ∀ τ, (gramAt D A τ).PosDef ∨ (-(gramAt D A τ)).PosDef`. Introduce `τ`. Establish `hp` using `(hx.cart τ).2.2`. Break down `hx.pm τ with h | h` into its components or cases. Use `left`.

Rewrite `hp` using `[h, Matrix.mul_one]`. Then use the resulting hypothesis. Use `right`. Rewrite `hp` using `[h, Matrix.mul_neg, Matrix.mul_one]`. Then use the resulting hypothesis. Introduce `σ`. Establish `hs` using `hx.sig σ`.

Establish `key : (A.sig σ).1 = A.rank ∧ (A.sig σ).2 = 0 ∨ (A.sig σ).1 = 0 ∧ (A.sig σ).2 = A.rank`. Take `⟨τ, rfl | rfl⟩` from `GlobalTheory.DefLiftMult.exists_tauE D σ`. Simplify `sig_eq_of_definite (hτ τ) hs` using `[Prod.ext_iff]`. Establish `e : A.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D A τ)ᴴᵀ`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite `hs` using `[e]`. Establish `hd : ((gramAt D A τ)ᴴᵀ).PosDef ∨ (-(gramAt D A τ)ᴴᵀ).PosDef`. Break down `hτ τ with h | h` into its components or cases. Conclude with `Or.inl h.conjTranspose.transpose`.

Use `right`. Use `h.conjTranspose.transpose` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_neg, Matrix.transpose_neg]`. Then use the resulting hypothesis. Simplify `sig_eq_of_definite hd hs` using `[Prod.ext_iff]`. Break down `key with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases.

Conclude with `Or.inl (Prod.ext h1 h2)`. Conclude with `Or.inr (Prod.ext h1 h2)`.
-/
theorem isDefinite_of_defSp {D : D7} {A : HSp D} (x : DefSp A) (hx : x.Is) : A.IsDefinite := by
  have hτ : ∀ τ, (gramAt D A τ).PosDef ∨ (-(gramAt D A τ)).PosDef := by
    intro τ
    have hp := (hx.cart τ).2.2
    rcases hx.pm τ with h | h
    · left
      rwa [h, Matrix.mul_one] at hp
    · right
      rwa [h, Matrix.mul_neg, Matrix.mul_one] at hp
  intro σ
  have hs := hx.sig σ
  have key : (A.sig σ).1 = A.rank ∧ (A.sig σ).2 = 0 ∨ (A.sig σ).1 = 0 ∧ (A.sig σ).2 = A.rank := by
    obtain ⟨τ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D σ
    · simpa [Prod.ext_iff] using sig_eq_of_definite (hτ τ) hs
    · have e : A.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D A τ)ᴴᵀ := by
        ext i j
        rfl
      rw [e] at hs
      have hd : ((gramAt D A τ)ᴴᵀ).PosDef ∨ (-(gramAt D A τ)ᴴᵀ).PosDef := by
        rcases hτ τ with h | h
        · exact Or.inl h.conjTranspose.transpose
        · right
          have := h.conjTranspose.transpose
          rwa [Matrix.conjTranspose_neg, Matrix.transpose_neg] at this
      simpa [Prod.ext_iff] using sig_eq_of_definite hd hs
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/- English proof (translation)
Introduce `_ _ x hx` and use `Formalism.IndefR.Eqv.isCompact_GinfC hx.sig (isDefinite_of_defSp x hx)`.
-/
theorem isCompact_ginfC_of_defSp : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) :=
  fun _ _ x hx => Formalism.IndefR.Eqv.isCompact_GinfC hx.sig (isDefinite_of_defSp x hx)

end GlobalTheory.SeeSaw

end
