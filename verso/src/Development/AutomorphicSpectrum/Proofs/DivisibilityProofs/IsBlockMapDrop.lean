import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

/- English proof (translation)
Use `⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h`. Establish `h' : (⟨a, x⟩ : Σ k, PIdx j k) = ⟨b, y⟩` using `h`. Consider the cases of `h'`. Both sides reduce to the same expression.

Introduce and unpack `⟨k, x⟩ ⟨⟨k', hk⟩, rfl⟩`. Conclude with `⟨⟨⟨k', hk⟩, x⟩, rfl⟩`.
-/
theorem isBlockMap_drop (j : K → FlBlock Ψ N) (k₀ : K) :
    IsBlockMap (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
    have h' : (⟨a, x⟩ : Σ k, PIdx j k) = ⟨b, y⟩ := h
    cases h'
    rfl
  · rintro ⟨k, x⟩ ⟨⟨k', hk⟩, rfl⟩
    exact ⟨⟨⟨k', hk⟩, x⟩, rfl⟩

/- English proof (translation)
Establish `key : ∀ f : MRing (PIdx (dropJ j k₀)), mConeMap (yPart j) (rename (dropV j k₀) f) = rename Subtype.val (mConeMap (yPart (dropJ j k₀)) f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp [hp, hq]`.

Consider the case `mul_X p n hp`. Simplify using `only [map_mul, hp, rename_X]`. Use `congr 1`. Simplify using `[mConeMap, yPart, dropV, dropJ]`. Use extensionality with `f`.

Simplify using `only [imageZ, PPart, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]`. Use `show mConeMap (yPart j) (rename (dropV j k₀) f) = 0 ↔ _`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `rename_injective _ Subtype.val_injective (by rw [h, map_zero])`. Introduce `h`. Establish `h' : mConeMap (yPart (dropJ j k₀)) f = 0` using `h`. Rewrite using `[h', map_zero]`.
-/
theorem imageZ_drop [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    imageZ (dropV j k₀) (PPart j) = PPart (dropJ j k₀) := by
  have key : ∀ f : MRing (PIdx (dropJ j k₀)), mConeMap (yPart j) (rename (dropV j k₀) f) =
      rename Subtype.val (mConeMap (yPart (dropJ j k₀)) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, yPart, dropV, dropJ]
  ext f
  simp only [imageZ, PPart, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  show mConeMap (yPart j) (rename (dropV j k₀) f) = 0 ↔ _
  rw [key]
  constructor
  · intro h
    exact rename_injective _ Subtype.val_injective (by rw [h, map_zero])
  · intro h
    have h' : mConeMap (yPart (dropJ j k₀)) f = 0 := h
    rw [h', map_zero]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
