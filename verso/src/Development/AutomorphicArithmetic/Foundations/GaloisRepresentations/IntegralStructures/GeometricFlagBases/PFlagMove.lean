import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `Γ k _ _ d ρ W P W' hW' hJH`. Establish `hPP : ∀ w : Fin d → k, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) = w`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hPP' : ∀ w : Fin d → k, (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec w) = w`.

Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hc : ∀ g v, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec v) = (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec v)`. Introduce `g v`. Rewrite using `[cj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP]`.

Use `⟨fun i g v hv => ?_, fun i U hU h1 h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[hW', hc]`. Conclude with `hJH.1 i g _ ((hW' i v).1 hv)`. Set `U0 : Submodule k (Fin d → k)` to `U.map (Matrix.mulVecLin (↑P : Matrix (Fin d) (Fin d) k))`. Establish `hmem : ∀ v, v ∈ U ↔ (↑P : Matrix (Fin d) (Fin d) k).mulVec v ∈ U0`.

Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨v, hv, rfl⟩`. Introduce and unpack `⟨u, hu, he⟩`.

Establish `huv : u = v`. Use `congrArg (fun w => (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) he` as an intermediate fact. Simplify `this` using `[Matrix.mulVecLin_apply, hPP']`. Conclude with `huv ▸ hu`. Establish `hinv : IsInv ρ U0`.

Introduce and unpack `g w ⟨u, hu, rfl⟩`. Use `⟨(↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec u, hU g u hu, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply]`. Conclude with `hc g u`. Establish `hlo : W i ≤ U0`.

Introduce `w hw`. Use `⟨(↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w, h1 ((hW' i _).2 (by rw [hPP]; exact hw)), ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply]`. Conclude with `hPP w`. Establish `hhi : U0 ≤ W (i + 1)`.

Introduce and unpack `w ⟨u, hu, rfl⟩`. Conclude with `(hW' (i + 1) u).1 (h2 hu)`. Break down `hJH.2 i U0 hinv hlo hhi with h | h` into its components or cases. Use `left`. Use extensionality with `v`.

Rewrite using `[hmem, h, hW']`. Use `right`. Use extensionality with `v`. Rewrite using `[hmem, h, hW']`.
-/
theorem UpperTheory.Gal.Int.Geo.flagMove_of :
    FlagMove := by
  intro Γ k _ _ d ρ W P W' hW' hJH
  have hPP : ∀ w : Fin d → k, (↑P : Matrix (Fin d) (Fin d) k).mulVec
      ((↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPP' : ∀ w : Fin d → k, (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec
      ((↑P : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hc : ∀ g v, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec v) =
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec v) := by
    intro g v
    rw [cj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP]
  refine ⟨fun i g v hv => ?_, fun i U hU h1 h2 => ?_⟩
  · rw [hW', hc]
    exact hJH.1 i g _ ((hW' i v).1 hv)
  · let U0 : Submodule k (Fin d → k) := U.map (Matrix.mulVecLin (↑P : Matrix (Fin d) (Fin d) k))
    have hmem : ∀ v, v ∈ U ↔ (↑P : Matrix (Fin d) (Fin d) k).mulVec v ∈ U0 := by
      intro v
      constructor
      · intro hv
        exact ⟨v, hv, rfl⟩
      · rintro ⟨u, hu, he⟩
        have huv : u = v := by
          have := congrArg (fun w => (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) he
          simpa [Matrix.mulVecLin_apply, hPP'] using this
        exact huv ▸ hu
    have hinv : IsInv ρ U0 := by
      rintro g w ⟨u, hu, rfl⟩
      refine ⟨(↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec u, hU g u hu, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hc g u
    have hlo : W i ≤ U0 := by
      intro w hw
      refine ⟨(↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w, h1 ((hW' i _).2 (by rw [hPP]; exact hw)), ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hPP w
    have hhi : U0 ≤ W (i + 1) := by
      rintro w ⟨u, hu, rfl⟩
      exact (hW' (i + 1) u).1 (h2 hu)
    rcases hJH.2 i U0 hinv hlo hhi with h | h
    · left
      ext v
      rw [hmem, h, hW']
    · right
      ext v
      rw [hmem, h, hW']
