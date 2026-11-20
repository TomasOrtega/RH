import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSliceLineSumEqIntertwinerImageStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticePairCharacterIndicatorTransformEqCosetIndStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumBoxTensorLineOverVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.LastTarget

/- English proof (translation)
Use `letI : MeasurableSpace k := borel k`. Use `haveI : BorelSpace k := ⟨rfl⟩`. Establish `h` using `((GlobalTheory.LastSteps.lastTwoSteps k n n n'').2.2.2 q Q.lat Λ).1 ⟨(c • Q).red, (c • Q).red_ne⟩`. Use function extensionality and compare the values at `x`. Establish `hx : withRow (x.submatrix Sum.inl id) (x (Sum.inr 0)) = x`.

Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Both sides reduce to the same expression. Use `fin_cases i`. Both sides reduce to the same expression.

Establish `h2` using `(h (x.submatrix Sum.inl id) (x (Sum.inr 0))).2`. Rewrite `h2` using `[hx]`. Conclude with `h2.symm`.
-/
theorem tensRow_eq_phiOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (q : Unif k) (Q : Pair k n)
    (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (c : 𝓀[k]ˣ) :
    tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (c • Q).red) = phiOne (c • Q) (lastPair q Λ) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have h := ((GlobalTheory.LastSteps.lastTwoSteps k n n n'').2.2.2 q Q.lat Λ).1 ⟨(c • Q).red, (c • Q).red_ne⟩
  funext x
  have hx : withRow (x.submatrix Sum.inl id) (x (Sum.inr 0)) = x := by
    ext i j
    rcases i with i | i
    · rfl
    · fin_cases i; rfl
  have h2 := (h (x.submatrix Sum.inl id) (x (Sum.inr 0))).2
  rw [hx] at h2
  exact h2.symm

end GlobalTheory.LastTarget

namespace GlobalTheory.LastTarget

/- English proof (translation)
Introduce `h`. Establish `h0` using `congrFun h 0`. Establish `hne : ∀ a, χ a ≠ 0` using `fun a ha => by`. Establish `h1` using `AddChar.map_add_eq_mul χ a (-a)`. Rewrite `h1` using `[add_neg_cancel, AddChar.map_zero_eq_one, ha, zero_mul]`.

Conclude with `one_ne_zero h1`. Simplify using `only [charInd, vecInd, Q.lat.zero_mem, if_true, mul_one, Pi.zero_apply] at h0`. Conclude with `hne _ h0`.
-/
theorem charInd_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hne : ∀ a, χ a ≠ 0 := fun a ha => by
    have h1 := AddChar.map_add_eq_mul χ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, ha, zero_mul] at h1
    exact one_ne_zero h1
  simp only [charInd, vecInd, Q.lat.zero_mem, if_true, mul_one, Pi.zero_apply] at h0
  exact hne _ h0

/- English proof (translation)
Introduce `D k _ _ _ _ p q ψ hψ hU χ hχ hc n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG`. Take `⟨ε, hε⟩` from `GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator D k p q ψ hψ hU χ hχ hc n L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG`. Use `⟨ε, ?_⟩` and prove the remaining obligations. Introduce `α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u`. Take `⟨g₁, T₁, hg₁, hT₁, hT₁a⟩` from `GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ (charInd (resChar χ hχ q) Q) (charInd_ne_zero _ Q) LS hLS L₁ L₂ f₁ Ξ hΞ u`.

Take `⟨g₃, T₃, hg₃, hT₃, hT₃b⟩` from `hε β LS hLS Q g₁ T₁ hg₁ hT₁`. Establish `hO2 : Over ψ β γ LS LT Φ₂ (latInd Q.lat Λ) Φ₂` using `((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n'' n ψ hψ S T β γ LS LT hLS hLT Φ₂ hΦ₂).2.2 hU Q.lat Λ hβQ hγΛ`. Establish `hrow` using `tensRow_eq_phiOne q Q Λ ε`. Establish `hSB : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) ∈ SB (Matrix (n'' ⊕ Fin 1) n k)` using `hrow ▸ GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _`. Take `⟨g, hg⟩` from `GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum D k p n n'' ψ hψ hU S X T L'' o'' ζ₀ hζ₀ β γ γ₀ hγ LS LT LX hLS hLT hLX Φ₂ Φ₂ (latInd Q.lat Λ) hO2 (cosetInd q Q.lat (ε • Q).red) g₃ T₃ hg₃ hT₃ hSB`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrow]`. Establish `hl : lastBi o o'' τ Ξ Φ₂ u = o''.boxT S Φ₂ (T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red)))`. Rewrite using `[hT₃b, hT₁a]`. Both sides reduce to the same expression.

Rewrite using `[hl]`. Conclude with `hg`.
-/
theorem lastTarget : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator D k p q ψ hψ hU χ hχ hc n L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
  obtain ⟨g₁, T₁, hg₁, hT₁, hT₁a⟩ := GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ
    (charInd (resChar χ hχ q) Q) (charInd_ne_zero _ Q) LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃b⟩ := hε β LS hLS Q g₁ T₁ hg₁ hT₁
  have hO2 : Over ψ β γ LS LT Φ₂ (latInd Q.lat Λ) Φ₂ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n'' n ψ hψ S T β γ LS LT hLS hLT Φ₂ hΦ₂).2.2 hU Q.lat Λ hβQ hγΛ
  have hrow := tensRow_eq_phiOne q Q Λ ε
  have hSB : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) ∈ SB (Matrix (n'' ⊕ Fin 1) n k) :=
    hrow ▸ GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _
  obtain ⟨g, hg⟩ := GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum D k p n n'' ψ hψ hU S X T L'' o'' ζ₀ hζ₀ β γ γ₀ hγ LS LT LX hLS hLT hLX Φ₂ Φ₂
    (latInd Q.lat Λ) hO2 (cosetInd q Q.lat (ε • Q).red) g₃ T₃ hg₃ hT₃ hSB
  refine ⟨g, ?_⟩
  rw [← hrow]
  have hl : lastBi o o'' τ Ξ Φ₂ u = o''.boxT S Φ₂ (T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red))) := by
    rw [hT₃b, hT₁a]
    rfl
  rw [hl]
  exact hg

end GlobalTheory.LastTarget
