import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDependsBelowAndSmallTranslationInvariaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetCosetRepsBoundedHalfPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhatStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Flip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k}

/- English proof (translation)
Introduce `x`. Rewrite using `[← h x]`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Use `H (-y) (by rwa [Valuation.map_neg])` as an intermediate fact.

Rewrite `this` using `[AddChar.inv_apply, neg_neg]`. Then use the resulting hypothesis. Introduce `H y hy`. Rewrite using `[AddChar.inv_apply]`. Conclude with `H (-y) (by rwa [Valuation.map_neg])`.
-/
theorem hasConductor_inv {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) : HasConductor ψ⁻¹ c := by
  intro x
  rw [← h x]
  constructor
  · intro H y hy
    have := H (-y) (by rwa [Valuation.map_neg])
    rwa [AddChar.inv_apply, neg_neg] at this
  · intro H y hy
    rw [AddChar.inv_apply]
    exact H (-y) (by rwa [Valuation.map_neg])

/- English proof (translation)
Establish `h1` using `(FourierDepth.fourier_exchange k A' Dd ψ ϖ e P hϖ hψ).1 Φ hΦ`. Establish `h2` using `@FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' Dd _ _ _ _ _ _ μ (by assumption) σ ν ϖ e (blockUnits ϖ e P) _ hϖ he hν h1`. Establish `h3 : HasDepth ϖ e (blockLat ϖ e Pᶜ) (phiA μ σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ))`. Rewrite using `[← latA_blockLat]`. Conclude with `h2`.

Conclude with `(FourierDepth.fourier_exchange k A Dd ψ⁻¹ ϖ e Pᶜ hϖ (hasConductor_inv hψ)).2 _ h3`.
-/
theorem isNatDatum_squareFlip {A A' Dd : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype Dd]
    [DecidableEq Dd] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ Dd) {ψ : AddChar k Circle} (ν : kˣ →* ℂˣ)
    {ϖ : kˣ} {e : ℕ} (P : Finset Dd) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) (hν : CondLE ϖ e ν)
    {Φ : Matrix A' Dd k → ℂ} (hΦ : IsNatDatum ϖ e Φ) : IsNatDatum ϖ e (squareFlip μ σ ψ ν ϖ e P Φ) := by
  have h1 := (FourierDepth.fourier_exchange k A' Dd ψ ϖ e P hϖ hψ).1 Φ hΦ
  have h2 := @FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' Dd _ _ _ _ _ _ μ (by assumption) σ ν ϖ e (blockUnits ϖ e P) _ hϖ he hν h1
  have h3 : HasDepth ϖ e (blockLat ϖ e Pᶜ) (phiA μ σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ)) := by
    rw [← latA_blockLat]; exact h2
  exact (FourierDepth.fourier_exchange k A Dd ψ⁻¹ ϖ e Pᶜ hϖ (hasConductor_inv hψ)).2 _ h3

/- English proof (translation)
Establish `h : phiA μ σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P 0) = 0`. Use function extensionality and compare the values at `X`. Simplify using `[phiA, fFun, smallF]`. Rewrite using `[squareFlip, h, map_zero]`.
-/
theorem squareFlip_zero {A A' Dd : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype Dd]
    [DecidableEq Dd] (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ Dd) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ)
    (P : Finset Dd) : squareFlip μ σ ψ ν ϖ e P 0 = 0 := by
  have h : phiA μ σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P 0) = 0 := by
    funext X
    simp [phiA, fFun, smallF]
  rw [squareFlip, h, map_zero]

/- English proof (translation)
Establish `hne : Edge.theta i j ≠ Edge.ex i j` using `by simp`. Use `⟨fun Z hZ => ?_, fun Z Z₀ hZ₀ => ?_⟩` and prove the remaining obligations. Rewrite `hZ` using `[mem_matLat_stdLat] at hZ push_neg`. Take `⟨r, c, hc⟩` from `hZ`. Break down `c with c | c` into its components or cases.

Use `hT.2.1 _ _ h1 fun H => hc ?_` and prove the remaining obligations. Use `mem_matLat_stdLat.1 H r c` as an intermediate fact. Simplify `this` using `[Function.update_of_ne hne, Matrix.toCols₁]`. Use `hT.2.1 _ _ h2 fun H => hc ?_` and prove the remaining obligations. Use `mem_matLat_stdLat.1 H c r` as an intermediate fact.

Simplify `this` using `[Matrix.toCols₂]`. Establish `key : (Function.update (Function.update x (.theta i j) (Z + Z₀).toCols₁) (.ex i j) (Z + Z₀).toCols₂ᵀ : G.Args) = Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ + Function.update (Function.update (0 : G.Args) (.theta i j) Z₀.toCols₁) (.ex i j) Z₀.t …`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = .ex i j`. Substitute `hb` using the available equality.

Use extensionality with `r s`. Simplify using `[Matrix.toCols₂]`. Distinguish the cases in `hb' : b = .theta i j`. Substitute `hb'` using the available equality. Use extensionality with `r s`.

Simplify using `[Function.update_of_ne hne, Matrix.toCols₁]`. Simplify using `[Function.update_of_ne hb, Function.update_of_ne hb']`. Establish `hZ'` using `FourierDepth.mem_matLat_smul_stdLat.1 hZ₀`. Use `(congrArg T key).trans (hT.2.2 _ _ fun b => ?_)` and prove the remaining obligations. Rewrite using `[FourierDepth.mem_matLat_smul_stdLat]`.

Distinguish the cases in `hb : b = .ex i j`. Substitute `hb` using the available equality. Introduce `r s`. Simplify `hZ' s (Sum.inr r)` using `[Matrix.toCols₂]`. Distinguish the cases in `hb' : b = .theta i j`.

Substitute `hb'` using the available equality. Introduce `r s`. Simplify `hZ' r (Sum.inl s)` using `[Function.update_of_ne hne, Matrix.toCols₁]`. Introduce `r s`. Simplify using `[Function.update_of_ne hb, Function.update_of_ne hb']`.
-/
theorem isNatDatum_sliceB {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) {i j : ℕ}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) (x : G.Args) : IsNatDatum ϖ e (G.sliceB i j T x) := by
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  refine ⟨fun Z hZ => ?_, fun Z Z₀ hZ₀ => ?_⟩
  · rw [mem_matLat_stdLat] at hZ
    push_neg at hZ
    obtain ⟨r, c, hc⟩ := hZ
    rcases c with c | c
    · refine hT.2.1 _ _ h1 fun H => hc ?_
      have := mem_matLat_stdLat.1 H r c
      simpa [Function.update_of_ne hne, Matrix.toCols₁] using this
    · refine hT.2.1 _ _ h2 fun H => hc ?_
      have := mem_matLat_stdLat.1 H c r
      simpa [Matrix.toCols₂] using this
  · have key : (Function.update (Function.update x (.theta i j) (Z + Z₀).toCols₁) (.ex i j) (Z + Z₀).toCols₂ᵀ : G.Args) =
        Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ +
          Function.update (Function.update (0 : G.Args) (.theta i j) Z₀.toCols₁) (.ex i j) Z₀.toCols₂ᵀ := by
      funext b
      by_cases hb : b = .ex i j
      · subst hb
        ext r s; simp [Matrix.toCols₂]
      · by_cases hb' : b = .theta i j
        · subst hb'
          ext r s; simp [Function.update_of_ne hne, Matrix.toCols₁]
        · simp [Function.update_of_ne hb, Function.update_of_ne hb']
    have hZ' := FourierDepth.mem_matLat_smul_stdLat.1 hZ₀
    refine (congrArg T key).trans (hT.2.2 _ _ fun b => ?_)
    rw [FourierDepth.mem_matLat_smul_stdLat]
    by_cases hb : b = .ex i j
    · subst hb
      intro r s; simpa [Matrix.toCols₂] using hZ' s (Sum.inr r)
    · by_cases hb' : b = .theta i j
      · subst hb'
        intro r s; simpa [Function.update_of_ne hne, Matrix.toCols₁] using hZ' r (Sum.inl s)
      · intro r s; simp [Function.update_of_ne hb, Function.update_of_ne hb']

end Flip

section Flip2

open scoped Pointwise

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k}

/- English proof (translation)
Establish `hJ'` using `isOpen_map_invT hJ hK`. Use `haveI := isHaarMeasure_haarVol hJ'.1 hJ'.2`. Establish `hne : Edge.theta i j ≠ Edge.ex i j` using `by simp`. Establish `hN : ∀ x, IsNatDatum ϖ e (squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e (Assignment.one.block _ _) (G.sliceB i j T x))` using `fun x => isNatDatum_squareFlip _ _ _ _ hϖ hψ he hν (isNatDatum_sliceB hT h1 h2 x)`. Establish `hfl : ∀ x, G.flipTensor .one ψ ϖ e i j J T x = squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e (Assignment.one.block _ _) (G.sliceB i j T x) (G.joinA i j x)` using `fun _ => rfl`.

Establish `m1 : Edge.ex i (j + 1) ∈ flipPath i j γ` using `List.mem_map.2 ⟨_, h1, by simp⟩`. Establish `m2 : Edge.theta (i + 1) j ∈ flipPath i j γ` using `List.mem_map.2 ⟨_, h2, by simp⟩`. Establish `mo : ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → b ∈ flipPath i j γ` using `fun b hb hb1 hb2 => List.mem_map.2 ⟨b, hb, by simp [hb1, hb2]⟩`. Establish `hs0 : ∀ x : G.Args, ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → x b ∉ matLat _ (SplitFlip.stdLat k _) → G.sliceB i j T x = 0` using `fun x b hb hb1 hb2 hx => funext fun Z => hT.2.1 _ b hb (by simpa [Function.update_of_ne hb1, Function.update_of_ne hb2] using hx)`. Use `⟨fun x y hxy => ?_, fun x b hb hx => ?_, fun x z hz => ?_⟩` and prove the remaining obligations.

Establish `e1 : G.sliceB i j T x = G.sliceB i j T y` using `funext fun Z => hT.1 fun b hb => by`. Distinguish the cases in `hb2 : b = .ex i j`. Substitute `hb2` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `hb1 : b = .theta i j`.

Substitute `hb1` using the available equality. Simplify using `[Function.update_of_ne hne]`. Simplify using `only [Function.update_of_ne hb2, Function.update_of_ne hb1]`. Conclude with `hxy b (mo b hb hb1 hb2)`. Establish `e2 : G.joinA i j x = G.joinA i j y`.

Simplify using `only [Grid.joinA, hxy _ m1, hxy _ m2]`. Rewrite using `[hfl, hfl, e1, e2]`. Rewrite using `[hfl]`. Establish `hcase : b = .ex i (j + 1) ∨ b = .theta (i + 1) j ∨ (b ∈ γ ∧ b ≠ .theta i j ∧ b ≠ .ex i j)`. Take `⟨b₀, hb₀, rfl⟩` from `List.mem_map.1 hb`.

Use `split_ifs with k1 k2`. Conclude with `.inl rfl`. Conclude with `.inr (.inl rfl)`. Conclude with `.inr (.inr ⟨hb₀, k1, k2⟩)`. Break down `hcase with rfl | rfl | ⟨hb₀, hb1, hb2⟩` into its components or cases.

Use `(hN x).1 _ fun H => hx ?_` and prove the remaining obligations. Rewrite `H`, the goal using `[mem_matLat_stdLat]`. Introduce `r s`. Simplify `H r (Sum.inl s)` using `[Grid.joinA]`. Use `(hN x).1 _ fun H => hx ?_` and prove the remaining obligations.

Rewrite `H`, the goal using `[mem_matLat_stdLat]`. Introduce `r s`. Simplify `H s (Sum.inr r)` using `[Grid.joinA]`. Rewrite using `[hs0 x b hb₀ hb1 hb2 hx, squareFlip_zero]`. Both sides reduce to the same expression.

Establish `e1 : G.sliceB i j T (x + z) = G.sliceB i j T x` using `funext fun Z => by`. Establish `key : (Function.update (Function.update (x + z) (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ : G.Args) = Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ + Function.update (Function.update z (.theta i j) 0) (.ex i j) 0`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = .ex i j`. Substitute `hb` using the available equality.

Simplify using the standard rewrite rules. Distinguish the cases in `hb' : b = .theta i j`. Substitute `hb'` using the available equality. Simplify using `[Function.update_of_ne hne]`. Simplify using `[Function.update_of_ne hb, Function.update_of_ne hb']`.

Use `(congrArg T key).trans (hT.2.2 _ _ fun b => ?_)` and prove the remaining obligations. Distinguish the cases in `hb : b = .ex i j`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `hb' : b = .theta i j`.

Substitute `hb'` using the available equality. Simplify using `[Function.update_of_ne hne]`. Simplify `hz b` using `[Function.update_of_ne hb, Function.update_of_ne hb']`. Establish `e2 : G.joinA i j (x + z) = G.joinA i j x + G.joinA i j z`. Apply the tactic sequence `ext r (s | s) <;> simp [Grid.joinA]`.

Establish `hj : G.joinA i j z ∈ matLat (Fin (G.rank (i + 1, j + 1))) (ϖ ^ e • SplitFlip.stdLat k (G.Cols i j))`. Rewrite using `[FourierDepth.mem_matLat_smul_stdLat]`. Establish `h3` using `FourierDepth.mem_matLat_smul_stdLat.1 (hz (.ex i (j + 1)))`. Establish `h4` using `FourierDepth.mem_matLat_smul_stdLat.1 (hz (.theta (i + 1) j))`. Introduce and unpack `r (s | s)`.

Simplify `h3 r s` using `[Grid.joinA]`. Simplify `h4 s r` using `[Grid.joinA]`. Rewrite using `[hfl, hfl, e1, e2, (hN x).2 _ _ hj]`.
-/
theorem isTensor_flipTensor {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e)
    {i j : ℕ} (hν : CondLE ϖ e (G.nu i j)) {J : G.Level} (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k)))
    (hK : J (i, j) ≤ KO k _) {γ : List Edge} (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ}
    (hT : G.IsTensor ϖ e γ T) : G.IsTensor ϖ e (flipPath i j γ) (G.flipTensor .one ψ ϖ e i j J T) := by
  have hJ' := isOpen_map_invT hJ hK
  haveI := isHaarMeasure_haarVol hJ'.1 hJ'.2
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  have hN : ∀ x, IsNatDatum ϖ e (squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e
      (Assignment.one.block _ _) (G.sliceB i j T x)) := fun x =>
    isNatDatum_squareFlip _ _ _ _ hϖ hψ he hν (isNatDatum_sliceB hT h1 h2 x)
  have hfl : ∀ x, G.flipTensor .one ψ ϖ e i j J T x = squareFlip (haarVol ((J (i, j)).map invT))
      (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e (Assignment.one.block _ _) (G.sliceB i j T x) (G.joinA i j x) :=
    fun _ => rfl
  have m1 : Edge.ex i (j + 1) ∈ flipPath i j γ := List.mem_map.2 ⟨_, h1, by simp⟩
  have m2 : Edge.theta (i + 1) j ∈ flipPath i j γ := List.mem_map.2 ⟨_, h2, by simp⟩
  have mo : ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → b ∈ flipPath i j γ := fun b hb hb1 hb2 =>
    List.mem_map.2 ⟨b, hb, by simp [hb1, hb2]⟩

  have hs0 : ∀ x : G.Args, ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → x b ∉ matLat _ (SplitFlip.stdLat k _) →
      G.sliceB i j T x = 0 := fun x b hb hb1 hb2 hx => funext fun Z =>
    hT.2.1 _ b hb (by simpa [Function.update_of_ne hb1, Function.update_of_ne hb2] using hx)
  refine ⟨fun x y hxy => ?_, fun x b hb hx => ?_, fun x z hz => ?_⟩
  · have e1 : G.sliceB i j T x = G.sliceB i j T y := funext fun Z => hT.1 fun b hb => by
      by_cases hb2 : b = .ex i j
      · subst hb2; simp
      · by_cases hb1 : b = .theta i j
        · subst hb1; simp [Function.update_of_ne hne]
        · simp only [Function.update_of_ne hb2, Function.update_of_ne hb1]
          exact hxy b (mo b hb hb1 hb2)
    have e2 : G.joinA i j x = G.joinA i j y := by
      simp only [Grid.joinA, hxy _ m1, hxy _ m2]
    rw [hfl, hfl, e1, e2]
  · rw [hfl]
    have hcase : b = .ex i (j + 1) ∨ b = .theta (i + 1) j ∨ (b ∈ γ ∧ b ≠ .theta i j ∧ b ≠ .ex i j) := by
      obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
      split_ifs with k1 k2
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr ⟨hb₀, k1, k2⟩)
    rcases hcase with rfl | rfl | ⟨hb₀, hb1, hb2⟩
    · refine (hN x).1 _ fun H => hx ?_
      rw [mem_matLat_stdLat] at H ⊢
      intro r s
      simpa [Grid.joinA] using H r (Sum.inl s)
    · refine (hN x).1 _ fun H => hx ?_
      rw [mem_matLat_stdLat] at H ⊢
      intro r s
      simpa [Grid.joinA] using H s (Sum.inr r)
    · rw [hs0 x b hb₀ hb1 hb2 hx, squareFlip_zero]
      rfl
  · have e1 : G.sliceB i j T (x + z) = G.sliceB i j T x := funext fun Z => by
      have key : (Function.update (Function.update (x + z) (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ : G.Args) =
          Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ +
            Function.update (Function.update z (.theta i j) 0) (.ex i j) 0 := by
        funext b
        by_cases hb : b = .ex i j
        · subst hb; simp
        · by_cases hb' : b = .theta i j
          · subst hb'; simp [Function.update_of_ne hne]
          · simp [Function.update_of_ne hb, Function.update_of_ne hb']
      refine (congrArg T key).trans (hT.2.2 _ _ fun b => ?_)
      by_cases hb : b = .ex i j
      · subst hb; simp
      · by_cases hb' : b = .theta i j
        · subst hb'; simp [Function.update_of_ne hne]
        · simpa [Function.update_of_ne hb, Function.update_of_ne hb'] using hz b
    have e2 : G.joinA i j (x + z) = G.joinA i j x + G.joinA i j z := by
      ext r (s | s) <;> simp [Grid.joinA]
    have hj : G.joinA i j z ∈ matLat (Fin (G.rank (i + 1, j + 1))) (ϖ ^ e • SplitFlip.stdLat k (G.Cols i j)) := by
      rw [FourierDepth.mem_matLat_smul_stdLat]
      have h3 := FourierDepth.mem_matLat_smul_stdLat.1 (hz (.ex i (j + 1)))
      have h4 := FourierDepth.mem_matLat_smul_stdLat.1 (hz (.theta (i + 1) j))
      rintro r (s | s)
      · simpa [Grid.joinA] using h3 r s
      · simpa [Grid.joinA] using h4 s r
    rw [hfl, hfl, e1, e2, (hN x).2 _ _ hj]

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro S _ _ _ hT`. Conclude with `hT`. Consider the case `cons x l ih`.

Introduce `S hν hc hJ hT`. Take `_ | ⟨hp, hc'⟩` from `hc`. Establish `hsub` using `hp.subset`. Use `ih (S.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _`.

Distinguish the cases in `hX : X = (x.1 + 1, x.2 + 1)`. Substitute `hX` using the available equality. Simplify using `only [Grid.flipLevel, Function.update_self]`. Conclude with `⟨isOpen_KO, le_rfl⟩`. Simplify using `only [Grid.flipLevel, Function.update_of_ne hX]`.

Conclude with `hJ X`. Conclude with `isTensor_flipTensor hϖ hψ he (hν x List.mem_cons_self) (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT`.
-/
theorem isTensor_flips {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2)) → CanFlip S.path l →
      (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) → G.IsTensor ϖ e S.path S.tensor →
      G.IsTensor ϖ e (S.flips .one ψ ϖ e l).path (S.flips .one ψ ϖ e l).tensor := by
  intro l
  induction l with
  | nil => intro S _ _ _ hT; exact hT
  | cons x l ih =>
    intro S hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    have hsub := hp.subset
    refine ih (S.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_) ?_
    · change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
      by_cases hX : X = (x.1 + 1, x.2 + 1)
      · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
      · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X
    · exact isTensor_flipTensor hϖ hψ he (hν x List.mem_cons_self) (hJ _).1 (hJ _).2 (hsub (by simp))
        (hsub (by simp)) hT

end Flip2

/- English proof (translation)
Establish `hg` using `(Good.locGrid_isGood hL G W t hde hc).1 w hw`. Establish `hadm` using `GivenAdm.givenStage_isAdmissible hL B t Φ hw`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `h00` using `hg.square 0 hm 0 hm`. Establish `hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2)`.

Introduce `x hx`. Simplify using `only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx`. Take `⟨i, hi, j, hj, rfl⟩` from `hx`. Rewrite using `[← Grid.alpha_div_beta]`. Conclude with `(hg.square i hi j hj).condν`.

Rewrite using `[← (flipStage_path_level t w B W Φ).1]`. Conclude with `isTensor_flips h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w B Φ) hν (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor`.
-/
theorem isTensor_Tflip {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (oppositePath D.R.m) (Tflip W B t Φ w) := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  rw [← (flipStage_path_level t w B W Φ).1]
  exact isTensor_flips h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w B Φ) hν (canFlip_flipOrder _).1
    (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor

section SB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : valuation k (ϖ : k) ≤ 1` using `hϖ ▸ uniformizer_lt_one.le`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]`. Conclude with `pow_le_pow_of_le_one zero_le' h1 h`.
-/
theorem val_pow_anti {ϖ : kˣ} (hϖ : IsUnif ϖ) {a b : ℕ} (h : a ≤ b) :
    valuation k ((ϖ ^ b : kˣ) : k) ≤ valuation k ((ϖ ^ a : kˣ) : k) := by
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
  exact pow_le_pow_of_le_one zero_le' h1 h

/- English proof (translation)
Rewrite using `[Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀]`. Conclude with `inv_anti₀ (zero_lt_iff.2 (by simp)) (val_pow_anti hϖ h)`.
-/
theorem val_inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {a b : ℕ} (h : a ≤ b) :
    valuation k (((ϖ ^ a)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ b)⁻¹ : kˣ) : k) := by
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀]
  exact inv_anti₀ (zero_lt_iff.2 (by simp)) (val_pow_anti hϖ h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hF.dep, fun x y a b ha hb => hF.per x y a b (fun j hj r s => (ha j hj r s).trans (val_pow_anti hϖ h)) (fun i hi r s => (hb i hi r s).trans (val_pow_anti hϖ h)), fun x y hxy => ⟨fun j hj r s => ((hF.supp x y hxy).1 j hj r s).trans (val_inv_pow_mono hϖ h), fun i hi r s => ((hF.sup …`.
-/
theorem IsSBArgs.mono {G : Grid k} {ϖ : kˣ} (hϖ : IsUnif ϖ) {n n' : ℕ} (h : n ≤ n') {F : ColArgs G → RowArgs G → ℂ}
    (hF : IsSBArgs G ϖ n F) : IsSBArgs G ϖ n' F :=
  ⟨hF.dep, fun x y a b ha hb => hF.per x y a b (fun j hj r s => (ha j hj r s).trans (val_pow_anti hϖ h))
      (fun i hi r s => (hb i hi r s).trans (val_pow_anti hϖ h)),
    fun x y hxy => ⟨fun j hj r s => ((hF.supp x y hxy).1 j hj r s).trans (val_inv_pow_mono hϖ h),
      fun i hi r s => ((hF.supp x y hxy).2 i hi r s).trans (val_inv_pow_mono hϖ h)⟩⟩

/- English proof (translation)
Take `⟨hdep, n₁, hper⟩` from `GlobalTheory.T.flatTensor_depends_below_and_small_translation_invariant G hs ψ ν ϖ e T keep g hϖ hψ hT`. Take `⟨n₂, hsupp⟩` from `GlobalTheory.T.flatTensor_support_bounded_by_uniformizer_pow G hs ψ ν ϖ e T keep g hϖ hT`. Take `⟨n₃, hlast⟩` from `GlobalTheory.T.flatTensor_vanishes_unless_lastRow_bounded G hs ψ ν ϖ e T keep g hm hϖ hψ hT`. Use `⟨max n₁ (max n₂ n₃), hdep, fun x y a b ha hb => hper x a y b (fun j hj r s => (ha j hj r s).trans (val_pow_anti hϖ (le_max_left _ _))) (fun i hi r s => (hb i hi r s).trans (val_pow_anti hϖ (le_max_left _ _))), fun x y hxy => ⟨fun j hj r s => ?_, fun i hi r s => ((hsupp x y hxy).2 …` and prove the remaining obligations. Distinguish the cases in `hr : j + 1 = G.m ∧ r = topLast G (j + 1)`.

Take `⟨h1, rfl⟩` from `hr`. Take `rfl : j = G.m - 1` from `by omega`. Conclude with `(hlast x y hxy s).trans (val_inv_pow_mono hϖ (by omega))`. Conclude with `((hsupp x y hxy).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans (val_inv_pow_mono hϖ (by omega))`.
-/
theorem exists_isSBArgs_flat [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup)
    (hm : 2 ≤ G.m) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) :
    ∃ n, IsSBArgs G ϖ n (flatTensor hs ψ ν (moved G keep g T)) := by
  obtain ⟨hdep, n₁, hper⟩ := GlobalTheory.T.flatTensor_depends_below_and_small_translation_invariant G hs ψ ν ϖ e T keep g hϖ hψ hT
  obtain ⟨n₂, hsupp⟩ := GlobalTheory.T.flatTensor_support_bounded_by_uniformizer_pow G hs ψ ν ϖ e T keep g hϖ hT
  obtain ⟨n₃, hlast⟩ := GlobalTheory.T.flatTensor_vanishes_unless_lastRow_bounded G hs ψ ν ϖ e T keep g hm hϖ hψ hT
  refine ⟨max n₁ (max n₂ n₃), hdep, fun x y a b ha hb => hper x a y b
    (fun j hj r s => (ha j hj r s).trans (val_pow_anti hϖ (le_max_left _ _)))
    (fun i hi r s => (hb i hi r s).trans (val_pow_anti hϖ (le_max_left _ _))), fun x y hxy => ⟨fun j hj r s => ?_,
      fun i hi r s => ((hsupp x y hxy).2 i hi r s).trans (val_inv_pow_mono hϖ (by omega))⟩⟩
  by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
  · obtain ⟨h1, rfl⟩ := hr
    obtain rfl : j = G.m - 1 := by omega
    exact (hlast x y hxy s).trans (val_inv_pow_mono hϖ (by omega))
  · exact ((hsupp x y hxy).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans (val_inv_pow_mono hϖ (by omega))

end SB

section Args

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

/- English proof (translation)
Rewrite using `[frAt, frAt, frAt, Matrix.map_add _ (map_add (toEAf D)), Comparison₂.fr_add, Matrix.map_add _ (map_add (cpt (D := D) w))]`.
-/
theorem frAt_add (w : Pl D.host.E) {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x + y) = frAt w β' β x + frAt w β' β y := by
  rw [frAt, frAt, frAt, Matrix.map_add _ (map_add (toEAf D)), Comparison₂.fr_add, Matrix.map_add _ (map_add (cpt (D := D) w))]

/- English proof (translation)
Establish `h` using `frAt_add w β' β x (-x)`. Rewrite `h` using `[add_neg_cancel]`. Establish `h0 : frAt w β' β 0 = 0` using `by ext; simp [frAt, Comparison₂.fr]`. Rewrite `h` using `[h0]`. Conclude with `eq_neg_of_add_eq_zero_right h.symm`.
-/
theorem frAt_neg (w : Pl D.host.E) {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x : Mx D b a) :
    frAt w β' β (-x) = -frAt w β' β x := by
  have h := frAt_add w β' β x (-x)
  rw [add_neg_cancel] at h
  have h0 : frAt w β' β 0 = 0 := by ext; simp [frAt, Comparison₂.fr]
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/- English proof (translation)
Rewrite using `[GridChoice.colAt, dif_pos h, frAt, Comparison₂.fr, Matrix.map_mul, Matrix.map_mul, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem colAt_eq (S : GridChoice W U) (t : T) (w : Pl D.host.E) (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    {j : ℕ} (h : j < D.R.m) : S.colAt t w x j = (frAt w (S.βp (j + 1)) (S.βp j) (x ⟨j, h⟩)).submatrix
      (Fin.cast (topRank_eq G t w h)) (Fin.cast (topRank_eq G t w h.le)) := by
  rw [GridChoice.colAt, dif_pos h, frAt, Comparison₂.fr, Matrix.map_mul, Matrix.map_mul, ← map_inv]
  rfl

/- English proof (translation)
Establish `e1 : Matrix.map (y ⟨i, h⟩) ((cpt w).comp (toEAf D)) = ((y ⟨i, h⟩).map (toEAf D)).map (cpt (D` using `D) w) := by ext; rfl`. Rewrite using `[GridChoice.rowAt, dif_pos h, e1, Comparison₂.coord_map]`. Both sides reduce to the same expression.
-/
theorem rowAt_eq (S : GridChoice W U) (t : T) (w : Pl D.host.E)
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) {i : ℕ} (h : i < D.R.m) :
    S.rowAt t w y i = (frAt w (S.B.β i D.R.m) (S.B.β (i + 1) D.R.m) (y ⟨i, h⟩)).submatrix
      (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨h.le, le_rfl⟩))
      (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨h, le_rfl⟩)) := by
  have e1 : Matrix.map (y ⟨i, h⟩) ((cpt w).comp (toEAf D)) = ((y ⟨i, h⟩).map (toEAf D)).map (cpt (D := D) w) := by
    ext; rfl
  rw [GridChoice.rowAt, dif_pos h, e1, Comparison₂.coord_map]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j < D.R.m`. Rewrite using `[Pi.add_apply, colAt_eq S t w _ h, colAt_eq S t w _ h, colAt_eq S t w _ h, Pi.add_apply, frAt_add] ext`. Simplify using the standard rewrite rules. Simplify using `[GridChoice.colAt, h]`.
-/
theorem colAt_add (S : GridChoice W U) (t : T) (w : Pl D.host.E) (x a : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) :
    S.colAt t w (x + a) = S.colAt t w x + S.colAt t w a := by
  funext j
  by_cases h : j < D.R.m
  · rw [Pi.add_apply, colAt_eq S t w _ h, colAt_eq S t w _ h, colAt_eq S t w _ h, Pi.add_apply, frAt_add]
    ext; simp
  · simp [GridChoice.colAt, h]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i < D.R.m`. Rewrite using `[Pi.add_apply, rowAt_eq S t w _ h, rowAt_eq S t w _ h, rowAt_eq S t w _ h, Pi.add_apply, frAt_add]`. Both sides reduce to the same expression. Simplify using `[GridChoice.rowAt, h]`.
-/
theorem rowAt_add (S : GridChoice W U) (t : T) (w : Pl D.host.E)
    (y b : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    S.rowAt t w (y + b) = S.rowAt t w y + S.rowAt t w b := by
  funext i
  by_cases h : i < D.R.m
  · rw [Pi.add_apply, rowAt_eq S t w _ h, rowAt_eq S t w _ h, rowAt_eq S t w _ h, Pi.add_apply, frAt_add]
    rfl
  · simp [GridChoice.rowAt, h]

end Args

section Abstract

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {A : ι → Type} [∀ j, AddCommGroup (A j)]
  {B : κ → Type} [∀ i, AddCommGroup (B i)]

open Classical in

/- English proof (translation)
Distinguish the cases in `hex : ∃ q : (∀ j, R j) × (∀ i, R' i), (∀ j, SA j (x j - (q.1 j).1)) ∧ ∀ i, SB i (y i - (q.2 i).1)`. Take `⟨q₀, hx, hy⟩` from `hex`. Rewrite using `[Finset.sum_eq_single q₀]`. Rewrite using `[Finset.prod_eq_one fun j _ => if_pos (hx j), Finset.prod_eq_one fun i _ => if_pos (hy i), mul_one, mul_one]`. Establish `h` using `hper (fun j => (q₀.1 j).1) (fun i => (q₀.2 i).1) (x - fun j => (q₀.1 j).1) (y - fun i => (q₀.2 i).1) hx hy`.

Rewrite `h` using `[add_sub_cancel, add_sub_cancel]`. Conclude with `h.symm`. Introduce `q _ hne`. Assume the negation of the conclusion as `hz`. Apply `hne` to reduce the goal to its premises.

Establish `h1 : ∀ j, SA j (x j - (q.1 j).1)` using `fun j => by`. Assume the negation of the conclusion as `h0`. Apply `hz` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ∀ i, SB i (y i - (q.2 i).1)` using `fun i => by`. Assume the negation of the conclusion as `h0`. Apply `hz` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) (if_neg h0)]`. Expand and normalize the polynomial expressions, which then agree.

Use `Prod.ext (funext fun j => Subtype.ext ?_) (funext fun i => Subtype.ext ?_)` and prove the remaining obligations. Use `hSA j _ _ (hx j) (h1 j)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left]`. Conclude with `hR3 j _ (q.1 j).2 _ (q₀.1 j).2 this`. Use `hSB i _ _ (hy i) (h2 i)` as an intermediate fact.

Rewrite `this` using `[sub_sub_sub_cancel_left]`. Conclude with `hR3' i _ (q.2 i).2 _ (q₀.2 i).2 this`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_eq_zero]`.

Use `symm`. Assume the negation of the conclusion as `hne`. Apply `hex` to reduce the goal to its premises. Take `⟨sx, sy⟩` from `hsupp hne`. Use `choose r hr hrs using fun j => hR2 j (x j) (sx j)`.

Use `choose r' hr' hrs' using fun i => hR2' i (y i) (sy i)`. Conclude with `⟨(fun j => ⟨r j, hr j⟩, fun i => ⟨r' i, hr' i⟩), hrs, hrs'⟩`. Introduce `q _`. Assume the negation of the conclusion as `hz`. Apply `hex` to reduce the goal to its premises.

Use `⟨q, fun j => ?_, fun i => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Apply `hz` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]`. Expand and normalize the polynomial expressions, which then agree.

Assume the negation of the conclusion as `h0`. Apply `hz` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) (if_neg h0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_reps_eq (SA : ∀ j, A j → Prop) (SB : ∀ i, B i → Prop) (BA : ∀ j, A j → Prop) (BB : ∀ i, B i → Prop)
    (hSA : ∀ j a b, SA j a → SA j b → SA j (a - b)) (hSB : ∀ i a b, SB i a → SB i b → SB i (a - b))
    (R : ∀ j, Finset (A j)) (R' : ∀ i, Finset (B i))
    (hR2 : ∀ j x, BA j x → ∃ r ∈ R j, SA j (x - r)) (hR2' : ∀ i y, BB i y → ∃ r ∈ R' i, SB i (y - r))
    (hR3 : ∀ j, ∀ r ∈ R j, ∀ r' ∈ R j, SA j (r - r') → r = r') (hR3' : ∀ i, ∀ r ∈ R' i, ∀ r' ∈ R' i, SB i (r - r') → r = r')
    (F : (∀ j, A j) → (∀ i, B i) → ℂ)
    (hper : ∀ x y a b, (∀ j, SA j (a j)) → (∀ i, SB i (b i)) → F (x + a) (y + b) = F x y) (x : ∀ j, A j) (y : ∀ i, B i)
    (hsupp : F x y ≠ 0 → (∀ j, BA j (x j)) ∧ ∀ i, BB i (y i)) :
    ∑ q : (∀ j, R j) × (∀ i, R' i), F (fun j => (q.1 j).1) (fun i => (q.2 i).1) *
      (∏ j, if SA j (x j - (q.1 j).1) then (1 : ℂ) else 0) * (∏ i, if SB i (y i - (q.2 i).1) then (1 : ℂ) else 0) =
      F x y := by
  by_cases hex : ∃ q : (∀ j, R j) × (∀ i, R' i), (∀ j, SA j (x j - (q.1 j).1)) ∧ ∀ i, SB i (y i - (q.2 i).1)
  · obtain ⟨q₀, hx, hy⟩ := hex
    rw [Finset.sum_eq_single q₀]
    · rw [Finset.prod_eq_one fun j _ => if_pos (hx j), Finset.prod_eq_one fun i _ => if_pos (hy i), mul_one, mul_one]
      have h := hper (fun j => (q₀.1 j).1) (fun i => (q₀.2 i).1) (x - fun j => (q₀.1 j).1) (y - fun i => (q₀.2 i).1) hx hy
      rw [add_sub_cancel, add_sub_cancel] at h
      exact h.symm
    · intro q _ hne
      by_contra hz
      apply hne
      have h1 : ∀ j, SA j (x j - (q.1 j).1) := fun j => by
        by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring
      have h2 : ∀ i, SB i (y i - (q.2 i).1) := fun i => by
        by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg h0)]; ring
      refine Prod.ext (funext fun j => Subtype.ext ?_) (funext fun i => Subtype.ext ?_)
      · have := hSA j _ _ (hx j) (h1 j)
        rw [sub_sub_sub_cancel_left] at this
        exact hR3 j _ (q.1 j).2 _ (q₀.1 j).2 this
      · have := hSB i _ _ (hy i) (h2 i)
        rw [sub_sub_sub_cancel_left] at this
        exact hR3' i _ (q.2 i).2 _ (q₀.2 i).2 this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hne
      apply hex
      obtain ⟨sx, sy⟩ := hsupp hne
      choose r hr hrs using fun j => hR2 j (x j) (sx j)
      choose r' hr' hrs' using fun i => hR2' i (y i) (sy i)
      exact ⟨(fun j => ⟨r j, hr j⟩, fun i => ⟨r' i, hr' i⟩), hrs, hrs'⟩
    · intro q _
      by_contra hz
      apply hex
      refine ⟨q, fun j => ?_, fun i => ?_⟩
      · by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring
      · by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg h0)]; ring

end Abstract

section Expand

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

/- English proof (translation)
Use `GlobalTheory.GridIdem.exists_isIdemSum _ (fun w hw => ?_) fun w hw w' hw' h => Good.under_injOn hL G t hw hw' h` and prove the remaining obligations. Break down `Good.locPl_cases hw with ⟨a, b⟩ | ⟨-, -, b⟩` into its components or cases. Conclude with `b ▸ G.pl.w_split _ a`. Use `first`. Consider the case `exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b h`.

Consider the case `exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)`. Consider the case `exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h)`.
-/
theorem exists_idemSum_locPl' {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) : ∃ e, IsIdemSum e (locPl G t) := by
  refine GlobalTheory.GridIdem.exists_isIdemSum _ (fun w hw => ?_) fun w hw w' hw' h => Good.under_injOn hL G t hw hw' h
  rcases Good.locPl_cases hw with ⟨a, b⟩ | ⟨-, -, b⟩
  · exact b ▸ G.pl.w_split _ a
  · first
    | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b h
    | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)
    | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h)

variable (G) in

def finDatOf (t : T) (p : Pair T) {e : AE D} (he : IsIdemSum e (locPl G t)) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsSBHalf e (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) f) : FinDatum G t p :=
  { FinDatum.ind G t p (locPl G t) (fun _ hw => (Good.locPl_cases hw).elim (fun h => .inl h.1)
      fun h => .inr ⟨_, h.2.2, rfl⟩) e he with
    fn := f
    sb := hf }

section Small

variable {a b : ℕ} {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}

/- English proof (translation)
Introduce `w _ r s` and use `by have h : frAt w β' β 0 = 0 := by ext; simp [frAt, Comparison₂.fr] rw [h]; simp`.
-/
theorem isSmall_zero : IsSmall P β' β n (0 : Mx D b a) := fun w _ r s => by
  have h : frAt w β' β 0 = 0 := by ext; simp [frAt, Comparison₂.fr]
  rw [h]; simp

/- English proof (translation)
Introduce `w hw r s` and use `by rw [frAt_add, Matrix.add_apply] exact Valuation.map_add_le _ (h w hw r s) (h' w hw r s)`.
-/
theorem IsSmall.add {x y : Mx D b a} (h : IsSmall P β' β n x) (h' : IsSmall P β' β n y) : IsSmall P β' β n (x + y) :=
  fun w hw r s => by
    rw [frAt_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (h w hw r s) (h' w hw r s)

/- English proof (translation)
Introduce `w hw r s` and use `by rw [frAt_neg, Matrix.neg_apply, Valuation.map_neg] exact h w hw r s`.
-/
theorem IsSmall.neg {x : Mx D b a} (h : IsSmall P β' β n x) : IsSmall P β' β n (-x) := fun w hw r s => by
  rw [frAt_neg, Matrix.neg_apply, Valuation.map_neg]
  exact h w hw r s

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `h.add h'.neg`.
-/
theorem IsSmall.sub {x y : Mx D b a} (h : IsSmall P β' β n x) (h' : IsSmall P β' β n y) : IsSmall P β' β n (x - y) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

/- English proof (translation)
Rewrite using `[cosLoc, if_pos ⟨hr, by rw [sub_self]; exact isSmall_zero⟩]`.
-/
theorem cosLoc_self {e : AE D} {r : Mx D b a} (hr : IsHalf e r) : cosLoc P e β' β n r r = 1 := by
  rw [cosLoc, if_pos ⟨hr, by rw [sub_self]; exact isSmall_zero⟩]

/- English proof (translation)
Unfold `cosLoc at h`. Use `split_ifs at h with h'`. Conclude with `h'`. Conclude with `absurd rfl h`.
-/
theorem cosLoc_of_ne_zero {e : AE D} {r x : Mx D b a} (h : cosLoc P e β' β n r x ≠ 0) :
    IsHalf e x ∧ IsSmall P β' β n (x - r) := by
  unfold cosLoc at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

open Classical in
/- English proof (translation)
Unfold `cosLoc`. Simplify using `only [hx, true_and]`.
-/
theorem cosLoc_eq_ite {e : AE D} {r x : Mx D b a} (hx : IsHalf e x) :
    cosLoc P e β' β n r x = if IsSmall P β' β n (x - r) then 1 else 0 := by
  unfold cosLoc
  simp only [hx, true_and]

end Small

def GridChoice.IsCosExpansion (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (τ : PureDat G t →₀ ℂ) : Prop :=
  S.IsExpansion t Φ β τ ∧ ∃ (e : AE D) (n : ℕ), IsIdemSum e (locPl G t) ∧ ∀ d ∈ τ.support,
    ∃ (r : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (r' : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (r j)) ∧ (∀ i, IsHalf e (r' i)) ∧
      (∀ j, (d.1 j).fn = cosLoc (locPl G t) e (S.βp (j + 1)) (S.βp j) n (r j)) ∧
      (∀ i, (d.2 i).fn = cosLoc (locPl G t) e (S.B.β i D.R.m) (S.B.β (i + 1) D.R.m) n (r' i)) ∧
      τ d = ∏ w, (S.term t Φ β w).datum (S.colAt t w r) (S.rowAt t w r')

end Expand

section Lat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
The claim follows from `(G.isV (X := .top j) hj fun _ e => by cases e).sd.1`.
-/
theorem isLattice_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : Submodule.IsLattice D.host.E (G.Λ (.top j)) :=
  (G.isV (X := .top j) hj fun _ e => by cases e).sd.1

/- English proof (translation)
The claim follows from `(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ fun j e => by injection e with h1; omega).sd.1`.
-/
theorem isLattice_grid_succ (G : GridData L sc) {i : ℕ} (hi : i + 1 ≤ D.R.m) :
    Submodule.IsLattice D.host.E (G.Λ (.grid (i + 1) D.R.m)) :=
  (G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ fun j e => by injection e with h1; omega).sd.1

/- English proof (translation)
Take `⟨c, hc⟩` from `hL.βX`. Take `⟨h1, h2⟩` from `GlobalTheory.ParahoricLift.base_lattice hc`. Conclude with `⟨h1, h2⟩`.
-/
theorem isLattice_X {μ₀ : T} (hL : L.Is μ₀) : Submodule.IsLattice D.host.E L.ΛX := by
  obtain ⟨c, hc⟩ := hL.βX
  obtain ⟨h1, h2⟩ := GlobalTheory.ParahoricLift.base_lattice hc
  exact ⟨h1, h2⟩

/- English proof (translation)
Establish `key : ∀ X : LSp D, X = ⟨D.sp.X', L.ΛX⟩ → Submodule.IsLattice D.host.E X.lat`. Introduce and unpack `_ rfl`. Conclude with `isLattice_X hL`. Conclude with `key (columnBlock L D.R.m) (colY_m L)`.
-/
theorem isLattice_grid_zero {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) :
    Submodule.IsLattice D.host.E (G.Λ (.grid 0 D.R.m)) := by
  have key : ∀ X : LSp D, X = ⟨D.sp.X', L.ΛX⟩ → Submodule.IsLattice D.host.E X.lat := by
    rintro _ rfl; exact isLattice_X hL
  exact key (columnBlock L D.R.m) (colY_m L)

end Lat

section SBs

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

/- English proof (translation)
The claim follows from `GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (G.V (.top j)) (G.V (.top (j + 1))) (G.Λ (.top j)) (G.Λ (.top (j + 1))) (S.βp j) (S.βp (j + 1)) (locPl G t) e N r (isLattice_top G j.2.le) (isLattice_top G j.2) (S.βp_is j j.2.le) (S.βp_is (j + 1) j.2) he hr`.
-/
theorem isSBHalf_cosLoc_top (S : GridChoice W U) (t : T) {e : AE D} (he : IsIdemSum e (locPl G t)) (N : ℕ) (j : Fin D.R.m)
    {r : WO (G.pS (.top t j)) (G.pT (.top t j))} (hr : IsHalf e r) :
    IsSBHalf e (latO (G.pS (.top t j)) (G.pT (.top t j)) (G.latS (.top t j) : Set _) (G.latT (.top t j) : Set _) fun _ => True)
      (cosLoc (locPl G t) e (S.βp (j + 1)) (S.βp j) N r) :=
  GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (G.V (.top j)) (G.V (.top (j + 1))) (G.Λ (.top j)) (G.Λ (.top (j + 1))) (S.βp j) (S.βp (j + 1)) (locPl G t) e N r
    (isLattice_top G j.2.le) (isLattice_top G j.2) (S.βp_is j j.2.le) (S.βp_is (j + 1) j.2) he hr

/- English proof (translation)
Establish `hT : Submodule.IsLattice D.host.E (G.Λ (.grid i D.R.m))`. Break down `i with ⟨_ | i, hi⟩` into its components or cases. Conclude with `isLattice_grid_zero hL G`. Conclude with `isLattice_grid_succ G hi.le`. Conclude with `GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.Λ (.grid (i + 1) D.R.m)) (G.Λ (.grid i D.R.m)) (S.B.β (i + 1) D.R.m) (S.B.β i D.R.m) (locPl G t) e N r (isLattice_grid_succ G i.2) hT (S.B.isFrame_β hL i.2 le_rfl) (S.B.isFram …`.
-/
theorem isSBHalf_cosLoc_chi {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) {e : AE D} (he : IsIdemSum e (locPl G t))
    (N : ℕ) (i : Fin D.R.m) {r : WO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m))} (hr : IsHalf e r) :
    IsSBHalf e (latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.latS (.chi i D.R.m : Pair T) : Set _)
      (G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True)
      (cosLoc (locPl G t) e (S.B.β i D.R.m) (S.B.β (i + 1) D.R.m) N r) := by
  have hT : Submodule.IsLattice D.host.E (G.Λ (.grid i D.R.m)) := by
    rcases i with ⟨_ | i, hi⟩
    · exact isLattice_grid_zero hL G
    · exact isLattice_grid_succ G hi.le
  exact GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.Λ (.grid (i + 1) D.R.m)) (G.Λ (.grid i D.R.m))
    (S.B.β (i + 1) D.R.m) (S.B.β i D.R.m) (locPl G t) e N r (isLattice_grid_succ G i.2) hT
    (S.B.isFrame_β hL i.2 le_rfl) (S.B.isFrame_β hL i.2.le le_rfl) he hr

end SBs

section Main

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨e, he⟩` from `exists_idemSum_locPl' hL G t`. Establish `hm : 2 ≤ D.R.m` using `D.R.two_le_m`. Establish `hSB : ∀ w : locPl G t, ∃ n, IsSBArgs (locGrid G t w.1) (unifAt w.1) n (S.term t Φ β w).datum` using `fun w => by`. Establish `hg` using `(Good.locGrid_isGood hL G W t hde hc).1 w.1 w.2`. Establish `h00` using `hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)`.

Use `haveI := (isUnitVol_unitVol w.1).1`. Conclude with `exists_isSBArgs_flat (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1) (Tflip W S.B t Φ w.1) (keepAt G w.1) ((repsAt G t w.1).elt (β w)) hm h00.unif h00.cond (isTensor_Tflip hL W S.B t Φ hde hc w.2)`. Use `choose n hn using hSB`. Use `set N := Finset.univ.sup n with hN`. Establish `hF : ∀ w : locPl G t, IsSBArgs (locGrid G t w.1) (unifAt w.1) N (S.term t Φ β w).datum` using `fun w => (hn w).mono (isUnif_unifAt w.1) (Finset.le_sup (f := n) (Finset.mem_univ w))`.

Use `choose R hR1 hR2 hR3 using fun j : Fin D.R.m => GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (S.βp (j + 1)) (S.βp j) (locPl G t) e N he`. Use `choose R' hR1' hR2' hR3' using fun i : Fin D.R.m => GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (S.B.β i D.R.m) (S.B.β (i + 1) D.R.m) (locPl G t) e N he`. Set `Ix` to `(∀ j : Fin D.R.m, R j) × (∀ i : Fin D.R.m, R' i)`. Set `rX : Ix → ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))` to `fun κ j => (κ.1 j).1`. Set `rY : Ix → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))` to `fun κ i => (κ.2 i).1`.

Set `d : Ix → PureDat G t` to `fun κ => (fun j => finDatOf G t (.top t j) he _ (isSBHalf_cosLoc_top S t he N j (hR1 j _ (κ.1 j).2).1), fun i => finDatOf G t (.chi i D.R.m) he _ (isSBHalf_cosLoc_chi hL S t he N i (hR1' i _ (κ.2 i).2).1))`. Set `val : Ix → ℂ` to `fun κ => ∏ w, (S.term t Φ β w).datum (S.colAt t w (rX κ)) (S.rowAt t w (rY κ))`. Establish `hinj : Function.Injective d`. Introduce `κ₁ κ₂ h`. Use `Prod.ext (funext fun j => Subtype.ext ?_) (funext fun i => Subtype.ext ?_)` and prove the remaining obligations.

Establish `h1` using `congrFun (congrArg (fun D : PureDat G t => (D.1 j).fn) h) (rX κ₁ j)`. Express the relevant statement in the definitionally equal form `cosLoc _ _ _ _ _ (rX κ₁ j) (rX κ₁ j) = cosLoc _ _ _ _ _ (rX κ₂ j) (rX κ₁ j) at h1`. Rewrite `h1` using `[cosLoc_self (hR1 j _ (κ₁.1 j).2).1]`. Conclude with `hR3 j _ (κ₁.1 j).2 _ (κ₂.1 j).2 (cosLoc_of_ne_zero (h1 ▸ one_ne_zero)).2`. Establish `h1` using `congrFun (congrArg (fun D : PureDat G t => (D.2 i).fn) h) (rY κ₁ i)`.

Express the relevant statement in the definitionally equal form `cosLoc _ _ _ _ _ (rY κ₁ i) (rY κ₁ i) = cosLoc _ _ _ _ _ (rY κ₂ i) (rY κ₁ i) at h1`. Rewrite `h1` using `[cosLoc_self (hR1' i _ (κ₁.2 i).2).1]`. Conclude with `hR3' i _ (κ₁.2 i).2 _ (κ₂.2 i).2 (cosLoc_of_ne_zero (h1 ▸ one_ne_zero)).2`. Use `⟨Finsupp.mapDomain d (Finsupp.equivFunOnFinite.symm val), ⟨e, he, ?_, ?_⟩, e, N, he, ?_⟩` and prove the remaining obligations. Introduce `d' hd'`.

Take `⟨κ, -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hd')`. Conclude with `⟨fun j => ⟨rfl, rfl, rfl⟩, fun i => ⟨rfl, rfl, rfl⟩⟩`. Introduce `x y hx hy`. Rewrite using `[Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring), Finsupp.sum_fintype _ _ (fun _ => by simp)]`. Establish `hper : ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) (a : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (b : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G. …` using `fun x y a b ha hb => Finset.prod_congr rfl fun w _ => by`.

Rewrite using `[colAt_add, rowAt_add]`. Use `(hF w).per _ _ _ _ (fun j hj r s => ?_) (fun i hi r s => ?_)` and prove the remaining obligations. Rewrite using `[colAt_eq S t w _ hj]`. Use `ha ⟨j, hj⟩ w.1 w.2 (Fin.cast (topRank_eq G t w hj) r) (Fin.cast (topRank_eq G t w hj.le) s)` as an intermediate fact. Rewrite `this` using `[zpow_natCast]`.

Conclude with `this`. Rewrite using `[rowAt_eq S t w _ hi]`. Use `hb ⟨i, hi⟩ w.1 w.2 (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨hi.le, le_rfl⟩) r) (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨hi, le_rfl⟩) s)` as an intermediate fact. Rewrite `this` using `[zpow_natCast]`. Conclude with `this`.

Establish `hsupp : ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 → (∀ j : Fin D.R.m, IsHalf e (x j) ∧ IsSmall (locPl G t) (S.βp ((j : ℕ) + 1)) (S.βp j) (-(N : ℤ)) (x j)) ∧ ∀ i : Fin D.R.m, IsHalf e (y i) ∧ IsSmall (locPl G t) (S.B.β i D.R.m) (S.B.β ((i : ℕ) + 1) D.R.m) (-( …`. Introduce `hne`. Establish `hw : ∀ w : locPl G t, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0` using `fun w h0 => hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)`. Use `⟨fun j => ⟨hx j, fun w hwP r s => ?_⟩, fun i => ⟨hy i, fun w hwP r s => ?_⟩⟩` and prove the remaining obligations. Use `((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).1 j j.2 (Fin.cast (topRank_eq G t w j.2).symm r) (Fin.cast (topRank_eq G t w j.2.le).symm s)` as an intermediate fact.

Rewrite `this` using `[colAt_eq S t w x j.2]`. Rewrite using `[_root_.zpow_neg, zpow_natCast]`. Conclude with `this`. Use `((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).2 i i.2 (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨i.2.le, le_rfl⟩).symm r) (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨i.2, le_rfl⟩).symm s)` as an intermediate fact. Rewrite `this` using `[rowAt_eq S t w y i.2]`.

Rewrite using `[_root_.zpow_neg, zpow_natCast]`. Conclude with `this`. Establish `key` using `sum_reps_eq (ι := Fin D.R.m) (κ := Fin D.R.m) (A := fun j : Fin D.R.m => WO (G.V (.top j)) (G.V (.top (j + 1)))) (B := fun i : Fin D.R.m => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) (fun j a => IsSmall (locPl G t) (S.βp ((j : ℕ) + 1)) (S.βp j) N a) (fun i …`. Use `(Finset.sum_congr rfl fun q _ => ?_).trans key` and prove the remaining obligations. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`.

Conclude with `congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j _ => cosLoc_eq_ite (hx j))) (Finset.prod_congr rfl fun i _ => cosLoc_eq_ite (hy i))`. Introduce `d' hd'`. Take `⟨κ, -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hd')`. Use `⟨rX κ, rY κ, fun j => (hR1 j _ (κ.1 j).2).1, fun i => (hR1' i _ (κ.2 i).2).1, fun j => rfl, fun i => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_apply hinj]`.

Both sides reduce to the same expression.
-/
theorem GridChoice.exists_isCosExpansion {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (β : CosFam G t) :
    ∃ τ, S.IsCosExpansion t Φ β τ := by
  classical
  obtain ⟨e, he⟩ := exists_idemSum_locPl' hL G t
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hSB : ∀ w : locPl G t, ∃ n, IsSBArgs (locGrid G t w.1) (unifAt w.1) n (S.term t Φ β w).datum := fun w => by
    have hg := (Good.locGrid_isGood hL G W t hde hc).1 w.1 w.2
    have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
    haveI := (isUnitVol_unitVol w.1).1
    exact exists_isSBArgs_flat (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1)
      (Tflip W S.B t Φ w.1) (keepAt G w.1) ((repsAt G t w.1).elt (β w)) hm h00.unif h00.cond
      (isTensor_Tflip hL W S.B t Φ hde hc w.2)
  choose n hn using hSB
  set N := Finset.univ.sup n with hN
  have hF : ∀ w : locPl G t, IsSBArgs (locGrid G t w.1) (unifAt w.1) N (S.term t Φ β w).datum := fun w =>
    (hn w).mono (isUnif_unifAt w.1) (Finset.le_sup (f := n) (Finset.mem_univ w))
  choose R hR1 hR2 hR3 using fun j : Fin D.R.m => GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (S.βp (j + 1)) (S.βp j) (locPl G t) e N he
  choose R' hR1' hR2' hR3' using fun i : Fin D.R.m =>
    GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (S.B.β i D.R.m) (S.B.β (i + 1) D.R.m) (locPl G t) e N he
  let Ix := (∀ j : Fin D.R.m, R j) × (∀ i : Fin D.R.m, R' i)
  let rX : Ix → ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))) := fun κ j => (κ.1 j).1
  let rY : Ix → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) := fun κ i => (κ.2 i).1
  let d : Ix → PureDat G t := fun κ =>
    (fun j => finDatOf G t (.top t j) he _ (isSBHalf_cosLoc_top S t he N j (hR1 j _ (κ.1 j).2).1),
      fun i => finDatOf G t (.chi i D.R.m) he _ (isSBHalf_cosLoc_chi hL S t he N i (hR1' i _ (κ.2 i).2).1))
  let val : Ix → ℂ := fun κ => ∏ w, (S.term t Φ β w).datum (S.colAt t w (rX κ)) (S.rowAt t w (rY κ))
  have hinj : Function.Injective d := by
    intro κ₁ κ₂ h
    refine Prod.ext (funext fun j => Subtype.ext ?_) (funext fun i => Subtype.ext ?_)
    · have h1 := congrFun (congrArg (fun D : PureDat G t => (D.1 j).fn) h) (rX κ₁ j)
      change cosLoc _ _ _ _ _ (rX κ₁ j) (rX κ₁ j) = cosLoc _ _ _ _ _ (rX κ₂ j) (rX κ₁ j) at h1
      rw [cosLoc_self (hR1 j _ (κ₁.1 j).2).1] at h1
      exact hR3 j _ (κ₁.1 j).2 _ (κ₂.1 j).2 (cosLoc_of_ne_zero (h1 ▸ one_ne_zero)).2
    · have h1 := congrFun (congrArg (fun D : PureDat G t => (D.2 i).fn) h) (rY κ₁ i)
      change cosLoc _ _ _ _ _ (rY κ₁ i) (rY κ₁ i) = cosLoc _ _ _ _ _ (rY κ₂ i) (rY κ₁ i) at h1
      rw [cosLoc_self (hR1' i _ (κ₁.2 i).2).1] at h1
      exact hR3' i _ (κ₁.2 i).2 _ (κ₂.2 i).2 (cosLoc_of_ne_zero (h1 ▸ one_ne_zero)).2
  refine ⟨Finsupp.mapDomain d (Finsupp.equivFunOnFinite.symm val), ⟨e, he, ?_, ?_⟩, e, N, he, ?_⟩
  · intro d' hd'
    obtain ⟨κ, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hd')
    exact ⟨fun j => ⟨rfl, rfl, rfl⟩, fun i => ⟨rfl, rfl, rfl⟩⟩
  · intro x y hx hy

    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring), Finsupp.sum_fintype _ _ (fun _ => by simp)]
    have hper : ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
        (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))
        (a : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
        (b : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
        (∀ j : Fin D.R.m, IsSmall (locPl G t) (S.βp ((j : ℕ) + 1)) (S.βp j) N (a j)) →
        (∀ i : Fin D.R.m, IsSmall (locPl G t) (S.B.β i D.R.m) (S.B.β ((i : ℕ) + 1) D.R.m) N (b i)) →
        ∏ w, (S.term t Φ β w).datum (S.colAt t w (x + a)) (S.rowAt t w (y + b)) =
          ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) := fun x y a b ha hb =>
      Finset.prod_congr rfl fun w _ => by
        rw [colAt_add, rowAt_add]
        refine (hF w).per _ _ _ _ (fun j hj r s => ?_) (fun i hi r s => ?_)
        · rw [colAt_eq S t w _ hj]
          have := ha ⟨j, hj⟩ w.1 w.2 (Fin.cast (topRank_eq G t w hj) r) (Fin.cast (topRank_eq G t w hj.le) s)
          rw [zpow_natCast] at this
          exact this
        · rw [rowAt_eq S t w _ hi]
          have := hb ⟨i, hi⟩ w.1 w.2 (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨hi.le, le_rfl⟩) r)
            (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨hi, le_rfl⟩) s)
          rw [zpow_natCast] at this
          exact this
    have hsupp : ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 →
        (∀ j : Fin D.R.m, IsHalf e (x j) ∧ IsSmall (locPl G t) (S.βp ((j : ℕ) + 1)) (S.βp j) (-(N : ℤ)) (x j)) ∧
        ∀ i : Fin D.R.m, IsHalf e (y i) ∧ IsSmall (locPl G t) (S.B.β i D.R.m) (S.B.β ((i : ℕ) + 1) D.R.m) (-(N : ℤ)) (y i) := by
      intro hne
      have hw : ∀ w : locPl G t, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 := fun w h0 =>
        hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
      refine ⟨fun j => ⟨hx j, fun w hwP r s => ?_⟩, fun i => ⟨hy i, fun w hwP r s => ?_⟩⟩
      · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).1 j j.2 (Fin.cast (topRank_eq G t w j.2).symm r)
          (Fin.cast (topRank_eq G t w j.2.le).symm s)
        rw [colAt_eq S t w x j.2] at this
        rw [_root_.zpow_neg, zpow_natCast]
        exact this
      · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).2 i i.2
          (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨i.2.le, le_rfl⟩).symm r)
          (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨i.2, le_rfl⟩).symm s)
        rw [rowAt_eq S t w y i.2] at this
        rw [_root_.zpow_neg, zpow_natCast]
        exact this
    have key := sum_reps_eq (ι := Fin D.R.m) (κ := Fin D.R.m)
      (A := fun j : Fin D.R.m => WO (G.V (.top j)) (G.V (.top (j + 1))))
      (B := fun i : Fin D.R.m => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) (fun j a => IsSmall (locPl G t) (S.βp ((j : ℕ) + 1)) (S.βp j) N a)
      (fun i a => IsSmall (locPl G t) (S.B.β i D.R.m) (S.B.β ((i : ℕ) + 1) D.R.m) N a)
      (fun j a => IsHalf e a ∧ IsSmall (locPl G t) (S.βp ((j : ℕ) + 1)) (S.βp j) (-(N : ℤ)) a)
      (fun i a => IsHalf e a ∧ IsSmall (locPl G t) (S.B.β i D.R.m) (S.B.β ((i : ℕ) + 1) D.R.m) (-(N : ℤ)) a)
      (fun _ _ _ h h' => h.sub h') (fun _ _ _ h h' => h.sub h') R R' (fun j x h => hR2 j x h.1 h.2)
      (fun i y h => hR2' i y h.1 h.2) hR3 hR3' (fun x y => ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y))
      hper x y hsupp
    refine (Finset.sum_congr rfl fun q _ => ?_).trans key
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j _ => cosLoc_eq_ite (hx j)))
      (Finset.prod_congr rfl fun i _ => cosLoc_eq_ite (hy i))
  · intro d' hd'
    obtain ⟨κ, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hd')
    refine ⟨rX κ, rY κ, fun j => (hR1 j _ (κ.1 j).2).1, fun i => (hR1' i _ (κ.2 i).2).1, fun j => rfl, fun i => rfl, ?_⟩
    rw [Finsupp.mapDomain_apply hinj]
    rfl

/- English proof (translation)
Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `hcond : ∀ w ∈ locPl G t, HasConductor (psiAt W w) 1` using `fun w hw => (((Good.locGrid_isGood hL G W t hde hc).1 w hw).square 0 hm 0 hm).cond`. Use `⟨fun w hw => ?_, ?_, fun β => S.exists_isCosExpansion hL t Φ hde hc β⟩` and prove the remaining obligations. Use `haveI := (isUnitVol_unitVol w).1`. Conclude with `flatIntegrable one_le_sLen (psiAt W w) (unitVol w) (isUnif_unifAt w) (hcond w hw).continuous (isTensor_Tflip hL W S.B t Φ hde hc hw)`.

Use `Set.Finite.subset (Set.Finite.pi' (κ := fun w : locPl G t => Cosets (G := locGrid G t w.1) one_le_sLen (givenLevel G t w.1)) (t := fun w : locPl G t => unfSupport (psiAt W w.1) (unitVol w.1) (keepAt G w.1) (repsAt G t w.1) (Tflip W S.B t Φ w.1)) fun w => ?_) fun β hβ => hβ haveI …` and prove the remaining obligations. Establish `hT` using `isTensor_Tflip hL W S.B t Φ hde hc w.2`. Establish `hE : Even (locGrid G t w.1).m` using `D.R.m_even`. Establish `hJ : ∀ j, 0 < j → j < (locGrid G t w.1).m → IsOpen (givenLevel G t w.1 ((locGrid G t w.1).m, j) : Set (GL (Fin ((locGrid G t w.1).rank ((locGrid G t w.1).m, j))) (Kw w.1)))` using `fun j _ _ => (GivenAdm.givenLevel_open hL w.2 _).1`. Conclude with `FiniteSupport.finite_unfSupport (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1) (Tflip W S.B t Φ w.1) (givenLevel G t w.1) hE (isUnif_unifAt w.1) (hcond w.1 w.2) hT hJ (keepAt G w.1) (repsAt G t w.1)`.
-/
theorem GridChoice.sumOK_flat_fin_ex {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    (∀ w ∈ locPl G t, FlatIntegrable (G := locGrid G t w) one_le_sLen (psiAt W w) (unitVol w) (Tflip W S.B t Φ w)) ∧
      (S.supp t Φ).Finite ∧ ∀ β, ∃ τ, S.IsCosExpansion t Φ β τ := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : ∀ w ∈ locPl G t, HasConductor (psiAt W w) 1 := fun w hw =>
    (((Good.locGrid_isGood hL G W t hde hc).1 w hw).square 0 hm 0 hm).cond
  refine ⟨fun w hw => ?_, ?_, fun β => S.exists_isCosExpansion hL t Φ hde hc β⟩
  · haveI := (isUnitVol_unitVol w).1
    exact flatIntegrable one_le_sLen (psiAt W w) (unitVol w) (isUnif_unifAt w) (hcond w hw).continuous
      (isTensor_Tflip hL W S.B t Φ hde hc hw)
  · refine Set.Finite.subset (Set.Finite.pi' (κ := fun w : locPl G t => Cosets (G := locGrid G t w.1) one_le_sLen
      (givenLevel G t w.1)) (t := fun w : locPl G t => unfSupport (psiAt W w.1) (unitVol w.1) (keepAt G w.1)
      (repsAt G t w.1) (Tflip W S.B t Φ w.1)) fun w => ?_) fun β hβ => hβ
    haveI := (isUnitVol_unitVol w.1).1
    have hT := isTensor_Tflip hL W S.B t Φ hde hc w.2
    have hE : Even (locGrid G t w.1).m := D.R.m_even
    have hJ : ∀ j, 0 < j → j < (locGrid G t w.1).m →
        IsOpen (givenLevel G t w.1 ((locGrid G t w.1).m, j) : Set (GL (Fin ((locGrid G t w.1).rank
          ((locGrid G t w.1).m, j))) (Kw w.1))) := fun j _ _ => (GivenAdm.givenLevel_open hL w.2 _).1
    exact FiniteSupport.finite_unfSupport (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1)
      (depthAt G w.1) (Tflip W S.B t Φ w.1) (givenLevel G t w.1) hE (isUnif_unifAt w.1) (hcond w.1 w.2) hT hJ
      (keepAt G w.1) (repsAt G t w.1)

/- English proof (translation)
Introduce `β _` and use `let ⟨τ, h⟩ := S.exists_isCosExpansion hL t Φ hde hc β ⟨τ, h.1⟩`.
-/
theorem GridChoice.sumOK_ex {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∀ β ∈ S.supp t Φ, ∃ τ, S.IsExpansion t Φ β τ := fun β _ =>
  let ⟨τ, h⟩ := S.exists_isCosExpansion hL t Φ hde hc β
  ⟨τ, h.1⟩

end Main

end GlobalTheory.FunObj

end
