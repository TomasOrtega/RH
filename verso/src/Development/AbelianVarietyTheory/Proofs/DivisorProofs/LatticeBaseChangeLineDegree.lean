import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LineBCTower

/- English proof (translation)
Use `set k : (Fin m → K') → (Fin m → K'') := fun v i => algebraMap K' K'' (v i) with hk`. Establish `hfac : ∀ v : Fin m → K, (fun i => algebraMap K K'' (v i)) = k (fun i => algebraMap K K' (v i))`. Introduce `v`. Use function extensionality and compare the values at `i`. Simplify using `[k, IsScalarTower.algebraMap_apply K K' K'']`.

Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `show (fun i => algebraMap K K'' (v i)) ∈ _`. Rewrite using `[hfac]`.

Conclude with `Submodule.subset_span ⟨_, Submodule.subset_span ⟨v, hv, rfl⟩, rfl⟩`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Express the relevant statement in the definitionally equal form `k w ∈ latBC K'' L`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Express the relevant statement in the definitionally equal form `k (fun i => algebraMap K K' (v i)) ∈ _`. Rewrite using `[← hfac]`. Conclude with `Submodule.subset_span ⟨v, hv, rfl⟩`.

Consider the case `zero`. Establish `: k 0 = 0` using `by funext i; simp [k]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`.

Establish `: k (x + y) = k x + k y` using `by funext i; simp [k]`. Rewrite using `[this]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `: k (a • x) = (algebraMap (𝓞 K') (𝓞 K'') a) • k x`.

Use function extensionality and compare the values at `i`. Simplify using `only [k, Pi.smul_apply, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem latBC_tower (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K'']
    [NumberField K''] [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) : latBC K'' L = latBC K'' (latBC K' L) := by
  set k : (Fin m → K') → (Fin m → K'') := fun v i => algebraMap K' K'' (v i) with hk
  have hfac : ∀ v : Fin m → K, (fun i => algebraMap K K'' (v i)) = k (fun i => algebraMap K K' (v i)) := by
    intro v; funext i; simp [k, IsScalarTower.algebraMap_apply K K' K'']
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    show (fun i => algebraMap K K'' (v i)) ∈ _
    rw [hfac]
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨v, hv, rfl⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    change k w ∈ latBC K'' L
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        change k (fun i => algebraMap K K' (v i)) ∈ _
        rw [← hfac]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    | zero =>
        have : k 0 = 0 := by funext i; simp [k]
        rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
        have : k (x + y) = k x + k y := by funext i; simp [k]
        rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
        have : k (a • x) = (algebraMap (𝓞 K') (𝓞 K'') a) • k x := by
          funext i
          simp only [k, Pi.smul_apply, Algebra.smul_def, map_mul]
          rfl
        rw [this]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `σ i j`. Rewrite using `[h2 σ i j, h1 (σ.comp (algebraMap K' K'')) i j, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]`.
-/
theorem isBC_tower {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K'']
    [NumberField K''] [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] {m : ℕ}
    {h : HermFam K (Fin m → K)} {h' : HermFam K' (Fin m → K')} {h'' : HermFam K'' (Fin m → K'')}
    (h1 : IsBC h h') (h2 : IsBC h h'') : IsBC h' h'' := by
  intro σ i j
  rw [h2 σ i j, h1 (σ.comp (algebraMap K' K'')) i j, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

/- English proof (translation)
Introduce `K K' K'' _ _ _ _ _ _ _ _ _ _ m h h' h'' L x hL h1 h2`. Use `⟨(GlobalTheory.T.hermitian_lattice_base_change K K'' m h L hL.1).2.1 hL, ?_⟩` and prove the remaining obligations. Establish `hL' : (latBC K' L).FG` using `GlobalTheory.Published.SiegelModel.latBC_fg K' hL.1`. Establish `h12 : IsBC h' h''` using `isBC_tower h1 h2`. Take `⟨_, _, hA⟩` from `GlobalTheory.T.hermitian_lattice_base_change K' K'' m h' (latBC K' L) hL'`.

Take `⟨_, _, hB⟩` from `GlobalTheory.T.hermitian_lattice_base_change K' K'' m h' (lineLat (latBC K' L) x) (GlobalTheory.Published.SiegelModel.lineLat_fg hL' x)`. Rewrite using `[latBC_tower K K' K'' m L, ← (hA h'' h12).2.2 x]`. Conclude with `(hB h'' h12).1`.
-/
theorem lineLat_deg_tower : ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] (m : ℕ) (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')) (h'' : HermFam K'' (Fin m → K'')) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K'), Full L → IsBC h h' → IsBC h h'' → Full (latBC K'' L) ∧ deg h'' (lineLat (latBC K'' L) (fun i => algebraMap K' K'' (x i))) = deg h' (lineLat (latBC K' L) x) := by
  intro K K' K'' _ _ _ _ _ _ _ _ _ _ m h h' h'' L x hL h1 h2
  refine ⟨(GlobalTheory.T.hermitian_lattice_base_change K K'' m h L hL.1).2.1 hL, ?_⟩
  have hL' : (latBC K' L).FG := GlobalTheory.Published.SiegelModel.latBC_fg K' hL.1
  have h12 : IsBC h' h'' := isBC_tower h1 h2
  obtain ⟨_, _, hA⟩ := GlobalTheory.T.hermitian_lattice_base_change K' K'' m h' (latBC K' L) hL'
  obtain ⟨_, _, hB⟩ := GlobalTheory.T.hermitian_lattice_base_change K' K'' m h' (lineLat (latBC K' L) x)
    (GlobalTheory.Published.SiegelModel.lineLat_fg hL' x)
  rw [latBC_tower K K' K'' m L, ← (hA h'' h12).2.2 x]
  exact (hB h'' h12).1

end GlobalTheory.LineBCTower
