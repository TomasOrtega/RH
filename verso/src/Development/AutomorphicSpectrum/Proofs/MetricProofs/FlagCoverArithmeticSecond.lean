import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Set `θ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ` to `aeval fun k => C (c k) * X k`. Establish `key : ∀ f : MRing ι, mConeMap (fun p => c p.1 * z' p) f = θ (mConeMap z' f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp]`. Use `congr 1`.

Simplify using `[mConeMap, θ, mul_assoc, mul_left_comm]`. Introduce `f hf`. Establish `hf' : mConeMap z' f = 0` using `hf`. Use `show mConeMap _ f = 0`. Rewrite using `[key, hf', map_zero]`.
-/
theorem mCoordIdeal_le_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  let θ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k) * X k
  have key : ∀ f : MRing ι, mConeMap (fun p => c p.1 * z' p) f = θ (mConeMap z' f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      simp [mConeMap, θ, mul_assoc, mul_left_comm]
  intro f hf
  have hf' : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [key, hf', map_zero]

/- English proof (translation)
The claim follows from `le_antisymm (mCoordIdeal_le_of_sameOrbit (Cj.sameOrbit_symm h)) (mCoordIdeal_le_of_sameOrbit h)`.
-/
theorem mCoordIdeal_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le_of_sameOrbit (Cj.sameOrbit_symm h)) (mCoordIdeal_le_of_sameOrbit h)

/- English proof (translation)
Introduce `e` and use `h (by show mConeMap z (X q) = 0 rw [mConeMap, aeval_X, e, map_zero, zero_mul])`.
-/
theorem coord_ne_of_X_notMem {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) :
    z q ≠ 0 := fun e => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

end Orbit

section Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω Ω' : Type} [Field Ω] [Field Ω']

/- English proof (translation)
Establish `key : ∀ f : MRing ι, mConeMap x' (rename v f) = rename κ (map φ (mConeMap x f))`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp, rename_X]`. Use `congr 1`. Simplify using `[mConeMap, hx, hv.2.2.1 i]`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hz.1 (κ k)`. Take `⟨p, hp⟩` from `hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩`. Take `⟨k₁, i₁⟩` from `p`. Establish `e : k₁ = k` using `hv.1 (by rw [← hv.2.2.1 ⟨k₁, i₁⟩, hp])`. Substitute `e` using the available equality.

Conclude with `⟨i₁, by simpa [Function.comp, hp] using hi⟩`. Establish `hf' : mConeMap x f = 0` using `hf`. Establish `h1 : rename v f ∈ mCoordIdeal x'` using `by show mConeMap x' (rename v f) = 0`. Rewrite using `[key, hf', map_zero, map_zero]`. Establish `h2` using `hz.2 _ h1`.

Rewrite `h2` using `[map_rename, eval_rename]`. Then use the resulting hypothesis.
-/
theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) (φ : Ω →+* Ω')
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : ∀ q, x' (v q) = φ (x q))
    {zb : (Σ k, ι' k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x')) : zb ∘ v ∈ mcPts (mCoordIdeal x) := by
  have key : ∀ f : MRing ι, mConeMap x' (rename v f) = rename κ (map φ (mConeMap x f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hx, hv.2.2.1 i]
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    obtain ⟨k₁, i₁⟩ := p
    have e : k₁ = k := hv.1 (by rw [← hv.2.2.1 ⟨k₁, i₁⟩, hp])
    subst e
    exact ⟨i₁, by simpa [Function.comp, hp] using hi⟩
  · have hf' : mConeMap x f = 0 := hf
    have h1 : rename v f ∈ mCoordIdeal x' := by
      show mConeMap x' (rename v f) = 0
      rw [key, hf', map_zero, map_zero]
    have h2 := hz.2 _ h1
    rwa [map_rename, eval_rename] at h2

end Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

/- English proof (translation)
Establish `hbase : basePart M.blk z = basePart M.blk z'`. Take `⟨c, -, e⟩` from `hb`. Establish `hc : ∀ k, c k = 1` using `fun k => by`. Use `congrFun e ⟨k, F.c k⟩` as an intermediate fact. Rewrite `this` using `[H.1 k, H'.1 k, mul_one]`.

Conclude with `this.symm`. Rewrite using `[e]`. Use function extensionality and compare the values at `p`. Simplify using `[hc]`. Establish `blockwise : ∀ k, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = t * z' ⟨k, m⟩`.

Introduce `k`. Distinguish the cases in `hk : ∀ p, M.blk p ≠ some k`. Conclude with `⟨1, one_ne_zero, fun m => by`. Simplify `congrFun hbase ⟨⟨k, hk⟩, m⟩⟩` using `[basePart]`. Use `push_neg at hk`.

Take `⟨p, hp⟩` from `hk`. Take `⟨a, ha, ea⟩` from `H.2.2 p k hp`. Take `⟨a', ha', ea'⟩` from `H'.2.2 p k hp`. Use `⟨a / a', div_ne_zero ha ha', fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[ea m, ea' m, hbase]`.

Clear the denominators using the available nonvanishing facts. Use `choose t ht e using blockwise`. Conclude with `⟨t, ht, funext fun p => e p.1 p.2⟩`.
-/
theorem sameOrbit_of_isFlagOf (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {z z' : (Σ k, ι k) → ℂ} {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hb : SameOrbit (basePart M.blk z) (basePart M.blk z')) (H : M.IsFlagOf F z h) (H' : M.IsFlagOf F z' h) :
    SameOrbit z z' := by
  have hbase : basePart M.blk z = basePart M.blk z' := by
    obtain ⟨c, -, e⟩ := hb
    have hc : ∀ k, c k = 1 := fun k => by
      have := congrFun e ⟨k, F.c k⟩
      rw [H.1 k, H'.1 k, mul_one] at this
      exact this.symm
    rw [e]
    funext p
    simp [hc]
  have blockwise : ∀ k, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = t * z' ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact ⟨1, one_ne_zero, fun m => by
        simpa [basePart] using congrFun hbase ⟨⟨k, hk⟩, m⟩⟩
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      obtain ⟨a, ha, ea⟩ := H.2.2 p k hp
      obtain ⟨a', ha', ea'⟩ := H'.2.2 p k hp
      refine ⟨a / a', div_ne_zero ha ha', fun m => ?_⟩
      rw [ea m, ea' m, hbase]
      field_simp
  choose t ht e using blockwise
  exact ⟨t, ht, funext fun p => e p.1 p.2⟩

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w w' hw hw'`. Take `⟨-, fr, -⟩` from `GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M`. Take `⟨bs', fr', fl'⟩` from `GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'`. Take `⟨F', hF', hG'⟩` from `fr' _ (bs' z hz)`. Establish `hne : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0` using `fun k => coord_ne_of_X_notMem (hG'.1 k)`.

Set `c : K' → ℂ` to `fun k => if h : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, h⟩, F'.c ⟨k, h⟩⟩)⁻¹ else 1`. Establish `hcb : ∀ k : NonPluckerBlocks M'.blk, c k.1 = (basePart M'.blk z ⟨k, F'.c k⟩)⁻¹` using `fun k => dif_pos k.2`. Establish `hc : ∀ k, c k ≠ 0` using `fun k => by`. Distinguish the cases in `h : ∀ p, M'.blk p ≠ some k`. Rewrite using `[hcb ⟨k, h⟩]`.

Conclude with `inv_ne_zero (hne ⟨k, h⟩)`. Simplify using `only [c, dif_neg h]`. Conclude with `one_ne_zero`. Set `z₁ : (Σ k, ι' k) → ℂ` to `fun p => c p.1 * z p`. Establish `h1 : SameOrbit z₁ z` using `⟨c, hc, rfl⟩`.

Establish `hz₁ : z₁ ∈ mcPts (mCoordIdeal y')` using `mcPts_smul hA'.2.1.2.1 c hc hz`. Establish `hb1 : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z)` using `⟨fun k => c k.1, fun k => hc k.1, rfl⟩`. Establish `hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁))`. Rewrite using `[mCoordIdeal_eq_of_sameOrbit hb1]`. Conclude with `hG'`.

Establish `hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1` using `fun k => by show c k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1`. Rewrite using `[hcb k]`. Conclude with `inv_mul_cancel₀ (hne k)`. Take `⟨h, hh⟩` from `(fl' F' hF' z₁ (bs' z₁ hz₁) hG₁ hnorm).1 hz₁`. Take `⟨F, hF, hG⟩` from `fr _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq (bs' z₁ hz₁))`.

Take `⟨z₀, a, b, e⟩` from `hw z₁ h1 F' F hF' hF hG₁ hG h hh`. Take `⟨z₀', a', b', e'⟩` from `hw' z₁ h1 F' F hF' hF hG₁ hG h hh`. Conclude with `Cj.sameOrbit_trans (Cj.sameOrbit_symm a) (Cj.sameOrbit_trans (sameOrbit_of_isFlagOf M (Cj.sameOrbit_trans b (Cj.sameOrbit_symm b')) e e') a')`.
-/
theorem isImg_unique : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w w' hw hw'
  obtain ⟨-, fr, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨bs', fr', fl'⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hG'⟩ := fr' _ (bs' z hz)
  have hne : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0 := fun k =>
    coord_ne_of_X_notMem (hG'.1 k)
  let c : K' → ℂ := fun k =>
    if h : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, h⟩, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M'.blk, c k.1 = (basePart M'.blk z ⟨k, F'.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · rw [hcb ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hb1 : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) :=
    ⟨fun k => c k.1, fun k => hc k.1, rfl⟩
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq_of_sameOrbit hb1]
    exact hG'
  have hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1
    rw [hcb k]
    exact inv_mul_cancel₀ (hne k)
  obtain ⟨h, hh⟩ := (fl' F' hF' z₁ (bs' z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨F, hF, hG⟩ := fr _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq (bs' z₁ hz₁))
  obtain ⟨z₀, a, b, e⟩ := hw z₁ h1 F' F hF' hF hG₁ hG h hh
  obtain ⟨z₀', a', b', e'⟩ := hw' z₁ h1 F' F hF' hF hG₁ hG h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm a) (Cj.sameOrbit_trans
    (sameOrbit_of_isFlagOf M (Cj.sameOrbit_trans b (Cj.sameOrbit_symm b')) e e') a')

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
