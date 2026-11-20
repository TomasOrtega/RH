import Mathlib
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric.FamilyInverse

/- English proof (translation)
Set `Φ : B × V → B × V` to `fun p => (p.1, d p)`. Set `L : (B × V) →L[ℂ] (B × V)` to `(ContinuousLinearMap.fst ℂ B V).prod ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V)`. Set `L' : (B × V) →L[ℂ] (B × V)` to `(ContinuousLinearMap.fst ℂ B V).prod ((2⁻¹ : ℂ) • ContinuousLinearMap.snd ℂ B V)`. Set `Le : (B × V) ≃L[ℂ] (B × V)` to `ContinuousLinearEquiv.equivOfInverse L L' (fun p => by simp [L, L', smul_smul]) (fun p => by simp [L, L', smul_smul])`. Establish `hLe : (Le : (B × V) →L[ℂ] (B × V)) = L` using `rfl`.

Establish `hΦan : AnalyticAt ℂ Φ (b₀, 0)` using `analyticAt_fst.prod han`. Establish `hΦd : HasFDerivAt Φ L (b₀, 0)` using `hasFDerivAt_fst.prodMk hd`. Establish `hs : HasStrictFDerivAt Φ (Le : (B × V) →L[ℂ] (B × V)) (b₀, 0)`. Use `hΦan.hasStrictFDerivAt` as an intermediate fact. Rewrite `this` using `[hΦd.fderiv, ← hLe]`. Then use the resulting hypothesis.

Establish `hfix : Φ (b₀, 0) = (b₀, 0)` using `by simp [Φ, h0]`. Set `P` to `hs.toOpenPartialHomeomorph Φ`. Establish `hPc : (P : B × V → B × V) = Φ` using `hs.toOpenPartialHomeomorph_coe`. Establish `hPan : AnalyticAt ℂ P.symm (P (b₀, 0))` using `P.analyticAt_symm' (i := Le) hs.mem_toOpenPartialHomeomorph_source (by rw [hPc]; exact hΦan) (by rw [hPc, hΦd.fderiv, hLe])`. Establish `hΨan : AnalyticAt ℂ P.symm (b₀, 0)`.

Establish `: P (b₀, 0) = (b₀, 0)` using `by rw [hPc]; exact hfix`. Rewrite `hPan` using `[this]`. Then use the resulting hypothesis. Establish `hright : ∀ᶠ q in 𝓝 (b₀, 0), Φ (P.symm q) = q`. Use `hs.eventually_right_inverse` as an intermediate fact. Rewrite `this` using `[hfix]`.

Conclude with `this`. Establish `hleft : ∀ᶠ p in 𝓝 (b₀, 0), P.symm (Φ p) = p` using `hs.eventually_left_inverse`. Establish `hΨ0 : P.symm (b₀, 0) = (b₀, 0)`. Use `hs.localInverse_apply_image` as an intermediate fact. Rewrite `this` using `[hfix]`.

Conclude with `this`. Use `⟨fun q => (P.symm q).2, analyticAt_snd.comp hΨan, by simp [hΨ0], ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hright] with q hq`. Establish `e1` using `congrArg Prod.fst hq`. Establish `e2` using `congrArg Prod.snd hq`.

Establish `h1 : (P.symm q).1 = q.1` using `e1`. Establish `h2 : d (P.symm q) = q.2` using `e2`. Establish `h3 : (q.1, (P.symm q).2) = P.symm q` using `by rw [← h1]`. Rewrite using `[h3, h2]`. Use `filter_upwards [hleft] with p hp`.

Establish `e` using `congrArg Prod.snd hp`. Conclude with `e`.
-/
theorem exists_analytic_family_inverse {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (b₀ : B) (d : B × V → V) (han : AnalyticAt ℂ d (b₀, 0)) (h0 : d (b₀, 0) = 0)
    (hd : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0)) :
    ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  let Φ : B × V → B × V := fun p => (p.1, d p)
  let L : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let L' : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2⁻¹ : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let Le : (B × V) ≃L[ℂ] (B × V) :=
    ContinuousLinearEquiv.equivOfInverse L L'
      (fun p => by simp [L, L', smul_smul]) (fun p => by simp [L, L', smul_smul])
  have hLe : (Le : (B × V) →L[ℂ] (B × V)) = L := rfl
  have hΦan : AnalyticAt ℂ Φ (b₀, 0) := analyticAt_fst.prod han
  have hΦd : HasFDerivAt Φ L (b₀, 0) := hasFDerivAt_fst.prodMk hd
  have hs : HasStrictFDerivAt Φ (Le : (B × V) →L[ℂ] (B × V)) (b₀, 0) := by
    have := hΦan.hasStrictFDerivAt
    rwa [hΦd.fderiv, ← hLe] at this
  have hfix : Φ (b₀, 0) = (b₀, 0) := by simp [Φ, h0]
  let P := hs.toOpenPartialHomeomorph Φ
  have hPc : (P : B × V → B × V) = Φ := hs.toOpenPartialHomeomorph_coe
  have hPan : AnalyticAt ℂ P.symm (P (b₀, 0)) :=
    P.analyticAt_symm' (i := Le) hs.mem_toOpenPartialHomeomorph_source
      (by rw [hPc]; exact hΦan) (by rw [hPc, hΦd.fderiv, hLe])
  have hΨan : AnalyticAt ℂ P.symm (b₀, 0) := by
    have : P (b₀, 0) = (b₀, 0) := by rw [hPc]; exact hfix
    rwa [this] at hPan
  have hright : ∀ᶠ q in 𝓝 (b₀, 0), Φ (P.symm q) = q := by
    have := hs.eventually_right_inverse
    rw [hfix] at this
    exact this
  have hleft : ∀ᶠ p in 𝓝 (b₀, 0), P.symm (Φ p) = p := hs.eventually_left_inverse
  have hΨ0 : P.symm (b₀, 0) = (b₀, 0) := by
    have := hs.localInverse_apply_image
    rw [hfix] at this
    exact this
  refine ⟨fun q => (P.symm q).2, analyticAt_snd.comp hΨan, by simp [hΨ0], ?_, ?_⟩
  · filter_upwards [hright] with q hq
    have e1 := congrArg Prod.fst hq
    have e2 := congrArg Prod.snd hq
    have h1 : (P.symm q).1 = q.1 := e1
    have h2 : d (P.symm q) = q.2 := e2
    have h3 : (q.1, (P.symm q).2) = P.symm q := by rw [← h1]
    rw [h3, h2]
  · filter_upwards [hleft] with p hp
    have e := congrArg Prod.snd hp
    exact e

end GlobalTheory.CompanionTheory.Metric.FamilyInverse
