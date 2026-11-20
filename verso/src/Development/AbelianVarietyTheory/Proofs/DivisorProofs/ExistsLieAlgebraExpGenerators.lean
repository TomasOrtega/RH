import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup

noncomputable section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ClosedMonoid

open GlobalTheory.ClosedMatGroup

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro g _`. Simplify using `using contDiff_const`. Consider the case `succ n ih`.

Introduce `g hg`. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Conclude with `(hg 0).mul (ih _ fun i => hg _)`.
-/
theorem contDiff_ofFn_prod {𝔸 E : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (n : ℕ) (g : Fin n → E → 𝔸), (∀ i, ContDiff ℝ ∞ (g i)) →
      ContDiff ℝ ∞ (fun z => (List.ofFn fun i => g i z).prod) := by
  intro n
  induction n with
  | zero => intro g _; simpa using contDiff_const
  | succ n ih =>
    intro g hg
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hg 0).mul (ih _ fun i => hg _)

/- English proof (translation)
Introduce `𝔸 _ _ _ _ S hc h1 hm hi d Z hZ hspan`. Set `_ : NormedAlgebra ℚ 𝔸` to `NormedAlgebra.restrictScalars ℚ ℝ 𝔸`. Set `L` to `lieSub S hc h1 hm`. Take `⟨W, hW⟩` from `L.exists_isCompl`. Set `F : (Fin d → ℝ) →ₗ[ℝ] 𝔸` to `Fintype.linearCombination ℝ Z`.

Establish `hF : ∀ v, F v = ∑ i, v i • Z i` using `fun v => Fintype.linearCombination_apply ℝ Z v`. Establish `hLF : L ≤ LinearMap.range F`. Introduce `x hx`. Rewrite using `[Fintype.range_linearCombination]`. Conclude with `hspan x hx`.

Take `⟨g, hg⟩` from `F.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict F)`. Set `c : 𝔸 →L[ℝ] (Fin d → ℝ)` to `LinearMap.toContinuousLinearMap (g ∘ₗ (Submodule.inclusion hLF) ∘ₗ L.projectionOnto W hW)`. Set `p : 𝔸 →L[ℝ] 𝔸` to `LinearMap.toContinuousLinearMap (L.projection W hW)`. Establish `hpc : ∀ z, ∑ i, c z i • Z i = p z`. Introduce `z`.

Rewrite using `[← hF]`. Establish `e` using `congrArg Subtype.val (LinearMap.congr_fun hg (Submodule.inclusion hLF (L.projectionOnto W hW z)))`. Conclude with `e`. Establish `hqW : ∀ z, z - p z ∈ W` using `fun z => by`. Establish `h` using `Submodule.projection_add_projection_eq_self hW z`.

Establish `e : z - p z = W.projection _ hW.symm z`. Rewrite using `[sub_eq_iff_eq_add']`. Conclude with `h.symm`. Rewrite using `[e]`. Conclude with `Submodule.projection_apply_mem hW.symm z`.

Set `Φ : 𝔸 → 𝔸` to `fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod * NormedSpace.exp (z - p z)`. Establish `hexpS : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸)` using `contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt`. Establish `hΦs : ContDiff ℝ ∞ Φ`. Use `(contDiff_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) fun i => ?_).mul ?_` and prove the remaining obligations. Conclude with `hexpS.comp ((((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).contDiff)`.

Conclude with `hexpS.comp ((ContinuousLinearMap.id ℝ 𝔸 - p).contDiff)`. Establish `hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸)` using `hasStrictFDerivAt_exp_zero`. Establish `hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i)) ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0` using `fun i => HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp) (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt`. Establish `hP` using `hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0 (fun i => by simp) hf`. Establish `h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z)) ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0` using `HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp) (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt`.

Establish `h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0`. Use `(hP.mul' h2).congr_fderiv ?_` and prove the remaining obligations. Use `ext1 z`. Establish `e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1` using `by simp`. Simplify using `[e1, hpc]`.

Establish `hΦ0 : Φ 0 = 1` using `by show (List.ofFn fun i => NormedSpace.exp (c 0 i • Z i)).prod * NormedSpace.exp (0 - p 0) = 1`. Simplify using the standard rewrite rules. Establish `hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0` using `by simp`. Establish `hΦa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ 0` using `hΦs.contDiffAt`. Set `Ψ` to `hΦa.localInverse h4.hasFDerivAt hn`.

Establish `hΨs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ 1`. Establish `h` using `hΦa.to_localInverse h4.hasFDerivAt hn`. Rewrite `h` using `[hΦ0]`. Conclude with `h`. Establish `h4'` using `hΦa.hasStrictFDerivAt' h4.hasFDerivAt hn`.

Establish `hΨ : Tendsto Ψ (𝓝 1) (𝓝 0)`. Establish `h` using `h4'.localInverse_tendsto`. Rewrite `h` using `[hΦ0]`. Conclude with `h`. Establish `hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X`.

Establish `h` using `h4'.eventually_right_inverse`. Rewrite `h` using `[hΦ0]`. Conclude with `h`. Establish `hp0 : Tendsto p (𝓝 0) (𝓝 0)` using `by simpa using p.continuous.tendsto 0`. Establish `hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸))`.

Simplify using `using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0`. Use `⟨fun X => c (Ψ X), c.contDiff.contDiffAt.comp 1 hΨs, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))] with X hX1 hX2 hXS`. Take `⟨Q, hQ, hQe⟩` from `exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i) (fun i => by rw [← neg_smul]; exact hZ i _)`. Establish `hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X` using `by conv_rhs => rw [← hX1] show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))`.

Rewrite using `[← mul_assoc, hQe, one_mul]`. Establish `hw` using `hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hw, NormedSpace.exp_zero, mul_one]`.
-/
theorem coords_second_kind_of_spanning : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (S : Set 𝔸), IsClosed S → (1 : 𝔸) ∈ S →
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) → (∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) →
    ∀ (d : ℕ) (Z : Fin d → 𝔸), (∀ (i : Fin d) (t : ℝ), NormedSpace.exp (t • Z i) ∈ S) →
    (∀ Y : 𝔸, (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ S) → Y ∈ Submodule.span ℝ (Set.range Z)) →
    ∃ s : 𝔸 → Fin d → ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s 1 ∧
      ∀ᶠ X in nhds (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  intro 𝔸 _ _ _ _ S hc h1 hm hi d Z hZ hspan
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let L := lieSub S hc h1 hm
  obtain ⟨W, hW⟩ := L.exists_isCompl
  let F : (Fin d → ℝ) →ₗ[ℝ] 𝔸 := Fintype.linearCombination ℝ Z
  have hF : ∀ v, F v = ∑ i, v i • Z i := fun v => Fintype.linearCombination_apply ℝ Z v
  have hLF : L ≤ LinearMap.range F := by
    intro x hx
    rw [Fintype.range_linearCombination]
    exact hspan x hx
  obtain ⟨g, hg⟩ := F.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict F)
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap
    (g ∘ₗ (Submodule.inclusion hLF) ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    rw [← hF]
    have e := congrArg Subtype.val (LinearMap.congr_fun hg (Submodule.inclusion hLF (L.projectionOnto W hW z)))
    exact e
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let Φ : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod * NormedSpace.exp (z - p z)
  have hexpS : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hΦs : ContDiff ℝ ∞ Φ := by
    refine (contDiff_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) fun i => ?_).mul ?_
    · exact hexpS.comp ((((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).contDiff)
    · exact hexpS.comp ((ContinuousLinearMap.id ℝ 𝔸 - p).contDiff)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show (List.ofFn fun i => NormedSpace.exp (c 0 i • Z i)).prod * NormedSpace.exp (0 - p 0) = 1
    simp
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΦa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ 0 := hΦs.contDiffAt
  let Ψ := hΦa.localInverse h4.hasFDerivAt hn
  have hΨs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ 1 := by
    have h := hΦa.to_localInverse h4.hasFDerivAt hn
    rw [hΦ0] at h
    exact h
  have h4' := hΦa.hasStrictFDerivAt' h4.hasFDerivAt hn
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4'.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4'.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨fun X => c (Ψ X), c.contDiff.contDiffAt.comp 1 hΨs, ?_⟩
  filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
    with X hX1 hX2 hXS
  obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
    (fun i => by rw [← neg_smul]; exact hZ i _)
  have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
    conv_rhs => rw [← hX1]
    show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
    rw [← mul_assoc, hQe, one_mul]
  have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
  calc X = Φ (Ψ X) := hX1.symm
    _ = _ := by
      show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
      rw [hw, NormedSpace.exp_zero, mul_one]

end GlobalTheory.ClosedMonoid
