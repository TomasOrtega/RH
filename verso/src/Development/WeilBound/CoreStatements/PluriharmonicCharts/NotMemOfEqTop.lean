import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtFlagPt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

/- English proof (translation)
Substitute `hJ` using the available equality. Conclude with `Proj.not_mem_mcPts_top z`.
-/
theorem not_mem_of_eq_top {J : Ideal (MRing ι)} (hJ : J = ⊤) (z : (Σ k, ι k) → ℂ) : z ∉ mcPts J := by
  subst hJ
  exact Proj.not_mem_mcPts_top z

/- English proof (translation)
Establish `hg` using `BM.good l b hb`. Establish `hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0` using `fun k h => hg.1 k (mem_mCoordIdeal_of_aeval_eq_zero _ (PositivityTheory.Xgp.W.isMultiHomog_X _) (by simpa using h))`. Establish `horb : SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b)` using `⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), by`. Use function extensionality and compare the values at `p`. Simplify using `[FC.bvec, div_eq_inv_mul]⟩`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb]`. Conclude with `(hg.2.1 q I).1`.
-/
private theorem regAt_u_bvec (l : Fin BM.q) (q : (k : K) × ι k) (I : Finset (Fin N)) (b : BM.Rb.X)
    (hb : b ∈ BM.O l) : RegAt M.x (mCoordIdeal (FC.bvec BM l b)) ((BM.F l).u q I) := by
  have hg := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k h =>
    hg.1 k (mem_mCoordIdeal_of_aeval_eq_zero _ (PositivityTheory.Xgp.W.isMultiHomog_X _) (by simpa using h))
  have horb : SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) :=
    ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), by
      funext p; simp [FC.bvec, div_eq_inv_mul]⟩
  rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb]
  exact (hg.2.1 q I).1

/- English proof (translation)
Take `⟨m, hm⟩` from `FA.Re.R.A.cover (σ x)`. Use `choose p hp using (FA.Re.R.mem (σ x) (σ x) (FA.Re.R.mem_U (σ x))).1`. Establish `hJ : FA.Re.R.lift (σ x) (σ x) ∉ mcPts FA.Re.J` using `not_mem_of_eq_top FA.J_top _`. Establish `hker` using `FA.Re.R.immersion (σ x) hJ p hp m hm`. Establish `hu0 : FA.S.A.chart k x ∈ (FA.S.A.chart k).target` using `(FA.S.A.chart k).map_source hk`.

Establish `hcx : (FA.S.A.chart k).symm (FA.S.A.chart k x) = x` using `(FA.S.A.chart k).left_inv hk`. Use `set φ := (FA.Re.R.A.chart m) ∘ σ ∘ (FA.S.A.chart k).symm with hφ`. Establish `hφd : DifferentiableAt ℂ φ (FA.S.A.chart k x)` using `(hσ.2 k m (FA.S.A.chart k x) ⟨hu0, by simpa [hcx] using hm⟩).differentiableAt`. Establish `hφu0 : φ (FA.S.A.chart k x) = FA.Re.R.A.chart m (σ x)` using `by simp [φ, hcx]`. Use `set F : (Fin (d + 1) → ℂ) → ((k : K) × ι k → ℂ) := fun w => affCoord p (FA.Re.R.lift (σ x) ((FA.Re.R.A.chart m).symm w)) with hF`.

Establish `hFd : DifferentiableAt ℂ F (φ (FA.S.A.chart k x))`. Rewrite using `[hφu0, differentiableAt_pi]`. Introduce `q`. Establish `h1` using `holoOn_at (FA.Re.R.holo (σ x) q) (FA.Re.R.mem_U (σ x)) hm`. Establish `h2` using `holoOn_at (FA.Re.R.holo (σ x) ⟨q.1, p q.1⟩) (FA.Re.R.mem_U (σ x)) hm`.

Simplify using `only [F, affCoord]`. Use `(h1.div h2 ?_).differentiableAt` and prove the remaining obligations. Simplify `hp q.1` using `[(FA.Re.R.A.chart m).left_inv hm]`. Use `set β := (BM.Rb.A.chart kb) ∘ FA.pr ∘ (FA.S.A.chart k).symm with hβdef`. Use `set Λ : (Fin (d + 1) → ℂ) → (Ψ → Fin N → Fin N → ℂ) := fun u τ a b => L τ ((FA.S.A.chart k).symm u) a b with hΛdef`.

Use `set ψ : (Fin (d + 1) → ℂ) → (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) := fun u => (β u, Λ u) with hψdef`. Use `set H : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) → ((k : K) × ι k → ℂ) := fun e => affCoord p (FC.flagPt M (BM.F l) (FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1)) fun τ => h₀ τ * Matrix.of (e.2 τ)) with hH`. Establish `hcont : ContinuousAt (FA.S.A.chart k).symm (FA.S.A.chart k x)` using `(FA.S.A.chart k).continuousAt_symm hu0`. Establish `hev : F ∘ φ =ᶠ[𝓝 (FA.S.A.chart k x)] H ∘ ψ`. Establish `h1 : (FA.S.A.chart k).symm ⁻¹' W ∈ 𝓝 (FA.S.A.chart k x)` using `hcont.preimage_mem_nhds (by rw [hcx]; exact hW.mem_nhds hx)`.

Establish `h2 : (FA.S.A.chart k).symm ⁻¹' (σ ⁻¹' (FA.Re.R.A.chart m).source) ∈ 𝓝 (FA.S.A.chart k x)` using `hcont.preimage_mem_nhds (by`. Rewrite using `[hcx]`. Conclude with `hσ.1.continuousAt.preimage_mem_nhds ((FA.Re.R.A.chart m).open_source.mem_nhds hm))`. Establish `h3 : (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source) ∈ 𝓝 (FA.S.A.chart k x)` using `hcont.preimage_mem_nhds (by`. Rewrite using `[hcx]`.

Conclude with `FA.pr_holo.1.continuousAt.preimage_mem_nhds ((BM.Rb.A.chart kb).open_source.mem_nhds hkb))`. Use `filter_upwards [h1, h2, h3] with u hu1 hu2 hu3`. Simplify using `only [Set.mem_preimage] at hu1 hu2 hu3`. Simplify using `only [Function.comp, F, H, ψ, β, Λ, φ]`. Rewrite using `[(FA.Re.R.A.chart m).left_inv hu2, (BM.Rb.A.chart kb).left_inv hu3]`.

Take `⟨cc, hcc, heq⟩` from `ho _ hu1`. Rewrite using `[heq]`. Use function extensionality and compare the values at `q`. Simplify using `only [affCoord]`. Rewrite using `[mul_div_mul_left _ _ (hcc q.1)]`.

Both sides reduce to the same expression. Establish `hβd : DifferentiableAt ℂ β (FA.S.A.chart k x)` using `(FA.pr_holo.2 k kb (FA.S.A.chart k x) ⟨hu0, by simpa [hcx] using hkb⟩).differentiableAt`. Establish `hLd : ∀ τ a b, DifferentiableAt ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x)` using `fun τ a b => (holoOn_at (hL τ a b) hx hk).differentiableAt`. Establish `hΛ : HasFDerivAt Λ (ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x)) (FA.S.A.chart k x)`. Rewrite using `[hasFDerivAt_pi]`.

Introduce `τ`. Rewrite using `[hasFDerivAt_pi]`. Introduce `a`. Rewrite using `[hasFDerivAt_pi]`. Introduce `b`.

Simplify using `using (hLd τ a b).hasFDerivAt`. Establish `hψ` using `hβd.hasFDerivAt.prodMk hΛ`. Establish `hψv : fderiv ℂ ψ (FA.S.A.chart k x) v = 0`. Rewrite using `[hψ.fderiv]`. Apply the tactic sequence `ext <;> simp [β, hβ, hD]`.

Establish `hψu0 : ψ (FA.S.A.chart k x) = (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b)`. Simplify using `[ψ, β, Λ, hcx]`. Establish `hbv` using `bvec_holo BM (A := BM.Rb.A) (pr := id) ⟨continuous_id, fun j k' => BM.Rb.A.holo j k'⟩ (BM.O_open l) (fun _ h => h)`. Take `⟨cc0, hcc0, heq0⟩` from `ho x hx`. Establish `hHd : DifferentiableAt ℂ H (ψ (FA.S.A.chart k x))`.

Rewrite using `[hψu0]`. Establish `hb : ∀ q, AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1) q) (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b)` using `fun q => by`. Establish `h` using `holoOn_at (hbv.1 q) hl hkb`. Conclude with `AnalyticAt.comp (f := Prod.fst) (g := fun w => FC.bvec BM l ((BM.Rb.A.chart kb).symm w) q) h analyticAt_fst`. Establish `hval : ∀ (q : (k : K) × ι k) (I : Finset (Fin N)), AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => valAt M.x ((BM.F l).u q I) (FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1))) (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b)` using `fun q I => by`.

Establish `h` using `holoOn_at (hbv.2 _ (fun b hb => regAt_u_bvec l q I b hb)) hl hkb`. Conclude with `AnalyticAt.comp (f := Prod.fst) (g := fun w => valAt M.x ((BM.F l).u q I) (FC.bvec BM l ((BM.Rb.A.chart kb).symm w))) h analyticAt_fst`. Establish `hh : ∀ (τ : Ψ) (r s : Fin N), AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => (h₀ τ * Matrix.of (e.2 τ)) r s) (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b)`. Introduce `τ r s`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`.

Establish `hp2 : ∀ t : Fin N, AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => e.2 τ t s) (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b)`. Introduce `t`. Establish `e : (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => e.2 τ t s) = ⇑((ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : Fin N => ℂ) s).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) t).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Ψ => Fin N → Fin N → ℂ) τ).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Ψ → Fin N → Fin N → ℂ))))) := rfl`. Rewrite using `[e]`. Conclude with `ContinuousLinearMap.analyticAt _ _`.

Establish `hs` using `Finset.analyticAt_sum Finset.univ (fun t _ => (analyticAt_const (v := h₀ τ r t)).mul (hp2 t))`. Conclude with `hs.congr (Filter.Eventually.of_forall fun e => by simp)`. Establish `hZ` using `analyticAt_flagPt (BM.F l) hb hval hh`. Rewrite using `[differentiableAt_pi]`. Introduce `q`.

Simplify using `only [H, affCoord]`. Use `((hZ q).div (hZ ⟨q.1, p q.1⟩) ?_).differentiableAt` and prove the remaining obligations. Establish `h1` using `hp q.1`. Rewrite `h1` using `[heq0]`. Establish `h2 : FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x)) (fun τ => h₀ τ * L τ x) ⟨q.1, p q.1⟩ ≠ 0` using `right_ne_zero_of_mul h1`.

Simplify using `only [(BM.Rb.A.chart kb).left_inv hkb]`. Conclude with `h2`. Establish `hψd : DifferentiableAt ℂ ψ (FA.S.A.chart k x)` using `hψ.differentiableAt`. Establish `key : fderiv ℂ F (φ (FA.S.A.chart k x)) (fderiv ℂ φ (FA.S.A.chart k x) v) = 0`. Establish `e1` using `fderiv_comp (FA.S.A.chart k x) hFd hφd`.

Establish `e2` using `fderiv_comp (FA.S.A.chart k x) hHd hψd`. Combine the equalities or inequalities in the displayed calculation. Establish `hz : fderiv ℂ φ (FA.S.A.chart k x) v = 0`. Rewrite `key` using `[hφu0]`. Establish `hinjF` using `LinearMap.ker_eq_bot.mp hker`.

Conclude with `hinjF (by rw [map_zero]; exact key)`. Conclude with `hinj x k m hk hm (by rw [hz, map_zero])`.
-/
theorem eq_zero_of_still (FA : FlagAn BM d) {σ : FA.S.X → FA.Re.R.X} (hσ : HoloMap FA.S.A FA.Re.R.A σ)
    (hinj : ∀ x k m, x ∈ (FA.S.A.chart k).source → σ x ∈ (FA.Re.R.A.chart m).source →
      Function.Injective (fderiv ℂ (FA.Re.R.A.chart m ∘ σ ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)))
    {l : Fin BM.q} {W : Set FA.S.X} (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W) (hl : FA.pr x ∈ BM.O l)
    {h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ} {L : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ}
    (hL : ∀ τ a b, FA.S.A.HoloOn W fun x' => L τ x' a b)
    (ho : ∀ x' ∈ W, SameOrbit (FA.Re.R.lift (σ x) (σ x'))
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => h₀ τ * L τ x'))
    {k : Fin FA.S.A.n} (hk : x ∈ (FA.S.A.chart k).source) {kb : Fin BM.Rb.A.n}
    (hkb : FA.pr x ∈ (BM.Rb.A.chart kb).source) {v : Fin (d + 1) → ℂ}
    (hβ : fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v = 0)
    (hD : ∀ τ a b, fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v = 0) : v = 0 := by
  classical
  obtain ⟨m, hm⟩ := FA.Re.R.A.cover (σ x)
  choose p hp using (FA.Re.R.mem (σ x) (σ x) (FA.Re.R.mem_U (σ x))).1
  have hJ : FA.Re.R.lift (σ x) (σ x) ∉ mcPts FA.Re.J := not_mem_of_eq_top FA.J_top _
  have hker := FA.Re.R.immersion (σ x) hJ p hp m hm
  have hu0 : FA.S.A.chart k x ∈ (FA.S.A.chart k).target := (FA.S.A.chart k).map_source hk
  have hcx : (FA.S.A.chart k).symm (FA.S.A.chart k x) = x := (FA.S.A.chart k).left_inv hk
  set φ := (FA.Re.R.A.chart m) ∘ σ ∘ (FA.S.A.chart k).symm with hφ
  have hφd : DifferentiableAt ℂ φ (FA.S.A.chart k x) :=
    (hσ.2 k m (FA.S.A.chart k x) ⟨hu0, by simpa [hcx] using hm⟩).differentiableAt
  have hφu0 : φ (FA.S.A.chart k x) = FA.Re.R.A.chart m (σ x) := by simp [φ, hcx]
  set F : (Fin (d + 1) → ℂ) → ((k : K) × ι k → ℂ) :=
    fun w => affCoord p (FA.Re.R.lift (σ x) ((FA.Re.R.A.chart m).symm w)) with hF
  have hFd : DifferentiableAt ℂ F (φ (FA.S.A.chart k x)) := by
    rw [hφu0, differentiableAt_pi]
    intro q
    have h1 := holoOn_at (FA.Re.R.holo (σ x) q) (FA.Re.R.mem_U (σ x)) hm
    have h2 := holoOn_at (FA.Re.R.holo (σ x) ⟨q.1, p q.1⟩) (FA.Re.R.mem_U (σ x)) hm
    simp only [F, affCoord]
    refine (h1.div h2 ?_).differentiableAt
    simpa [(FA.Re.R.A.chart m).left_inv hm] using hp q.1
  set β := (BM.Rb.A.chart kb) ∘ FA.pr ∘ (FA.S.A.chart k).symm with hβdef
  set Λ : (Fin (d + 1) → ℂ) → (Ψ → Fin N → Fin N → ℂ) :=
    fun u τ a b => L τ ((FA.S.A.chart k).symm u) a b with hΛdef
  set ψ : (Fin (d + 1) → ℂ) → (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) := fun u => (β u, Λ u) with hψdef
  set H : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) → ((k : K) × ι k → ℂ) := fun e =>
    affCoord p (FC.flagPt M (BM.F l) (FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1))
      fun τ => h₀ τ * Matrix.of (e.2 τ)) with hH
  have hcont : ContinuousAt (FA.S.A.chart k).symm (FA.S.A.chart k x) :=
    (FA.S.A.chart k).continuousAt_symm hu0
  have hev : F ∘ φ =ᶠ[𝓝 (FA.S.A.chart k x)] H ∘ ψ := by
    have h1 : (FA.S.A.chart k).symm ⁻¹' W ∈ 𝓝 (FA.S.A.chart k x) :=
      hcont.preimage_mem_nhds (by rw [hcx]; exact hW.mem_nhds hx)
    have h2 : (FA.S.A.chart k).symm ⁻¹' (σ ⁻¹' (FA.Re.R.A.chart m).source) ∈ 𝓝 (FA.S.A.chart k x) :=
      hcont.preimage_mem_nhds (by
        rw [hcx]; exact hσ.1.continuousAt.preimage_mem_nhds ((FA.Re.R.A.chart m).open_source.mem_nhds hm))
    have h3 : (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source) ∈ 𝓝 (FA.S.A.chart k x) :=
      hcont.preimage_mem_nhds (by
        rw [hcx]
        exact FA.pr_holo.1.continuousAt.preimage_mem_nhds ((BM.Rb.A.chart kb).open_source.mem_nhds hkb))
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    simp only [Set.mem_preimage] at hu1 hu2 hu3
    simp only [Function.comp, F, H, ψ, β, Λ, φ]
    rw [(FA.Re.R.A.chart m).left_inv hu2, (BM.Rb.A.chart kb).left_inv hu3]
    obtain ⟨cc, hcc, heq⟩ := ho _ hu1
    rw [heq]
    funext q
    simp only [affCoord]
    rw [mul_div_mul_left _ _ (hcc q.1)]
    rfl
  have hβd : DifferentiableAt ℂ β (FA.S.A.chart k x) :=
    (FA.pr_holo.2 k kb (FA.S.A.chart k x) ⟨hu0, by simpa [hcx] using hkb⟩).differentiableAt
  have hLd : ∀ τ a b, DifferentiableAt ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b)
      (FA.S.A.chart k x) := fun τ a b =>
    (holoOn_at (hL τ a b) hx hk).differentiableAt
  have hΛ : HasFDerivAt Λ (ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a =>
      ContinuousLinearMap.pi fun b => fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b)
        (FA.S.A.chart k x)) (FA.S.A.chart k x) := by
    rw [hasFDerivAt_pi]
    intro τ
    rw [hasFDerivAt_pi]
    intro a
    rw [hasFDerivAt_pi]
    intro b
    simpa using (hLd τ a b).hasFDerivAt
  have hψ := hβd.hasFDerivAt.prodMk hΛ
  have hψv : fderiv ℂ ψ (FA.S.A.chart k x) v = 0 := by
    rw [hψ.fderiv]
    ext <;> simp [β, hβ, hD]
  have hψu0 : ψ (FA.S.A.chart k x) = (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := by
    simp [ψ, β, Λ, hcx]
  have hbv := bvec_holo BM (A := BM.Rb.A) (pr := id) ⟨continuous_id, fun j k' => BM.Rb.A.holo j k'⟩
    (BM.O_open l) (fun _ h => h)
  obtain ⟨cc0, hcc0, heq0⟩ := ho x hx
  have hHd : DifferentiableAt ℂ H (ψ (FA.S.A.chart k x)) := by
    rw [hψu0]
    have hb : ∀ q, AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) =>
        FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1) q)
        (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := fun q => by
      have h := holoOn_at (hbv.1 q) hl hkb
      exact AnalyticAt.comp (f := Prod.fst)
        (g := fun w => FC.bvec BM l ((BM.Rb.A.chart kb).symm w) q) h analyticAt_fst
    have hval : ∀ (q : (k : K) × ι k) (I : Finset (Fin N)), AnalyticAt ℂ
        (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) =>
          valAt M.x ((BM.F l).u q I) (FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1)))
        (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := fun q I => by
      have h := holoOn_at (hbv.2 _ (fun b hb => regAt_u_bvec l q I b hb)) hl hkb
      exact AnalyticAt.comp (f := Prod.fst)
        (g := fun w => valAt M.x ((BM.F l).u q I) (FC.bvec BM l ((BM.Rb.A.chart kb).symm w))) h analyticAt_fst
    have hh : ∀ (τ : Ψ) (r s : Fin N), AnalyticAt ℂ
        (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => (h₀ τ * Matrix.of (e.2 τ)) r s)
        (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := by
      intro τ r s
      simp only [Matrix.mul_apply, Matrix.of_apply]
      have hp2 : ∀ t : Fin N, AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => e.2 τ t s)
          (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := by
        intro t
        have e : (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => e.2 τ t s) =
            ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) s).comp
              ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) t).comp
                ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Ψ => Fin N → Fin N → ℂ) τ).comp
                  (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Ψ → Fin N → Fin N → ℂ))))) := rfl
        rw [e]
        exact ContinuousLinearMap.analyticAt _ _
      have hs := Finset.analyticAt_sum Finset.univ (fun t _ => (analyticAt_const (v := h₀ τ r t)).mul (hp2 t))
      exact hs.congr (Filter.Eventually.of_forall fun e => by simp)
    have hZ := analyticAt_flagPt (BM.F l) hb hval hh
    rw [differentiableAt_pi]
    intro q
    simp only [H, affCoord]
    refine ((hZ q).div (hZ ⟨q.1, p q.1⟩) ?_).differentiableAt
    have h1 := hp q.1
    rw [heq0] at h1
    have h2 : FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x)) (fun τ => h₀ τ * L τ x) ⟨q.1, p q.1⟩ ≠ 0 :=
      right_ne_zero_of_mul h1
    simp only [(BM.Rb.A.chart kb).left_inv hkb]
    exact h2
  have hψd : DifferentiableAt ℂ ψ (FA.S.A.chart k x) := hψ.differentiableAt
  have key : fderiv ℂ F (φ (FA.S.A.chart k x)) (fderiv ℂ φ (FA.S.A.chart k x) v) = 0 := by
    have e1 := fderiv_comp (FA.S.A.chart k x) hFd hφd
    have e2 := fderiv_comp (FA.S.A.chart k x) hHd hψd
    calc fderiv ℂ F (φ (FA.S.A.chart k x)) (fderiv ℂ φ (FA.S.A.chart k x) v)
        = fderiv ℂ (F ∘ φ) (FA.S.A.chart k x) v := by rw [e1]; rfl
      _ = fderiv ℂ (H ∘ ψ) (FA.S.A.chart k x) v := by rw [hev.fderiv_eq]
      _ = fderiv ℂ H (ψ (FA.S.A.chart k x)) (fderiv ℂ ψ (FA.S.A.chart k x) v) := by rw [e2]; rfl
      _ = 0 := by rw [hψv, map_zero]
  have hz : fderiv ℂ φ (FA.S.A.chart k x) v = 0 := by
    rw [hφu0] at key
    have hinjF := LinearMap.ker_eq_bot.mp hker
    exact hinjF (by rw [map_zero]; exact key)
  exact hinj x k m hk hm (by rw [hz, map_zero])

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)`. Rewrite using `[hB c b (fun h' => hab (h.trans h')), mul_zero]`.

Rewrite using `[hA a c h, zero_mul]`.
-/
private theorem isBlockDiag_mul' {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (hB : IsBlockDiag j B) :
    IsBlockDiag j (A * B) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · rw [hB c b (fun h' => hab (h.trans h')), mul_zero]
  · rw [hA a c h, zero_mul]

/- English proof (translation)
Introduce `k hk v hv`. Take `⟨kb, hkb⟩` from `BM.Rb.A.cover (FA.pr x)`. Establish `hφ0 : (FA.S.A.chart k).symm (FA.S.A.chart k x) = x` using `(FA.S.A.chart k).left_inv hk`. Establish `hu0 : FA.S.A.chart k x ∈ (FA.S.A.chart k).target ∩ (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source)` using `⟨(FA.S.A.chart k).map_source hk, by simp only [Set.mem_preimage, hφ0]; exact hkb⟩`. Establish `hβd : DifferentiableAt ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)` using `(FA.pr_holo.2 k kb _ hu0).differentiableAt`.

Establish `hopen : IsOpen ((FA.S.A.chart k).target ∩ (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source))` using `(FA.S.A.chart k).continuousOn_symm.isOpen_inter_preimage (FA.S.A.chart k).open_target ((BM.Rb.A.chart kb).open_source.preimage FA.pr_holo.1)`. Establish `hchain : ∀ τ a b, fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) = (fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) (BM.Rb.A.chart kb (FA.pr x))).comp (fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)) ∧ Di …`. Introduce `τ a b`. Establish `hG` using `(holoOn_at (hPi.2.1 τ a b) hVb hkb).differentiableAt`. Establish `hG' : DifferentiableAt ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) ((BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x))`.

Simplify `hG` using `only [Function.comp, hφ0]`. Establish `heq : (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) =ᶠ[𝓝 (FA.S.A.chart k x)] (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) ∘ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm)` using `by filter_upwards [hopen.mem_nhds hu0] with u hu`. Simplify using `only [Function.comp, (BM.Rb.A.chart kb).left_inv hu.2]`. Use `⟨?_, (hG'.comp _ hβd).congr_of_eventuallyEq heq⟩` and prove the remaining obligations. Rewrite using `[heq.fderiv_eq, fderiv_comp _ hG' hβd]`.

Simplify using `only [Function.comp, hφ0]`. Establish `hLd : ∀ τ a b, DifferentiableAt ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x)` using `fun τ a b => (holoOn_at (hL τ a b) hx hk).differentiableAt`. Establish `hLconst : ∀ τ (a b : Fin N), (a ≤ b ∨ ¬((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) → fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v = 0`. Introduce `τ a b hab`. Establish `: (fun u => L τ ((FA.S.A.chart k).symm u) a b) = fun _ => if a = b then (1 : ℂ) else 0`.

Use function extensionality and compare the values at `u`. Break down `hab with hab | hab` into its components or cases. Break down `hab.lt_or_eq with h | h` into its components or cases. Rewrite using `[(hLb τ _).2.2 a b h, if_neg h.ne]`. Substitute `h` using the available equality.

Rewrite using `[(hLb τ _).2.1 a, if_pos rfl]`. Establish `hne : a ≠ b` using `by rintro rfl; exact hab Iff.rfl`. Rewrite using `[(hLb τ _).1 a b hab, if_neg hne]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `hprod : ∀ τ, (Matrix.of fun a b => fderiv ℂ (fun u => (Pi τ (FA.pr ((FA.S.A.chart k).symm u)) * (h₀ τ * L τ ((FA.S.A.chart k).symm u))) a b) (FA.S.A.chart k x) v) = (Matrix.of fun a b => fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) v) * (h₀ τ …`. Introduce `τ`. Establish `hQd : ∀ a b, DifferentiableAt ℂ (fun u => (h₀ τ * L τ ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x)`. Introduce `a b`. Simplify using `only [Matrix.mul_apply]`.

Conclude with `DifferentiableAt.fun_sum fun c _ => (differentiableAt_const _).mul (hLd τ c b)`. Rewrite using `[fderiv_mul_of (fun a b => (hchain τ a b).2) hQd v, fderiv_mul_of (P := fun _ => h₀ τ) (fun a b => differentiableAt_const _) (hLd τ) v]`. Establish `h0 : (Matrix.of fun a b => fderiv ℂ (fun _ : Fin (d+1) → ℂ => h₀ τ a b) (FA.S.A.chart k x) v) = 0`. Use extensionality with `a b`. Simplify using the standard rewrite rules.

Rewrite using `[h0, Matrix.zero_mul, zero_add, hφ0]`. Establish `hdet : ∀ τ, IsUnit (Pi τ (FA.pr x)).det` using `fun τ => (hPi.2.2 τ _ hVb).1.1`. Establish `hLdet : ∀ τ (x' : FA.S.X), (L τ x').det = 1`. Introduce `τ x'`. Rewrite using `[Matrix.det_of_lowerTriangular]`.

Simplify using `[(hLb τ x').2.1]`. Introduce `a b hab`. Conclude with `(hLb τ x').2.2 a b hab`. Establish `hHdet : ∀ τ, (h₀ τ * L τ x).det ≠ 0` using `fun τ => by`. Rewrite using `[Matrix.det_mul, hLdet, mul_one]`.

Conclude with `(hh₀ τ).2`. Use `set dP : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b => fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) v with hdP`. Use `set dL : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b => fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v with hdL`. Establish `hdLbd : ∀ τ, IsBlockDiag j (dL τ)` using `fun τ a b hab => hLconst τ a b (Or.inr hab)`. Establish `hkey : ∀ τ, ((h₀ τ * L τ x)⁻¹ * ((Pi τ (FA.pr x))⁻¹ * dP τ * (h₀ τ * L τ x) + h₀ τ * dL τ)).BlockTriangular id`.

Introduce `τ`. Establish `h1` using `hv τ`. Establish `h2 : (Pi τ (FA.pr x) * (h₀ τ * L τ x))⁻¹ * (dP τ * (h₀ τ * L τ x) + Pi τ (FA.pr x) * (h₀ τ * dL τ)) = (h₀ τ * L τ x)⁻¹ * ((Pi τ (FA.pr x))⁻¹ * dP τ * (h₀ τ * L τ x) + h₀ τ * dL τ)`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_add (Pi τ (FA.pr x))⁻¹, ← Matrix.mul_assoc (Pi τ (FA.pr x))⁻¹ (Pi τ (FA.pr x)), Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_mul, ← Matrix.mul_assoc (Pi τ (FA.pr x))⁻¹ (dP τ)]`. Rewrite using `[← h2, ← hprod τ]`.

Conclude with `h1`. Establish `hll : ∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * dP τ) a b = 0` using `fun τ => lower_left_zero (isBlockDiag_mul' (hh₀ τ).1 (hLb τ x).1) (hHdet τ) (isBlockDiag_mul' (hh₀ τ).1 (hdLbd τ)) (hkey τ)`. Establish `hdP' : ∀ τ, dP τ = Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) (BM.Rb.A.chart kb (FA.pr x)) (fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v)`. Introduce `τ`. Use extensionality with `a b`.

Simplify using `only [hdP, Matrix.of_apply, (hchain τ a b).1, ContinuousLinearMap.comp_apply]`. Establish `hβ : fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v = 0` using `himm kb hkb _ fun τ a b ha hb => by rw [← hdP' τ]; exact hll τ a b ha hb`. Establish `hdP0 : ∀ τ, dP τ = 0`. Introduce `τ`. Rewrite using `[hdP' τ, hβ]`.

Use extensionality with `a b`. Simplify using the standard rewrite rules. Establish `hdL0 : ∀ τ, dL τ = 0`. Introduce `τ`. Use `eq_zero_of_lower (hLb τ x).2 (fun a b hab => hLconst τ a b (Or.inl hab)) ?_` and prove the remaining obligations.

Establish `h3` using `hkey τ`. Rewrite `h3` using `[hdP0 τ, Matrix.mul_zero, Matrix.zero_mul, zero_add, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h₀ τ)⁻¹ (h₀ τ), Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hh₀ τ).2), Matrix.one_mul]`. Conclude with `h3`. Conclude with `eq_zero_of_still FA hσ hinj hW hx hl hL ho hk hkb hβ fun τ a b => by`. Use `congrFun (congrFun (hdL0 τ) a) b` as an intermediate fact.

Simplify `this` using `[hdL]`.
-/
theorem flag_immersion (FA : FlagAn BM d) {σ : FA.S.X → FA.Re.R.X} (hσ : HoloMap FA.S.A FA.Re.R.A σ)
    (hinj : ∀ x k m, x ∈ (FA.S.A.chart k).source → σ x ∈ (FA.Re.R.A.chart m).source →
      Function.Injective (fderiv ℂ (FA.Re.R.A.chart m ∘ σ ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)))
    {l : Fin BM.q} {Vb : Set BM.Rb.X} {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ}
    (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) {W : Set FA.S.X} (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W)
    (hl : FA.pr x ∈ BM.O l) (hVb : FA.pr x ∈ Vb)
    {h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ} {L : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ}
    (hh₀ : ∀ τ, IsBlockDiag j (h₀ τ) ∧ (h₀ τ).det ≠ 0)
    (hL : ∀ τ a b, FA.S.A.HoloOn W fun x' => L τ x' a b) (hLb : ∀ τ x', IsBlockDiag j (L τ x') ∧ IsLowerUni (L τ x'))
    (ho : ∀ x' ∈ W, SameOrbit (FA.Re.R.lift (σ x) (σ x'))
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => h₀ τ * L τ x'))
    (himm : ∀ k, FA.pr x ∈ (BM.Rb.A.chart k).source → ∀ v : Fin n → ℂ,
      (∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * Matrix.of fun a b =>
        fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart k).symm w) a b) (BM.Rb.A.chart k (FA.pr x)) v) a b = 0) → v = 0) :
    IsFlagImmersionAt FA.S.A (fun τ x' => Pi τ (FA.pr x') * (h₀ τ * L τ x')) x := by
  intro k hk v hv
  obtain ⟨kb, hkb⟩ := BM.Rb.A.cover (FA.pr x)
  have hφ0 : (FA.S.A.chart k).symm (FA.S.A.chart k x) = x := (FA.S.A.chart k).left_inv hk
  have hu0 : FA.S.A.chart k x ∈ (FA.S.A.chart k).target ∩
      (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source) :=
    ⟨(FA.S.A.chart k).map_source hk, by simp only [Set.mem_preimage, hφ0]; exact hkb⟩
  have hβd : DifferentiableAt ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) :=
    (FA.pr_holo.2 k kb _ hu0).differentiableAt
  have hopen : IsOpen ((FA.S.A.chart k).target ∩
      (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source)) :=
    (FA.S.A.chart k).continuousOn_symm.isOpen_inter_preimage (FA.S.A.chart k).open_target
      ((BM.Rb.A.chart kb).open_source.preimage FA.pr_holo.1)
  have hchain : ∀ τ a b, fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) =
      (fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) (BM.Rb.A.chart kb (FA.pr x))).comp
        (fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)) ∧
      DifferentiableAt ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) := by
    intro τ a b
    have hG := (holoOn_at (hPi.2.1 τ a b) hVb hkb).differentiableAt
    have hG' : DifferentiableAt ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b)
        ((BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)) := by
      simpa only [Function.comp, hφ0] using hG
    have heq : (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) =ᶠ[𝓝 (FA.S.A.chart k x)]
        (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) ∘ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) := by
      filter_upwards [hopen.mem_nhds hu0] with u hu
      simp only [Function.comp, (BM.Rb.A.chart kb).left_inv hu.2]
    refine ⟨?_, (hG'.comp _ hβd).congr_of_eventuallyEq heq⟩
    rw [heq.fderiv_eq, fderiv_comp _ hG' hβd]
    simp only [Function.comp, hφ0]
  have hLd : ∀ τ a b, DifferentiableAt ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) :=
    fun τ a b => (holoOn_at (hL τ a b) hx hk).differentiableAt
  have hLconst : ∀ τ (a b : Fin N), (a ≤ b ∨ ¬((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) →
      fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v = 0 := by
    intro τ a b hab
    have : (fun u => L τ ((FA.S.A.chart k).symm u) a b) = fun _ => if a = b then (1 : ℂ) else 0 := by
      funext u
      rcases hab with hab | hab
      · rcases hab.lt_or_eq with h | h
        · rw [(hLb τ _).2.2 a b h, if_neg h.ne]
        · subst h; rw [(hLb τ _).2.1 a, if_pos rfl]
      · have hne : a ≠ b := by rintro rfl; exact hab Iff.rfl
        rw [(hLb τ _).1 a b hab, if_neg hne]
    rw [this]; simp
  have hprod : ∀ τ, (Matrix.of fun a b => fderiv ℂ (fun u => (Pi τ (FA.pr ((FA.S.A.chart k).symm u)) *
      (h₀ τ * L τ ((FA.S.A.chart k).symm u))) a b) (FA.S.A.chart k x) v) =
      (Matrix.of fun a b => fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) v) *
        (h₀ τ * L τ x) +
      Pi τ (FA.pr x) * (h₀ τ * Matrix.of fun a b => fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b)
        (FA.S.A.chart k x) v) := by
    intro τ
    have hQd : ∀ a b, DifferentiableAt ℂ (fun u => (h₀ τ * L τ ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) := by
      intro a b
      simp only [Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun c _ => (differentiableAt_const _).mul (hLd τ c b)
    rw [fderiv_mul_of (fun a b => (hchain τ a b).2) hQd v,
      fderiv_mul_of (P := fun _ => h₀ τ) (fun a b => differentiableAt_const _) (hLd τ) v]
    have h0 : (Matrix.of fun a b => fderiv ℂ (fun _ : Fin (d+1) → ℂ => h₀ τ a b) (FA.S.A.chart k x) v) = 0 := by
      ext a b; simp
    rw [h0, Matrix.zero_mul, zero_add, hφ0]
  have hdet : ∀ τ, IsUnit (Pi τ (FA.pr x)).det := fun τ => (hPi.2.2 τ _ hVb).1.1
  have hLdet : ∀ τ (x' : FA.S.X), (L τ x').det = 1 := by
    intro τ x'
    rw [Matrix.det_of_lowerTriangular]
    · simp [(hLb τ x').2.1]
    · intro a b hab; exact (hLb τ x').2.2 a b hab
  have hHdet : ∀ τ, (h₀ τ * L τ x).det ≠ 0 := fun τ => by
    rw [Matrix.det_mul, hLdet, mul_one]; exact (hh₀ τ).2
  set dP : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b =>
    fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) v with hdP
  set dL : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b =>
    fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v with hdL
  have hdLbd : ∀ τ, IsBlockDiag j (dL τ) := fun τ a b hab => hLconst τ a b (Or.inr hab)
  have hkey : ∀ τ, ((h₀ τ * L τ x)⁻¹ * ((Pi τ (FA.pr x))⁻¹ * dP τ * (h₀ τ * L τ x) + h₀ τ * dL τ)).BlockTriangular id := by
    intro τ
    have h1 := hv τ
    have h2 : (Pi τ (FA.pr x) * (h₀ τ * L τ x))⁻¹ * (dP τ * (h₀ τ * L τ x) + Pi τ (FA.pr x) * (h₀ τ * dL τ)) =
        (h₀ τ * L τ x)⁻¹ * ((Pi τ (FA.pr x))⁻¹ * dP τ * (h₀ τ * L τ x) + h₀ τ * dL τ) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_add (Pi τ (FA.pr x))⁻¹,
        ← Matrix.mul_assoc (Pi τ (FA.pr x))⁻¹ (Pi τ (FA.pr x)), Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_mul,
        ← Matrix.mul_assoc (Pi τ (FA.pr x))⁻¹ (dP τ)]
    rw [← h2, ← hprod τ]
    exact h1
  have hll : ∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * dP τ) a b = 0 :=
    fun τ => lower_left_zero (isBlockDiag_mul' (hh₀ τ).1 (hLb τ x).1) (hHdet τ) (isBlockDiag_mul' (hh₀ τ).1 (hdLbd τ)) (hkey τ)
  have hdP' : ∀ τ, dP τ = Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b)
      (BM.Rb.A.chart kb (FA.pr x)) (fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v) := by
    intro τ; ext a b
    simp only [hdP, Matrix.of_apply, (hchain τ a b).1, ContinuousLinearMap.comp_apply]
  have hβ : fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v = 0 :=
    himm kb hkb _ fun τ a b ha hb => by rw [← hdP' τ]; exact hll τ a b ha hb
  have hdP0 : ∀ τ, dP τ = 0 := by
    intro τ; rw [hdP' τ, hβ]; ext a b; simp
  have hdL0 : ∀ τ, dL τ = 0 := by
    intro τ
    refine eq_zero_of_lower (hLb τ x).2 (fun a b hab => hLconst τ a b (Or.inl hab)) ?_
    have h3 := hkey τ
    rw [hdP0 τ, Matrix.mul_zero, Matrix.zero_mul, zero_add, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (h₀ τ)⁻¹ (h₀ τ), Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hh₀ τ).2),
      Matrix.one_mul] at h3
    exact h3
  exact eq_zero_of_still FA hσ hinj hW hx hl hL ho hk hkb hβ fun τ a b => by
    have := congrFun (congrFun (hdL0 τ) a) b
    simpa [hdL] using this

end PositivityTheory.Xgp.c_unif
