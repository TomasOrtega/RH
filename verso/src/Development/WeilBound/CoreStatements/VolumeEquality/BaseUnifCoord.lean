import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefsB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.TangentOrigin

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem spMap_fst_comp {R : Type} [CommRing R] (φ : R →+* DualNumber ℂ) :
    spMap fstC ≫ spMap φ = spMap (fstC.comp φ) := (Spec.map_comp _ _).symm

/- English proof (translation)
Rewrite using `[← evalPt_spMap φ]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem evalPt_top {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (r : Γ(Sp R, ⊤)) :
    evalPt (spMap φ) ⊤ le_rfl r = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  rw [← evalPt_spMap φ]
  congr 1
  simp

/- English proof (translation)
Rewrite using `[top_le_preimage_iff, spMap_fst_comp, GlobalTheory.top_le_preimage_basicOpen_iff _ ⊤ r, valAt'_eq_evalPt _ _ le_rfl, evalPt_top]`. Both sides reduce to the same expression.
-/
theorem mem_basicOpen_iff {R : Type} [CommRing R] (φ : R →+* DualNumber ℂ) (r : Γ(Sp R, ⊤)) :
    ⊤ ≤ spMap φ ⁻¹ᵁ (Sp R).basicOpen r ↔ (φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)).fst ≠ 0 := by
  rw [top_le_preimage_iff, spMap_fst_comp, GlobalTheory.top_le_preimage_basicOpen_iff _ ⊤ r,
    valAt'_eq_evalPt _ _ le_rfl, evalPt_top]
  rfl

/- English proof (translation)
Set `p₀ : Sp R` to `(spMap fstC ≫ spMap φ₀) (default : PrimeSpectrum ℂ)`. Establish `hmem : p₀ ∈ v ⁻¹ᵁ U`. Establish `h1 : ⊤ ≤ spMap φ₀ ⁻¹ᵁ (v ⁻¹ᵁ U)` using `by rwa [Scheme.Hom.comp_preimage] at h₀`. Conclude with `(GlobalTheory.top_le_preimage_iff_mem _ _).1 ((top_le_preimage_iff _ _).1 h1)`. Take `⟨r, hrU, hr0⟩` from `(isAffineOpen_top (Sp R)).exists_basicOpen_le (V := v ⁻¹ᵁ U) ⟨p₀, hmem⟩ trivial`.

Take `⟨⟨hh, s⟩, hk⟩` from `IsLocalization.surj (Submonoid.powers r) ((v.appLE U _ hrU).hom f)`. Take `⟨k, hks⟩` from `s.2`. Simplify using `only at hk hks`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hh, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, k, ?_, fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_basicOpen_iff, top_le_preimage_iff]`.

Conclude with `(GlobalTheory.top_le_preimage_iff_mem _ _).2 hr0`. Establish `hD` using `(mem_basicOpen_iff φ r).2 hφ`. Establish `hU : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U`. Rewrite using `[Scheme.Hom.comp_preimage]`. Conclude with `hD.trans (Scheme.Hom.preimage_mono _ hrU)`.

Use `⟨hU, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (evalPt (spMap φ) _ hD) hk`. Establish `e2 : ∀ x : Γ(Sp R, ⊤), evalPt (spMap φ) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen r) x) = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)` using `fun x => (evalPt_res (spMap φ) le_top le_rfl hD x).trans (evalPt_top φ x)`. Rewrite `e` using `[map_mul, e2, e2, ← hks, map_pow, map_pow]`. Rewrite using `[← e]`.

Use `congr 1`.
-/
theorem exists_frac {Z : Scheme.{0}} {R : Type} [CommRing R] (v : Sp R ⟶ Z) (U : Z.Opens) (f : Γ(Z, U))
    (φ₀ : R →+* DualNumber ℂ) (h₀ : ⊤ ≤ (spMap φ₀ ≫ v) ⁻¹ᵁ U) :
    ∃ (a r : R) (k : ℕ), (φ₀ r).fst ≠ 0 ∧ ∀ φ : R →+* DualNumber ℂ, (φ r).fst ≠ 0 →
      ∃ h : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U, evalPt (spMap φ ≫ v) U h f * φ r ^ k = φ a := by
  let p₀ : Sp R := (spMap fstC ≫ spMap φ₀) (default : PrimeSpectrum ℂ)
  have hmem : p₀ ∈ v ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ spMap φ₀ ⁻¹ᵁ (v ⁻¹ᵁ U) := by rwa [Scheme.Hom.comp_preimage] at h₀
    exact (GlobalTheory.top_le_preimage_iff_mem _ _).1 ((top_le_preimage_iff _ _).1 h1)
  obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := v ⁻¹ᵁ U) ⟨p₀, hmem⟩ trivial
  obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) ((v.appLE U _ hrU).hom f)
  obtain ⟨k, hks⟩ := s.2
  dsimp only at hk hks
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hh, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, k, ?_,
    fun φ hφ => ?_⟩
  · rw [← mem_basicOpen_iff, top_le_preimage_iff]
    exact (GlobalTheory.top_le_preimage_iff_mem _ _).2 hr0
  · have hD := (mem_basicOpen_iff φ r).2 hφ
    have hU : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U := by
      rw [Scheme.Hom.comp_preimage]
      exact hD.trans (Scheme.Hom.preimage_mono _ hrU)
    refine ⟨hU, ?_⟩
    have e := congrArg (evalPt (spMap φ) _ hD) hk
    have e2 : ∀ x : Γ(Sp R, ⊤), evalPt (spMap φ) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen r) x) =
        φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
      (evalPt_res (spMap φ) le_top le_rfl hD x).trans (evalPt_top φ x)
    rw [map_mul, e2, e2, ← hks, map_pow, map_pow] at e
    rw [← e]
    congr 1

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)`.
-/
theorem analyticAt_det {n g : ℕ} {M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {t₀ : Fin n → ℂ}
    (h : ∀ a b, AnalyticAt ℂ (fun t => M t a b) t₀) : AnalyticAt ℂ (fun t => (M t).det) t₀ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

/- English proof (translation)
Set `S : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ)` to `{μ | ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ), (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ = μ}`. Establish `hS : Submodule.span ℂ S = ⊤` using `Submodule.span_eq_top_of_ne_zero fun z hz => by`. Take `⟨Λ, r, h1, h2, h3, h4⟩` from `h z hz`. Conclude with `⟨Λ t₀, ⟨Λ, r, h1, h2, h3, rfl⟩, h4⟩`. Establish `hall : ∀ μ, μ ∈ S` using `fun μ => by`.

Establish `hμ : μ ∈ Submodule.span ℂ S` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hμ using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨fun _ => 0, fun _ => 0, fun _ => analyticAt_const, analyticAt_const, by simp, rfl⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨Λ, r, h1, h2, h3, rfl⟩` from `hx`. Take `⟨Λ', r', h1', h2', h3', rfl⟩` from `hy`. Use `⟨fun t => Λ t + Λ' t, fun t => r t + r' t, fun u => (h1 u).add (h1' u), h2.add h2', ?_, rfl⟩` and prove the remaining obligations. Use `filter_upwards [h3, h3'] with t a b`. Rewrite using `[LinearMap.add_apply, a, b]`.

Consider the case `smul c x _ hx`. Take `⟨Λ, r, h1, h2, h3, rfl⟩` from `hx`. Use `⟨fun t => c • Λ t, fun t => c * r t, fun u => analyticAt_const.mul (h1 u), analyticAt_const.mul h2, ?_, rfl⟩` and prove the remaining obligations. Use `filter_upwards [h3] with t a`. Rewrite using `[LinearMap.smul_apply, a, smul_eq_mul]`.

Use `choose Λ r h1 h2 h3 h4 using fun k : Fin g => hall (LinearMap.proj k)`. Set `M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun t => Matrix.of fun k l => Λ k t (Pi.single l 1)`. Establish `hM : ∀ t x k, (M t *ᵥ x) k = Λ k t x` using `fun t x k => by`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ (Λ k t) x]`. Use `show ∑ l, M t k l * x l = _`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `e : (fun j => if l = j then (1 : ℂ) else 0) = Pi.single l 1`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[e, smul_eq_mul, mul_comm]`.

Both sides reduce to the same expression. Establish `hM0 : M t₀ = 1`. Use extensionality with `k l`. Simplify using `[M, h4, Pi.single_apply, Matrix.one_apply]`. Establish `hd : AnalyticAt ℂ (fun t => (M t).det) t₀` using `analyticAt_det fun a b => h1 a _`.

Establish `hd0 : (M t₀).det ≠ 0` using `by rw [hM0]; simp`. Use `analyticAt_pi_iff.2 fun k => ?_` and prove the remaining obligations. Establish `hc : AnalyticAt ℂ (fun t => ((M t).updateCol k fun i => r i t).det) t₀` using `analyticAt_det fun a b => by`. Distinguish the cases in `hb : b = k`. Substitute `hb` using the available equality.

Simplify using `using h2 a`. Simplify using `only [Matrix.updateCol_ne hb]`. Conclude with `h1 a (Pi.single b 1)`. Use `(hc.div hd hd0).congr ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_all.2 h3, hd.continuousAt.eventually_ne hd0] with t ht hne`.

Establish `e1 : (fun i => r i t) = M t *ᵥ w t` using `funext fun i => by rw [hM, ht]`. Establish `e2 : (M t).cramer (M t *ᵥ w t) = (M t).det • w t`. Rewrite using `[Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `e3` using `congrFun e2 k`. Rewrite `e3` using `[Matrix.cramer_apply]`.

Use `show ((M t).updateCol k fun i => r i t).det / (M t).det = w t k`. Rewrite using `[e1, e3, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hne]`.
-/
theorem analyticAt_of_forms {n g : ℕ} (w : (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ)
    (h : ∀ z : Fin g → ℂ, z ≠ 0 → ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ),
      (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ z ≠ 0) :
    AnalyticAt ℂ w t₀ := by
  classical
  let S : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ) := {μ | ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ),
      (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ = μ}
  have hS : Submodule.span ℂ S = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    obtain ⟨Λ, r, h1, h2, h3, h4⟩ := h z hz
    exact ⟨Λ t₀, ⟨Λ, r, h1, h2, h3, rfl⟩, h4⟩
  have hall : ∀ μ, μ ∈ S := fun μ => by
    have hμ : μ ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
    induction hμ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨fun _ => 0, fun _ => 0, fun _ => analyticAt_const, analyticAt_const, by simp, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨Λ, r, h1, h2, h3, rfl⟩ := hx
      obtain ⟨Λ', r', h1', h2', h3', rfl⟩ := hy
      refine ⟨fun t => Λ t + Λ' t, fun t => r t + r' t, fun u => (h1 u).add (h1' u), h2.add h2', ?_, rfl⟩
      filter_upwards [h3, h3'] with t a b
      rw [LinearMap.add_apply, a, b]
    | smul c x _ hx =>
      obtain ⟨Λ, r, h1, h2, h3, rfl⟩ := hx
      refine ⟨fun t => c • Λ t, fun t => c * r t, fun u => analyticAt_const.mul (h1 u), analyticAt_const.mul h2, ?_, rfl⟩
      filter_upwards [h3] with t a
      rw [LinearMap.smul_apply, a, smul_eq_mul]
  choose Λ r h1 h2 h3 h4 using fun k : Fin g => hall (LinearMap.proj k)
  let M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => Matrix.of fun k l => Λ k t (Pi.single l 1)
  have hM : ∀ t x k, (M t *ᵥ x) k = Λ k t x := fun t x k => by
    rw [LinearMap.pi_apply_eq_sum_univ (Λ k t) x]
    show ∑ l, M t k l * x l = _
    refine Finset.sum_congr rfl fun l _ => ?_
    have e : (fun j => if l = j then (1 : ℂ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [e, smul_eq_mul, mul_comm]
    rfl
  have hM0 : M t₀ = 1 := by
    ext k l
    simp [M, h4, Pi.single_apply, Matrix.one_apply]
  have hd : AnalyticAt ℂ (fun t => (M t).det) t₀ := analyticAt_det fun a b => h1 a _
  have hd0 : (M t₀).det ≠ 0 := by rw [hM0]; simp
  refine analyticAt_pi_iff.2 fun k => ?_
  have hc : AnalyticAt ℂ (fun t => ((M t).updateCol k fun i => r i t).det) t₀ := analyticAt_det fun a b => by
    by_cases hb : b = k
    · subst hb
      simpa using h2 a
    · simp only [Matrix.updateCol_ne hb]
      exact h1 a (Pi.single b 1)
  refine (hc.div hd hd0).congr ?_
  filter_upwards [Filter.eventually_all.2 h3, hd.continuousAt.eventually_ne hd0] with t ht hne
  have e1 : (fun i => r i t) = M t *ᵥ w t := funext fun i => by rw [hM, ht]
  have e2 : (M t).cramer (M t *ᵥ w t) = (M t).det • w t := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have e3 := congrFun e2 k
  rw [Matrix.cramer_apply] at e3
  show ((M t).updateCol k fun i => r i t).det / (M t).det = w t k
  rw [e1, e3, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hne]

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem snd_of_mul_eq {x ρ α : DualNumber ℂ} (h : x * ρ = α) (hρ : ρ.fst ≠ 0) :
    x.snd = (α.snd * ρ.fst - α.fst * ρ.snd) / ρ.fst ^ 2 := by
  subst h
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  field_simp
  ring

/- English proof (translation)
Introduce `Z n g B e A _ v ψ w hB hol hψ hder huniq t₀ ht₀`. Use `analyticAt_of_forms w t₀ fun z hz => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨U, h₀, f, hf⟩ : ∃ (U : Z.Opens) (_ : ⊤ ≤ (spMap (dualMap (ψ t₀)) ≫ v) ⁻¹ᵁ U) (f : Γ(Z, U)), fderiv ℂ (fun z => valAt' (e t₀ z) U f) 0 z ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`.

Establish `h' : IsDerivAt0 (e t₀) (w t₀ + z) (spMap (dualMap (ψ t₀)) ≫ v)` using `⟨(hder t₀ ht₀).1, fun U h f => by rw [map_add, hn U h f, add_zero]; exact (hder t₀ ht₀).2 U h f⟩`. Use `huniq t₀ ht₀ _ _ _ h' (hder t₀ ht₀)` as an intermediate fact. Conclude with `hz (by simpa using this)`. Establish `h00 : ⊤ ≤ e t₀ 0 ⁻¹ᵁ U` using `(GlobalTheory.FibreDeriv.top_le_preimage_eps _ _ (hder t₀ ht₀).1 U).1 h₀`. Set `G : (Fin n → ℂ) × (Fin g → ℂ) → ℂ` to `fun bz => valAt' (e bz.1 bz.2) U f`.

Establish `hG : AnalyticAt ℂ G (t₀, 0)` using `GlobalTheory.SCV.analyticAt_of_differentiableOn (hol U f).2 ((hol U f).1.mem_nhds ⟨⟨ht₀, trivial⟩, h00⟩)`. Establish `hι : AnalyticAt ℂ (fun t : Fin n → ℂ => ((t, 0) : (Fin n → ℂ) × (Fin g → ℂ))) t₀` using `analyticAt_id.prod analyticAt_const`. Establish `hslice : ∀ t, DifferentiableAt ℂ G (t, 0) → ∀ u, fderiv ℂ (fun z => valAt' (e t z) U f) 0 u = fderiv ℂ G (t, 0) (0, u)` using `fun t ht u => by`. Establish `h1 : HasFDerivAt (fun z : Fin g → ℂ => ((t, z) : (Fin n → ℂ) × (Fin g → ℂ))) (ContinuousLinearMap.inr ℂ _ _) 0` using `hasFDerivAt_prodMk_right t 0`. Establish `h2` using `ht.hasFDerivAt.comp (0 : Fin g → ℂ) h1`.

Establish `h3` using `h2.fderiv`. Conclude with `congrArg (fun T => T u) h3`. Take `⟨a, r, k, hr0, hfr⟩` from `exists_frac v U f (dualMap (ψ t₀)) h₀`. Establish `hψa : ∀ x, AnalyticAt ℂ (fun t => ψ t x) t₀` using `fun x => GlobalTheory.SCV.analyticAt_of_differentiableOn (hψ x) (hB.mem_nhds ht₀)`. Establish `hfst : ∀ t (x : DualNumber A), (dualMap (ψ t) x).fst = ψ t x.fst` using `fun t x => by simp [dualMap]`.

Establish `hsnd : ∀ t (x : DualNumber A), (dualMap (ψ t) x).snd = ψ t x.snd` using `fun t x => by simp [dualMap]`. Establish `hpow : ∀ t, ψ t r.fst ≠ 0 → ψ t (r ^ k).fst ≠ 0` using `fun t ht => by`. Rewrite using `[TrivSqZeroExt.fst_pow, map_pow]`. Conclude with `pow_ne_zero _ ht`. Rewrite `hr0` using `[hfst]`.

Use `⟨fun t => (fderiv ℂ G (t, 0)).toLinearMap.comp (LinearMap.inr ℂ _ _), fun t => (ψ t a.snd * ψ t (r ^ k).fst - ψ t a.fst * ψ t (r ^ k).snd) / ψ t (r ^ k).fst ^ 2, fun u => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (fun t : Fin n → ℂ => fderiv ℂ G (t, 0)) t₀` using `hG.fderiv.comp_of_eq hι rfl`. Conclude with `((ContinuousLinearMap.apply ℂ ℂ ((0, u) : (Fin n → ℂ) × (Fin g → ℂ))).analyticAt _).comp h1`. Conclude with `(((hψa _).mul (hψa _)).sub ((hψa _).mul (hψa _))).div ((hψa _).pow 2) (pow_ne_zero _ (hpow _ hr0))`. Use `filter_upwards [hB.mem_nhds ht₀, (hψa r.fst).continuousAt.eventually_ne hr0, hι.continuousAt.eventually hG.eventually_analyticAt] with t ht hne hGt`.

Take `⟨hU, he⟩` from `hfr (dualMap (ψ t)) (by rwa [hfst])`. Rewrite `he` using `[← map_pow]`. Establish `h1` using `snd_of_mul_eq he (by rw [hfst]; exact hpow t hne)`. Rewrite `h1` using `[hfst, hfst, hsnd, hsnd]`. Rewrite using `[← h1]`.

Conclude with `(hslice t hGt.differentiableAt (w t)).symm.trans ((hder t ht).2 U hU f).symm`. Conclude with `fun h => hf ((hslice t₀ hG.differentiableAt z).trans h)`.
-/
theorem holCoord : HolCoord := by
  intro Z n g B e A _ v ψ w hB hol hψ hder huniq t₀ ht₀
  refine analyticAt_of_forms w t₀ fun z hz => ?_

  obtain ⟨U, h₀, f, hf⟩ : ∃ (U : Z.Opens) (_ : ⊤ ≤ (spMap (dualMap (ψ t₀)) ≫ v) ⁻¹ᵁ U) (f : Γ(Z, U)),
      fderiv ℂ (fun z => valAt' (e t₀ z) U f) 0 z ≠ 0 := by
    by_contra hn
    push Not at hn
    have h' : IsDerivAt0 (e t₀) (w t₀ + z) (spMap (dualMap (ψ t₀)) ≫ v) :=
      ⟨(hder t₀ ht₀).1, fun U h f => by rw [map_add, hn U h f, add_zero]; exact (hder t₀ ht₀).2 U h f⟩
    have := huniq t₀ ht₀ _ _ _ h' (hder t₀ ht₀)
    exact hz (by simpa using this)
  have h00 : ⊤ ≤ e t₀ 0 ⁻¹ᵁ U := (GlobalTheory.FibreDeriv.top_le_preimage_eps _ _ (hder t₀ ht₀).1 U).1 h₀
  let G : (Fin n → ℂ) × (Fin g → ℂ) → ℂ := fun bz => valAt' (e bz.1 bz.2) U f
  have hG : AnalyticAt ℂ G (t₀, 0) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (hol U f).2 ((hol U f).1.mem_nhds ⟨⟨ht₀, trivial⟩, h00⟩)
  have hι : AnalyticAt ℂ (fun t : Fin n → ℂ => ((t, 0) : (Fin n → ℂ) × (Fin g → ℂ))) t₀ :=
    analyticAt_id.prod analyticAt_const
  have hslice : ∀ t, DifferentiableAt ℂ G (t, 0) → ∀ u,
      fderiv ℂ (fun z => valAt' (e t z) U f) 0 u = fderiv ℂ G (t, 0) (0, u) := fun t ht u => by
    have h1 : HasFDerivAt (fun z : Fin g → ℂ => ((t, z) : (Fin n → ℂ) × (Fin g → ℂ)))
        (ContinuousLinearMap.inr ℂ _ _) 0 := hasFDerivAt_prodMk_right t 0
    have h2 := ht.hasFDerivAt.comp (0 : Fin g → ℂ) h1
    have h3 := h2.fderiv
    exact congrArg (fun T => T u) h3
  obtain ⟨a, r, k, hr0, hfr⟩ := exists_frac v U f (dualMap (ψ t₀)) h₀
  have hψa : ∀ x, AnalyticAt ℂ (fun t => ψ t x) t₀ := fun x =>
    GlobalTheory.SCV.analyticAt_of_differentiableOn (hψ x) (hB.mem_nhds ht₀)
  have hfst : ∀ t (x : DualNumber A), (dualMap (ψ t) x).fst = ψ t x.fst := fun t x => by simp [dualMap]
  have hsnd : ∀ t (x : DualNumber A), (dualMap (ψ t) x).snd = ψ t x.snd := fun t x => by simp [dualMap]
  have hpow : ∀ t, ψ t r.fst ≠ 0 → ψ t (r ^ k).fst ≠ 0 := fun t ht => by
    rw [TrivSqZeroExt.fst_pow, map_pow]
    exact pow_ne_zero _ ht
  rw [hfst] at hr0
  refine ⟨fun t => (fderiv ℂ G (t, 0)).toLinearMap.comp (LinearMap.inr ℂ _ _),
    fun t => (ψ t a.snd * ψ t (r ^ k).fst - ψ t a.fst * ψ t (r ^ k).snd) / ψ t (r ^ k).fst ^ 2, fun u => ?_, ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun t : Fin n → ℂ => fderiv ℂ G (t, 0)) t₀ := hG.fderiv.comp_of_eq hι rfl
    exact ((ContinuousLinearMap.apply ℂ ℂ ((0, u) : (Fin n → ℂ) × (Fin g → ℂ))).analyticAt _).comp h1
  · exact (((hψa _).mul (hψa _)).sub ((hψa _).mul (hψa _))).div ((hψa _).pow 2) (pow_ne_zero _ (hpow _ hr0))
  · filter_upwards [hB.mem_nhds ht₀, (hψa r.fst).continuousAt.eventually_ne hr0,
      hι.continuousAt.eventually hG.eventually_analyticAt] with t ht hne hGt
    obtain ⟨hU, he⟩ := hfr (dualMap (ψ t)) (by rwa [hfst])
    rw [← map_pow] at he
    have h1 := snd_of_mul_eq he (by rw [hfst]; exact hpow t hne)
    rw [hfst, hfst, hsnd, hsnd] at h1
    rw [← h1]
    exact (hslice t hGt.differentiableAt (w t)).symm.trans ((hder t ht).2 U hU f).symm
  · exact fun h => hf ((hslice t₀ hG.differentiableAt z).trans h)

end SheetDecomposition
