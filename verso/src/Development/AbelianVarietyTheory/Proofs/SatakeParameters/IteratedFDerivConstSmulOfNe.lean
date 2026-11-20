import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLatticesStatement

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwU.LawAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {σ R : Type} [Fintype σ] [CommRing R]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by rw [map_sum] exact Finset.sum_eq_zero fun y _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]`.
-/
theorem hasSubst_linMat (B : σ → σ → R) :
    MvPowerSeries.HasSubst (fun x : σ => ∑ y, MvPowerSeries.C (B x y) * MvPowerSeries.X y) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun y _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_C, MvPowerSeries.subst_X ha]`.
-/
theorem subst_linMat {τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (c : σ → R) :
    MvPowerSeries.subst a (∑ y, MvPowerSeries.C (c y) * MvPowerSeries.X y : MvPowerSeries σ R) =
      ∑ y, MvPowerSeries.C (c y) * a y := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_C, MvPowerSeries.subst_X ha]

/- English proof (translation)
Unfold `linSub`. Rewrite using `[MvPowerSeries.subst_mul (hasSubst_linMat B), MvPowerSeries.subst_C]`.
-/
theorem linSub_C_mul' (B : σ → σ → R) (a : R) (f : MvPowerSeries σ R) :
    linSub B (MvPowerSeries.C a * f) = MvPowerSeries.C a * linSub B f := by
  unfold linSub
  rw [MvPowerSeries.subst_mul (hasSubst_linMat B), MvPowerSeries.subst_C]

/- English proof (translation)
Unfold `linSub`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_linMat V) (hasSubst_linMat U)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[subst_linMat (hasSubst_linMat U)]`.

Simplify using `only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linSub_linSub' (U V : σ → σ → R) (f : MvPowerSeries σ R) :
    linSub U (linSub V f) = linSub (fun x y => ∑ z, V x z * U z y) f := by
  unfold linSub
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_linMat V) (hasSubst_linMat U)]
  congr 1
  funext x
  rw [subst_linMat (hasSubst_linMat U)]
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  ring

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_C_mul, Formalism.L2.KerInert.Loc.resV_coeff, Formalism.L2.KerInert.Loc.resV_coeff, MvPowerSeries.coeff_C_mul]`.
-/
theorem resV_C_mul' {ι κ : Type} (f : κ → ι) (a : R) (g : MvPowerSeries ι R) :
    resV f (MvPowerSeries.C a * g) = MvPowerSeries.C a * resV f g := by
  ext n
  rw [MvPowerSeries.coeff_C_mul, Formalism.L2.KerInert.Loc.resV_coeff, Formalism.L2.KerInert.Loc.resV_coeff, MvPowerSeries.coeff_C_mul]

end Lin

/- English proof (translation)
Establish `hr : MvPowerSeries.HasSubst (Formalism.L2.KerInert.Loc.resFam (R` using `R) e) := Formalism.L2.KerInert.Loc.hasSubst_resFam e`. Establish `hB` using `hasSubst_linMat B`. Establish `hBe` using `hasSubst_linMat (fun x y => B (e x) (e y))`. Unfold `linSub`. Rewrite using `[Formalism.L2.KerInert.Loc.resV_eq_subst he.1, Formalism.L2.KerInert.Loc.resV_eq_subst he.1, MvPowerSeries.subst_comp_subst_apply hB hr, MvPowerSeries.subst_comp_subst_apply hr hBe]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Take `⟨k, rfl⟩` from `he.2 i`. Rewrite using `[subst_linMat hr, Formalism.L2.KerInert.Loc.resFam_apply he.1, MvPowerSeries.subst_X hBe]`. Rewrite using `[← Equiv.sum_comp (Equiv.ofBijective e he)]`.

Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.ofBijective_apply]`. Rewrite using `[Formalism.L2.KerInert.Loc.resFam_apply he.1]`.
-/
theorem resV_linSub {κ ι R : Type} [Fintype κ] [Fintype ι] [CommRing R] (e : κ → ι) (he : Function.Bijective e)
    (B : ι → ι → R) (g : MvPowerSeries ι R) : resV e (linSub B g) = linSub (fun x y => B (e x) (e y)) (resV e g) := by
  classical
  have hr : MvPowerSeries.HasSubst (Formalism.L2.KerInert.Loc.resFam (R := R) e) := Formalism.L2.KerInert.Loc.hasSubst_resFam e
  have hB := hasSubst_linMat B
  have hBe := hasSubst_linMat (fun x y => B (e x) (e y))
  unfold linSub
  rw [Formalism.L2.KerInert.Loc.resV_eq_subst he.1, Formalism.L2.KerInert.Loc.resV_eq_subst he.1,
    MvPowerSeries.subst_comp_subst_apply hB hr, MvPowerSeries.subst_comp_subst_apply hr hBe]
  congr 1
  funext i
  obtain ⟨k, rfl⟩ := he.2 i
  rw [subst_linMat hr, Formalism.L2.KerInert.Loc.resFam_apply he.1, MvPowerSeries.subst_X hBe]
  rw [← Equiv.sum_comp (Equiv.ofBijective e he)]
  refine Finset.sum_congr rfl fun k' _ => ?_
  simp only [Equiv.ofBijective_apply]
  rw [Formalism.L2.KerInert.Loc.resFam_apply he.1]

section Cst

/- English proof (translation)
Set `_ : Invertible c` to `invertibleOfNonzero hc`. Proceed by induction on `n with`. Consider the case `zero`. Use extensionality with `x m`. Simplify using `[iteratedFDeriv_zero_apply]`.

Consider the case `succ n ih`. Rewrite using `[iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Rewrite using `[fderiv_const_smul_of_invertible c, map_smul]`.

Both sides reduce to the same expression.
-/
theorem iteratedFDeriv_const_smul_of_ne {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

/- English proof (translation)
Unfold `TaylorLogMetric.taylor`. Establish `h` using `iteratedFDeriv_const_smul_of_ne s hs G (Multiset.card α.toMultiset)`. Simplify using `only [smul_eq_mul] at h`. Rewrite using `[h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]`.
-/
theorem taylor_const_mul' (D : D7) {N N' : ℕ} (s : ℂ) (hs : s ≠ 0) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => s * G z) α = s * TaylorLogMetric.taylor D G α := by
  unfold TaylorLogMetric.taylor
  have h := iteratedFDeriv_const_smul_of_ne s hs G (Multiset.card α.toMultiset)
  simp only [smul_eq_mul] at h
  rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

/- English proof (translation)
Unfold `TaylorLogMetric.lamC`. Distinguish the cases in `ht : t ∈ TaylorLogMetric.Qbar`. Establish `hst : s * t ∈ TaylorLogMetric.Qbar` using `TaylorLogMetric.Qbar.mul_mem hs ht`. Rewrite using `[dif_pos hst, dif_pos hs, dif_pos ht, ← map_mul]`. Both sides reduce to the same expression.

Establish `hst : s * t ∉ TaylorLogMetric.Qbar`. Introduce `h`. Apply `ht` to reduce the goal to its premises. Establish `: s⁻¹ * (s * t) ∈ TaylorLogMetric.Qbar` using `TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.inv_mem hs) h`. Rewrite `this` using `[← mul_assoc, inv_mul_cancel₀ hs0, one_mul]`. Then use the resulting hypothesis.

Rewrite using `[dif_neg hst, dif_neg ht, mul_zero]`.
-/
theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (hs0 : s ≠ 0) (t : ℂ) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  unfold TaylorLogMetric.lamC
  by_cases ht : t ∈ TaylorLogMetric.Qbar
  · have hst : s * t ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs ht
    rw [dif_pos hst, dif_pos hs, dif_pos ht, ← map_mul]
    rfl
  · have hst : s * t ∉ TaylorLogMetric.Qbar := by
      intro h
      apply ht
      have : s⁻¹ * (s * t) ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.inv_mem hs) h
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at this
    rw [dif_neg hst, dif_neg ht, mul_zero]

/- English proof (translation)
Unfold `TaylorLogMetric.lamC`. Rewrite using `[dif_pos (TaylorLogMetric.Qbar.zero_mem)]`. Conclude with `map_zero lam`.
-/
theorem lamC_zero' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : TaylorLogMetric.lamC lam 0 = 0 := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos (TaylorLogMetric.Qbar.zero_mem)]
  exact map_zero lam

/- English proof (translation)
Distinguish the cases in `hs0 : s = 0`. Substitute `hs0` using the available equality. Use extensionality with `α`. Rewrite using `[MvPowerSeries.coeff_C_mul]`. Use `show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => 0 * G z) α) = _`.

Simplify using `only [zero_mul]`. Rewrite using `[lamC_zero', zero_mul]`. Establish `: TaylorLogMetric.taylor D (fun _ : TaylorLogMetric.VC D N N' => (0 : ℂ)) α = 0`. Unfold `TaylorLogMetric.taylor`. Simplify using the standard rewrite rules.

Rewrite using `[this, lamC_zero']`. Use extensionality with `α`. Rewrite using `[MvPowerSeries.coeff_C_mul]`. Use `show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * G z) α) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D G α)`. Rewrite using `[taylor_const_mul' D s hs0 G α, lamC_mul' lam hs hs0]`.
-/
theorem pSer_const_mul' (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pSer D lam (fun z => s * G z) = MvPowerSeries.C (TaylorLogMetric.lamC lam s) * TaylorLogMetric.pSer D lam G := by
  by_cases hs0 : s = 0
  · subst hs0
    ext α
    rw [MvPowerSeries.coeff_C_mul]
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => 0 * G z) α) = _
    simp only [zero_mul]
    rw [lamC_zero', zero_mul]
    have : TaylorLogMetric.taylor D (fun _ : TaylorLogMetric.VC D N N' => (0 : ℂ)) α = 0 := by
      unfold TaylorLogMetric.taylor
      simp
    rw [this, lamC_zero']
  · ext α
    rw [MvPowerSeries.coeff_C_mul]
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * G z) α) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D G α)
    rw [taylor_const_mul' D s hs0 G α, lamC_mul' lam hs hs0]

end Cst

section KerLin

/- English proof (translation)
Establish `hS : ∀ x, xiS H α vol SA SB (fun s => k * Φ (s - x)) e = fun w => k * xiS H α vol SA SB (fun s => Φ (s - x)) e w`. Introduce `x`. Use function extensionality and compare the values at `w`. Unfold `xiS Formalism.L2.Th1.H.sumU`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Establish `: hatS H vol SA (fun s => k * Φ (s - x)) y = k * hatS H vol SA (fun s => Φ (s - x)) y`. Unfold `hatS`. Simplify using `only [mul_assoc, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Use `beta_reduce`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Unfold `xiL`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hS x]`. Simplify using `only [Formalism.L2.Th1.H.opU]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xiL_const_mul' {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (vol : ℝ)
    (SX SA SB : Finset V) (k : ℂ) (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB (fun v => k * Φ v) e z = k * xiL H α vol SX SA SB Φ e z := by
  have hS : ∀ x, xiS H α vol SA SB (fun s => k * Φ (s - x)) e = fun w => k * xiS H α vol SA SB (fun s => Φ (s - x)) e w := by
    intro x
    funext w
    unfold xiS Formalism.L2.Th1.H.sumU
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : hatS H vol SA (fun s => k * Φ (s - x)) y = k * hatS H vol SA (fun s => Φ (s - x)) y := by
      unfold hatS
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    beta_reduce
    rw [this]
    ring
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS x]
  simp only [Formalism.L2.Th1.H.opU]
  ring

/- English proof (translation)
Establish `hon : Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => k * Ξ x) = fun v => k * Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ v`. Use function extensionality and compare the values at `v`. Unfold `Formalism.L2.Ker.onV`. Apply the tactic sequence `split_ifs <;> simp`. Unfold `kerTh thC xiV`.

Rewrite using `[hon]`. Conclude with `xiL_const_mul' _ _ _ _ _ _ _ _ _ _`.
-/
theorem kerTh_const_mul {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k : ℂ) (z : TaylorLogMetric.VC D a b) :
    kerTh B χ SS cl N N' (fun x => k * Ξ x) z = k * kerTh B χ SS cl N N' Ξ z := by
  have hon : Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => k * Ξ x) =
      fun v => k * Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ v := by
    funext v
    unfold Formalism.L2.Ker.onV
    split_ifs <;> simp
  unfold kerTh thC xiV
  rw [hon]
  exact xiL_const_mul' _ _ _ _ _ _ _ _ _ _

end KerLin

section Ser

variable {p : ℕ} [Fact p.Prime] {D : D7}

def rMat (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ} (e : Matrix (Fin N) (Fin N) D.host.E)
    (x y : D.what₂.Tau × Fin N' × Fin N) : ℂ_[p] :=
  TaylorLogMetric.lamC lam (Formalism.L2.KerInert.PullbackComparison.cz D
    (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ e (1 : Matrix (Fin N') (Fin N') D.host.E) (TaylorLogMetric.coordV D y)) x)

/- English proof (translation)
Establish `h` using `Formalism.L2.KerInert.PullbackComparison.pSer_comp D H hH.1 hH.2 (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ e (1 : Matrix (Fin N') (Fin N') D.host.E)) (fun s k => Formalism.L2.KerInert.PullbackComparison.tPull_entry_mem cc δ e 1 s k) lam`. Unfold `serP linSub`. Establish `e1 : (fun z => H (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e (1 : Matrix (Fin N') (Fin N') D.host.E) z)) = H ∘ Formalism.L2.KerInert.PullbackComparison.tPullL cc δ e (1 : Matrix (Fin N') (Fin N') D.host.E)` using `rfl`. Rewrite using `[e1, h]`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Rewrite using `[← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X]`. Both sides reduce to the same expression.
-/
theorem serLaw' (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ} (e : Matrix (Fin N) (Fin N) D.host.E)
    (H : TaylorLogMetric.VC D N N' → ℂ) (hH : Formalism.L2.KerInert.AlgEnt D H) :
    linSub (rMat cc δ lam e) (serP lam H) =
      serP lam (fun z => H (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e (1 : Matrix (Fin N') (Fin N') D.host.E) z)) := by
  have h := Formalism.L2.KerInert.PullbackComparison.pSer_comp D H hH.1 hH.2 (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ e (1 : Matrix (Fin N') (Fin N') D.host.E))
    (fun s k => Formalism.L2.KerInert.PullbackComparison.tPull_entry_mem cc δ e 1 s k) lam
  unfold serP linSub
  have e1 : (fun z => H (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e (1 : Matrix (Fin N') (Fin N') D.host.E) z)) =
      H ∘ Formalism.L2.KerInert.PullbackComparison.tPullL cc δ e (1 : Matrix (Fin N') (Fin N') D.host.E) := rfl
  rw [e1, h]
  congr 1
  funext s
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X]
  rfl

end Ser

section Lk

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.L2.G.Pend.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ)
  (A : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

/- English proof (translation)
Unfold `LkB`. Rewrite using `[Finset.sum_eq_single a']`. Rewrite using `[if_pos rfl]`. Introduce `a'' _ hne`. Rewrite using `[if_neg]`.

Introduce `hh`. Conclude with `hne (congrArg (fun z : X.ZA j => z.2.2.1) hh).symm`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`.
-/
theorem lkB_same (v : X.Pl) (s : Fin (X.G.P.n' v)) (a a' : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))) :
    LkB X Kc j A ⟨v, (s, a, b)⟩ ⟨v, (s, a', b)⟩ = cf X Kc j A v s a a' := by
  unfold LkB
  rw [Finset.sum_eq_single a']
  · rw [if_pos rfl]
  · intro a'' _ hne
    rw [if_neg]
    intro hh
    exact hne (congrArg (fun z : X.ZA j => z.2.2.1) hh).symm
  · intro hh
    exact absurd (Finset.mem_univ _) hh

/- English proof (translation)
Unfold `LkB at h`. Take `⟨a'', _, ha''⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Use `⟨a'', ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `ha'' (if_neg hc)`.
-/
theorem lkB_shape (x y : X.ZA j) (h : LkB X Kc j A x y ≠ 0) : ∃ a'', y = (⟨x.1, (x.2.1, a'', x.2.2.2)⟩ : X.ZA j) := by
  unfold LkB at h
  obtain ⟨a'', _, ha''⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨a'', ?_⟩
  by_contra hc
  exact ha'' (if_neg hc)

/- English proof (translation)
Unfold `linSub SA`. Use `congr 1`. Use function extensionality and compare the values at `z`. Conclude with `linS_LkB X Kc j A z`.
-/
theorem linSub_lkB (f : MvPowerSeries (X.ZA j) Kc) : linSub (LkB X Kc j A) f = SA X Kc j A f := by
  unfold linSub SA
  congr 1
  funext z
  exact linS_LkB X Kc j A z

/- English proof (translation)
Rewrite using `[← linSub_lkB, ← linSub_lkB, linSub_C_mul']`.
-/
theorem SA_C_mul' (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) :
    SA X Kc j A (MvPowerSeries.C a * f) = MvPowerSeries.C a * SA X Kc j A f := by
  rw [← linSub_lkB, ← linSub_lkB, linSub_C_mul']

end Lk

section Frames

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

open Classical in

def frameGL (fd : FData X D) (j : ℕ) (La : X.Lt j) (v : X.Pl) : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  if h : IsUnit (fd.frM j La v).det then Matrix.nonsingInvUnit _ h else 1

def frameInv (fd : FData X D) (j : ℕ) (La : X.Lt j) : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  fun v => (frameGL fd j La v)⁻¹

/- English proof (translation)
Unfold `frameGL`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem frameGL_val (fd : FData X D) (j : ℕ) (La : X.Lt j) (v : X.Pl) (h : IsUnit (fd.frM j La v).det) :
    ((frameGL fd j La v : GL _ _) : Matrix _ _ _) = fd.frM j La v := by
  unfold frameGL
  rw [dif_pos h]
  rfl

open Classical in

def vMat (Kc : Type) [Field Kc] [Algebra (Formalism.L2.G.Pend.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ)
    (La' : X.Lt (j + 1)) (x y : X.ZA j) : Kc :=
  if (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩ ∧ y.2.2.1 = x.2.2.1 then
    c * (if IsOddPos x.2.1 then
      (((fd.frM (j + 1) La' x.1)⁻¹).map (Formalism.L2.G.Pend.tw X Kc x.1 x.2.1))
        (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm y.2.2.2) (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm x.2.2.2)
    else
      ((fd.frM (j + 1) La' x.1).map (Formalism.L2.G.Pend.tw X Kc x.1 x.2.1))
        (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm x.2.2.2) (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm y.2.2.2))
  else 0

variable (Kc : Type) [Field Kc] [Algebra (Formalism.L2.G.Pend.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises. Unfold `vMat`. Conclude with `if_neg hc`.
-/
theorem vMat_shape (fd : FData X D) (cS : Kc) (La' : X.Lt (j + 1)) (x y : X.ZA j) (h : vMat Kc fd cS j La' x y ≠ 0) :
    (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩ ∧ y.2.2.1 = x.2.2.1 := by
  by_contra hc
  apply h
  unfold vMat
  exact if_neg hc

/- English proof (translation)
Take `⟨v, s, a, b⟩` from `x`. Take `⟨v', s', a', b'⟩` from `y`. Distinguish the cases in `h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩`. Consider the cases of `h`. Rewrite using `[Finset.sum_eq_single (⟨v, (s, a, b')⟩ : X.ZA j), Finset.sum_eq_single (⟨v, (s, a', b)⟩ : X.ZA j)]`.

Rewrite using `[lkB_same, lkB_same]`. Simplify using `only [vMat, and_self, if_true]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨vz, sz, az, bz⟩ _ hz`. Assume the negation of the conclusion as `hne`.

Take `⟨a'', h1⟩` from `lkB_shape X Kc j A _ _ (left_ne_zero_of_mul hne)`. Take `⟨-, h3⟩` from `vMat_shape Kc j fd cS La' _ _ (right_ne_zero_of_mul hne)`. Rewrite `h3`, `hz` using `[h1]`. Simplify using `only at h3`. Conclude with `hz (by rw [← h3])`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Introduce and unpack `⟨vz, sz, az, bz⟩ _ hz`. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `vMat_shape Kc j fd cS La' _ _ (left_ne_zero_of_mul hne)`.

Take `⟨a'', h3⟩` from `lkB_shape X Kc j A _ _ (right_ne_zero_of_mul hne)`. Consider the cases of `h1`. Establish `hb : b' = bz` using `congrArg (fun z : X.ZA j => z.2.2.2) h3`. Substitute `hb` using the available equality. Conclude with `hz (by rw [show az = a from h2])`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Rewrite using `[Finset.sum_eq_zero, Finset.sum_eq_zero]`. Introduce `z _`. Assume the negation of the conclusion as `hz`.

Establish `h1` using `LkB_ne X Kc j A _ z (left_ne_zero_of_mul hz)`. Establish `h2` using `(vMat_shape Kc j fd cS La' z _ (right_ne_zero_of_mul hz)).1`. Conclude with `h (h2.trans h1)`. Introduce `z _`. Assume the negation of the conclusion as `hz`.

Establish `h1` using `(vMat_shape Kc j fd cS La' _ z (left_ne_zero_of_mul hz)).1`. Establish `h2` using `LkB_ne X Kc j A z _ (right_ne_zero_of_mul hz)`. Conclude with `h (h2.trans h1)`.
-/
theorem vMat_comm (A : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (fd : FData X D) (cS : Kc) (La' : X.Lt (j + 1))
    (x y : X.ZA j) :
    ∑ z, vMat Kc fd cS j La' x z * LkB X Kc j A z y = ∑ z, LkB X Kc j A x z * vMat Kc fd cS j La' z y := by
  classical
  obtain ⟨v, s, a, b⟩ := x
  obtain ⟨v', s', a', b'⟩ := y
  by_cases h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩
  · cases h
    rw [Finset.sum_eq_single (⟨v, (s, a, b')⟩ : X.ZA j), Finset.sum_eq_single (⟨v, (s, a', b)⟩ : X.ZA j)]
    · rw [lkB_same, lkB_same]
      simp only [vMat, and_self, if_true]
      ring
    · rintro ⟨vz, sz, az, bz⟩ _ hz
      by_contra hne
      obtain ⟨a'', h1⟩ := lkB_shape X Kc j A _ _ (left_ne_zero_of_mul hne)
      obtain ⟨-, h3⟩ := vMat_shape Kc j fd cS La' _ _ (right_ne_zero_of_mul hne)
      rw [h1] at h3 hz
      simp only at h3
      exact hz (by rw [← h3])
    · intro hh
      exact absurd (Finset.mem_univ _) hh
    · rintro ⟨vz, sz, az, bz⟩ _ hz
      by_contra hne
      obtain ⟨h1, h2⟩ := vMat_shape Kc j fd cS La' _ _ (left_ne_zero_of_mul hne)
      obtain ⟨a'', h3⟩ := lkB_shape X Kc j A _ _ (right_ne_zero_of_mul hne)
      cases h1
      have hb : b' = bz := congrArg (fun z : X.ZA j => z.2.2.2) h3
      subst hb
      exact hz (by rw [show az = a from h2])
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro z _
      by_contra hz
      have h1 := LkB_ne X Kc j A _ z (left_ne_zero_of_mul hz)
      have h2 := (vMat_shape Kc j fd cS La' z _ (right_ne_zero_of_mul hz)).1
      exact h (h2.trans h1)
    · intro z _
      by_contra hz
      have h1 := (vMat_shape Kc j fd cS La' _ z (left_ne_zero_of_mul hz)).1
      have h2 := LkB_ne X Kc j A z _ (right_ne_zero_of_mul hz)
      exact h (h2.trans h1)

end Frames

section Split

variable {p : ℕ} [Fact p.Prime] {D : D7}

/- English proof (translation)
Set `G : (Σ v : X.Pl, Fin (X.G.P.n' v)) → ℂ_[p]` to `fun q => if IsOddPos q.2 then ((fd.frM j La q.1).map (twG X E q.1 q.2)) (Fin.cast (rank_eq X j).symm a) (Fin.cast (rank_eq X j).symm a') * (((fd.frM (j + 1) La' q.1)⁻¹).map (twG X E q.1 q.2)) (Fin.cast (rank_eq X (j + 1)).symm b') (Fin.cast (rank_eq X (j + 1)).symm b) else ((fd.f …`. Establish `h1 : subBG E pos fd j La La' (kapOf X pos j ⟨v, (s, a, b)⟩) (kapOf X pos j ⟨v, (s, a', b')⟩) = G (pos.symm (pos ⟨v, s⟩))`. Unfold `subBG`. Conclude with `if_pos rfl`. Rewrite using `[h1]`.

Conclude with `congrArg G (pos.symm_apply_apply _)`.
-/
theorem subBG_block {X : Sys p} (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (v : X.Pl) (s : Fin (X.G.P.n' v)) (a a' : Fin (NN X.G.P.m X.t j))
    (b b' : Fin (NN X.G.P.m X.t (j + 1))) :
    subBG E pos fd j La La' (kapOf X pos j ⟨v, (s, a, b)⟩) (kapOf X pos j ⟨v, (s, a', b')⟩) =
      if IsOddPos s then
        ((fd.frM j La v).map (twG X E v s)) (Fin.cast (rank_eq X j).symm a) (Fin.cast (rank_eq X j).symm a') *
          (((fd.frM (j + 1) La' v)⁻¹).map (twG X E v s)) (Fin.cast (rank_eq X (j + 1)).symm b') (Fin.cast (rank_eq X (j + 1)).symm b)
      else
        ((fd.frM (j + 1) La' v).map (twG X E v s)) (Fin.cast (rank_eq X (j + 1)).symm b) (Fin.cast (rank_eq X (j + 1)).symm b') *
          (((fd.frM j La v)⁻¹).map (twG X E v s)) (Fin.cast (rank_eq X j).symm a') (Fin.cast (rank_eq X j).symm a) := by
  let G : (Σ v : X.Pl, Fin (X.G.P.n' v)) → ℂ_[p] := fun q =>
    if IsOddPos q.2 then
        ((fd.frM j La q.1).map (twG X E q.1 q.2)) (Fin.cast (rank_eq X j).symm a) (Fin.cast (rank_eq X j).symm a') *
          (((fd.frM (j + 1) La' q.1)⁻¹).map (twG X E q.1 q.2)) (Fin.cast (rank_eq X (j + 1)).symm b') (Fin.cast (rank_eq X (j + 1)).symm b)
      else
        ((fd.frM (j + 1) La' q.1).map (twG X E q.1 q.2)) (Fin.cast (rank_eq X (j + 1)).symm b) (Fin.cast (rank_eq X (j + 1)).symm b') *
          (((fd.frM j La q.1)⁻¹).map (twG X E q.1 q.2)) (Fin.cast (rank_eq X j).symm a') (Fin.cast (rank_eq X j).symm a)
  have h1 : subBG E pos fd j La La' (kapOf X pos j ⟨v, (s, a, b)⟩) (kapOf X pos j ⟨v, (s, a', b')⟩) =
      G (pos.symm (pos ⟨v, s⟩)) := by
    unfold subBG
    exact if_pos rfl
  rw [h1]
  exact congrArg G (pos.symm_apply_apply _)

/- English proof (translation)
Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Take `⟨v, s, a, b⟩` from `x`. Take `⟨v', s', a', b'⟩` from `y`. Distinguish the cases in `h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩`.

Consider the cases of `h`. Rewrite using `[Finset.sum_eq_single (⟨v, (s, a, b')⟩ : X.ZA j)]`. Rewrite using `[lkB_same, subBG_block]`. Establish `htw : twG X E v s = tw X ℂ_[p] v s` using `rfl`. Establish `hB : ((frameInv fd j La v : GL _ _) : Matrix _ _ _) = (fd.frM j La v)⁻¹`.

Unfold `frameInv`. Rewrite using `[Matrix.coe_units_inv, frameGL_val fd j La v (hFr v)]`. Establish `hBi : (((frameInv fd j La v)⁻¹ : GL _ _) : Matrix _ _ _) = fd.frM j La v`. Unfold `frameInv`. Rewrite using `[inv_inv, frameGL_val fd j La v (hFr v)]`.

Distinguish the cases in `hs : IsOddPos s`. Simplify using `only [vMat, cf, hs, and_self, ↓reduceIte, htw, hBi, mAt, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [vMat, cf, hs, and_self, ↓reduceIte, htw, hB, mAt, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨vz, sz, az, bz⟩ _ hz`. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `vMat_shape ℂ_[p] j fd c La' _ _ (left_ne_zero_of_mul hne)`. Take `⟨a'', h3⟩` from `lkB_shape X ℂ_[p] j (frameInv fd j La) _ _ (right_ne_zero_of_mul hne)`. Consider the cases of `h1`.

Establish `hb : b' = bz` using `congrArg (fun z : X.ZA j => z.2.2.2) h3`. Substitute `hb` using the available equality. Conclude with `hz (by rw [show az = a from h2])`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`.

Establish `hne : (kapOf X pos j ⟨v, (s, a, b)⟩).1 ≠ (kapOf X pos j ⟨v', (s', a', b')⟩).1`. Introduce `hh`. Conclude with `h (pos.injective hh).symm`. Unfold `subBG`. Rewrite using `[if_neg hne, mul_zero]`.

Use `symm`. Use `Finset.sum_eq_zero fun z _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hz`. Establish `h1` using `(vMat_shape ℂ_[p] j fd c La' _ z (left_ne_zero_of_mul hz)).1`. Establish `h2` using `LkB_ne X ℂ_[p] j (frameInv fd j La) z _ (right_ne_zero_of_mul hz)`.

Conclude with `h (h2.trans h1)`.
-/
theorem subB_split (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (c : ℂ_[p])
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (hFr : ∀ v, IsUnit (fd.frM j La v).det) (x y : X.ZA j) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    c * subBG E pos fd j La La' (kapOf X pos j x) (kapOf X pos j y) =
      ∑ z, vMat ℂ_[p] fd c j La' x z * LkB X ℂ_[p] j (frameInv fd j La) z y := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  classical
  obtain ⟨v, s, a, b⟩ := x
  obtain ⟨v', s', a', b'⟩ := y
  by_cases h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩
  · cases h
    rw [Finset.sum_eq_single (⟨v, (s, a, b')⟩ : X.ZA j)]
    · rw [lkB_same, subBG_block]
      have htw : twG X E v s = tw X ℂ_[p] v s := rfl
      have hB : ((frameInv fd j La v : GL _ _) : Matrix _ _ _) = (fd.frM j La v)⁻¹ := by
        unfold frameInv
        rw [Matrix.coe_units_inv, frameGL_val fd j La v (hFr v)]
      have hBi : (((frameInv fd j La v)⁻¹ : GL _ _) : Matrix _ _ _) = fd.frM j La v := by
        unfold frameInv
        rw [inv_inv, frameGL_val fd j La v (hFr v)]
      by_cases hs : IsOddPos s
      · simp only [vMat, cf, hs, and_self, ↓reduceIte, htw, hBi, mAt, Matrix.submatrix_apply,
          Matrix.map_apply, finCongr_apply]
        ring
      · simp only [vMat, cf, hs, and_self, ↓reduceIte, htw, hB, mAt, Matrix.transpose_apply,
          Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply]
        ring
    · rintro ⟨vz, sz, az, bz⟩ _ hz
      by_contra hne
      obtain ⟨h1, h2⟩ := vMat_shape ℂ_[p] j fd c La' _ _ (left_ne_zero_of_mul hne)
      obtain ⟨a'', h3⟩ := lkB_shape X ℂ_[p] j (frameInv fd j La) _ _ (right_ne_zero_of_mul hne)
      cases h1
      have hb : b' = bz := congrArg (fun z : X.ZA j => z.2.2.2) h3
      subst hb
      exact hz (by rw [show az = a from h2])
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · have hne : (kapOf X pos j ⟨v, (s, a, b)⟩).1 ≠ (kapOf X pos j ⟨v', (s', a', b')⟩).1 := by
      intro hh
      exact h (pos.injective hh).symm
    unfold subBG
    rw [if_neg hne, mul_zero]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    by_contra hz
    have h1 := (vMat_shape ℂ_[p] j fd c La' _ z (left_ne_zero_of_mul hz)).1
    have h2 := LkB_ne X ℂ_[p] j (frameInv fd j La) z _ (right_ne_zero_of_mul hz)
    exact h (h2.trans h1)

open Classical in
/- English proof (translation)
Rewrite using `[Formalism.L2.KerInert.PullbackComparison.tPullL_apply]`. Use `show ((Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D x.1)) * Matrix.of (TaylorLogMetric.coordV D y x.1) * e.map (TaylorLogMetric.embT D x.1) : Matrix _ _ ℂ)) x.2.1 x.2.2 = _`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, Matrix.map_apply, TaylorLogMetric.coordV]`. Distinguish the cases in `h : x.1 = y.1 ∧ x.2.1 = y.2.1`.

Rewrite using `[if_pos h, Finset.sum_eq_single y.2.2]`. Rewrite using `[if_pos ⟨h.1, h.2, rfl⟩, one_mul]`. Introduce `d _ hd`. Rewrite using `[if_neg (fun hh => hd hh.2.2), zero_mul]`. Introduce `hh`.

Conclude with `absurd (Finset.mem_univ _) hh`. Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun hh => h ⟨hh.1, hh.2.1⟩), zero_mul]`.
-/
theorem cz_tPull' (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (e : Matrix (Fin N) (Fin N) D.host.E)
    (x y : D.what₂.Tau × Fin N' × Fin N) :
    Formalism.L2.KerInert.PullbackComparison.cz D (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ e (1 : Matrix (Fin N') (Fin N') D.host.E) (TaylorLogMetric.coordV D y)) x =
      if x.1 = y.1 ∧ x.2.1 = y.2.1 then TaylorLogMetric.embT D x.1 (e y.2.2 x.2.2) else 0 := by
  rw [Formalism.L2.KerInert.PullbackComparison.tPullL_apply]
  show ((Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D x.1)) * Matrix.of (TaylorLogMetric.coordV D y x.1) *
    e.map (TaylorLogMetric.embT D x.1) : Matrix _ _ ℂ)) x.2.1 x.2.2 = _
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.map_apply, TaylorLogMetric.coordV]
  by_cases h : x.1 = y.1 ∧ x.2.1 = y.2.1
  · rw [if_pos h, Finset.sum_eq_single y.2.2]
    · rw [if_pos ⟨h.1, h.2, rfl⟩, one_mul]
    · intro d _ hd
      rw [if_neg (fun hh => hd hh.2.2), zero_mul]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg (fun hh => h ⟨hh.1, hh.2.1⟩), zero_mul]

def eGL' (X : Sys p) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) {N : ℕ} (e : Matrix (Fin N) (Fin N) D.host.E) (he : e * star e = 1)
    (v : X.Pl) : GL (Fin N) (X.G.P.Qq v) :=
  ⟨e.map (ρ v), (star e).map (ρ v), by rw [← Matrix.map_mul, he, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, mul_eq_one_comm.1 he, Matrix.map_one _ (map_zero _) (map_one _)]⟩

/- English proof (translation)
Use `⟨kapOf_injective X pos j, fun t => ?_⟩` and prove the remaining obligations. Take `⟨τ, b, a⟩` from `t`. Use `⟨⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast (rank_eq X j) a, Fin.cast (rank_eq X (j + 1)) b)⟩, ?_⟩` and prove the remaining obligations. Simplify using `[kapOf]`.
-/
theorem kapOf_bij' (X : Sys p) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (j : ℕ) :
    Function.Bijective (kapOf X pos j) := by
  refine ⟨kapOf_injective X pos j, fun t => ?_⟩
  obtain ⟨τ, b, a⟩ := t
  refine ⟨⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast (rank_eq X j) a, Fin.cast (rank_eq X (j + 1)) b)⟩, ?_⟩
  simp [kapOf]

variable (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (cS : ℂ_[p])
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)

/- English proof (translation)
Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Take `⟨v, s, a, b⟩` from `x`. Take `⟨v', s', a', b'⟩` from `y`. Unfold `rMat`.

Rewrite using `[cz_tPull']`. Distinguish the cases in `h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩`. Consider the cases of `h`. Distinguish the cases in `hb : b' = b`. Substitute `hb` using the available equality.

Rewrite using `[lkB_same, if_pos ⟨rfl, rfl⟩]`. Establish `h1` using `hLP v s (e (Fin.cast (rank_eq X j).symm a') (Fin.cast (rank_eq X j).symm a))`. Establish `h2 : TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (kapOf X pos j ⟨v, (s, a, b')⟩).1 (e (kapOf X pos j ⟨v, (s, a', b')⟩).2.2 (kapOf X pos j ⟨v, (s, a, b')⟩).2.2)) = TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) (e (Fin.cast (rank_eq X j).symm a') (Fin.cast (ran …` using `rfl`. Rewrite using `[h2, h1]`. Establish `htw : twG X E v s = tw X ℂ_[p] v s` using `rfl`.

Rewrite using `[htw]`. Distinguish the cases in `hs : IsOddPos s`. Establish `hi : (((eGL' X ρ e he v)⁻¹ : GL _ _) : Matrix _ _ (X.G.P.Qq v)) = (star e).map (ρ v)` using `rfl`. Simplify using `only [cf, hs, if_true, mAt, hi, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Matrix.star_apply, Formalism.L2.KerInert.PullbackComparison.conj_eq_star]`. Establish `hi : ((eGL' X ρ e he v : GL _ _) : Matrix _ _ (X.G.P.Qq v)) = e.map (ρ v)` using `rfl`.

Simplify using `only [cf, hs, if_false, mAt, hi, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply]`. Rewrite using `[if_neg, lamC_zero']`. Assume the negation of the conclusion as `hne`. Take `⟨a'', h3⟩` from `lkB_shape X ℂ_[p] j _ _ _ hne`. Conclude with `hb (congrArg (fun z : X.ZA j => z.2.2.2) h3)`.

Introduce and unpack `⟨-, h2⟩`. Conclude with `hb (Fin.cast_injective (rank_eq X (j + 1)).symm h2).symm`. Rewrite using `[if_neg, lamC_zero']`. Assume the negation of the conclusion as `hne`. Conclude with `h (LkB_ne X ℂ_[p] j _ _ _ hne)`.

Introduce and unpack `⟨h1, -⟩`. Conclude with `h (pos.injective h1).symm`.
-/
theorem lkB_eGL (hLP : LamPos X E pos lam ρ) (j : ℕ)
    (e : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (he : e * star e = 1) (x y : X.ZA j) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    LkB X ℂ_[p] j (eGL' X ρ e he) x y = rMat cc δ lam e (kapOf X pos j x) (kapOf X pos j y) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  classical
  obtain ⟨v, s, a, b⟩ := x
  obtain ⟨v', s', a', b'⟩ := y
  unfold rMat
  rw [cz_tPull']
  by_cases h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩
  · cases h
    by_cases hb : b' = b
    · subst hb
      rw [lkB_same, if_pos ⟨rfl, rfl⟩]
      have h1 := hLP v s (e (Fin.cast (rank_eq X j).symm a') (Fin.cast (rank_eq X j).symm a))
      have h2 : TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (kapOf X pos j ⟨v, (s, a, b')⟩).1
          (e (kapOf X pos j ⟨v, (s, a', b')⟩).2.2 (kapOf X pos j ⟨v, (s, a, b')⟩).2.2)) =
          TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) (e (Fin.cast (rank_eq X j).symm a') (Fin.cast (rank_eq X j).symm a))) := rfl
      rw [h2, h1]
      have htw : twG X E v s = tw X ℂ_[p] v s := rfl
      rw [htw]
      by_cases hs : IsOddPos s
      · have hi : (((eGL' X ρ e he v)⁻¹ : GL _ _) : Matrix _ _ (X.G.P.Qq v)) = (star e).map (ρ v) := rfl
        simp only [cf, hs, if_true, mAt, hi, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Matrix.star_apply,
          Formalism.L2.KerInert.PullbackComparison.conj_eq_star]
      · have hi : ((eGL' X ρ e he v : GL _ _) : Matrix _ _ (X.G.P.Qq v)) = e.map (ρ v) := rfl
        simp only [cf, hs, if_false, mAt, hi, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply]
    · rw [if_neg, lamC_zero']
      · by_contra hne
        obtain ⟨a'', h3⟩ := lkB_shape X ℂ_[p] j _ _ _ hne
        exact hb (congrArg (fun z : X.ZA j => z.2.2.2) h3)
      · rintro ⟨-, h2⟩
        exact hb (Fin.cast_injective (rank_eq X (j + 1)).symm h2).symm
  · rw [if_neg, lamC_zero']
    · by_contra hne
      exact h (LkB_ne X ℂ_[p] j _ _ _ hne)
    · rintro ⟨h1, -⟩
      exact h (pos.injective h1).symm

/- English proof (translation)
The claim follows from `resV_linSub _ (kapOf_bij' X pos j) Bm f`.
-/
theorem ren' (j : ℕ) (Bm : (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (f : MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    resV (kapOf X pos j) (linSub Bm f) = linSub (fun x y => Bm (kapOf X pos j x) (kapOf X pos j y)) (resV (kapOf X pos j) f) :=
  resV_linSub _ (kapOf_bij' X pos j) Bm f

/- English proof (translation)
Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Establish `hsplit : (fun x y => cS * subBG E pos fd j La La' (kapOf X pos j x) (kapOf X pos j y)) = fun x y => ∑ z, vMat ℂ_[p] fd cS j La' x z * LkB X ℂ_[p] j (frameInv fd j La) z y`. Use function extensionality and compare the values at `x y`. Conclude with `subB_split X E pos fd cS j La La' hFr x y`.

Rewrite using `[hsplit, ← linSub_linSub', linSub_lkB]`.
-/
theorem split2' (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (hFr : ∀ v, IsUnit (fd.frM j La v).det)
    (g : MvPowerSeries (X.ZA j) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    linSub (fun x y => cS * subBG E pos fd j La La' (kapOf X pos j x) (kapOf X pos j y)) g =
      SA X ℂ_[p] j (frameInv fd j La) (linSub (vMat ℂ_[p] fd cS j La') g) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  have hsplit : (fun x y => cS * subBG E pos fd j La La' (kapOf X pos j x) (kapOf X pos j y)) =
      fun x y => ∑ z, vMat ℂ_[p] fd cS j La' x z * LkB X ℂ_[p] j (frameInv fd j La) z y := by
    funext x y
    exact subB_split X E pos fd cS j La La' hFr x y
  rw [hsplit, ← linSub_linSub', linSub_lkB]

/- English proof (translation)
Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Rewrite using `[← linSub_lkB, linSub_linSub', linSub_linSub']`. Use `congr 1`. Use function extensionality and compare the values at `x y`.

Rewrite using `[vMat_comm]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[lkB_eGL X E pos cc δ lam ρ hLP j e he x z]`.
-/
theorem comm2' (hLP : LamPos X E pos lam ρ) (j : ℕ) (La' : X.Lt (j + 1))
    (e : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (he : e * star e = 1) (g : MvPowerSeries (X.ZA j) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    SA X ℂ_[p] j (eGL' X ρ e he) (linSub (vMat ℂ_[p] fd cS j La') g) =
      linSub (vMat ℂ_[p] fd cS j La') (linSub (fun x y => rMat cc δ lam e (kapOf X pos j x) (kapOf X pos j y)) g) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  rw [← linSub_lkB, linSub_linSub', linSub_linSub']
  congr 1
  funext x y
  rw [vMat_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [lkB_eGL X E pos cc δ lam ρ hLP j e he x z]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `h : frameGL fd j (c, (X.Lv.lev j c).smul γ L) v * gamAt X j c γ v = eGL' X ρ e he v * frameGL fd j (c, L) v`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, frameGL_val fd j _ v (hG v), frameGL_val fd j _ v (hF v)]`. Conclude with `hT v`.

Unfold `frameInv`. Rewrite using `[eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]`.
-/
theorem gl_move (j : ℕ) (c : X.Lv.comp j) (L : (X.Pj j).Tup) (γ : (X.Lv.lev j c).Γ)
    (e : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (he : e * star e = 1)
    (hF : ∀ v, IsUnit (fd.frM j (c, L) v).det) (hG : ∀ v, IsUnit (fd.frM j (c, (X.Lv.lev j c).smul γ L) v).det)
    (hT : ∀ v, fd.frM j (c, (X.Lv.lev j c).smul γ L) v * (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) =
      e.map (ρ v) * fd.frM j (c, L) v) :
    (fun v => gamAt X j c γ v * frameInv fd j (c, L) v) = fun v => frameInv fd j (c, (X.Lv.lev j c).smul γ L) v * eGL' X ρ e he v := by
  funext v
  have h : frameGL fd j (c, (X.Lv.lev j c).smul γ L) v * gamAt X j c γ v = eGL' X ρ e he v * frameGL fd j (c, L) v := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, frameGL_val fd j _ v (hG v), frameGL_val fd j _ v (hF v)]
    exact hT v
  unfold frameInv
  rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]

/- English proof (translation)
Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Rewrite using `[ren', ren', ren', split2' X E pos fd cS j (c, L) La' hF, split2' X E pos fd cS j (c, (X.Lv.lev j c).smul γ L) La' hG, SA_mul, gl_move X fd ρ j c L γ e he hF hG hT, ← SA_mul, comm2' X E pos fd cc δ lam cS ρ hLP j La' e he]`.
-/
theorem frm_move (hLP : LamPos X E pos lam ρ) (j : ℕ) (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1))
    (γ : (X.Lv.lev j c).Γ) (e : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (he : e * star e = 1)
    (hF : ∀ v, IsUnit (fd.frM j (c, L) v).det) (hG : ∀ v, IsUnit (fd.frM j (c, (X.Lv.lev j c).smul γ L) v).det)
    (hT : ∀ v, fd.frM j (c, (X.Lv.lev j c).smul γ L) v * (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) =
      e.map (ρ v) * fd.frM j (c, L) v)
    (f : MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    SA X ℂ_[p] j (gamAt X j c γ) (resV (kapOf X pos j) (linSub (fun x y => cS * subBG E pos fd j (c, L) La' x y) f)) =
      resV (kapOf X pos j) (linSub (fun x y => cS * subBG E pos fd j (c, (X.Lv.lev j c).smul γ L) La' x y)
        (linSub (rMat cc δ lam e) f)) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  rw [ren', ren', ren', split2' X E pos fd cS j (c, L) La' hF, split2' X E pos fd cS j (c, (X.Lv.lev j c).smul γ L) La' hG,
    SA_mul, gl_move X fd ρ j c L γ e he hF hG hT, ← SA_mul, comm2' X E pos fd cc δ lam cS ρ hLP j La' e he]

end Split

section Move

/- English proof (translation)
Establish `hN1 : SDLat.smulLat (1 : Matrix (Fin b) (Fin b) D.host.E) N' = N'`. Simplify using `[SDLat.smulLat]`. Establish `hXg : (fun x => cΞ * Ξ (Matrix.toLin' (star (1 : Matrix (Fin b) (Fin b) D.host.E)) ∘ₗ x ∘ₗ Matrix.toLin' e)) = Ξg`. Use function extensionality and compare the values at `x`. Rewrite using `[hXi x, star_one, Matrix.toLin'_one, LinearMap.id_comp]`.

Rewrite `hI` using `[hN1, hXg]`. Rewrite using `[hI]`. Conclude with `kerTh_const_mul B χ SS cl N N' Ξ cΞ _`.
-/
theorem kerTh_move (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (Ξ Ξg : Formalism.L2.Col.HomE D.host.E a b → ℂ)
    (e : Matrix (Fin a) (Fin a) D.host.E) (cΞ : ℂ)
    (hI : kerTh B χ SS cl (SDLat.smulLat e N) (SDLat.smulLat (1 : Matrix (Fin b) (Fin b) D.host.E) N')
      (fun x => cΞ * Ξ (Matrix.toLin' (star (1 : Matrix (Fin b) (Fin b) D.host.E)) ∘ₗ x ∘ₗ Matrix.toLin' e)) =
      TaylorLogMetric.pull D B.tor e 1 (kerTh B χ SS cl N N' (fun x => cΞ * Ξ x))) (hXi : ∀ x, Ξg x = cΞ * Ξ (x ∘ₗ Matrix.toLin' e))
    (z : TaylorLogMetric.VC D a b) :
    kerTh B χ SS cl (SDLat.smulLat e N) N' Ξg z =
      cΞ * kerTh B χ SS cl N N' Ξ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e (1 : Matrix (Fin b) (Fin b) D.host.E) z) := by
  have hN1 : SDLat.smulLat (1 : Matrix (Fin b) (Fin b) D.host.E) N' = N' := by
    simp [SDLat.smulLat]
  have hXg : (fun x => cΞ * Ξ (Matrix.toLin' (star (1 : Matrix (Fin b) (Fin b) D.host.E)) ∘ₗ x ∘ₗ Matrix.toLin' e)) = Ξg := by
    funext x
    rw [hXi x, star_one, Matrix.toLin'_one, LinearMap.id_comp]
  rw [hN1, hXg] at hI
  rw [hI]
  exact kerTh_const_mul B χ SS cl N N' Ξ cΞ _

end Move

/- English proof (translation)
Introduce `D cc δ B χ hcv hd12 hδ hχ hLat hVec hEq SS cl hcl hSS p _ X E pos fd lam Ξ₀ muT ρ cS hOK hLP hMT`. Introduce `j hj c0 L La' γ hL hL'`. Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Take `⟨e, cΞ, he, hT, hN, hcΞ, hXi, hsc⟩` from `hMT j hj c0 L La' γ hL hL'`.

Establish `hLg : (X.Pj j).IsLatTup ((X.Lv.lev j c0).smul γ L)` using `(Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ L).2 hL`. Take `⟨hAdm, hDat, hDiff, hCoef, hsQ, hcQ, -, hFrL⟩` from `hOK j hj (c0, L) La' hL hL'`. Take `⟨-, -, -, -, hsQg, hcQg, -, hFrG⟩` from `hOK j hj (c0, (X.Lv.lev j c0).smul γ L) La' hLg hL'`. Establish `hAlg : Formalism.L2.KerInert.AlgEnt D (kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La'))` using `⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable hDiff _, hCoef⟩`. Establish `hkQ : scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' * (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * cΞ ∈ TaylorLogMetric.Qbar` using `TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hsQg (TaylorLogMetric.Qbar.inv_mem hcQg)) hcΞ`.

Establish `hsL : scal0 X fd χ muT j (c0, L) La' * (Base.chiFac χ _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar` using `TaylorLogMetric.Qbar.mul_mem hsQ (TaylorLogMetric.Qbar.inv_mem hcQ)`. Establish `hmove : ∀ z, kerTh B χ SS cl (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, (X.Lv.lev j c0).smul γ L) La') z = cΞ * kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La') (Formalism.L2.KerInert.tPull D (TaylorLo …`. Introduce `z`. Rewrite using `[hN]`. Establish `h1 : (1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) D.host.E) * star (1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) D.host.E) = 1`.

Rewrite using `[star_one, mul_one]`. Conclude with `kerTh_move D cc δ B χ SS cl _ _ _ _ e cΞ (GlobalTheory.T.kernel_theta_unitary_lattice_equivariant D cc δ B χ hcv hd12 hδ hχ hLat hVec hEq SS cl hcl hSS _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (fun x => cΞ * xiM X fd Ξ₀ j (c0, L) La' x) hAdm (hDat.const_mul cΞ) e 1 he h1) hX …`. Establish `hserG : (serP lam fun z => scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' * (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * kerTh B χ SS cl (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, (X.Lv.l …`. Establish `h1 : (fun z => scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' * (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * kerTh B χ SS cl (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, (X.Lv.lev j c0).smu …`. Use function extensionality and compare the values at `z`.

Rewrite using `[hmove z]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, serLaw' cc δ lam e _ hAlg]`. Conclude with `pSer_const_mul' D lam hkQ _`. Establish `hserL : (serP lam fun z => scal0 X fd χ muT j (c0, L) La' * (Base.chiFac χ _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La'))⁻¹ * kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La') z) = MvPowerSeries.C (TaylorLogMetric.lamC lam (scal0 X fd χ muT j ( …` using `pSer_const_mul' D lam hsL _`.

Establish `hFL : ∀ v, IsUnit (fd.frM j (c0, L) v).det` using `fun v => (hFrL v).1`. Establish `hFG : ∀ v, IsUnit (fd.frM j (c0, (X.Lv.lev j c0).smul γ L) v).det` using `fun v => (hFrG v).1`. Unfold `thFOf`. Rewrite using `[frecG_eq, frecG_eq, hserG, hserL, MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, linSub_C_mul', linSub_C_mul', resV_C_mul', resV_C_mul', SA_C_mul', ← mul_assoc, ← map_mul, hsc, ← frm_move X E pos fd cc δ lam cS ρ hLP j c …`.
-/
theorem kapLawLt_frecG : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (c : ℂ_[p]), PairOK X fd B χ SS cl Ξ₀ muT ρ → LamPos X E pos lam ρ → MoveTie X E fd χ lam Ξ₀ muT ρ → letI := wittFractionAlgebraCp p; letI := algKfC E; KapLawLt X ℂ_[p] (thFOf X pos (FrecG E pos fd B χ lam SS cl Ξ₀ muT c)) := by
  intro D cc δ B χ hcv hd12 hδ hχ hLat hVec hEq SS cl hcl hSS p _ X E pos fd lam Ξ₀ muT ρ cS hOK hLP hMT
  intro j hj c0 L La' γ hL hL'
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  obtain ⟨e, cΞ, he, hT, hN, hcΞ, hXi, hsc⟩ := hMT j hj c0 L La' γ hL hL'
  have hLg : (X.Pj j).IsLatTup ((X.Lv.lev j c0).smul γ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ L).2 hL
  obtain ⟨hAdm, hDat, hDiff, hCoef, hsQ, hcQ, -, hFrL⟩ := hOK j hj (c0, L) La' hL hL'
  obtain ⟨-, -, -, -, hsQg, hcQg, -, hFrG⟩ := hOK j hj (c0, (X.Lv.lev j c0).smul γ L) La' hLg hL'
  have hAlg : Formalism.L2.KerInert.AlgEnt D (kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La')) :=
    ⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable hDiff _, hCoef⟩
  have hkQ : scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' *
      (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * cΞ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hsQg (TaylorLogMetric.Qbar.inv_mem hcQg)) hcΞ
  have hsL : scal0 X fd χ muT j (c0, L) La' * (Base.chiFac χ _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hsQ (TaylorLogMetric.Qbar.inv_mem hcQ)
  have hmove : ∀ z, kerTh B χ SS cl (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La')
      (xiM X fd Ξ₀ j (c0, (X.Lv.lev j c0).smul γ L) La') z =
      cΞ * kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La')
        (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e 1 z) := by
    intro z
    rw [hN]
    have h1 : (1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) D.host.E) *
        star (1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) D.host.E) = 1 := by
      rw [star_one, mul_one]
    exact kerTh_move D cc δ B χ SS cl _ _ _ _ e cΞ
      (GlobalTheory.T.kernel_theta_unitary_lattice_equivariant D cc δ B χ hcv hd12 hδ hχ hLat hVec hEq SS cl hcl hSS _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La')
        (fun x => cΞ * xiM X fd Ξ₀ j (c0, L) La' x) hAdm (hDat.const_mul cΞ) e 1 he h1) hXi z
  have hserG : (serP lam fun z => scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' *
        (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ *
      kerTh B χ SS cl (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La')
        (xiM X fd Ξ₀ j (c0, (X.Lv.lev j c0).smul γ L) La') z) =
      MvPowerSeries.C (TaylorLogMetric.lamC lam (scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' *
        (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * cΞ)) *
      linSub (rMat cc δ lam e) (serP lam (kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La'))) := by
    have h1 : (fun z => scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' *
          (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ *
        kerTh B χ SS cl (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La')
          (xiM X fd Ξ₀ j (c0, (X.Lv.lev j c0).smul γ L) La') z) =
        fun z => (scal0 X fd χ muT j (c0, (X.Lv.lev j c0).smul γ L) La' *
          (Base.chiFac χ _ _ (fd.kerN j (c0, (X.Lv.lev j c0).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * cΞ) *
          kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La')
            (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e 1 z) := by
      funext z
      rw [hmove z]
      ring
    rw [h1, serLaw' cc δ lam e _ hAlg]
    exact pSer_const_mul' D lam hkQ _
  have hserL : (serP lam fun z => scal0 X fd χ muT j (c0, L) La' *
        (Base.chiFac χ _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La'))⁻¹ *
      kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La') z) =
      MvPowerSeries.C (TaylorLogMetric.lamC lam (scal0 X fd χ muT j (c0, L) La' *
        (Base.chiFac χ _ _ (fd.kerN j (c0, L)) (fd.kerN (j + 1) La'))⁻¹)) *
      serP lam (kerTh B χ SS cl (fd.kerN j (c0, L)) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j (c0, L) La')) :=
    pSer_const_mul' D lam hsL _
  have hFL : ∀ v, IsUnit (fd.frM j (c0, L) v).det := fun v => (hFrL v).1
  have hFG : ∀ v, IsUnit (fd.frM j (c0, (X.Lv.lev j c0).smul γ L) v).det := fun v => (hFrG v).1
  unfold thFOf
  rw [frecG_eq, frecG_eq, hserG, hserL, MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← map_mul, linSub_C_mul', linSub_C_mul', resV_C_mul', resV_C_mul', SA_C_mul', ← mul_assoc, ← map_mul, hsc,
    ← frm_move X E pos fd cc δ lam cS ρ hLP j c0 L La' γ e he hFL hFG hT]

end GlobalTheory.TwU.LawAll
