import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨c, hc, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `AddSubgroup.add_mem _ ha hb`.

Consider the case `neg a _ ha => rw [mul_neg]`. Conclude with `AddSubgroup.neg_mem _ ha`.
-/
theorem int_mul_mem_lamOf (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨w, hw, B, hB, rfl⟩` from `hw`. Conclude with `AddSubgroup.subset_closure ⟨_, int_mul_mem_lamOf a hw, B, hB, smul_smul _ _ _⟩`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `AddSubgroup.add_mem _ ha hb`. Consider the case `neg a _ ha => rw [smul_neg]`. Conclude with `AddSubgroup.neg_mem _ ha`.
-/
theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, int_mul_mem_lamOf a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

/- English proof (translation)
Introduce `D cc δ B h N N' L L' hA x hx`. Establish `hsd` using `(h.1 N N' L L' hA).1`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `hw` using `int_smul_mem_La L L' a hx`. Rewrite `hw` using `[ha]`.

Establish `hw' : StandardLatticesGL3.w0 D • x ∈ dualLat (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L')`. Rewrite using `[hsd]`. Conclude with `hw`. Take `⟨m, hm⟩` from `hw' x hx`. Establish `him : (TaylorLogMetric.Hf D B.tor x x).im = 0`.

Establish `: starRingEnd ℂ (TaylorLogMetric.Hf D B.tor x x) = TaylorLogMetric.Hf D B.tor x x`. Simplify using `only [TaylorLogMetric.Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]`. Conclude with `Complex.conj_eq_iff_im.1 this`. Establish `h1 : (StandardLatticesGL3.w0 D).re = 1 / 2` using `by simp [StandardLatticesGL3.w0]`. Establish `h2 : (StandardLatticesGL3.w0 D).im = Real.sqrt D.host.d / 2` using `by simp [StandardLatticesGL3.w0]`.

Establish `h3 : formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = TaylorLogMetric.Hf D B.tor x x` using `rfl`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, altE, LinearMap.map_smul₂, h3, smul_eq_mul, Complex.mul_im, h1, h2, him]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qIntAll_of_latAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  intro D cc δ B h N N' L L' hA x hx
  have hsd := (h.1 N N' L L' hA).1
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hw := int_smul_mem_La L L' a hx
  rw [ha] at hw
  have hw' : StandardLatticesGL3.w0 D • x ∈ dualLat (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') := by
    rw [hsd]; exact hw
  obtain ⟨m, hm⟩ := hw' x hx
  have him : (TaylorLogMetric.Hf D B.tor x x).im = 0 := by
    have : starRingEnd ℂ (TaylorLogMetric.Hf D B.tor x x) = TaylorLogMetric.Hf D B.tor x x := by
      simp only [TaylorLogMetric.Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
    exact Complex.conj_eq_iff_im.1 this
  have h1 : (StandardLatticesGL3.w0 D).re = 1 / 2 := by simp [StandardLatticesGL3.w0]
  have h2 : (StandardLatticesGL3.w0 D).im = Real.sqrt D.host.d / 2 := by simp [StandardLatticesGL3.w0]
  have h3 : formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = TaylorLogMetric.Hf D B.tor x x := rfl
  refine ⟨m, ?_⟩
  rw [← hm, altE, LinearMap.map_smul₂, h3, smul_eq_mul, Complex.mul_im, h1, h2, him]
  ring

end GlobalTheory.ThetaMove
