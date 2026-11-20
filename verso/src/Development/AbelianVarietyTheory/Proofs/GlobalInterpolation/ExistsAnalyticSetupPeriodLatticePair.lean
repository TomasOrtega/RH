import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.MomSetup

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' : ℕ}

abbrev Ix (D : D7) (N N' : ℕ) : Type := D.what₂.Tau × Fin N' × Fin N

abbrev gDim (D : D7) (N N' : ℕ) : ℕ := Fintype.card (Ix D N N')

def coordL (D : D7) (N N' : ℕ) : VC D N N' ≃ₗ[ℂ] (Fin (gDim D N N') → ℂ) where
  toFun z k := z ((Fintype.equivFin (Ix D N N')).symm k).1 ((Fintype.equivFin (Ix D N N')).symm k).2.1
    ((Fintype.equivFin (Ix D N N')).symm k).2.2
  invFun w τ i j := w (Fintype.equivFin (Ix D N N') (τ, i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by funext τ i j; simp
  right_inv w := by funext k; simp

def coord (D : D7) (N N' : ℕ) : VC D N N' ≃L[ℂ] (Fin (gDim D N N') → ℂ) :=
  (coordL D N N').toContinuousLinearEquiv

/- English proof (translation)
Use `show coordL D N N' z _ = _`. Simplify using `[coordL]`.
-/
theorem coord_apply_equivFin (z : VC D N N') (x : Ix D N N') :
    coord D N N' z (Fintype.equivFin (Ix D N N') x) = z x.1 x.2.1 x.2.2 := by
  show coordL D N N' z _ = _
  simp [coordL]

/- English proof (translation)
Establish `h1 : ∀ u v : Fin (gDim D N N') → ℂ, JMB.hf (((area T.abelian₂ : ℂ))⁻¹ • (1 : Matrix (Fin (gDim D N N')) (Fin (gDim D N N')) ℂ)) u v = (∑ k, u k * starRingEnd ℂ (v k)) / (area T.abelian₂ : ℂ)`. Introduce `u v`. Simplify using `only [JMB.hf, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[h1, Hf]`.

Use `congr 1`. Rewrite using `[← (Fintype.equivFin (Ix D N N')).sum_comp]`. Simplify using `only [coord_apply_equivFin]`. Rewrite using `[Fintype.sum_prod_type]`. Conclude with `Finset.sum_congr rfl fun τ _ => Fintype.sum_prod_type _`.
-/
theorem hf_coord (T : Tor D) (z w : VC D N N') :
    JMB.hf (((area T.abelian₂ : ℂ))⁻¹ • (1 : Matrix (Fin (gDim D N N')) (Fin (gDim D N N')) ℂ))
      (coord D N N' z) (coord D N N' w) = Hf D T z w := by
  have h1 : ∀ u v : Fin (gDim D N N') → ℂ,
      JMB.hf (((area T.abelian₂ : ℂ))⁻¹ • (1 : Matrix (Fin (gDim D N N')) (Fin (gDim D N N')) ℂ)) u v
        = (∑ k, u k * starRingEnd ℂ (v k)) / (area T.abelian₂ : ℂ) := by
    intro u v
    simp only [JMB.hf, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, Hf]
  congr 1
  rw [← (Fintype.equivFin (Ix D N N')).sum_comp]
  simp only [coord_apply_equivFin]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun τ _ => Fintype.sum_prod_type _

def setup (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : JMB.Setup (gDim D N N') where
  d := D.host.d
  Hm := ((area (tor0 D cc δ).abelian₂ : ℂ))⁻¹ • 1
  La := (AddSubgroup.comap ((coordL D N N').symm.toAddEquiv.toAddMonoidHom) (La D (tor0 D cc δ) L L')).toIntSubmodule

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_setup {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (y : Fin (gDim D N N') → ℂ) :
    y ∈ (setup D cc δ N N' L L').La ↔ (coord D N N').symm y ∈ La D (tor0 D cc δ) L L' := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_setup, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem coord_mem_setup {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (x : VC D N N') :
    coord D N N' x ∈ (setup D cc δ N N' L L').La ↔ x ∈ La D (tor0 D cc δ) L L' := by
  rw [mem_setup, ContinuousLinearEquiv.symm_apply_apply]

end GlobalTheory.MomSetup

namespace GlobalTheory.MomSetup

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
The claim follows from `FL.embT_K D τ _ k.2`.
-/
theorem embT_Kc (τ : D.what₂.Tau) (k : D.host.K) : embT D τ (k : D.host.E) = D.host.φ₀ (k : D.host.E) :=
  FL.embT_K D τ _ k.2

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.
-/
theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j; simp [embV, tor0]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.
-/
theorem embV_add (A B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (A + B) = embV D (tor0 D cc δ) A + embV D (tor0 D cc δ) B := by
  funext τ i j; simp [embV, tor0]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.
-/
theorem embV_neg (A : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (-A) = -embV D (tor0 D cc δ) A := by
  funext τ i j; simp [embV, tor0]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0, embT_Kc]`.
-/
theorem embV_smulK (k : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) ((k : D.host.E) • A) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) A := by
  funext τ i j; simp [embV, tor0, embT_Kc]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.
-/
theorem embV_natsmul (s : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) ((s : D.host.E) • A) = (s : ℂ) • embV D (tor0 D cc δ) A := by
  funext τ i j; simp [embV, tor0]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0, embT_Kc, Finset.sum_apply, Matrix.sum_apply, map_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem embV_comb {r : ℕ} (k : Fin r → D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    δ • embV D (tor0 D cc δ) (∑ i, ((k i : D.host.K) : D.host.E) • b i)
      = ∑ i, D.host.φ₀ ((k i : D.host.K) : D.host.E) • (δ • embV D (tor0 D cc δ) (b i)) := by
  funext τ i j
  simp [embV, tor0, embT_Kc, Finset.sum_apply, Matrix.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Introduce `A B h`. Take `⟨τ⟩` from `(inferInstance : Nonempty D.what₂.Tau)`. Use function extensionality and compare the values at `i j`. Conclude with `(embT D τ).injective (congrFun (congrFun (congrFun h τ) i) j)`.
-/
theorem embV_injective [Nonempty D.what₂.Tau] :
    Function.Injective (embV D (tor0 D cc δ) : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  intro A B h
  obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
  funext i j
  exact (embT D τ).injective (congrFun (congrFun (congrFun h τ) i) j)

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨w, hw, A, hA, rfl⟩` from `hz`. Take `⟨c, hc, rfl⟩` from `FL.lam_mem D cc δ w hw`. Use `⟨(((c : D.host.K) : D.host.E)) • A, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (((c : D.host.K) : D.host.E)) • A = (⟨_, FL.intK D c⟩ : 𝓞 D.host.E) • A` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hA`. Rewrite using `[embV_smulK, smul_smul]`. Consider the case `zero => exact ⟨0, zero_mem _, by rw [embV_zero, smul_zero]⟩`.

Consider the case `add x y _ _ h1 h2`. Take `⟨A, hA, rfl⟩` from `h1`. Take `⟨B, hB, rfl⟩` from `h2`. Conclude with `⟨A + B, add_mem hA hB, by rw [embV_add, smul_add]⟩`. Consider the case `neg x _ h`.

Take `⟨A, hA, rfl⟩` from `h`. Conclude with `⟨-A, neg_mem hA, by rw [embV_neg, smul_neg]⟩`.
-/
theorem La_rep {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ A ∈ YYl D L L', x = δ • embV D (tor0 D cc δ) A := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D cc δ w hw
    refine ⟨(((c : D.host.K) : D.host.E)) • A, ?_, ?_⟩
    · have : (((c : D.host.K) : D.host.E)) • A = (⟨_, FL.intK D c⟩ : 𝓞 D.host.E) • A := rfl
      rw [this]; exact Submodule.smul_mem _ _ hA
    · rw [embV_smulK, smul_smul]
  | zero => exact ⟨0, zero_mem _, by rw [embV_zero, smul_zero]⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨A, hA, rfl⟩ := h1
    obtain ⟨B, hB, rfl⟩ := h2
    exact ⟨A + B, add_mem hA hB, by rw [embV_add, smul_add]⟩
  | neg x _ h =>
    obtain ⟨A, hA, rfl⟩ := h
    exact ⟨-A, neg_mem hA, by rw [embV_neg, smul_neg]⟩

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨w, hw, A, hA, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨_, GlobalTheory.FourthRootStd.lam_mul o hw, A, hA, by rw [smul_smul]⟩`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg x _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem La_smulK {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (o : 𝓞 D.host.K) {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    D.host.φ₀ ((o : D.host.K) : D.host.E) • x ∈ La D (tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨_, GlobalTheory.FourthRootStd.lam_mul o hw, A, hA, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.MomSetup

namespace GlobalTheory.MomSetup

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Conclude with `(IO.sqrt_d_pos D).ne'` after adjusting the coercions.
-/
theorem sqrt_ne : (Real.sqrt D.host.d : ℂ) ≠ 0 := by
  exact_mod_cast (IO.sqrt_d_pos D).ne'

/- English proof (translation)
Rewrite using `[((GlobalTheory.MomDict.main D).2.2.2.2 cc δ hcc.1).1]`. Establish `h1 : 0 < Complex.normSq δ` using `Complex.normSq_pos.mpr h0`. Establish `h2 : (0 : ℝ) < (Ideal.absNorm cc : ℝ)`. Establish `: Ideal.absNorm cc ≠ 0` using `by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions.

Establish `h3` using `IO.sqrt_d_pos D`. Check the signs of the components of the expression.
-/
theorem area_pos (hcc : IsCurveIdeal D cc) (h0 : δ ≠ 0) : 0 < area (lamOf D cc δ) := by
  rw [((GlobalTheory.MomDict.main D).2.2.2.2 cc δ hcc.1).1]
  have h1 : 0 < Complex.normSq δ := Complex.normSq_pos.mpr h0
  have h2 : (0 : ℝ) < (Ideal.absNorm cc : ℝ) := by
    have : Ideal.absNorm cc ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
    exact_mod_cast Nat.pos_of_ne_zero this
  have h3 := IO.sqrt_d_pos D
  positivity

/- English proof (translation)
Establish `h0 : δ ≠ 0` using `GlobalTheory.FourthRootStd.delta_ne_zero B`. Take `⟨hdp, hd16, hOK, -, -⟩` from `GlobalTheory.MomDict.main D`. Take `⟨hdisc, hspan⟩` from `FL.fullLat D L L' hA cc hcc δ h0`. Establish `hI` using `hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA`. Establish `hf' : ∀ u v : Fin (gDim D N N') → ℂ, JMB.hf (setup D cc δ N N' L L').Hm u v = Hf D (tor0 D cc δ) ((coord D N N').symm u) ((coord D N N').symm v)`.

Introduce `u v`. Use `hf_coord (N := N) (N' := N') (tor0 D cc δ) ((coord D N N').symm u) ((coord D N N').symm v)` as an intermediate fact. Simplify using `only [ContinuousLinearEquiv.apply_symm_apply] at this`. Conclude with `this`. Use `⟨hdp, hd16, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hpos` using `area_pos hcc h0`. Establish `ha : (0 : ℂ) < ((area (lamOf D cc δ) : ℂ))⁻¹`. Rewrite using `[← Complex.ofReal_inv]`. Conclude with `Complex.zero_lt_real.mpr (inv_pos.mpr hpos)`. Conclude with `Matrix.PosDef.one.smul ha`.

Establish `hc : Continuous fun y : (setup D cc δ N N' L L').La => (⟨(coord D N N').symm y, y.2⟩ : La D (tor0 D cc δ) L L')` using `Continuous.subtype_mk ((coord D N N').symm.continuous.comp continuous_subtype_val) _`. Use `DiscreteTopology.of_continuous_injective hc ?_` and prove the remaining obligations. Introduce `y y' h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val h` as an intermediate fact.

Conclude with `(coord D N N').symm.injective this`. Use `set f : VC D N N' →ₗ[ℝ] (Fin (gDim D N N') → ℂ) := (coord D N N').toLinearEquiv.toLinearMap.restrictScalars ℝ`. Establish `hset : ((setup D cc δ N N' L L').La : Set (Fin (gDim D N N') → ℂ)) = f '' (La D (tor0 D cc δ) L L' : Set (VC D N N'))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `⟨(coord D N N').symm y, hy, by simp [f]⟩`. Introduce and unpack `⟨x, hx, rfl⟩ show (coord D N N').symm (coord D N N' x) ∈ La D (tor0 D cc δ) L L'`. Simplify using `using hx`. Rewrite using `[hset, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`.

Introduce `y`. Conclude with `⟨(coord D N N').symm y, by simp [f]⟩`. Introduce `x hx`. Take `⟨o, ho⟩` from `(hOK (GlobalTheory.MomOne.wK D.host.d)).1 ⟨0, 1, by simp⟩`. Establish `hw : JMB.w0 D.host.d = GlobalTheory.MomOne.wK D.host.d` using `rfl`.

Use `show (coord D N N').symm (JMB.w0 D.host.d • x) ∈ La D (tor0 D cc δ) L L'`. Rewrite using `[map_smul, hw, ho]`. Conclude with `La_smulK o hx`. Introduce `x hx y hy`. Take `⟨a, b, hab, he⟩` from `hI _ ((mem_setup x).1 hx) _ ((mem_setup y).1 hy)`.

Take `⟨r, hr⟩` from `hab`. Use `show ((Real.sqrt (D.host.d : ℝ) / 2 : ℝ) : ℂ) * JMB.hf (setup D cc δ N N' L L').Hm x y ∈ JMB.OK D.host.d`. Rewrite using `[hf', he]`. Use `⟨r, b, ?_⟩` and prove the remaining obligations. Establish `hs` using `sqrt_ne (D := D)`.

Establish `ha : (a : ℂ) = 2 * r + b`. Establish `: a = 2 * r + b` using `by omega`. Conclude with `this` after adjusting the coercions. Simplify using `only [JMB.w0, JMB.rtd]`. Use `push_cast`.

Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `y hy`. Use `show (coord D N N').symm y ∈ La D (tor0 D cc δ) L L'`.

Use `self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA _ fun y' hy' => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `hy (coord D N N' y') ((coord_mem_setup y').2 hy')`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[hf', ContinuousLinearEquiv.symm_apply_apply]`. Rewrite using `[IO.Hf_herm (tor0 D cc δ) y' ((coord D N N').symm y), Complex.conj_im, hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem setup_ok (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L') : (setup D cc δ N N' L L').Ok := by
  have h0 : δ ≠ 0 := GlobalTheory.FourthRootStd.delta_ne_zero B
  obtain ⟨hdp, hd16, hOK, -, -⟩ := GlobalTheory.MomDict.main D
  obtain ⟨hdisc, hspan⟩ := FL.fullLat D L L' hA cc hcc δ h0
  have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
  have hf' : ∀ u v : Fin (gDim D N N') → ℂ, JMB.hf (setup D cc δ N N' L L').Hm u v
      = Hf D (tor0 D cc δ) ((coord D N N').symm u) ((coord D N N').symm v) := by
    intro u v
    have := hf_coord (N := N) (N' := N') (tor0 D cc δ) ((coord D N N').symm u) ((coord D N N').symm v)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  refine ⟨hdp, hd16, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hpos := area_pos hcc h0
    have ha : (0 : ℂ) < ((area (lamOf D cc δ) : ℂ))⁻¹ := by
      rw [← Complex.ofReal_inv]; exact Complex.zero_lt_real.mpr (inv_pos.mpr hpos)
    exact Matrix.PosDef.one.smul ha
  ·
    have hc : Continuous fun y : (setup D cc δ N N' L L').La =>
        (⟨(coord D N N').symm y, y.2⟩ : La D (tor0 D cc δ) L L') :=
      Continuous.subtype_mk ((coord D N N').symm.continuous.comp continuous_subtype_val) _
    refine DiscreteTopology.of_continuous_injective hc ?_
    intro y y' h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact (coord D N N').symm.injective this
  ·
    set f : VC D N N' →ₗ[ℝ] (Fin (gDim D N N') → ℂ) :=
      (coord D N N').toLinearEquiv.toLinearMap.restrictScalars ℝ
    have hset : ((setup D cc δ N N' L L').La : Set (Fin (gDim D N N') → ℂ))
        = f '' (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
      ext y
      constructor
      · intro hy
        exact ⟨(coord D N N').symm y, hy, by simp [f]⟩
      · rintro ⟨x, hx, rfl⟩
        show (coord D N N').symm (coord D N N' x) ∈ La D (tor0 D cc δ) L L'
        simpa using hx
    rw [hset, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    intro y
    exact ⟨(coord D N N').symm y, by simp [f]⟩
  ·
    intro x hx
    obtain ⟨o, ho⟩ := (hOK (GlobalTheory.MomOne.wK D.host.d)).1 ⟨0, 1, by simp⟩
    have hw : JMB.w0 D.host.d = GlobalTheory.MomOne.wK D.host.d := rfl
    show (coord D N N').symm (JMB.w0 D.host.d • x) ∈ La D (tor0 D cc δ) L L'
    rw [map_smul, hw, ho]
    exact La_smulK o hx
  ·
    intro x hx y hy
    obtain ⟨a, b, hab, he⟩ := hI _ ((mem_setup x).1 hx) _ ((mem_setup y).1 hy)
    obtain ⟨r, hr⟩ := hab
    show ((Real.sqrt (D.host.d : ℝ) / 2 : ℝ) : ℂ) * JMB.hf (setup D cc δ N N' L L').Hm x y ∈ JMB.OK D.host.d
    rw [hf', he]
    refine ⟨r, b, ?_⟩
    have hs := sqrt_ne (D := D)
    have ha : (a : ℂ) = 2 * r + b := by
      have : a = 2 * r + b := by omega
      exact_mod_cast this
    simp only [JMB.w0, JMB.rtd]
    push_cast
    rw [ha]
    field_simp
    ring
  ·
    intro y hy
    show (coord D N N').symm y ∈ La D (tor0 D cc δ) L L'
    refine self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA _ fun y' hy' => ?_
    obtain ⟨k, hk⟩ := hy (coord D N N' y') ((coord_mem_setup y').2 hy')
    refine ⟨-k, ?_⟩
    rw [hf', ContinuousLinearEquiv.symm_apply_apply] at hk
    rw [IO.Hf_herm (tor0 D cc δ) y' ((coord D N N').symm y), Complex.conj_im, hk]
    push_cast; ring

end GlobalTheory.MomSetup

namespace GlobalTheory.MomSetup

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

/- English proof (translation)
Introduce `D cc δ B hcc hδ N N' L L' hA`. Establish `h0 : δ ≠ 0` using `GlobalTheory.FourthRootStd.delta_ne_zero B`. Take `⟨-, -, hOK, -, harea⟩` from `GlobalTheory.MomDict.main D`. Establish `hN : (Ideal.absNorm cc : ℂ) ≠ 0`. Establish `: Ideal.absNorm cc ≠ 0` using `by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1`.

Conclude with `this` after adjusting the coercions. Use `haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩`. Use `⟨gDim D N N', setup D cc δ N N' L L', coord D N N', rfl, setup_ok B hcc hδ hA, fun x => coord_mem_setup x, fun x y => hf_coord _ x y, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Use `show ((Real.sqrt (D.host.d : ℝ) / 2 : ℝ) : ℂ) * JMB.hf (((area (tor0 D cc δ).abelian₂ : ℂ))⁻¹ • 1) _ _ = _`.

Rewrite using `[hf_coord, IO.Hf_smul, FL.Hf_embV D (tor0 D cc δ) (fun _ _ => rfl)]`. Use `show _ * (_ * _ * (_ / ((area (lamOf D cc δ) : ℝ) : ℂ))) = _`. Rewrite using `[(harea cc δ hcc.1).1, Complex.mul_conj]`. Establish `hs` using `sqrt_ne (D := D)`. Establish `hδ2 : (Complex.normSq δ : ℂ) ≠ 0` using `by exact_mod_cast (Complex.normSq_pos.mpr h0).ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `x hx`. Take `⟨A, hA', rfl⟩` from `La_rep hx`. Conclude with `⟨1, A, one_pos, rfl, by simpa using hA'⟩`.

Introduce `q r b _ hb`. Take `⟨⟨hli, -, hspanb⟩, hbL⟩` from `hb`. Use `⟨fun i => (coord_mem_setup _).2 (hbL i), ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨A, hA', hAe⟩` from `La_rep ((mem_setup y).1 hy)`.

Take `⟨s, hs, c, hc⟩` from `hspanb A hA'`. Use `⟨s, hs, fun i => D.host.φ₀ (((c i : 𝓞 D.host.K) : D.host.K) : D.host.E), fun i => (hOK _).2 ⟨c i, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : y = coord D N N' (δ • embV D (tor0 D cc δ) A)`. Rewrite using `[← hAe, ContinuousLinearEquiv.apply_symm_apply]`. Establish `e2 : (s : ℂ) • (δ • embV D (tor0 D cc δ) A) = δ • embV D (tor0 D cc δ) ((s : D.host.E) • A)`.

Rewrite using `[embV_natsmul, smul_comm]`. Rewrite using `[e1, ← map_smul, e2, hc, embV_comb, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul]`. Introduce `c hc hsum i choose k hk using fun i => (hOK (c i)).1 (hc i)`. Establish `e1 : ∑ i, c i • coord D N N' (δ • embV D (tor0 D cc δ) (b i)) = coord D N N' (δ • embV D (tor0 D cc δ) (∑ i, (((k i : 𝓞 D.host.K) : D.host.K) : D.host.E) • b i))`.

Rewrite using `[embV_comb, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hk]; exact ((coord D N N').map_smul _ _).symm`. Establish `hsum' : coord D N N' (δ • embV D (tor0 D cc δ) (∑ i, (((k i : 𝓞 D.host.K) : D.host.K) : D.host.E) • b i)) = 0`. Rewrite using `[← e1]`. Conclude with `hsum`.

Rewrite `hsum'` using `[map_eq_zero_iff _ (coord D N N').injective, smul_eq_zero]`. Establish `hM : (∑ i, (((k i : 𝓞 D.host.K) : D.host.K) : D.host.E) • b i) = 0`. Break down `hsum' with h | h` into its components or cases. Conclude with `absurd h h0`. Conclude with `embV_injective (cc := cc) (δ := δ) (by rw [h, embV_zero])`.

Establish `hK : ∑ i, ((k i : 𝓞 D.host.K) : D.host.K) • b i = 0`. Rewrite using `[← hM]`. Conclude with `Finset.sum_congr rfl fun i _ => (algebraMap_smul D.host.E _ (b i)).symm`. Use `Fintype.linearIndependent_iff.1 hli _ hK i` as an intermediate fact. Rewrite using `[hk i, this]`.

Simplify using the standard rewrite rules.
-/
theorem periodSetup : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∃ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d ∧ S.Ok ∧ (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') ∧ (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) ∧ (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) ∧ (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') ∧ ∀ (q r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Nat.Coprime (Ideal.absNorm cc) q → NNBasis D B.tor δ q L L' b → JMB.Setup.NNBasis S q fun i => e (δ • embV D B.tor (b i)) := by
  intro D cc δ B hcc hδ N N' L L' hA
  have h0 : δ ≠ 0 := GlobalTheory.FourthRootStd.delta_ne_zero B
  obtain ⟨-, -, hOK, -, harea⟩ := GlobalTheory.MomDict.main D
  have hN : (Ideal.absNorm cc : ℂ) ≠ 0 := by
    have : Ideal.absNorm cc ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
    exact_mod_cast this
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine ⟨gDim D N N', setup D cc δ N N' L L', coord D N N', rfl, setup_ok B hcc hδ hA,
    fun x => coord_mem_setup x, fun x y => hf_coord _ x y, ?_, ?_, ?_⟩
  ·
    intro x y
    show ((Real.sqrt (D.host.d : ℝ) / 2 : ℝ) : ℂ) * JMB.hf (((area (tor0 D cc δ).abelian₂ : ℂ))⁻¹ • 1) _ _ = _
    rw [hf_coord, IO.Hf_smul, FL.Hf_embV D (tor0 D cc δ) (fun _ _ => rfl)]
    show _ * (_ * _ * (_ / ((area (lamOf D cc δ) : ℝ) : ℂ))) = _
    rw [(harea cc δ hcc.1).1, Complex.mul_conj]
    have hs := sqrt_ne (D := D)
    have hδ2 : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.mpr h0).ne'
    push_cast
    field_simp
  ·
    intro x hx
    obtain ⟨A, hA', rfl⟩ := La_rep hx
    exact ⟨1, A, one_pos, rfl, by simpa using hA'⟩
  ·
    intro q r b _ hb
    obtain ⟨⟨hli, -, hspanb⟩, hbL⟩ := hb
    refine ⟨fun i => (coord_mem_setup _).2 (hbL i), ?_, ?_⟩
    · intro y hy
      obtain ⟨A, hA', hAe⟩ := La_rep ((mem_setup y).1 hy)
      obtain ⟨s, hs, c, hc⟩ := hspanb A hA'
      refine ⟨s, hs, fun i => D.host.φ₀ (((c i : 𝓞 D.host.K) : D.host.K) : D.host.E),
        fun i => (hOK _).2 ⟨c i, rfl⟩, ?_⟩
      have e1 : y = coord D N N' (δ • embV D (tor0 D cc δ) A) := by
        rw [← hAe, ContinuousLinearEquiv.apply_symm_apply]
      have e2 : (s : ℂ) • (δ • embV D (tor0 D cc δ) A) = δ • embV D (tor0 D cc δ) ((s : D.host.E) • A) := by
        rw [embV_natsmul, smul_comm]
      rw [e1, ← map_smul, e2, hc, embV_comb, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    · intro c hc hsum i
      choose k hk using fun i => (hOK (c i)).1 (hc i)
      have e1 : ∑ i, c i • coord D N N' (δ • embV D (tor0 D cc δ) (b i))
          = coord D N N' (δ • embV D (tor0 D cc δ) (∑ i, (((k i : 𝓞 D.host.K) : D.host.K) : D.host.E) • b i)) := by
        rw [embV_comb, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hk]; exact ((coord D N N').map_smul _ _).symm
      have hsum' : coord D N N' (δ • embV D (tor0 D cc δ) (∑ i, (((k i : 𝓞 D.host.K) : D.host.K) : D.host.E) • b i)) = 0 := by
        rw [← e1]; exact hsum
      rw [map_eq_zero_iff _ (coord D N N').injective, smul_eq_zero] at hsum'
      have hM : (∑ i, (((k i : 𝓞 D.host.K) : D.host.K) : D.host.E) • b i) = 0 := by
        rcases hsum' with h | h
        · exact absurd h h0
        · exact embV_injective (cc := cc) (δ := δ) (by rw [h, embV_zero])
      have hK : ∑ i, ((k i : 𝓞 D.host.K) : D.host.K) • b i = 0 := by
        rw [← hM]
        exact Finset.sum_congr rfl fun i _ => (algebraMap_smul D.host.E _ (b i)).symm
      have := Fintype.linearIndependent_iff.1 hli _ hK i
      rw [hk i, this]
      simp

end GlobalTheory.MomSetup
