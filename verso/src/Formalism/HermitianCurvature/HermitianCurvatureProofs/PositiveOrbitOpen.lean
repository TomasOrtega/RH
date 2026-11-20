import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section local_

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `x hx hxG`. Establish `hγ` using `Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt x X 0`. Establish `hγ0 : x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = x` using `by simp`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp ((t : ℂ) • X) ∈ V` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hx)`. Use `show deriv (fun t : ℝ => f₁ (x * NormedSpace.exp ((t : ℂ) • X))) 0 = deriv (fun t : ℝ => f₂ (x * NormedSpace.exp ((t : ℂ) • X))) 0`.

Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Use `filter_upwards [hmem] with t ht`. Conclude with `h _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)`.
-/
theorem rdV_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) {X : Mat k r} (hX : inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → RdV X f₁ x = RdV X f₂ x := by
  intro x hx hxG
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt x X 0
  have hγ0 : x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = x := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp ((t : ℂ) • X) ∈ V :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hx)
  show deriv (fun t : ℝ => f₁ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h`. Consider the case `cons X w ih`. Introduce `x hx hxG`. Conclude with `rdV_local hV (ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY))) (hw X (by simp)) x hx hxG`.
-/
theorem rw_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → Rw w f₁ x = Rw w f₂ x := by
  induction w with
  | nil => exact h
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local hV (ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY))) (hw X (by simp)) x hx hxG

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons X w ih => show RdV X (Rw w (c • f)) = c • RdV X (Rw w f)`. Rewrite using `[ih]`. Use function extensionality and compare the values at `g`.

Simplify using `only [RdV, Pi.smul_apply]`. Conclude with `deriv_const_smul' (f := fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) c`.
-/
theorem rw_smul (w : List (Mat k r)) (c : ℂ) (f : Mat k r → E) : Rw w (c • f) = c • Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (Rw w (c • f)) = c • RdV X (Rw w f)
    rw [ih]
    funext g
    simp only [RdV, Pi.smul_apply]
    exact deriv_const_smul' (f := fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) c

end local_

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Introduce `x hx hxG`. Unfold `opApply`. Use `congr 1`. Use `List.map_congr_left fun T _ => ?_` and prove the remaining obligations. Rewrite using `[rw_local hV h T.word T.word_lie x hx hxG]`.
-/
theorem op_local (Θ : DiffOp k r Wp Wq) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) : ∀ x ∈ V, x ∈ GV k r → opApply Θ f₁ x = opApply Θ f₂ x := by
  intro x hx hxG
  unfold opApply
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_local hV h T.word T.word_lie x hx hxG]

/- English proof (translation)
Unfold `opApply`. Rewrite using `[WordIntegralScaling.smul_list]`. Use `congr 1`. Use `List.map_congr_left fun T _ => ?_` and prove the remaining obligations. Rewrite using `[rw_smul, Pi.smul_apply]`.
-/
theorem op_smul (Θ : DiffOp k r Wp Wq) (c : ℂ) (f : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    opApply Θ (c • f) x = c • opApply Θ f x := by
  unfold opApply
  rw [WordIntegralScaling.smul_list]
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_smul, Pi.smul_apply]

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Unfold `Zhat herm`. Conclude with `continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))`.
-/
theorem zhat_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Zhat k r z z' g) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold Zhat herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold `Dmin`. Conclude with `((zhat_cont z z').matrix_submatrix _ _).matrix_det`.
-/
theorem dmin_cont (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Continuous (fun g : Mat k r => Dmin k r z z' g l) := by
  unfold Dmin
  exact ((zhat_cont z z').matrix_submatrix _ _).matrix_det

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold `Gf`. Conclude with `(Complex.continuous_normSq.comp (dmin_cont z z' _)).sub (continuous_const.mul (Complex.continuous_normSq.comp (dmin_cont z z' _)))`.
-/
theorem gf_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Gf k r z z' g) := by
  unfold Gf
  exact (Complex.continuous_normSq.comp (dmin_cont z z' _)).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (dmin_cont z z' _)))

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g hg`. Establish `h1 : ∀ᶠ x in 𝓝 g, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' x l ≠ 0`. Use `Filter.eventually_all.2 fun l => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l.val ≤ r`.

Use `filter_upwards [(dmin_cont z z' l).continuousAt.eventually_ne (hg.1 l hl)] with x hx`. Conclude with `fun _ => hx`. Conclude with `Filter.Eventually.of_forall fun x h => absurd h hl`. Establish `h2 : ∀ᶠ x in 𝓝 g, 0 < Gf k r z z' x` using `continuousAt_const.eventually_lt (gf_cont z z').continuousAt hg.2`. Use `filter_upwards [h1, h2] with x hx1 hx2`.

Conclude with `⟨hx1, hx2⟩`.
-/
theorem omPlus_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Q.OmPlus k r z z') := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h1 : ∀ᶠ x in 𝓝 g, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' x l ≠ 0 := by
    refine Filter.eventually_all.2 fun l => ?_
    by_cases hl : l.val ≤ r
    · filter_upwards [(dmin_cont z z' l).continuousAt.eventually_ne (hg.1 l hl)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hl
  have h2 : ∀ᶠ x in 𝓝 g, 0 < Gf k r z z' x := continuousAt_const.eventually_lt (gf_cont z z').continuousAt hg.2
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hp`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_inv_rev]`. Conclude with `⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩`. Conclude with `(sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, BigCellZetaMinors.one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _ ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩`.
-/
theorem sgs_S (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z ∧
      (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  · exact (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, BigCellZetaMinors.one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Rewrite using `[B5.sgs_eq]`. Conclude with `WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B5.inSS_left D hp)) hy) (B5.inSS_right D hp)`.
-/
theorem sgs_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ GV k r) :
    sgs p y ∈ GV k r := by
  rw [B5.sgs_eq]
  exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B5.inSS_left D hp)) hy) (B5.inSS_right D hp)

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Use `⟨sgs_GV D hp hy.1, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[BigCellZetaMinors.dmin_sgs D hp]`. Conclude with `hy.2.1 l hl`. Take `⟨hs, hs'⟩` from `sgs_S D hp show 0 < Gf k r D.z D.z' (sgs p y)`. Rewrite using `[B5.sgs_eq, gInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' y]`.

Conclude with `hy.2.2`.
-/
theorem sgs_Om (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ Om k r D.z D.z') :
    sgs p y ∈ Om k r D.z D.z' := by
  refine ⟨sgs_GV D hp hy.1, fun l hl => ?_, ?_⟩
  · rw [BigCellZetaMinors.dmin_sgs D hp]; exact hy.2.1 l hl
  · obtain ⟨hs, hs'⟩ := sgs_S D hp
    show 0 < Gf k r D.z D.z' (sgs p y)
    rw [B5.sgs_eq, gInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' y]
    exact hy.2.2

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold `sgs`. Conclude with `((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul continuous_const`.
-/
theorem sgs_cont (p : SS k r) : Continuous (fun y : Mat k r => sgs p y) := by
  unfold sgs
  exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul continuous_const

end Formalism.FourierDecayAlt.P.PositiveOrbitOpen

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ D Θ f hC hf hE p hp g hg`. Establish `hx₀ : sgs p g ∈ Om k r D.z D.z'` using `PositiveOrbitOpen.sgs_Om D hp hg`. Take `⟨U, F', hU, hx₀U, hF', hfe⟩` from `hf (sgs p g) ⟨WordKeyIdentity.glev0 hx₀.1, hx₀.2⟩`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hU (sgs p g) hx₀U`. Set `b : ContDiffBump (sgs p g)` to `⟨ε / 4, ε / 2, by positivity, by linarith⟩`.

Set `ft : Mat k r → (Wq →L[ℂ] Wp)` to `fun y => b y • F' y`. Establish `hft : ContDiff ℝ ((opOrder Θ : ℕ∞) : WithTop ℕ∞) ft`. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `y`. Distinguish the cases in `hy : y ∈ Metric.ball (sgs p g) ε`.

Conclude with `b.contDiff.contDiffAt.smul (hF'.contDiffAt (hU.mem_nhds (hball hy)))`. Establish `hy' : y ∈ (Metric.closedBall (sgs p g) (ε / 2))ᶜ`. Rewrite `hy` using `[Metric.mem_ball, not_lt]`. Simplify using `only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `he : ft =ᶠ[𝓝 y] fun _ => 0` using `by filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy'] with w hw`. Establish `: b w = 0`. Apply `b.zero_of_le_dist` to reduce the goal to its premises. Simplify using `only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hw`. Conclude with `hw.le`.

Use `show b w • F' w = 0`. Rewrite using `[this, zero_smul]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq he`. Establish `hftCk : CkOn (opOrder Θ : ℕ∞) (GV k r) ft` using `fun _ _ => ⟨Set.univ, ft, isOpen_univ, trivial, hft.contDiffOn, fun _ _ _ => rfl⟩`. Establish `hagree : ∀ y ∈ Metric.ball (sgs p g) (ε / 4), y ∈ GV k r → ft y = f y`.

Introduce `y hy hyG`. Establish `h1 : b y = 1` using `b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)`. Use `show b y • F' y = f y`. Rewrite using `[h1, one_smul, hfe y (hball (Metric.ball_subset_ball (by linarith) hy)) (WordKeyIdentity.glev0 hyG)]`. Establish `hε4 : 0 < ε / 4` using `by positivity`.

Establish `s5 : opApply Θ ft (sgs p g) = opApply Θ f (sgs p g)` using `PositiveOrbitOpen.op_local Θ Metric.isOpen_ball hagree _ (Metric.mem_ball_self hε4) hx₀.1`. Establish `s3 : opApply Θ (rho D p f) g = opApply Θ (rho D p ft) g`. Use `PositiveOrbitOpen.op_local Θ (Metric.isOpen_ball.preimage (PositiveOrbitOpen.sgs_cont p)) (fun y hy hyG => ?_) g (Set.mem_preimage.2 (Metric.mem_ball_self hε4)) hg.1` and prove the remaining obligations. Establish `hy' : sgs p y ∈ Metric.ball (sgs p g) (ε / 4)` using `hy`. Unfold `rho`.

Rewrite using `[hagree _ hy' (PositiveOrbitOpen.sgs_GV D hp hyG)]`. Establish `s1 : opApply Θ f g = opApply Θ (xiP D p • rho D p f) g` using `PositiveOrbitOpen.op_local Θ (PositiveOrbitOpen.omPlus_open D.z D.z') (fun y hy hyG => (hE p hp y ⟨hyG, hy⟩).symm) g hg.2 hg.1`. Rewrite using `[s1, PositiveOrbitOpen.op_smul, s3, hC p hp ft hftCk g hg]`. Unfold `rho`. Rewrite using `[s5]`.
-/
theorem theta_equivariant : Formalism.FourierDecayAlt.JF.ThetaEquiv := by
  intro k r Wp Wq _ _ _ _ _ D Θ f hC hf hE p hp g hg
  have hx₀ : sgs p g ∈ Om k r D.z D.z' := PositiveOrbitOpen.sgs_Om D hp hg
  obtain ⟨U, F', hU, hx₀U, hF', hfe⟩ := hf (sgs p g) ⟨WordKeyIdentity.glev0 hx₀.1, hx₀.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (sgs p g) hx₀U
  let b : ContDiffBump (sgs p g) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let ft : Mat k r → (Wq →L[ℂ] Wp) := fun y => b y • F' y
  have hft : ContDiff ℝ ((opOrder Θ : ℕ∞) : WithTop ℕ∞) ft := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Metric.ball (sgs p g) ε
    · exact b.contDiff.contDiffAt.smul (hF'.contDiffAt (hU.mem_nhds (hball hy)))
    · have hy' : y ∈ (Metric.closedBall (sgs p g) (ε / 2))ᶜ := by
        rw [Metric.mem_ball, not_lt] at hy
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
        linarith
      have he : ft =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy'] with w hw
        have : b w = 0 := by
          apply b.zero_of_le_dist
          simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hw
          exact hw.le
        show b w • F' w = 0
        rw [this, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hftCk : CkOn (opOrder Θ : ℕ∞) (GV k r) ft :=
    fun _ _ => ⟨Set.univ, ft, isOpen_univ, trivial, hft.contDiffOn, fun _ _ _ => rfl⟩
  have hagree : ∀ y ∈ Metric.ball (sgs p g) (ε / 4), y ∈ GV k r → ft y = f y := by
    intro y hy hyG
    have h1 : b y = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show b y • F' y = f y
    rw [h1, one_smul, hfe y (hball (Metric.ball_subset_ball (by linarith) hy)) (WordKeyIdentity.glev0 hyG)]
  have hε4 : 0 < ε / 4 := by positivity
  have s5 : opApply Θ ft (sgs p g) = opApply Θ f (sgs p g) :=
    PositiveOrbitOpen.op_local Θ Metric.isOpen_ball hagree _ (Metric.mem_ball_self hε4) hx₀.1
  have s3 : opApply Θ (rho D p f) g = opApply Θ (rho D p ft) g := by
    refine PositiveOrbitOpen.op_local Θ (Metric.isOpen_ball.preimage (PositiveOrbitOpen.sgs_cont p)) (fun y hy hyG => ?_) g
      (Set.mem_preimage.2 (Metric.mem_ball_self hε4)) hg.1
    have hy' : sgs p y ∈ Metric.ball (sgs p g) (ε / 4) := hy
    unfold rho
    rw [hagree _ hy' (PositiveOrbitOpen.sgs_GV D hp hyG)]
  have s1 : opApply Θ f g = opApply Θ (xiP D p • rho D p f) g :=
    PositiveOrbitOpen.op_local Θ (PositiveOrbitOpen.omPlus_open D.z D.z') (fun y hy hyG => (hE p hp y ⟨hyG, hy⟩).symm) g hg.2 hg.1
  rw [s1, PositiveOrbitOpen.op_smul, s3, hC p hp ft hftCk g hg]
  unfold rho
  rw [s5]

end Formalism.FourierDecayAlt.P
