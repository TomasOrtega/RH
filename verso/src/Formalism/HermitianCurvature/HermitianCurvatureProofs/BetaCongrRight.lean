import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section comp

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

/- English proof (translation)
Take `⟨U, f', hU, hgU, hc, hff⟩` from `hG g hg`. Establish `hc0 : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U` using `by simpa using hc`. Establish `e1` using `P.B4.op_eq_op' 0 b hU hc0 hff hX g hgU hg`. Set `pr : (ι → E) →L[ℝ] E` to `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ`. Establish `hc' : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) (fun h => f' h i) U` using `pr.contDiff.comp_contDiffOn hc0`.

Establish `hff' : ∀ h ∈ U, h ∈ GV k r → (fun h => G h i) h = (fun h => f' h i) h` using `fun h hU' hG' => by`. Simplify using `only [hff h hU' hG']`. Establish `e2` using `P.B4.op_eq_op' 0 b hU hc' hff' hX g hgU hg`. Rewrite using `[e2, e1]`. Unfold `P.B4.op'`.

Establish `hd : DifferentiableAt ℝ f' g` using `(hc0.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Establish `hfd : HasFDerivAt (fun h => f' h i) (pr.comp (fderiv ℝ f' g)) g` using `pr.hasFDerivAt.comp g hd.hasFDerivAt`. Rewrite using `[hfd.fderiv]`. Both sides reduce to the same expression.
-/
theorem op_comp (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → (ι → E)}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) (i : ι) {g : Mat k r} (hg : g ∈ GV k r) :
    P.B4.op b X (fun h => G h i) g = P.B4.op b X G g i := by
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g hg
  have hc0 : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U := by simpa using hc
  have e1 := P.B4.op_eq_op' 0 b hU hc0 hff hX g hgU hg
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  have hc' : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) (fun h => f' h i) U :=
    pr.contDiff.comp_contDiffOn hc0
  have hff' : ∀ h ∈ U, h ∈ GV k r → (fun h => G h i) h = (fun h => f' h i) h := fun h hU' hG' => by
    simp only [hff h hU' hG']
  have e2 := P.B4.op_eq_op' 0 b hU hc' hff' hX g hgU hg
  rw [e2, e1]
  unfold P.B4.op'
  have hd : DifferentiableAt ℝ f' g :=
    (hc0.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hfd : HasFDerivAt (fun h => f' h i) (pr.comp (fderiv ℝ f' g)) g :=
    pr.hasFDerivAt.comp g hd.hasFDerivAt
  rw [hfd.fderiv]
  rfl

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro g _`. Both sides reduce to the same expression. Consider the case `cons x w ih`. Introduce `g hg`.

Establish `hw' : P.B4.AllLie w` using `fun y hy => hw y (List.mem_cons_of_mem _ hy)`. Establish `hl : w.length ≤ (x :: w).length` using `by simp`. Establish `hl1 : 1 + w.length ≤ (x :: w).length` using `by simp; omega`. Rewrite using `[P.B4.W_cons, P.B4.W_cons, P.B4.op_congr x.1 (hw x List.mem_cons_self) (ih hw' (P.B4.ckOn_mono hl hG)) g hg]`. Conclude with `op_comp x.1 (hw x List.mem_cons_self) (P.B4.smooth_on_of_word_derivatives w hw' 1 (P.B4.ckOn_mono hl1 hG)) i hg`.
-/
theorem W_comp (w : List (Bool × Mat k r)) (hw : P.B4.AllLie w) {G : Mat k r → (ι → E)}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) (i : ι) :
    ∀ g ∈ GV k r, P.B4.W w (fun h => G h i) g = P.B4.W w G g i := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hl : w.length ≤ (x :: w).length := by simp
    have hl1 : 1 + w.length ≤ (x :: w).length := by simp; omega
    rw [P.B4.W_cons, P.B4.W_cons,
      P.B4.op_congr x.1 (hw x List.mem_cons_self) (ih hw' (P.B4.ckOn_mono hl hG)) g hg]
    exact op_comp x.1 (hw x List.mem_cons_self) (P.B4.smooth_on_of_word_derivatives w hw' 1 (P.B4.ckOn_mono hl1 hG)) i hg

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hc, hff⟩` from `hG g₀ hg₀`. Set `pr : (ι → E) →L[ℝ] E` to `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ`. Conclude with `⟨U, fun h => f' h i, hU, hgU, pr.contDiff.comp_contDiffOn hc, fun g hg hgG => by simp only [hff g hg hgG]⟩`.
-/
theorem ckOn_comp {m : ℕ∞} {G : Mat k r → (ι → E)} (hG : CkOn m (GV k r) G) (i : ι) :
    CkOn m (GV k r) (fun h => G h i) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g₀ hg₀
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  exact ⟨U, fun h => f' h i, hU, hgU, pr.contDiff.comp_contDiffOn hc, fun g hg hgG => by simp only [hff g hg hgG]⟩

/- English proof (translation)
Use `⟨ckOn_comp hG.1 i, fun u v hu hv hl g hg => ?_⟩` and prove the remaining obligations. Establish `hw : P.B4.AllLie (P.B4.lr u v)`. Introduce `x hx`. Simplify using `only [P.B4.lr, List.mem_append, List.mem_map] at hx`. Break down `hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩` into its components or cases.

Conclude with `(hu X hX).1`. Conclude with `(hv X hX).1`. Establish `hlen : (P.B4.lr u v).length ≤ m` using `by simp [P.B4.lr]; omega`. Establish `e : dLR u v (fun h => G h i) g = dLR u v G g i`. Rewrite using `[P.B4.dLR_eq, P.B4.dLR_eq]`.

Conclude with `W_comp _ hw (P.B4.ckOn_mono hlen hG.1) i g hg`. Rewrite using `[e]`. Use `le_trans ?_ (hG.2 u v hu hv hl g hg)` and prove the remaining obligations. Establish `hgN : 0 ≤ gN g ^ A` using `Real.rpow_nonneg (Real.sqrt_nonneg _) A`. Conclude with `mul_le_mul_of_nonneg_left (norm_le_pi_norm (dLR u v G g) i) hgN`.
-/
theorem ccle_comp {A c : ℝ} {m : ℕ} {G : Mat k r → (ι → E)} (hG : CCle A m G c) (i : ι) :
    CCle A m (fun h => G h i) c := by
  refine ⟨ckOn_comp hG.1 i, fun u v hu hv hl g hg => ?_⟩
  have hw : P.B4.AllLie (P.B4.lr u v) := by
    intro x hx
    simp only [P.B4.lr, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  have hlen : (P.B4.lr u v).length ≤ m := by simp [P.B4.lr]; omega
  have e : dLR u v (fun h => G h i) g = dLR u v G g i := by
    rw [P.B4.dLR_eq, P.B4.dLR_eq]
    exact W_comp _ hw (P.B4.ckOn_mono hlen hG.1) i g hg
  rw [e]
  refine le_trans ?_ (hG.2 u v hu hv hl g hg)
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (dLR u v G g) i) hgN

end comp

section beta

open Formalism.FourierDecayAlt.P.JCx2 Filter

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `B.beta betaBig`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq`. Distinguish the cases in `hQ : q ∈ B.Qset D`. Establish `hg : bigCell k r q.1 (D.μsec q.2) ∈ GV k r` using `(hq hQ).1 show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2)))) (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2)))) (h …`.

Rewrite using `[sq_jf_congr D h hg]`. Establish `hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0` using `le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q) show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _`. Rewrite using `[hw]`. Simplify using the standard rewrite rules.
-/
theorem beta_congr_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, G g = G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [sq_jf_congr D h hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end beta

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P0 T sg j w a mm ε' Sg hε' ha hmm hmm5 hSg V _ _ Mo`. Set `comp : V → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)` to `fun u e γ => Mo.ev u γ e`. Establish `hcc : ∀ u e, CCle a mm (comp u e) ‖u‖` using `fun u e => FormNormSumIdentities.ccle_comp (Mo.mem u) e`. Establish `hin : ∀ u e, InCC a mm (comp u e)` using `fun u e => ⟨_, hcc u e⟩`. Establish `hadd : ∀ u u', comp (u + u') = comp u + comp u'`.

Introduce `u u'`. Use function extensionality and compare the values at `e γ`. Simplify using `[comp, map_add]`. Establish `hsmul : ∀ (c : ℂ) u, comp (c • u) = c • comp u`. Introduce `c u`.

Use function extensionality and compare the values at `e γ`. Simplify using `[comp, map_smul]`. Establish `hzero : comp 0 = 0` using `by funext e γ; simp [comp]`. Establish `hS` using `fun x x' y c hx hx' hy => JCx4.formLev_sesq_core P0 T sg j w a mm ha hmm x x' y c hx hx' hy`. Establish `h0l : ∀ u', D.formLev T sg j w 0 (comp u') = 0`.

Introduce `u'`. Establish `h` using `(hS (comp 0) (comp 0) (comp u') 1 (hin 0) (hin 0) (hin u')).1`. Rewrite `h` using `[hzero, one_smul, add_zero, one_mul]`. Take the linear combination `-h`. Establish `h0r : ∀ u, D.formLev T sg j w (comp u) 0 = 0`.

Introduce `u`. Establish `h` using `(hS (comp 0) (comp 0) (comp u) 1 (hin 0) (hin 0) (hin u)).2`. Rewrite `h` using `[hzero, one_smul, add_zero, map_one, one_mul]`. Take the linear combination `-h`. Set `Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u u' => D.formLev T sg j w (comp u) (comp u')) (fun u₁ u₂ u' => by`.

Rewrite using `[hadd]`. Establish `h` using `(hS (comp u₁) (comp u₂) (comp u') 1 (hin u₁) (hin u₂) (hin u')).1`. Rewrite `h` using `[one_smul, one_mul]`. Conclude with `h)`. Use the proof step `(fun c u u' => by`.

Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Rewrite using `[hsmul]`. Establish `h` using `(hS (comp 0) (comp u) (comp u') c (hin 0) (hin u) (hin u')).1`. Rewrite `h` using `[hzero, zero_add, h0l, zero_add]`. Conclude with `h)`.

Use the proof step `(fun u u₁ u₂ => by`. Rewrite using `[hadd]`. Establish `h` using `(hS (comp u₁) (comp u₂) (comp u) 1 (hin u₁) (hin u₂) (hin u)).2`. Rewrite `h` using `[one_smul, map_one, one_mul]`. Conclude with `h)`.

Use the proof step `(fun c u u' => by`. Simplify using `only [smul_eq_mul]`. Rewrite using `[hsmul]`. Establish `h` using `(hS (comp 0) (comp u') (comp u) c (hin 0) (hin u') (hin u)).2`. Rewrite `h` using `[hzero, zero_add, h0r, zero_add]`.

Conclude with `h)`. Take `⟨Cf, hCf0, hCf⟩` from `JCx4.formLev_bound_mm P0 T sg j w a ha`. Establish `hN0 : (0 : ℝ) ≤ (w.length : ℝ)` using `Nat.cast_nonneg _`. Use `⟨Bf, Real.sqrt Cf, Real.sqrt_nonneg _, fun u => ?_, ?_⟩` and prove the remaining obligations. Establish `hb` using `hCf (comp u) (comp u) ‖u‖ ‖u‖ (fun b => pd_ccle_mono (by linarith) hmm5 (hcc u b)) (fun b => pd_ccle_mono (by linarith) (by omega) (hcc u b))`.

Establish `e : Bf u u = D.formLev T sg j w (comp u) (comp u)` using `rfl`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Introduce `u u' x x' ε'' hε'' hx hx' hxu hxu' show D.formLev T sg j w (comp u) (comp u') = D.formLev T sg j w x x'`. Unfold `D.formLev`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Establish `hRR` using `JCx4.ma_hS P0 T sg j w`. Establish `hmmU : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 w.length` using `pd_thr_mm P0 j w.length _ le_rfl`. Establish `hinx : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x b)` using `fun b => sq_inCC_mono le_rfl (by omega) (hx b).2.1`. Establish `hinu : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (comp u b)` using `fun b => sq_inCC_mono ha (by omega) (hin u b)`.

Establish `hloc : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T sg j w) (comp u) e g = D.actOp (D.RRlev T sg j w) x e g`. Introduce `g hg`. Rewrite using `[JCx4.ma_actOp_eq, JCx4.ma_actOp_eq]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hA : P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ) + ((2 * w.length : ℕ) : ℝ) = P5.Auser P0 w.length + 1` using `by ring`.

Establish `hm : 0 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length = (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length` using `by ring`. Use `(hRR e b).2.2 (P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ)) 0 (comp u b) (x b) (by rw [hA, hm]; exact hinu b) (by rw [hA, hm]; exact hinx b) (fun γ hγ => hxu b γ hγ) g hg` and prove the remaining obligations. Rewrite using `[sq_beta_congr (T.bs j) hloc]`. Conclude with `FormNormSumIdentities.beta_congr_right (T.bs j) (fun γ hγ => hxu' e γ hγ)`.
-/
theorem form_model : Formalism.FourierDecayAlt.P.FormNormSumIdentities.FormModel := by
  intro Wp Wq _ _ _ _ _ _ P0 T sg j w a mm ε' Sg hε' ha hmm hmm5 hSg V _ _ Mo
  let comp : V → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun u e γ => Mo.ev u γ e
  have hcc : ∀ u e, CCle a mm (comp u e) ‖u‖ := fun u e => FormNormSumIdentities.ccle_comp (Mo.mem u) e
  have hin : ∀ u e, InCC a mm (comp u e) := fun u e => ⟨_, hcc u e⟩
  have hadd : ∀ u u', comp (u + u') = comp u + comp u' := by
    intro u u'; funext e γ; simp [comp, map_add]
  have hsmul : ∀ (c : ℂ) u, comp (c • u) = c • comp u := by
    intro c u; funext e γ; simp [comp, map_smul]
  have hzero : comp 0 = 0 := by funext e γ; simp [comp]
  have hS := fun x x' y c hx hx' hy => JCx4.formLev_sesq_core P0 T sg j w a mm ha hmm x x' y c hx hx' hy
  have h0l : ∀ u', D.formLev T sg j w 0 (comp u') = 0 := by
    intro u'
    have h := (hS (comp 0) (comp 0) (comp u') 1 (hin 0) (hin 0) (hin u')).1
    rw [hzero, one_smul, add_zero, one_mul] at h
    linear_combination -h
  have h0r : ∀ u, D.formLev T sg j w (comp u) 0 = 0 := by
    intro u
    have h := (hS (comp 0) (comp 0) (comp u) 1 (hin 0) (hin 0) (hin u)).2
    rw [hzero, one_smul, add_zero, map_one, one_mul] at h
    linear_combination -h
  let Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u u' => D.formLev T sg j w (comp u) (comp u'))
    (fun u₁ u₂ u' => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u') 1 (hin u₁) (hin u₂) (hin u')).1
      rw [one_smul, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u) (comp u') c (hin 0) (hin u) (hin u')).1
      rw [hzero, zero_add, h0l, zero_add] at h
      exact h)
    (fun u u₁ u₂ => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u) 1 (hin u₁) (hin u₂) (hin u)).2
      rw [one_smul, map_one, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u') (comp u) c (hin 0) (hin u') (hin u)).2
      rw [hzero, zero_add, h0r, zero_add] at h
      exact h)
  obtain ⟨Cf, hCf0, hCf⟩ := JCx4.formLev_bound_mm P0 T sg j w a ha
  have hN0 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
  refine ⟨Bf, Real.sqrt Cf, Real.sqrt_nonneg _, fun u => ?_, ?_⟩
  · have hb := hCf (comp u) (comp u) ‖u‖ ‖u‖
      (fun b => pd_ccle_mono (by linarith) hmm5 (hcc u b))
      (fun b => pd_ccle_mono (by linarith) (by omega) (hcc u b))
    have e : Bf u u = D.formLev T sg j w (comp u) (comp u) := rfl
    rw [e]
    calc (D.formLev T sg j w (comp u) (comp u)).re ≤ ‖D.formLev T sg j w (comp u) (comp u)‖ := Complex.re_le_norm _
      _ ≤ Cf * ‖u‖ * ‖u‖ := hb
      _ = (Real.sqrt Cf * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hCf0]; ring
  · intro u u' x x' ε'' hε'' hx hx' hxu hxu'
    show D.formLev T sg j w (comp u) (comp u') = D.formLev T sg j w x x'
    unfold D.formLev
    refine Finset.sum_congr rfl fun e _ => ?_
    have hRR := JCx4.ma_hS P0 T sg j w
    have hmmU : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 w.length :=
      pd_thr_mm P0 j w.length _ le_rfl
    have hinx : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x b) :=
      fun b => sq_inCC_mono le_rfl (by omega) (hx b).2.1
    have hinu : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (comp u b) :=
      fun b => sq_inCC_mono ha (by omega) (hin u b)
    have hloc : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T sg j w) (comp u) e g =
        D.actOp (D.RRlev T sg j w) x e g := by
      intro g hg
      rw [JCx4.ma_actOp_eq, JCx4.ma_actOp_eq]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hA : P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ) + ((2 * w.length : ℕ) : ℝ) =
          P5.Auser P0 w.length + 1 := by ring
      have hm : 0 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length =
          (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length := by ring
      refine (hRR e b).2.2 (P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ)) 0 (comp u b) (x b)
        (by rw [hA, hm]; exact hinu b) (by rw [hA, hm]; exact hinx b) (fun γ hγ => hxu b γ hγ) g hg
    rw [sq_beta_congr (T.bs j) hloc]
    exact FormNormSumIdentities.beta_congr_right (T.bs j) (fun γ hγ => hxu' e γ hγ)

end Formalism.FourierDecayAlt.P
