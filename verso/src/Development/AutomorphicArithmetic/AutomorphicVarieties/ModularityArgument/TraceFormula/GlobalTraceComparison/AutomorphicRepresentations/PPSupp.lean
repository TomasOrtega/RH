import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemLp
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulLinearAe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulFunctionAe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationFunction
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationNormBound

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS

open MeasureTheory

section Abs

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/- English proof (translation)
Use `set p := S.starProjection w with hp`. Establish `hpS : p ∈ S` using `Submodule.starProjection_apply_mem S w`. Establish `hq : w - p ∈ Sᗮ` using `Submodule.sub_starProjection_mem_orthogonal w`. Establish `hmq : m (w - p) ∈ Sᗮ`. Rewrite `hq`, the goal using `[Submodule.mem_orthogonal]`.

Introduce `u hu`. Rewrite using `[← hs]`. Conclude with `hq _ (hS u hu)`. Establish `h1 : m p - p ∈ S` using `S.sub_mem (hS p hpS) hpS`. Establish `h2 : m p - p ∈ Sᗮ`.

Establish `e : m p - p = (w - p) - m (w - p)`. Rewrite using `[map_sub, hw]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Sᗮ.sub_mem hq hmq`.

Establish `h3 : m p - p = 0`. Use `(Submodule.mem_orthogonal S _).1 h2 _ h1` as an intermediate fact. Conclude with `inner_self_eq_zero.1 this`. Conclude with `sub_eq_zero.1 h3`.
-/
private theorem fix_proj (S : Submodule ℂ K) [S.HasOrthogonalProjection] (m : K →L[ℂ] K)
    (hs : ∀ x y, inner ℂ (m x) y = inner ℂ x (m y)) (hS : ∀ x ∈ S, m x ∈ S) (w : K) (hw : m w = w) :
    m (S.starProjection w) = S.starProjection w := by
  set p := S.starProjection w with hp
  have hpS : p ∈ S := Submodule.starProjection_apply_mem S w
  have hq : w - p ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal w
  have hmq : m (w - p) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal] at hq ⊢
    intro u hu
    rw [← hs]
    exact hq _ (hS u hu)
  have h1 : m p - p ∈ S := S.sub_mem (hS p hpS) hpS
  have h2 : m p - p ∈ Sᗮ := by
    have e : m p - p = (w - p) - m (w - p) := by
      rw [map_sub, hw]; abel
    rw [e]
    exact Sᗮ.sub_mem hq hmq
  have h3 : m p - p = 0 := by
    have := (Submodule.mem_orthogonal S _).1 h2 _ h1
    exact inner_self_eq_zero.1 this
  exact sub_eq_zero.1 h3

end Abs

section Mul

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (c : X → ℝ)

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Qf3.mul_memLp <;> assumption`.
-/
private theorem mul_memLp (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    MemLp (fun x => (c x : ℂ) * (f : X → ℂ) x) 2 ν :=
  by apply _root_.UpperTheory.Reformulated.B.Qf3.mul_memLp <;> assumption

private noncomputable def mulFn (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) : Lp ℂ 2 ν :=
  by apply _root_.UpperTheory.Reformulated.B.MultiplicationFunction.mulFn <;> assumption

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.MulFunctionAe.mulFn_ae <;> assumption`.
-/
private theorem mulFn_ae (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    (mulFn c hc hb f : X → ℂ) =ᵐ[ν] fun x => (c x : ℂ) * (f : X → ℂ) x :=
  by apply _root_.UpperTheory.Reformulated.B.MulFunctionAe.mulFn_ae <;> assumption

private noncomputable def mulL (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  by apply _root_.UpperTheory.Reformulated.B.MultiplicationNormBound.mulL <;> assumption

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.MulLinearAe.mulL_ae <;> assumption`.
-/
private theorem mulL_ae (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    (mulL c hc hb f : X → ℂ) =ᵐ[ν] fun x => (c x : ℂ) * (f : X → ℂ) x :=
  by apply _root_.UpperTheory.Reformulated.B.MulLinearAe.mulL_ae <;> assumption

/- English proof (translation)
Rewrite using `[L2.inner_def, L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [mulL_ae c hc hb f, mulL_ae c hc hb g] with x h1 h2`. Rewrite using `[h1, h2]`. Simplify using `only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mulL_inner (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f g : Lp ℂ 2 ν) :
    inner ℂ (mulL c hc hb f) g = inner ℂ f (mulL c hc hb g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL_ae c hc hb f, mulL_ae c hc hb g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

private def mulS (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) :
    PiLp 2 (fun _ : Unit => Lp ℂ 2 ν) →L[ℂ] PiLp 2 (fun _ : Unit => Lp ℂ 2 ν) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Unit => Lp ℂ 2 ν)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i : Unit => (mulL c hc hb).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => Lp ℂ 2 ν) i)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Unit => Lp ℂ 2 ν)).toContinuousLinearMap)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mulS_apply (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1)
    (f : PiLp 2 (fun _ : Unit => Lp ℂ 2 ν)) (i : Unit) : mulS c hc hb f i = mulL c hc hb (f i) := rfl

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mulS_apply, mulS_apply, mulL_inner]`.
-/
private theorem mulS_inner (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1)
    (f g : PiLp 2 (fun _ : Unit => Lp ℂ 2 ν)) :
    inner ℂ (mulS c hc hb f) g = inner ℂ f (mulS c hc hb g) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulS_apply, mulS_apply, mulL_inner]

end Mul

section Cut

private def chi (a b s : ℝ) : ℝ := max 0 (1 - (max (a - s) 0 + max (s - b) 0))

/- English proof (translation)
Unfold `chi`. Use `fun_prop`.
-/
private theorem chi_cont (a b : ℝ) : Continuous (chi a b) := by
  unfold chi
  fun_prop

/- English proof (translation)
Establish `h1 : 0 ≤ max (a - s) 0` using `le_max_right _ _`. Establish `h2 : 0 ≤ max (s - b) 0` using `le_max_right _ _`. Establish `h3 : 0 ≤ chi a b s` using `le_max_left _ _`. Rewrite using `[abs_of_nonneg h3]`. Conclude with `max_le zero_le_one (by linarith)`.
-/
private theorem chi_abs (a b s : ℝ) : |chi a b s| ≤ 1 := by
  have h1 : 0 ≤ max (a - s) 0 := le_max_right _ _
  have h2 : 0 ≤ max (s - b) 0 := le_max_right _ _
  have h3 : 0 ≤ chi a b s := le_max_left _ _
  rw [abs_of_nonneg h3]
  exact max_le zero_le_one (by linarith)

/- English proof (translation)
Establish `h1 : max (a - s) 0 = 0` using `max_eq_right (by linarith [h.1])`. Establish `h2 : max (s - b) 0 = 0` using `max_eq_right (by linarith [h.2])`. Simplify using `[chi, h1, h2]`.
-/
private theorem chi_eq_one {a b s : ℝ} (h : s ∈ Set.Icc a b) : chi a b s = 1 := by
  have h1 : max (a - s) 0 = 0 := max_eq_right (by linarith [h.1])
  have h2 : max (s - b) 0 = 0 := max_eq_right (by linarith [h.2])
  simp [chi, h1, h2]

/- English proof (translation)
Introduce `e`. Establish `h1 : 0 ≤ max (a - s) 0` using `le_max_right _ _`. Establish `h2 : 0 ≤ max (s - b) 0` using `le_max_right _ _`. Establish `h3 : 1 ≤ 1 - (max (a - s) 0 + max (s - b) 0)`. Unfold `chi at e`.

Break down `max_choice (0 : ℝ) (1 - (max (a - s) 0 + max (s - b) 0)) with h | h` into its components or cases. Rewrite `e` using `[h]`. Evaluate the numerical expressions using `at e`. Rewrite `e` using `[h]`. Conclude with `e.ge`.

Establish `h4 : a - s ≤ 0` using `by linarith [le_max_left (a - s) 0]`. Establish `h5 : s - b ≤ 0` using `by linarith [le_max_left (s - b) 0]`. Conclude with `h ⟨by linarith, by linarith⟩`.
-/
private theorem chi_ne_one {a b s : ℝ} (h : s ∉ Set.Icc a b) : chi a b s ≠ 1 := by
  intro e
  have h1 : 0 ≤ max (a - s) 0 := le_max_right _ _
  have h2 : 0 ≤ max (s - b) 0 := le_max_right _ _
  have h3 : 1 ≤ 1 - (max (a - s) 0 + max (s - b) 0) := by
    unfold chi at e
    rcases max_choice (0 : ℝ) (1 - (max (a - s) 0 + max (s - b) 0)) with h | h
    · rw [h] at e; norm_num at e
    · rw [h] at e; exact e.ge
  have h4 : a - s ≤ 0 := by linarith [le_max_left (a - s) 0]
  have h5 : s - b ≤ 0 := by linarith [le_max_left (s - b) 0]
  exact h ⟨by linarith, by linarith⟩

end Cut

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS

end

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc MeasureTheory in
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH in
/- English proof (translation)
Introduce `E _ _ _ n D π a b v hv`. Use `haveI : BorelSpace (H E n 0) := ⟨rfl⟩`. Establish `hl : Continuous (ldet : H E n 0 → ℝ)` using `continuous_ldet`. Use `set c : H E n 0 → ℝ := fun x => chi a b (ldet x) with hcdef`. Establish `hc : Measurable c` using `((chi_cont a b).comp hl).measurable`.

Establish `hb : ∀ x, |c x| ≤ 1` using `fun x => chi_abs a b _`. Establish `hgen : ∀ f : Hs (ι` using `Unit) D, IsPiVec D π f → IsPiVec D π (mulS c hc hb f) := by`. Introduce `f hf i`. Take `⟨ψ, hψ, u, hu, hus, he⟩` from `hf i`. Use `⟨ψ, hψ, fun s => (chi a b s : ℂ) * u s, (Complex.continuous_ofReal.comp (chi_cont a b)).mul hu, hus.mul_left, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulS_apply]`. Use `filter_upwards [mulL_ae c hc hb (f i), he] with x h1 h2`. Rewrite using `[h1, h2]`. Simplify using `only [hcdef]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hS : ∀ f ∈ piSp D π Unit, mulS c hc hb f ∈ piSp D π Unit`. Establish `hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π Unit).comap (mulS (ν` using `D.ν) c hc hb).toLinearMap := by`. Use `Submodule.span_le.2 fun f hf => ?_` and prove the remaining obligations. Conclude with `Submodule.le_topologicalClosure _ (Submodule.subset_span (hgen f hf))`. Establish `hcl : IsClosed (((piSp D π Unit).comap (mulS (ν` using `D.ν) c hc hb).toLinearMap : Submodule ℂ _) : Set (Hs (ι := Unit) D)) := (show IsClosed (piSp D π Unit : Set (Hs (ι := Unit) D)) from Submodule.isClosed_topologicalClosure _).preimage (mulS c hc hb).continuous`.

Conclude with `fun f hf => Submodule.topologicalClosure_minimal _ hle hcl hf`. Establish `hv1 : mulL c hc hb v = v`. Use `Lp.ext ?_` and prove the remaining obligations. Use `filter_upwards [mulL_ae c hc hb v, hv] with x h1 h2`. Rewrite using `[h1]`.

Distinguish the cases in `hx : ldet x ∈ Set.Icc a b`. Simplify using `[hcdef, chi_eq_one hx]`. Simplify using `[h2 hx]`. Establish `hw : mulS c hc hb (vecM v fun _ : Unit => 1) = vecM v fun _ : Unit => 1` using `by ext1 i`. Rewrite using `[mulS_apply]`.

Use `show mulL c hc hb ((1 : ℂ) • v) = (1 : ℂ) • v`. Rewrite using `[one_smul, hv1]`. Establish `key` using `fix_proj (piSp D π Unit) (mulS c hc hb) (mulS_inner c hc hb) hS _ hw`. Establish `h2 : mulL c hc hb (P0 D π v) = P0 D π v`. Use `congrArg (fun f : Hs (ι := Unit) D => f ()) key` as an intermediate fact.

Conclude with `this`. Establish `h3` using `mulL_ae c hc hb (P0 D π v)`. Rewrite `h3` using `[h2]`. Use `filter_upwards [h3] with x h4 hx`. Establish `h5 : ((c x : ℂ) - 1) * (P0 D π v : H E n 0 → ℂ) x = 0`.

Rewrite using `[sub_mul, one_mul, ← h4, sub_self]`. Break down `mul_eq_zero.1 h5 with h6 | h6` into its components or cases. It suffices to derive a contradiction. Establish `h7 : (c x : ℂ) = ((1 : ℝ) : ℂ)`. Rewrite using `[sub_eq_zero.1 h6]`.

Simplify using the standard rewrite rules. Conclude with `chi_ne_one hx (Complex.ofReal_injective h7)`. Conclude with `h6`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pSupp_pf :
    PSupp := by
  intro E _ _ _ n D π a b v hv
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have hl : Continuous (ldet : H E n 0 → ℝ) := continuous_ldet
  set c : H E n 0 → ℝ := fun x => chi a b (ldet x) with hcdef
  have hc : Measurable c := ((chi_cont a b).comp hl).measurable
  have hb : ∀ x, |c x| ≤ 1 := fun x => chi_abs a b _
  have hgen : ∀ f : Hs (ι := Unit) D, IsPiVec D π f → IsPiVec D π (mulS c hc hb f) := by
    intro f hf i
    obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hf i
    refine ⟨ψ, hψ, fun s => (chi a b s : ℂ) * u s,
      (Complex.continuous_ofReal.comp (chi_cont a b)).mul hu, hus.mul_left, ?_⟩
    rw [mulS_apply]
    filter_upwards [mulL_ae c hc hb (f i), he] with x h1 h2
    rw [h1, h2]
    simp only [hcdef]
    ring
  have hS : ∀ f ∈ piSp D π Unit, mulS c hc hb f ∈ piSp D π Unit := by
    have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤
        (piSp D π Unit).comap (mulS (ν := D.ν) c hc hb).toLinearMap := by
      refine Submodule.span_le.2 fun f hf => ?_
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hgen f hf))
    have hcl : IsClosed (((piSp D π Unit).comap
        (mulS (ν := D.ν) c hc hb).toLinearMap : Submodule ℂ _) : Set (Hs (ι := Unit) D)) :=
      (show IsClosed (piSp D π Unit : Set (Hs (ι := Unit) D)) from
        Submodule.isClosed_topologicalClosure _).preimage (mulS c hc hb).continuous
    exact fun f hf => Submodule.topologicalClosure_minimal _ hle hcl hf
  have hv1 : mulL c hc hb v = v := by
    refine Lp.ext ?_
    filter_upwards [mulL_ae c hc hb v, hv] with x h1 h2
    rw [h1]
    by_cases hx : ldet x ∈ Set.Icc a b
    · simp [hcdef, chi_eq_one hx]
    · simp [h2 hx]
  have hw : mulS c hc hb (vecM v fun _ : Unit => 1) = vecM v fun _ : Unit => 1 := by
    ext1 i
    rw [mulS_apply]
    show mulL c hc hb ((1 : ℂ) • v) = (1 : ℂ) • v
    rw [one_smul, hv1]
  have key := fix_proj (piSp D π Unit) (mulS c hc hb) (mulS_inner c hc hb) hS _ hw
  have h2 : mulL c hc hb (P0 D π v) = P0 D π v := by
    have := congrArg (fun f : Hs (ι := Unit) D => f ()) key
    exact this
  have h3 := mulL_ae c hc hb (P0 D π v)
  rw [h2] at h3
  filter_upwards [h3] with x h4 hx
  have h5 : ((c x : ℂ) - 1) * (P0 D π v : H E n 0 → ℂ) x = 0 := by
    rw [sub_mul, one_mul, ← h4, sub_self]
  rcases mul_eq_zero.1 h5 with h6 | h6
  · exfalso
    have h7 : (c x : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [sub_eq_zero.1 h6]; simp
    exact chi_ne_one hx (Complex.ofReal_injective h7)
  · exact h6
