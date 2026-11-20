import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `h : M.topologicalClosure = M` using `hM.submodule_topologicalClosure_eq`. Establish `h2 : prj M x ∈ M.topologicalClosure` using `Submodule.starProjection_apply_mem M.topologicalClosure x`. Rewrite `h2` using `[h]`. Then use the resulting hypothesis.
-/
private lemma prj_mem' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) : prj M x ∈ M := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  have h2 : prj M x ∈ M.topologicalClosure := Submodule.starProjection_apply_mem M.topologicalClosure x
  rwa [h] at h2

/- English proof (translation)
The claim follows from `(Submodule.mem_orthogonal' _ _).1 (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) y (M.le_topologicalClosure hy)`.
-/
private lemma prj_orth' (M : Submodule ℂ H) (x : H) {y : H} (hy : y ∈ M) :
    ⟪x - prj M x, y⟫_ℂ = 0 :=
  (Submodule.mem_orthogonal' _ _).1
    (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) y
    (M.le_topologicalClosure hy)

/- English proof (translation)
Establish `h : M.topologicalClosure = M` using `hM.submodule_topologicalClosure_eq`. Conclude with `Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure) (M.le_topologicalClosure hv) fun y hy => ho y (by rwa [h] at hy)`.
-/
private lemma prj_eq' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {u v : H} (hv : v ∈ M)
    (ho : ∀ y ∈ M, ⟪u - v, y⟫_ℂ = 0) : prj M u = v := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure)
    (M.le_topologicalClosure hv) fun y hy => ho y (by rwa [h] at hy)

/- English proof (translation)
The claim follows from `prj_eq' hM hv fun y _ => by simp`.
-/
private lemma prj_self' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {v : H} (hv : v ∈ M) :
    prj M v = v :=
  prj_eq' hM hv fun y _ => by simp

/- English proof (translation)
Use `ContinuousLinearMap.ext fun x => ?_` and prove the remaining obligations. Use `show B (prj M x) = prj M (B x)`. Use `(prj_eq' hM (h1 _ (prj_mem' hM x)) fun y hy => ?_).symm` and prove the remaining obligations. Rewrite using `[← map_sub, hadj]`. Conclude with `prj_orth' M x (h2 y hy)`.
-/
private lemma comm_of_stable {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (B B' : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B' y⟫_ℂ) (h1 : ∀ v ∈ M, B v ∈ M) (h2 : ∀ v ∈ M, B' v ∈ M) :
    Commute B (prj M) := by
  refine ContinuousLinearMap.ext fun x => ?_
  show B (prj M x) = prj M (B x)
  refine (prj_eq' hM (h1 _ (prj_mem' hM x)) fun y hy => ?_).symm
  rw [← map_sub, hadj]
  exact prj_orth' M x (h2 y hy)

/- English proof (translation)
Establish `hcl` using `Submodule.closed_of_finiteDimensional W`. Set `e` to `stdOrthonormalBasis ℂ W`. Apply the tactic sequence `have he : Orthonormal ℂ (fun k => ((e k : W) : H)) := e.orthonormal.comp_linearIsometry W.subtypeₗᵢ`. Take `⟨s, b, hvs, hb⟩` from `(he.toSubtypeRange).exists_hilbertBasis_extension`. Establish `hbi : ∀ i, b i = (i : H)` using `fun i => congrFun hb i`.

Set `f : Fin _ → s` to `fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩`. Establish `hf : Function.Injective f` using `fun k l h => by`. Establish `: ((e k : W) : H) = (e l : W)` using `congrArg (fun z : s => (z : H)) h`. Conclude with `he.linearIndependent.injective this`. Establish `hbf : ∀ k, b (f k) = (e k : H)` using `fun k => hbi _`.

Establish `hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0` using `fun i hi => by`. Use `prj_eq' hcl W.zero_mem fun y hy => ?_` and prove the remaining obligations. Establish `hy' : (y : H) = ∑ k, ⟪(e k : H), y⟫_ℂ • (e k : H)`. Establish `h2` using `congrArg Subtype.val (e.sum_repr' (⟨y, hy⟩ : W))`. Simplify `h2.symm` using `[Submodule.coe_sum]`.

Rewrite using `[sub_zero, hy', inner_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, ← hbf k]`. Establish `: ⟪b i, b (f k)⟫_ℂ = 0` using `b.orthonormal.2 fun h => hi ⟨k, h.symm⟩`. Rewrite using `[this, mul_zero]`.

Rewrite using `[isHilbertSchmidt_iff b]`. Establish `hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f` using `fun i hi => by`. Assume the negation of the conclusion as `h`. Conclude with `hi (by simp [hout i h])`. Rewrite using `[← hf.tsum_eq hs, tsum_fintype]`.

Conclude with `ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top enorm_lt_top`.
-/
private lemma hs_prj (W : Submodule ℂ H) [FiniteDimensional ℂ W] : IsHilbertSchmidt (prj W) := by
  have hcl := Submodule.closed_of_finiteDimensional W
  let e := stdOrthonormalBasis ℂ W
  have he : Orthonormal ℂ (fun k => ((e k : W) : H)) :=
    e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  obtain ⟨s, b, hvs, hb⟩ := (he.toSubtypeRange).exists_hilbertBasis_extension
  have hbi : ∀ i, b i = (i : H) := fun i => congrFun hb i
  let f : Fin _ → s := fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩
  have hf : Function.Injective f := fun k l h => by
    have : ((e k : W) : H) = (e l : W) := congrArg (fun z : s => (z : H)) h
    exact he.linearIndependent.injective this
  have hbf : ∀ k, b (f k) = (e k : H) := fun k => hbi _
  have hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0 := fun i hi => by
    refine prj_eq' hcl W.zero_mem fun y hy => ?_
    have hy' : (y : H) = ∑ k, ⟪(e k : H), y⟫_ℂ • (e k : H) := by
      have h2 := congrArg Subtype.val (e.sum_repr' (⟨y, hy⟩ : W))
      simpa [Submodule.coe_sum] using h2.symm
    rw [sub_zero, hy', inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, ← hbf k]
    have : ⟪b i, b (f k)⟫_ℂ = 0 := b.orthonormal.2 fun h => hi ⟨k, h.symm⟩
    rw [this, mul_zero]
  rw [isHilbertSchmidt_iff b]
  have hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f := fun i hi => by
    by_contra h
    exact hi (by simp [hout i h])
  rw [← hf.tsum_eq hs, tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top enorm_lt_top

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `E _ _ _`. Simplify using the standard rewrite rules.

Consider the case `succ r ih`. Introduce `E hE hc hs`. Take `⟨i1, i2, i3⟩` from `ih (fun i => E i.succ) (fun i => hE _) (fun i j => hc _ _) (fun i => hs _)`. Establish `hP : ∀ u, (List.ofFn fun i => prj (E i)).prod u = prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)` using `fun u => by`. Rewrite using `[List.ofFn_succ, List.prod_cons]`.

Both sides reduce to the same expression. Use `⟨fun u hu => ?_, fun u => ?_, fun u y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hP]`. Conclude with `hs 0 _ (i1 u hu)`. Rewrite using `[hP, Submodule.mem_iInf]`.

Use `Fin.cases (prj_mem' (hE 0) _) fun j => ?_` and prove the remaining obligations. Establish `hx` using `Submodule.mem_iInf _ |>.1 (i2 u) j`. Establish `h1 : prj (E j.succ) (prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) = prj (E 0) (prj (E j.succ) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u))` using `congrArg (fun T : H →L[ℂ] H => T ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) (hc j.succ 0).eq`. Rewrite `h1` using `[prj_self' (hE _) hx]`. Rewrite using `[← h1]`.

Conclude with `prj_mem' (hE _) _`. Rewrite using `[hP]`. Establish `hy0 : y ∈ E 0` using `(Submodule.mem_iInf _).1 hy 0`. Establish `hys : y ∈ ⨅ i : Fin r, E i.succ` using `(Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).1 hy j.succ`. Establish `e : u - prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) = (u - (List.ofFn fun i : Fin r => prj (E i.succ)).prod u) + ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u - prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u))` using `by abel`.

Rewrite using `[e, inner_add_left, i3 u y hys, prj_orth' _ _ hy0, add_zero]`.
-/
private lemma pr_props (Z : Submodule ℂ H) : ∀ (r : ℕ) (E : Fin r → Submodule ℂ H),
    (∀ i, IsClosed (E i : Set H)) → (∀ i j, Commute (prj (E i)) (prj (E j))) →
    (∀ i, ∀ v ∈ Z, prj (E i) v ∈ Z) →
    (∀ u ∈ Z, (List.ofFn fun i => prj (E i)).prod u ∈ Z) ∧
    (∀ u, (List.ofFn fun i => prj (E i)).prod u ∈ ⨅ i, E i) ∧
    ∀ u, ∀ y ∈ ⨅ i, E i, ⟪u - (List.ofFn fun i => prj (E i)).prod u, y⟫_ℂ = 0 := by
  intro r
  induction r with
  | zero =>
    intro E _ _ _
    simp
  | succ r ih =>
    intro E hE hc hs
    obtain ⟨i1, i2, i3⟩ := ih (fun i => E i.succ) (fun i => hE _) (fun i j => hc _ _) (fun i => hs _)
    have hP : ∀ u, (List.ofFn fun i => prj (E i)).prod u =
        prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) := fun u => by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    refine ⟨fun u hu => ?_, fun u => ?_, fun u y hy => ?_⟩
    · rw [hP]
      exact hs 0 _ (i1 u hu)
    · rw [hP, Submodule.mem_iInf]
      refine Fin.cases (prj_mem' (hE 0) _) fun j => ?_
      have hx := Submodule.mem_iInf _ |>.1 (i2 u) j
      have h1 : prj (E j.succ) (prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) =
          prj (E 0) (prj (E j.succ) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) :=
        congrArg (fun T : H →L[ℂ] H => T ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) (hc j.succ 0).eq
      rw [prj_self' (hE _) hx] at h1
      rw [← h1]
      exact prj_mem' (hE _) _
    · rw [hP]
      have hy0 : y ∈ E 0 := (Submodule.mem_iInf _).1 hy 0
      have hys : y ∈ ⨅ i : Fin r, E i.succ := (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).1 hy j.succ
      have e : u - prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) =
          (u - (List.ofFn fun i : Fin r => prj (E i.succ)).prod u) +
          ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u -
            prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) := by abel
      rw [e, inner_add_left, i3 u y hys, prj_orth' _ _ hy0, add_zero]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYX`. Establish `hXc` using `Submodule.closed_of_finiteDimensional X`. Establish `hYc` using `Submodule.closed_of_finiteDimensional Y`. Establish `e1 : prj X ∘L (Pr ∘L R) ∘L prj X = prj Y ∘L (R ∘L prj X)`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations.

Establish `hx : R (prj X v) ∈ Z` using `hR _ (hXZ (prj_mem' hXc v))`. Use `show prj X (Pr (R (prj X v))) = prj Y (R (prj X v))`. Rewrite using `[prj_self' hXc (hYX (h1 _ hx)), prj_eq' hYc (h1 _ hx) (h2 _)]`. Establish `e2 : (R ∘L prj X) ∘L prj Y = R ∘L prj Y`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations.

Use `show R (prj X (prj Y v)) = R (prj Y v)`. Rewrite using `[prj_self' hXc (hYX (prj_mem' hYc v))]`. Establish `e3 : (R ∘L prj Y) ∘L prj Y = R ∘L prj Y`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Use `show R (prj Y (prj Y v)) = R (prj Y v)`.

Rewrite using `[prj_self' hYc (prj_mem' hYc v)]`. Establish `e4 : prj Y ∘L prj Y = prj Y`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Conclude with `prj_self' hYc (prj_mem' hYc v)`. Establish `hT : IsTraceClass (prj Y)`.

Use `isTraceClass_comp (hs_prj Y) (hs_prj Y)` as an intermediate fact. Rewrite `this` using `[show (prj Y).comp (prj Y) = prj Y from e4]`. Then use the resulting hypothesis. Unfold `trOn`. Rewrite using `[e1]`. Establish `a` using `trace_comp_comm hT (R ∘L prj X)`.

Establish `b` using `trace_comp_comm hT (R ∘L prj Y)`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma tr_main {Z X Y : Submodule ℂ H} (Pr R : H →L[ℂ] H) [FiniteDimensional ℂ X] (hYX : Y ≤ X)
    (hXZ : X ≤ Z) (hR : ∀ v ∈ Z, R v ∈ Z) (h1 : ∀ u ∈ Z, Pr u ∈ Y)
    (h2 : ∀ u, ∀ y ∈ Y, ⟪u - Pr u, y⟫_ℂ = 0) : trOn X (Pr ∘L R) = trOn Y R := by
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYX
  have hXc := Submodule.closed_of_finiteDimensional X
  have hYc := Submodule.closed_of_finiteDimensional Y
  have e1 : prj X ∘L (Pr ∘L R) ∘L prj X = prj Y ∘L (R ∘L prj X) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hx : R (prj X v) ∈ Z := hR _ (hXZ (prj_mem' hXc v))
    show prj X (Pr (R (prj X v))) = prj Y (R (prj X v))
    rw [prj_self' hXc (hYX (h1 _ hx)), prj_eq' hYc (h1 _ hx) (h2 _)]
  have e2 : (R ∘L prj X) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj X (prj Y v)) = R (prj Y v)
    rw [prj_self' hXc (hYX (prj_mem' hYc v))]
  have e3 : (R ∘L prj Y) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj Y (prj Y v)) = R (prj Y v)
    rw [prj_self' hYc (prj_mem' hYc v)]
  have e4 : prj Y ∘L prj Y = prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self' hYc (prj_mem' hYc v)
  have hT : IsTraceClass (prj Y) := by
    have := isTraceClass_comp (hs_prj Y) (hs_prj Y)
    rwa [show (prj Y).comp (prj Y) = prj Y from e4] at this
  unfold trOn
  rw [e1]
  have a := trace_comp_comm hT (R ∘L prj X)
  have b := trace_comp_comm hT (R ∘L prj Y)
  calc trace (prj Y ∘L R ∘L prj X) = trace ((R ∘L prj X) ∘L prj Y) := a.symm
    _ = trace ((R ∘L prj Y) ∘L prj Y) := by rw [e2, e3]
    _ = trace (prj Y ∘L R ∘L prj Y) := b

end Hilbert

/- English proof (translation)
Introduce `K _ _ n μ _ Z r w hw J χ hc R hCO hZ hst hR hfd`. Establish `hB` using `fun i => UpperTheory.ConvolutionTheory.L1.eigBasic K n μ (w i) (J i) (χ i) (hCO i) (hc i)`. Establish `hF` using `UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥`. Establish `hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h'` using `hF.2.2.2.2.2.1`. Establish `hadjF : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹` using `hF.2.2.2.2.2.2.2.1`.

Establish `hadj : ∀ (u : Pl K) g x y, ⟪rhoL μ u g x, y⟫_ℂ = ⟪x, rhoL μ u g⁻¹ y⟫_ℂ` using `fun u g x y => by`. Establish `: rhoL μ u g⁻¹ = ContinuousLinearMap.adjoint (rhoL μ u g)`. Unfold `rhoL`. Rewrite using `[hadjF, map_inv]`. Rewrite using `[this, ContinuousLinearMap.adjoint_inner_right]`.

Establish `hcomZ : ∀ i, Commute (prj Z) (prj (eigL μ (w i) (J i) (χ i)))` using `fun i => (hB i).2.2.2 (prj Z) fun x _ => (comm_of_stable hZ (rhoL μ (w i) x) (rhoL μ (w i) x⁻¹) (hadj _ x) (hst i x) (hst i x⁻¹)).symm`. Establish `hs : ∀ i, ∀ v ∈ Z, prj (eigL μ (w i) (J i) (χ i)) v ∈ Z` using `fun i v hv => by`. Establish `h1 : prj Z (prj (eigL μ (w i) (J i) (χ i)) v) = prj (eigL μ (w i) (J i) (χ i)) (prj Z v)` using `congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (hcomZ i).eq`. Rewrite `h1` using `[prj_self' hZ hv]`. Rewrite using `[← h1]`.

Conclude with `prj_mem' hZ _`. Establish `hrho : ∀ i j, i ≠ j → ∀ x y, Commute (rhoL μ (w j) x) (rhoL μ (w i) y)` using `fun i j hij x y => by`. Establish `hne : w i ≠ w j` using `fun h => hij (hw h)`. Use `(UpperTheory.ConvolutionTheory.Tf.locEmb K n (w j)).2.2.2.1 (w i) hne x y` as an intermediate fact. Use `show rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _`.

Rewrite using `[← hmul, ← hmul, this]`. Establish `hcom : ∀ i j, Commute (prj (eigL μ (w i) (J i) (χ i))) (prj (eigL μ (w j) (J j) (χ j)))` using `fun i j => by`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `Commute.refl _`.

Conclude with `(hB j).2.2.2 _ fun x _ => ((hB i).2.2.2 _ fun y _ => hrho i j hij x y).symm`. Take `⟨p1, p2, p3⟩` from `pr_props Z r (fun i => eigL μ (w i) (J i) (χ i)) (fun i => (hB i).1) hcom hs`. Establish `hle : ∀ i, eigL μ (w i) (J i) (χ i) ≤ fixL μ (w i) (kerChr (J i) (χ i) (hc i))` using `fun i v hv => by`. Use `((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `h1 : rhoL μ (w i) x v = χ i x • v`. Simplify `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv x) hx.1` using `[eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]`. Establish `h2 : χ i x = 1` using `hx.2`. Rewrite `h1` using `[h2, one_smul]`. Conclude with `h1`.

Use `tr_main (Z := Z) _ R (inf_le_inf_left Z (iInf_mono hle)) inf_le_left hR (fun u hu => Submodule.mem_inf.2 ⟨p1 u hu, p2 u⟩) fun u y hy => p3 u y (Submodule.mem_inf.1 hy).2` and prove the remaining obligations.
-/
theorem UpperTheory.trOn_prod_eigenProjections_eq_trOn_joint_eigenspace :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (Z : Submodule ℂ (LL μ))
        (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (χ : ∀ i, Gw n (w i) → ℂ)
        (hc : ∀ i, IsChr (J i) (χ i)) (R : LL μ →L[ℂ] LL μ), (∀ i, CO (J i)) → IsClosed (Z : Set (LL μ)) →
        (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) → (∀ v ∈ Z, R v ∈ Z) →
        FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) →
        trOn (Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) ((List.ofFn fun i => prj (eigL μ (w i) (J i) (χ i))).prod ∘L R) =
          trOn (Z ⊓ ⨅ i, eigL μ (w i) (J i) (χ i)) R := by
  intro K _ _ n μ _ Z r w hw J χ hc R hCO hZ hst hR hfd
  have hB := fun i => UpperTheory.ConvolutionTheory.L1.eigBasic K n μ (w i) (J i) (χ i) (hCO i) (hc i)
  have hF := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := hF.2.2.2.2.2.1
  have hadjF : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := hF.2.2.2.2.2.2.2.1
  have hadj : ∀ (u : Pl K) g x y, ⟪rhoL μ u g x, y⟫_ℂ = ⟪x, rhoL μ u g⁻¹ y⟫_ℂ := fun u g x y => by
    have : rhoL μ u g⁻¹ = ContinuousLinearMap.adjoint (rhoL μ u g) := by
      unfold rhoL
      rw [hadjF, map_inv]
    rw [this, ContinuousLinearMap.adjoint_inner_right]
  have hcomZ : ∀ i, Commute (prj Z) (prj (eigL μ (w i) (J i) (χ i))) := fun i =>
    (hB i).2.2.2 (prj Z) fun x _ =>
      (comm_of_stable hZ (rhoL μ (w i) x) (rhoL μ (w i) x⁻¹) (hadj _ x) (hst i x) (hst i x⁻¹)).symm
  have hs : ∀ i, ∀ v ∈ Z, prj (eigL μ (w i) (J i) (χ i)) v ∈ Z := fun i v hv => by
    have h1 : prj Z (prj (eigL μ (w i) (J i) (χ i)) v) = prj (eigL μ (w i) (J i) (χ i)) (prj Z v) :=
      congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (hcomZ i).eq
    rw [prj_self' hZ hv] at h1
    rw [← h1]
    exact prj_mem' hZ _
  have hrho : ∀ i j, i ≠ j → ∀ x y, Commute (rhoL μ (w j) x) (rhoL μ (w i) y) := fun i j hij x y => by
    have hne : w i ≠ w j := fun h => hij (hw h)
    have := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w j)).2.2.2.1 (w i) hne x y
    show rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
    rw [← hmul, ← hmul, this]
  have hcom : ∀ i j, Commute (prj (eigL μ (w i) (J i) (χ i))) (prj (eigL μ (w j) (J j) (χ j))) := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact (hB j).2.2.2 _ fun x _ => ((hB i).2.2.2 _ fun y _ => hrho i j hij x y).symm
  obtain ⟨p1, p2, p3⟩ := pr_props Z r (fun i => eigL μ (w i) (J i) (χ i)) (fun i => (hB i).1) hcom hs
  have hle : ∀ i, eigL μ (w i) (J i) (χ i) ≤ fixL μ (w i) (kerChr (J i) (χ i) (hc i)) := fun i v hv => by
    refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 : rhoL μ (w i) x v = χ i x • v := by
      simpa [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] using
        (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv x) hx.1
    have h2 : χ i x = 1 := hx.2
    rw [h2, one_smul] at h1
    exact h1
  refine tr_main (Z := Z) _ R (inf_le_inf_left Z (iInf_mono hle)) inf_le_left hR
    (fun u hu => Submodule.mem_inf.2 ⟨p1 u hu, p2 u⟩) fun u y hy => p3 u y (Submodule.mem_inf.1 hy).2
