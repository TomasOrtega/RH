import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.RepOne
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TensF
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TensHt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.WordHt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

section SlopeTestRemainingChoices
open scoped Pointwise
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Establish `h1 : (Function.mulSupport fun v => if v ∈ s then 1 else g v).Finite` using `hg.subset fun v hv => by`. Distinguish the cases in `h : v ∈ s`. Simplify using `[h] at hv`. Simplify `hv` using `[h]`. Establish `h2 : (Function.mulSupport fun v => if v ∈ s then g v else 1) ⊆ s` using `fun v hv => by`.

Assume the negation of the conclusion as `h`. Establish `h' : v ∉ s` using `h`. Simplify using `[h'] at hv`. Establish `h3 : ∏ v ∈ s, g v = ∏ᶠ v, if v ∈ s then g v else 1`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ h2]`.

Conclude with `Finset.prod_congr rfl fun v hv => by simp [hv]`. Rewrite using `[h3, ← finprod_mul_distrib h1 (s.finite_toSet.subset h2)]`. Apply the tactic sequence `exact finprod_congr fun v => by by_cases h : v ∈ s <;> simp [h]`.
-/
private theorem fp_split {ι : Type} [DecidableEq ι] (g : ι → ℂ) (hg : (Function.mulSupport g).Finite) (s : Finset ι) :
    ∏ᶠ v, g v = (∏ᶠ v, if v ∈ s then 1 else g v) * ∏ v ∈ s, g v := by
  have h1 : (Function.mulSupport fun v => if v ∈ s then 1 else g v).Finite :=
    hg.subset fun v hv => by
      by_cases h : v ∈ s
      · simp [h] at hv
      · simpa [h] using hv
  have h2 : (Function.mulSupport fun v => if v ∈ s then g v else 1) ⊆ s := fun v hv => by
    by_contra h
    have h' : v ∉ s := h
    simp [h'] at hv
  have h3 : ∏ v ∈ s, g v = ∏ᶠ v, if v ∈ s then g v else 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset _ h2]
    exact Finset.prod_congr rfl fun v hv => by simp [hv]
  rw [h3, ← finprod_mul_distrib h1 (s.finite_toSet.subset h2)]
  exact finprod_congr fun v => by by_cases h : v ∈ s <;> simp [h]

/- English proof (translation)
Establish `h` using `Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n (finEmb K n x))`. Use `(h.union S.finite_toSet).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[Set.mem_union, not_or]`. Establish `h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion K) n` using `not_not.1 hc.1`.

Apply `hv` to reduce the goal to its premises. Simplify using `only [hf v hc.2]`. Conclude with `Set.indicator_of_mem (by exact h1) _`.
-/
private theorem fin_supp (S : Finset (Pl K)) (f : ∀ v : Pl K, GL (Fin n) (v.adicCompletion K) → ℂ)
    (hf : ∀ v ∉ S, f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set _).indicator 1) (x : AdelicGLn.FiniteAdelicGL K n) :
    (Function.mulSupport fun v => f v (cf v x)).Finite := by
  have h := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n (finEmb K n x))
  refine (h.union S.finite_toSet).subset fun v hv => ?_
  by_contra hc
  rw [Set.mem_union, not_or] at hc
  have h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion K) n := not_not.1 hc.1
  apply hv
  simp only [hf v hc.2]
  exact Set.indicator_of_mem (by exact h1) _

/- English proof (translation)
Unfold `cf`. Rewrite using `[map_mul, finAt_mul]`.
-/
private theorem cf_mul (w : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : cf w (x * y) = cf w x * cf w y := by
  unfold cf; rw [map_mul, finAt_mul]

/- English proof (translation)
Rewrite using `[cf_mul, cf, (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.1 w h, one_mul]`.
-/
private theorem cf_loc {v w : Pl K} (h : w ≠ v) (y) (x : AdelicGLn.FiniteAdelicGL K n) :
    cf w (AdelicGLn.localEmbedding v y * x) = cf w x := by
  rw [cf_mul, cf, (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.1 w h, one_mul]

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
private theorem cf_finPart (w : Pl K) (g : AdelicGLn.AdelicGL K n) : cf w (finPart K n g) = finAt w g := by
  ext i j
  rfl

/- English proof (translation)
Use `show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).1) w = 1`. Rewrite using `[AutomorphicForm.prodEquiv_finEmb, map_one]`. Both sides reduce to the same expression.
-/
private theorem infAt_finEmb' (w : InfinitePlace K) (x : AdelicGLn.FiniteAdelicGL K n) : infAt w (finEmb K n x) = 1 := by
  show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩`. Introduce and unpack `⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩`.

Conclude with `⟨a, ha, b, hb, rfl⟩`.
-/
private theorem iw_eq (w : Pl K) (ν : Fin n → ℤ) : iwCoset w ν =
    (GLnLocal.iwahori (w.adicCompletion K) n : Set _) * {Cartan.diagPow (w.adicCompletion K) n ν} *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set _) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/- English proof (translation)
Establish `hc : IsCompact (iwCoset w ν)`. Rewrite using `[iw_eq]`. Conclude with `((GLnLocal.isCompact_iwahori _ n).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ n)`. Establish `ho : IsOpen (iwCoset w ν)`. Rewrite using `[iw_eq]`.

Conclude with `(GLnLocal.isOpen_iwahori _ n).mul_left`. Use `⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ iwCoset w ν`. Conclude with `⟨_, ho, hx, fun y hy => by simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩`.

Conclude with `⟨_, hc.isClosed.isOpen_compl, hx, fun y hy => by`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩`.
-/
private theorem iw_test (w : Pl K) (ν : Fin n → ℤ) :
    IsLocallyConstant ((iwCoset w ν).indicator 1 : GL (Fin n) (w.adicCompletion K) → ℂ) ∧ HasCompactSupport ((iwCoset w ν).indicator 1 : GL (Fin n) (w.adicCompletion K) → ℂ) := by
  have hc : IsCompact (iwCoset w ν) := by
    rw [iw_eq]
    exact ((GLnLocal.isCompact_iwahori _ n).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ n)
  have ho : IsOpen (iwCoset w ν) := by
    rw [iw_eq]
    exact (GLnLocal.isOpen_iwahori _ n).mul_left
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ iwCoset w ν
  · exact ⟨_, ho, hx, fun y hy => by simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩

/- English proof (translation)
Establish `key : ∀ g ∈ GLnLocal.integralGL (w.adicCompletion K) n, Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det ≤ 1`. Introduce `g hg`. Rewrite `hg` using `[GLnLocal.mem_integralGL_iff]`. Simplify using `only [GroundTheory.Global.mem_valuationInteger_iff] at hg`. Rewrite using `[Matrix.det_apply']`.

Conclude with `(w.adicCompletionIntegers K).sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hg.1 _ _)`. Establish `h1` using `key g hg`. Establish `h2` using `key _ (inv_mem hg)`. Establish `h3 : Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det * Valued.v ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1`. Rewrite using `[← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem det_int (w : Pl K) {g : GL (Fin n) (w.adicCompletion K)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion K) n) :
    Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1 := by
  have key : ∀ g ∈ GLnLocal.integralGL (w.adicCompletion K) n,
      Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det ≤ 1 := by
    intro g hg
    rw [GLnLocal.mem_integralGL_iff] at hg
    simp only [GroundTheory.Global.mem_valuationInteger_iff] at hg
    rw [Matrix.det_apply']
    exact (w.adicCompletionIntegers K).sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hg.1 _ _)
  have h1 := key g hg
  have h2 := key _ (inv_mem hg)
  have h3 : Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det *
      Valued.v ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

/- English proof (translation)
Take `⟨a, ha, b, hb, rfl⟩` from `hg`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, det_int w (GLnLocal.iwahori_le_integralGL _ n ha), det_int w (GLnLocal.iwahori_le_integralGL _ n hb), Cartan.coe_diagPow, Matrix.det_diagonal]`. Establish `hz : ∀ (a : w.adicCompletion K), a ≠ 0 → ∀ s : Finset (Fin n), ∏ i ∈ s, a ^ ν i = a ^ ∑ i ∈ s, ν i`. Introduce `a ha s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]`. Rewrite using `[hz _ (Cartan.uniformizer_ne_zero _), hν]`. Simplify using the standard rewrite rules.
-/
private theorem det_iw (w : Pl K) {ν : Fin n → ℤ} (hν : ∑ i, ν i = 0) {g : GL (Fin n) (w.adicCompletion K)} (hg : g ∈ iwCoset w ν) :
    Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
    det_int w (GLnLocal.iwahori_le_integralGL _ n ha), det_int w (GLnLocal.iwahori_le_integralGL _ n hb), Cartan.coe_diagPow,
    Matrix.det_diagonal]
  have hz : ∀ (a : w.adicCompletion K), a ≠ 0 → ∀ s : Finset (Fin n), ∏ i ∈ s, a ^ ν i = a ^ ∑ i ∈ s, ν i := by
    intro a ha s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]
  rw [hz _ (Cartan.uniformizer_ne_zero _), hν]
  simp

/- English proof (translation)
Establish `hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion K) → ℝ)`. Unfold `locHeight`. Use `continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))` and prove the remaining obligations. Conclude with `(Units.continuous_val.matrix_elem _ _).nnnorm`. Conclude with `(Units.continuous_coe_inv.matrix_elem _ _).nnnorm`.

Take `⟨B, hB⟩` from `(hC.image hc).bddAbove`. Conclude with `⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩`.
-/
private theorem loc_bd (w : Pl K) {C : Set (GL (Fin n) (w.adicCompletion K))} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, locHeight g ≤ B := by
  have hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion K) → ℝ) := by
    unfold locHeight
    refine continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))
    · exact (Units.continuous_val.matrix_elem _ _).nnnorm
    · exact (Units.continuous_coe_inv.matrix_elem _ _).nnnorm
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

/- English proof (translation)
Establish `h` using `w.2`. Use `HeightOneSpectrum.ext ?_` and prove the remaining obligations. Establish `h2 : Ideal.under (𝓞 K) w.1.asIdeal = w.1.asIdeal` using `Ideal.comap_id _`. Conclude with `h2.symm.trans h.over.symm`.
-/
private theorem pl_self (q : Pl K) (w : PlacesOver K q) : w.1 = q := by
  have h := w.2
  refine HeightOneSpectrum.ext ?_
  have h2 : Ideal.under (𝓞 K) w.1.asIdeal = w.1.asIdeal := Ideal.comap_id _
  exact h2.symm.trans h.over.symm

/- English proof (translation)
Conclude with `HeightOneSpectrum.ext (Ideal.comap_id _)`.
-/
private theorem below_self (w : Pl K) : AdeleBaseChange.below K w = w := by
  exact HeightOneSpectrum.ext (Ideal.comap_id _)

/- English proof (translation)
Unfold `heightOff`. Establish `hi : (∏ w : InfinitePlace K, locHeight (infAt w (finEmb K n x)) ^ w.mult) = 1` using `Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]`. Rewrite using `[hi, one_mul]`. Establish `hg : ∀ w : Pl K, (∏ᶠ (_ : AdeleBaseChange.below K w ≠ q), locHeight (finAt w (finEmb K n x))) = if w ≠ q then locHeight (cf w x) else 1`. Introduce `w`.

Rewrite using `[below_self, finprod_eq_if]`. Both sides reduce to the same expression. Simplify using `only [hg]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := T)]`. Use `Finset.prod_le_prod (fun v _ => ?_) fun v hv => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `(locHeight_pos _).le`. Conclude with `zero_le_one`. Use `split_ifs with hq`. Conclude with `h1 v hq hv`.

Conclude with `hB v`. Introduce `v hv`. Assume the negation of the conclusion as `hc`. Apply `hv` to reduce the goal to its premises. Establish `hc' : v ∉ T` using `hc`.

Distinguish the cases in `hq : v = q`. Simplify using `[hq]`. Simplify using `only [ne_eq, hq, not_false_eq_true, if_true]`. Conclude with `h2 v hq hc'`.
-/
private theorem ht_le (q : Pl K) (T : Finset (Pl K)) (B : Pl K → ℝ) (hB : ∀ v, 1 ≤ B v) (x : AdelicGLn.FiniteAdelicGL K n)
    (h1 : ∀ v, v ≠ q → v ∈ T → locHeight (cf v x) ≤ B v) (h2 : ∀ v, v ≠ q → v ∉ T → locHeight (cf v x) = 1) :
    heightOff q (finEmb K n x) ≤ ∏ v ∈ T, B v := by
  classical
  unfold heightOff
  have hi : (∏ w : InfinitePlace K, locHeight (infAt w (finEmb K n x)) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]
  rw [hi, one_mul]
  have hg : ∀ w : Pl K, (∏ᶠ (_ : AdeleBaseChange.below K w ≠ q), locHeight (finAt w (finEmb K n x))) =
      if w ≠ q then locHeight (cf w x) else 1 := by
    intro w
    rw [below_self, finprod_eq_if]
    rfl
  simp only [hg]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
  · refine Finset.prod_le_prod (fun v _ => ?_) fun v hv => ?_
    · split_ifs
      · exact (locHeight_pos _).le
      · exact zero_le_one
    · split_ifs with hq
      · exact h1 v hq hv
      · exact hB v
  · intro v hv
    by_contra hc
    apply hv
    have hc' : v ∉ T := hc
    by_cases hq : v = q
    · simp [hq]
    · simp only [ne_eq, hq, not_false_eq_true, if_true]
      exact h2 v hq hc'

/- English proof (translation)
Distinguish the cases in `hx : x ∈ H`. Rewrite using `[Set.indicator_of_mem (show k * x ∈ (H : Set G) from mul_mem hk hx), Set.indicator_of_mem (show x ∈ (H : Set G) from hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show k * x ∉ (H : Set G) from fun h' => hx ((Subgroup.mul_mem_cancel_left _ hk).1 h')), Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]`.
-/
private theorem ind_inv {G : Type*} [Group G] (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    (H : Set G).indicator (1 : G → ℂ) (k * x) = (H : Set G).indicator 1 x := by
  by_cases hx : x ∈ H
  · rw [Set.indicator_of_mem (show k * x ∈ (H : Set G) from mul_mem hk hx), Set.indicator_of_mem (show x ∈ (H : Set G) from hx)]
    rfl
  · rw [Set.indicator_of_notMem (show k * x ∉ (H : Set G) from fun h' => hx ((Subgroup.mul_mem_cancel_left _ hk).1 h')),
      Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
end SlopeTestRemainingChoices
/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ q w₀ q₀ νF _ aF L ν hν 𝔣 h𝔣`. Take `⟨rfl, rfl, hS, hU, hg, hUq⟩` from `h𝔣`. Take `⟨q₁, hq₁⟩` from `q₀`. Take `rfl : q₁ = q` from `pl_self q ⟨q₁, hq₁⟩`. Establish `hqS : q₁ ∈ 𝔣.S` using `(hS _).2 (Or.inr rfl)`.

Establish `hLS : ∀ v ∈ L.S, v ∈ 𝔣.S` using `fun v hv => (hS v).2 (Or.inl hv)`. Take `⟨Y, hY1, hY⟩` from `wordHt F n hn 𝔣.ν 𝔣.a₀ 𝔣.smooth`. Take `⟨c, hc⟩` from `tensHt F F n hn q₁`. Use `⟨Y ^ c, one_le_pow₀ hY1, fun κ hκ p h hsph hoff => ?_⟩` and prove the remaining obligations. Establish `hκS : ∀ v ∈ κ, v ∉ L.S` using `fun v hv hv' => hκ v hv (hLS v hv')`.

Establish `hκq : ∀ v ∈ κ, v ≠ q₁` using `fun v hv hv' => hκ v hv (hv' ▸ hqS)`. Use `set T : Finset (Pl F) := L.S ∪ κ with hT`. Use `set ψ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ := fun v => if v ∈ L.S then L.f v else h v with hψ`. Establish `hψt : ∀ v ∈ T, IsLocallyConstant (ψ v) ∧ HasCompactSupport (ψ v)`. Introduce `v hv`.

Distinguish the cases in `hvS : v ∈ L.S`. Simplify using `only [hψ, hvS, if_true]`. Conclude with `⟨(L.test v hvS).2.2.1, (L.test v hvS).2.2.2⟩`. Establish `hvk : v ∈ κ` using `(Finset.mem_union.1 hv).resolve_left hvS`. Simplify using `only [hψ, hvS, if_false]`.

Use `(sphEx F n hn v).2.2 (p v) (h v) (hsph v hvk)` as an intermediate fact. Conclude with `⟨this.1, this.2.1⟩`. Establish `hBex : ∀ v, ∃ b : ℝ, 1 ≤ b ∧ (v ∈ T → ∀ g, ψ v g ≠ 0 → locHeight g ≤ b)`. Introduce `v`. Distinguish the cases in `hv : v ∈ T`.

Take `⟨b, hb1, hb⟩` from `loc_bd v (hψt v hv).2.isCompact`. Conclude with `⟨b, hb1, fun _ g hg => hb g (subset_tsupport _ hg)⟩`. Conclude with `⟨1, le_rfl, fun h' => absurd h' hv⟩`. Use `choose B hB1 hB using hBex`. Take `⟨C₁, hC₁, hC⟩` from `hc (∏ v ∈ T, B v) (Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun v _ => hB1 v)`.

Use `⟨C₁ * Y ^ (2 * c), one_le_mul_of_one_le_of_one_le hC₁ (one_le_pow₀ hY1), fun ev hev j wd φ hφS hφq hφo => ?_⟩` and prove the remaining obligations. Use `set s : Finset (Pl F) := insert q₁ κ with hs`. Establish `hφψ : ∀ v, v ≠ q₁ → φ v = ψ v`. Introduce `v hv`. Distinguish the cases in `hvS : v ∈ L.S`.

Simplify using `only [hψ, hvS, if_true]`. Conclude with `hφS v hvS`. Simplify using `only [hψ, hvS, if_false]`. Conclude with `hφo v hvS hv`. Establish `hφoff : ∀ v ∉ insert q₁ T, φ v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1`.

Introduce `v hv`. Rewrite `hv` using `[Finset.mem_insert, not_or]`. Establish `hvS : v ∉ L.S` using `fun h' => hv.2 (Finset.mem_union_left _ h')`. Establish `hvk : v ∉ κ` using `fun h' => hv.2 (Finset.mem_union_right _ h')`. Rewrite using `[hφo v hvS hv.1, hoff v hvk]`.

Establish `hφt : ∀ v ∈ insert q₁ T, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v)`. Introduce `v hv`. Distinguish the cases in `hvq : v = q₁`. Substitute `hvq` using the available equality. Rewrite using `[hφq]`.

Conclude with `iw_test _ _`. Rewrite using `[hφψ v hvq]`. Conclude with `hψt v ((Finset.mem_insert.1 hv).resolve_left hvq)`. Establish `hfoff : ∀ v ∉ insert q₁ L.S, L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1`. Introduce `v hv`.

Rewrite `hv` using `[Finset.mem_insert, not_or]`. Conclude with `(L.off v hv.2 hv.1).2.1`. Establish `hft : ∀ v ∈ insert q₁ L.S, IsLocallyConstant (L.f v) ∧ HasCompactSupport (L.f v)`. Introduce `v hv`. Distinguish the cases in `hvq : v = q₁`.

Substitute `hvq` using the available equality. Rewrite using `[L.at_q.2.1]`. Conclude with `iw_test _ _`. Use `L.test v ((Finset.mem_insert.1 hv).resolve_left hvq)` as an intermediate fact. Conclude with `⟨this.2.2.1, this.2.2.2⟩`.

Take `⟨e, -, he, hae⟩` from `avgF F n hn (insert q₁ T) (word 𝔣.ν 𝔣.a₀ (none :: wd)) φ hφt hφoff`. Take `⟨e₀, -, he₀, hae₀⟩` from `avgF F n hn (insert q₁ L.S) 𝔣.a₀ L.f hft hfoff`. Establish `hg₀ : 𝔣.g = tens 𝔣.a₀ e₀`. Use extensionality with `x`. Rewrite using `[hg x, hae₀ x]`.

Establish `hfs : ∀ x, (Function.mulSupport fun v => L.f v (cf v x)).Finite` using `fin_supp _ _ hfoff`. Establish `hφs : ∀ x, (Function.mulSupport fun v => φ v (cf v x)).Finite` using `fin_supp _ _ hφoff`. Use `set r : AdelicGLn.FiniteAdelicGL F n → ℂ := fun x => ∏ᶠ v, if v ∈ s then 1 else L.f v (cf v x) with hr`. Establish `hfree : ∀ w ∈ s, Free w r`. Introduce `w hw y x`.

Use `finprod_congr fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ s`. Simplify using `[hv]`. Establish `hvw : v ≠ w` using `fun h' => hv (h' ▸ hw)`. Simplify using `only [hv, if_false, cf_loc hvw]`.

Establish `hφr : ∀ v ∉ s, φ v = L.f v`. Introduce `v hv`. Rewrite `hv` using `[Finset.mem_insert, not_or]`. Distinguish the cases in `hvS : v ∈ L.S`. Conclude with `hφS v hvS`.

Rewrite using `[hφo v hvS hv.1, hoff v hv.2, (L.off v hvS hv.1).2.1]`. Establish `hkap : ∀ v ∈ κ, L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1` using `fun v hv => (L.off v (hκS v hv) (hκq v hv)).2.1`. Establish `hq₁κ : q₁ ∉ κ` using `fun h' => hκq _ h' rfl`. Establish `hform₀ : ∀ x, e₀ x = r x * (iwCoset q₁ 0).indicator 1 (cf q₁ x) * ∏ w ∈ κ, (GLnLocal.integralGL (w.adicCompletion F) n : Set _).indicator 1 (cf w x)`. Introduce `x`.

Rewrite using `[he₀, fp_split _ (hfs x) s, hs, Finset.prod_insert hq₁κ, L.at_q.2.1, mul_assoc]`. Use `congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun v hv => by rw [hkap v hv]))` and prove the remaining obligations. Establish `hform₁ : ∀ x, e x = r x * (iwCoset q₁ fun i => (j : ℤ) * ν i).indicator 1 (cf q₁ x) * ∏ w ∈ κ, h w (cf w x)`. Introduce `x`. Rewrite using `[he, fp_split _ (hφs x) s]`.

Establish `hrx : (∏ᶠ v, if v ∈ s then (1 : ℂ) else φ v (cf v x)) = r x` using `finprod_congr fun v => by`. Distinguish the cases in `hv : v ∈ s`. Simplify using `only [hv, if_true]`. Simplify using `only [hv, if_false]`. Rewrite using `[hφr v hv]`.

Rewrite using `[hrx, hs, Finset.prod_insert hq₁κ, hφq, mul_assoc]`. Use `congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun v hv => ?_))` and prove the remaining obligations. Rewrite using `[hφψ v (hκq v hv)]`. Simplify using `only [hψ, hκS v hv, if_false]`. Establish `hUc : ∀ u ∈ 𝔣.toAmp.U, cf q₁ u ∈ GLnLocal.iwahori (q₁.adicCompletion F) n ∧ ∀ x, r (u * x) = r x`.

Introduce `u hu`. Rewrite `hu` using `[hU]`. Establish `hu' : ∀ v, cf v u ∈ L.UF v` using `hu`. Use `⟨L.at_q.2.2.2 ▸ hu' q₁, fun x => finprod_congr fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ s`.

Simplify using `[hv]`. Simplify using `only [hv, if_false, cf_mul]`. Rewrite `hv` using `[Finset.mem_insert, not_or]`. Distinguish the cases in `hvS : v ∈ L.S`. Conclude with `(L.inv v hvS).2 _ (hu' v) _`.

Take `⟨-, h2, -, h4⟩` from `L.off v hvS hv.1`. Establish `hk : cf v u ∈ GLnLocal.integralGL (v.adicCompletion F) n` using `h4 ▸ hu' v`. Rewrite using `[h2]`. Conclude with `ind_inv _ hk _`. Establish `hne : ∀ x, e x ≠ 0 → ∀ v, φ v (cf v x) ≠ 0`.

Introduce `x hx v h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[he]`. Conclude with `finprod_eq_zero _ v h0 (hφs x)`. Establish `hsum : ∑ i, (fun i => (j : ℤ) * ν i) i = 0`.

Simplify using `only [← Finset.mul_sum, hν.2.1, mul_zero]`. Establish `hwq : ∀ x, e x ≠ 0 → cf q₁ x ∈ iwCoset q₁ (fun i => (j : ℤ) * ν i)`. Introduce `x hx`. Use `hne x hx q₁` as an intermediate fact. Rewrite `this` using `[hφq]`.

Conclude with `Set.mem_of_indicator_ne_zero this`. Establish `hsup` using `hC (word 𝔣.ν 𝔣.a₀ (none :: wd)) e (Y ^ (wd.length + 2)) (one_le_pow₀ hY1) (fun g hg => by simpa using hY (none :: wd) g hg) (fun x hx => ⟨?_, ?_⟩)`. Use `⟨tens (word 𝔣.ν 𝔣.a₀ (none :: wd)) e, hae, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hUq, hg₀]`. Conclude with `repOne F n hn μ 𝔣.toAmp ev hev q₁ hqS ν hν.1.antitone κ hκ p h hsph r (hfree q₁ (Finset.mem_insert_self _ _)) (fun w hw => hfree w (Finset.mem_insert_of_mem hw)) hUc j wd e₀ e hform₀ hform₁`.

Introduce `g hfg`. Take `⟨h1, h2⟩` from `hsup g hfg`. Use `⟨h1.trans (le_of_eq ?_), ?_, fun w hw => absurd (Subtype.ext (pl_self q₁ w)) hw⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← cf_finPart]`. Conclude with `hwq _ h2`. Use `ht_le q₁ T B hB1 x (fun v hvq hvT => hB v hvT _ ?_) (fun v hvq hvT => ?_)` and prove the remaining obligations. Rewrite using `[← hφψ v hvq]`.

Conclude with `hne x hx v`. Establish `h1` using `hne x hx v`. Rewrite `h1` using `[hφoff v (by simp [hvq, hvT])]`. Conclude with `locHeight_eq_one_of_mem_integralGL (Set.mem_of_indicator_ne_zero h1)`. Introduce `w`.

Take `⟨w, hw⟩` from `w`. Take `rfl : w = q₁` from `pl_self q₁ ⟨w, hw⟩`. Conclude with `det_iw _ hsum (hwq x hx)`.
-/
theorem UpperTheory.ConvolutionTheory.GM.termF :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL F n)) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q) (q₀ : PlacesOver F q)
      (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aF : TI F n) (L : Loc σ n q w₀) (ν : Fin n → ℤ), Good ν →
    ∀ 𝔣 : Side (Twist.id μ) (Module.finrank F E), IsSideF L νF aF ν 𝔣 → ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ κ : Finset (Pl F), (∀ w ∈ κ, w ∉ 𝔣.S) →
    ∀ (p : Pl F → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl F, GL (Fin n) (w.adicCompletion F) → ℂ), (∀ w ∈ κ, IsSph w (p w) (h w)) →
      (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion F) n : Set _).indicator 1) → ∃ Y₁ : ℝ, 1 ≤ Y₁ ∧
    ∀ ev, 𝔣.toAmp.IsEv ev → ∀ (j : ℕ) (wd : List (Option (Ix F n))) (φ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ),
      (∀ v ∈ L.S, φ v = L.f v) → φ q = (iwCoset q fun i => (j : ℤ) * ν i).indicator 1 → (∀ v ∉ L.S, v ≠ q → φ v = h v) →
      ∃ f : TG F n, (∀ x, f x = avg (tensF (onInf (word νF aF (none :: wd))) φ) x) ∧
        Rop μ f = 𝔣.toAmp.A ∘L (ev (C (mono wd) * map C (∏ w ∈ κ, atPl w (p w))) ∘L 𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∧
        Sup q₀ ν j (Y₁ * Y₀ ^ wd.length) f := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ q w₀ q₀ νF _ aF L ν hν 𝔣 h𝔣
  obtain ⟨rfl, rfl, hS, hU, hg, hUq⟩ := h𝔣
  obtain ⟨q₁, hq₁⟩ := q₀
  obtain rfl : q₁ = q := pl_self q ⟨q₁, hq₁⟩
  have hqS : q₁ ∈ 𝔣.S := (hS _).2 (Or.inr rfl)
  have hLS : ∀ v ∈ L.S, v ∈ 𝔣.S := fun v hv => (hS v).2 (Or.inl hv)
  obtain ⟨Y, hY1, hY⟩ := wordHt F n hn 𝔣.ν 𝔣.a₀ 𝔣.smooth
  obtain ⟨c, hc⟩ := tensHt F F n hn q₁
  refine ⟨Y ^ c, one_le_pow₀ hY1, fun κ hκ p h hsph hoff => ?_⟩
  have hκS : ∀ v ∈ κ, v ∉ L.S := fun v hv hv' => hκ v hv (hLS v hv')
  have hκq : ∀ v ∈ κ, v ≠ q₁ := fun v hv hv' => hκ v hv (hv' ▸ hqS)
  set T : Finset (Pl F) := L.S ∪ κ with hT
  set ψ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ := fun v => if v ∈ L.S then L.f v else h v with hψ
  have hψt : ∀ v ∈ T, IsLocallyConstant (ψ v) ∧ HasCompactSupport (ψ v) := by
    intro v hv
    by_cases hvS : v ∈ L.S
    · simp only [hψ, hvS, if_true]
      exact ⟨(L.test v hvS).2.2.1, (L.test v hvS).2.2.2⟩
    · have hvk : v ∈ κ := (Finset.mem_union.1 hv).resolve_left hvS
      simp only [hψ, hvS, if_false]
      have := (sphEx F n hn v).2.2 (p v) (h v) (hsph v hvk)
      exact ⟨this.1, this.2.1⟩
  have hBex : ∀ v, ∃ b : ℝ, 1 ≤ b ∧ (v ∈ T → ∀ g, ψ v g ≠ 0 → locHeight g ≤ b) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨b, hb1, hb⟩ := loc_bd v (hψt v hv).2.isCompact
      exact ⟨b, hb1, fun _ g hg => hb g (subset_tsupport _ hg)⟩
    · exact ⟨1, le_rfl, fun h' => absurd h' hv⟩
  choose B hB1 hB using hBex
  obtain ⟨C₁, hC₁, hC⟩ := hc (∏ v ∈ T, B v) (Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun v _ => hB1 v)
  refine ⟨C₁ * Y ^ (2 * c), one_le_mul_of_one_le_of_one_le hC₁ (one_le_pow₀ hY1), fun ev hev j wd φ hφS hφq hφo => ?_⟩
  set s : Finset (Pl F) := insert q₁ κ with hs
  have hφψ : ∀ v, v ≠ q₁ → φ v = ψ v := by
    intro v hv
    by_cases hvS : v ∈ L.S
    · simp only [hψ, hvS, if_true]; exact hφS v hvS
    · simp only [hψ, hvS, if_false]; exact hφo v hvS hv
  have hφoff : ∀ v ∉ insert q₁ T, φ v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    have hvS : v ∉ L.S := fun h' => hv.2 (Finset.mem_union_left _ h')
    have hvk : v ∉ κ := fun h' => hv.2 (Finset.mem_union_right _ h')
    rw [hφo v hvS hv.1, hoff v hvk]
  have hφt : ∀ v ∈ insert q₁ T, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v) := by
    intro v hv
    by_cases hvq : v = q₁
    · subst hvq
      rw [hφq]
      exact iw_test _ _
    · rw [hφψ v hvq]
      exact hψt v ((Finset.mem_insert.1 hv).resolve_left hvq)
  have hfoff : ∀ v ∉ insert q₁ L.S, L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    exact (L.off v hv.2 hv.1).2.1
  have hft : ∀ v ∈ insert q₁ L.S, IsLocallyConstant (L.f v) ∧ HasCompactSupport (L.f v) := by
    intro v hv
    by_cases hvq : v = q₁
    · subst hvq
      rw [L.at_q.2.1]
      exact iw_test _ _
    · have := L.test v ((Finset.mem_insert.1 hv).resolve_left hvq)
      exact ⟨this.2.2.1, this.2.2.2⟩
  obtain ⟨e, -, he, hae⟩ := avgF F n hn (insert q₁ T) (word 𝔣.ν 𝔣.a₀ (none :: wd)) φ hφt hφoff
  obtain ⟨e₀, -, he₀, hae₀⟩ := avgF F n hn (insert q₁ L.S) 𝔣.a₀ L.f hft hfoff
  have hg₀ : 𝔣.g = tens 𝔣.a₀ e₀ := by
    ext x
    rw [hg x, hae₀ x]
  have hfs : ∀ x, (Function.mulSupport fun v => L.f v (cf v x)).Finite := fin_supp _ _ hfoff
  have hφs : ∀ x, (Function.mulSupport fun v => φ v (cf v x)).Finite := fin_supp _ _ hφoff
  set r : AdelicGLn.FiniteAdelicGL F n → ℂ := fun x => ∏ᶠ v, if v ∈ s then 1 else L.f v (cf v x) with hr
  have hfree : ∀ w ∈ s, Free w r := by
    intro w hw y x
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ s
    · simp [hv]
    · have hvw : v ≠ w := fun h' => hv (h' ▸ hw)
      simp only [hv, if_false, cf_loc hvw]
  have hφr : ∀ v ∉ s, φ v = L.f v := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    by_cases hvS : v ∈ L.S
    · exact hφS v hvS
    · rw [hφo v hvS hv.1, hoff v hv.2, (L.off v hvS hv.1).2.1]
  have hkap : ∀ v ∈ κ, L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 :=
    fun v hv => (L.off v (hκS v hv) (hκq v hv)).2.1
  have hq₁κ : q₁ ∉ κ := fun h' => hκq _ h' rfl
  have hform₀ : ∀ x, e₀ x = r x * (iwCoset q₁ 0).indicator 1 (cf q₁ x) *
      ∏ w ∈ κ, (GLnLocal.integralGL (w.adicCompletion F) n : Set _).indicator 1 (cf w x) := by
    intro x
    rw [he₀, fp_split _ (hfs x) s, hs, Finset.prod_insert hq₁κ, L.at_q.2.1, mul_assoc]
    refine congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun v hv => by rw [hkap v hv]))
  have hform₁ : ∀ x, e x = r x * (iwCoset q₁ fun i => (j : ℤ) * ν i).indicator 1 (cf q₁ x) * ∏ w ∈ κ, h w (cf w x) := by
    intro x
    rw [he, fp_split _ (hφs x) s]
    have hrx : (∏ᶠ v, if v ∈ s then (1 : ℂ) else φ v (cf v x)) = r x := finprod_congr fun v => by
      by_cases hv : v ∈ s
      · simp only [hv, if_true]
      · simp only [hv, if_false]
        rw [hφr v hv]
    rw [hrx, hs, Finset.prod_insert hq₁κ, hφq, mul_assoc]
    refine congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun v hv => ?_))
    rw [hφψ v (hκq v hv)]
    simp only [hψ, hκS v hv, if_false]
  have hUc : ∀ u ∈ 𝔣.toAmp.U, cf q₁ u ∈ GLnLocal.iwahori (q₁.adicCompletion F) n ∧ ∀ x, r (u * x) = r x := by
    intro u hu
    rw [hU] at hu
    have hu' : ∀ v, cf v u ∈ L.UF v := hu
    refine ⟨L.at_q.2.2.2 ▸ hu' q₁, fun x => finprod_congr fun v => ?_⟩
    by_cases hv : v ∈ s
    · simp [hv]
    · simp only [hv, if_false, cf_mul]
      rw [Finset.mem_insert, not_or] at hv
      by_cases hvS : v ∈ L.S
      · exact (L.inv v hvS).2 _ (hu' v) _
      · obtain ⟨-, h2, -, h4⟩ := L.off v hvS hv.1
        have hk : cf v u ∈ GLnLocal.integralGL (v.adicCompletion F) n := h4 ▸ hu' v
        rw [h2]
        exact ind_inv _ hk _
  have hne : ∀ x, e x ≠ 0 → ∀ v, φ v (cf v x) ≠ 0 := by
    intro x hx v h0
    apply hx
    rw [he]
    exact finprod_eq_zero _ v h0 (hφs x)
  have hsum : ∑ i, (fun i => (j : ℤ) * ν i) i = 0 := by
    simp only [← Finset.mul_sum, hν.2.1, mul_zero]
  have hwq : ∀ x, e x ≠ 0 → cf q₁ x ∈ iwCoset q₁ (fun i => (j : ℤ) * ν i) := by
    intro x hx
    have := hne x hx q₁
    rw [hφq] at this
    exact Set.mem_of_indicator_ne_zero this
  have hsup := hC (word 𝔣.ν 𝔣.a₀ (none :: wd)) e (Y ^ (wd.length + 2)) (one_le_pow₀ hY1)
    (fun g hg => by simpa using hY (none :: wd) g hg) (fun x hx => ⟨?_, ?_⟩)
  · refine ⟨tens (word 𝔣.ν 𝔣.a₀ (none :: wd)) e, hae, ?_, ?_⟩
    · rw [hUq, hg₀]
      exact repOne F n hn μ 𝔣.toAmp ev hev q₁ hqS ν hν.1.antitone κ hκ p h hsph r (hfree q₁ (Finset.mem_insert_self _ _))
        (fun w hw => hfree w (Finset.mem_insert_of_mem hw)) hUc j wd e₀ e hform₀ hform₁
    · intro g hfg
      obtain ⟨h1, h2⟩ := hsup g hfg
      refine ⟨h1.trans (le_of_eq ?_), ?_, fun w hw => absurd (Subtype.ext (pl_self q₁ w)) hw⟩
      · rw [mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
        congr 2
        ring
      · rw [← cf_finPart]
        exact hwq _ h2
  · refine ht_le q₁ T B hB1 x (fun v hvq hvT => hB v hvT _ ?_) (fun v hvq hvT => ?_)
    · rw [← hφψ v hvq]; exact hne x hx v
    · have h1 := hne x hx v
      rw [hφoff v (by simp [hvq, hvT])] at h1
      exact locHeight_eq_one_of_mem_integralGL (Set.mem_of_indicator_ne_zero h1)
  · intro w
    obtain ⟨w, hw⟩ := w
    obtain rfl : w = q₁ := pl_self q₁ ⟨w, hw⟩
    exact det_iw _ hsum (hwq x hx)
