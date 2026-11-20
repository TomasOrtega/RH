import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CompactLoweringSpanDiagStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.GeneratedSubStable

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m f`. Simplify using `only [diagE, sgE_cpT, eT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply, map_add, tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, map_smul]`. Consider the case `add y y' hy hy'`.

Rewrite using `[map_add, map_add, hy, hy', map_add, map_add, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem tco_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) =
      E a b (tcoef ((fockBasis n).coord s) y) +
        tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [diagE, sgE_cpT, eT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      LinearMap.id_apply, map_add, tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, map_smul]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, map_add, map_add]
    abel

/- English proof (translation)
Rewrite using `[tco_diagE, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a a) y]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single s]`. Simplify using `[fockBasis_wt]`. Introduce `b _ hb`.

Simplify using `[fockBasis_wt, Finsupp.single_apply, hb]`. Simplify using the standard rewrite rules.
-/
theorem tco_diagE_wt (E : Fin n → Fin n → Module.End ℂ N) (a : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a y) =
      E a a (tcoef ((fockBasis n).coord s) y) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
  rw [tco_diagE, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a a) y]
  congr 1
  rw [Finset.sum_eq_single s]
  · simp [fockBasis_wt]
  · intro b _ hb
    simp [fockBasis_wt, Finsupp.single_apply, hb]
  · simp

end T

/- English proof (translation)
Unfold `modeChar modeWt`. Distinguish the cases in `h : IsPhys ε x`. Rewrite using `[if_pos h, if_pos (show ε x.1 = true ∧ ε x.2 = false from h), Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [root, Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Complex.conj_ofReal, Complex.conj_I]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg (show ¬(ε x.1 = true ∧ ε x.2 = false) from h)]`. Simplify using the standard rewrite rules.
-/
theorem modeChar_exp (θ : Fin n → ℝ) (x : Fin n × Fin n) :
    modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, modeWt ε x a * θ a : ℝ) : ℂ) * Complex.I) := by
  unfold modeChar modeWt
  by_cases h : IsPhys ε x
  · rw [if_pos h, if_pos (show ε x.1 = true ∧ ε x.2 = false from h), Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [root, Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [if_neg h, if_neg (show ¬(ε x.1 = true ∧ ε x.2 = false) from h)]
    simp

/- English proof (translation)
Simplify using `only [modeChar_exp]`. Rewrite using `[← Complex.exp_sum]`. Use `congr 1`. Rewrite using `[← Finset.sum_mul, ← Complex.ofReal_sum]`. Use `congr 2`.

Simplify using `only [fockWt, Finset.sum_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem prod_modeChar_exp (θ : Fin n → ℝ) (s : Finset (Fin (n * n))) :
    ∏ m ∈ s, modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (finProdFinEquiv.symm m) =
      Complex.exp (((∑ a, fockWt ε s a * θ a : ℝ) : ℂ) * Complex.I) := by
  simp only [modeChar_exp]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  simp only [fockWt, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
The claim follows from `bwt_diag_mem_Kset ε θ`.
-/
theorem diag_mem_Kset' (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε :=
  bwt_diag_mem_Kset ε θ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
Apply `coordH_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Rewrite using `[map_smul, Pi.smul_apply, coordH_apply, coordH_apply, tco_wK]`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one, prod_modeChar_exp]`.

Establish `hts : ∀ a, E a a (tcoef ((fockBasis n).coord s) y) = (((μ - fockWt ε s) a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y`. Introduce `a`. Establish `h` using `congrArg (tcoef ((fockBasis n).coord s)) (hy a)`. Rewrite `h` using `[tco_diagE_wt, map_smul]`. Rewrite using `[Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h]`.

Normalize the expressions using the abelian group laws. Establish `hw` using `(isWtOn_iff hσ hD (tcoef ((fockBasis n).coord s) y) (μ - fockWt ε s)).2 hts θ (bwt_diag_mem_Kset ε θ)`. Rewrite using `[Submodule.coe_smul]`. Express the relevant statement in the definitionally equal form `_ • σ _ _ = _`. Rewrite using `[hw, smul_smul, ← Complex.exp_add]`.

Use `congr 2`. Use `push_cast`. Simplify using `only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`.

Rewrite using `[ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg hb, smul_zero, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem wK_diag_wt (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)} (hy : ∀ a, diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y)
    (θ : Fin n → ℝ) :
    wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y := by
  apply coordH_injective
  funext s
  rw [map_smul, Pi.smul_apply, coordH_apply, coordH_apply, tco_wK]
  rw [Finset.sum_eq_single s]
  · rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, prod_modeChar_exp]
    have hts : ∀ a, E a a (tcoef ((fockBasis n).coord s) y) =
        (((μ - fockWt ε s) a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hy a)
      rw [tco_diagE_wt, map_smul] at h
      rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hw := (isWtOn_iff hσ hD (tcoef ((fockBasis n).coord s) y) (μ - fockWt ε s)).2 hts θ
      (bwt_diag_mem_Kset ε θ)
    rw [Submodule.coe_smul]
    change _ • σ _ _ = _
    rw [hw, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  · intro b _ hb
    rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_neg hb, smul_zero, zero_smul]
  · simp

/- English proof (translation)
Use `⟨bwtDiag_inG ε θ, ?_⟩` and prove the remaining obligations. Unfold `bwtDiag Jm`. Rewrite using `[diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bwtDiag_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) : inK ε (bwtDiag θ) := by
  refine ⟨bwtDiag_inG ε θ, ?_⟩
  unfold bwtDiag Jm
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  ring

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem wK_congr (hD : IsDerivedOn ε σ D E) {k k' : Matrix (Fin n) (Fin n) ℂ} (h : k = k')
    (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) (y : TensorProduct ℂ D (Fock n)) :
    wK hD hk y = wK hD hk' y := by
  subst h
  rfl

/- English proof (translation)
Use `set θ : Fin n → ℝ := Pi.single a 1 with hθ`. Establish `hX` using `bwtDiag_inK ε θ`. Establish `hcurve : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) = Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I) • coordH y`. Introduce `t`. Rewrite using `[wK_congr hD (bwt_exp θ t) _ (diag_mem_Kset' ε (fun b => t * θ b)), hy, map_smul]`.

Use `congr 4`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)]`. Simplify using `[hθ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hder1 : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y)) (coordH (actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y)) 0` using `hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s`.

Establish `he : HasDerivAt (fun t : ℝ => Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I)) (((μ a : ℝ) : ℂ) * Complex.I) 0`. Establish `h1 : HasDerivAt (fun t : ℝ => ((t * μ a : ℝ) : ℂ)) ((1 * μ a : ℝ) : ℂ) 0` using `((hasDerivAt_id (0 : ℝ)).mul_const (μ a)).ofReal_comp`. Establish `h2` using `(h1.mul_const Complex.I).cexp`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.

Establish `hder2` using `he.smul_const (coordH y)`. Rewrite `hder1` using `[funext hcurve]`. Establish `heq` using `hder1.unique hder2`. Establish `h2 : actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y = (((μ a : ℝ) : ℂ) * Complex.I) • y` using `coordH_injective (by rw [heq, map_smul])`. Rewrite `h2` using `[bwtDiag, bwt_actM_diag, LinearMap.sum_apply, Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)]`.

Simplify using `only [hθ, Pi.single_eq_same, Complex.ofReal_one, one_mul, LinearMap.smul_apply] at h2`. Establish `h3` using `congrArg (fun v => (-Complex.I) • v) h2`. Simplify using `only [smul_smul] at h3`. Establish `hI : -Complex.I * Complex.I = 1` using `by rw [neg_mul, Complex.I_mul_I, neg_neg]`. Establish `hI' : -Complex.I * (((μ a : ℝ) : ℂ) * Complex.I) = ((μ a : ℝ) : ℂ)`.

Take the linear combination `(-((μ a : ℝ) : ℂ)) * Complex.I_mul_I`. Rewrite `h3` using `[hI, one_smul, hI']`. Conclude with `h3`.
-/
theorem diagE_wt_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)}
    (hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y)
    (a : Fin n) : diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y := by
  set θ : Fin n → ℝ := Pi.single a 1 with hθ
  have hX := bwtDiag_inK ε θ
  have hcurve : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) =
      Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I) • coordH y := by
    intro t
    rw [wK_congr hD (bwt_exp θ t) _ (diag_mem_Kset' ε (fun b => t * θ b)), hy, map_smul]
    congr 4
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)]
    simp [hθ]
    ring
  have hder1 : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have he : HasDerivAt (fun t : ℝ => Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I))
      (((μ a : ℝ) : ℂ) * Complex.I) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((t * μ a : ℝ) : ℂ)) ((1 * μ a : ℝ) : ℂ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const (μ a)).ofReal_comp
    have h2 := (h1.mul_const Complex.I).cexp
    convert h2 using 1
    simp
  have hder2 := he.smul_const (coordH y)
  rw [funext hcurve] at hder1
  have heq := hder1.unique hder2
  have h2 : actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y = (((μ a : ℝ) : ℂ) * Complex.I) • y :=
    coordH_injective (by rw [heq, map_smul])
  rw [bwtDiag, bwt_actM_diag, LinearMap.sum_apply,
    Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)] at h2
  simp only [hθ, Pi.single_eq_same, Complex.ofReal_one, one_mul, LinearMap.smul_apply] at h2
  have h3 := congrArg (fun v => (-Complex.I) • v) h2
  simp only [smul_smul] at h3
  have hI : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hI' : -Complex.I * (((μ a : ℝ) : ℂ) * Complex.I) = ((μ a : ℝ) : ℂ) := by
    linear_combination (-((μ a : ℝ) : ℂ)) * Complex.I_mul_I
  rw [hI, one_smul, hI'] at h3
  exact h3

section Orth

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `horth : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → tform y (lowWord A z l) = 0`. Introduce `l hl`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, μ a ≠ lowWt γ l a := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne l hl (funext h)`. Establish `h1` using `hA a y (lowWord A z l)`. Rewrite `h1` using `[hμ a, lowerWord_weight hK hz.1 l hl a, tensorForm_smul_left, tform_smul_right, Complex.star_def, Complex.conj_ofReal]`.

Establish `h2 : (((μ a : ℝ) : ℂ) - ((lowWt γ l a : ℝ) : ℂ)) * tform y (lowWord A z l) = 0`. Rewrite using `[sub_mul, h1, sub_self]`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast sub_eq_zero.1 h) ha`. Conclude with `h`.

Establish `hall : ∀ w ∈ kLowSpan ε A z, tform y w = 0`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`.

Conclude with `horth l hl`. Consider the case `zero => simp [tform]`. Consider the case `add x x' _ _ hx hx' => rw [tform_add_right, hx, hx', add_zero]`. Consider the case `smul c x _ hx => rw [tform_smul_right, hx, mul_zero]`. Use `tform_self_re_pos hy0` as an intermediate fact.

Rewrite `this` using `[hall y hy]`. Simplify using `at this`.
-/
theorem kLow_wt_eq_lowWt {A : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))}
    (hK : Formalism.REAL.KRel ε A)
    (hA : ∀ (a : Fin n) (y y' : TensorProduct ℂ M (Fock n)), tform (A a a y) y' = tform y (A a a y'))
    {γ : Fin n → ℝ} {z : TensorProduct ℂ M (Fock n)} (hz : IsKHWVec ε A γ z)
    {y : TensorProduct ℂ M (Fock n)} (hy : y ∈ kLowSpan ε A z) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a y = ((μ a : ℝ) : ℂ) • y) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ μ = lowWt γ l := by
  by_contra hne
  push Not at hne
  have horth : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → tform y (lowWord A z l) = 0 := by
    intro l hl
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ lowWt γ l a := by
      by_contra h
      push Not at h
      exact hne l hl (funext h)
    have h1 := hA a y (lowWord A z l)
    rw [hμ a, lowerWord_weight hK hz.1 l hl a, tensorForm_smul_left, tform_smul_right, Complex.star_def,
      Complex.conj_ofReal] at h1
    have h2 : (((μ a : ℝ) : ℂ) - ((lowWt γ l a : ℝ) : ℂ)) * tform y (lowWord A z l) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h) ha
    · exact h
  have hall : ∀ w ∈ kLowSpan ε A z, tform y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact horth l hl
    | zero => simp [tform]
    | add x x' _ _ hx hx' => rw [tform_add_right, hx, hx', add_zero]
    | smul c x _ hx => rw [tform_smul_right, hx, mul_zero]
  have := tform_self_re_pos hy0
  rw [hall y hy] at this
  simp at this

end Orth

/- English proof (translation)
The claim follows from `| [], _ => ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [lowWt]⟩ | p :: l, hl => by obtain ⟨c, hc, heq⟩ := cdom_lowWt γ l fun q hq => hl q (List.mem_cons_of_mem _ hq) obtain ⟨c0, d0⟩ := p have hp : IsKLow ε (c0, d0) := hl _ (List.mem_cons_self ..) refine ⟨fun a b => c a b + …`.
-/
theorem cdom_lowWt (γ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → Formalism.MainNotions.S.CDom ε (lowWt γ l) γ
  | [], _ => ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [lowWt]⟩
  | p :: l, hl => by
    obtain ⟨c, hc, heq⟩ := cdom_lowWt γ l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨c0, d0⟩ := p
    have hp : IsKLow ε (c0, d0) := hl _ (List.mem_cons_self ..)
    refine ⟨fun a b => c a b + if a = d0 ∧ b = c0 then 1 else 0, ?_, ?_⟩
    · intro a b h
      by_cases h' : a = d0 ∧ b = c0
      · obtain ⟨rfl, rfl⟩ := h'
        exact ⟨hp.1, hp.2.symm⟩
      · dsimp only at h
        rw [if_neg h', add_zero] at h
        exact hc a b h
    · have hs : (∑ a, ∑ b, (((if a = d0 ∧ b = c0 then 1 else 0 : ℕ)) : ℝ) • Formalism.REAL.root a b) =
          Formalism.REAL.root d0 c0 := by
        rw [Finset.sum_eq_single d0 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [ha]) (by simp),
          Finset.sum_eq_single c0 (fun b _ hb => by simp [hb]) (by simp)]
        simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, hs, ← heq, lowWt]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, root, Formalism.REAL.root]
      ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
