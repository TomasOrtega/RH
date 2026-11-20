import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.AdmissibleHermitianColumns

namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `hre : (τ.1 X.κ0).re = 0`. Establish `h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0)`. Establish `hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0` using `X.ξ0_im`. Rewrite using `[← emb_cc']`. Apply the tactic sequence `rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]`.

Use `congrArg Complex.re h1` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.

Establish `hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im|` using `by conv_lhs => rw [hz]`. Simplify using the standard rewrite rules. Establish `hnorm : ‖τ.1 X.κ0‖ = X.c τ`. Unfold `Data.c`. Apply the tactic sequence `rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]`.

Establish `him` using `X.κ0_sign τ`. Rewrite `hnorm` using `[hn, abs_of_neg him]`. Rewrite using `[hz, ← hnorm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma emb_kappa (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring

/- English proof (translation)
Use `set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw`. Establish `hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w`. Introduce `γ`. Use extensionality with `a b`. Simplify using `only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, hw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ∑ j, w j * ξ j = 0`. Rewrite using `[← hξ]`. Unfold `herm`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [hw, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0`. Use extensionality with `a b`.

Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Use `_ = 0 := by rw [h0, mul_zero]`.

Rewrite using `[hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA, smul_zero, add_zero, add_smul]`. Normalize the expressions using the abelian group laws.
-/
lemma transvMat_mul (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[transvMat, Matrix.one_apply]`.
-/
lemma transvMat_zero (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [transvMat_zero]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ih, transvMat_mul G hξ]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma transvMat_pow (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α : E) (n : ℕ) : transvMat G ξ α ^ n = transvMat G ξ (n * α) := by
  induction n with
  | zero => simp [transvMat_zero]
  | succ k ih =>
    rw [pow_succ, ih, transvMat_mul G hξ]
    congr 1
    push_cast
    ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring`.
-/
lemma transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by
  ext a b
  simp only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]
  split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring

variable (X : Data E r)

def cR (p : X.Ψ → ℝ) : X.Ψ → ℂ := fun τ => (p τ : ℂ)

/- English proof (translation)
Establish `h0` using `(flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)`. Establish `e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im`. Use function extensionality and compare the values at `τ`. Simplify using `[cR]`. Rewrite using `[flow_mem_dom_iff X hξ y hy, e]`.

Conclude with `h0`.
-/
lemma flow_real_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (y : Frame X.Ψ r)
    (hy : y ∈ X.dom) : X.flow ξ (cR X p) y ∈ X.dom := by
  have h0 := (flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)
  have e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im := by
    funext τ
    simp [cR]
  rw [flow_mem_dom_iff X hξ y hy, e]
  exact h0

/- English proof (translation)
Establish `h1 : X.χ la 1 = 1`. Take `⟨N, hN, hfin⟩` from `X.χ_fin la`. Establish `hne : X.χ la 1 ≠ 0`. Introduce `h`. Use `hfin 1 X.Γ.one_mem` as an intermediate fact.

Rewrite `this` using `[h, zero_pow hN.ne']`. Conclude with `zero_ne_one this`. Establish `hsq` using `X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem`. Rewrite `hsq` using `[mul_one]`. Conclude with `mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)`.

Proceed by induction on `n with`. Consider the case `zero => simp [h1]`. Consider the case `succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]`.
-/
lemma chi_pow (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]

/- English proof (translation)
Take `⟨γ0, hγ0, hγ0m⟩` from `X.transv ξ hξΛ hξ a ha hai`. Establish `hγ : γ0 ^ X.chiOrd la ∈ X.Γ` using `X.Γ.pow_mem hγ0 _`. Establish `hχ : X.χ la (γ0 ^ X.chiOrd la) = 1`. Rewrite using `[chi_pow X la hγ0]`. Conclude with `(X.χ_fin la).choose_spec.2 γ0 hγ0`.

Establish `hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0))`. Rewrite using `[Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]`. Establish `hlact : lact (γ0 ^ X.chiOrd la) y = X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y`. Use function extensionality and compare the values at `τ`. Establish `hta : τ.1 a = ((τ.1 a).re : ℂ)`.

Establish `h` using `emb_cc' τ.1 a`. Rewrite `h` using `[ha]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use `congrArg Complex.im h` as an intermediate fact.

Simplify using `at this`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) = -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ)`. Rewrite using `[map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]`.

Use `conv_lhs => rw [hta]`. Simplify using `only [cR]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [lact, Data.flow]`.

Rewrite using `[hmat, transvMat_map X ξ τ _ _ hs]`. Rewrite using `[← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]`.
-/
lemma sec_periodic_gen (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a)
    (y : Frame X.Ψ r) (hy : y ∈ X.dom) :
    P (X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y) = P y := by
  obtain ⟨γ0, hγ0, hγ0m⟩ := X.transv ξ hξΛ hξ a ha hai
  have hγ : γ0 ^ X.chiOrd la ∈ X.Γ := X.Γ.pow_mem hγ0 _
  have hχ : X.χ la (γ0 ^ X.chiOrd la) = 1 := by
    rw [chi_pow X la hγ0]
    exact (X.χ_fin la).choose_spec.2 γ0 hγ0
  have hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) := by
    rw [Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]

  have hlact : lact (γ0 ^ X.chiOrd la) y =
      X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y := by
    funext τ
    have hta : τ.1 a = ((τ.1 a).re : ℂ) := by
      have h := emb_cc' τ.1 a
      rw [ha] at h
      apply Complex.ext
      · simp
      · have := congrArg Complex.im h
        simp at this
        simp
        linarith
    have hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) =
        -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ) := by
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]
      conv_lhs => rw [hta]
      simp only [cR]
      push_cast
      ring
    simp only [lact, Data.flow]
    rw [hmat, transvMat_map X ξ τ _ _ hs]
  rw [← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[cR]`.
-/
lemma cR_add (p q : X.Ψ → ℝ) : cR X (p + q) = cR X p + cR X q := by
  funext τ
  simp [cR]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[cR]`.
-/
lemma cR_neg (p : X.Ψ → ℝ) : cR X (-p) = -cR X p := by
  funext τ
  simp [cR]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[cR]`.
-/
lemma cR_zero : cR X 0 = 0 := by
  funext τ
  simp [cR]

/- English proof (translation)
Proceed by induction on `hp using AddSubgroup.closure_induction with`. Consider the case `mem p hp`. Take `⟨a, ha, hai, rfl⟩` from `hp`. Conclude with `fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy`. Consider the case `zero`.

Introduce `y _`. Rewrite using `[cR_zero, flow_zero]`. Consider the case `add p q _ _ hp hq`. Introduce `y hy`. Rewrite using `[cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]`.

Consider the case `neg p _ hp`. Introduce `y hy`. Establish `hz` using `flow_real_mem_dom X hξ (-p) y hy`. Establish `e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y`. Rewrite using `[flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]`.

Rewrite using `[← hp _ hz, e]`.
-/
lemma sec_periodic (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) :
    ∀ y ∈ X.dom, P (X.flow ξ (cR X p) y) = P y := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨a, ha, hai, rfl⟩ := hp
    exact fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy
  | zero =>
    intro y _
    rw [cR_zero, flow_zero]
  | add p q _ _ hp hq =>
    intro y hy
    rw [cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]
  | neg p _ hp =>
    intro y hy
    have hz := flow_real_mem_dom X hξ (-p) y hy
    have e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y := by
      rw [flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]
    rw [← hp _ hz, e]

end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
