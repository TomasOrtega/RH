import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForEveryTwist

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this`. Establish `h2 : t * (A i j - B i j) = 0` using `by rw [mul_sub, this, sub_self]`. Conclude with `sub_eq_zero.mp (ht _ h2)`.
-/
lemma mat_cancel {OC : Type} [CommRing OC] {r : ℕ} (t : OC) (ht : ∀ a : OC, t * a = 0 → a = 0)
    {A B : Matrix (Fin r) (Fin r) OC} (h : t • A = t • B) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  have h2 : t * (A i j - B i j) = 0 := by rw [mul_sub, this, sub_self]
  exact sub_eq_zero.mp (ht _ h2)

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.
-/
lemma map_scalar {ℓ : ℕ} [Fact ℓ.Prime] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC] {r : ℕ}
    (e : OC ≃ₐ[ℤ_[ℓ]] OC) :
    (((ℓ : OC)) • (1 : Matrix (Fin r) (Fin r) OC)).map e = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/- English proof (translation)
Introduce `ℓ _ G _ OC _ _ actO r S S' Y Y' hℓ hY h1 h2 g`. Apply `mat_cancel (ℓ : OC) hℓ` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_scalar (actO g), ← h2, Matrix.map_mul]`. Use `_ = (ℓ : OC) • (S'.Mx g * Y') := by rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]`.
-/
theorem interInv : StatInterInv := by
  intro ℓ _ G _ OC _ _ actO r S S' Y Y' hℓ hY h1 h2 g
  apply mat_cancel (ℓ : OC) hℓ
  calc (ℓ : OC) • (Y'.map (actO g) * S.Mx g)
      = Y'.map (actO g) * S.Mx g * ((ℓ : OC) • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
    _ = Y'.map (actO g) * (S.Mx g * Y) * Y' := by rw [← h1]; simp only [Matrix.mul_assoc]
    _ = (Y'.map (actO g) * Y.map (actO g)) * S'.Mx g * Y' := by rw [← hY g]; simp only [Matrix.mul_assoc]
    _ = ((ℓ : OC) • 1) * S'.Mx g * Y' := by
        rw [← map_scalar (actO g), ← h2, Matrix.map_mul]
    _ = (ℓ : OC) • (S'.Mx g * Y') := by rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]

/- English proof (translation)
Introduce `ℓ _ G _ OC _ _ actO r S S' Y χ i hY g`. Use `show Y.map (actO g) * ((((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S'.Mx g) = ((((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx g) * Y`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, hY g]`.
-/
theorem interTwist : StatInterTwist := by
  intro ℓ _ G _ OC _ _ actO r S S' Y χ i hY g
  show Y.map (actO g) * ((((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S'.Mx g)
    = ((((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx g) * Y
  rw [Matrix.mul_smul, Matrix.smul_mul, hY g]

/- English proof (translation)
Introduce `ℓ _ G _ OC _ _ actO r S' Um Y Y' hℓ hU h1`. Establish `cancelY : ∀ A B : Matrix (Fin r) (Fin r) OC, A * Y = B * Y → A = B`. Introduce `A B h`. Apply `mat_cancel (ℓ : OC) hℓ` to reduce the goal to its premises. Establish `: A * Y * Y' = B * Y * Y'` using `by rw [h]`.

Rewrite `this` using `[Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]`. Conclude with `this`. Prove the components needed by the constructor for the conclusion. Apply `cancelY` to reduce the goal to its premises. Rewrite using `[← hU 1, S'.one, Matrix.mul_one, Matrix.one_mul]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Introduce `g h`. Apply `cancelY` to reduce the goal to its premises. Rewrite using `[← hU (g * h), S'.mul, Matrix.mul_assoc, ← hU g, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← hU h, Matrix.map_mul]`.

Use `congr 2`. Use extensionality with `i j`. Simplify using `[map_mul]`.
-/
theorem slOfInter : StatSLofInter := by
  intro ℓ _ G _ OC _ _ actO r S' Um Y Y' hℓ hU h1
  have cancelY : ∀ A B : Matrix (Fin r) (Fin r) OC, A * Y = B * Y → A = B := by
    intro A B h
    apply mat_cancel (ℓ : OC) hℓ
    have : A * Y * Y' = B * Y * Y' := by rw [h]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  constructor
  · apply cancelY
    rw [← hU 1, S'.one, Matrix.mul_one, Matrix.one_mul]
    ext i j
    simp
  · intro g h
    apply cancelY
    rw [← hU (g * h), S'.mul, Matrix.mul_assoc, ← hU g, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.map_mul, ← hU h, Matrix.map_mul]
    congr 2
    ext i j
    simp [map_mul]

/- English proof (translation)
Introduce `ℓ _ G G' _ _ _ OC _ _ _ _ _ actO r S S' Y Y' h h' p hYY x`. Take `⟨c, rfl⟩` from `Submodule.mkQ_surjective _ x`. Use `show Submodule.mkQ _ _ = (ℓ : ℤ_[ℓ]) • Submodule.mkQ _ c`. Rewrite using `[← map_smul]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show (c.1 g ᵥ* Y') ᵥ* Y = (ℓ : ℤ_[ℓ]) • c.1 g`. Rewrite using `[Matrix.vecMul_vecMul, hYY, Matrix.vecMul_smul, Matrix.vecMul_one]`. Use function extensionality and compare the values at `k`.

Simplify using `[Algebra.smul_def]`.
-/
theorem sandwich_composite_on_H1 : SandwichCompositeOnH1 := by
  intro ℓ _ G G' _ _ _ OC _ _ _ _ _ actO r S S' Y Y' h h' p hYY x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  show Submodule.mkQ _ _ = (ℓ : ℤ_[ℓ]) • Submodule.mkQ _ c
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext g
  show (c.1 g ᵥ* Y') ᵥ* Y = (ℓ : ℤ_[ℓ]) • c.1 g
  rw [Matrix.vecMul_vecMul, hYY, Matrix.vecMul_smul, Matrix.vecMul_one]
  funext k
  simp [Algebra.smul_def]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[matAct, LinearMap.pi_apply, LinearMap.sum_apply]`.
-/
lemma matAct_apply {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {r : ℕ}
    (V : Matrix (Fin r) (Fin r) R) (g0 : X →ₗ[R] X) (v : Fin r → X) :
    matAct V g0 v = fun k => ∑ t, V k t • g0 (v t) := by
  funext k
  simp [matAct, LinearMap.pi_apply, LinearMap.sum_apply]

/- English proof (translation)
Establish `hn : ∀ n : ℕ, (w : ℤ_[ℓ]) - 1 ∣ ((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1`. Introduce `n`. Rewrite using `[Units.val_pow_eq_pow_val]`. Simplify using `using sub_dvd_pow_sub_pow (w : ℤ_[ℓ]) 1 n`. Take `⟨n, rfl | rfl⟩` from `i.eq_nat_or_neg`.

Simplify using `using hn n`. Take `⟨q, hq⟩` from `hn n`. Use `⟨-(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * q, ?_⟩` and prove the remaining obligations. Establish `e1 : ((w ^ (-(n : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])` using `by simp`. Establish `e2 : (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1`.

Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_sub, neg_mul, e2]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ((w : ℤ_[ℓ]) - 1) * (-(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * q) := by rw [hq]; ring`.
-/
lemma zpow_sub_one_dvd {ℓ : ℕ} [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (i : ℤ) :
    (w : ℤ_[ℓ]) - 1 ∣ ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
  have hn : ∀ n : ℕ, (w : ℤ_[ℓ]) - 1 ∣ ((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro n
    rw [Units.val_pow_eq_pow_val]
    simpa using sub_dvd_pow_sub_pow (w : ℤ_[ℓ]) 1 n
  obtain ⟨n, rfl | rfl⟩ := i.eq_nat_or_neg
  · simpa using hn n
  · obtain ⟨q, hq⟩ := hn n
    refine ⟨-(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * q, ?_⟩
    have e1 : ((w ^ (-(n : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by simp
    have e2 : (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
      rw [← Units.val_mul]; simp
    rw [e1]
    calc (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1
        = -(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
          rw [mul_sub, neg_mul, e2]; ring
      _ = ((w : ℤ_[ℓ]) - 1) * (-(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * q) := by rw [hq]; ring

/- English proof (translation)
Introduce `ℓ _ Tt r Vm z z' ϖ ϖ₁ w i hz hϖ hc hT2 hV hw`. Establish `hdv : z * ϖ ∣ algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1`. Take `⟨q, hq⟩` from `hw.trans (zpow_sub_one_dvd w i)`. Establish `: algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 = algebraMap ℤ_[ℓ] Tt.Om (((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)` using `by simp`. Rewrite using `[this, hq, map_mul, map_pow, sq, ← hz]`.

Use `nth_rewrite 2 [hz]`. Rewrite using `[← hϖ]`. Conclude with `⟨z' * ϖ₁ * algebraMap ℤ_[ℓ] Tt.Om q, by ring⟩`. Establish `hVt : ∀ a b, z * ϖ ∣ (Vmᵀ - 1) a b`. Introduce `a b`.

Use `hV b a` as an intermediate fact. Simplify `this` using `[Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm]`. Establish `hVi` using `twistUm Tt.Om (z * ϖ) _ r Vmᵀ hdv hVt`. Take `⟨h1, h2⟩` from `unitCongruenceGivesPerturbation_statement ℓ Tt.Om Tt.Xm ϖ z z' r (Tt.Vi Vm w i) Tt.gX hz hc hT2.1 hT2.2.1 hT2.2.2 hVi`. Prove the components needed by the constructor for the conclusion.

Introduce `v hv`. Apply `h1 v` to reduce the goal to its premises. Rewrite using `[← matAct_apply]`. Conclude with `hv`. Introduce `v`.

Take `⟨y, hy⟩` from `h2 v`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, ← matAct_apply]`. Both sides reduce to the same expression.
-/
theorem t3W : PerturbationForEveryTwist := by
  intro ℓ _ Tt r Vm z z' ϖ ϖ₁ w i hz hϖ hc hT2 hV hw
  have hdv : z * ϖ ∣ algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    obtain ⟨q, hq⟩ := hw.trans (zpow_sub_one_dvd w i)
    have : algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1
        = algebraMap ℤ_[ℓ] Tt.Om (((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by simp
    rw [this, hq, map_mul, map_pow, sq, ← hz]
    nth_rewrite 2 [hz]
    rw [← hϖ]
    exact ⟨z' * ϖ₁ * algebraMap ℤ_[ℓ] Tt.Om q, by ring⟩
  have hVt : ∀ a b, z * ϖ ∣ (Vmᵀ - 1) a b := by
    intro a b
    have := hV b a
    simpa [Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using this
  have hVi := twistUm Tt.Om (z * ϖ) _ r Vmᵀ hdv hVt
  obtain ⟨h1, h2⟩ := unitCongruenceGivesPerturbation_statement ℓ Tt.Om Tt.Xm ϖ z z' r (Tt.Vi Vm w i) Tt.gX hz hc hT2.1 hT2.2.1 hT2.2.2 hVi
  constructor
  · intro v hv
    apply h1 v
    rw [← matAct_apply]
    exact hv
  · intro v
    obtain ⟨y, hy⟩ := h2 v
    refine ⟨y, ?_⟩
    rw [hy, ← matAct_apply]
    rfl

/- English proof (translation)
Introduce `ℓ _ G _ _ _ M _ _ _ _ _ _ a H γ lg c w0 hlg hadd hH hgen hfix hcH hcγ σ`. Take `⟨hcc, hcoc⟩` from `c.2`. Establish `lg1 : lg 1 = 0`. Use `hadd 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `(add_eq_left.mp this.symm)`. Establish `c1 : c.1 1 = 0`. Use `hcoc 1 1` as an intermediate fact. Rewrite `this` using `[mul_one, map_one]`. Conclude with `(add_eq_left.mp this.symm)`.

Set `S : Subgroup G` to `{ carrier := {σ | lg γ • c.1 σ = lg σ • w0} one_mem' := by show lg γ • c.1 1 = lg 1 • w0`. Rewrite using `[lg1, c1, smul_zero, zero_smul]`. Use the proof step `mul_mem' := by`. Introduce `x y hx hy`. Use `show lg γ • c.1 (x * y) = lg (x * y) • w0`.

Establish `hx' : lg γ • c.1 x = lg x • w0` using `hx`. Establish `hy' : lg γ • c.1 y = lg y • w0` using `hy`. Rewrite using `[hcoc, smul_add, hx', ← map_smul, hy', map_smul, hfix, hadd, add_smul]`. Use the proof step `inv_mem' := by`. Introduce `x hx`.

Use `show lg γ • c.1 x⁻¹ = lg x⁻¹ • w0`. Establish `hx' : lg γ • c.1 x = lg x • w0` using `hx`. Establish `e1 : c.1 x⁻¹ + a x⁻¹ (c.1 x) = 0` using `by rw [← hcoc, inv_mul_cancel, c1]`. Establish `e2 : lg x⁻¹ + lg x = 0` using `by rw [← hadd, inv_mul_cancel, lg1]`. Establish `e3 : lg γ • c.1 x⁻¹ + lg x • w0 = 0`.

Use `congrArg (fun t => lg γ • t) e1` as an intermediate fact. Simplify using `only [smul_add, smul_zero] at this`. Rewrite `this` using `[← map_smul, hx', map_smul, hfix]`. Then use the resulting hypothesis. Establish `e4 : lg x⁻¹ • w0 + lg x • w0 = 0` using `by rw [← add_smul, e2, zero_smul]`. Conclude with `add_right_cancel (e3.trans e4.symm) }`.

Establish `hS : S = ⊤`. Apply `hgen S` to reduce the goal to its premises. Conclude with `isClosed_eq (hcc.const_smul _) (hlg.smul continuous_const)`. Introduce `h hh show lg γ • c.1 h = lg h • w0`. Rewrite using `[hcH h hh, hH h hh, smul_zero, zero_smul]`.

Use `show lg γ • c.1 γ = lg γ • w0`. Rewrite using `[hcγ]`. Establish `: σ ∈ S` using `hS ▸ Subgroup.mem_top σ`. Conclude with `this`.
-/
theorem logClass : StatLogClass := by
  intro ℓ _ G _ _ _ M _ _ _ _ _ _ a H γ lg c w0 hlg hadd hH hgen hfix hcH hcγ σ
  obtain ⟨hcc, hcoc⟩ := c.2
  have lg1 : lg 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  have c1 : c.1 1 = 0 := by
    have := hcoc 1 1
    rw [mul_one, map_one] at this
    exact (add_eq_left.mp this.symm)
  let S : Subgroup G :=
    { carrier := {σ | lg γ • c.1 σ = lg σ • w0}
      one_mem' := by
        show lg γ • c.1 1 = lg 1 • w0
        rw [lg1, c1, smul_zero, zero_smul]
      mul_mem' := by
        intro x y hx hy
        show lg γ • c.1 (x * y) = lg (x * y) • w0
        have hx' : lg γ • c.1 x = lg x • w0 := hx
        have hy' : lg γ • c.1 y = lg y • w0 := hy
        rw [hcoc, smul_add, hx', ← map_smul, hy', map_smul, hfix, hadd, add_smul]
      inv_mem' := by
        intro x hx
        show lg γ • c.1 x⁻¹ = lg x⁻¹ • w0
        have hx' : lg γ • c.1 x = lg x • w0 := hx
        have e1 : c.1 x⁻¹ + a x⁻¹ (c.1 x) = 0 := by rw [← hcoc, inv_mul_cancel, c1]
        have e2 : lg x⁻¹ + lg x = 0 := by rw [← hadd, inv_mul_cancel, lg1]
        have e3 : lg γ • c.1 x⁻¹ + lg x • w0 = 0 := by
          have := congrArg (fun t => lg γ • t) e1
          simp only [smul_add, smul_zero] at this
          rwa [← map_smul, hx', map_smul, hfix] at this
        have e4 : lg x⁻¹ • w0 + lg x • w0 = 0 := by rw [← add_smul, e2, zero_smul]
        exact add_right_cancel (e3.trans e4.symm) }
  have hS : S = ⊤ := by
    apply hgen S
    · exact isClosed_eq (hcc.const_smul _) (hlg.smul continuous_const)
    · intro h hh
      show lg γ • c.1 h = lg h • w0
      rw [hcH h hh, hH h hh, smul_zero, zero_smul]
    · show lg γ • c.1 γ = lg γ • w0
      rw [hcγ]
  have : σ ∈ S := hS ▸ Subgroup.mem_top σ
  exact this

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
