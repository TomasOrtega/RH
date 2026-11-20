import ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

namespace DeterminantValuationBounds

variable {C : Type} [Field C] {v : Valuation C NNReal}

/- English proof (translation)
Assume the negation of the conclusion as `hfin`. Rewrite `hfin` using `[not_infinite_iff_finite]`. Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField v.valuationSubring)`. Take `⟨q, hq⟩ : ∃ q, q = Fintype.card (IsLocalRing.ResidueField v.valuationSubring)` from `⟨_, rfl⟩`. Establish `hq2 : 2 ≤ q`.

Use `Fintype.one_lt_card (α := IsLocalRing.ResidueField v.valuationSubring)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hdeg : (Polynomial.X ^ q - (Polynomial.X + Polynomial.C 1) : Polynomial C).degree ≠ 0`. Apply the tactic sequence `rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]`. Conclude with `(by omega : q ≠ 0)` after adjusting the coercions.

Rewrite using `[Polynomial.degree_X_add_C]`. Conclude with `(by omega : 1 < q)` after adjusting the coercions. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root _ hdeg`. Simplify using `only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C] at hα`. Establish `hαq : α ^ q = α + 1` using `sub_eq_zero.mp hα`.

Establish `hle : v α ≤ 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : v (α + 1) ≤ v α`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : v α < v α ^ q`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[← map_pow, hαq]`. Conclude with `absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)`. Establish `hmem : α ∈ v.valuationSubring` using `(v.mem_valuationSubring_iff α).mpr hle`.

Establish `hx : (⟨α, hmem⟩ : v.valuationSubring) ^ q = ⟨α, hmem⟩ + 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `hαq`. Establish `hr` using `congrArg (IsLocalRing.residue v.valuationSubring) hx`.

Establish `hpc` using `FiniteField.pow_card (IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩)`. Rewrite `hpc` using `[← hq]`. Rewrite `hr` using `[map_pow, map_add, map_one, hpc]`. Establish `h10 : (1 : IsLocalRing.ResidueField v.valuationSubring) = 0`. Use `congrArg (· - IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩) hr` as an intermediate fact.

Simplify using `using this.symm`. Conclude with `one_ne_zero h10`.
-/
theorem infinite_residueField [IsAlgClosed C] :
    Infinite (IsLocalRing.ResidueField v.valuationSubring) := by
  classical
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  letI := Fintype.ofFinite (IsLocalRing.ResidueField v.valuationSubring)
  obtain ⟨q, hq⟩ : ∃ q, q = Fintype.card (IsLocalRing.ResidueField v.valuationSubring) := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := IsLocalRing.ResidueField v.valuationSubring)
    omega
  have hdeg : (Polynomial.X ^ q - (Polynomial.X + Polynomial.C 1) : Polynomial C).degree ≠ 0 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
    · exact_mod_cast (by omega : q ≠ 0)
    · rw [Polynomial.degree_X_add_C]
      exact_mod_cast (by omega : 1 < q)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_C] at hα
  have hαq : α ^ q = α + 1 := sub_eq_zero.mp hα
  have hle : v α ≤ 1 := by
    by_contra h
    push_neg at h
    have h1 : v (α + 1) ≤ v α := by
      calc v (α + 1) ≤ max (v α) (v 1) := v.map_add _ _
        _ = v α := by rw [map_one]; exact max_eq_left h.le
    have h2 : v α < v α ^ q := by
      calc v α = v α ^ 1 := (pow_one _).symm
        _ < v α ^ q := pow_lt_pow_right₀ h (by omega)
    rw [← map_pow, hαq] at h2
    exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
  have hmem : α ∈ v.valuationSubring := (v.mem_valuationSubring_iff α).mpr hle
  have hx : (⟨α, hmem⟩ : v.valuationSubring) ^ q = ⟨α, hmem⟩ + 1 := by
    apply Subtype.ext
    push_cast
    exact hαq
  have hr := congrArg (IsLocalRing.residue v.valuationSubring) hx
  have hpc := FiniteField.pow_card (IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩)
  rw [← hq] at hpc
  rw [map_pow, map_add, map_one, hpc] at hr
  have h10 : (1 : IsLocalRing.ResidueField v.valuationSubring) = 0 := by
    have := congrArg (· - IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩) hr
    simpa using this.symm
  exact one_ne_zero h10

/- English proof (translation)
Establish `hu : IsUnit x` using `(IsLocalRing.residue_ne_zero_iff_isUnit x).mp hx`. Take `⟨u, rfl⟩` from `hu`. Establish `h1 : v ((u : v.valuationSubring) : C) ≤ 1` using `(u : v.valuationSubring).2`. Establish `h2 : v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤ 1` using `((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring).2`. Establish `hmul : ((u : v.valuationSubring) : C) * (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1`.

Establish `h` using `congrArg (fun z : v.valuationSubring => (z : C)) (Units.mul_inv u)`. Conclude with `h` after adjusting the coercions. Establish `hv : v ((u : v.valuationSubring) : C) * v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1`. Rewrite using `[← map_mul, hmul, map_one]`. Use `le_antisymm h1 ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `: v ((u : v.valuationSubring) : C) * v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤ v ((u : v.valuationSubring) : C)` using `mul_le_of_le_one_right zero_le h2`. Rewrite `this` using `[hv]`. Conclude with `absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)`.
-/
theorem v_eq_one_of_residue_ne_zero {x : v.valuationSubring}
    (hx : IsLocalRing.residue v.valuationSubring x ≠ 0) : v (x : C) = 1 := by
  have hu : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp hx
  obtain ⟨u, rfl⟩ := hu
  have h1 : v ((u : v.valuationSubring) : C) ≤ 1 := (u : v.valuationSubring).2
  have h2 : v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤ 1 :=
    ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring).2
  have hmul : ((u : v.valuationSubring) : C) *
      (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1 := by
    have h := congrArg (fun z : v.valuationSubring => (z : C)) (Units.mul_inv u)
    exact_mod_cast h
  have hv : v ((u : v.valuationSubring) : C) *
      v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : v ((u : v.valuationSubring) : C) *
      v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤
      v ((u : v.valuationSubring) : C) := mul_le_of_le_one_right zero_le h2
  rw [hv] at this
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[map_sum]`.
-/
theorem eval_det_gen {K : Type} [CommRing K] {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (A : Matrix ι σ K) (z : σ × ι → K) :
    MvPolynomial.eval z (Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (A i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) K))) =
      Matrix.det (Matrix.of fun i j => ∑ r, A i r * z (r, j)) := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [map_sum]

/- English proof (translation)
Use `haveI : Infinite (IsLocalRing.ResidueField v.valuationSubring) := infinite_residueField`. Set `QO : T → Matrix ι σ v.valuationSubring` to `fun t i r => ⟨Q t i r, (v.mem_valuationSubring_iff _).mpr (hQ t i r)⟩`. Set `Qk : T → Matrix ι σ (IsLocalRing.ResidueField v.valuationSubring)` to `fun t i r => IsLocalRing.residue v.valuationSubring (QO t i r)`. Set `p : T → MvPolynomial (σ × ι) (IsLocalRing.ResidueField v.valuationSubring)` to `fun t => Matrix.det (Matrix.of fun i j => ∑ r, MvPolynomial.C (Qk t i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) _))`. Establish `hp : ∀ t, p t ≠ 0`.

Introduce `t hzero`. Take `⟨d, hd, hQd⟩` from `hsec t`. Set `dO : Matrix σ ι v.valuationSubring` to `fun r i => ⟨d r i, (v.mem_valuationSubring_iff _).mpr (hd r i)⟩`. Establish `h1` using `eval_det_gen (Qk t) (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))`. Establish `h1' : MvPolynomial.eval (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2)) (p t) = _` using `h1`.

Rewrite `h1'` using `[hzero, map_zero]`. Establish `hone : (Matrix.of fun i j => ∑ r, Qk t i r * IsLocalRing.residue v.valuationSubring (dO (r, j).1 (r, j).2)) = 1`. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hQd i) j`. Rewrite `hij` using `[Matrix.mul_apply]`.

Establish `hO : ∑ r, QO t i r * dO r j = (1 : Matrix ι ι v.valuationSubring) i j`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hc : ((∑ r, QO t i r * dO r j : v.valuationSubring) : C) = ∑ r, Q t i r * d r j`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[hc, hij]`. Distinguish the cases in `hij' : i = j`. Substitute `hij'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij']`.

Simplify using `only [Matrix.of_apply, Qk]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[map_sum, map_mul]`. Use `_ = (1 : Matrix ι ι (IsLocalRing.ResidueField v.valuationSubring)) i j := by`. Rewrite using `[hO]`.

Distinguish the cases in `hij' : i = j`. Substitute `hij'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij']`. Rewrite `h1'` using `[hone, Matrix.det_one]`.

Conclude with `zero_ne_one h1'`. Establish `hP : ∏ t, p t ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun t _ => hp t`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, MvPolynomial.eval z (∏ t, p t) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hP (MvPolynomial.funext fun x => by rw [h x, map_zero])`. Rewrite `hz` using `[map_prod]`. Establish `hzt : ∀ t, MvPolynomial.eval z (p t) ≠ 0` using `fun t => (Finset.prod_ne_zero_iff.mp hz) t (Finset.mem_univ _)`. Use `choose y hy using fun x : σ × ι => IsLocalRing.residue_surjective (z x)`. Use `⟨Matrix.of fun r i => (y (r, i) : C), fun r i => (y (r, i)).2, fun t => ?_⟩` and prove the remaining obligations.

Set `cO : Matrix σ ι v.valuationSubring` to `fun r i => y (r, i)`. Establish `hcoe : (Q t * Matrix.of fun r i => (y (r, i) : C)).det = v.valuationSubring.subtype (QO t * cO).det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul]`. Both sides reduce to the same expression. Rewrite using `[hcoe]`. Apply `v_eq_one_of_residue_ne_zero` to reduce the goal to its premises. Rewrite using `[RingHom.map_det]`.

Establish `hzt'` using `hzt t`. Establish `he : MvPolynomial.eval z (p t) = Matrix.det (Matrix.of fun i j => ∑ r, Qk t i r * z (r, j))` using `eval_det_gen (Qk t) z`. Rewrite `hzt'` using `[he]`. Establish `hmat : (IsLocalRing.residue v.valuationSubring).mapMatrix (QO t * cO) = Matrix.of fun i j => ∑ r, Qk t i r * z (r, j)`. Use extensionality with `i j`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← hy (r, j)]`. Rewrite using `[hmat]`. Conclude with `hzt'`.
-/
theorem exists_generic [IsAlgClosed C] {ι σ T : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [Fintype T] (Q : T → Matrix ι σ C) (hQ : ∀ t i r, v (Q t i r) ≤ 1)
    (hsec : ∀ t, ∃ d : Matrix σ ι C, (∀ r i, v (d r i) ≤ 1) ∧ Q t * d = 1) :
    ∃ c : Matrix σ ι C, (∀ r i, v (c r i) ≤ 1) ∧ ∀ t, v (Q t * c).det = 1 := by
  classical
  haveI : Infinite (IsLocalRing.ResidueField v.valuationSubring) := infinite_residueField
  let QO : T → Matrix ι σ v.valuationSubring :=
    fun t i r => ⟨Q t i r, (v.mem_valuationSubring_iff _).mpr (hQ t i r)⟩
  let Qk : T → Matrix ι σ (IsLocalRing.ResidueField v.valuationSubring) :=
    fun t i r => IsLocalRing.residue v.valuationSubring (QO t i r)
  let p : T → MvPolynomial (σ × ι) (IsLocalRing.ResidueField v.valuationSubring) := fun t =>
    Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (Qk t i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) _))
  have hp : ∀ t, p t ≠ 0 := by
    intro t hzero
    obtain ⟨d, hd, hQd⟩ := hsec t
    let dO : Matrix σ ι v.valuationSubring :=
      fun r i => ⟨d r i, (v.mem_valuationSubring_iff _).mpr (hd r i)⟩
    have h1 := eval_det_gen (Qk t) (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))
    have h1' : MvPolynomial.eval (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))
        (p t) = _ := h1
    rw [hzero, map_zero] at h1'
    have hone : (Matrix.of fun i j => ∑ r, Qk t i r *
        IsLocalRing.residue v.valuationSubring (dO (r, j).1 (r, j).2)) = 1 := by
      ext i j
      have hij := congrFun (congrFun hQd i) j
      rw [Matrix.mul_apply] at hij
      have hO : ∑ r, QO t i r * dO r j = (1 : Matrix ι ι v.valuationSubring) i j := by
        apply Subtype.ext
        have hc : ((∑ r, QO t i r * dO r j : v.valuationSubring) : C) = ∑ r, Q t i r * d r j := by
          push_cast
          rfl
        rw [hc, hij]
        by_cases hij' : i = j
        · subst hij'
          simp
        · simp [Matrix.one_apply_ne hij']
      simp only [Matrix.of_apply, Qk]
      calc ∑ r, IsLocalRing.residue v.valuationSubring (QO t i r) *
            IsLocalRing.residue v.valuationSubring (dO r j)
          = IsLocalRing.residue v.valuationSubring (∑ r, QO t i r * dO r j) := by
            simp [map_sum, map_mul]
        _ = (1 : Matrix ι ι (IsLocalRing.ResidueField v.valuationSubring)) i j := by
            rw [hO]
            by_cases hij' : i = j
            · subst hij'; simp
            · simp [Matrix.one_apply_ne hij']
    rw [hone, Matrix.det_one] at h1'
    exact zero_ne_one h1'
  have hP : ∏ t, p t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hp t
  obtain ⟨z, hz⟩ : ∃ z, MvPolynomial.eval z (∏ t, p t) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_prod] at hz
  have hzt : ∀ t, MvPolynomial.eval z (p t) ≠ 0 :=
    fun t => (Finset.prod_ne_zero_iff.mp hz) t (Finset.mem_univ _)
  choose y hy using fun x : σ × ι => IsLocalRing.residue_surjective (z x)
  refine ⟨Matrix.of fun r i => (y (r, i) : C), fun r i => (y (r, i)).2, fun t => ?_⟩
  let cO : Matrix σ ι v.valuationSubring := fun r i => y (r, i)
  have hcoe : (Q t * Matrix.of fun r i => (y (r, i) : C)).det =
      v.valuationSubring.subtype (QO t * cO).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum,
      map_mul]
    rfl
  rw [hcoe]
  apply v_eq_one_of_residue_ne_zero
  rw [RingHom.map_det]
  have hzt' := hzt t
  have he : MvPolynomial.eval z (p t) =
      Matrix.det (Matrix.of fun i j => ∑ r, Qk t i r * z (r, j)) := eval_det_gen (Qk t) z
  rw [he] at hzt'
  have hmat : (IsLocalRing.residue v.valuationSubring).mapMatrix (QO t * cO) =
      Matrix.of fun i j => ∑ r, Qk t i r * z (r, j) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply,
      map_sum, map_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hy (r, j)]
  rw [hmat]
  exact hzt'

variable {n s : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hw`. Consider the case `succ k ih`. Establish `e : (fun y : Fin n × Fin s => a y.1 ^ (k + 1) * w y) = fun y => a y.1 * (a y.1 ^ k * w y)`. Use function extensionality and compare the values at `y`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hM _ ih`.
-/
theorem pow_stable {a : Fin n → C} {M : Lat v (Fin n × Fin s)} (hM : IsLaStable a M) (k : ℕ)
    {w : Fin n × Fin s → C} (hw : w ∈ M.pts) :
    (fun y : Fin n × Fin s => a y.1 ^ k * w y) ∈ M.pts := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    have e : (fun y : Fin n × Fin s => a y.1 ^ (k + 1) * w y) =
        fun y => a y.1 * (a y.1 ^ k * w y) := by
      funext y
      ring
    rw [e]
    exact hM _ ih

/- English proof (translation)
Use `choose c hc using hX`. Use `set U : Matrix ι ι C := Matrix.of fun i y => c y i with hU`. Establish `hXe : X = L.B * U`. Use extensionality with `x y`. Rewrite using `[show X x y = (L.B *ᵥ c y) x from congrFun (hc y).2 x, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Simplify using `[hU]`. Establish `hUi : IsIntegralMat v U` using `fun i y => by simpa [hU] using (hc y).1 i`. Rewrite using `[hXe, Matrix.det_mul, map_mul]`. Conclude with `mul_le_of_le_one_right zero_le hUi.det_le_one`.
-/
theorem v_det_le_of_cols {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) (X : Matrix ι ι C)
    (hX : ∀ y, (fun x => X x y) ∈ L.pts) : v X.det ≤ v L.B.det := by
  choose c hc using hX
  set U : Matrix ι ι C := Matrix.of fun i y => c y i with hU
  have hXe : X = L.B * U := by
    ext x y
    rw [show X x y = (L.B *ᵥ c y) x from congrFun (hc y).2 x, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
    simp [hU]
  have hUi : IsIntegralMat v U := fun i y => by simpa [hU] using (hc y).1 i
  rw [hXe, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right zero_le hUi.det_le_one

end DeterminantValuationBounds

open DeterminantValuationBounds in

/- English proof (translation)
Establish `v_discr : v (discr a) = v (Matrix.vandermonde a).det ^ 2`. Rewrite using `[Matrix.det_vandermonde, discr, sq]`. Simplify using `only [map_prod]`. Establish `hsplit : ∀ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') = (∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ)) * ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ')`. Introduce `τ`.

Establish `hu : Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ`. Use extensionality with `x`. Simplify using `only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Break down `lt_or_gt_of_ne h with h | h` into its components or cases. Conclude with `Or.inr h`. Conclude with `Or.inl h`. Introduce and unpack `(h | h)`. Conclude with `ne_of_gt h`.

Conclude with `ne_of_lt h`. Rewrite using `[hu, Finset.prod_union (Finset.disjoint_left.mpr fun x h1 h2 => by`. Simplify using `only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2`. Conclude with `lt_asymm h1 h2)]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun x _ => Valuation.map_sub_swap _ _ _`. Rewrite using `[Finset.prod_congr rfl fun τ _ => hsplit τ, Finset.prod_mul_distrib]`. Use `congr 1`. Conclude with `Finset.prod_comm' (by intro x y; simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true])`. Establish `v_det_sum : v S.B.det = ∏ τ, v (Mτ τ).B.det`.

Set `Bb : Matrix (Fin n × Fin s) (Fin n × Fin s) C` to `Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n)) (Matrix.blockDiagonal fun τ => (Mτ τ).B)`. Establish `hdet : Bb.det = ∏ τ, (Mτ τ).B.det`. Simplify using `only [Bb, Matrix.det_reindex_self, Matrix.det_blockDiagonal]`. Set `Sb : Lat v (Fin n × Fin s)` to `⟨Bb, by rw [hdet]; exact Finset.prod_ne_zero_iff.mpr fun τ _ => (Mτ τ).det_ne⟩`. Establish `hmv : ∀ (c : Fin n × Fin s → C) (τ : Fin n) (i : Fin s), (Bb *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i`.

Introduce `c τ i`. Simplify using `only [Bb, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Simplify using the standard rewrite rules. Establish `hpts : Sb.pts = sumPts Mτ`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩ τ`. Use `⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Conclude with `hmv c τ i`. Introduce `hx choose cτ hcτ hxτ using hx`. Use `⟨fun p => cτ p.1 p.2, fun p => hcτ p.1 p.2, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨τ, i⟩`. Use `show x (τ, i) = (Bb *ᵥ fun p => cτ p.1 p.2) (τ, i)`.

Rewrite using `[hmv]`. Conclude with `congrFun (hxτ τ) i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdet, map_prod]`. Set `R : Fin n → Matrix (Fin s) (Fin n × Fin s) C` to `fun τ => Matrix.of fun i y => M.B (τ, i) y`.

Set `Q : Fin n → Matrix (Fin s) (Fin n × Fin s) C` to `fun τ => (Mτ τ).B⁻¹ * R τ`. Establish `hB : ∀ τ, (Mτ τ).B⁻¹ * (Mτ τ).B = 1` using `fun τ => Matrix.nonsing_inv_mul _ (Mτ τ).isUnit_det`. Establish `hB' : ∀ τ, (Mτ τ).B * (Mτ τ).B⁻¹ = 1` using `fun τ => Matrix.mul_nonsing_inv _ (Mτ τ).isUnit_det`. Establish `hproj : ∀ τ (w : Fin n × Fin s → C), w ∈ M.pts → (fun i => w (τ, i)) ∈ (Mτ τ).pts`. Introduce `τ w hw`.

Rewrite using `[hτ τ]`. Conclude with `⟨w, hw, rfl⟩`. Establish `hcolM : ∀ (c : Fin n × Fin s → C), IsIntegralVec v c → M.B *ᵥ c ∈ M.pts` using `fun c hc => ⟨c, hc, rfl⟩`. Establish `hQint : ∀ τ i y, v (Q τ i y) ≤ 1`. Introduce `τ i y`.

Establish `hcol : M.B *ᵥ Pi.single y 1 ∈ M.pts` using `hcolM _ (isIntegralVec_single y)`. Take `⟨c, hc, hce⟩` from `hproj τ _ hcol`. Establish `hQc : (fun i => Q τ i y) = c`. Establish `h1 : (fun i => Q τ i y) = (Mτ τ).B⁻¹ *ᵥ (fun i => (M.B *ᵥ Pi.single y 1) (τ, i))`. Use extensionality with `i`.

Simplify using `[Q, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[h1, hce, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]`. Use `hc i` as an intermediate fact. Rewrite `this` using `[← hQc]`. Conclude with `this`.

Establish `hsec : ∀ τ, ∃ d : Matrix (Fin n × Fin s) (Fin s) C, (∀ r i, v (d r i) ≤ 1) ∧ Q τ * d = 1`. Introduce `τ`. Establish `hmem : ∀ j, (fun i => (Mτ τ).B i j) ∈ projPts M.pts τ`. Introduce `j`. Rewrite using `[← hτ τ]`.

Use `⟨Pi.single j 1, isIntegralVec_single j, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Use `choose w hw hwe using hmem`. Use `choose d hd hde using hw`.

Use `⟨Matrix.of fun r j => d j r, fun r j => hd j r, ?_⟩` and prove the remaining obligations. Establish `hRd : R τ * (Matrix.of fun r j => d j r) = (Mτ τ).B`. Use extensionality with `i j`. Establish `h1 : w j (τ, i) = (Mτ τ).B i j` using `congrFun (hwe j) i`. Rewrite `h1` using `[hde j]`.

Rewrite using `[← h1]`. Simplify using `[R, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use `show (Mτ τ).B⁻¹ * R τ * _ = 1`. Rewrite using `[Matrix.mul_assoc, hRd, hB]`. Take `⟨c, hcint, hcdet⟩` from `exists_generic Q (fun τ i y => hQint τ i y) hsec`.

Set `X : Matrix (Fin n × Fin s) (Fin n × Fin s) C` to `Matrix.of fun x y => a x.1 ^ (y.1 : ℕ) * (M.B * c) x y.2`. Establish `hXcols : ∀ y, (fun x => X x y) ∈ M.pts`. Introduce `y`. Establish `hw : (fun x => (M.B * c) x y.2) ∈ M.pts`. Use `⟨fun r => c r y.2, fun r => hcint r y.2, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Conclude with `pow_stable hM y.1 hw`. Establish `hle : v X.det ≤ v M.B.det` using `v_det_le_of_cols M X hXcols`. Set `G : Fin n → Matrix (Fin s) (Fin s) C` to `fun τ => (Mτ τ).B * (Q τ * c)`.

Establish `hG : ∀ τ i j, (M.B * c) (τ, i) j = G τ i j`. Introduce `τ i j`. Use `show _ = ((Mτ τ).B * ((Mτ τ).B⁻¹ * R τ * c)) i j`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hB', Matrix.one_mul]`. Simplify using `[R, Matrix.mul_apply]`.

Establish `hfree : freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a`. Use extensionality with `x y`. Simplify using `[freeMat, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]`. Establish `hXfac : X = Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n)) (Matrix.blockDiagonal G) * freeMat a s`. Use extensionality with `x y`.

Rewrite using `[Matrix.mul_apply, Fintype.sum_prod_type]`. Simplify using `only [X, Matrix.of_apply, hG, freeMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap, Matrix.blockDiagonal_apply]`. Simplify using `only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGdet : ∀ τ, v (G τ).det = v (Mτ τ).B.det`.

Introduce `τ`. Simplify using `only [G, Matrix.det_mul, map_mul, hcdet τ, mul_one]`. Establish `hdetX : v X.det = (∏ τ, v (Mτ τ).B.det) * v (Matrix.vandermonde a).det ^ s`. Rewrite using `[hXfac, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_blockDiagonal, hfree, Matrix.det_blockDiagonal, map_mul, map_prod, map_prod]`. Simplify using `only [hGdet, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Establish `hSdet` using `v_det_sum`. Establish `hSpos : 0 < v S.B.det`. Rewrite using `[pos_iff_ne_zero, Ne, map_eq_zero]`. Conclude with `S.det_ne`. Establish `hcol : v (Matrix.vandermonde a).det ^ s ≤ colen M S`.

Rewrite using `[colen, le_div_iff₀ hSpos, hSdet, mul_comm, ← hdetX]`. Conclude with `hle`. Rewrite using `[v_discr, ← pow_mul, mul_comm 2 s, pow_mul]`. Conclude with `pow_le_pow_left₀ zero_le hcol 2`.
-/
theorem valuation_pairwiseDifferenceProduct_pow_le_colength_sq (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (n : ℕ)
    (a : Fin n → C) (s : ℕ) (M S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s))
    (hM : IsLaStable a M) (hτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ) (hS : S.pts = sumPts Mτ) :
    v (discr a) ^ s ≤ colen M S ^ 2 := by
  classical
  have v_discr : v (discr a) = v (Matrix.vandermonde a).det ^ 2 := by
    rw [Matrix.det_vandermonde, discr, sq]
    simp only [map_prod]
    have hsplit : ∀ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
        (∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ)) * ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
      intro τ
      have hu : Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
          Finset.mem_Iio]
        constructor
        · intro h
          rcases lt_or_gt_of_ne h with h | h
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | h)
          · exact ne_of_gt h
          · exact ne_of_lt h
      rw [hu, Finset.prod_union (Finset.disjoint_left.mpr fun x h1 h2 => by
        simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2
        exact lt_asymm h1 h2)]
      congr 1
      exact Finset.prod_congr rfl fun x _ => Valuation.map_sub_swap _ _ _
    rw [Finset.prod_congr rfl fun τ _ => hsplit τ, Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_comm' (by intro x y; simp only [Finset.mem_univ, Finset.mem_Iio,
      Finset.mem_Ioi, true_and, and_true])
  have v_det_sum : v S.B.det = ∏ τ, v (Mτ τ).B.det := by
    let Bb : Matrix (Fin n × Fin s) (Fin n × Fin s) C :=
      Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (Matrix.blockDiagonal fun τ => (Mτ τ).B)
    have hdet : Bb.det = ∏ τ, (Mτ τ).B.det := by
      simp only [Bb, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    let Sb : Lat v (Fin n × Fin s) :=
      ⟨Bb, by rw [hdet]; exact Finset.prod_ne_zero_iff.mpr fun τ _ => (Mτ τ).det_ne⟩
    have hmv : ∀ (c : Fin n × Fin s → C) (τ : Fin n) (i : Fin s),
        (Bb *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
      intro c τ i
      simp only [Bb, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
        Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    have hpts : Sb.pts = sumPts Mτ := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩ τ
        refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
        ext i
        exact hmv c τ i
      · intro hx
        choose cτ hcτ hxτ using hx
        refine ⟨fun p => cτ p.1 p.2, fun p => hcτ p.1 p.2, ?_⟩
        ext ⟨τ, i⟩
        show x (τ, i) = (Bb *ᵥ fun p => cτ p.1 p.2) (τ, i)
        rw [hmv]
        exact congrFun (hxτ τ) i
    calc v S.B.det = v Sb.B.det := Lat.v_det_eq_of_pts_eq (hS.trans hpts.symm)
      _ = ∏ τ, v (Mτ τ).B.det := by
        show v Bb.det = _
        rw [hdet, map_prod]
  let R : Fin n → Matrix (Fin s) (Fin n × Fin s) C := fun τ => Matrix.of fun i y => M.B (τ, i) y
  let Q : Fin n → Matrix (Fin s) (Fin n × Fin s) C := fun τ => (Mτ τ).B⁻¹ * R τ
  have hB : ∀ τ, (Mτ τ).B⁻¹ * (Mτ τ).B = 1 := fun τ => Matrix.nonsing_inv_mul _ (Mτ τ).isUnit_det
  have hB' : ∀ τ, (Mτ τ).B * (Mτ τ).B⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (Mτ τ).isUnit_det
  have hproj : ∀ τ (w : Fin n × Fin s → C), w ∈ M.pts → (fun i => w (τ, i)) ∈ (Mτ τ).pts := by
    intro τ w hw
    rw [hτ τ]
    exact ⟨w, hw, rfl⟩
  have hcolM : ∀ (c : Fin n × Fin s → C), IsIntegralVec v c → M.B *ᵥ c ∈ M.pts :=
    fun c hc => ⟨c, hc, rfl⟩
  have hQint : ∀ τ i y, v (Q τ i y) ≤ 1 := by
    intro τ i y
    have hcol : M.B *ᵥ Pi.single y 1 ∈ M.pts := hcolM _ (isIntegralVec_single y)
    obtain ⟨c, hc, hce⟩ := hproj τ _ hcol
    have hQc : (fun i => Q τ i y) = c := by
      have h1 : (fun i => Q τ i y) = (Mτ τ).B⁻¹ *ᵥ (fun i => (M.B *ᵥ Pi.single y 1) (τ, i)) := by
        ext i
        simp [Q, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h1, hce, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
    have := hc i
    rw [← hQc] at this
    exact this
  have hsec : ∀ τ, ∃ d : Matrix (Fin n × Fin s) (Fin s) C, (∀ r i, v (d r i) ≤ 1) ∧ Q τ * d = 1 := by
    intro τ
    have hmem : ∀ j, (fun i => (Mτ τ).B i j) ∈ projPts M.pts τ := by
      intro j
      rw [← hτ τ]
      refine ⟨Pi.single j 1, isIntegralVec_single j, ?_⟩
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    choose w hw hwe using hmem
    choose d hd hde using hw
    refine ⟨Matrix.of fun r j => d j r, fun r j => hd j r, ?_⟩
    have hRd : R τ * (Matrix.of fun r j => d j r) = (Mτ τ).B := by
      ext i j
      have h1 : w j (τ, i) = (Mτ τ).B i j := congrFun (hwe j) i
      rw [hde j] at h1
      rw [← h1]
      simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    show (Mτ τ).B⁻¹ * R τ * _ = 1
    rw [Matrix.mul_assoc, hRd, hB]
  obtain ⟨c, hcint, hcdet⟩ := exists_generic Q (fun τ i y => hQint τ i y) hsec
  let X : Matrix (Fin n × Fin s) (Fin n × Fin s) C :=
    Matrix.of fun x y => a x.1 ^ (y.1 : ℕ) * (M.B * c) x y.2
  have hXcols : ∀ y, (fun x => X x y) ∈ M.pts := by
    intro y
    have hw : (fun x => (M.B * c) x y.2) ∈ M.pts := by
      refine ⟨fun r => c r y.2, fun r => hcint r y.2, ?_⟩
      ext x
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact pow_stable hM y.1 hw
  have hle : v X.det ≤ v M.B.det := v_det_le_of_cols M X hXcols
  let G : Fin n → Matrix (Fin s) (Fin s) C := fun τ => (Mτ τ).B * (Q τ * c)
  have hG : ∀ τ i j, (M.B * c) (τ, i) j = G τ i j := by
    intro τ i j
    show _ = ((Mτ τ).B * ((Mτ τ).B⁻¹ * R τ * c)) i j
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB', Matrix.one_mul]
    simp [R, Matrix.mul_apply]
  have hfree : freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
    ext x y
    simp [freeMat, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]
  have hXfac : X = Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal G) * freeMat a s := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [X, Matrix.of_apply, hG, freeMat, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap, Matrix.blockDiagonal_apply]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  have hGdet : ∀ τ, v (G τ).det = v (Mτ τ).B.det := by
    intro τ
    simp only [G, Matrix.det_mul, map_mul, hcdet τ, mul_one]
  have hdetX : v X.det = (∏ τ, v (Mτ τ).B.det) * v (Matrix.vandermonde a).det ^ s := by
    rw [hXfac, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_blockDiagonal, hfree,
      Matrix.det_blockDiagonal, map_mul, map_prod, map_prod]
    simp only [hGdet, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hSdet := v_det_sum
  have hSpos : 0 < v S.B.det := by
    rw [pos_iff_ne_zero, Ne, map_eq_zero]
    exact S.det_ne
  have hcol : v (Matrix.vandermonde a).det ^ s ≤ colen M S := by
    rw [colen, le_div_iff₀ hSpos, hSdet, mul_comm, ← hdetX]
    exact hle
  rw [v_discr, ← pow_mul, mul_comm 2 s, pow_mul]
  exact pow_le_pow_left₀ zero_le hcol 2

end ReciprocityTheory.PGsh.Up
