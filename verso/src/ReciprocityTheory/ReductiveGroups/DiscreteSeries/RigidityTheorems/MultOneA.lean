import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]`.
-/
theorem matrixAction_add {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [actM, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]`.
-/
theorem matrixAction_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp only [actM, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Simplify using `only [actM, Matrix.single_apply, ite_smul, one_smul, zero_smul]`. Rewrite using `[Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero (fun y _ => if_neg (fun h => hx h.1.symm))) (by simp)]`. Rewrite using `[Finset.sum_eq_single b (fun y _ hy => if_neg (fun h => hy h.2.symm)) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem matrixAction_single {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) : actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  simp only [actM, Matrix.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero (fun y _ => if_neg (fun h => hx h.1.symm)))
    (by simp)]
  rw [Finset.sum_eq_single b (fun y _ hy => if_neg (fun h => hy h.2.symm)) (by simp)]
  simp

/- English proof (translation)
Rewrite using `[Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem signMatrix_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem signMatrix_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

/- English proof (translation)
Establish `hJ` using `signMatrix_mul_self ε`. Establish `hJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Establish `hc : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Unfold `inG`.

Rewrite using `[Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, signMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one, smul_sub, smul_add, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem hermPart_mem_lieAlgebra (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε)) := by
  have hJ := signMatrix_mul_self ε
  have hJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold inG
  rw [Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, signMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc,
    hJ, hJ', Matrix.mul_one, smul_sub, smul_add, neg_smul]
  abel

/- English proof (translation)
Establish `hJ` using `signMatrix_mul_self ε`. Establish `hJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Establish `key : ∀ c : ℂ, star c = -c → inG ε (c • (M + Jm ε * Mᴴ * Jm ε))`. Introduce `c hc`.

Unfold `inG`. Rewrite using `[Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, signMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[neg_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add_eq_zero]`. Use `congr 1`. Simplify using `only [add_mul, mul_add, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Apply `key` to reduce the goal to its premises. Rewrite using `[Complex.star_def, map_div₀, map_neg, Complex.conj_I, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermPart_mem_lieAlgebra_var (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I / 2 : ℂ) • (M + Jm ε * Mᴴ * Jm ε)) := by
  have hJ := signMatrix_mul_self ε
  have hJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have key : ∀ c : ℂ, star c = -c → inG ε (c • (M + Jm ε * Mᴴ * Jm ε)) := by
    intro c hc
    unfold inG
    rw [Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, signMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rw [neg_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add_eq_zero]
    congr 1
    simp only [add_mul, mul_add, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    abel
  apply key
  rw [Complex.star_def, map_div₀, map_neg, Complex.conj_I, map_ofNat]
  ring

/- English proof (translation)
Rewrite using `[smul_smul, show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by`. Rewrite using `[mul_div_assoc', mul_neg, Complex.I_mul_I]`. Use the proof step `norm_num]`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem matrix_decomp_lieAlgebra (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) + Complex.I • ((-Complex.I / 2 : ℂ) • (M + Jm ε * Mᴴ * Jm ε)) := by
  rw [smul_smul, show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `show (g * h)ᴴ * Jm ε * (g * h) = Jm ε`. Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `hh' : hᴴ * Jm ε * h = Jm ε` using `hh`. Rewrite using `[Matrix.conjTranspose_mul, show hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h by simp only [Matrix.mul_assoc], hg', hh']`.
-/
theorem mul_mem_unitaryJ {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h by simp only [Matrix.mul_assoc],
    hg', hh']

/- English proof (translation)
Use `show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε`. Simplify using the standard rewrite rules.
-/
theorem one_mem_unitaryJ (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
  simp

/- English proof (translation)
Set `T : Submodule ℂ D` to `{ carrier := {v | ∀ g ∈ UJset ε, σ g (v : H) ∈ A} add_mem' := by`. Introduce `u w hu hw g hg`. Simplify using `only [Set.mem_setOf_eq] at hu hw`. Simplify using `using A.add_mem (hu g hg) (hw g hg)`. Use the proof step `zero_mem' := by`.

Introduce `g hg`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c v hv g hg`. Simplify using `only [Set.mem_setOf_eq] at hv`.

Simplify using `using A.smul_mem c (hv g hg) }`. Establish `hder : ∀ X, inG ε X → ∀ v ∈ T, actM E X v ∈ T`. Introduce `X hX v hv`. Establish `hv' : ∀ g ∈ UJset ε, σ g (v : H) ∈ A` using `hv`. Use `show ∀ g ∈ UJset ε, σ g ((actM E X v : D) : H) ∈ A`.

Introduce `g hg`. Establish `hd` using `hD.deriv X hX v`. Establish `hd2 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) (σ g ((actM E X v : D) : H)) 0` using `((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Establish `hval : ∀ t : ℝ, σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ∈ A`. Introduce `t`.

Establish `hmul` using `hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)`. Establish `h5` using `hv' (g * NormedSpace.exp ((t : ℂ) • X)) (mul_mem_unitaryJ hg (exp_smul_mem_UJset hX t))`. Rewrite `h5` using `[hmul]`. Conclude with `h5`. Use `hA.mem_of_tendsto hd2.tendsto_slope_zero ?_` and prove the remaining obligations.

Use `filter_upwards with t`. Conclude with `A.smul_of_tower_mem _ (A.sub_mem (hval _) (hval _))`. Establish `hE : ∀ a b, ∀ v ∈ T, E a b v ∈ T`. Introduce `a b v hv`. Rewrite using `[← matrixAction_single E a b, matrix_decomp_lieAlgebra ε (Matrix.single a b (1 : ℂ)), matrixAction_add, matrixAction_smul E Complex.I, LinearMap.add_apply, LinearMap.smul_apply]`.

Conclude with `T.add_mem (hder _ (hermPart_mem_lieAlgebra ε _) v hv) (T.smul_mem _ (hder _ (hermPart_mem_lieAlgebra_var ε _) v hv))`. Establish `hGT : genSub E V ≤ T` using `sInf_le ⟨fun v hv => (show ∀ g ∈ UJset ε, σ g (v : H) ∈ A from fun g hg => hVA g hg v hv), hE⟩`. Use `Submodule.topologicalClosure_minimal _ ?_ hA` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `h1 : σ 1 (v : H) ∈ A` using `(show ∀ g ∈ UJset ε, σ g (v : H) ∈ A from hGT hv) 1 (one_mem_unitaryJ ε)`.

Rewrite `h1` using `[hσ.1.1]`. Simplify using `using h1`.
-/
theorem generatedSub_closure_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (A : Submodule ℂ H) (hA : IsClosed (A : Set H))
    (hVA : ∀ g ∈ UJset ε, ∀ v ∈ V, σ g (v : H) ∈ A) :
    ((genSub E V).map D.subtype).topologicalClosure ≤ A := by
  let T : Submodule ℂ D :=
    { carrier := {v | ∀ g ∈ UJset ε, σ g (v : H) ∈ A}
      add_mem' := by
        intro u w hu hw g hg
        simp only [Set.mem_setOf_eq] at hu hw
        simpa using A.add_mem (hu g hg) (hw g hg)
      zero_mem' := by
        intro g hg
        simp
      smul_mem' := by
        intro c v hv g hg
        simp only [Set.mem_setOf_eq] at hv
        simpa using A.smul_mem c (hv g hg) }
  have hder : ∀ X, inG ε X → ∀ v ∈ T, actM E X v ∈ T := by
    intro X hX v hv
    have hv' : ∀ g ∈ UJset ε, σ g (v : H) ∈ A := hv
    show ∀ g ∈ UJset ε, σ g ((actM E X v : D) : H) ∈ A
    intro g hg
    have hd := hD.deriv X hX v
    have hd2 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
        (σ g ((actM E X v : D) : H)) 0 :=
      ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have hval : ∀ t : ℝ, σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ∈ A := by
      intro t
      have hmul := hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)
      have h5 := hv' (g * NormedSpace.exp ((t : ℂ) • X)) (mul_mem_unitaryJ hg (exp_smul_mem_UJset hX t))
      rw [hmul] at h5
      exact h5
    refine hA.mem_of_tendsto hd2.tendsto_slope_zero ?_
    filter_upwards with t
    exact A.smul_of_tower_mem _ (A.sub_mem (hval _) (hval _))
  have hE : ∀ a b, ∀ v ∈ T, E a b v ∈ T := by
    intro a b v hv
    rw [← matrixAction_single E a b, matrix_decomp_lieAlgebra ε (Matrix.single a b (1 : ℂ)), matrixAction_add,
      matrixAction_smul E Complex.I, LinearMap.add_apply, LinearMap.smul_apply]
    exact T.add_mem (hder _ (hermPart_mem_lieAlgebra ε _) v hv) (T.smul_mem _ (hder _ (hermPart_mem_lieAlgebra_var ε _) v hv))
  have hGT : genSub E V ≤ T := sInf_le ⟨fun v hv =>
    (show ∀ g ∈ UJset ε, σ g (v : H) ∈ A from fun g hg => hVA g hg v hv), hE⟩
  refine Submodule.topologicalClosure_minimal _ ?_ hA
  rintro _ ⟨v, hv, rfl⟩
  have h1 : σ 1 (v : H) ∈ A := (show ∀ g ∈ UJset ε, σ g (v : H) ∈ A from hGT hv) 1 (one_mem_unitaryJ ε)
  rw [hσ.1.1] at h1
  simpa using h1

end ReciprocityTheory.ChartRestriction.DS
