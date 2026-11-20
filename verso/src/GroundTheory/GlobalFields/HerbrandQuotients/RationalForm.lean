import Mathlib

namespace GroundTheory.Global

open Matrix

/- English proof (translation)
Take `⟨V, hV⟩ : ∃ V : Submodule ℚ ℝ, V = Submodule.span ℚ (Set.range fun p : ι × ι => P p.1 p.2)` from `⟨_, rfl⟩`. Establish `: Module.Finite ℚ V` using `hV ▸ Module.Finite.span_of_finite ℚ (Set.finite_range _)`. Take `⟨κ, _, ⟨c⟩⟩ : ∃ (κ : Type) (_ : Fintype κ), Nonempty (Module.Basis κ ℚ V)` from `⟨_, inferInstance, ⟨Module.Free.chooseBasis ℚ V⟩⟩`. Establish `hmem : ∀ a b, P a b ∈ V` using `fun a b => hV ▸ Submodule.subset_span ⟨(a, b), rfl⟩`. Set `Bm : κ → Matrix ι ι ℚ` to `fun k a b => c.repr ⟨P a b, hmem a b⟩ k`.

Establish `hcast : ∀ (q : ℚ) (r : ℝ), q • r = (q : ℝ) * r` using `fun q r => by`. Rewrite using `[Algebra.smul_def, eq_ratCast]`. Establish `hP_eq : P = ∑ k, (c k : ℝ) • (Bm k).map (Rat.cast : ℚ → ℝ)`. Use extensionality with `a b`. Establish `h1` using `congrArg (Subtype.val : V → ℝ) (c.sum_repr ⟨P a b, hmem a b⟩)`.

Rewrite `h1` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, hcast] at h1`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Rewrite using `[← h1]`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hli : LinearIndependent ℚ (fun k => (c k : ℝ))` using `c.linearIndependent.map' V.subtype (Submodule.ker_subtype V)`. Establish `hB : ∀ k j, Bm k * A j = A' j * Bm k`. Introduce `k j`. Establish `hsum : ∑ k, (c k : ℝ) • (Bm k * A j - A' j * Bm k).map (Rat.cast : ℚ → ℝ) = 0`.

Establish `hmap : ∀ X Y : Matrix ι ι ℚ, (X * Y).map (Rat.cast : ℚ → ℝ) = X.map (Rat.cast : ℚ → ℝ) * Y.map (Rat.cast : ℚ → ℝ)` using `fun X Y => Matrix.map_mul (f := Rat.castHom ℝ)`. Establish `hsub : ∀ X Y : Matrix ι ι ℚ, (X - Y).map (Rat.cast : ℚ → ℝ) = X.map (Rat.cast : ℚ → ℝ) - Y.map (Rat.cast : ℚ → ℝ)` using `fun X Y => by ext; simp`. Establish `e1 : ∑ k, (c k : ℝ) • ((Bm k).map (Rat.cast : ℚ → ℝ) * (A j).map (Rat.cast : ℚ → ℝ)) = P * (A j).map (Rat.cast : ℚ → ℝ)`. Rewrite using `[hP_eq, Finset.sum_mul]`. Simplify using `only [Matrix.smul_mul]`.

Establish `e2 : ∑ k, (c k : ℝ) • ((A' j).map (Rat.cast : ℚ → ℝ) * (Bm k).map (Rat.cast : ℚ → ℝ)) = (A' j).map (Rat.cast : ℚ → ℝ) * P`. Rewrite using `[hP_eq, Finset.mul_sum]`. Simplify using `only [Matrix.mul_smul]`. Simplify using `only [hsub, hmap, smul_sub, Finset.sum_sub_distrib, e1, e2, h j, sub_self]`. Use extensionality with `a b`.

Establish `hab` using `congrFun (congrFun hsum a) b`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply] at hab`. Use `Fintype.linearIndependent_iff.1 hli (fun k => (Bm k * A j - A' j * Bm k) a b) (by simpa only [hcast, mul_comm] using hab) k` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Use `clear_value Bm`.

Take `⟨Mx, hMx⟩ : ∃ Mx : Matrix ι ι (MvPolynomial κ ℚ), Mx = Matrix.of fun a b => ∑ k, MvPolynomial.X k * MvPolynomial.C (Bm k a b)` from `⟨_, rfl⟩`. Establish `hev : ∀ (t : κ → ℝ), (MvPolynomial.aeval t : MvPolynomial κ ℚ →ₐ[ℚ] ℝ).mapMatrix Mx = Matrix.of fun a b => ∑ k, t k * algebraMap ℚ ℝ (Bm k a b)`. Introduce `t`. Use extensionality with `a b`. Rewrite using `[AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`.

Rewrite using `[hMx, Matrix.of_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]`. Establish `hPof : P = Matrix.of fun a b => ∑ k, (c k : ℝ) * algebraMap ℚ ℝ (Bm k a b)`. Use `hP_eq.trans ?_` and prove the remaining obligations.

Use extensionality with `a b`. Rewrite using `[Matrix.sum_apply, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eq_ratCast]`. Establish `hF : Mx.det ≠ 0`.

Introduce `h0`. Apply `hP` to reduce the goal to its premises. Rewrite using `[hPof, ← hev, ← AlgHom.map_det, h0]`. Conclude with `map_zero _`. Take `⟨q, hq⟩ : ∃ q : κ → ℚ, MvPolynomial.eval q Mx.det ≠ 0` from `by by_contra! hall`.

Conclude with `hF (MvPolynomial.funext fun x => by rw [hall x, map_zero])`. Use `⟨∑ k, q k • Bm k, ?_, fun j => ?_⟩` and prove the remaining obligations. Establish `hQ : ∑ k, q k • Bm k = Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b)`. Use extensionality with `a b`. Rewrite using `[Matrix.sum_apply, Matrix.of_apply]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]`. Establish `hevq : (MvPolynomial.eval q).mapMatrix Mx = Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b)`. Use extensionality with `a b`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hMx, Matrix.of_apply, Matrix.of_apply, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.algebraMap_self, RingHom.id_apply]`. Use `RingHom.map_det (MvPolynomial.eval q) Mx` as an intermediate fact. Rewrite `this` using `[hevq]`. Rewrite using `[hQ, ← this]`.

Conclude with `hq`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul, Matrix.mul_smul, hB]`.
-/
theorem exists_rat_intertwiner {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (A A' : J → Matrix ι ι ℚ) (P : Matrix ι ι ℝ) (hP : P.det ≠ 0)
    (h : ∀ j, P * (A j).map (Rat.cast : ℚ → ℝ) = (A' j).map (Rat.cast : ℚ → ℝ) * P) :
    ∃ Q : Matrix ι ι ℚ, Q.det ≠ 0 ∧ ∀ j, Q * A j = A' j * Q := by

  obtain ⟨V, hV⟩ : ∃ V : Submodule ℚ ℝ,
      V = Submodule.span ℚ (Set.range fun p : ι × ι => P p.1 p.2) := ⟨_, rfl⟩
  have : Module.Finite ℚ V := hV ▸ Module.Finite.span_of_finite ℚ (Set.finite_range _)
  obtain ⟨κ, _, ⟨c⟩⟩ : ∃ (κ : Type) (_ : Fintype κ), Nonempty (Module.Basis κ ℚ V) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℚ V⟩⟩
  have hmem : ∀ a b, P a b ∈ V := fun a b => hV ▸ Submodule.subset_span ⟨(a, b), rfl⟩

  let Bm : κ → Matrix ι ι ℚ := fun k a b => c.repr ⟨P a b, hmem a b⟩ k
  have hcast : ∀ (q : ℚ) (r : ℝ), q • r = (q : ℝ) * r := fun q r => by
    rw [Algebra.smul_def, eq_ratCast]
  have hP_eq : P = ∑ k, (c k : ℝ) • (Bm k).map (Rat.cast : ℚ → ℝ) := by
    ext a b
    have h1 := congrArg (Subtype.val : V → ℝ) (c.sum_repr ⟨P a b, hmem a b⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul, hcast] at h1
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hli : LinearIndependent ℚ (fun k => (c k : ℝ)) :=
    c.linearIndependent.map' V.subtype (Submodule.ker_subtype V)

  have hB : ∀ k j, Bm k * A j = A' j * Bm k := by
    intro k j
    have hsum : ∑ k, (c k : ℝ) • (Bm k * A j - A' j * Bm k).map (Rat.cast : ℚ → ℝ) = 0 := by
      have hmap : ∀ X Y : Matrix ι ι ℚ, (X * Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) * Y.map (Rat.cast : ℚ → ℝ) := fun X Y =>
        Matrix.map_mul (f := Rat.castHom ℝ)
      have hsub : ∀ X Y : Matrix ι ι ℚ, (X - Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) - Y.map (Rat.cast : ℚ → ℝ) := fun X Y => by
        ext; simp
      have e1 : ∑ k, (c k : ℝ) • ((Bm k).map (Rat.cast : ℚ → ℝ) * (A j).map (Rat.cast : ℚ → ℝ)) =
          P * (A j).map (Rat.cast : ℚ → ℝ) := by
        rw [hP_eq, Finset.sum_mul]
        simp only [Matrix.smul_mul]
      have e2 : ∑ k, (c k : ℝ) • ((A' j).map (Rat.cast : ℚ → ℝ) * (Bm k).map (Rat.cast : ℚ → ℝ)) =
          (A' j).map (Rat.cast : ℚ → ℝ) * P := by
        rw [hP_eq, Finset.mul_sum]
        simp only [Matrix.mul_smul]
      simp only [hsub, hmap, smul_sub, Finset.sum_sub_distrib, e1, e2, h j, sub_self]
    ext a b
    have hab := congrFun (congrFun hsum a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at hab
    have := Fintype.linearIndependent_iff.1 hli (fun k => (Bm k * A j - A' j * Bm k) a b)
      (by simpa only [hcast, mul_comm] using hab) k
    rwa [Matrix.sub_apply, sub_eq_zero] at this

  clear_value Bm
  obtain ⟨Mx, hMx⟩ : ∃ Mx : Matrix ι ι (MvPolynomial κ ℚ),
      Mx = Matrix.of fun a b => ∑ k, MvPolynomial.X k * MvPolynomial.C (Bm k a b) := ⟨_, rfl⟩
  have hev : ∀ (t : κ → ℝ),
      (MvPolynomial.aeval t : MvPolynomial κ ℚ →ₐ[ℚ] ℝ).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, t k * algebraMap ℚ ℝ (Bm k a b) := by
    intro t
    ext a b
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hMx, Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have hPof : P = Matrix.of fun a b => ∑ k, (c k : ℝ) * algebraMap ℚ ℝ (Bm k a b) := by
    refine hP_eq.trans ?_
    ext a b
    rw [Matrix.sum_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eq_ratCast]
  have hF : Mx.det ≠ 0 := by
    intro h0
    apply hP
    rw [hPof, ← hev, ← AlgHom.map_det, h0]
    exact map_zero _
  obtain ⟨q, hq⟩ : ∃ q : κ → ℚ, MvPolynomial.eval q Mx.det ≠ 0 := by
    by_contra! hall
    exact hF (MvPolynomial.funext fun x => by rw [hall x, map_zero])
  refine ⟨∑ k, q k • Bm k, ?_, fun j => ?_⟩
  · have hQ : ∑ k, q k • Bm k = Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [Matrix.sum_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
    have hevq : (MvPolynomial.eval q).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hMx, Matrix.of_apply, Matrix.of_apply,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.algebraMap_self,
        RingHom.id_apply]
    have := RingHom.map_det (MvPolynomial.eval q) Mx
    rw [hevq] at this
    rw [hQ, ← this]
    exact hq
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul, Matrix.mul_smul, hB]

end GroundTheory.Global
