import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Use `set P : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if p k then (1 : R) else 0) with hP`. Use `set Q : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if q k then (1 : R) else 0) with hQ`. Establish `hPw : P * w = w * Q`. Use extensionality with `a b`. Rewrite using `[hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Distinguish the cases in `hab : p a = q b`. Rewrite using `[hab, mul_comm]`. Rewrite using `[hw a b hab]`. Simplify using the standard rewrite rules. Establish `hQwi : Q * wi = wi * P`.

Combine the equalities or inequalities in the displayed calculation. Establish `hwi : ∀ a b, p b ≠ q a → wi a b = 0`. Introduce `a b hab`. Establish `e` using `congrFun (congrFun hQwi a) b`. Rewrite `e` using `[hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Apply the tactic sequence `cases hpa : p b <;> cases hqa : q a <;> simp_all`. Simplify using `only [Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[Finset.sum_mul]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hj : p j = q i`. Distinguish the cases in `hk : p k = q i`. Rewrite using `[hZ j k (hj.trans hk.symm)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw k i hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hwi i j hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem conjugate_diagonal_zero_of_parity {R : Type} [CommRing R] {n : ℕ} (p q : Fin n → Bool)
    (w wi Z : Matrix (Fin n) (Fin n) R) (h1 : w * wi = 1) (h2 : wi * w = 1)
    (hw : ∀ i j, p i ≠ q j → w i j = 0) (hZ : ∀ i j, p i = p j → Z i j = 0) (i : Fin n) :
    (wi * Z * w) i i = 0 := by
  classical
  set P : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if p k then (1 : R) else 0) with hP
  set Q : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if q k then (1 : R) else 0) with hQ
  have hPw : P * w = w * Q := by
    ext a b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : p a = q b
    · rw [hab, mul_comm]
    · rw [hw a b hab]; simp
  have hQwi : Q * wi = wi * P := by
    calc Q * wi = (wi * w) * Q * wi := by rw [h2, Matrix.one_mul]
      _ = wi * (w * Q) * wi := by rw [Matrix.mul_assoc wi w Q]
      _ = wi * (P * w) * wi := by rw [hPw]
      _ = wi * P * (w * wi) := by simp only [Matrix.mul_assoc]
      _ = wi * P := by rw [h1, Matrix.mul_one]
  have hwi : ∀ a b, p b ≠ q a → wi a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun hQwi a) b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    cases hpa : p b <;> cases hqa : q a <;> simp_all
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j = q i
  · by_cases hk : p k = q i
    · rw [hZ j k (hj.trans hk.symm)]; ring
    · rw [hw k i hk]; ring
  · rw [hwi i j hj]; ring

/- English proof (translation)
Introduce `l _ L G G0 h n x R _ _ v`. Establish `hmat : ∀ g, mat x.ρ g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A)` using `fun g => rfl`. Establish `hconj : ∀ g, x.wiX R v * x.ρX R g * x.wX R v = ((((x.w v)⁻¹ * x.ρ g * x.w v : GL (Fin n) x.A)) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A R)`. Introduce `g`. Simplify using `only [NP.wX, NP.wiX, NP.ρX, hmat, Units.val_mul, Matrix.map_mul]`.

Establish `hw1 : x.wX R v * x.wiX R v = 1`. Simplify using `only [NP.wX, NP.wiX]`. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hw2 : x.wiX R v * x.wX R v = 1`. Simplify using `only [NP.wX, NP.wiX]`.

Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨hw1, hw2, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z hZ i`. Use `conjugate_diagonal_zero_of_parity (fun k => decide ((k : ℕ) < x.a)) (x.ty v) _ _ Z hw1 hw2 ?_ ?_ i` and prove the remaining obligations. Introduce `a b hab`.

Simplify using `only [NP.wX, Matrix.map_apply]`. Rewrite using `[x.w_blk v a b hab, map_zero]`. Introduce `a b hab`. Use `(hZ a b).1 (by simpa using hab)` as an intermediate fact. Simplify using `using this`.

Introduce `g`. Establish `t` using `x.tri v g`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hconj, Matrix.map_apply]`. Conclude with `(congrArg (algebraMap x.A R) (t.1 i j hij)).trans (map_zero _)`.

Rewrite using `[hconj, Matrix.map_apply]`. Conclude with `congrArg (algebraMap x.A R) (t.2 i)`. Introduce `g g'`. Simplify using `only [NP.ρX, map_mul, Matrix.map_mul]`. Simplify using `only [NP.ρX, map_one]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Introduce `g i j`. Establish `hb` using `x.blk g i j`. Use `⟨fun _ => Submodule.mem_top, fun hn => ?_⟩` and prove the remaining obligations. Establish `h0` using `hb.2 hn`.

Rewrite `h0`, the goal using `[Submodule.mem_bot]`. Simplify using `only [NP.ρX, Matrix.map_apply, h0, map_zero]`. Introduce `g`. Establish `e` using `x.form g`. Establish `e2` using `congrArg (fun M => M.map (algebraMap x.A R)) e`.

Simplify using `only [Units.val_one, Matrix.mul_one] at e2`. Simplify using `only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul]`. Rewrite using `[e2]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Simplify using `[Matrix.one_apply, GFrame.eps, hij]`. Simplify using `[Matrix.one_apply, GFrame.eps, hij]`.
-/
theorem UpperTheory.V.Pa.oddDiag :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (R : Type) [CommRing R] [Algebra x.A R] (v : L.Vl), x.wX R v * x.wiX R v = 1 ∧ x.wiX R v * x.wX R v = 1 ∧ (∀ Z ∈ Od x.A R n x.a, ∀ i, (x.wiX R v * Z * x.wX R v) i i = 0) ∧ (∀ g, (∀ i j, j < i → (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i j = 0) ∧ ∀ i, (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i i = algebraMap x.A R (x.ψ v i g)) ∧ (∀ g g', x.ρX R (g * g') = x.ρX R g * x.ρX R g') ∧ x.ρX R 1 = 1 ∧ (∀ g, x.ρX R g ∈ Ev x.A R n x.a) ∧ ∀ g, (x.ρX R g)ᵀ * x.ρX R (G0.frame.conj g) = algebraMap x.A R ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) R) := by
  intro l _ L G G0 h n x R _ _ v
  have hmat : ∀ g, mat x.ρ g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := fun g => rfl
  have hconj : ∀ g, x.wiX R v * x.ρX R g * x.wX R v =
      ((((x.w v)⁻¹ * x.ρ g * x.w v : GL (Fin n) x.A)) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A R) := by
    intro g
    simp only [NP.wX, NP.wiX, NP.ρX, hmat, Units.val_mul, Matrix.map_mul]
  have hw1 : x.wX R v * x.wiX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hw2 : x.wiX R v * x.wX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨hw1, hw2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ i
    refine conjugate_diagonal_zero_of_parity (fun k => decide ((k : ℕ) < x.a)) (x.ty v) _ _ Z hw1 hw2 ?_ ?_ i
    · intro a b hab
      simp only [NP.wX, Matrix.map_apply]
      rw [x.w_blk v a b hab, map_zero]
    · intro a b hab
      have := (hZ a b).1 (by simpa using hab)
      simpa using this
  · intro g
    have t := x.tri v g
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hconj, Matrix.map_apply]
      exact (congrArg (algebraMap x.A R) (t.1 i j hij)).trans (map_zero _)
    · rw [hconj, Matrix.map_apply]
      exact congrArg (algebraMap x.A R) (t.2 i)
  · intro g g'
    simp only [NP.ρX, map_mul, Matrix.map_mul]
  · simp only [NP.ρX, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro g i j
    have hb := x.blk g i j
    refine ⟨fun _ => Submodule.mem_top, fun hn => ?_⟩
    have h0 := hb.2 hn
    rw [Submodule.mem_bot] at h0 ⊢
    simp only [NP.ρX, Matrix.map_apply, h0, map_zero]
  · intro g
    have e := x.form g
    have e2 := congrArg (fun M => M.map (algebraMap x.A R)) e
    simp only [Units.val_one, Matrix.mul_one] at e2
    simp only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul]
    rw [e2]
    ext i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, GFrame.eps, hij]
    · simp [Matrix.one_apply, GFrame.eps, hij]
