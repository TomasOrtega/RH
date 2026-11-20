import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n A E _ _ _ D S _ _ x y`. Set `i : S →ₐ[A] S[X]` to `IsScalarTower.toAlgHom A S S[X]`. Set `ι` to `Algebra.TensorProduct.map i (AlgHom.id A E)`. Set `ev : S → (S[X] →ₐ[A] S)` to `fun c => (Polynomial.aeval c : S[X] →ₐ[S] S).restrictScalars A`. Set `π` to `fun c => Algebra.TensorProduct.map (ev c) (AlgHom.id A E)`.

Establish `hπι : ∀ c z, π c (ι z) = z`. Introduce `c z`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `tmul s e => simp [π, ι, ev, i]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Set `t : S[X] ⊗[A] E` to `X ⊗ₜ 1`. Establish `ht : ∀ c, π c t = c ⊗ₜ 1`. Introduce `c`. Simplify using `[π, t, ev]`.

Set `u : S[X] ⊗[A] E` to `1 + t * ι (x - 1)`. Establish `hu0 : π 0 u = 1`. Simplify using `only [u, map_add, map_mul, map_one, hπι, ht]`. Simplify using the standard rewrite rules. Establish `hu1 : π 1 u = x`.

Simplify using `only [u, map_add, map_mul, map_one, hπι, ht]`. Rewrite using `[← Algebra.TensorProduct.one_def]`. Simplify using the standard rewrite rules. Establish `hc : (D.D S[X] u).coeff 0 = 1`. Establish `h` using `D.nat S[X] S (ev 0) u`.

Express the relevant statement in the definitionally equal form `D.D S (π 0 u) = _ at h`. Rewrite `h` using `[hu0, map_one]`. Rewrite using `[h]`. Simplify using `[ev, Polynomial.coeff_zero_eq_eval_zero]`. Establish `hnz : D.D S[X] u ∈ nonZeroDivisors S[X]` using `Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by rw [hc]; exact one_mem _)`.

Establish `key : D.D S[X] (1 + u * ι y) = D.D S[X] (1 + ι y * u)`. Establish `h : (1 + u * ι y) * u = u * (1 + ι y * u)` using `by noncomm_ring`. Establish `h2` using `congrArg (D.D S[X]) h`. Rewrite `h2` using `[map_mul, map_mul, mul_comm (D.D S[X] u)]`. Conclude with `(mul_cancel_right_mem_nonZeroDivisors hnz).1 h2`.

Establish `h` using `congrArg (ev 1) key`. Rewrite `h` using `[← D.nat, ← D.nat]`. Express the relevant statement in the definitionally equal form `D.D S (π 1 _) = D.D S (π 1 _) at h`. Simplify `h` using `only [map_add, map_mul, map_one, hπι, hu1]`.
-/
theorem UpperTheory.V.CA.d_comm :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E), D.D S (1 + x * y) = D.D S (1 + y * x) := by
  intro n A E _ _ _ D S _ _ x y
  let i : S →ₐ[A] S[X] := IsScalarTower.toAlgHom A S S[X]
  let ι := Algebra.TensorProduct.map i (AlgHom.id A E)
  let ev : S → (S[X] →ₐ[A] S) := fun c => (Polynomial.aeval c : S[X] →ₐ[S] S).restrictScalars A
  let π := fun c => Algebra.TensorProduct.map (ev c) (AlgHom.id A E)
  have hπι : ∀ c z, π c (ι z) = z := by
    intro c z
    induction z with
    | zero => simp
    | tmul s e => simp [π, ι, ev, i]
    | add a b ha hb => simp only [map_add, ha, hb]
  let t : S[X] ⊗[A] E := X ⊗ₜ 1
  have ht : ∀ c, π c t = c ⊗ₜ 1 := by
    intro c
    simp [π, t, ev]
  let u : S[X] ⊗[A] E := 1 + t * ι (x - 1)
  have hu0 : π 0 u = 1 := by
    simp only [u, map_add, map_mul, map_one, hπι, ht]
    simp
  have hu1 : π 1 u = x := by
    simp only [u, map_add, map_mul, map_one, hπι, ht]
    rw [← Algebra.TensorProduct.one_def]
    simp
  have hc : (D.D S[X] u).coeff 0 = 1 := by
    have h := D.nat S[X] S (ev 0) u
    change D.D S (π 0 u) = _ at h
    rw [hu0, map_one] at h
    rw [h]
    simp [ev, Polynomial.coeff_zero_eq_eval_zero]
  have hnz : D.D S[X] u ∈ nonZeroDivisors S[X] :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by rw [hc]; exact one_mem _)
  have key : D.D S[X] (1 + u * ι y) = D.D S[X] (1 + ι y * u) := by
    have h : (1 + u * ι y) * u = u * (1 + ι y * u) := by noncomm_ring
    have h2 := congrArg (D.D S[X]) h
    rw [map_mul, map_mul, mul_comm (D.D S[X] u)] at h2
    exact (mul_cancel_right_mem_nonZeroDivisors hnz).1 h2
  have h := congrArg (ev 1) key
  rw [← D.nat, ← D.nat] at h
  change D.D S (π 1 _) = D.D S (π 1 _) at h
  simpa only [map_add, map_mul, map_one, hπι, hu1] using h
