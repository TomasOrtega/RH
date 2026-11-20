import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Take `⟨a, s⟩` from `y`. Take `rfl : s = -1` from `hr`. Establish `h : ((-1 : ℤˣ) = 1) = False` using `by decide`. Establish `h1 : a * theta a = 1`. Use `congrArg SemidirectProduct.left hy` as an intermediate fact.

Simplify `this` using `[SemidirectProduct.mul_left]`. Establish `h3 : theta a = a⁻¹` using `eq_inv_of_mul_eq_one_right h1`. Establish `h4 : (a : Matrix (Fin 3) (Fin 3) R) = Jmat R 3 * (a : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3`. Rewrite using `[← theta_inv_val, h3, inv_inv]`. Establish `hJ` using `Jmat_mul_Jmat (R := R) 3`.

Use `set A : Matrix (Fin 3) (Fin 3) R := a.val with hA`. Use `set A' : Matrix (Fin 3) (Fin 3) R := (a⁻¹ : GL (Fin 3) R).val with hA'`. Establish `hAA : A' * A = 1` using `by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hAA' : A * A' = 1` using `by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hB : (A * Jmat R 3)ᵀ = A * Jmat R 3`.

Rewrite using `[Matrix.transpose_mul, Jmat_transpose]`. Use `conv_rhs => rw [h4, Matrix.mul_assoc, hJ, Matrix.mul_one]`. Establish `key : ∀ X : Matrix (Fin 3) (Fin 3) R, GG.ad 3 R ⟨a, -1⟩ X = X → (X * (A * Jmat R 3))ᵀ = -(X * (A * Jmat R 3))`. Introduce `X hX`. Establish `hX' : A * (-(Jmat R 3 * Xᵀ * Jmat R 3)) * A' = X`.

Simplify `hX` using `only [GG.ad_apply, GG.adFun, GG.mat, h, if_false, thetaLie]`. Rewrite using `[Matrix.transpose_mul, hB]`. Use `conv_rhs => rw [← hX']`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc A' A, hAA, Matrix.one_mul, hJ, Matrix.mul_one]`.

Establish `anti : ∀ Y : Matrix (Fin 3) (Fin 3) R, Yᵀ = -Y → Y 0 1 = 0 → Y 0 2 = 0 → Y 1 2 = 0 → Y = 0`. Introduce `Y hY e1 e2 e3`. Establish `hs : ∀ i j, Y j i = -Y i j` using `fun i j => congrFun (congrFun hY i) j`. Establish `hd : ∀ i, Y i i = 0` using `fun i => by`. Apply `h2.mul_left_cancel` to reduce the goal to its premises.

Use `hs i i` as an intermediate fact. Take the linear combination `this`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [hd, e1, e2, e3, hs 0 1, hs 0 2, hs 1 2]`. Set `f : Matrix (Fin 3) (Fin 3) R → R × R × R` to `fun X => ((X * (A * Jmat R 3)) 0 1, (X * (A * Jmat R 3)) 0 2, (X * (A * Jmat R 3)) 1 2)`.

Establish `hinj : Set.InjOn f {X : Matrix (Fin 3) (Fin 3) R | GG.ad 3 R ⟨a, -1⟩ X = X}`. Introduce `X hX X' hX' hf`. Simplify using `only [f, Prod.mk.injEq] at hf`. Establish `h0 : X * (A * Jmat R 3) - X' * (A * Jmat R 3) = 0`. Apply `anti` to reduce the goal to its premises.

Rewrite using `[Matrix.transpose_sub, key X hX, key X' hX']`. Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.sub_apply, hf.1, sub_self]`. Rewrite using `[Matrix.sub_apply, hf.2.1, sub_self]`. Rewrite using `[Matrix.sub_apply, hf.2.2, sub_self]`.

Establish `h5` using `congrArg (· * (Jmat R 3 * A')) (sub_eq_zero.1 h0)`. Simplify using `only [Matrix.mul_assoc] at h5`. Rewrite `h5` using `[← Matrix.mul_assoc (Jmat R 3), hJ, Matrix.one_mul, hAA', Matrix.mul_one, Matrix.mul_one]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem arch_gen {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R)) (y : GG 3 R)
    (hy : y * y = 1) (hr : y.right = -1) :
    {X : Matrix (Fin 3) (Fin 3) R | GG.ad 3 R y X = X}.ncard ≤ Nat.card R ^ 3 := by
  obtain ⟨a, s⟩ := y
  obtain rfl : s = -1 := hr
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  have h1 : a * theta a = 1 := by
    have := congrArg SemidirectProduct.left hy
    simpa [SemidirectProduct.mul_left] using this
  have h3 : theta a = a⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h4 : (a : Matrix (Fin 3) (Fin 3) R) = Jmat R 3 * (a : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := by
    rw [← theta_inv_val, h3, inv_inv]
  have hJ := Jmat_mul_Jmat (R := R) 3
  set A : Matrix (Fin 3) (Fin 3) R := a.val with hA
  set A' : Matrix (Fin 3) (Fin 3) R := (a⁻¹ : GL (Fin 3) R).val with hA'
  have hAA : A' * A = 1 := by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB : (A * Jmat R 3)ᵀ = A * Jmat R 3 := by
    rw [Matrix.transpose_mul, Jmat_transpose]
    conv_rhs => rw [h4, Matrix.mul_assoc, hJ, Matrix.mul_one]
  have key : ∀ X : Matrix (Fin 3) (Fin 3) R, GG.ad 3 R ⟨a, -1⟩ X = X →
      (X * (A * Jmat R 3))ᵀ = -(X * (A * Jmat R 3)) := by
    intro X hX
    have hX' : A * (-(Jmat R 3 * Xᵀ * Jmat R 3)) * A' = X := by
      simpa only [GG.ad_apply, GG.adFun, GG.mat, h, if_false, thetaLie] using hX
    rw [Matrix.transpose_mul, hB]
    conv_rhs => rw [← hX']
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A' A, hAA, Matrix.one_mul, hJ, Matrix.mul_one]
  have anti : ∀ Y : Matrix (Fin 3) (Fin 3) R, Yᵀ = -Y → Y 0 1 = 0 → Y 0 2 = 0 → Y 1 2 = 0 → Y = 0 := by
    intro Y hY e1 e2 e3
    have hs : ∀ i j, Y j i = -Y i j := fun i j => congrFun (congrFun hY i) j
    have hd : ∀ i, Y i i = 0 := fun i => by
      apply h2.mul_left_cancel
      have := hs i i
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, e1, e2, e3, hs 0 1, hs 0 2, hs 1 2]
  let f : Matrix (Fin 3) (Fin 3) R → R × R × R := fun X =>
    ((X * (A * Jmat R 3)) 0 1, (X * (A * Jmat R 3)) 0 2, (X * (A * Jmat R 3)) 1 2)
  have hinj : Set.InjOn f {X : Matrix (Fin 3) (Fin 3) R | GG.ad 3 R ⟨a, -1⟩ X = X} := by
    intro X hX X' hX' hf
    simp only [f, Prod.mk.injEq] at hf
    have h0 : X * (A * Jmat R 3) - X' * (A * Jmat R 3) = 0 := by
      apply anti
      · rw [Matrix.transpose_sub, key X hX, key X' hX']; abel
      · rw [Matrix.sub_apply, hf.1, sub_self]
      · rw [Matrix.sub_apply, hf.2.1, sub_self]
      · rw [Matrix.sub_apply, hf.2.2, sub_self]
    have h5 := congrArg (· * (Jmat R 3 * A')) (sub_eq_zero.1 h0)
    simp only [Matrix.mul_assoc] at h5
    rwa [← Matrix.mul_assoc (Jmat R 3), hJ, Matrix.one_mul, hAA', Matrix.mul_one, Matrix.mul_one] at h5
  calc _ ≤ (Set.univ : Set (R × R × R)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun _ _ => Set.mem_univ _) hinj (Set.toFinite _)
    _ = Nat.card R ^ 3 := by rw [Set.ncard_univ, Nat.card_prod, Nat.card_prod]; ring

/- English proof (translation)
Introduce `l hl O _ _ _ _ _ hl0 hl2 x hx hr k _`. Establish `hfin : Finite (Ok l O k)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hne : Ideal.span {(l : O) ^ k} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `pow_ne_zero _ hl0`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ`. Use `haveI : Finite (O ⧸ maximalIdeal O) := (inferInstance : Finite (ResidueField O))`. Establish `hf : Finite (O ⧸ maximalIdeal O ^ n)` using `Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n`. Rewrite `hf` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn]`.

Conclude with `hf`. Establish `h2 : IsUnit (2 : O)`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_ofNat]`. Introduce `h`. Establish `h' : ((2 : ℕ) : ResidueField O) = 0` using `by exact_mod_cast h`.

Rewrite `h'` using `[CharP.cast_eq_zero_iff (ResidueField O) l]`. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')`. Establish `h2' : IsUnit (2 : Ok l O k)`. Simplify `h2.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))` using `only [map_ofNat]`. Conclude with `arch_gen h2' _ (by rw [← map_mul, hx, map_one]) hr`.
-/
theorem UpperTheory.V.Z.J.archUp :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → l ≠ 2 → ∀ (x : GG 3 O), x * x = 1 → x.right = -1 → ∀ k, 0 < k → {X : Matrix (Fin 3) (Fin 3) (Ok l O k) | GG.ad 3 (Ok l O k) (GG.map (Ideal.Quotient.mk _) x) X = X}.ncard ≤ Nat.card (Ok l O k) ^ 3 := by
  intro l hl O _ _ _ _ _ hl0 hl2 x hx hr k _
  have hfin : Finite (Ok l O k) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hne : Ideal.span {(l : O) ^ k} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hl0
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
    haveI : Finite (O ⧸ maximalIdeal O) := (inferInstance : Finite (ResidueField O))
    have hf : Finite (O ⧸ maximalIdeal O ^ n) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at hf
    exact hf
  have h2 : IsUnit (2 : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h
    have h' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')
  have h2' : IsUnit (2 : Ok l O k) := by
    simpa only [map_ofNat] using h2.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))
  exact arch_gen h2' _ (by rw [← map_mul, hx, map_one]) hr
