import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOfbox
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Establish `hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) Q), A * X.map μ = (A.map π * X).map μ` using `fun A X => by`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]`. Establish `hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) Q), X.map μ * A = (X * A.map π).map μ` using `fun A X => by`. Use extensionality with `i j`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (X i k), hm, mul_comm]`. Establish `h1 : ∀ X Y : Matrix (Fin n) (Fin n) Q, X.map μ * Y.map μ = 0` using `fun X Y => by`. Rewrite using `[hL]`.

Establish `: (X.map μ).map π = 0`. Use extensionality with `i j`. Conclude with `h0 _`. Rewrite using `[this, Matrix.zero_mul]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Establish `hadd : ∀ X Y : Matrix (Fin n) (Fin n) Q, (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ` using `fun X Y => by`. Establish `: (X + Y).map μ = X.map μ + Y.map μ`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[this, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Establish `hz : (0 : Matrix (Fin n) (Fin n) Q).map μ = 0`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Set `e : Matrix (Fin n) (Fin n) Q → GL (Fin n) C` to `fun X => ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hadd, add_neg_cancel, hz, add_zero], by rw [hadd, neg_add_cancel, hz, add_zero]⟩`. Establish `he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ` using `fun X => rfl`. Establish `hinv : ∀ X, (e X)⁻¹ = e (-X)` using `fun X => Units.ext rfl`. Establish `hconj : ∀ (a : GL (Fin n) C) (X : Matrix (Fin n) (Fin n) Q), a * e X = e ((a : Matrix (Fin n) (Fin n) C).map π * X * (((GeneralLinearGroup.map π a)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) Q)) * a` using `fun a X => by`.

Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : (((GeneralLinearGroup.map π a)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) Q) * (a : Matrix (Fin n) (Fin n) C).map π = 1` using `(GeneralLinearGroup.map π a).inv_mul`. Rewrite using `[Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, hL, hR, Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]`. Establish `hth : ∀ X, theta (e X) = e (thetaLie X)` using `fun X => by`. Apply `Units.ext` to reduce the goal to its premises.

Establish `hJ : (Jmat C n).map π = Jmat Q n` using `Jmat_map π n`. Rewrite using `[theta_val, hinv, he, he, Matrix.transpose_add, Matrix.transpose_one, ← Matrix.transpose_map, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, hL, hR, hJ, thetaLie, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]`. Use `⟨e, he, fun X Y => Units.ext (hadd X Y).symm, hinv, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, s⟩ X`. Establish `hm : ((-1 : ℤˣ) = 1) = False` using `by decide`.

Apply `SemidirectProduct.ext` to reduce the goal to its premises. Simplify using `only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, GG.adFun, GG.map_right]`. Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Simplify using `only [sgnAct_one, if_true]`. Conclude with `hconj a X`.

Simplify using `only [sgnAct_neg_one, hm, if_false, hth]`. Conclude with `hconj a _`. Simplify using the standard rewrite rules.
-/
private theorem sq_exp {C Q : Type} [CommRing C] [CommRing Q] (n : ℕ) (π : C →+* Q) (μ : Q →+ C)
    (hm : ∀ a c, μ (π a * c) = a * μ c) (h0 : ∀ c, π (μ c) = 0) :
    ∃ e : Matrix (Fin n) (Fin n) Q → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧
      (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧
      ∀ (x : GG n C) (X : Matrix (Fin n) (Fin n) Q), x * GG.ofGL (e X) = GG.ofGL (e ((GG.map π x).adFun X)) * x := by
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) Q),
      A * X.map μ = (A.map π * X).map μ := fun A X => by
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) Q),
      X.map μ * A = (X * A.map π).map μ := fun A X => by
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hm, mul_comm]
  have h1 : ∀ X Y : Matrix (Fin n) (Fin n) Q, X.map μ * Y.map μ = 0 := fun X Y => by
    rw [hL]
    have : (X.map μ).map π = 0 := by
      ext i j
      exact h0 _
    rw [this, Matrix.zero_mul]
    ext i j
    simp
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) Q,
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := fun X Y => by
    have : (X + Y).map μ = X.map μ + Y.map μ := by
      ext i j
      simp
    rw [this, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  have hz : (0 : Matrix (Fin n) (Fin n) Q).map μ = 0 := by
    ext i j
    simp
  let e : Matrix (Fin n) (Fin n) Q → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hadd, add_neg_cancel, hz, add_zero],
      by rw [hadd, neg_add_cancel, hz, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (a : GL (Fin n) C) (X : Matrix (Fin n) (Fin n) Q),
      a * e X = e ((a : Matrix (Fin n) (Fin n) C).map π * X *
        (((GeneralLinearGroup.map π a)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) Q)) * a := fun a X => by
    apply Units.ext
    have h1 : (((GeneralLinearGroup.map π a)⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) Q) * (a : Matrix (Fin n) (Fin n) C).map π = 1 :=
      (GeneralLinearGroup.map π a).inv_mul
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, hL, hR, Matrix.mul_assoc,
      h1, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
  have hth : ∀ X, theta (e X) = e (thetaLie X) := fun X => by
    apply Units.ext
    have hJ : (Jmat C n).map π = Jmat Q n := Jmat_map π n
    rw [theta_val, hinv, he, he, Matrix.transpose_add, Matrix.transpose_one, ← Matrix.transpose_map,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, hL, hR, hJ, thetaLie,
      Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨e, he, fun X Y => Units.ext (hadd X Y).symm, hinv, ?_⟩
  rintro ⟨a, s⟩ X
  have hm : ((-1 : ℤˣ) = 1) = False := by decide
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      sgnAct_one, GG.adFun, GG.map_right]
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp only [sgnAct_one, if_true]
      exact hconj a X
    · simp only [sgnAct_neg_one, hm, if_false, hth]
      exact hconj a _
  · simp

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Break down `lt_or_ge b i with h' | h'` into its components or cases. Rewrite using `[hA i b h', zero_mul]`.

Rewrite using `[hB b j (lt_of_lt_of_le h h'), mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with h' | h'` into its components or cases. Rewrite using `[hA i b h', zero_mul]`.

Rewrite using `[hB b i h', mul_zero]`. Simplify using the standard rewrite rules.
-/
private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {A B : Matrix (Fin n) (Fin n) C} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b i with h' | h'
    · rw [hA i b h', zero_mul]
    · rw [hB b j (lt_of_lt_of_le h h'), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [hA i b h', zero_mul]
      · rw [hB b i h', mul_zero]
    · simp

/- English proof (translation)
Take `⟨e, e1, e2, e3, e4⟩` from `sq_exp n π μ hm h0`. Establish `e5 : ∀ s X, B.r s * GG.ofGL (e X) = GG.ofGL (e ((B.map π).ad s X)) * B.r s` using `fun s X => e4 _ X`. Establish `z1 : z 1 = 0`. Use `hz 1 1` as an intermediate fact. Rewrite `this` using `[mul_one, map_one, Module.End.one_apply]`.

Conclude with `left_eq_add.1 this`. Establish `e0 : e 0 = 1`. Use `e2 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.

Set `r : F.Γ →* GG n C` to `{ toFun := fun s => GG.ofGL (e (z s)) * B.r s map_one' := by rw [z1, e0, map_one, map_one, mul_one] map_mul' := fun s t => by`. Rewrite using `[hz, e2, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (B.r s), e5, mul_assoc] }`. Establish `hl : ∀ s, (r s).left = e (z s) * (B.r s).left` using `fun s => by show (GG.ofGL (e (z s)) * B.r s).left = _`. Simplify using the standard rewrite rules. Establish `hloc : ∀ v s, (B.r (F.loc v s)).right = 1` using `fun v s => (B.nu _).trans (F.loc0 v s).2`.

Establish `key : ∀ v s, (B.g v * e (Y v)) * (r (F.loc v s)).left * (B.g v * e (Y v))⁻¹ = e (z' v s) * (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹)` using `fun v s => by`. Establish `a1 : (B.r (F.loc v s)).left * e (-Y v) = e (-(B.map π).ad (F.loc v s) (Y v)) * (B.r (F.loc v s)).left`. Use `congrArg SemidirectProduct.left (e5 (F.loc v s) (-Y v))` as an intermediate fact. Simplify `this` using `[hloc]`. Establish `a2 : ∀ X, B.g v * e X = e (((B.map π).g v : Matrix (Fin n) (Fin n) Q) * X * ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q)) * B.g v` using `fun X => by`.

Use `congrArg SemidirectProduct.left (e4 (GG.ofGL (B.g v)) X)` as an intermediate fact. Simplify using `only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, GG.adFun, GG.map_right, if_true] at this`. Conclude with `this`. Establish `a3 : Y v + (z (F.loc v s) + -(B.map π).ad (F.loc v s) (Y v)) = ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q) * z' v s * ((B.map π).g v : Matrix (Fin n) (Fin n) Q)`. Rewrite using `[hY]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hl, _root_.mul_inv_rev, e3]`. Simplify using `only [mul_assoc]`. Use `_ = B.g v * e (Y v + (z (F.loc v s) + -(B.map π).ad (F.loc v s) (Y v))) * (B.r (F.loc v s)).left * (B.g v)⁻¹ := by`.

Rewrite using `[a1, e2, e2]`. Simplify using `only [mul_assoc]`. Use `_ = _ := by`. Rewrite using `[a3, a2]`. Simplify using `only [mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]`.

Establish `key' : ∀ v s, ((B.g v * e (Y v) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat * (((B.g v * e (Y v))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = (1 + (z' v s).map μ) * ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat * (((B.g v)⁻¹ : GL (Fin n) C) …` using `fun v s => by`. Rewrite using `[← e1]`. Conclude with `congrArg Units.val (key v s)`. Establish `hu : ∀ v s, UpT (1 + (z' v s).map μ)` using `fun v s i j h => by`. Rewrite using `[Matrix.add_apply, Matrix.map_apply, hz' v s i j h, map_zero, add_zero, Matrix.one_apply_ne h.ne']`.

Use `⟨⟨r, fun s => ?_, fun v => B.g v * e (Y v), fun v s => ?_⟩, fun s => ?_, fun v s i => ?_⟩` and prove the remaining obligations. Use `show (GG.ofGL (e (z s)) * B.r s).right = _`. Simplify using `[B.nu]`. Rewrite using `[key']`. Conclude with `(upT_mul (hu v s) (B.tri v s)).1`.

Rewrite using `[← e1]`. Conclude with `congrArg Units.val (hl s)`. Simplify using `only`. Rewrite using `[key', (upT_mul (hu v s) (B.tri v s)).2]`. Simplify using the standard rewrite rules.
-/
private theorem box_def {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] {F : Frame l κ} {n : ℕ}
    {C Q : Type} [CommRing C] [CommRing Q] (π : C →+* Q) (μ : Q →+ C)
    (hm : ∀ a c, μ (π a * c) = a * μ c) (h0 : ∀ c, π (μ c) = 0) (B : Box F n C)
    (z : F.Γ → Matrix (Fin n) (Fin n) Q) (hz : ∀ s t, z (s * t) = z s + (B.map π).ad s (z t))
    (z' : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) Q) (Y : F.V → Matrix (Fin n) (Fin n) Q)
    (hz' : ∀ v s, UpT (z' v s))
    (hY : ∀ v s, z (F.loc v s) = ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q) * z' v s *
      ((B.map π).g v : Matrix (Fin n) (Fin n) Q) + ((B.map π).ad (F.loc v s) (Y v) - Y v)) :
    ∃ B' : Box F n C, (∀ s, (B'.r s).mat = (1 + (z s).map μ) * (B.r s).mat) ∧
      ∀ v s i, ((B'.g v : Matrix (Fin n) (Fin n) C) * (B'.r (F.loc v s)).mat *
        (((B'.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i =
        (1 + μ (z' v s i i)) * ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i := by
  obtain ⟨e, e1, e2, e3, e4⟩ := sq_exp n π μ hm h0
  have e5 : ∀ s X, B.r s * GG.ofGL (e X) = GG.ofGL (e ((B.map π).ad s X)) * B.r s := fun s X => e4 _ X
  have z1 : z 1 = 0 := by
    have := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.1 this
  have e0 : e 0 = 1 := by
    have := e2 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  let r : F.Γ →* GG n C :=
    { toFun := fun s => GG.ofGL (e (z s)) * B.r s
      map_one' := by rw [z1, e0, map_one, map_one, mul_one]
      map_mul' := fun s t => by
        rw [hz, e2, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (B.r s), e5, mul_assoc] }
  have hl : ∀ s, (r s).left = e (z s) * (B.r s).left := fun s => by
    show (GG.ofGL (e (z s)) * B.r s).left = _
    simp
  have hloc : ∀ v s, (B.r (F.loc v s)).right = 1 := fun v s => (B.nu _).trans (F.loc0 v s).2
  have key : ∀ v s, (B.g v * e (Y v)) * (r (F.loc v s)).left * (B.g v * e (Y v))⁻¹ =
      e (z' v s) * (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) := fun v s => by
    have a1 : (B.r (F.loc v s)).left * e (-Y v) = e (-(B.map π).ad (F.loc v s) (Y v)) * (B.r (F.loc v s)).left := by
      have := congrArg SemidirectProduct.left (e5 (F.loc v s) (-Y v))
      simpa [hloc] using this
    have a2 : ∀ X, B.g v * e X = e (((B.map π).g v : Matrix (Fin n) (Fin n) Q) * X *
        ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q)) * B.g v := fun X => by
      have := congrArg SemidirectProduct.left (e4 (GG.ofGL (B.g v)) X)
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        sgnAct_one, GG.adFun, GG.map_right, if_true] at this
      exact this
    have a3 : Y v + (z (F.loc v s) + -(B.map π).ad (F.loc v s) (Y v)) =
        ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q) * z' v s *
          ((B.map π).g v : Matrix (Fin n) (Fin n) Q) := by
      rw [hY]
      abel
    calc _ = B.g v * (e (Y v) * (e (z (F.loc v s)) * ((B.r (F.loc v s)).left * e (-Y v)))) * (B.g v)⁻¹ := by
          rw [hl, _root_.mul_inv_rev, e3]
          simp only [mul_assoc]
      _ = B.g v * e (Y v + (z (F.loc v s) + -(B.map π).ad (F.loc v s) (Y v))) *
          (B.r (F.loc v s)).left * (B.g v)⁻¹ := by
          rw [a1, e2, e2]
          simp only [mul_assoc]
      _ = _ := by
          rw [a3, a2]
          simp only [mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  have key' : ∀ v s, ((B.g v * e (Y v) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat *
      (((B.g v * e (Y v))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = (1 + (z' v s).map μ) *
      ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := fun v s => by
    rw [← e1]
    exact congrArg Units.val (key v s)
  have hu : ∀ v s, UpT (1 + (z' v s).map μ) := fun v s i j h => by
    rw [Matrix.add_apply, Matrix.map_apply, hz' v s i j h, map_zero, add_zero, Matrix.one_apply_ne h.ne']
  refine ⟨⟨r, fun s => ?_, fun v => B.g v * e (Y v), fun v s => ?_⟩, fun s => ?_, fun v s i => ?_⟩
  · show (GG.ofGL (e (z s)) * B.r s).right = _
    simp [B.nu]
  · rw [key']
    exact (upT_mul (hu v s) (B.tri v s)).1
  · rw [← e1]
    exact congrArg Units.val (hl s)
  · dsimp only
    rw [key', (upT_mul (hu v s) (B.tri v s)).2]
    simp

/- English proof (translation)
Introduce `N` and use `by have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N) show f y ∈ maximalIdeal R' rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff] exact hy exact (h N).comp (Ideal.qu …`.
-/
private theorem ac_map {O R R' Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] [TopologicalSpace Γ] (f : R →ₐ[O] R') {u : Γ → R}
    (h : AdicCont (maximalIdeal R) u) : AdicCont (maximalIdeal R') fun g => f (u g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (h N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

/- English proof (translation)
Introduce `N`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `h : ∀ᶠ y in nhds x, ∀ p q, Ideal.Quotient.mk (I ^ N) (m y p q) = Ideal.Quotient.mk (I ^ N) (m x p q)` using `Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q => (IsLocallyConstant.iff_eventually_eq _).1 (hm p q N) x`. Use `(h.and ((IsLocallyConstant.iff_eventually_eq _).1 ha x)).mono fun y hy => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mul_apply, map_sum, map_mul, hy.1, hy.2]`.
-/
private theorem ac_lc {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (a m : X → Matrix (Fin n) (Fin n) C) (ha : IsLocallyConstant a) (hm : ∀ i j, AdicCont I fun s => m s i j)
    (i j : Fin n) : AdicCont I fun s => (a s * m s) i j := by
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ∀ p q, Ideal.Quotient.mk (I ^ N) (m y p q) = Ideal.Quotient.mk (I ^ N) (m x p q) :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
      (IsLocallyConstant.iff_eventually_eq _).1 (hm p q N) x
  refine (h.and ((IsLocallyConstant.iff_eventually_eq _).1 ha x)).mono fun y hy => ?_
  simp only [Matrix.mul_apply, map_sum, map_mul, hy.1, hy.2]

/- English proof (translation)
Rewrite using `[NRep.map_map]`. Use `congr 1`. Conclude with `RingHom.ext fun x => res_map f x`.
-/
private theorem lift_of_bar {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') (ρ : NRep F n R) :
    (ρ.map (f : R →+* R')).map (res O R' : R' →+* ResidueField O) = ρ.map (res O R : R →+* ResidueField O) := by
  rw [NRep.map_map]
  congr 1
  exact RingHom.ext fun x => res_map f x

/- English proof (translation)
Rewrite using `[Matrix.add_mul, Matrix.one_mul]`. Use `ext`. Simplify using `[Matrix.mul_apply, TrivSqZeroExt.fst_sum]`. Simplify using `[Matrix.mul_apply, TrivSqZeroExt.snd_sum, Algebra.smul_def, mul_comm]`.
-/
private theorem sq_mul {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) Q) (A : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    (((1 + X.map (TrivSqZeroExt.inr : Q → TrivSqZeroExt O Q)) * A.map TrivSqZeroExt.inl :
      Matrix (Fin n) (Fin n) (TrivSqZeroExt O Q)) i j) =
      TrivSqZeroExt.inl (A i j) + TrivSqZeroExt.inr ((X * A.map (algebraMap O Q)) i j) := by
  rw [Matrix.add_mul, Matrix.one_mul]
  ext
  · simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, Algebra.smul_def, mul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a c => by ext <;> simp [Algebra.smul_def], by simp, by simp, by simp, by simp⟩`.
-/
private theorem sq_facts {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] :
    (∀ (a : TrivSqZeroExt O Q) (c : Q), TrivSqZeroExt.inr (algebraMap O Q a.fst * c) = a * TrivSqZeroExt.inr c) ∧
    (∀ (a : O) (c : Q), (TrivSqZeroExt.inl a + TrivSqZeroExt.inr c : TrivSqZeroExt O Q).fst = a) ∧
    (∀ (a : O) (c : Q), (TrivSqZeroExt.inl a + TrivSqZeroExt.inr c : TrivSqZeroExt O Q).snd = c) ∧
    (∀ (a : O) (c : Q), ((1 + TrivSqZeroExt.inr c) * TrivSqZeroExt.inl a : TrivSqZeroExt O Q).fst = a) ∧
    (∀ a : O, ((1 + TrivSqZeroExt.inr (0 : Q)) * TrivSqZeroExt.inl a : TrivSqZeroExt O Q).snd = 0) :=
  ⟨fun a c => by ext <;> simp [Algebra.smul_def], by simp, by simp, by simp, by simp⟩

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ F C₀ hF _ S ξ B hB hC k _ z hz`. Take `⟨⟨⟨z1, z2⟩, z3⟩, z4, z5⟩` from `hz`. Use `choose z' hz' Y hY using z3`. Set `Q` to `Ok l O k`. Set `C` to `TrivSqZeroExt O Q`.

Take `⟨q1, q2, q3, q4, q5⟩` from `sq_facts (O := O) (Q := Q)`. Use `haveI : IsCO O C := co_sqz O O Q fun _ => rfl`. Set `φ : C →ₐ[O] O` to `TrivSqZeroExt.fstHom O O Q`. Set `ι : O →ₐ[O] C` to `Algebra.ofId O C`. Set `π : C →+* Q` to `(Ideal.Quotient.mk _).comp (φ : C →+* O)`.

Set `μ : Q →+ C` to `(TrivSqZeroExt.inrHom O Q).toAddMonoidHom`. Establish `hm : ∀ a c, μ (π a * c) = a * μ c` using `q1`. Take `⟨B', b1, b2⟩` from `box_def π μ hm (fun c => map_zero (Ideal.Quotient.mk _)) (B.map (ι : O →+* C)) z z2 z' Y (fun v => (hz' v).2.2.1) hY`. Establish `b3 : ∀ s i j, (B'.r s).mat i j = TrivSqZeroExt.inl ((B.r s).mat i j) + TrivSqZeroExt.inr ((z s * ((boxK B k).r s).mat) i j)` using `fun s i j => by`. Rewrite using `[b1]`.

Conclude with `sq_mul (z s) (B.r s).mat i j`. Take `⟨ρ', h1, h2⟩` from `pr_ofbox hF C (maximalIdeal C) B' (by`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[b3, z4, hB.atc, Matrix.zero_mul, Matrix.zero_apply, TrivSqZeroExt.inr_zero, add_zero]`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply])`.

Use the proof step `(fun i j h => by`. Establish `a1` using `z5 i j h`. Establish `a2` using `(S.ρ.map (ξ : S.R →+* O)).diag i j h`. Rewrite `a2` using `[← hB.res, ← hB.res]`. Rewrite `a1`, `a2`, the goal using `[Matrix.sub_apply, sub_eq_zero]`.

Rewrite using `[b3, b3, a1, a2])`. Use the proof step `(fun i j => by`. Simplify using `only [b1]`. Conclude with `ac_lc _ _ _ (z1.comp fun M => 1 + M.map μ) (fun p q => ac_map ι (hC p q)) i j)`. Establish `b4 : ∀ v s i, (ρ'.ψ v i s : C) = (1 + TrivSqZeroExt.inr (z' v s i i)) * TrivSqZeroExt.inl (ξ (S.ρ.ψ v i s : S.R))` using `fun v s i => by`.

Rewrite using `[← h1.psi, ← h1.res]`. Use `(b2 v s i).trans ?_` and prove the remaining obligations. Use `congr 1`. Use `(hB.map (ι : O →+* C)).psi v i s` as an intermediate fact. Rewrite `this` using `[← (hB.map (ι : O →+* C)).res]`.

Conclude with `this`. Establish `h3 : ρ'.map (φ : C →+* O) = S.ρ.map (ξ : S.R →+* O)`. Use `NRep.ext (MonoidHom.ext fun s => Matrix.ext fun i j => ?_) (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)` and prove the remaining obligations. Use `show (ρ'.r s i j).fst = _`. Rewrite using `[← h1.res, b3, ← hB.res]`.

Conclude with `q2 _ _`. Use `show (ρ'.ψ v i s : C).fst = ξ (S.ρ.ψ v i s : S.R)`. Rewrite using `[b4]`. Conclude with `q4 _ _`. Establish `h4 : ρ'.map (res O C : C →+* ResidueField O) = S.ρ.map (res O S.R : S.R →+* ResidueField O)`.

Rewrite using `[← lift_of_bar φ, h3, lift_of_bar]`. Take `⟨f, hf, -⟩` from `S.univ C ρ' ⟨h2, by rw [h4]; exact S.lift.2⟩`. Take `⟨g, -, hg⟩` from `S.univ O (S.ρ.map (ξ : S.R →+* O)) ⟨⟨fun i j => ac_map ξ (S.lift.1.1 i j), fun v i => ac_map ξ (S.lift.1.2 v i)⟩, by`. Rewrite using `[lift_of_bar]`. Conclude with `S.lift.2⟩`.

Establish `h5 : φ.comp f = ξ` using `(hg _ (by rw [← h3, ← hf]; rfl)).trans (hg ξ rfl).symm`. Establish `h6 : ∀ a, (f a).fst = ξ a` using `fun a => AlgHom.congr_fun h5 a`. Use `⟨(TrivSqZeroExt.sndHom O Q).comp f.toLinearMap, ⟨fun a b => ?_, fun v j s hs => ?_⟩, fun s i j => ?_⟩` and prove the remaining obligations. Use `show (f (a * b)).snd = ξ a • (f b).snd + ξ b • (f a).snd`. Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, h6, h6, op_smul_eq_smul]`.

Use `show ((S.ρ.map (f : S.R →+* C)).ψ v j s : C).snd = 0`. Rewrite using `[hf, b4, (hz' v).2.2.2 s hs]`. Conclude with `q5 _`. Use `show ((S.ρ.map (f : S.R →+* C)).r s i j).snd = _`. Rewrite using `[hf, ← h1.res, b3]`.

Conclude with `q3 _ _`.
-/
theorem UpperTheory.V.Z.J.derOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O) (B : Box F 3 O), B.Of (S.ρ.map (ξ : S.R →+* O)) → B.Cont (maximalIdeal O) → ∀ k, 0 < k → ∀ z ∈ ZN B k, ∃ δ ∈ WDer S.ρ ξ (Ok l O k), ∀ (s : F.G0) i j, δ (S.ρ.r s i j) = (z s * ((boxK B k).r s).mat) i j := by
  intro l _ O _ _ _ _ _ F C₀ hF _ S ξ B hB hC k _ z hz
  obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4, z5⟩ := hz
  choose z' hz' Y hY using z3
  let Q := Ok l O k
  let C := TrivSqZeroExt O Q
  obtain ⟨q1, q2, q3, q4, q5⟩ := sq_facts (O := O) (Q := Q)
  haveI : IsCO O C := co_sqz O O Q fun _ => rfl
  let φ : C →ₐ[O] O := TrivSqZeroExt.fstHom O O Q
  let ι : O →ₐ[O] C := Algebra.ofId O C
  let π : C →+* Q := (Ideal.Quotient.mk _).comp (φ : C →+* O)
  let μ : Q →+ C := (TrivSqZeroExt.inrHom O Q).toAddMonoidHom
  have hm : ∀ a c, μ (π a * c) = a * μ c := q1
  obtain ⟨B', b1, b2⟩ := box_def π μ hm (fun c => map_zero (Ideal.Quotient.mk _)) (B.map (ι : O →+* C)) z z2 z' Y
    (fun v => (hz' v).2.2.1) hY
  have b3 : ∀ s i j, (B'.r s).mat i j = TrivSqZeroExt.inl ((B.r s).mat i j) +
      TrivSqZeroExt.inr ((z s * ((boxK B k).r s).mat) i j) := fun s i j => by
    rw [b1]
    exact sq_mul (z s) (B.r s).mat i j
  obtain ⟨ρ', h1, h2⟩ := pr_ofbox hF C (maximalIdeal C) B'
    (by
      refine Matrix.ext fun i j => ?_
      rw [b3, z4, hB.atc, Matrix.zero_mul, Matrix.zero_apply, TrivSqZeroExt.inr_zero, add_zero]
      by_cases h : i = j <;> simp [h, Matrix.one_apply])
    (fun i j h => by
      have a1 := z5 i j h
      have a2 := (S.ρ.map (ξ : S.R →+* O)).diag i j h
      rw [← hB.res, ← hB.res] at a2
      rw [Matrix.sub_apply, sub_eq_zero] at a1 a2 ⊢
      rw [b3, b3, a1, a2])
    (fun i j => by
      simp only [b1]
      exact ac_lc _ _ _ (z1.comp fun M => 1 + M.map μ) (fun p q => ac_map ι (hC p q)) i j)
  have b4 : ∀ v s i, (ρ'.ψ v i s : C) = (1 + TrivSqZeroExt.inr (z' v s i i)) *
      TrivSqZeroExt.inl (ξ (S.ρ.ψ v i s : S.R)) := fun v s i => by
    rw [← h1.psi, ← h1.res]
    refine (b2 v s i).trans ?_
    congr 1
    have := (hB.map (ι : O →+* C)).psi v i s
    rw [← (hB.map (ι : O →+* C)).res] at this
    exact this
  have h3 : ρ'.map (φ : C →+* O) = S.ρ.map (ξ : S.R →+* O) := by
    refine NRep.ext (MonoidHom.ext fun s => Matrix.ext fun i j => ?_)
      (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)
    · show (ρ'.r s i j).fst = _
      rw [← h1.res, b3, ← hB.res]
      exact q2 _ _
    · show (ρ'.ψ v i s : C).fst = ξ (S.ρ.ψ v i s : S.R)
      rw [b4]
      exact q4 _ _
  have h4 : ρ'.map (res O C : C →+* ResidueField O) = S.ρ.map (res O S.R : S.R →+* ResidueField O) := by
    rw [← lift_of_bar φ, h3, lift_of_bar]
  obtain ⟨f, hf, -⟩ := S.univ C ρ' ⟨h2, by rw [h4]; exact S.lift.2⟩
  obtain ⟨g, -, hg⟩ := S.univ O (S.ρ.map (ξ : S.R →+* O))
    ⟨⟨fun i j => ac_map ξ (S.lift.1.1 i j), fun v i => ac_map ξ (S.lift.1.2 v i)⟩, by
      rw [lift_of_bar]; exact S.lift.2⟩
  have h5 : φ.comp f = ξ := (hg _ (by rw [← h3, ← hf]; rfl)).trans (hg ξ rfl).symm
  have h6 : ∀ a, (f a).fst = ξ a := fun a => AlgHom.congr_fun h5 a
  refine ⟨(TrivSqZeroExt.sndHom O Q).comp f.toLinearMap, ⟨fun a b => ?_, fun v j s hs => ?_⟩, fun s i j => ?_⟩
  · show (f (a * b)).snd = ξ a • (f b).snd + ξ b • (f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h6, h6, op_smul_eq_smul]
  · show ((S.ρ.map (f : S.R →+* C)).ψ v j s : C).snd = 0
    rw [hf, b4, (hz' v).2.2.2 s hs]
    exact q5 _
  · show ((S.ρ.map (f : S.R →+* C)).r s i j).snd = _
    rw [hf, ← h1.res, b3]
    exact q3 _ _
