import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> rfl`.
-/
private theorem corner_eq' {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    corner X = !![X 0 0, X 0 2; X 2 0, X 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/- English proof (translation)
Simplify using `only [corner_eq']`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h2]`.
-/
private theorem corner_mul' {R : Type} [CommRing R] (X Y : Matrix (Fin 3) (Fin 3) R)
    (h0 : X 0 1 = 0) (h2 : X 2 1 = 0) : corner (X * Y) = corner X * corner Y := by
  simp only [corner_eq']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h2]

/- English proof (translation)
Rewrite using `[corner_eq']`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem corner_one' {R : Type} [CommRing R] : corner (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  rw [corner_eq']
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Establish `h1 : corner (a : Matrix (Fin 3) (Fin 3) R) * corner ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1`. Rewrite using `[← corner_mul' _ _ h0 h2, Units.mul_inv, corner_one']`. Establish `h3 : corner ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = (corner (a : Matrix (Fin 3) (Fin 3) R)).adjugate`. Use `congrArg (fun Z => (corner (a : Matrix (Fin 3) (Fin 3) R)).adjugate * Z) h1` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul, Matrix.mul_one]`.

Rewrite using `[theta_val]`. Generalize the expression as in `((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = Y at h3`. Generalize the expression as in `(a : Matrix (Fin 3) (Fin 3) R) = X at h3`. Rewrite `h3` using `[Matrix.adjugate_fin_two]`. Establish `e00 : Y 0 0 = X 2 2` using `by simpa [corner] using congrFun (congrFun h3 0) 0`.

Establish `e01 : Y 0 2 = - X 0 2` using `by simpa [corner] using congrFun (congrFun h3 0) 1`. Establish `e10 : Y 2 0 = - X 2 0` using `by simpa [corner] using congrFun (congrFun h3 1) 0`. Establish `e11 : Y 2 2 = X 0 0` using `by simpa [corner] using congrFun (congrFun h3 1) 1`. Simplify using `only [corner_eq']`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Jmat, Fin.rev, Matrix.diagonal, e00, e01, e10, e11]`.
-/
private theorem corner_theta' {R : Type} [CommRing R] (a : GL (Fin 3) R)
    (h0 : (a : Matrix (Fin 3) (Fin 3) R) 0 1 = 0) (h2 : (a : Matrix (Fin 3) (Fin 3) R) 2 1 = 0)
    (hd : (corner (a : Matrix (Fin 3) (Fin 3) R)).det = 1) :
    corner (theta a : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal ![-1, 1] * corner (a : Matrix (Fin 3) (Fin 3) R) * Matrix.diagonal ![-1, 1] := by
  have h1 : corner (a : Matrix (Fin 3) (Fin 3) R) *
      corner ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← corner_mul' _ _ h0 h2, Units.mul_inv, corner_one']
  have h3 : corner ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (corner (a : Matrix (Fin 3) (Fin 3) R)).adjugate := by
    have := congrArg (fun Z => (corner (a : Matrix (Fin 3) (Fin 3) R)).adjugate * Z) h1
    simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul,
      Matrix.mul_one] using this
  rw [theta_val]
  generalize ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = Y at h3
  generalize (a : Matrix (Fin 3) (Fin 3) R) = X at h3
  rw [Matrix.adjugate_fin_two] at h3
  have e00 : Y 0 0 = X 2 2 := by simpa [corner] using congrFun (congrFun h3 0) 0
  have e01 : Y 0 2 = - X 0 2 := by simpa [corner] using congrFun (congrFun h3 0) 1
  have e10 : Y 2 0 = - X 2 0 := by simpa [corner] using congrFun (congrFun h3 1) 0
  have e11 : Y 2 2 = X 0 0 := by simpa [corner] using congrFun (congrFun h3 1) 1
  simp only [corner_eq']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Jmat, Fin.rev,
      Matrix.diagonal, e00, e01, e10, e11]

/- English proof (translation)
Introduce `G R _ _ η r c hm hc hrc hB hd`. Establish `hne : ((-1 : ℤˣ) = 1) = False` using `by decide`. Establish `key : ∀ g, ∃ k ∈ η.ker, (r g).mat = (r k).mat`. Introduce `g`. Break down `Int.units_eq_one_or (η g) with hg | hg` into its components or cases.

Conclude with `⟨g, hg, rfl⟩`. Establish `hk : η (g * c⁻¹) = 1` using `by rw [map_mul, map_inv, hg, hc, mul_inv_cancel]`. Use `⟨g * c⁻¹, hk, ?_⟩` and prove the remaining obligations. Establish `e : r g = r (g * c⁻¹) * r c` using `by rw [← map_mul, inv_mul_cancel_right]`. Establish `hr : (r (g * c⁻¹)).right = 1` using `(hm _).trans hk`.

Rewrite using `[e]`. Simplify using `only [GG.mat] at hrc ⊢`. Rewrite using `[SemidirectProduct.mul_left, hr, sgnAct_one, Units.val_mul, hrc, Matrix.mul_one]`. Establish `h0 : ∀ g, (r g).mat 0 1 = 0` using `fun g => by`. Take `⟨k, hk, e⟩` from `key g`.

Rewrite using `[e]; exact hB k hk 0 1 (by decide)`. Establish `h2 : ∀ g, (r g).mat 2 1 = 0` using `fun g => by`. Take `⟨k, hk, e⟩` from `key g`. Rewrite using `[e]; exact hB k hk 2 1 (by decide)`. Establish `hdet : ∀ g, (corner (r g).mat).det = 1` using `fun g => by`.

Take `⟨k, hk, e⟩` from `key g`. Rewrite using `[e]`. Conclude with `hd k hk`. Establish `hD : (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![-1, 1] = 1`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]`. Establish `hp : ∀ g h, (r g).right = 1 → corner (r (g * h)).mat = corner (r g).mat * corner (r h).mat`. Introduce `g h hg`. Rewrite using `[← corner_mul' _ _ (h0 g) (h2 g), map_mul]`. Simplify using `only [GG.mat]`.

Rewrite using `[SemidirectProduct.mul_left, hg, sgnAct_one, Units.val_mul]`. Establish `hn : ∀ g h, (r g).right = -1 → corner (r (g * h)).mat = corner (r g).mat * (Matrix.diagonal ![-1, 1] * corner (r h).mat * Matrix.diagonal ![-1, 1])`. Introduce `g h hg`. Establish `: corner (theta (r h).left : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![-1, 1] * corner (r h).mat * Matrix.diagonal ![-1, 1]` using `corner_theta' (r h).left (h0 h) (h2 h) (hdet h)`. Rewrite using `[← this, ← corner_mul' _ _ (h0 g) (h2 g), map_mul]`.

Simplify using `only [GG.mat]`. Rewrite using `[SemidirectProduct.mul_left, hg, sgnAct_neg_one, Units.val_mul]`. Set `W0 : G →* Matrix (Fin 2) (Fin 2) R` to `{ toFun := Wfun r map_one' := by simp [Wfun, GG.mat, corner_one'] map_mul' := fun g h => by`. Establish `hgh : (r (g * h)).right = (r g).right * (r h).right`. Rewrite using `[map_mul, SemidirectProduct.mul_right]`.

Apply the tactic sequence `rcases Int.units_eq_one_or (r g).right with hg | hg <;>`. Break down `Int.units_eq_one_or (r h).right with hh | hh` into its components or cases. Simplify using `only [Wfun, hgh, hg, hh, mul_one, if_true, hp g h hg]`. Simplify using `only [Wfun, hgh, hg, hh, one_mul, if_true, hne, if_false, hp g h hg, Matrix.mul_assoc]`. Simplify using `only [Wfun, hgh, hg, hh, mul_one, if_true, hne, if_false, hn g h hg, Matrix.mul_assoc, hD]`.

Simplify using `only [Wfun, hgh, hg, hh, neg_mul_neg, mul_one, if_true, hne, if_false, hn g h hg, Matrix.mul_assoc] }`. Use `⟨W0.toHomUnits, fun g => rfl, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Wfun r g).det = _`. Rewrite using `[← hm g]`. Break down `Int.units_eq_one_or (r g).right with hg | hg` into its components or cases.

Simplify using `[Wfun, hg, hdet]`. Simplify using `[Wfun, hg, hne, hdet, Fin.prod_univ_two]`.
-/
theorem UpperTheory.V.U3.exists_lieElement_middleBlockPart :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (r : G →* GG 3 R) (c : G), HasMult η r → η c = -1 → (r c).mat = 1 → Block η r →
      (∀ g ∈ η.ker, (corner (r g).mat).det = 1) →
      ∃ W : G →* GL (Fin 2) R, (∀ g, (W g : Matrix (Fin 2) (Fin 2) R) = Wfun r g) ∧ ∀ g, (W g : Matrix (Fin 2) (Fin 2) R).det = ((η g : ℤˣ) : ℤ) := by
  intro G R _ _ η r c hm hc hrc hB hd
  have hne : ((-1 : ℤˣ) = 1) = False := by decide
  have key : ∀ g, ∃ k ∈ η.ker, (r g).mat = (r k).mat := by
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact ⟨g, hg, rfl⟩
    · have hk : η (g * c⁻¹) = 1 := by rw [map_mul, map_inv, hg, hc, mul_inv_cancel]
      refine ⟨g * c⁻¹, hk, ?_⟩
      have e : r g = r (g * c⁻¹) * r c := by rw [← map_mul, inv_mul_cancel_right]
      have hr : (r (g * c⁻¹)).right = 1 := (hm _).trans hk
      rw [e]
      simp only [GG.mat] at hrc ⊢
      rw [SemidirectProduct.mul_left, hr, sgnAct_one, Units.val_mul, hrc, Matrix.mul_one]
  have h0 : ∀ g, (r g).mat 0 1 = 0 := fun g => by
    obtain ⟨k, hk, e⟩ := key g
    rw [e]; exact hB k hk 0 1 (by decide)
  have h2 : ∀ g, (r g).mat 2 1 = 0 := fun g => by
    obtain ⟨k, hk, e⟩ := key g
    rw [e]; exact hB k hk 2 1 (by decide)
  have hdet : ∀ g, (corner (r g).mat).det = 1 := fun g => by
    obtain ⟨k, hk, e⟩ := key g
    rw [e]; exact hd k hk
  have hD : (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![-1, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have hp : ∀ g h, (r g).right = 1 →
      corner (r (g * h)).mat = corner (r g).mat * corner (r h).mat := by
    intro g h hg
    rw [← corner_mul' _ _ (h0 g) (h2 g), map_mul]
    simp only [GG.mat]
    rw [SemidirectProduct.mul_left, hg, sgnAct_one, Units.val_mul]
  have hn : ∀ g h, (r g).right = -1 →
      corner (r (g * h)).mat = corner (r g).mat *
        (Matrix.diagonal ![-1, 1] * corner (r h).mat * Matrix.diagonal ![-1, 1]) := by
    intro g h hg
    have : corner (theta (r h).left : Matrix (Fin 3) (Fin 3) R) =
        Matrix.diagonal ![-1, 1] * corner (r h).mat * Matrix.diagonal ![-1, 1] :=
      corner_theta' (r h).left (h0 h) (h2 h) (hdet h)
    rw [← this, ← corner_mul' _ _ (h0 g) (h2 g), map_mul]
    simp only [GG.mat]
    rw [SemidirectProduct.mul_left, hg, sgnAct_neg_one, Units.val_mul]
  let W0 : G →* Matrix (Fin 2) (Fin 2) R :=
    { toFun := Wfun r
      map_one' := by simp [Wfun, GG.mat, corner_one']
      map_mul' := fun g h => by
        have hgh : (r (g * h)).right = (r g).right * (r h).right := by
          rw [map_mul, SemidirectProduct.mul_right]
        rcases Int.units_eq_one_or (r g).right with hg | hg <;>
          rcases Int.units_eq_one_or (r h).right with hh | hh
        · simp only [Wfun, hgh, hg, hh, mul_one, if_true, hp g h hg]
        · simp only [Wfun, hgh, hg, hh, one_mul, if_true, hne, if_false, hp g h hg,
            Matrix.mul_assoc]
        · simp only [Wfun, hgh, hg, hh, mul_one, if_true, hne, if_false, hn g h hg,
            Matrix.mul_assoc, hD]
        · simp only [Wfun, hgh, hg, hh, neg_mul_neg, mul_one, if_true, hne, if_false, hn g h hg,
            Matrix.mul_assoc] }
  refine ⟨W0.toHomUnits, fun g => rfl, fun g => ?_⟩
  change (Wfun r g).det = _
  rw [← hm g]
  rcases Int.units_eq_one_or (r g).right with hg | hg
  · simp [Wfun, hg, hdet]
  · simp [Wfun, hg, hne, hdet, Fin.prod_univ_two]
