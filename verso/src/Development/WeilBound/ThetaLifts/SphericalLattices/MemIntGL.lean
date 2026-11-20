import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt

noncomputable section

namespace PositivityTheory.Sph.M2.GenB

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `g ∈ GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _`. Rewrite using `[Subgroup.mem_inf]`. Apply `and_congr Iff.rfl` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).BlockTriangular (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use extensionality with `i j`. Conclude with `h (show GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inl j) < GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inr i) from Nat.zero_lt_one)`. Introduce `h i j hij`. Consider the cases of `i with`.

Consider the case `inl i => exact absurd hij (Nat.not_lt_zero _)`. Consider the case `inr i`. Consider the cases of `j with`. Consider the case `inl j => exact congrFun (congrFun h i) j`. Consider the case `inr j => exact absurd hij (lt_irrefl 1)`.
-/
theorem mem_PW {g : GL (Fin m ⊕ Fin m) L} : g ∈ PW L c m ↔
    Iso c (Wm L (Fin m)) (Wm L (Fin m)) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₂₁ = 0 := by
  change g ∈ GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
  rw [Subgroup.mem_inf]
  apply and_congr Iff.rfl
  change (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).BlockTriangular
    (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
  constructor
  · intro h
    ext i j
    exact h (show GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inl j) <
      GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inr i) from Nat.zero_lt_one)
  · intro h i j hij
    cases i with
    | inl i => exact absurd hij (Nat.not_lt_zero _)
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun h i) j
      | inr j => exact absurd hij (lt_irrefl 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lev_val (t : GL (Fin m) L) :
    ((lev L c m t : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) = levM L c m t := rfl

/- English proof (translation)
Rewrite using `[mem_PW, lev_val]`. Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `h1 : (↑t : Matrix (Fin m) (Fin m) L)ᵀ * (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]`. Establish `h2 : (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c * (↑t : Matrix (Fin m) (Fin m) L).map c = 1`.

Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]`. Establish `h3 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c).map c = (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ`. Use extensionality with `i j`. Simplify using `[hc]`. Establish `h4 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c)ᵀ = (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c`.

Rewrite using `[Matrix.transpose_map, Matrix.transpose_transpose]`. Establish `hlev : levM L c m t = fromBlocks (↑t : Matrix (Fin m) (Fin m) L) 0 0 ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c)` using `rfl`. Establish `hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0` using `rfl`. Express the relevant statement in the definitionally equal form `(levM L c m t)ᵀ * Wm L (Fin m) * (levM L c m t).map c = Wm L (Fin m)`. Rewrite using `[hlev, hW]`.

Simplify using `only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h3, h4, Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, h1, h2]`.
-/
theorem lev_mem (hc : ∀ x, c (c x) = x) (t : GL (Fin m) L) : lev L c m t ∈ PW L c m := by
  rw [mem_PW, lev_val]
  refine ⟨?_, rfl⟩
  have h1 : (↑t : Matrix (Fin m) (Fin m) L)ᵀ * (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c * (↑t : Matrix (Fin m) (Fin m) L).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c).map c = (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ := by
    ext i j
    simp [hc]
  have h4 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c)ᵀ = (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c := by
    rw [Matrix.transpose_map, Matrix.transpose_transpose]
  have hlev : levM L c m t = fromBlocks (↑t : Matrix (Fin m) (Fin m) L) 0 0
      ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c) := rfl
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change (levM L c m t)ᵀ * Wm L (Fin m) * (levM L c m t).map c = Wm L (Fin m)
  rw [hlev, hW]
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h3, h4,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, h1, h2]

def un (X : Matrix (Fin m) (Fin m) L) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem un_val (X : Matrix (Fin m) (Fin m) L) :
    ((un X : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) = fromBlocks 1 X 0 1 := rfl

/- English proof (translation)
Rewrite using `[mem_PW, un_val]`. Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0` using `rfl`. Express the relevant statement in the definitionally equal form `(fromBlocks 1 X 0 1)ᵀ * Wm L (Fin m) * (fromBlocks 1 X 0 1).map c = Wm L (Fin m)`. Rewrite using `[hW]`.

Simplify using `only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h, Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c), Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix …`.
-/
theorem un_mem {X : Matrix (Fin m) (Fin m) L} (h : X.map c = -Xᵀ) : un X ∈ PW L c m := by
  rw [mem_PW, un_val]
  refine ⟨?_, rfl⟩
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change (fromBlocks 1 X 0 1)ᵀ * Wm L (Fin m) * (fromBlocks 1 X 0 1).map c = Wm L (Fin m)
  rw [hW]
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c),
    Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.mul_neg, neg_add_cancel, neg_zero]

/- English proof (translation)
Use `ext1`. Rewrite using `[Units.val_mul, un_val, un_val, un_val, fromBlocks_multiply]`. Simplify using `[add_comm]`.
-/
theorem un_mul (X Y : Matrix (Fin m) (Fin m) L) : un X * un Y = un (X + Y) := by
  ext1
  rw [Units.val_mul, un_val, un_val, un_val, fromBlocks_multiply]
  simp [add_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zW_val (x : Lˣ) : ((zW L m x : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
    fromBlocks ((x : L) • 1) 0 0 (((x⁻¹ : Lˣ) : L) • 1) := rfl

/- English proof (translation)
Establish `hx : (↑x⁻¹ : L) * (↑x * ↑x) = ↑x` using `by rw [← mul_assoc, Units.inv_mul, one_mul]`. Use `ext1`. Simplify using `only [Units.val_mul, zW_val, un_val, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_zero, hx]`.
-/
theorem zW_un (x : Lˣ) (X : Matrix (Fin m) (Fin m) L) :
    zW L m x * un X = un (((x : L) * x) • X) * zW L m x := by
  have hx : (↑x⁻¹ : L) * (↑x * ↑x) = ↑x := by rw [← mul_assoc, Units.inv_mul, one_mul]
  ext1
  simp only [Units.val_mul, zW_val, un_val, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_zero, hx]

/- English proof (translation)
Rewrite `hp` using `[mem_PW]`. Take `⟨hiso, h21⟩` from `hp`. Use `set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L := (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) with hP`. Establish `hPb : P = fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ 0 P.toBlocks₂₂`. Rewrite using `[← h21]`.

Conclude with `(Matrix.fromBlocks_toBlocks P).symm`. Establish `hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0` using `rfl`. Express the relevant statement in the definitionally equal form `Pᵀ * Wm L (Fin m) * P.map c = Wm L (Fin m) at hiso`. Rewrite `hiso` using `[hPb, hW]`. Simplify using `only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.fromBlocks_inj] at hiso`.

Take `⟨-, h12, h21', h22⟩` from `hiso`. Use `set A := P.toBlocks₁₁ with hA`. Use `set B := P.toBlocks₁₂ with hB`. Use `set D := P.toBlocks₂₂ with hD`. Establish `hDD : (D.map c).map c = D`.

Use extensionality with `i j`. Simplify using `[hc]`. Establish `hinv1 : (D.map c)ᵀ * A = 1`. Use `congrArg Matrix.transpose h12` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis.

Establish `hinv2 : A * (D.map c)ᵀ = 1` using `by first`. Consider the case `exact mul_eq_one_comm.mp hinv1`. Consider the case `exact Matrix.mul_eq_one_comm.mp hinv1`. Consider the case `exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hinv1`. Use `⟨⟨A, (D.map c)ᵀ, hinv2, hinv1⟩, (D.map c)ᵀ * B, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.map_mul, Matrix.transpose_map, hDD, Matrix.transpose_mul, Matrix.transpose_transpose]`. Conclude with `eq_neg_of_add_eq_zero_left h22`. Use `ext1`. Rewrite using `[Units.val_mul, lev_val, un_val]`. Express the relevant statement in the definitionally equal form `P = _`.

Rewrite using `[hPb]`. Express the relevant statement in the definitionally equal form `_ = fromBlocks (A : Matrix (Fin m) (Fin m) L) 0 0 ((((⟨A, (D.map c)ᵀ, hinv2, hinv1⟩ : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c) * _`. Simplify using `only [Units.inv_mk, Units.val_mk, Matrix.transpose_transpose, hDD, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, ← Matrix.mul_assoc, hinv2]`.
-/
theorem decomp (hc : ∀ x, c (c x) = x) {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    ∃ (t : GL (Fin m) L) (X : Matrix (Fin m) (Fin m) L), X.map c = -Xᵀ ∧ p = lev L c m t * un X := by
  rw [mem_PW] at hp
  obtain ⟨hiso, h21⟩ := hp
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L := (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) with hP
  have hPb : P = fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ 0 P.toBlocks₂₂ := by
    rw [← h21]
    exact (Matrix.fromBlocks_toBlocks P).symm
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change Pᵀ * Wm L (Fin m) * P.map c = Wm L (Fin m) at hiso
  rw [hPb, hW] at hiso
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.fromBlocks_inj] at hiso
  obtain ⟨-, h12, h21', h22⟩ := hiso
  set A := P.toBlocks₁₁ with hA
  set B := P.toBlocks₁₂ with hB
  set D := P.toBlocks₂₂ with hD
  have hDD : (D.map c).map c = D := by
    ext i j
    simp [hc]
  have hinv1 : (D.map c)ᵀ * A = 1 := by
    have := congrArg Matrix.transpose h12
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hinv2 : A * (D.map c)ᵀ = 1 := by
    first
    | exact mul_eq_one_comm.mp hinv1
    | exact Matrix.mul_eq_one_comm.mp hinv1
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hinv1
  refine ⟨⟨A, (D.map c)ᵀ, hinv2, hinv1⟩, (D.map c)ᵀ * B, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.transpose_map, hDD, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact eq_neg_of_add_eq_zero_left h22
  · ext1
    rw [Units.val_mul, lev_val, un_val]
    change P = _
    rw [hPb]
    change _ = fromBlocks (A : Matrix (Fin m) (Fin m) L) 0 0
      ((((⟨A, (D.map c)ᵀ, hinv2, hinv1⟩ : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c) * _
    simp only [Units.inv_mk, Units.val_mk, Matrix.transpose_transpose, hDD, fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, hinv2]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `g ∈ (Matrix.GeneralLinearGroup.map (intL L).subtype).range`. Rewrite using `[MonoidHom.mem_range]`. Set `A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L)` to `Matrix.of fun a b => ⟨(g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h1 a b⟩`. Set `B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L)` to `Matrix.of fun a b => ⟨((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h2 a b⟩`. Establish `hinj : ∀ M N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L), M.map (intL L).subtype = N.map (intL L).subtype → M = N` using `fun M N h => Matrix.map_injective Subtype.val_injective h`.

Establish `hA : A.map (intL L).subtype = (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)`. Use extensionality with `a b`. Both sides reduce to the same expression. Establish `hB : B.map (intL L).subtype = ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)`. Use extensionality with `a b`.

Both sides reduce to the same expression. Establish `hAB : A * B = 1` using `hinj _ _ (by`. Rewrite using `[Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Units.mul_inv g)`. Establish `hBA : B * A = 1` using `hinj _ _ (by`.

Rewrite using `[Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Units.inv_mul g)`. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hA`.
-/
theorem mem_IntGL {g : GL (Fin m ⊕ Fin m) L}
    (h1 : ∀ i j, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L) :
    g ∈ IntGL L m := by
  change g ∈ (Matrix.GeneralLinearGroup.map (intL L).subtype).range
  rw [MonoidHom.mem_range]
  let A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) :=
    Matrix.of fun a b => ⟨(g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h1 a b⟩
  let B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) :=
    Matrix.of fun a b => ⟨((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h2 a b⟩
  have hinj : ∀ M N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L),
      M.map (intL L).subtype = N.map (intL L).subtype → M = N :=
    fun M N h => Matrix.map_injective Subtype.val_injective h
  have hA : A.map (intL L).subtype = (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    ext a b; rfl
  have hB : B.map (intL L).subtype =
      ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    ext a b; rfl
  have hAB : A * B = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv g)
  have hBA : B * A = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul g)
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

end PositivityTheory.Sph.M2.GenB

end
