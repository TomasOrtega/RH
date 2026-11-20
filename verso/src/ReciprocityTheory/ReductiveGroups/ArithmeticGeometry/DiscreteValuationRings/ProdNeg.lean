import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Cube

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def cQ (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

/- English proof (translation)
Unfold `cQ`. Rewrite using `[D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul]`.
-/
theorem cQ_add (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cQ D T (a + b) = cQ D T a * cQ D T b := by
  unfold cQ
  rw [D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[zero_smul, pow_zero]`. Establish `h0 : cQ D T 0 * cQ D T 0 = cQ D T 0` using `by rw [← cQ_add, add_zero]`. Simplify using `using h0`.

Consider the case `succ k ih => rw [succ_nsmul, cQ_add, ih, pow_succ]`.
-/
theorem cQ_nsmul (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (a : D.X) : cQ D T (k • a) = cQ D T a ^ k := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero]
    have h0 : cQ D T 0 * cQ D T 0 = cQ D T 0 := by rw [← cQ_add, add_zero]
    simpa using h0
  | succ k ih => rw [succ_nsmul, cQ_add, ih, pow_succ]

/- English proof (translation)
Unfold `cQ`. Rewrite using `[← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]`.
-/
theorem comp_cQ {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) : ρ ≫ cQ D T a = cQ D T' a := by
  unfold cQ
  rw [← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

/- English proof (translation)
Establish `e1 : ρ.left ≫ (𝟙 D.P.A.left) = ρ.left` using `Category.comp_id _`. Establish `e2 : ρ.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = (ρ * cQ D T χ).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Rewrite using `[padd, Hom.mul_def, comp_lift_assoc, Category.comp_id, cQ, ← Category.assoc, comp_toUnit]`.

Establish `e3 : ρ.left ≫ (toUnit D.P.A ≫ D.c χ).left = (cQ D T χ).left`. Rewrite using `[← Over.comp_left, ← Category.assoc, comp_toUnit]`. Both sides reduce to the same expression. Establish `e4 : ρ.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left`. Rewrite using `[← Over.comp_left, ← Category.assoc, comp_toUnit, Hom.one_def]`.

Rewrite using `[Fin.prod_univ_four]`. Simplify using `only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg, e1, e2, e3, e4]`.
-/
theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cQ D T χ).left * (h (cQ D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e1 : ρ.left ≫ (𝟙 D.P.A.left) = ρ.left := Category.comp_id _
  have e2 : ρ.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = (ρ * cQ D T χ).left := by
    rw [← Over.comp_left]
    congr 1
    rw [padd, Hom.mul_def, comp_lift_assoc, Category.comp_id, cQ, ← Category.assoc, comp_toUnit]
  have e3 : ρ.left ≫ (toUnit D.P.A ≫ D.c χ).left = (cQ D T χ).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  have e4 : ρ.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit, Hom.one_def]
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg, e1, e2, e3, e4]

/- English proof (translation)
Simplify using `only [zpow_neg, Finset.prod_inv_distrib, h]`.
-/
theorem prod_neg' {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) {c : U} (h : ∏ i, f i ^ e i = c) :
    ∏ i, f i ^ (-e i) = c⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib, h]

/- English proof (translation)
Rewrite using `[Fintype.prod_sum_type, h, h']`.
-/
theorem prod_sum₂' {K K' U : Type} [Fintype K] [Fintype K'] [CommGroup U] (f : K ⊕ K' → U) {c c' : U}
    (h : ∏ i, f (.inl i) = c) (h' : ∏ i, f (.inr i) = c') : ∏ i, f i = c * c' := by
  rw [Fintype.prod_sum_type, h, h']

/- English proof (translation)
Use `set a : D.P.A ⟶ D.P.A := cQ D _ α with ha`. Use `set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm`. Establish `hα' : cQ D D.P.A (α + k • mu) = a * m ^ k` using `by rw [cQ_add, cQ_nsmul]`. Take `⟨N, hN, vN⟩` from `exists_cubN D.cub a m (𝟙 D.P.A) k`. Take `⟨e, he, ve⟩` from `exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu)) (fun i => (𝟙 D.P.A * m).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by`.

Establish `p₁` using `prod_cub a (𝟙 D.P.A) m h`. Establish `p₂` using `hC U h`. Establish `p₃` using `prod_famB D (𝟙 _) (α + k • mu) k h`. Establish `p₄` using `prod_famB D (𝟙 D.P.A * m) α k h`. Establish `e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i` using `fun i => by simp`.

Simplify using `only [e₃] at p₃`. Rewrite `p₃` using `[hα']`. Rewrite `p₄` using `[← ha]`. Establish `q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A` using `mul_comm _ _`. Establish `q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m` using `by rw [mul_comm _ a, ← _root_.mul_assoc]`.

Establish `q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m` using `mul_comm _ _`. Rewrite `p₃` using `[q₁]`. Rewrite `p₄` using `[q₂]`. Establish `S : ∀ {K K' : Type} {_ : Fintype K} {_ : Fintype K'} (f : K ⊕ K' → U), ∏ i, f i = (∏ i, f (.inl i)) * ∏ i, f (.inr i)` using `fun f => Fintype.prod_sum_type f`. Rewrite using `[S, S]`.

Use `erw [S]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε]`. Use `erw [prod_neg' _ _ p₁]`. Rewrite using `[p₂, p₃, prod_neg' _ _ p₄]`. Simplify using `only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]`. Use the proof step `module)`. Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift (𝟙 D.P.A) m)).left))) (LB.pullGen D.P.L _ _ w D.P.A.hom))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hw _))`.

Use `⟨e, he, fun T ρ z J hJ => ?_⟩` and prove the remaining obligations. Establish `E` using `(ve _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))) (val_pull hJ _ _ _)))`. Use `E.trans ?_` and prove the remaining obligations. Rewrite using `[ha, hm, comp_cQ, comp_cQ, Category.comp_id]`.
-/
theorem exists_eB (k : ℕ) (α mu : D.X) {Ix : Type} [Fintype Ix]
    {φV : Ix → (Spec (CommRingCat.of R) ⟶ D.P.A.left)} {εV : Ix → ℤ}
    (w : LB.Gen (LB.LinComb D.P.L φV εV)) (hw : w.IsGen)
    (hC : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), ∏ i, h (D.P.A.hom ≫ φV i) ^ εV i =
      (h (cQ D D.P.A α * cQ D D.P.A mu).left)⁻¹ * h (cQ D D.P.A α).left * h (cQ D D.P.A mu).left *
        (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ * (h (cQ D D.P.A mu).left ^ k)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ k) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu))
        (fun i => (𝟙 D.P.A * cQ D D.P.A mu).left ≫ D.famφB α i)) (DegPre.deltaε k)), eB.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val eB ρ.left z J = cubN (cubV D.cub z J) k (cQ D T α) (cQ D T mu) ρ *
          (cubV D.cub z J (cQ D T α) ρ (cQ D T mu))⁻¹ * val w (ρ.left ≫ D.P.A.hom) z J := by
  set a : D.P.A ⟶ D.P.A := cQ D _ α with ha
  set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm
  have hα' : cQ D D.P.A (α + k • mu) = a * m ^ k := by rw [cQ_add, cQ_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m (𝟙 D.P.A) k
  obtain ⟨e, he, ve⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu))
      (fun i => (𝟙 D.P.A * m).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a (𝟙 D.P.A) m h
      have p₂ := hC U h
      have p₃ := prod_famB D (𝟙 _) (α + k • mu) k h
      have p₄ := prod_famB D (𝟙 D.P.A * m) α k h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i := fun i => by simp
      simp only [e₃] at p₃
      rw [hα'] at p₃
      rw [← ha] at p₄
      have q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A := mul_comm _ _
      have q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m := by rw [mul_comm _ a, ← _root_.mul_assoc]
      have q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m := mul_comm _ _
      rw [q₁] at p₃
      rw [q₂] at p₄
      have S : ∀ {K K' : Type} {_ : Fintype K} {_ : Fintype K'} (f : K ⊕ K' → U),
          ∏ i, f i = (∏ i, f (.inl i)) * ∏ i, f (.inr i) := fun f => Fintype.prod_sum_type f
      rw [S, S]
      erw [S]
      simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε]
      erw [prod_neg' _ _ p₁]
      rw [p₂, p₃, prod_neg' _ _ p₄]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift (𝟙 D.P.A) m)).left)))
      (LB.pullGen D.P.L _ _ w D.P.A.hom))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hw _))
  refine ⟨e, he, fun T ρ z J hJ => ?_⟩
  have E := (ve _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))) (val_pull hJ _ _ _)))
  refine E.trans ?_
  rw [ha, hm, comp_cQ, comp_cQ, Category.comp_id]

end Cube

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
