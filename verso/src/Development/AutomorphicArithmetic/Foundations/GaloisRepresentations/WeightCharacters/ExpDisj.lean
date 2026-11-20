import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private noncomputable def chiZ (m : ℤ) : Circle →* ℂ where
  toFun z := (z : ℂ) ^ m
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow]

/- English proof (translation)
Introduce `m n h`. Assume the negation of the conclusion as `hmn`. Establish `hk : m - n ≠ 0` using `sub_ne_zero.mpr hmn`. Use `set z : Circle := Circle.exp (Real.pi / (m - n : ℤ)) with hz`. Establish `hpow : (z : ℂ) ^ (m - n) = -1`.

Rewrite using `[hz, Circle.coe_exp, ← Complex.exp_int_mul]`. Establish `: ((m - n : ℤ) : ℂ) * (((Real.pi / ((m - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I`. Establish `hk' : ((m - n : ℤ) : ℂ) ≠ 0` using `by exact_mod_cast hk`. Use `push_cast`. Move the coercions through the operations in `at hk'`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.exp_pi_mul_I]`. Establish `h1 : (z : ℂ) ^ m = (z : ℂ) ^ n` using `DFunLike.congr_fun h z`. Establish `hz0 : (z : ℂ) ≠ 0` using `Circle.coe_ne_zero z`. Establish `h2 : (z : ℂ) ^ (m - n) = 1`.

Rewrite using `[zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]`. Rewrite `hpow` using `[h2]`. Evaluate the numerical expressions using `at hpow`.
-/
private theorem chiZ_injective : Function.Injective chiZ := by
  intro m n h
  by_contra hmn
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  set z : Circle := Circle.exp (Real.pi / (m - n : ℤ)) with hz
  have hpow : (z : ℂ) ^ (m - n) = -1 := by
    rw [hz, Circle.coe_exp, ← Complex.exp_int_mul]
    have : ((m - n : ℤ) : ℂ) * (((Real.pi / ((m - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have hk' : ((m - n : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
      push_cast
      push_cast at hk'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h1 : (z : ℂ) ^ m = (z : ℂ) ^ n := DFunLike.congr_fun h z
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have h2 : (z : ℂ) ^ (m - n) = 1 := by
    rw [zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]
  rw [h2] at hpow
  norm_num at hpow

/- English proof (translation)
Introduce `s t f hst hle hge`. Set `v : ℤ → (Circle → ℂ)` to `fun m z => (z : ℂ) ^ m`. Establish `hli : LinearIndependent ℂ v` using `(linearIndependent_monoidHom Circle ℂ).comp chiZ chiZ_injective`. Establish `hd : Disjoint (Set.Iic s) (Set.Ici t)`. Rewrite using `[Set.disjoint_left]`.

Introduce `x hx hx'`. Conclude with `absurd (lt_of_le_of_lt (Set.mem_Iic.mp hx) hst) (not_lt.mpr (Set.mem_Ici.mp hx'))`. Establish `hdisj` using `hli.disjoint_span_image hd`. Establish `e1 : ExpLe s = Submodule.span ℂ (v '' Set.Iic s)`. Unfold `ExpLe`.

Use `congr 1`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `⟨m, hm, rfl⟩`.

Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `⟨m, hm, rfl⟩`. Establish `e2 : ExpGe t = Submodule.span ℂ (v '' Set.Ici t)`. Unfold `ExpGe`. Use `congr 1`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `⟨m, hm, rfl⟩`. Introduce and unpack `⟨m, hm, rfl⟩`.

Conclude with `⟨m, hm, rfl⟩`. Rewrite `hle` using `[e1]`. Rewrite `hge` using `[e2]`. Conclude with `Submodule.disjoint_def.mp hdisj f hle hge`.
-/
theorem UpperTheory.Gal.Wt.expDisj_of :
    UpperTheory.Gal.Wt.ExpDisj := by
  intro s t f hst hle hge
  let v : ℤ → (Circle → ℂ) := fun m z => (z : ℂ) ^ m
  have hli : LinearIndependent ℂ v :=
    (linearIndependent_monoidHom Circle ℂ).comp chiZ chiZ_injective
  have hd : Disjoint (Set.Iic s) (Set.Ici t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hx) hst) (not_lt.mpr (Set.mem_Ici.mp hx'))
  have hdisj := hli.disjoint_span_image hd
  have e1 : ExpLe s = Submodule.span ℂ (v '' Set.Iic s) := by
    unfold ExpLe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  have e2 : ExpGe t = Submodule.span ℂ (v '' Set.Ici t) := by
    unfold ExpGe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  rw [e1] at hle
  rw [e2] at hge
  exact Submodule.disjoint_def.mp hdisj f hle hge
