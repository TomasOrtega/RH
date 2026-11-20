import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ZarhinUniqIso

open Matrix

variable {S : Scheme.{0}}

/- English proof (translation)
Establish `hc` using `hA.comm`. Take `⟨h1, h2⟩` from `GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA n hn`. Establish `e : ((𝟙 A) ^ n : A ⟶ A) = ReciprocityTheory.ChartRestriction.G.Out.mulA A n` using `rfl`. Rewrite using `[e]`. Use `⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩` and prove the remaining obligations.

Establish `hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left` using `MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1`. Rewrite `hf`, the goal using `[GlobalTheory.MulFiniteFlat.pullback_map_mulA]`. Establish `hB` using `ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA`. Establish `hBc` using `hB.comm`. Conclude with `(GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _ hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2`.
-/
theorem mulA_flat_surjective_qc (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (n : ℕ) (hn : 1 ≤ n) :
    Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left ∧
      QuasiCompact ((𝟙 A) ^ n : A ⟶ A).left := by
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA n hn
  have e : ((𝟙 A) ^ n : A ⟶ A) = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := rfl
  rw [e]
  refine ⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

def preHom {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) :=
  MonoidHom.mk' (fun g => f ≫ g) (fun a b => MonObj.comp_mul f a b)

def postHom {X M N : Over S} [GrpObj M] [GrpObj N] (g : M ⟶ N) [IsMonHom g] : (X ⟶ M) →* (X ⟶ N) :=
  MonoidHom.mk' (fun f => f ≫ g) (fun a b => MonObj.mul_comp a b g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem preHom_apply {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) (g : Y ⟶ M) : preHom f g = f ≫ g := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem postHom_apply {X M N : Over S} [GrpObj M] [GrpObj N] (g : M ⟶ N) [IsMonHom g] (f : X ⟶ M) :
    postHom g f = f ≫ g := rfl

/- English proof (translation)
The claim follows from `map_zpow (preHom f) g n`.
-/
theorem comp_zpow' {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℤ) : f ≫ g ^ n = (f ≫ g) ^ n :=
  map_zpow (preHom f) g n

/- English proof (translation)
The claim follows from `map_zpow (postHom (X := X) g) f n`.
-/
theorem zpow_comp' {X M N : Over S} [GrpObj M] [GrpObj N] (f : X ⟶ M) (g : M ⟶ N) [IsMonHom g] (n : ℤ) :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  map_zpow (postHom (X := X) g) f n

/- English proof (translation)
The claim follows from `map_pow (preHom f) g n`.
-/
theorem comp_npow' {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n :=
  map_pow (preHom f) g n

/- English proof (translation)
The claim follows from `map_pow (postHom (X := X) g) f n`.
-/
theorem npow_comp' {X M N : Over S} [GrpObj M] [GrpObj N] (f : X ⟶ M) (g : M ⟶ N) [IsMonHom g] (n : ℕ) :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  map_pow (postHom (X := X) g) f n

/- English proof (translation)
The claim follows from `map_prod (preHom f) g s`.
-/
theorem comp_prod' {X Y M : Over S} [GrpObj M] [IsCommMonObj M] {J : Type} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ (∏ i ∈ s, g i) = ∏ i ∈ s, (f ≫ g i) :=
  map_prod (preHom f) g s

/- English proof (translation)
The claim follows from `map_prod (postHom (X := X) g) f s`.
-/
theorem prod_comp' {X M N : Over S} [GrpObj M] [IsCommMonObj M] [GrpObj N] [IsCommMonObj N] {J : Type}
    (s : Finset J) (f : J → (X ⟶ M)) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) :=
  map_prod (postHom (X := X) g) f s

end GlobalTheory.ZarhinUniqIso

noncomputable section

namespace GlobalTheory.ZarhinUniqIso

open Matrix GlobalTheory.ZarhinFam

variable {S : Scheme.{0}}

section Act

variable {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {act : O → (A ⟶ A)}

/- English proof (translation)
Establish `e` using `h.2.2.2 0 0`. Rewrite `e` using `[add_zero]`. Conclude with `(mul_eq_left.1 e.symm)`.
-/
theorem act_zero' (h : IsRAct A act) : act 0 = 1 := by
  have e := h.2.2.2 0 0
  rw [add_zero] at e
  exact (mul_eq_left.1 e.symm)

def ahom (h : IsRAct A act) : O →+ Additive (A ⟶ A) where
  toFun a := Additive.ofMul (act a)
  map_zero' := by rw [act_zero' h]; rfl
  map_add' a b := by rw [h.2.2.2]; rfl

/- English proof (translation)
Use `map_sum (ahom h) f s` as an intermediate fact. Conclude with `congrArg Additive.toMul this`.
-/
theorem act_sum' (h : IsRAct A act) {J : Type} (s : Finset J) (f : J → O) :
    act (∑ i ∈ s, f i) = ∏ i ∈ s, act (f i) := by
  have := map_sum (ahom h) f s
  exact congrArg Additive.toMul this

/- English proof (translation)
Use `map_zsmul (ahom h) n a` as an intermediate fact. Conclude with `congrArg Additive.toMul this`.
-/
theorem act_zsmul' (h : IsRAct A act) (n : ℤ) (a : O) : act (n • a) = act a ^ n := by
  have := map_zsmul (ahom h) n a
  exact congrArg Additive.toMul this

end Act

def lo (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨(d : ℤ) • single k (Sum.inl 0) 1, fun i j => by
    simp only [Matrix.smul_apply, single_apply, smul_eq_mul]
    split_ifs <;> simp⟩

def up (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨single (Sum.inl 0) k 1, fun i j => by simp [single_apply]⟩

def ecol (d : ℕ) (k : Fin 4 ⊕ Fin 4) (i : Fin 4) : ord d :=
  ⟨single k (Sum.inr i) 1, fun a b => by simp [single_apply]⟩

def erow (d : ℕ) (i : Fin 4) (l : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨single (Sum.inl i) l 1, fun a b => by simp [single_apply]⟩

/- English proof (translation)
Apply the tactic sequence `ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum …`.
-/
theorem lo_inl (d : ℕ) (i : Fin 4) : lo d (Sum.inl i) = (d : ℤ) • erow d i (Sum.inl 0) := by
  ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

/- English proof (translation)
Apply the tactic sequence `ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum …`.
-/
theorem up_inr (d : ℕ) (i : Fin 4) : up d (Sum.inr i) = polUnit d * ecol d (Sum.inr 0) i := by
  ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

/- English proof (translation)
Apply the tactic sequence `ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, singl …`.
-/
theorem lo_idem_pol (d : ℕ) (k : Fin 4 ⊕ Fin 4) : lo d k * idem d * polUnit d = (d : ℤ) • ecol d k 0 := by
  ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finset_sum, AddSubgroupClass.coe_zsmul, OneMemClass.coe_one]`. Use extensionality with `a b`. Rewrite using `[Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.s …`.
-/
theorem lo_idem_up_sum (d : ℕ) : ∑ k, lo d k * idem d * up d k = (d : ℤ) • (1 : ord d) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum, AddSubgroupClass.coe_zsmul, OneMemClass.coe_one]
  ext a b
  rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

/- English proof (translation)
Use `split_ifs with hk`. Apply the tactic sequence `subst hk; ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Finty …`. Apply the tactic sequence `ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, singl …`.
-/
theorem idem_lo (d : ℕ) (k : Fin 4 ⊕ Fin 4) : idem d * lo d k = if k = Sum.inl 0 then (d : ℤ) • idem d else 0 := by
  split_ifs with hk
  · subst hk; ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]
  · ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try (intros; subst_vars; simp_all))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zarhinOrderUpperMatrixUnit_inl_zero (d : ℕ) : up d (Sum.inl 0) = idem d := rfl

/- English proof (translation)
Apply the tactic sequence `ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, singl …`.
-/
theorem mul_lo (d : ℕ) (o : ord d) (k : Fin 4 ⊕ Fin 4) :
    o * lo d k = ∑ j, (o : Matrix _ _ ℤ) j k • lo d j := by
  ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

/- English proof (translation)
Apply the tactic sequence `ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, singl …`.
-/
theorem up_mul (d : ℕ) (o : ord d) (k : Fin 4 ⊕ Fin 4) :
    up d k * o = ∑ j, (o : Matrix _ _ ℤ) k j • up d j := by
  ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finset_sum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

end GlobalTheory.ZarhinUniqIso

noncomputable section

namespace GlobalTheory.ZarhinUniqIso

open Matrix GlobalTheory.ZarhinFam

variable {S : Scheme.{0}}

/- English proof (translation)
Rewrite using `[npow_comp', comp_npow', Category.id_comp, Category.comp_id]`.
-/
theorem mulA_comm {X Y : Over S} [GrpObj X] [GrpObj Y] (g : X ⟶ Y) [IsMonHom g] (n : ℕ) :
    ((𝟙 X) ^ n) ≫ g = g ≫ (𝟙 Y) ^ n := by
  rw [npow_comp', comp_npow', Category.id_comp, Category.comp_id]

/- English proof (translation)
Establish `h : x ^ d = 1` using `by rw [← hx, comp_npow', Category.comp_id]`. Rewrite using `[comp_zpow', zpow_natCast, ← npow_comp', h, MonObj.one_comp]`.
-/
theorem pow_kill {T X M : Over S} [GrpObj X] [GrpObj M] (x : T ⟶ X) (g : X ⟶ M) [IsMonHom g] (d : ℕ)
    (hx : x ≫ (𝟙 X) ^ d = 1) : x ≫ g ^ (d : ℤ) = 1 := by
  have h : x ^ d = 1 := by rw [← hx, comp_npow', Category.comp_id]
  rw [comp_zpow', zpow_natCast, ← npow_comp', h, MonObj.one_comp]

section Main

variable {A Z₁ Z₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z₁] [IsCommMonObj Z₁] [GrpObj Z₂]
  [IsCommMonObj Z₂] {d : ℕ} {act₁ : ord d → (Z₁ ⟶ Z₁)} {act₂ : ord d → (Z₂ ⟶ Z₂)}

def dMap (d : ℕ) (act₁ : ord d → (Z₁ ⟶ Z₁)) (act₂ : ord d → (Z₂ ⟶ Z₂)) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂) :
    Z₁ ⟶ Z₂ :=
  ∏ k, act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)

/- English proof (translation)
Use `haveI := h₁.1`. Use `haveI := h₂.1`. Conclude with `Finset.prod_induction _ (fun x => IsMonHom x) (fun x y hx hy => by haveI := hx; haveI := hy; exact GlobalTheory.Serre.isMonHom_mul x y) GlobalTheory.Serre.isMonHom_one (fun k _ => inferInstance)`.
-/
theorem isMonHom_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₂] : IsMonHom (dMap d act₁ act₂ pr₁ inc₂) := by
  haveI := h₁.1; haveI := h₂.1
  exact Finset.prod_induction _ (fun x => IsMonHom x)
    (fun x y hx hy => by haveI := hx; haveI := hy; exact GlobalTheory.Serre.isMonHom_mul x y)
    GlobalTheory.Serre.isMonHom_one (fun k _ => inferInstance)

/- English proof (translation)
Use `haveI := h₁.1`. Use `haveI := h₂.1`. Unfold `dMap`. Rewrite using `[comp_prod', prod_comp']`. Establish `L : ∀ k, act₁ o ≫ act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k) = ∏ j, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ^ ((o : Matrix _ _ ℤ) j k)`.

Introduce `k`. Rewrite using `[← Category.assoc, ← h₁.2.2.1, mul_lo, act_sum' h₁, prod_comp']`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[act_zsmul' h₁, zpow_comp']`. Establish `R : ∀ j, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d j)) ≫ act₂ o = ∏ k, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ^ ((o : Matrix _ _ ℤ) j k)`.

Introduce `j`. Simplify using `only [Category.assoc]`. Rewrite using `[← h₂.2.2.1, up_mul, act_sum' h₂]`. Simplify using `only [act_zsmul' h₂, comp_prod', comp_zpow']`. Repeatedly rewrite using `[L, R]`.

Conclude with `Finset.prod_comm`.
-/
theorem dMap_lin (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₂] (o : ord d) :
    act₁ o ≫ dMap d act₁ act₂ pr₁ inc₂ = dMap d act₁ act₂ pr₁ inc₂ ≫ act₂ o := by
  haveI := h₁.1; haveI := h₂.1
  unfold dMap
  rw [comp_prod', prod_comp']
  have L : ∀ k, act₁ o ≫ act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k) =
      ∏ j, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ^ ((o : Matrix _ _ ℤ) j k) := by
    intro k
    rw [← Category.assoc, ← h₁.2.2.1, mul_lo, act_sum' h₁, prod_comp']
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [act_zsmul' h₁, zpow_comp']
  have R : ∀ j, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d j)) ≫ act₂ o =
      ∏ k, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ^ ((o : Matrix _ _ ℤ) j k) := by
    intro j
    simp only [Category.assoc]
    rw [← h₂.2.2.1, up_mul, act_sum' h₂]
    simp only [act_zsmul' h₂, comp_prod', comp_zpow']
  simp_rw [L, R]
  exact Finset.prod_comm

/- English proof (translation)
Use `haveI := h₁.1`. Use `haveI := h₂.1`. Unfold `dMap`. Rewrite using `[comp_prod']`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations.

Break down `k with i | i` into its components or cases. Rewrite using `[lo_inl, act_zsmul' h₁, ← Category.assoc, pow_kill x _ d hx, MonObj.one_comp]`. Establish `h0 : (x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁) ≫ inc₁ ≫ act₁ (polUnit d) = 1`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hpi₁, ← h₁.2.2.1, ← h₁.2.2.1, ← _root_.mul_assoc, lo_idem_pol, act_zsmul' h₁, pow_kill x _ d hx]`.

Establish `h1` using `hker T _ h0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[up_inr, h₂.2.2.1]`. Simplify using `only [Category.assoc]`. Use `_ = 1 := by rw [h1, MonObj.one_comp]`.
-/
theorem dMap_kill (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₁] [IsMonHom inc₂] (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d))
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ inc₁ ≫ act₁ (polUnit d) = 1 → x ≫ inc₂ ≫ act₂ (polUnit d) = 1)
    (T : Over S) (x : T ⟶ Z₁) (hx : x ≫ (𝟙 Z₁) ^ d = 1) : x ≫ dMap d act₁ act₂ pr₁ inc₂ = 1 := by
  haveI := h₁.1; haveI := h₂.1
  unfold dMap
  rw [comp_prod']
  refine Finset.prod_eq_one fun k _ => ?_
  rcases k with i | i
  · rw [lo_inl, act_zsmul' h₁, ← Category.assoc, pow_kill x _ d hx, MonObj.one_comp]
  · have h0 : (x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁) ≫ inc₁ ≫ act₁ (polUnit d) = 1 := by
      simp only [Category.assoc]
      rw [reassoc_of% hpi₁, ← h₁.2.2.1, ← h₁.2.2.1, ← _root_.mul_assoc, lo_idem_pol, act_zsmul' h₁, pow_kill x _ d hx]
    have h1 := hker T _ h0
    calc x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inr i))
        = ((x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁) ≫ inc₂ ≫ act₂ (polUnit d)) ≫ act₂ (ecol d (Sum.inr 0) i) := by
          rw [up_inr, h₂.2.2.1]; simp only [Category.assoc]
      _ = 1 := by rw [h1, MonObj.one_comp]

/- English proof (translation)
Use `haveI := h₁.1`. Use `haveI := h₂.1`. Establish `hi : inc₁ = inc₁ ≫ act₁ (idem d)` using `by rw [← hpi₁, reassoc_of% hip₁]`. Establish `hW : act₁ (idem d) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0)) = pr₁ ≫ inc₂`. Rewrite using `[zarhinOrderUpperMatrixUnit_inl_zero, ← hpi₂, ← hpi₁]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hip₁, reassoc_of% hip₂]`. Unfold `dMap`. Rewrite using `[comp_prod', Finset.prod_eq_single (Sum.inl 0)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h₁.2.2.1]`. Use `conv_lhs => rw [hi]`. Simplify using `only [Category.assoc]`. Use `_ = inc₁ ≫ (act₁ (idem d) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0))) ^ (d : ℤ) := by`. Rewrite using `[idem_lo, if_pos rfl, act_zsmul' h₁, zpow_comp']`.

Use `_ = ((𝟙 A) ^ d) ≫ inc₂ := by`. Rewrite using `[hW, comp_zpow', reassoc_of% hip₁, zpow_natCast, npow_comp', Category.id_comp]`. Introduce `k _ hk`. Rewrite using `[hi, Category.assoc, ← Category.assoc (act₁ (idem d)), ← h₁.2.2.1, idem_lo, if_neg hk, act_zero' h₁, MonObj.one_comp, MonObj.comp_one]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem inc_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (pr₂ : Z₂ ⟶ A)
    (inc₂ : A ⟶ Z₂) [IsMonHom pr₁] [IsMonHom inc₁] [IsMonHom inc₂] [IsMonHom pr₂]
    (hip₁ : inc₁ ≫ pr₁ = 𝟙 A) (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d))
    (hip₂ : inc₂ ≫ pr₂ = 𝟙 A) (hpi₂ : pr₂ ≫ inc₂ = act₂ (idem d)) :
    inc₁ ≫ dMap d act₁ act₂ pr₁ inc₂ = ((𝟙 A) ^ d) ≫ inc₂ := by
  haveI := h₁.1; haveI := h₂.1
  have hi : inc₁ = inc₁ ≫ act₁ (idem d) := by rw [← hpi₁, reassoc_of% hip₁]
  have hW : act₁ (idem d) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0)) = pr₁ ≫ inc₂ := by
    rw [zarhinOrderUpperMatrixUnit_inl_zero, ← hpi₂, ← hpi₁]; simp only [Category.assoc]; rw [reassoc_of% hip₁, reassoc_of% hip₂]
  unfold dMap
  rw [comp_prod', Finset.prod_eq_single (Sum.inl 0)]
  · calc inc₁ ≫ act₁ (lo d (Sum.inl 0)) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0))
        = inc₁ ≫ act₁ (idem d * lo d (Sum.inl 0)) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0)) := by
          rw [h₁.2.2.1]; conv_lhs => rw [hi]
          simp only [Category.assoc]
      _ = inc₁ ≫ (act₁ (idem d) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0))) ^ (d : ℤ) := by
          rw [idem_lo, if_pos rfl, act_zsmul' h₁, zpow_comp']
      _ = ((𝟙 A) ^ d) ≫ inc₂ := by
          rw [hW, comp_zpow', reassoc_of% hip₁, zpow_natCast, npow_comp', Category.id_comp]
  · intro k _ hk
    rw [hi, Category.assoc, ← Category.assoc (act₁ (idem d)), ← h₁.2.2.1, idem_lo, if_neg hk, act_zero' h₁,
      MonObj.one_comp, MonObj.comp_one]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `haveI := h₁.1`. Rewrite using `[← cancel_epi ((𝟙 Z₁) ^ d), ← Category.assoc, mulA_comm, Category.assoc, hf, reassoc_of% hf, dMap_lin h₁ h₂]`.
-/
theorem lin_of_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₂] (e : Z₁ ⟶ Z₂) [Epi ((𝟙 Z₁) ^ d)]
    (hf : ((𝟙 Z₁) ^ d) ≫ e = dMap d act₁ act₂ pr₁ inc₂) (o : ord d) : act₁ o ≫ e = e ≫ act₂ o := by
  haveI := h₁.1
  rw [← cancel_epi ((𝟙 Z₁) ^ d), ← Category.assoc, mulA_comm, Category.assoc, hf, reassoc_of% hf,
    dMap_lin h₁ h₂]

/- English proof (translation)
Rewrite using `[← cancel_epi ((𝟙 A) ^ d), ← Category.assoc, mulA_comm, Category.assoc, hf, inc_dMap h₁ h₂ pr₁ inc₁ pr₂ inc₂ hip₁ hpi₁ hip₂ hpi₂]`.
-/
theorem inc_of_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (pr₂ : Z₂ ⟶ A)
    (inc₂ : A ⟶ Z₂) [IsMonHom pr₁] [IsMonHom inc₁] [IsMonHom inc₂] [IsMonHom pr₂]
    (hip₁ : inc₁ ≫ pr₁ = 𝟙 A) (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d))
    (hip₂ : inc₂ ≫ pr₂ = 𝟙 A) (hpi₂ : pr₂ ≫ inc₂ = act₂ (idem d)) (e : Z₁ ⟶ Z₂) [Epi ((𝟙 A) ^ d)]
    (hf : ((𝟙 Z₁) ^ d) ≫ e = dMap d act₁ act₂ pr₁ inc₂) : inc₁ ≫ e = inc₂ := by
  rw [← cancel_epi ((𝟙 A) ^ d), ← Category.assoc, mulA_comm, Category.assoc, hf,
    inc_dMap h₁ h₂ pr₁ inc₁ pr₂ inc₂ hip₁ hpi₁ hip₂ hpi₂]

/- English proof (translation)
Rewrite using `[← cancel_epi ((𝟙 Z₁) ^ d), reassoc_of% hf, Category.comp_id]`. Unfold `dMap`. Rewrite using `[prod_comp']`. Establish `key : ∀ k, (act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ≫ e₂₁ = act₁ (lo d k * idem d * up d k)`. Introduce `k`.

Simplify using `only [Category.assoc]`. Rewrite using `[hlin, reassoc_of% hinc, reassoc_of% hpi₁, h₁.2.2.1, h₁.2.2.1, Category.assoc]`. Repeatedly rewrite using `[key]`. Rewrite using `[← act_sum' h₁, lo_idem_up_sum, act_zsmul' h₁, h₁.2.1, zpow_natCast]`.
-/
theorem inv_of_dMap (h₁ : IsRAct Z₁ act₁) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (inc₂ : A ⟶ Z₂)
    (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d)) (e₁₂ : Z₁ ⟶ Z₂) (e₂₁ : Z₂ ⟶ Z₁) [IsMonHom e₂₁] [Epi ((𝟙 Z₁) ^ d)]
    (hf : ((𝟙 Z₁) ^ d) ≫ e₁₂ = dMap d act₁ act₂ pr₁ inc₂) (hlin : ∀ o, act₂ o ≫ e₂₁ = e₂₁ ≫ act₁ o)
    (hinc : inc₂ ≫ e₂₁ = inc₁) : e₁₂ ≫ e₂₁ = 𝟙 Z₁ := by
  rw [← cancel_epi ((𝟙 Z₁) ^ d), reassoc_of% hf, Category.comp_id]
  unfold dMap
  rw [prod_comp']
  have key : ∀ k, (act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ≫ e₂₁ = act₁ (lo d k * idem d * up d k) := by
    intro k
    simp only [Category.assoc]
    rw [hlin, reassoc_of% hinc, reassoc_of% hpi₁, h₁.2.2.1, h₁.2.2.1, Category.assoc]
  simp_rw [key]
  rw [← act_sum' h₁, lo_idem_up_sum, act_zsmul' h₁, h₁.2.1, zpow_natCast]

end Main

end GlobalTheory.ZarhinUniqIso

namespace GlobalTheory.ZarhinUniqIso

open GlobalTheory.ZarhinFam

/- English proof (translation)
Introduce `h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ _hu h₁ h₂ hinc₁ hpr₁ hip₁ hpi₁ hinc₂ hpr₂ hip₂ hpi₂ hker`. Establish `hd1 : 1 ≤ d` using `hd`. Take `⟨fZ₁, sZ₁, qZ₁⟩` from `mulA_flat_surjective_qc z₁.A z₁.ab d hd1`. Take `⟨fZ₂, sZ₂, qZ₂⟩` from `mulA_flat_surjective_qc z₂.A z₂.ab d hd1`. Take `⟨fA, sA, qA⟩` from `mulA_flat_surjective_qc c.A c.ab d hd1`.

Establish `m₁ : IsMonHom ((𝟙 z₁.A) ^ d)` using `GlobalTheory.AbLaw.MulN.isMonHom_mulA z₁.A d`. Establish `m₂ : IsMonHom ((𝟙 z₂.A) ^ d)` using `GlobalTheory.AbLaw.MulN.isMonHom_mulA z₂.A d`. Establish `mA : IsMonHom ((𝟙 c.A) ^ d)` using `GlobalTheory.AbLaw.MulN.isMonHom_mulA c.A d`. Take `⟨⟨e₁₂, he₁₂, hf₁₂⟩, epi₁⟩` from `GlobalTheory.exists_monHom_factor_of_flat_surjective S z₁.A z₁.A z₂.A ((𝟙 z₁.A) ^ d) (dMap d act₁ act₂ pr₁ inc₂) m₁ (isMonHom_dMap h₁ h₂ pr₁ inc₂) fZ₁ sZ₁ qZ₁ (dMap_kill h₁ h₂ pr₁ inc₁ inc₂ hpi₁ (fun T x => (hker T x).1))`. Take `⟨⟨e₂₁, he₂₁, hf₂₁⟩, epi₂⟩` from `GlobalTheory.exists_monHom_factor_of_flat_surjective S z₂.A z₂.A z₁.A ((𝟙 z₂.A) ^ d) (dMap d act₂ act₁ pr₂ inc₁) m₂ (isMonHom_dMap h₂ h₁ pr₂ inc₁) fZ₂ sZ₂ qZ₂ (dMap_kill h₂ h₁ pr₂ inc₂ inc₁ hpi₂ (fun T x => (hker T x).2))`.

Establish `epiA` using `(GlobalTheory.exists_monHom_factor_of_flat_surjective S c.A c.A c.A ((𝟙 c.A) ^ d) ((𝟙 c.A) ^ d) mA mA fA sA qA (fun _ _ hx => hx)).2`. Establish `lin₁₂` using `lin_of_dMap h₁ h₂ pr₁ inc₂ e₁₂ hf₁₂`. Establish `lin₂₁` using `lin_of_dMap h₂ h₁ pr₂ inc₁ e₂₁ hf₂₁`. Establish `inc₁₂` using `inc_of_dMap h₁ h₂ pr₁ inc₁ pr₂ inc₂ hip₁ hpi₁ hip₂ hpi₂ e₁₂ hf₁₂`. Establish `inc₂₁` using `inc_of_dMap h₂ h₁ pr₂ inc₂ pr₁ inc₁ hip₂ hpi₂ hip₁ hpi₁ e₂₁ hf₂₁`.

Use `⟨⟨e₁₂, e₂₁, ?_, ?_⟩, he₁₂, inc₁₂, lin₁₂⟩` and prove the remaining obligations. Conclude with `inv_of_dMap h₁ pr₁ inc₁ inc₂ hpi₁ e₁₂ e₂₁ hf₁₂ lin₂₁ inc₂₁`. Conclude with `inv_of_dMap h₂ pr₂ inc₂ inc₁ hpi₂ e₂₁ e₁₂ hf₂₁ lin₁₂ inc₁₂`.
-/
theorem zarhin_uniq_iso : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (pr₂ : z₂.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → IsMonHom inc₂ → IsMonHom pr₂ → inc₂ ≫ pr₂ = 𝟙 c.A → pr₂ ≫ inc₂ = act₂ (GlobalTheory.ZarhinFam.idem d) → (∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔ x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1) → ∃ e : z₁.A ≅ z₂.A, IsMonHom e.hom ∧ inc₁ ≫ e.hom = inc₂ ∧ ∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o := by
  intro h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ _hu h₁ h₂ hinc₁ hpr₁ hip₁ hpi₁ hinc₂ hpr₂ hip₂ hpi₂ hker
  have hd1 : 1 ≤ d := hd
  obtain ⟨fZ₁, sZ₁, qZ₁⟩ := mulA_flat_surjective_qc z₁.A z₁.ab d hd1
  obtain ⟨fZ₂, sZ₂, qZ₂⟩ := mulA_flat_surjective_qc z₂.A z₂.ab d hd1
  obtain ⟨fA, sA, qA⟩ := mulA_flat_surjective_qc c.A c.ab d hd1
  have m₁ : IsMonHom ((𝟙 z₁.A) ^ d) := GlobalTheory.AbLaw.MulN.isMonHom_mulA z₁.A d
  have m₂ : IsMonHom ((𝟙 z₂.A) ^ d) := GlobalTheory.AbLaw.MulN.isMonHom_mulA z₂.A d
  have mA : IsMonHom ((𝟙 c.A) ^ d) := GlobalTheory.AbLaw.MulN.isMonHom_mulA c.A d
  obtain ⟨⟨e₁₂, he₁₂, hf₁₂⟩, epi₁⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S z₁.A z₁.A z₂.A
    ((𝟙 z₁.A) ^ d) (dMap d act₁ act₂ pr₁ inc₂) m₁ (isMonHom_dMap h₁ h₂ pr₁ inc₂) fZ₁ sZ₁ qZ₁
    (dMap_kill h₁ h₂ pr₁ inc₁ inc₂ hpi₁ (fun T x => (hker T x).1))
  obtain ⟨⟨e₂₁, he₂₁, hf₂₁⟩, epi₂⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S z₂.A z₂.A z₁.A
    ((𝟙 z₂.A) ^ d) (dMap d act₂ act₁ pr₂ inc₁) m₂ (isMonHom_dMap h₂ h₁ pr₂ inc₁) fZ₂ sZ₂ qZ₂
    (dMap_kill h₂ h₁ pr₂ inc₂ inc₁ hpi₂ (fun T x => (hker T x).2))
  have epiA := (GlobalTheory.exists_monHom_factor_of_flat_surjective S c.A c.A c.A ((𝟙 c.A) ^ d) ((𝟙 c.A) ^ d) mA mA
    fA sA qA (fun _ _ hx => hx)).2
  have lin₁₂ := lin_of_dMap h₁ h₂ pr₁ inc₂ e₁₂ hf₁₂
  have lin₂₁ := lin_of_dMap h₂ h₁ pr₂ inc₁ e₂₁ hf₂₁
  have inc₁₂ := inc_of_dMap h₁ h₂ pr₁ inc₁ pr₂ inc₂ hip₁ hpi₁ hip₂ hpi₂ e₁₂ hf₁₂
  have inc₂₁ := inc_of_dMap h₂ h₁ pr₂ inc₂ pr₁ inc₁ hip₂ hpi₂ hip₁ hpi₁ e₂₁ hf₂₁
  refine ⟨⟨e₁₂, e₂₁, ?_, ?_⟩, he₁₂, inc₁₂, lin₁₂⟩
  · exact inv_of_dMap h₁ pr₁ inc₁ inc₂ hpi₁ e₁₂ e₂₁ hf₁₂ lin₂₁ inc₂₁
  · exact inv_of_dMap h₂ pr₂ inc₂ inc₁ hpi₂ e₂₁ e₁₂ hf₂₁ lin₁₂ inc₁₂

end GlobalTheory.ZarhinUniqIso
