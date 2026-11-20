import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfInvariantGenTranslates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyKa

section
variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r₀ : Fin 4)

def rowEmb : x.P.A ⟶ Out.powObj x.P.A 4 :=
  (Out.powIsLimit x.P.A 4).lift (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c)

/- English proof (translation)
The claim follows from `(Out.powIsLimit x.P.A 4).fac (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c) ⟨c⟩`.
-/
theorem rowEmb_pr (c : Fin 4) : rowEmb x al r₀ ≫ Out.powPr x.P.A c = (𝟙 x.P.A) ^ al r₀ c :=
  (Out.powIsLimit x.P.A 4).fac (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c) ⟨c⟩

/- English proof (translation)
Use `x.P.isAb.comm` as an intermediate fact. Establish `h : al r₀ 0 * al r 0 + (al r₀ 1 * al r 1 + (al r₀ 2 * al r 2 + al r₀ 3 * al r 3)) = if r = r₀ then (m : ℤ) else 0`. Use `congrFun (congrFun hal r₀) r` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, eq_comm (a := r₀)] at this`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[alMap, MonObj.comp_mul, ← Category.assoc, comp_toUnit]`. Use `congr 1`. Simplify using `only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow, rowEmb_pr, _root_.mul_one, ← zpow_mul, ← zpow_add]`. Use `(congrArg (fun n : ℤ => (𝟙 x.P.A) ^ n) h).trans ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `zpow_natCast _ _`. Conclude with `zpow_zero _`.
-/
theorem rowEmb_alMap {m : ℕ} (hal : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (r : Fin 4)
    (ζ : Pt x) : rowEmb x al r₀ ≫ alMap x al r ζ =
      (if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ) := by
  have := x.P.isAb.comm
  have h : al r₀ 0 * al r 0 + (al r₀ 1 * al r 1 + (al r₀ 2 * al r 2 + al r₀ 3 * al r 3)) =
      if r = r₀ then (m : ℤ) else 0 := by
    have := congrFun (congrFun hal r₀) r
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, eq_comm (a := r₀)] at this
    rw [← this]; ring
  rw [alMap, MonObj.comp_mul, ← Category.assoc, comp_toUnit]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
    rowEmb_pr, _root_.mul_one, ← zpow_mul, ← zpow_add]
  refine (congrArg (fun n : ℤ => (𝟙 x.P.A) ^ n) h).trans ?_
  split_ifs
  · exact zpow_natCast _ _
  · exact zpow_zero _

/- English proof (translation)
Use `x.P.isAb.comm` as an intermediate fact. Use `(Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(_ ≫ _) ≫ Out.powPr x.P.A c = (_ ≫ _) ≫ Out.powPr x.P.A c`. Rewrite using `[Category.assoc, Category.assoc, rowEmb_pr, MonObj.mul_comp _ _ (Out.powPr x.P.A c), MonObj.comp_mul, Category.id_comp, Category.assoc, Category.assoc, rowEmb_pr, ← Category.assoc (rowEmb x al r₀), comp_toUnit]`. Simplify using `only [GrpObj.comp_zpow, Category.comp_id, mul_zpow]`.
-/
theorem transl_rowEmb (δ : Pt x) : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A) ≫ rowEmb x al r₀ =
    rowEmb x al r₀ ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ rowEmb x al r₀) * 𝟙 (Out.powObj x.P.A 4)) := by
  have := x.P.isAb.comm
  refine (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => ?_
  change (_ ≫ _) ≫ Out.powPr x.P.A c = (_ ≫ _) ≫ Out.powPr x.P.A c
  rw [Category.assoc, Category.assoc, rowEmb_pr, MonObj.mul_comp _ _ (Out.powPr x.P.A c), MonObj.comp_mul, Category.id_comp, Category.assoc,
    Category.assoc, rowEmb_pr, ← Category.assoc (rowEmb x al r₀), comp_toUnit]
  simp only [GrpObj.comp_zpow, Category.comp_id, mul_zpow]

end

/- English proof (translation)
Introduce `laws K _ _ x m al ξ ξ' w w' hm hal hw hw' hinv`. Establish `hL` using `x.P.isLB`. Establish `hm0 : (m : ℤ) ≠ 0` using `fun h => hm (by rw [Int.natCast_eq_zero.1 h, Nat.cast_zero])`. Establish `hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)`. Establish `hd : al.det ≠ 0` using `fun h => by`.

Use `congrArg Matrix.det hal` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one]`. Conclude with `pow_ne_zero _ hm0 this.symm`. Establish `h1 : (al * al.transpose - (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al = 0`. Rewrite using `[sub_mul, _root_.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, _root_.mul_one, _root_.one_mul, sub_self]`.

Establish `h2` using `congrArg (· * al.adjugate) h1`. Simplify using `only [_root_.mul_assoc, Matrix.mul_adjugate, zero_mul, Matrix.mul_smul, _root_.mul_one] at h2`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)`. Use function extensionality and compare the values at `r₀`. Take `⟨g, hg⟩` from `DVR.exists_gen_of_local (V := K) x.P.L hL (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (ξ r).left) (fun r => (ξ' r).left)) (Sum.elim (fun r => if r = r₀ then 0 else -1) (fun r => if r = r₀ then 0 else 1))`.

Set `i` to `rowEmb x al r₀`. Establish `hu₀` using `DVR.mulGen_isGen x.P.L _ _ _ _ _ _ (DVR.mulGen_isGen x.P.L _ _ _ _ _ _ (DVR.pullGen_isGen x.P.L _ _ w hw i.left) (DVR.invGen_isGen x.P.L _ _ _ (DVR.pullGen_isGen x.P.L _ _ w' hw' i.left))) (DVR.pullGen_isGen x.P.L _ _ g hg (toUnit x.P.A).left)`. Take `⟨u, hu, hval⟩` from `exists_gen hL (K' := Fin 2) (φ' := ![((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ r₀)).left, ((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ' r₀)).left]) (ε' := ![1, -1]) (by`. Introduce `U _ h`. Establish `e : ∀ (r : Fin 4) (ζ : Pt x), i.left ≫ (alMap x al r ζ).left = ((if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ)).left` using `fun r ζ => congrArg (fun q => q.left) (rowEmb_alMap x al r₀ hal' r ζ)`.

Establish `e' : ∀ ζ : Pt x, (toUnit x.P.A).left ≫ ζ.left = (toUnit x.P.A ≫ ζ).left` using `fun _ => rfl`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]`. Simplify using `only [← Finset.prod_mul_distrib]`. Rewrite using `[Finset.prod_eq_single r₀ (fun r _ hr => ?_) (fun hr => absurd (Finset.mem_univ _) hr)]`. Simplify using `only [if_true, zpow_zero, _root_.mul_one, zpow_neg]`.

Rewrite using `[_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]`. Simplify using `only [if_neg hr, _root_.one_mul, zpow_one, zpow_neg, e']`. Rewrite using `[_root_.mul_mul_mul_comm, mul_inv_cancel_comm, inv_mul_cancel_comm, inv_mul_cancel]) _ hu₀`. Use `GlobalTheory.eq_of_invariantGen_translates laws K x.P m (ξ r₀) (ξ' r₀) u hm hu fun δ hδ y J hJ => ?_` and prove the remaining obligations. Establish `hv` using `hinv (δ ≫ i) (fun r => by`.

Rewrite using `[Category.assoc, rowEmb_alMap x al r₀ hal', MonObj.comp_one, _root_.mul_one]`. Use `split_ifs`. Rewrite using `[MonObj.comp_pow, Category.comp_id, hδ]`. Conclude with `MonObj.comp_one _) _ i.left y J hJ`. Establish `e₁ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ i.left = i.left ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ i) * 𝟙 (Out.powObj x.P.A 4)).left` using `congrArg (fun q => q.left) (transl_rowEmb x al r₀ δ)`.

Establish `e₂ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ (toUnit x.P.A).left = (toUnit x.P.A).left` using `congrArg (fun q => q.left) (comp_toUnit ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A))`. Rewrite using `[hval _ _ y J hJ, hval _ _ y J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, e₁, Category.id_comp, Category.id_comp]`. Use `erw [e₂]`. Use `congr 1`. Rewrite using `[mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, hv, mul_comm]`.
-/
theorem eq_of_similitude_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  intro laws K _ _ x m al ξ ξ' w w' hm hal hw hw' hinv
  have hL := x.P.isLB
  have hm0 : (m : ℤ) ≠ 0 := fun h => hm (by rw [Int.natCast_eq_zero.1 h, Nat.cast_zero])
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hd : al.det ≠ 0 := fun h => by
      have := congrArg Matrix.det hal
      rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
      exact pow_ne_zero _ hm0 this.symm
    have h1 : (al * al.transpose - (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al = 0 := by
      rw [sub_mul, _root_.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, _root_.mul_one,
        _root_.one_mul, sub_self]
    have h2 := congrArg (· * al.adjugate) h1
    simp only [_root_.mul_assoc, Matrix.mul_adjugate, zero_mul, Matrix.mul_smul, _root_.mul_one] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)
  funext r₀
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) x.P.L hL (K := Fin 4 ⊕ Fin 4)
    (Sum.elim (fun r => (ξ r).left) (fun r => (ξ' r).left))
    (Sum.elim (fun r => if r = r₀ then 0 else -1) (fun r => if r = r₀ then 0 else 1))
  let i := rowEmb x al r₀
  have hu₀ := DVR.mulGen_isGen x.P.L _ _ _ _ _ _
    (DVR.mulGen_isGen x.P.L _ _ _ _ _ _ (DVR.pullGen_isGen x.P.L _ _ w hw i.left)
      (DVR.invGen_isGen x.P.L _ _ _ (DVR.pullGen_isGen x.P.L _ _ w' hw' i.left)))
    (DVR.pullGen_isGen x.P.L _ _ g hg (toUnit x.P.A).left)
  obtain ⟨u, hu, hval⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ r₀)).left, ((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ' r₀)).left])
    (ε' := ![1, -1]) (by
      intro U _ h
      have e : ∀ (r : Fin 4) (ζ : Pt x), i.left ≫ (alMap x al r ζ).left =
          ((if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ)).left := fun r ζ =>
        congrArg (fun q => q.left) (rowEmb_alMap x al r₀ hal' r ζ)
      have e' : ∀ ζ : Pt x, (toUnit x.P.A).left ≫ ζ.left = (toUnit x.P.A ≫ ζ).left := fun _ => rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, neg_neg]
      simp only [← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_single r₀ (fun r _ hr => ?_) (fun hr => absurd (Finset.mem_univ _) hr)]
      · simp only [if_true, zpow_zero, _root_.mul_one, zpow_neg]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]
      · simp only [if_neg hr, _root_.one_mul, zpow_one, zpow_neg, e']
        rw [_root_.mul_mul_mul_comm, mul_inv_cancel_comm, inv_mul_cancel_comm, inv_mul_cancel]) _ hu₀
  refine GlobalTheory.eq_of_invariantGen_translates laws K x.P m (ξ r₀) (ξ' r₀) u hm hu fun δ hδ y J hJ => ?_
  have hv := hinv (δ ≫ i) (fun r => by
    rw [Category.assoc, rowEmb_alMap x al r₀ hal', MonObj.comp_one, _root_.mul_one]
    split_ifs
    · rw [MonObj.comp_pow, Category.comp_id, hδ]
    · exact MonObj.comp_one _) _ i.left y J hJ
  have e₁ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ i.left =
      i.left ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ i) * 𝟙 (Out.powObj x.P.A 4)).left :=
    congrArg (fun q => q.left) (transl_rowEmb x al r₀ δ)
  have e₂ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ (toUnit x.P.A).left = (toUnit x.P.A).left :=
    congrArg (fun q => q.left) (comp_toUnit ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A))
  rw [hval _ _ y J hJ, hval _ _ y J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, e₁, Category.id_comp,
    Category.id_comp]
  erw [e₂]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, hv, mul_comm]

end GlobalTheory.KeyKa

end
