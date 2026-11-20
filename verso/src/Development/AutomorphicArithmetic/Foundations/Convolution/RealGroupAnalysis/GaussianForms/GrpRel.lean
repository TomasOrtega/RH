import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

section
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma nU_val (b : A F) : (nU b).1 = !![1, b; 0, 1] := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma mD_val (a : (A F)ˣ) : (mD a).1 = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

/- English proof (translation)
The claim follows from `Subtype.ext e`.
-/
private lemma sl_ext {g h : G1 F} (e : g.1 = h.1) : g = h := Subtype.ext e

/- English proof (translation)
Apply `sl_ext` to reduce the goal to its premises. Rewrite using `[e, Matrix.eta_fin_two g.1, h00, h01, h10, h11]`.
-/
private lemma sl_of {g h : G1 F} {p q r s : A F} (e : h.1 = !![p, q; r, s])
    (h00 : g.1 0 0 = p) (h01 : g.1 0 1 = q) (h10 : g.1 1 0 = r) (h11 : g.1 1 1 = s) : g = h := by
  apply sl_ext
  rw [e, Matrix.eta_fin_two g.1, h00, h01, h10, h11]

/- English proof (translation)
Establish `h` using `g.det_coe`. Rewrite `h` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis.
-/
private lemma det_eq (g : G1 F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

/- English proof (translation)
Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, nU_val, mD_val, Matrix.mul_fin_two]`. Simplify using the standard rewrite rules.
-/
private lemma nm_val (b : A F) (a : (A F)ˣ) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, mD_val, Matrix.mul_fin_two]
  simp

/- English proof (translation)
Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, nm_val, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]`. Use `congr 1`. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form.
-/
private lemma cell_val (b b' : A F) (a : (A F)ˣ) :
    (nU b * mD a * wW F * nU b').1 =
      !![-(b * ((a⁻¹ : (A F)ˣ) : A F)), (a : A F) - b * ((a⁻¹ : (A F)ˣ) : A F) * b';
        -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b')] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, nm_val, wW_val, nU_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  simp
  ring_nf

/- English proof (translation)
Apply `sl_ext` to reduce the goal to its premises. Simplify using `[nU_val, Matrix.one_fin_two]`. Use `N_add b c := by`. Apply `sl_ext` to reduce the goal to its premises. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, nU_val, nU_val, nU_val, Matrix.mul_fin_two]`.

Simplify using `[add_comm]`. Use `M_one := by`. Apply `sl_ext` to reduce the goal to its premises. Simplify using `[mD_val, Matrix.one_fin_two]`. Use `M_mul a a' := by`.

Apply `sl_ext` to reduce the goal to its premises. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, mD_val, mD_val, mD_val, Matrix.mul_fin_two]`. Simplify using `[mul_comm]`. Use `MN a b := by`. Apply `sl_ext` to reduce the goal to its premises.

Establish `he : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1` using `a.mul_inv`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, nm_val, mD_val, nU_val, Matrix.mul_fin_two]`. Establish `hq : (a : A F) ^ 2 * b * ((a⁻¹ : (A F)ˣ) : A F) = (a : A F) * b`. Take the linear combination `((a : A F) * b) * he`. Simplify using `[hq]`.

Use `WM a := by`. Apply `sl_ext` to reduce the goal to its premises. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, mD_val, mD_val, Matrix.mul_fin_two, Matrix.mul_fin_two]`. Simplify using the standard rewrite rules. Use `W_unit := Group.isUnit _`.
-/
private lemma rel_part : Rel (nU (F := F)) mD (wW F) where
  N_zero := by
    apply sl_ext
    simp [nU_val, Matrix.one_fin_two]
  N_add b c := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, nU_val, nU_val, Matrix.mul_fin_two]
    simp [add_comm]
  M_one := by
    apply sl_ext
    simp [mD_val, Matrix.one_fin_two]
  M_mul a a' := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, mD_val, mD_val, mD_val, Matrix.mul_fin_two]
    simp [mul_comm]
  MN a b := by
    apply sl_ext
    have he : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
    rw [Matrix.SpecialLinearGroup.coe_mul, nm_val, mD_val, nU_val, Matrix.mul_fin_two]
    have hq : (a : A F) ^ 2 * b * ((a⁻¹ : (A F)ˣ) : A F) = (a : A F) * b := by
      linear_combination ((a : A F) * b) * he
    simp [hq]
  WM a := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, mD_val, mD_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp
  W_unit := Group.isUnit _

/- English proof (translation)
Introduce `t`. Apply `sl_ext` to reduce the goal to its premises. Establish `he : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1` using `t.mul_inv`. Rewrite using `[cell_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]`. Simplify using `[he]`.
-/
private lemma gauss_part : Gauss (nU (F := F)) mD (wW F) := by
  intro t
  apply sl_ext
  have he : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := t.mul_inv
  rw [cell_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [he]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : g.1 1 0 = 0` using `h`. Establish `hd` using `det_eq g`. Rewrite `hd` using `[h', mul_zero, sub_zero]`.

Establish `hd' : g.1 1 1 * g.1 0 0 = 1` using `by rw [mul_comm]; exact hd`. Use `⟨g.1 0 1 * g.1 0 0, ⟨g.1 0 0, g.1 1 1, hd, hd'⟩, ?_⟩` and prove the remaining obligations. Use `sl_of (nm_val _ _) rfl ?_ h' rfl` and prove the remaining obligations. Use `show g.1 0 1 = g.1 0 1 * g.1 0 0 * g.1 1 1`. Take the linear combination `(-g.1 0 1) * hd`.

Introduce and unpack `⟨b, a, rfl⟩ show (nU b * mD a).1 1 0 = 0`. Rewrite using `[nm_val]`. Simplify using the standard rewrite rules.
-/
private lemma tri_part (g : G1 F) : g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a := by
  constructor
  · intro h
    have h' : g.1 1 0 = 0 := h
    have hd := det_eq g
    rw [h', mul_zero, sub_zero] at hd
    have hd' : g.1 1 1 * g.1 0 0 = 1 := by rw [mul_comm]; exact hd
    refine ⟨g.1 0 1 * g.1 0 0, ⟨g.1 0 0, g.1 1 1, hd, hd'⟩, ?_⟩
    refine sl_of (nm_val _ _) rfl ?_ h' rfl
    show g.1 0 1 = g.1 0 1 * g.1 0 0 * g.1 1 1
    linear_combination (-g.1 0 1) * hd
  · rintro ⟨b, a, rfl⟩
    show (nU b * mD a).1 1 0 = 0
    rw [nm_val]
    simp

/- English proof (translation)
Establish `h` using `congrArg Subtype.val e`. Rewrite `h` using `[nm_val, nm_val]`. Establish `h00` using `congrFun (congrFun h 0) 0`. Establish `h01` using `congrFun (congrFun h 0) 1`. Simplify using `at h00 h01`.

Establish `ha : a = a'` using `Units.ext h00`. Substitute `ha` using the available equality. Conclude with `⟨(Units.mul_left_inj _).1 h01, rfl⟩`.
-/
private lemma tri_uniq (b b' : A F) (a a' : (A F)ˣ) (e : nU b * mD a = nU b' * mD a') : b = b' ∧ a = a' := by
  have h := congrArg Subtype.val e
  rw [nm_val, nm_val] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  have ha : a = a' := Units.ext h00
  subst ha
  exact ⟨(Units.mul_left_inj _).1 h01, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `hc' : g.1 1 0 = (c : A F)` using `hc.symm`. Establish `he : (c : A F) * ((c⁻¹ : (A F)ˣ) : A F) = 1` using `c.mul_inv`. Establish `hd` using `det_eq g`.

Rewrite `hd` using `[hc']`. Use `⟨g.1 0 0 * ((c⁻¹ : (A F)ˣ) : A F), -c⁻¹, g.1 1 1 * ((c⁻¹ : (A F)ˣ) : A F), ?_⟩` and prove the remaining obligations. Use `sl_of (cell_val _ _ _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [inv_neg, inv_inv, Units.val_neg]`. Take the linear combination `(-g.1 0 0) * he`.

Simplify using `only [inv_neg, inv_inv, Units.val_neg]`. Take the linear combination `(-((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) ^ 2)) * hd + (-((c⁻¹ : (A F)ˣ) : A F) - g.1 0 1 * ((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) + 1)) * he`. Simplify using `only [inv_neg, inv_inv, Units.val_neg, neg_neg]`. Conclude with `hc'`. Simplify using `only [inv_neg, inv_inv, Units.val_neg]`.

Take the linear combination `(-g.1 1 1) * he`. Introduce and unpack `⟨b, a, b', rfl⟩ show IsUnit ((nU b * mD a * wW F * nU b').1 1 0)`. Rewrite using `[cell_val]`. Simplify using the standard rewrite rules.
-/
private lemma cell_part (g : G1 F) : IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  constructor
  · rintro ⟨c, hc⟩
    have hc' : g.1 1 0 = (c : A F) := hc.symm
    have he : (c : A F) * ((c⁻¹ : (A F)ˣ) : A F) = 1 := c.mul_inv
    have hd := det_eq g
    rw [hc'] at hd
    refine ⟨g.1 0 0 * ((c⁻¹ : (A F)ˣ) : A F), -c⁻¹, g.1 1 1 * ((c⁻¹ : (A F)ˣ) : A F), ?_⟩
    refine sl_of (cell_val _ _ _) ?_ ?_ ?_ ?_
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 0 0) * he
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) ^ 2)) * hd +
        (-((c⁻¹ : (A F)ˣ) : A F) - g.1 0 1 * ((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) + 1)) * he
    · simp only [inv_neg, inv_inv, Units.val_neg, neg_neg]
      exact hc'
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 1 1) * he
  · rintro ⟨b, a, b', rfl⟩
    show IsUnit ((nU b * mD a * wW F * nU b').1 1 0)
    rw [cell_val]
    simp
end

/- English proof (translation)
Introduce `F _ _`. Conclude with `⟨rel_part, gauss_part, tri_part, tri_uniq, cell_part⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.grpRel :
    ∀ (F : Type) [Field F] [NumberField F], Rel (nU (F := F)) mD (wW F) ∧ Gauss (nU (F := F)) mD (wW F) ∧
    (∀ g : G1 F, g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a) ∧ (∀ (b b' : A F) a a', nU b * mD a = nU b' * mD a' → b = b' ∧ a = a') ∧
    ∀ g : G1 F, IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  intro F _ _
  exact ⟨rel_part, gauss_part, tri_part, tri_uniq, cell_part⟩
