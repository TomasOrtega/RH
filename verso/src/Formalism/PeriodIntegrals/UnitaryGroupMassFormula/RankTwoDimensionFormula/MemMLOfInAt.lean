import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.ReferenceReprMemLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DualBetaReferenceCongruence

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section Par

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Establish `hdot : ∀ x y : n → A, Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y)`. Introduce `x y`. Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Establish `hσ : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i))`. Use function extensionality and compare the values at `i`.

Simplify using `[mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[hdot, hdot, hσ, ← vecMul_transpose, ← dotProduct_mulVec]`. Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc]`. Rewrite using `[show (M.map σ)ᵀ * J * M = J from hM]`.
-/
theorem hform_mulVec' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hdot : ∀ x y : n → A, Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [hdot, hdot, hσ, ← vecMul_transpose, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [show (M.map σ)ᵀ * J * M = J from hM]

/- English proof (translation)
The claim follows from `hform_mulVec' _ _ _ g.2 x y`.
-/
theorem hA_unit (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat g *ᵥ x) (X.B.I.fmat g *ᵥ y) = hA X.B.I x y :=
  hform_mulVec' _ _ _ g.2 x y

/- English proof (translation)
Use `conv_lhs => rw [← hA_unit X g⁻¹ x (X.B.I.fmat g *ᵥ y)]`. Rewrite using `[Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]`.
-/
theorem hA_adj (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := by
  conv_lhs => rw [← hA_unit X g⁻¹ x (X.B.I.fmat g *ᵥ y)]
  rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨c, hc, hcd⟩` from `h`. Establish `hb : ((c : ℤ) * Nat.gcdA c X.B.g + (X.B.g : ℤ) * Nat.gcdB c X.B.g) = 1`. Rewrite using `[← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]`. Both sides reduce to the same expression. Establish `e : d = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) + ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d)`.

Rewrite using `[smul_smul, smul_smul, ← add_smul]`. Establish `: ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) + ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1`. Use `congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.

Rewrite using `[this, one_smul]`. Rewrite using `[e]`. Establish `hint : ∀ z : ℤ, ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E` using `fun z => intCast_mem _ z`. Establish `sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ mL X.B.I X.B.g → ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ mL X.B.I X.B.g` using `fun z w hw => by`. Establish `: ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, hint z⟩ : IntAf X.B.I.F X.B.I.E) • w` using `rfl`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hw`. Conclude with `add_mem (sm _ _ hcd) (sm _ _ (smul_mem_mL X.B.I hd))`.
-/
theorem mem_mL_of_InAt {d : VA X.B.I} (hd : d ∈ X.B.I.Lf) (h : InAt X.B.I X.B.g X.B.g d) :
    d ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcd⟩ := h
  have hb : ((c : ℤ) * Nat.gcdA c X.B.g + (X.B.g : ℤ) * Nat.gcdB c X.B.g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have e : d = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) +
      ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
      have := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
      push_cast at this
      linear_combination this
    rw [this, one_smul]
  rw [e]
  have hint : ∀ z : ℤ, ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := fun z => intCast_mem _ z
  have sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ mL X.B.I X.B.g →
      ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ mL X.B.I X.B.g := fun z w hw => by
    have : ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, hint z⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
    rw [this]; exact Submodule.smul_mem _ _ hw
  exact add_mem (sm _ _ hcd) (sm _ _ (smul_mem_mL X.B.I hd))

/- English proof (translation)
Take `⟨hE, hF, hZ, hB, hBd⟩` from `frame_Lf X`. Establish `hd` using `dual_coords X hv`. Establish `e : v = (v - repr0 X v) + repr0 X v` using `by abel`. Rewrite using `[e]`. Use `add_mem (mL_Mo X.B.I hd) ?_` and prove the remaining obligations.

Establish `spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E → w ∈ Set.range X.e0 ∪ Set.range X.bw → c • w ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw)` using `fun c w hc hw => by`. Establish `: c • w = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • w` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (sub_Mo X.B.I hw)`. Unfold `repr0`.

Use `add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_` and prove the remaining obligations. Conclude with `sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF a) hv) (Or.inl ⟨a, rfl⟩)`. Conclude with `sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))`. Conclude with `mL_Mo X.B.I (Z_smul_mL X hz hZ)`. Conclude with `sum_mem fun l _ => spn _ _ (hA_int X.B.I (hBd l) hv) (Or.inr ⟨l, rfl⟩)`.

Conclude with `sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))`.
-/
theorem mem_Mo_eb {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) :
    v ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  have e : v = (v - repr0 X v) + repr0 X v := by abel
  rw [e]
  refine add_mem (mL_Mo X.B.I hd) ?_
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      w ∈ Set.range X.e0 ∪ Set.range X.bw → c • w ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) :=
    fun c w hc hw => by
      have : c • w = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hw)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF a) hv) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => spn _ _ (hA_int X.B.I (hBd l) hv) (Or.inr ⟨l, rfl⟩)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

def Par (x : X.B.I.Gf) : Prop :=
  x ∈ X.B.I.Kset ∧ (∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) ∧
    ∀ j, X.B.I.fmat x *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw)

def Good (x : X.B.I.Gf) : Prop := Par X x ∧ Par X x⁻¹

/- English proof (translation)
Use `⟨K_one X.B.I, fun a => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]`. Conclude with `sub_Mo X.B.I ⟨a, rfl⟩`. Rewrite using `[show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]`. Conclude with `sub_Mo X.B.I (Or.inr ⟨j, rfl⟩)`.
-/
theorem par_one : Par X 1 := by
  refine ⟨K_one X.B.I, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]; exact sub_Mo X.B.I ⟨a, rfl⟩
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]; exact sub_Mo X.B.I (Or.inr ⟨j, rfl⟩)

/- English proof (translation)
Use `⟨K_mul X.B.I hx.1 hy.1, fun a => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[fmat_mul, ← Matrix.mulVec_mulVec]`. Use `pres X.B.I hx.1 X.B.g (Set.range X.e0) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.1 a)` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`.

Conclude with `sub_mem (hx.2.1 b) (sub_Mo X.B.I ⟨b, rfl⟩)`. Rewrite using `[fmat_mul, ← Matrix.mulVec_mulVec]`. Use `pres X.B.I hx.1 X.B.g (Set.range X.e0 ∪ Set.range X.bw) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.2 j)` and prove the remaining obligations. Introduce and unpack `s (⟨b, rfl⟩ | ⟨l, rfl⟩)`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`.

Conclude with `sub_mem (Mo_mono X.B.I Set.subset_union_left (hx.2.1 b)) (sub_Mo X.B.I (Or.inl ⟨b, rfl⟩))`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `sub_mem (hx.2.2 l) (sub_Mo X.B.I (Or.inr ⟨l, rfl⟩))`.
-/
theorem par_mul {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) : Par X (x * y) := by
  refine ⟨K_mul X.B.I hx.1 hy.1, fun a => ?_, fun j => ?_⟩
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.1 a)
    rintro _ ⟨b, rfl⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (hx.2.1 b) (sub_Mo X.B.I ⟨b, rfl⟩)
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0 ∪ Set.range X.bw) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.2 j)
    rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (Mo_mono X.B.I Set.subset_union_left (hx.2.1 b)) (sub_Mo X.B.I (Or.inl ⟨b, rfl⟩))
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hx.2.2 l) (sub_Mo X.B.I (Or.inr ⟨l, rfl⟩))

/- English proof (translation)
Assemble the required witnesses or components as `⟨par_one X, by simpa using par_one X⟩`.
-/
theorem good_one : Good X 1 := ⟨par_one X, by simpa using par_one X⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨par_mul X hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact par_mul X hy.2 hx.2⟩`.
-/
theorem good_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : Good X (x * y) :=
  ⟨par_mul X hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact par_mul X hy.2 hx.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hx.2, by rw [inv_inv]; exact hx.1⟩`.
-/
theorem good_inv {x : X.B.I.Gf} (hx : Good X x) : Good X x⁻¹ := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {X} (TR : TypedRed X)

/- English proof (translation)
The claim follows from `leviM_mul TR hx.1 hy.1 hy.2.2 hx.2.1 v`.
-/
theorem leviM_mul_par {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v :=
  leviM_mul TR hx.1 hy.1 hy.2.2 hx.2.1 v

/- English proof (translation)
Use extensionality with `i j`. Establish `hbw : ∀ j, X.bw j ∈ X.B.I.Lf` using `fun j => (X.vectorsInLattice.2.2 j).1`. Establish `hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf` using `fun j => (X.vectorsInLattice.2.2 j).2`. Simplify using `only [leviM, show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]`. Establish `hI` using `hA_int X.B.I (hbwd i) (hbw j)`.

Rewrite using `[resT_of_mem TR v hI]`. Establish `hZ` using `X.bw_dual i j`. Establish `hIt : (if i = j then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E` using `by split_ifs`. Conclude with `X.ew_int`. Conclude with `zero_mem _`.

Establish `e : (⟨_, hI⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, sub_mem hI hIt⟩ + ⟨_, hIt⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[e, map_add, res_eq_zero_of_Z TR v _ hZ, zero_add]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `only [if_true, Matrix.one_apply_eq]`. Establish `e2 : (⟨X.ew, X.ew_int⟩ : IntAf X.B.I.F X.B.I.E) = ⟨X.ew * (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (one_mem _)⟩` using `by apply Subtype.ext; simp`. Use `TR.res_ew v 1` as an intermediate fact. Simplify using `only [OneMemClass.coe_one] at this`.

Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `(map_one (TR.res v)).symm`. Simplify using `only [h, if_false, Matrix.one_apply_ne h]`. Conclude with `map_zero (TR.res v) |>.symm ▸ (by congr 1)`.
-/
theorem leviM_one (v : TR.Pl) : leviM TR 1 v = 1 := by
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  simp only [leviM, show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  have hI := hA_int X.B.I (hbwd i) (hbw j)
  rw [resT_of_mem TR v hI]
  have hZ := X.bw_dual i j
  have hIt : (if i = j then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have e : (⟨_, hI⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, sub_mem hI hIt⟩ + ⟨_, hIt⟩ := by
    apply Subtype.ext; simp
  rw [e, map_add, res_eq_zero_of_Z TR v _ hZ, zero_add]
  by_cases h : i = j
  · subst h
    simp only [if_true, Matrix.one_apply_eq]
    have e2 : (⟨X.ew, X.ew_int⟩ : IntAf X.B.I.F X.B.I.E) = ⟨X.ew * (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (one_mem _)⟩ := by apply Subtype.ext; simp
    have := TR.res_ew v 1
    simp only [OneMemClass.coe_one] at this
    convert this using 2
    exact (map_one (TR.res v)).symm
  · simp only [h, if_false, Matrix.one_apply_ne h]
    exact map_zero (TR.res v) |>.symm ▸ (by congr 1)

end Par

end PI.UnitaryDimensionFormula.NormCutK
