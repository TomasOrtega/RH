import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdInvOfBlockTriangular

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct GlobalTheory.IwahoriFactor
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.IwGLV

section Tri

variable {L : Type} [Field L] {n : ℕ}

def btSub {α : Type} [LinearOrder α] (b : Fin n → α) : Subgroup (GL (Fin n) L) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) L).BlockTriangular b}
  one_mem' := by simpa using Matrix.blockTriangular_one (b := b) (R := L)
  mul_mem' := fun {x y} hx hy => by simpa using Matrix.BlockTriangular.mul hx hy
  inv_mem' := fun {g} hg => by
    letI : Invertible (g : Matrix (Fin n) (Fin n) L) := g.invertible
    have := Matrix.blockTriangular_inv_of_blockTriangular (M := (g : Matrix (Fin n) (Fin n) L)) hg
    simpa [Matrix.coe_units_inv] using this

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne (hb.ne hk) with h | h` into its components or cases. Rewrite using `[hA h]`. Simplify using the standard rewrite rules.

Rewrite using `[hB h]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem mul_diag {α : Type} [LinearOrder α] {b : Fin n → α} (hb : Function.Injective b)
    {A B : Matrix (Fin n) (Fin n) L} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hA h]; simp
    · rw [hB h]; simp
  · simp

def triSub {α : Type} [LinearOrder α] (b : Fin n → α) (hb : Function.Injective b) :
    Subgroup (GL (Fin n) L) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) L).BlockTriangular b ∧
    ∀ i, (g : Matrix (Fin n) (Fin n) L) i i = 1}
  one_mem' := ⟨(btSub b).one_mem, fun i => by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨(btSub b).mul_mem hx.1 hy.1, fun i => by
    rw [Units.val_mul, mul_diag hb hx.1 hy.1, hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {g} hg => by
    have h3 : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular b :=
      (btSub b).inv_mem hg.1
    refine ⟨h3, fun i => ?_⟩
    have := mul_diag hb hg.1 h3 i
    rw [← Units.val_mul, mul_inv_cancel, hg.2, one_mul] at this
    simpa using this.symm

/- English proof (translation)
Establish `h1 : t * h ∈ btSub b` using `(btSub b).mul_mem ht hh.1`. Establish `h2 : t⁻¹ ∈ btSub b` using `(btSub b).inv_mem ht`. Use `⟨(btSub b).mul_mem h1 h2, fun i => ?_⟩` and prove the remaining obligations. Establish `e1` using `mul_diag hb h1 h2 i`. Establish `e2` using `mul_diag hb ht hh.1 i`.

Establish `e3` using `mul_diag hb ht h2 i`. Rewrite using `[Units.val_mul, e1, Units.val_mul, e2, hh.2 i, mul_one, ← e3, ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules.
-/
theorem conj_mem {α : Type} [LinearOrder α] {b : Fin n → α} (hb : Function.Injective b)
    {t h : GL (Fin n) L} (ht : t ∈ btSub b) (hh : h ∈ triSub b hb) : t * h * t⁻¹ ∈ triSub b hb := by
  have h1 : t * h ∈ btSub b := (btSub b).mul_mem ht hh.1
  have h2 : t⁻¹ ∈ btSub b := (btSub b).inv_mem ht
  refine ⟨(btSub b).mul_mem h1 h2, fun i => ?_⟩
  have e1 := mul_diag hb h1 h2 i
  have e2 := mul_diag hb ht hh.1 i
  have e3 := mul_diag hb ht h2 i
  rw [Units.val_mul, e1, Units.val_mul, e2, hh.2 i, mul_one, ← e3, ← Units.val_mul, mul_inv_cancel]
  simp

def diagSub : Subgroup (GL (Fin n) L) :=
  btSub (id : Fin n → Fin n) ⊓ btSub (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ)

def upSub : Subgroup (GL (Fin n) L) := triSub (id : Fin n → Fin n) Function.injective_id

def lowSub : Subgroup (GL (Fin n) L) :=
  triSub (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) OrderDual.toDual.injective

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun _ _ hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩`.
-/
theorem mem_upSub {g : GL (Fin n) L} : g ∈ upSub ↔ IsUniM g :=
  ⟨fun h => ⟨fun _ _ hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun _ _ hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩`.
-/
theorem mem_lowSub {g : GL (Fin n) L} : g ∈ lowSub ↔ IsLowUniM g :=
  ⟨fun h => ⟨fun _ _ hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hij`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `h2 (show OrderDual.toDual j < OrderDual.toDual i from h)`. Conclude with `h1 h`.

Introduce `h`. Conclude with `⟨fun i j hij => h i j (ne_of_gt hij), fun i j hij => h i j (ne_of_lt (show i < j from hij))⟩`.
-/
theorem mem_diagSub {g : GL (Fin n) L} : g ∈ diagSub ↔ IsDiagM g := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (show OrderDual.toDual j < OrderDual.toDual i from h)
    · exact h1 h
  · intro h
    exact ⟨fun i j hij => h i j (ne_of_gt hij), fun i j hij => h i j
      (ne_of_lt (show i < j from hij))⟩

section Top

variable [TopologicalSpace L]

/- English proof (translation)
The claim follows from `Units.continuous_val.matrix_elem i j`.
-/
theorem continuous_entry (i j : Fin n) :
    Continuous fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) i j :=
  Units.continuous_val.matrix_elem i j

variable [T2Space L]

/- English proof (translation)
Establish `: ((btSub b : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) = ⋂ (i : Fin n) (j : Fin n) (_ : b j < b i), {g : GL (Fin n) L | (g : Matrix (Fin n) (Fin n) L) i j = 0}`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩`. Rewrite using `[this]`.

Apply the tactic sequence `exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (continuous_entry i j) continuous_const`.
-/
theorem isClosed_btSub {α : Type} [LinearOrder α] (b : Fin n → α) :
    IsClosed ((btSub b : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
  have : ((btSub b : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) = ⋂ (i : Fin n) (j : Fin n) (_ : b j < b i),
      {g : GL (Fin n) L | (g : Matrix (Fin n) (Fin n) L) i j = 0} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_entry i j) continuous_const

/- English proof (translation)
Establish `: ((triSub b hb : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) = ((btSub b : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) ∩ ⋂ i : Fin n, {g : GL (Fin n) L | (g : Matrix (Fin n) (Fin n) L) i i = 1}`. Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `Iff.rfl`. Rewrite using `[this]`.

Apply the tactic sequence `exact (isClosed_btSub b).inter (isClosed_iInter fun i => isClosed_eq (continuous_entry i i) continuous_const)`.
-/
theorem isClosed_triSub {α : Type} [LinearOrder α] (b : Fin n → α) (hb : Function.Injective b) :
    IsClosed ((triSub b hb : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
  have : ((triSub b hb : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) = ((btSub b : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) ∩ ⋂ i : Fin n,
      {g : GL (Fin n) L | (g : Matrix (Fin n) (Fin n) L) i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [this]
  exact (isClosed_btSub b).inter (isClosed_iInter fun i =>
    isClosed_eq (continuous_entry i i) continuous_const)

end Top

end Tri

section Lat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def IsInt (m : Matrix (Fin n) (Fin n) L) : Prop := ∀ i j, Valued.v (m i j) ≤ 1

def IsIw (m : Matrix (Fin n) (Fin n) L) : Prop :=
  IsInt m ∧ ∀ i j, j < i → Valued.v (m i j) < 1

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latK {k : ℕ} {x : Fin n → L} : x ∈ latK L n k ↔
    ∀ i : Fin n, if i.val < k then Valued.v (x i) ≤ 1 else Valued.v (x i) < 1 := Iff.rfl

/- English proof (translation)
Use `hx j` as an intermediate fact. Use `split_ifs at this`. Conclude with `this`. Conclude with `this.le`.
-/
theorem le_one_of_mem_latK {k : ℕ} {x : Fin n → L} (hx : x ∈ latK L n k) (j : Fin n) :
    Valued.v (x j) ≤ 1 := by
  have := hx j
  split_ifs at this
  · exact this
  · exact this.le

/- English proof (translation)
Rewrite using `[mem_latK]`. Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `split_ifs with hi`. Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hm.1 i j) (le_one_of_mem_latK hx j)`. Use `Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Establish `hj` using `hx j`.

Use `split_ifs at hj with hjk`. Establish `hji : j < i`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le' (hm.2 i j hji) hj`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (hm.1 i j) zero_le' hj`.
-/
theorem isIw_mulVec {m : Matrix (Fin n) (Fin n) L} (hm : IsIw m) {k : ℕ} {x : Fin n → L}
    (hx : x ∈ latK L n k) : m *ᵥ x ∈ latK L n k := by
  rw [mem_latK]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  split_ifs with hi
  · refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hm.1 i j) (le_one_of_mem_latK hx j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    have hj := hx j
    split_ifs at hj with hjk
    · have hji : j < i := by
        rw [Fin.lt_def]; omega
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' (hm.2 i j hji) hj
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hm.1 i j) zero_le' hj

/- English proof (translation)
Rewrite using `[mem_latK]`. Introduce `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hj]`.

Apply the tactic sequence `rw [Pi.single_eq_of_ne hij] split_ifs <;> simp`.
-/
theorem single_mem_latK {k : ℕ} {j : Fin n} (hj : j.val < k) :
    (Pi.single j 1 : Fin n → L) ∈ latK L n k := by
  rw [mem_latK]
  intro i
  by_cases hij : i = j
  · subst hij
    simp [hj]
  · rw [Pi.single_eq_of_ne hij]
    split_ifs <;> simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i j`. Establish `h1` using `h (Fin.last n) _ (single_mem_latK (L := L) (k := n) (j := j) j.2) i`. Rewrite `h1` using `[Matrix.mulVec_single_one]`. Simplify `h1` using `[Matrix.col]`.

Introduce `i j hji`. Establish `hk : j.val + 1 < n + 1` using `by have := j.2; omega`. Establish `h1` using `h ⟨j.val + 1, hk⟩ _ (single_mem_latK (L := L) (k := j.val + 1) (j := j) (by omega)) i`. Rewrite `h1` using `[Matrix.mulVec_single_one]`. Establish `hi : ¬ i.val < j.val + 1`.

Establish `: j.val < i.val` using `hji`. Use linear arithmetic over natural numbers and integers. Simplify `h1` using `[Matrix.col, hi]`.
-/
theorem isIw_of_pres {m : Matrix (Fin n) (Fin n) L}
    (h : ∀ k : Fin (n + 1), ∀ x ∈ latK L n k, m *ᵥ x ∈ latK L n k) : IsIw m := by
  constructor
  · intro i j
    have h1 := h (Fin.last n) _ (single_mem_latK (L := L) (k := n) (j := j) j.2) i
    rw [Matrix.mulVec_single_one] at h1
    simpa [Matrix.col] using h1
  · intro i j hji
    have hk : j.val + 1 < n + 1 := by have := j.2; omega
    have h1 := h ⟨j.val + 1, hk⟩ _ (single_mem_latK (L := L) (k := j.val + 1) (j := j) (by omega)) i
    rw [Matrix.mulVec_single_one] at h1
    have hi : ¬ i.val < j.val + 1 := by
      have : j.val < i.val := hji
      omega
    simpa [Matrix.col, hi] using h1

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x conv_lhs => rw [← h]`. Conclude with `Set.smul_mem_smul_set_iff`. Introduce `h`.

Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, ← h, smul_inv_smul]`.
-/
theorem stab_iff {G X : Type*} [Group G] [MulAction G X] (f : G) (S : Set X) :
    f ∈ MulAction.stabilizer G S ↔ ∀ x, f • x ∈ S ↔ x ∈ S := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    conv_lhs => rw [← h]
    exact Set.smul_mem_smul_set_iff
  · intro h
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, ← h, smul_inv_smul]

/- English proof (translation)
Simplify using `only [IwGL, Subgroup.mem_iInf, Subgroup.mem_comap, stab_iff]`. Conclude with `Iff.rfl`.
-/
theorem mem_IwGL_iff_pres {g : GL (Fin n) L} : g ∈ IwGL L n ↔
    ∀ k : Fin (n + 1), ∀ x, (g : Matrix (Fin n) (Fin n) L) *ᵥ x ∈ latK L n k ↔ x ∈ latK L n k := by
  simp only [IwGL, Subgroup.mem_iInf, Subgroup.mem_comap, stab_iff]
  exact Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `(IwGL L n).inv_mem h`. Rewrite `h`, `h'` using `[mem_IwGL_iff_pres]`. Conclude with `⟨isIw_of_pres fun k x hx => (h k x).2 hx, isIw_of_pres fun k x hx => (h' k x).2 hx⟩`.

Introduce and unpack `⟨h1, h2⟩`. Rewrite using `[mem_IwGL_iff_pres]`. Introduce `k x`. Use `⟨fun hx => ?_, isIw_mulVec h1⟩` and prove the remaining obligations. Use `isIw_mulVec h2 hx` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem mem_IwGL_iff_isIw {g : GL (Fin n) L} : g ∈ IwGL L n ↔
    IsIw (g : Matrix (Fin n) (Fin n) L) ∧ IsIw ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  constructor
  · intro h
    have h' := (IwGL L n).inv_mem h
    rw [mem_IwGL_iff_pres] at h h'
    exact ⟨isIw_of_pres fun k x hx => (h k x).2 hx, isIw_of_pres fun k x hx => (h' k x).2 hx⟩
  · rintro ⟨h1, h2⟩
    rw [mem_IwGL_iff_pres]
    intro k x
    refine ⟨fun hx => ?_, isIw_mulVec h1⟩
    have := isIw_mulVec h2 hx
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

end Lat

end GlobalTheory.CompanionTheory.IwGLV

namespace GlobalTheory.CompanionTheory.IwGLV

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

variable (L) in

abbrev OL : ValuationSubring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring

variable (L n) in

abbrev iO : GL (Fin n) (OL L) →* GL (Fin n) L := Matrix.GeneralLinearGroup.map (OL L).subtype

/- English proof (translation)
The claim follows from `Matrix.GeneralLinearGroup.map_apply _ i j h`.
-/
theorem iO_apply (h : GL (Fin n) (OL L)) (i j : Fin n) :
    ((iO L n h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (((h : Matrix (Fin n) (Fin n) (OL L)) i j : OL L) : L) :=
  Matrix.GeneralLinearGroup.map_apply _ i j h

/- English proof (translation)
Set `a : Matrix (Fin n) (Fin n) (OL L)` to `fun i j => ⟨(g : Matrix (Fin n) (Fin n) L) i j, h1 i j⟩`. Set `b : Matrix (Fin n) (Fin n) (OL L)` to `fun i j => ⟨((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j, h2 i j⟩`. Establish `ha : (OL L).subtype.mapMatrix a = g` using `by ext i j; rfl`. Establish `hb : (OL L).subtype.mapMatrix b = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `inj : Function.Injective ((OL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (OL L) → Matrix (Fin n) (Fin n) L)` using `Matrix.map_injective Subtype.val_injective`. Establish `hab : a * b = 1` using `inj (by`. Rewrite using `[map_mul, map_one, ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one])`. Establish `hba : b * a = 1` using `inj (by`.

Rewrite using `[map_mul, map_one, ha, hb, ← Units.val_mul, inv_mul_cancel, Units.val_one])`. Use `⟨⟨a, b, hab, hba⟩, Units.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem exists_lift {g : GL (Fin n) L} (h1 : IsInt (g : Matrix (Fin n) (Fin n) L))
    (h2 : IsInt ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :
    ∃ g' : GL (Fin n) (OL L), iO L n g' = g := by
  let a : Matrix (Fin n) (Fin n) (OL L) := fun i j => ⟨(g : Matrix (Fin n) (Fin n) L) i j, h1 i j⟩
  let b : Matrix (Fin n) (Fin n) (OL L) := fun i j =>
    ⟨((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j, h2 i j⟩
  have ha : (OL L).subtype.mapMatrix a = g := by ext i j; rfl
  have hb : (OL L).subtype.mapMatrix b = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have inj : Function.Injective ((OL L).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (OL L) → Matrix (Fin n) (Fin n) L) :=
    Matrix.map_injective Subtype.val_injective
  have hab : a * b = 1 := inj (by
    rw [map_mul, map_one, ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hba : b * a = 1 := inj (by
    rw [map_mul, map_one, ha, hb, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨a, b, hab, hba⟩, Units.ext ?_⟩
  ext i j
  rfl

variable {ϖ : L}
  (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))

include hϖ

/- English proof (translation)
Rewrite using `[hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]`. Conclude with `Multiplicative.ofAdd_lt.2 (by norm_num)`.
-/
theorem v_pi_lt : Valued.v ϖ < 1 := by
  rw [hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]
  exact Multiplicative.ofAdd_lt.2 (by norm_num)

/- English proof (translation)
Rewrite using `[hϖ]`. Conclude with `WithZero.coe_ne_zero`.
-/
theorem v_pi_ne : Valued.v ϖ ≠ 0 := by
  rw [hϖ]; exact WithZero.coe_ne_zero

/- English proof (translation)
Rewrite using `[hϖ]`. Generalize the expression as in `Valued.v x = a at hx ⊢`. Proceed by induction on `a using WithZero.recZeroCoe with`. Consider the case `zero => exact zero_le'`. Consider the case `coe a`.

Rewrite using `[WithZero.coe_le_coe]`. Rewrite `hx` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Establish `h0 : Multiplicative.toAdd a < 0` using `hx`. Use `show Multiplicative.toAdd a ≤ -1`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_pi_of_lt_one {x : L} (hx : Valued.v x < 1) : Valued.v x ≤ Valued.v ϖ := by
  rw [hϖ]
  generalize Valued.v x = a at hx ⊢
  induction a using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [WithZero.coe_le_coe]
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hx
    have h0 : Multiplicative.toAdd a < 0 := hx
    show Multiplicative.toAdd a ≤ -1
    omega

def piO : OL L := ⟨ϖ, (v_pi_lt hϖ).le⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩ show Valued.v (ϖ * (c : L)) < 1`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le' (v_pi_lt hϖ) c.2`. Introduce `h`.

Establish `hv0` using `v_pi_ne hϖ`. Establish `h0 : ϖ ≠ 0` using `fun e => hv0 (by rw [e, map_zero])`. Use `⟨⟨ϖ⁻¹ * x, ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show Valued.v (ϖ⁻¹ * (x : L)) ≤ 1`. Rewrite using `[map_mul, map_inv₀]`.

Conclude with `(inv_mul_le_one₀ (zero_lt_iff.2 hv0)).2 (le_pi_of_lt_one hϖ h)`. Use `show (x : L) = ϖ * (ϖ⁻¹ * x)`. Clear the denominators using the available nonvanishing facts.
-/
theorem dvd_iff (x : OL L) : piO hϖ ∣ x ↔ Valued.v (x : L) < 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    show Valued.v (ϖ * (c : L)) < 1
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' (v_pi_lt hϖ) c.2
  · intro h
    have hv0 := v_pi_ne hϖ
    have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
    refine ⟨⟨ϖ⁻¹ * x, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v (ϖ⁻¹ * (x : L)) ≤ 1
      rw [map_mul, map_inv₀]
      exact (inv_mul_le_one₀ (zero_lt_iff.2 hv0)).2 (le_pi_of_lt_one hϖ h)
    · show (x : L) = ϖ * (ϖ⁻¹ * x)
      field_simp

/- English proof (translation)
Introduce `hu` and use `by have := (dvd_iff hϖ 1).1 (isUnit_iff_dvd_one.1 hu) simp at this`.
-/
theorem not_isUnit_piO : ¬ IsUnit (piO hϖ) := fun hu => by
  have := (dvd_iff hϖ 1).1 (isUnit_iff_dvd_one.1 hu)
  simp at this

/- English proof (translation)
Introduce `i j` and use `⟨fun _ => one_dvd _, fun hji => (dvd_iff hϖ _).2 (by have := h.2 i j hji rwa [iO_apply] at this)⟩`.
-/
theorem shape_of_isIw {g : GL (Fin n) (OL L)}
    (h : IsIw ((iO L n g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :
    Shape 1 (piO hϖ) (g : Matrix (Fin n) (Fin n) (OL L)) := fun i j =>
  ⟨fun _ => one_dvd _, fun hji => (dvd_iff hϖ _).2 (by
    have := h.2 i j hji
    rwa [iO_apply] at this)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => by rw [iO_apply]; exact ((g : Matrix (Fin n) (Fin n) (OL L)) i j).2, fun i j hji => by rw [iO_apply]; exact (dvd_iff hϖ _).1 ((hs i j).2 hji)⟩`.
-/
theorem isIw_of_shape {g : GL (Fin n) (OL L)}
    (hs : Shape 1 (piO hϖ) (g : Matrix (Fin n) (Fin n) (OL L))) :
    IsIw ((iO L n g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
  ⟨fun i j => by rw [iO_apply]; exact ((g : Matrix (Fin n) (Fin n) (OL L)) i j).2,
    fun i j hji => by rw [iO_apply]; exact (dvd_iff hϖ _).1 ((hs i j).2 hji)⟩

/- English proof (translation)
The claim follows from `mem_IwGL_iff_isIw.2 ⟨isIw_of_shape hϖ hs, by rw [← map_inv] exact isIw_of_shape hϖ (Shape.inv hs)⟩`.
-/
theorem iO_mem {g : GL (Fin n) (OL L)}
    (hs : Shape 1 (piO hϖ) (g : Matrix (Fin n) (Fin n) (OL L))) : iO L n g ∈ IwGL L n :=
  mem_IwGL_iff_isIw.2 ⟨isIw_of_shape hϖ hs, by
    rw [← map_inv]
    exact isIw_of_shape hϖ (Shape.inv hs)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨h1, h2⟩` from `mem_IwGL_iff_isIw.1 h`. Conclude with `⟨h1.1, h2.1, h1.2⟩`. Introduce and unpack `⟨h1, h2, h3⟩`.

Take `⟨g', rfl⟩` from `exists_lift h1 h2`. Conclude with `iO_mem hϖ (shape_of_isIw hϖ ⟨h1, h3⟩)`.
-/
theorem mem_IwGL_iff {g : GL (Fin n) L} : g ∈ IwGL L n ↔
    IsInt (g : Matrix (Fin n) (Fin n) L) ∧
      IsInt ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ∧
      ∀ i j : Fin n, j < i → Valued.v ((g : Matrix (Fin n) (Fin n) L) i j) < 1 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := mem_IwGL_iff_isIw.1 h
    exact ⟨h1.1, h2.1, h1.2⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨g', rfl⟩ := exists_lift h1 h2
    exact iO_mem hϖ (shape_of_isIw hϖ ⟨h1, h3⟩)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `(mem_IwGL_iff hϖ).1 hg`. Take `⟨g', rfl⟩` from `exists_lift h1 h2`. Conclude with `⟨g', rfl, shape_of_isIw hϖ ⟨h1, h3⟩⟩`.
-/
theorem exists_of_mem {g : GL (Fin n) L} (hg : g ∈ IwGL L n) :
    ∃ g' : GL (Fin n) (OL L), iO L n g' = g ∧
      Shape 1 (piO hϖ) (g' : Matrix (Fin n) (Fin n) (OL L)) := by
  obtain ⟨h1, h2, h3⟩ := (mem_IwGL_iff hϖ).1 hg
  obtain ⟨g', rfl⟩ := exists_lift h1 h2
  exact ⟨g', rfl, shape_of_isIw hϖ ⟨h1, h3⟩⟩

/- English proof (translation)
Take `⟨U, rfl⟩ : ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = u` from `⟨Matrix.nonsingInvUnit u (by rw [hu.det]; exact isUnit_one), rfl⟩`. Use `⟨U, rfl, iO_mem hϖ (hu.shape _), mem_upSub.2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[iO_apply, (hu i j).1 hji]`. Both sides reduce to the same expression. Rewrite using `[iO_apply, (hu i i).2.1 rfl]`.

Both sides reduce to the same expression.
-/
theorem up_fac {u : Matrix (Fin n) (Fin n) (OL L)} (hu : UpperUnip 1 u) :
    ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = u ∧
      iO L n U ∈ IwGL L n ⊓ upSub := by
  obtain ⟨U, rfl⟩ : ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = u :=
    ⟨Matrix.nonsingInvUnit u (by rw [hu.det]; exact isUnit_one), rfl⟩
  refine ⟨U, rfl, iO_mem hϖ (hu.shape _), mem_upSub.2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩
  · rw [iO_apply, (hu i j).1 hji]; rfl
  · rw [iO_apply, (hu i i).2.1 rfl]; rfl

/- English proof (translation)
Take `⟨U, rfl⟩ : ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = l` from `⟨Matrix.nonsingInvUnit l (by rw [hl.det]; exact isUnit_one), rfl⟩`. Use `⟨U, rfl, iO_mem hϖ (hl.shape _), mem_lowSub.2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[iO_apply, (hl i j).1 hji]`. Both sides reduce to the same expression. Rewrite using `[iO_apply, (hl i i).2.1 rfl]`.

Both sides reduce to the same expression.
-/
theorem low_fac {l : Matrix (Fin n) (Fin n) (OL L)} (hl : LowerUnip (piO hϖ) l) :
    ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = l ∧
      iO L n U ∈ IwGL L n ⊓ lowSub := by
  obtain ⟨U, rfl⟩ : ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = l :=
    ⟨Matrix.nonsingInvUnit l (by rw [hl.det]; exact isUnit_one), rfl⟩
  refine ⟨U, rfl, iO_mem hϖ (hl.shape _), mem_lowSub.2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩
  · rw [iO_apply, (hl i j).1 hji]; rfl
  · rw [iO_apply, (hl i i).2.1 rfl]; rfl

/- English proof (translation)
Take `⟨U, hU⟩ : ∃ U : GL (Fin n) (OL L), (U : Matrix (Fin n) (Fin n) (OL L)) = Matrix.diagonal (fun i => (d i : OL L))` from `⟨⟨Matrix.diagonal (fun i => (d i : OL L)), Matrix.diagonal (fun i => ((d i)⁻¹ : (OL L)ˣ)), by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩, rfl⟩`. Use `⟨U, hU, iO_mem hϖ ?_, mem_diagSub.2 fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hU]`. Conclude with `Shape.diagonal _ _ _`. Rewrite using `[iO_apply, hU, Matrix.diagonal_apply_ne _ hij]`.

Both sides reduce to the same expression.
-/
theorem diag_fac (d : Fin n → (OL L)ˣ) :
    ∃ U : GL (Fin n) (OL L),
      (U : Matrix (Fin n) (Fin n) (OL L)) = Matrix.diagonal (fun i => (d i : OL L)) ∧
      iO L n U ∈ IwGL L n ⊓ diagSub := by
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin n) (OL L),
      (U : Matrix (Fin n) (Fin n) (OL L)) = Matrix.diagonal (fun i => (d i : OL L)) :=
    ⟨⟨Matrix.diagonal (fun i => (d i : OL L)), Matrix.diagonal (fun i => ((d i)⁻¹ : (OL L)ˣ)),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩, rfl⟩
  refine ⟨U, hU, iO_mem hϖ ?_, mem_diagSub.2 fun i j hij => ?_⟩
  · rw [hU]; exact Shape.diagonal _ _ _
  · rw [iO_apply, hU, Matrix.diagonal_apply_ne _ hij]; rfl

/- English proof (translation)
Take `⟨x', rfl, hs⟩` from `exists_of_mem hϖ hx`. Take `⟨⟨u, d, l⟩, ⟨hu, hl, hf⟩, -⟩` from `existsUnique_factor (not_isUnit_piO hϖ) x' hs`. Take `⟨U, rfl, hU⟩` from `up_fac hϖ hu`. Take `⟨D, hD, hD'⟩` from `diag_fac hϖ d`. Take `⟨W, rfl, hW⟩` from `low_fac hϖ hl`.

Use `⟨_, hU, _, hD', _, hW, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, hD]`.

Conclude with `hf`.
-/
theorem fact_up {x : GL (Fin n) L} (hx : x ∈ IwGL L n) :
    ∃ c ∈ IwGL L n ⊓ upSub, ∃ b ∈ IwGL L n ⊓ diagSub, ∃ a ∈ IwGL L n ⊓ lowSub, x = c * b * a := by
  obtain ⟨x', rfl, hs⟩ := exists_of_mem hϖ hx
  obtain ⟨⟨u, d, l⟩, ⟨hu, hl, hf⟩, -⟩ := existsUnique_factor (not_isUnit_piO hϖ) x' hs
  obtain ⟨U, rfl, hU⟩ := up_fac hϖ hu
  obtain ⟨D, hD, hD'⟩ := diag_fac hϖ d
  obtain ⟨W, rfl, hW⟩ := low_fac hϖ hl
  refine ⟨_, hU, _, hD', _, hW, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD]
  exact hf

/- English proof (translation)
Take `⟨x', rfl, hs⟩` from `exists_of_mem hϖ hx`. Take `⟨⟨l, d, u⟩, ⟨hl, hu, hf⟩, -⟩` from `existsUnique_factor_opp (not_isUnit_piO hϖ) x' hs`. Take `⟨U, rfl, hU⟩` from `up_fac hϖ hu`. Take `⟨D, hD, hD'⟩` from `diag_fac hϖ d`. Take `⟨W, rfl, hW⟩` from `low_fac hϖ hl`.

Use `⟨_, hW, _, hD', _, hU, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, hD]`.

Conclude with `hf`.
-/
theorem fact_low {x : GL (Fin n) L} (hx : x ∈ IwGL L n) :
    ∃ a ∈ IwGL L n ⊓ lowSub, ∃ b ∈ IwGL L n ⊓ diagSub, ∃ c ∈ IwGL L n ⊓ upSub, x = a * b * c := by
  obtain ⟨x', rfl, hs⟩ := exists_of_mem hϖ hx
  obtain ⟨⟨l, d, u⟩, ⟨hl, hu, hf⟩, -⟩ := existsUnique_factor_opp (not_isUnit_piO hϖ) x' hs
  obtain ⟨U, rfl, hU⟩ := up_fac hϖ hu
  obtain ⟨D, hD, hD'⟩ := diag_fac hϖ d
  obtain ⟨W, rfl, hW⟩ := low_fac hϖ hl
  refine ⟨_, hW, _, hD', _, hU, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD]
  exact hf

end Int

section Top

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
The claim follows from `Valued.isOpen_integer L`.
-/
theorem isOpen_le : IsOpen {x : L | Valued.v x ≤ 1} := Valued.isOpen_integer L

/- English proof (translation)
Use `Valued.isOpen_ball L (Γ₀ := WithZero (Multiplicative ℤ)) 1` as an intermediate fact. Simplify using `using this`.
-/
theorem isOpen_lt : IsOpen {x : L | Valued.v x < 1} := by
  have := Valued.isOpen_ball L (Γ₀ := WithZero (Multiplicative ℤ)) 1
  simpa using this

/- English proof (translation)
Establish `: {g | IsInt (f g)} = ⋂ (i : Fin n) (j : Fin n), {g | Valued.v (f g i j) ≤ 1}`. Use extensionality with `g`. Simplify using `[IsInt]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_le.preimage (hf.matrix_elem i j)`.
-/
theorem isOpen_isInt_set (f : GL (Fin n) L → Matrix (Fin n) (Fin n) L) (hf : Continuous f) :
    IsOpen {g | IsInt (f g)} := by
  have : {g | IsInt (f g)} = ⋂ (i : Fin n) (j : Fin n), {g | Valued.v (f g i j) ≤ 1} := by
    ext g; simp [IsInt]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_le.preimage (hf.matrix_elem i j)

/- English proof (translation)
Establish `: {g | IsIw (f g)} = {g | IsInt (f g)} ∩ ⋂ (i : Fin n) (j : Fin n) (_ : j < i), {g | Valued.v (f g i j) < 1}`. Use extensionality with `g`. Simplify using `[IsIw]`. Rewrite using `[this]`. Conclude with `(isOpen_isInt_set f hf).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isOpen_lt.preimage (hf.matrix_elem i j))`.
-/
theorem isOpen_isIw_set (f : GL (Fin n) L → Matrix (Fin n) (Fin n) L) (hf : Continuous f) :
    IsOpen {g | IsIw (f g)} := by
  have : {g | IsIw (f g)} = {g | IsInt (f g)} ∩
      ⋂ (i : Fin n) (j : Fin n) (_ : j < i), {g | Valued.v (f g i j) < 1} := by
    ext g; simp [IsIw]
  rw [this]
  exact (isOpen_isInt_set f hf).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt.preimage (hf.matrix_elem i j))

/- English proof (translation)
Establish `: ((IwGL L n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) = {g : GL (Fin n) L | IsIw (g : Matrix (Fin n) (Fin n) L)} ∩ {g : GL (Fin n) L | IsIw ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)}`. Use extensionality with `g`. Conclude with `mem_IwGL_iff_isIw`. Rewrite using `[this]`. Conclude with `(isOpen_isIw_set _ Units.continuous_val).inter (isOpen_isIw_set _ (Units.continuous_val.comp continuous_inv))`.
-/
theorem isOpen_IwGL : IsOpen ((IwGL L n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
  have : ((IwGL L n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) =
      {g : GL (Fin n) L | IsIw (g : Matrix (Fin n) (Fin n) L)} ∩
        {g : GL (Fin n) L | IsIw ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)} := by
    ext g; exact mem_IwGL_iff_isIw
  rw [this]
  exact (isOpen_isIw_set _ Units.continuous_val).inter
    (isOpen_isIw_set _ (Units.continuous_val.comp continuous_inv))

/- English proof (translation)
Take `⟨-, hv, -, hϖ, -, hq, hcard⟩` from `h`. Use `haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩`. Use `letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne := Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)`. Establish `hp` using `(Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing, Nat.finite_of_card_ne_zero (by`. Use `ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩` and prove the remaining obligations.

Conclude with `isCompact_iff_compactSpace.2 hp`.
-/
theorem isCompact_le [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact {x : L | Valued.v x ≤ 1} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero,
      by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  exact isCompact_iff_compactSpace.2 hp

/- English proof (translation)
Establish `hc` using `isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => isCompact_le h`. Establish `: {m : Matrix (Fin n) (Fin n) L | IsInt m} = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : L | Valued.v x ≤ 1}`. Use extensionality with `m`. Conclude with `⟨fun hm i _ j _ => hm i j, fun hm i j => hm i trivial j trivial⟩`. Rewrite using `[this]`.

Conclude with `hc`.
-/
theorem isCompact_isInt [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact {m : Matrix (Fin n) (Fin n) L | IsInt m} := by
  have hc := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => isCompact_le h
  have : {m : Matrix (Fin n) (Fin n) L | IsInt m} = Set.univ.pi fun _ : Fin n => Set.univ.pi
      fun _ : Fin n => {x : L | Valued.v x ≤ 1} := by
    ext m
    exact ⟨fun hm i _ j _ => hm i j, fun hm i j => hm i trivial j trivial⟩
  rw [this]
  exact hc

/- English proof (translation)
Establish `hK` using `isCompact_isInt (n := n) h`. Establish `hK' : IsCompact (MulOpposite.unop ⁻¹' {m : Matrix (Fin n) (Fin n) L | IsInt m})` using `(MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) L)).symm.isCompact_preimage.2 hK`. Establish `hc` using `Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) L) |>.isCompact_preimage (hK.prod hK')`. Use `hc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_IwGL) ?_` and prove the remaining obligations. Introduce `g hg`.

Take `⟨h1, h2⟩` from `mem_IwGL_iff_isIw.1 hg`. Conclude with `⟨h1.1, h2.1⟩`.
-/
theorem isCompact_IwGL [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact ((IwGL L n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
  have hK := isCompact_isInt (n := n) h
  have hK' : IsCompact (MulOpposite.unop ⁻¹' {m : Matrix (Fin n) (Fin n) L | IsInt m}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) L)).symm.isCompact_preimage.2 hK
  have hc := Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) L) |>.isCompact_preimage (hK.prod hK')
  refine hc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_IwGL) ?_
  intro g hg
  obtain ⟨h1, h2⟩ := mem_IwGL_iff_isIw.1 hg
  exact ⟨h1.1, h2.1⟩

/- English proof (translation)
Use `Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem hb ht hh, fun hh => ?_⟩` and prove the remaining obligations. Use `conj_mem hb ((btSub b).inv_mem ht) hh` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
theorem norm_tri {α : Type} [LinearOrder α] {b : Fin n → α} (hb : Function.Injective b)
    {t : GL (Fin n) L} (ht : t ∈ btSub b) :
    t ∈ Subgroup.normalizer ((triSub b hb : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem hb ht hh, fun hh => ?_⟩
  have := conj_mem hb ((btSub b).inv_mem ht) hh
  simpa [mul_assoc] using this

end Top

end GlobalTheory.CompanionTheory.IwGLV
