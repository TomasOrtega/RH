import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerLast

noncomputable section

open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix

namespace GlobalTheory.CompanionTheory.BLevel

section Entries

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}

def IsInt (A : Matrix (Fin m) (Fin m) L) : Prop := ∀ i j, ‖A i j‖ ≤ 1

def IsNear (r : ℝ) (A : Matrix (Fin m) (Fin m) L) : Prop := ∀ i j, ‖(A - 1) i j‖ ≤ r

/- English proof (translation)
Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`.
-/
theorem norm_one_entry (i j : Fin m) : ‖(1 : Matrix (Fin m) (Fin m) L) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) ha`.
-/
theorem norm_mul_entry {A B : Matrix (Fin m) (Fin m) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin m) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => ?_
  rw [norm_mul]; exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) ha

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Simplify using `using mul_le_mul (hB i k) (hv k) (norm_nonneg _) hr`.
-/
theorem norm_mulVec_entry {B : Matrix (Fin m) (Fin m) L} {v : Fin m → L} {r : ℝ} (hr : 0 ≤ r)
    (hB : ∀ i j, ‖B i j‖ ≤ r) (hv : ∀ j, ‖v j‖ ≤ 1) (i : Fin m) : ‖(B *ᵥ v) i‖ ≤ r := by
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun k _ => ?_
  rw [norm_mul]; simpa using mul_le_mul (hB i k) (hv k) (norm_nonneg _) hr

/- English proof (translation)
Introduce `i j` and use `by have e : A i j = (A - 1) i j + (1 : Matrix (Fin m) (Fin m) L) i j := by simp rw [e] exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((h i j).trans hr) (norm_one_entry i j))`.
-/
theorem IsNear.isInt {r : ℝ} {A : Matrix (Fin m) (Fin m) L} (hr : r ≤ 1) (h : IsNear r A) : IsInt A := fun i j => by
  have e : A i j = (A - 1) i j + (1 : Matrix (Fin m) (Fin m) L) i j := by simp
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((h i j).trans hr) (norm_one_entry i j))

/- English proof (translation)
Introduce `i j` and use `by simpa using norm_mul_entry zero_le_one zero_le_one hA hB i j`.
-/
theorem IsInt.mul {A B : Matrix (Fin m) (Fin m) L} (hA : IsInt A) (hB : IsInt B) : IsInt (A * B) := fun i j => by
  simpa using norm_mul_entry zero_le_one zero_le_one hA hB i j

/- English proof (translation)
The claim follows from `norm_one_entry`.
-/
theorem isInt_one : IsInt (1 : Matrix (Fin m) (Fin m) L) := norm_one_entry

/- English proof (translation)
Establish `e : A * B - 1 = (A - 1) * B + (B - 1)` using `by rw [sub_mul]; simp`. Introduce `i j`. Rewrite using `[e, Matrix.add_apply]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))` and prove the remaining obligations. Apply the tactic sequence `simpa using norm_mul_entry h0 zero_le_one hA (hB.isInt hr) i j`.
-/
theorem IsNear.mul {r : ℝ} {A B : Matrix (Fin m) (Fin m) L} (h0 : 0 ≤ r) (hr : r ≤ 1) (hA : IsNear r A)
    (hB : IsNear r B) : IsNear r (A * B) := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by rw [sub_mul]; simp
  intro i j
  rw [e, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  simpa using norm_mul_entry h0 zero_le_one hA (hB.isInt hr) i j

/- English proof (translation)
Introduce `i j` and use `by simpa using h0`.
-/
theorem isNear_one {r : ℝ} (h0 : 0 ≤ r) : IsNear r (1 : Matrix (Fin m) (Fin m) L) := fun i j => by simpa using h0

/- English proof (translation)
Establish `e : B - 1 = -(B * (A - 1))` using `by rw [mul_sub, hBA]; simp`. Establish `key : ∀ c : ℝ, 0 ≤ c → (∀ i j, ‖B i j‖ ≤ c) → ∀ i j, ‖(B - 1) i j‖ ≤ c * r` using `fun c hc hB i j => by`. Rewrite using `[e, Matrix.neg_apply, norm_neg]`. Apply the tactic sequence `exact norm_mul_entry hc h0 hB hA i j`. Establish `hint : ∀ i j, ‖B i j‖ ≤ 1`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨i₀, j₀, h1⟩` from `hcon`. Use `haveI : Nonempty (Fin m × Fin m) := ⟨(i₀, j₀)⟩`. Take `⟨p, hp⟩` from `Finite.exists_max fun p : Fin m × Fin m => ‖B p.1 p.2‖`.

Establish `hc : 1 < ‖B p.1 p.2‖` using `h1.trans_le (hp (i₀, j₀))`. Establish `h2` using `key _ (norm_nonneg _) (fun i j => hp (i, j)) p.1 p.2`. Establish `h3 : B p.1 p.2 = (B - 1) p.1 p.2 + (1 : Matrix (Fin m) (Fin m) L) p.1 p.2` using `by simp`. Establish `h4` using `IsUltrametricDist.norm_add_le_max ((B - 1) p.1 p.2) ((1 : Matrix (Fin m) (Fin m) L) p.1 p.2)`. Rewrite `h4` using `[← h3]`.

Break down `le_max_iff.1 h4 with h | h` into its components or cases. Use the polynomial consequences of the given equalities and inequalities. Apply the tactic sequence `linarith [norm_one_entry (L := L) p.1 p.2]`. Introduce `i j`. Simplify using `using key 1 zero_le_one hint i j`.
-/
theorem IsNear.inv {r : ℝ} {A B : Matrix (Fin m) (Fin m) L} (h0 : 0 ≤ r) (hr : r < 1) (hA : IsNear r A)
    (hBA : B * A = 1) : IsNear r B := by
  have e : B - 1 = -(B * (A - 1)) := by rw [mul_sub, hBA]; simp
  have key : ∀ c : ℝ, 0 ≤ c → (∀ i j, ‖B i j‖ ≤ c) → ∀ i j, ‖(B - 1) i j‖ ≤ c * r := fun c hc hB i j => by
    rw [e, Matrix.neg_apply, norm_neg]; exact norm_mul_entry hc h0 hB hA i j
  have hint : ∀ i j, ‖B i j‖ ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₀, j₀, h1⟩ := hcon
    haveI : Nonempty (Fin m × Fin m) := ⟨(i₀, j₀)⟩
    obtain ⟨p, hp⟩ := Finite.exists_max fun p : Fin m × Fin m => ‖B p.1 p.2‖
    have hc : 1 < ‖B p.1 p.2‖ := h1.trans_le (hp (i₀, j₀))
    have h2 := key _ (norm_nonneg _) (fun i j => hp (i, j)) p.1 p.2
    have h3 : B p.1 p.2 = (B - 1) p.1 p.2 + (1 : Matrix (Fin m) (Fin m) L) p.1 p.2 := by simp
    have h4 := IsUltrametricDist.norm_add_le_max ((B - 1) p.1 p.2) ((1 : Matrix (Fin m) (Fin m) L) p.1 p.2)
    rw [← h3] at h4
    rcases le_max_iff.1 h4 with h | h
    · nlinarith
    · linarith [norm_one_entry (L := L) p.1 p.2]
  intro i j
  simpa using key 1 zero_le_one hint i j

/- English proof (translation)
Establish `e : C * K * D - 1 = C * (K - 1) * D`. Rewrite using `[mul_sub, sub_mul, mul_one, hCD]`. Introduce `i j`. Rewrite using `[e]`. Apply the tactic sequence `simpa using norm_mul_entry (mul_nonneg zero_le_one h0) zero_le_one (norm_mul_entry zero_le_one h0 hC hK) hD i j`.
-/
theorem IsNear.conj {r : ℝ} {C D K : Matrix (Fin m) (Fin m) L} (h0 : 0 ≤ r) (hC : IsInt C) (hD : IsInt D)
    (hCD : C * D = 1) (hK : IsNear r K) : IsNear r (C * K * D) := by
  have e : C * K * D - 1 = C * (K - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  intro i j
  rw [e]
  simpa using norm_mul_entry (mul_nonneg zero_le_one h0) zero_le_one (norm_mul_entry zero_le_one h0 hC hK) hD i j

def congS (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : Subgroup (GL (Fin m) L) where
  carrier := {g | IsNear r g.1}
  mul_mem' := fun ha hb => IsNear.mul h0 h1.le ha hb
  one_mem' := isNear_one h0
  inv_mem' := fun {g} hg => IsNear.inv h0 h1 hg g.inv_mul

def intS : Subgroup (GL (Fin m) L) where
  carrier := {g | IsInt g.1 ∧ IsInt (g⁻¹).1}
  mul_mem' := fun {a b} ha hb => ⟨IsInt.mul ha.1 hb.1, by rw [mul_inv_rev]; exact IsInt.mul hb.2 ha.2⟩
  one_mem' := by simpa using isInt_one
  inv_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_intS {g : GL (Fin m) L} : g ∈ intS ↔ IsInt g.1 ∧ IsInt (g⁻¹).1 := Iff.rfl

/- English proof (translation)
Introduce `g hg` and use `⟨IsNear.isInt h1.le hg, IsNear.isInt h1.le ((congS r h0 h1).inv_mem hg)⟩`.
-/
theorem congS_le_intS {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : congS (L := L) (m := m) r h0 h1 ≤ intS := fun g hg =>
  ⟨IsNear.isInt h1.le hg, IsNear.isInt h1.le ((congS r h0 h1).inv_mem hg)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hk`. Conclude with `IsNear.conj h0 hc.1 hc.2 c.mul_inv hk`. Introduce `hk`. Use `IsNear.conj h0 hc.2 (by simpa using hc.1) (by simp) hk` as an intermediate fact.

Establish `e : (c⁻¹).1 * (c * k * c⁻¹).1 * c.1 = k.1`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem congS_conj {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) {c : GL (Fin m) L} (hc : c ∈ intS) (k : GL (Fin m) L) :
    k ∈ congS r h0 h1 ↔ c * k * c⁻¹ ∈ congS r h0 h1 := by
  constructor
  · intro hk
    exact IsNear.conj h0 hc.1 hc.2 c.mul_inv hk
  · intro hk
    have := IsNear.conj h0 hc.2 (by simpa using hc.1) (by simp) hk
    have e : (c⁻¹).1 * (c * k * c⁻¹).1 * c.1 = k.1 := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    rwa [e] at this

end Entries

section Top

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}

/- English proof (translation)
Establish `e : {A : Matrix (Fin m) (Fin m) L | IsNear r A} = ⋂ i, ⋂ j, (fun A : Matrix (Fin m) (Fin m) L => A i j) ⁻¹' Metric.closedBall ((1 : Matrix (Fin m) (Fin m) L) i j) r`. Use extensionality with `A`. Simplify using `[IsNear, dist_eq_norm]`. Establish `h2 : IsOpen {A : Matrix (Fin m) (Fin m) L | IsNear r A}`. Rewrite using `[e]`.

Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (continuous_id.matrix_elem i j)`. Conclude with `h2.preimage Units.continuous_val`.
-/
theorem isOpen_near {r : ℝ} (hr : 0 < r) : IsOpen {g : GL (Fin m) L | IsNear r g.1} := by
  have e : {A : Matrix (Fin m) (Fin m) L | IsNear r A} = ⋂ i, ⋂ j, (fun A : Matrix (Fin m) (Fin m) L => A i j) ⁻¹'
      Metric.closedBall ((1 : Matrix (Fin m) (Fin m) L) i j) r := by
    ext A; simp [IsNear, dist_eq_norm]
  have h2 : IsOpen {A : Matrix (Fin m) (Fin m) L | IsNear r A} := by
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (continuous_id.matrix_elem i j)
  exact h2.preimage Units.continuous_val

/- English proof (translation)
Take `⟨ε, hε, h⟩` from `Metric.mem_nhds_iff.1 hA`. Use `⟨ε / 2, half_pos hε, fun B hB => h (Metric.mem_ball.2 ?_)⟩` and prove the remaining obligations. Use `(dist_pi_lt_iff hε).2 fun i => (dist_pi_lt_iff hε).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`. Conclude with `(hB i j).trans_lt (half_lt_self hε)`.
-/
theorem exists_near_of_mem_nhds {c : Fin m → Fin m → L} {A : Set (Fin m → Fin m → L)} (hA : A ∈ 𝓝 c) :
    ∃ ε > 0, ∀ B : Fin m → Fin m → L, (∀ i j, ‖B i j - c i j‖ ≤ ε) → B ∈ A := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun B hB => h (Metric.mem_ball.2 ?_)⟩
  refine (dist_pi_lt_iff hε).2 fun i => (dist_pi_lt_iff hε).2 fun j => ?_
  rw [dist_eq_norm]; exact (hB i j).trans_lt (half_lt_self hε)

/- English proof (translation)
Rewrite `hW` using `[Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨t, ht, hsub⟩` from `hW`. Establish `ht' : t ∈ 𝓝 ((1 : Matrix (Fin m) (Fin m) L), MulOpposite.op (1 : Matrix (Fin m) (Fin m) L))`. Simplify using `using ht`. Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.1 ht'`.

Establish `hv' : MulOpposite.op ⁻¹' v ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) L)` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hv`. Take `⟨ε, hε, h⟩` from `exists_near_of_mem_nhds (L := L) (m := m) (c := (1 : Matrix (Fin m) (Fin m) L)) (A := u ∩ MulOpposite.op ⁻¹' v) (Filter.inter_mem hu hv')`. Take `⟨π, hπ0, hπ⟩` from `NormedField.exists_norm_lt L (lt_min hε one_pos)`. Establish `hπ1 : ‖π‖ < 1` using `hπ.trans_le (min_le_right _ _)`. Establish `hπε : ‖π‖ ≤ ε` using `(hπ.trans_le (min_le_left _ _)).le`.

Use `⟨π, norm_pos_iff.1 hπ0, hπ1, fun g hg => hsub ?_⟩` and prove the remaining obligations. Establish `hg' : IsNear ‖π‖ (g⁻¹).1` using `(congS ‖π‖ (norm_nonneg _) hπ1).inv_mem (show g ∈ congS ‖π‖ (norm_nonneg _) hπ1 from hg)`. Apply `huv` to reduce the goal to its premises. Conclude with `⟨(h g.1 fun i j => (hg i j).trans hπε).1, (h (g⁻¹).1 fun i j => (hg' i j).trans hπε).2⟩`.
-/
theorem exists_level {W : Set (GL (Fin m) L)} (hW : W ∈ 𝓝 (1 : GL (Fin m) L)) :
    ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : GL (Fin m) L, IsNear ‖π‖ g.1 → g ∈ W := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨t, ht, hsub⟩ := hW
  have ht' : t ∈ 𝓝 ((1 : Matrix (Fin m) (Fin m) L), MulOpposite.op (1 : Matrix (Fin m) (Fin m) L)) := by
    simpa using ht
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht'
  have hv' : MulOpposite.op ⁻¹' v ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hv
  obtain ⟨ε, hε, h⟩ := exists_near_of_mem_nhds (L := L) (m := m) (c := (1 : Matrix (Fin m) (Fin m) L))
    (A := u ∩ MulOpposite.op ⁻¹' v) (Filter.inter_mem hu hv')
  obtain ⟨π, hπ0, hπ⟩ := NormedField.exists_norm_lt L (lt_min hε one_pos)
  have hπ1 : ‖π‖ < 1 := hπ.trans_le (min_le_right _ _)
  have hπε : ‖π‖ ≤ ε := (hπ.trans_le (min_le_left _ _)).le
  refine ⟨π, norm_pos_iff.1 hπ0, hπ1, fun g hg => hsub ?_⟩
  have hg' : IsNear ‖π‖ (g⁻¹).1 := (congS ‖π‖ (norm_nonneg _) hπ1).inv_mem (show g ∈ congS ‖π‖ (norm_nonneg _) hπ1 from hg)
  apply huv
  exact ⟨(h g.1 fun i j => (hg i j).trans hπε).1, (h (g⁻¹).1 fun i j => (hg' i j).trans hπε).2⟩

variable [ProperSpace L]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf31.isCompact_box c r`.
-/
theorem isCompact_box (c : Matrix (Fin m) (Fin m) L) (r : ℝ) :
    IsCompact {g : GL (Fin m) L | (∀ i j, ‖g.1 i j - c i j‖ ≤ r) ∧ ∀ i j, ‖(g⁻¹).1 i j - c i j‖ ≤ r} :=
  _root_.UpperTheory.Reformulated.B.Qf31.isCompact_box c r

/- English proof (translation)
Use `isCompact_box (L := L) (m := m) 0 1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `[mem_intS, IsInt]`.
-/
theorem isCompact_intS : IsCompact ((intS : Subgroup (GL (Fin m) L)) : Set (GL (Fin m) L)) := by
  convert isCompact_box (L := L) (m := m) 0 1 using 1
  ext g
  simp [mem_intS, IsInt]

/- English proof (translation)
Use `isCompact_box (L := L) (m := m) 1 r using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Conclude with `⟨hg, (congS r h0 h1).inv_mem hg⟩`.

Introduce `hg`. Conclude with `hg.1`.
-/
theorem isCompact_congS {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : IsCompact ((congS r h0 h1 : Subgroup (GL (Fin m) L)) : Set (GL (Fin m) L)) := by
  convert isCompact_box (L := L) (m := m) 1 r using 1
  ext g
  constructor
  · intro hg
    exact ⟨hg, (congS r h0 h1).inv_mem hg⟩
  · intro hg
    exact hg.1

end Top

section Conj

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n m : ℕ}
  (b : Module.Basis (Fin m) L (Fin n → L))

def conj : Matrix (Fin n) (Fin n) L ≃ₐ[L] Matrix (Fin m) (Fin m) L :=
  Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[conj, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]`.
-/
theorem conj_eq (A : Matrix (Fin n) (Fin n) L) : conj b A = LinearMap.toMatrix b b (Matrix.toLin' A) := by
  ext i j
  simp [conj, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

/- English proof (translation)
Simplify using `[conj_eq, LinearMap.toMatrix_apply]`.
-/
theorem conj_apply (A : Matrix (Fin n) (Fin n) L) (i j : Fin m) : conj b A i j = b.repr (A *ᵥ b j) i := by
  simp [conj_eq, LinearMap.toMatrix_apply]

/- English proof (translation)
Rewrite using `[conj_eq, LinearMap.toMatrix_mulVec_repr]`. Simplify using the standard rewrite rules.
-/
theorem repr_mulVec (A : Matrix (Fin n) (Fin n) L) (x : Fin n → L) : ⇑(b.repr (A *ᵥ x)) = conj b A *ᵥ ⇑(b.repr x) := by
  rw [conj_eq, LinearMap.toMatrix_mulVec_repr]; simp

variable {b} {Λ : AddSubgroup (Fin n → L)}

/- English proof (translation)
The claim follows from `(hΛ _).2 fun i => by simp only [Module.Basis.repr_self, Finsupp.single_apply] split_ifs <;> simp`.
-/
theorem basis_mem (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) (j : Fin m) : b j ∈ Λ :=
  (hΛ _).2 fun i => by
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h x hx => (hΛ _).2 fun i => by rw [repr_mulVec]; exact norm_mulVec_entry zero_le_one h ((hΛ x).1 hx) i, fun h i j => by rw [conj_apply]; exact (hΛ _).1 (h _ (basis_mem hΛ j)) i⟩`.
-/
theorem isInt_conj_iff (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) (A : Matrix (Fin n) (Fin n) L) :
    IsInt (conj b A) ↔ ∀ x ∈ Λ, A *ᵥ x ∈ Λ :=
  ⟨fun h x hx => (hΛ _).2 fun i => by
      rw [repr_mulVec]; exact norm_mulVec_entry zero_le_one h ((hΛ x).1 hx) i,
    fun h i j => by rw [conj_apply]; exact (hΛ _).1 (h _ (basis_mem hΛ j)) i⟩

/- English proof (translation)
Establish `e : conj b A - 1 = conj b (A - 1)` using `by simp`. Establish `e2 : ∀ x : Fin n → L, (A - 1) *ᵥ x = A *ᵥ x - x` using `fun x => by simp [Matrix.sub_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Use `⟨π⁻¹ • (A *ᵥ x - x), (hΛ _).2 fun i => ?_, by rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]⟩` and prove the remaining obligations.

Rewrite using `[← e2, map_smul, Finsupp.smul_apply, repr_mulVec, smul_eq_mul, norm_mul, norm_inv, ← e, inv_mul_le_iff₀ (norm_pos_iff.2 hπ)]`. Apply the tactic sequence `simpa using norm_mulVec_entry (norm_nonneg π) h ((hΛ x).1 hx) i`. Introduce `h i j`. Take `⟨y, hy, e3⟩` from `h _ (basis_mem hΛ j)`. Rewrite using `[e, conj_apply, e2, e3, map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]`.

Simplify using `using mul_le_mul_of_nonneg_left ((hΛ y).1 hy i) (norm_nonneg π)`.
-/
theorem isNear_conj_iff (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : π ≠ 0)
    (A : Matrix (Fin n) (Fin n) L) :
    IsNear ‖π‖ (conj b A) ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, A *ᵥ x - x = π • y := by
  have e : conj b A - 1 = conj b (A - 1) := by simp
  have e2 : ∀ x : Fin n → L, (A - 1) *ᵥ x = A *ᵥ x - x := fun x => by simp [Matrix.sub_mulVec]
  constructor
  · intro h x hx
    refine ⟨π⁻¹ • (A *ᵥ x - x), (hΛ _).2 fun i => ?_, by rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]⟩
    rw [← e2, map_smul, Finsupp.smul_apply, repr_mulVec, smul_eq_mul, norm_mul, norm_inv, ← e,
      inv_mul_le_iff₀ (norm_pos_iff.2 hπ)]
    simpa using norm_mulVec_entry (norm_nonneg π) h ((hΛ x).1 hx) i
  · intro h i j
    obtain ⟨y, hy, e3⟩ := h _ (basis_mem hΛ j)
    rw [e, conj_apply, e2, e3, map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
    simpa using mul_le_mul_of_nonneg_left ((hΛ y).1 hy i) (norm_nonneg π)

variable (b)

def phi : GL (Fin n) L ≃* GL (Fin m) L := Units.mapEquiv (conj b).toMulEquiv

variable [ProperSpace L]

/- English proof (translation)
The claim follows from `LinearMap.continuous_of_finiteDimensional (conj b).toLinearMap`.
-/
theorem continuous_conj : Continuous (conj b) :=
  LinearMap.continuous_of_finiteDimensional (conj b).toLinearMap

/- English proof (translation)
The claim follows from `LinearMap.continuous_of_finiteDimensional (conj b).symm.toLinearMap`.
-/
theorem continuous_conj_symm : Continuous (conj b).symm :=
  LinearMap.continuous_of_finiteDimensional (conj b).symm.toLinearMap

def phiHomeo : GL (Fin n) L ≃ₜ GL (Fin m) L where
  toEquiv := (phi b).toEquiv
  continuous_toFun := Continuous.units_map (conj b).toMulEquiv.toMonoidHom (continuous_conj b)
  continuous_invFun := Continuous.units_map (conj b).toMulEquiv.symm.toMonoidHom (continuous_conj_symm b)

end Conj

/- English proof (translation)
Establish `hc : Continuous s` using `(AddMonoidHomClass.isometry_of_norm s hs).continuous`. Establish `e : (UG s J : Set (GL (Fin n) L)) = {g | (g.1.map s).transpose * J * g.1 = J}` using `rfl`. Rewrite using `[e]`. Conclude with `isClosed_eq (((Units.continuous_val.matrix_map hc).matrix_transpose.matrix_mul continuous_const).matrix_mul Units.continuous_val) continuous_const`.
-/
theorem isClosed_UG {L : Type} [NontriviallyNormedField L] (s : L →+* L) (hs : ∀ x, ‖s x‖ = ‖x‖) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) : IsClosed (UG s J : Set (GL (Fin n) L)) := by
  have hc : Continuous s := (AddMonoidHomClass.isometry_of_norm s hs).continuous
  have e : (UG s J : Set (GL (Fin n) L)) = {g | (g.1.map s).transpose * J * g.1 = J} := rfl
  rw [e]
  exact isClosed_eq (((Units.continuous_val.matrix_map hc).matrix_transpose.matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const

/- English proof (translation)
Introduce `L _ _ _ s hs n J Λ hL`. Take `⟨m, b, hΛ⟩` from `hL`. Set `ψ : UG s J →* GL (Fin m) L` to `(phi b).toMonoidHom.comp (UG s J).subtype`. Establish `hψ : IsClosedEmbedding ψ` using `(phiHomeo b).isClosedEmbedding.comp (isClosed_UG s hs J).isClosedEmbedding_subtypeVal`. Establish `hv : ∀ g : UG s J, (ψ g).1 = conj b g.1.1` using `fun _ => rfl`.

Establish `hi : ∀ g : UG s J, ((ψ g)⁻¹).1 = conj b (g.1⁻¹).1` using `fun g => by`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Use `⟨fun π hπ0 hπ1 => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Establish `hn : 0 ≤ ‖π‖` using `norm_nonneg π`.

Use `⟨(congS ‖π‖ hn hπ1).comap ψ, intS.comap ψ, fun g => ?_, fun g => ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isNear_conj_iff hΛ hπ0 g.1.1`. Rewrite using `[Subgroup.mem_comap, mem_intS, hv, hi, isInt_conj_iff hΛ, isInt_conj_iff hΛ]`. Establish `e1 : ∀ x, (g.1⁻¹).1 *ᵥ (g.1.1 *ᵥ x) = x` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Establish `e2 : ∀ x, g.1.1 *ᵥ ((g.1⁻¹).1 *ᵥ x) = x` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ x`. Use `⟨fun hx => ?_, h1 x⟩` and prove the remaining obligations.

Simplify `h2 _ hx` using `only [e1]`. Introduce `h`. Conclude with `⟨fun x hx => (h x).2 hx, fun x hx => (h _).1 (by simpa only [e2] using hx)⟩`. Conclude with `(isOpen_near (norm_pos_iff.2 hπ0)).preimage hψ.continuous`. Conclude with `hψ.isCompact_preimage (isCompact_congS hn hπ1)`.

Conclude with `hψ.isCompact_preimage isCompact_intS`. Conclude with `Subgroup.comap_mono (congS_le_intS hn hπ1)`. Introduce `c hc k show ψ k ∈ congS ‖π‖ hn hπ1 ↔ ψ (c * k * c⁻¹) ∈ congS ‖π‖ hn hπ1`. Rewrite using `[map_mul, map_mul, map_inv]`. Conclude with `congS_conj hn hπ1 hc _`.

Establish `hU1` using `hU.mem_nhds (one_mem U)`. Rewrite `hU1` using `[hψ.isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨W, hW, hsub⟩` from `hU1`. Rewrite `hW` using `[map_one]`. Take `⟨π, h0, h1, h⟩` from `exists_level hW`.

Conclude with `⟨π, h0, h1, fun g hg => hsub (h _ ((isNear_conj_iff hΛ h0 _).2 hg))⟩`.
-/
theorem main : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L), (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)), IsLat L Λ → (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J), (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧ (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧ IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧ ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧ ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U := by
  intro L _ _ _ s hs n J Λ hL
  obtain ⟨m, b, hΛ⟩ := hL
  let ψ : UG s J →* GL (Fin m) L := (phi b).toMonoidHom.comp (UG s J).subtype
  have hψ : IsClosedEmbedding ψ :=
    (phiHomeo b).isClosedEmbedding.comp (isClosed_UG s hs J).isClosedEmbedding_subtypeVal
  have hv : ∀ g : UG s J, (ψ g).1 = conj b g.1.1 := fun _ => rfl
  have hi : ∀ g : UG s J, ((ψ g)⁻¹).1 = conj b (g.1⁻¹).1 := fun g => by
    rw [← map_inv]; rfl
  refine ⟨fun π hπ0 hπ1 => ?_, fun U hU => ?_⟩
  · have hn : 0 ≤ ‖π‖ := norm_nonneg π
    refine ⟨(congS ‖π‖ hn hπ1).comap ψ, intS.comap ψ, fun g => ?_, fun g => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isNear_conj_iff hΛ hπ0 g.1.1
    · rw [Subgroup.mem_comap, mem_intS, hv, hi, isInt_conj_iff hΛ, isInt_conj_iff hΛ]
      have e1 : ∀ x, (g.1⁻¹).1 *ᵥ (g.1.1 *ᵥ x) = x := fun x => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have e2 : ∀ x, g.1.1 *ᵥ ((g.1⁻¹).1 *ᵥ x) = x := fun x => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      constructor
      · rintro ⟨h1, h2⟩ x
        refine ⟨fun hx => ?_, h1 x⟩
        simpa only [e1] using h2 _ hx
      · intro h
        exact ⟨fun x hx => (h x).2 hx, fun x hx => (h _).1 (by simpa only [e2] using hx)⟩
    · exact (isOpen_near (norm_pos_iff.2 hπ0)).preimage hψ.continuous
    · exact hψ.isCompact_preimage (isCompact_congS hn hπ1)
    · exact hψ.isCompact_preimage isCompact_intS
    · exact Subgroup.comap_mono (congS_le_intS hn hπ1)
    · intro c hc k
      show ψ k ∈ congS ‖π‖ hn hπ1 ↔ ψ (c * k * c⁻¹) ∈ congS ‖π‖ hn hπ1
      rw [map_mul, map_mul, map_inv]
      exact congS_conj hn hπ1 hc _
  · have hU1 := hU.mem_nhds (one_mem U)
    rw [hψ.isInducing.nhds_eq_comap, Filter.mem_comap] at hU1
    obtain ⟨W, hW, hsub⟩ := hU1
    rw [map_one] at hW
    obtain ⟨π, h0, h1, h⟩ := exists_level hW
    exact ⟨π, h0, h1, fun g hg => hsub (h _ ((isNear_conj_iff hΛ h0 _).2 hg))⟩

end GlobalTheory.CompanionTheory.BLevel

end
