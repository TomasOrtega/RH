import Formalism.DoubleCosetMeasures.StatementV

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix

namespace Formalism.DoubleCosetMeasures.P.Vol

section PartA

section Alg

variable {F : Type} [Field F]

def piece (O : Subring F) (ϖ : F) {n a : ℕ} (r : Matrix (Fin n) (Fin a) F) :
    Set (Matrix (Fin n) (Fin a) F) :=
  (fun h => -r + h) ⁻¹' IIset O ϖ

/- English proof (translation)
Simplify using `only [piece, Set.mem_preimage, IIset, Set.mem_setOf_eq, Matrix.add_apply, Matrix.neg_apply, neg_add_eq_sub, Matrix.sub_apply]`.
-/
theorem mem_piece {O : Subring F} {ϖ : F} {n a : ℕ} {r y : Matrix (Fin n) (Fin a) F} :
    y ∈ piece O ϖ r ↔ ∀ i j, ∃ o ∈ O, y i j - r i j = ϖ * o := by
  simp only [piece, Set.mem_preimage, IIset, Set.mem_setOf_eq, Matrix.add_apply,
    Matrix.neg_apply, neg_add_eq_sub, Matrix.sub_apply]

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [IIset, Set.mem_setOf_eq]`. Use `forall₂_congr fun i j => ⟨?_, fun h => ⟨_, h, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨o, ho, e⟩`. Rewrite using `[e, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]`.

Conclude with `ho`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]`.
-/
theorem iiset_eq (O : Subring F) (ϖ : F) (hϖ0 : ϖ ≠ 0) {n a : ℕ} :
    (IIset O ϖ : Set (Matrix (Fin n) (Fin a) F)) = {y | ∀ i j, ϖ⁻¹ * y i j ∈ O} := by
  ext y
  simp only [IIset, Set.mem_setOf_eq]
  refine forall₂_congr fun i j => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
  · rintro ⟨o, ho, e⟩
    rw [e, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
    exact ho
  · rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, e⟩`. Use `⟨⟨o, ho⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show o * ϖ = x - y`.

Rewrite using `[e, mul_comm]`. Introduce and unpack `⟨c, hc⟩`. Use `⟨c, c.2, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val hc`. Express the relevant statement in the definitionally equal form `(c : F) * ϖ = x - y at h1`.

Rewrite using `[← h1, mul_comm]`.
-/
theorem sub_mem_iff {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {x y : F} (hx : x ∈ O) (hy : y ∈ O) :
    (∃ o ∈ O, x - y = ϖ * o) ↔
      (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨x, hx⟩ =
        Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨y, hy⟩) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨o, ho, e⟩
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    show o * ϖ = x - y
    rw [e, mul_comm]
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have h1 := congrArg Subtype.val hc
    change (c : F) * ϖ = x - y at h1
    rw [← h1, mul_comm]

end Alg

end PartA

section PartB

variable {F : Type} [Field F]

/- English proof (translation)
Set `P : O` to `⟨ϖ, hϖ⟩`. Set `W : Matrix (Fin a) (Fin a) O` to `fun i j => ⟨w i j, hw i j⟩`. Set `A : Matrix (Fin a) (Fin a) O` to `1 + P • W`. Establish `hA : O.subtype.mapMatrix A = 1 + ϖ • w`. Use extensionality with `i j`.

Use `show (((1 + P • W : Matrix (Fin a) (Fin a) O) i j : O) : F) = (1 + ϖ • w) i j`. Rewrite using `[Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Subring.coe_add, Subring.coe_mul]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h, P, W]`. Establish `hdet : (1 + ϖ • w).det = ((A.det : O) : F)`. Rewrite using `[← hA, ← RingHom.map_det]`.

Both sides reduce to the same expression. Set `q` to `Ideal.Quotient.mk (Ideal.span {P})`. Establish `hqP : q P = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)`. Establish `hqA : q.mapMatrix A = 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [A, hqP, Matrix.one_apply, h, Matrix.smul_apply, Pi.smul_apply]`. Establish `hq : q A.det = q 1` using `by rw [RingHom.map_det, hqA, Matrix.det_one, map_one]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hq)`. Establish `hc'` using `congrArg Subtype.val hc`. Express the relevant statement in the definitionally equal form `(c : F) * ϖ = (A.det : F) - 1 at hc'`.

Establish `hdF : (1 + ϖ • w).det = 1 + ϖ * c`. Rewrite using `[hdet]`. Take the linear combination `-hc'`. Establish `hdO : (1 + ϖ • w).det ∈ O`. Rewrite using `[hdF]`.

Conclude with `O.add_mem O.one_mem (O.mul_mem hϖ c.2)`. Establish `hdnot : ∀ o ∈ O, (1 + ϖ • w).det ≠ ϖ * o`. Introduce `o ho h`. Apply `hloc.1` to reduce the goal to its premises. Rewrite `h` using `[hdF]`.

Establish `h1 : ϖ * (o - c) = 1` using `by linear_combination -h`. Rewrite using `[inv_eq_of_mul_eq_one_right h1]`. Conclude with `O.sub_mem ho c.2`. Establish `hd0 : (1 + ϖ • w).det ≠ 0` using `fun h => hdnot 0 O.zero_mem (by rw [h, mul_zero])`. Establish `hdinv : ((1 + ϖ • w).det)⁻¹ ∈ O` using `hloc.2 _ hdO hdnot`.

Establish `hadj : (1 + ϖ • w).adjugate = O.subtype.mapMatrix A.adjugate`. Rewrite using `[← hA, RingHom.map_adjugate]`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + ϖ • w) hd0, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce `i j show (1 + ϖ • w) i j ∈ O`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Use `O.add_mem ?_ (O.mul_mem hϖ (hw i j))` and prove the remaining obligations. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h, O.one_mem, O.zero_mem]`. Introduce `i j`. Rewrite using `[Matrix.coe_units_inv]`. Use `show (1 + ϖ • w)⁻¹ i j ∈ O`.

Rewrite using `[Matrix.inv_def, hadj, Ring.inverse_eq_inv']`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `O.mul_mem hdinv (A.adjugate i j).2`. Introduce `i j show (ϖ⁻¹ • ((1 + ϖ • w) - 1)) i j ∈ O`. Rewrite using `[add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hϖ0, one_smul]`.

Conclude with `hw i j`.
-/
theorem one_add_mem_cong (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} (w : Matrix (Fin a) (Fin a) F) (hw : IsInt O w) :
    ∃ k : GL (Fin a) F, k ∈ congSub O ϖ a ∧
      (k : Matrix (Fin a) (Fin a) F) = 1 + ϖ • w := by
  classical
  let P : O := ⟨ϖ, hϖ⟩
  let W : Matrix (Fin a) (Fin a) O := fun i j => ⟨w i j, hw i j⟩
  let A : Matrix (Fin a) (Fin a) O := 1 + P • W
  have hA : O.subtype.mapMatrix A = 1 + ϖ • w := by
    ext i j
    show (((1 + P • W : Matrix (Fin a) (Fin a) O) i j : O) : F) = (1 + ϖ • w) i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul, Subring.coe_add, Subring.coe_mul]
    by_cases h : i = j <;> simp [Matrix.one_apply, h, P, W]
  have hdet : (1 + ϖ • w).det = ((A.det : O) : F) := by
    rw [← hA, ← RingHom.map_det]
    rfl
  let q := Ideal.Quotient.mk (Ideal.span {P})
  have hqP : q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hqA : q.mapMatrix A = 1 := by
    ext i j
    by_cases h : i = j <;> simp [A, hqP, Matrix.one_apply, h, Matrix.smul_apply, Pi.smul_apply]
  have hq : q A.det = q 1 := by rw [RingHom.map_det, hqA, Matrix.det_one, map_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hq)
  have hc' := congrArg Subtype.val hc
  change (c : F) * ϖ = (A.det : F) - 1 at hc'
  have hdF : (1 + ϖ • w).det = 1 + ϖ * c := by
    rw [hdet]
    linear_combination -hc'
  have hdO : (1 + ϖ • w).det ∈ O := by
    rw [hdF]
    exact O.add_mem O.one_mem (O.mul_mem hϖ c.2)
  have hdnot : ∀ o ∈ O, (1 + ϖ • w).det ≠ ϖ * o := by
    intro o ho h
    apply hloc.1
    rw [hdF] at h
    have h1 : ϖ * (o - c) = 1 := by linear_combination -h
    rw [inv_eq_of_mul_eq_one_right h1]
    exact O.sub_mem ho c.2
  have hd0 : (1 + ϖ • w).det ≠ 0 := fun h => hdnot 0 O.zero_mem (by rw [h, mul_zero])
  have hdinv : ((1 + ϖ • w).det)⁻¹ ∈ O := hloc.2 _ hdO hdnot
  have hadj : (1 + ϖ • w).adjugate = O.subtype.mapMatrix A.adjugate := by
    rw [← hA, RingHom.map_adjugate]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + ϖ • w) hd0, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
  · intro i j
    show (1 + ϖ • w) i j ∈ O
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine O.add_mem ?_ (O.mul_mem hϖ (hw i j))
    by_cases h : i = j <;> simp [Matrix.one_apply, h, O.one_mem, O.zero_mem]
  · intro i j
    rw [Matrix.coe_units_inv]
    show (1 + ϖ • w)⁻¹ i j ∈ O
    rw [Matrix.inv_def, hadj, Ring.inverse_eq_inv']
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact O.mul_mem hdinv (A.adjugate i j).2
  · intro i j
    show (ϖ⁻¹ • ((1 + ϖ • w) - 1)) i j ∈ O
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hϖ0, one_smul]
    exact hw i j

/- English proof (translation)
Establish `hgI : IsInt O (g : Matrix (Fin a) (Fin a) F)` using `hg.1`. Establish `hk1 : IsInt O (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1))` using `hk.2`. Rewrite using `[mem_piece]`. Introduce `i j`. Use `⟨((g : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1))) i j, isInt_mul' O hgI hk1 i j, ?_⟩` and prove the remaining obligations.

Establish `e : ((g * k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - g = ϖ • ((g : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1)))`. Rewrite using `[Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hϖ0, one_smul, Matrix.mul_sub, Matrix.mul_one, Units.val_mul]`. Establish `h1` using `congrFun (congrFun e i) j`. Simplify `h1` using `[Matrix.sub_apply, Matrix.smul_apply]`.
-/
theorem mul_cong_mem_piece (O : Subring F) (ϖ : F) (hϖ0 : ϖ ≠ 0) {a : ℕ} {g k : GL (Fin a) F}
    (hg : g ∈ GLint O a) (hk : k ∈ congSub O ϖ a) :
    (((g * k : GL (Fin a) F)) : Matrix (Fin a) (Fin a) F) ∈
      piece O ϖ (g : Matrix (Fin a) (Fin a) F) := by
  have hgI : IsInt O (g : Matrix (Fin a) (Fin a) F) := hg.1
  have hk1 : IsInt O (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1)) := hk.2
  rw [mem_piece]
  intro i j
  refine ⟨((g : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1))) i j,
    isInt_mul' O hgI hk1 i j, ?_⟩
  have e : ((g * k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - g =
      ϖ • ((g : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1))) := by
    rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hϖ0, one_smul, Matrix.mul_sub,
      Matrix.mul_one, Units.val_mul]
  have h1 := congrFun (congrFun e i) j
  simpa [Matrix.sub_apply, Matrix.smul_apply] using h1

/- English proof (translation)
Rewrite `hm` using `[mem_piece]`. Use `choose o ho hmo using hm`. Establish `hY : IsInt O (Matrix.of o)` using `fun i j => ho i j`. Establish `hgi : IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)` using `hg.2`. Take `⟨k, hk, hkw⟩` from `one_add_mem_cong O ϖ hϖ hϖ0 hloc _ (isInt_mul' O hgi hY)`.

Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, hkw, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]`. Take the linear combination `-(hmo i j)`.
-/
theorem piece_sub_mul_cong (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} {g : GL (Fin a) F} (hg : g ∈ GLint O a)
    {m : Matrix (Fin a) (Fin a) F} (hm : m ∈ piece O ϖ (g : Matrix (Fin a) (Fin a) F)) :
    ∃ k ∈ congSub O ϖ a, (((g * k : GL (Fin a) F)) : Matrix (Fin a) (Fin a) F) = m := by
  rw [mem_piece] at hm
  choose o ho hmo using hm
  have hY : IsInt O (Matrix.of o) := fun i j => ho i j
  have hgi : IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := hg.2
  obtain ⟨k, hk, hkw⟩ := one_add_mem_cong O ϖ hϖ hϖ0 hloc _ (isInt_mul' O hgi hY)
  refine ⟨k, hk, ?_⟩
  rw [Units.val_mul, hkw, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination -(hmo i j)

end PartB

section PartC

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]

/- English proof (translation)
Rewrite using `[iiset_eq O ϖ hϖ0]`. Establish `hOm : MeasurableSet (O : Set F)` using `hO.measurableSet`. Establish `e : {y : Matrix (Fin n) (Fin a) F | ∀ i j, ϖ⁻¹ * y i j ∈ O} = ⋂ i, ⋂ j, (fun y : Matrix (Fin n) (Fin a) F => ϖ⁻¹ * y i j) ⁻¹' (O : Set F)`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Use `MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_` and prove the remaining obligations. Conclude with `((continuous_mul_left ϖ⁻¹).measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))) hOm`.
-/
theorem meas_ii (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ0 : ϖ ≠ 0) (n a : ℕ) :
    MeasurableSet (IIset O ϖ : Set (Matrix (Fin n) (Fin a) F)) := by
  rw [iiset_eq O ϖ hϖ0]
  have hOm : MeasurableSet (O : Set F) := hO.measurableSet
  have e : {y : Matrix (Fin n) (Fin a) F | ∀ i j, ϖ⁻¹ * y i j ∈ O} =
      ⋂ i, ⋂ j, (fun y : Matrix (Fin n) (Fin a) F => ϖ⁻¹ * y i j) ⁻¹' (O : Set F) := by
    ext y
    simp
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  exact ((continuous_mul_left ϖ⁻¹).measurable.comp
    ((measurable_pi_apply j).comp (measurable_pi_apply i))) hOm

/- English proof (translation)
Conclude with `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ((continuous_const.add continuous_id).measurable (f := fun t : F => x i j + t)).comp ((measurable_pi_apply j).comp (measurable_pi_apply i))`.
-/
theorem meas_add (n a : ℕ) (x : Matrix (Fin n) (Fin a) F) :
    Measurable (fun y : Matrix (Fin n) (Fin a) F => x + y) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((continuous_const.add continuous_id).measurable (f := fun t : F => x i j + t)).comp
      ((measurable_pi_apply j).comp (measurable_pi_apply i))

/- English proof (translation)
Use `⟨fun x => meas_add n a x, fun x => ?_⟩` and prove the remaining obligations. Conclude with `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ((continuous_id.add continuous_const).measurable (f := fun t : F => t + x i j)).comp ((measurable_pi_apply j).comp (measurable_pi_apply i))`.
-/
theorem measurableAdd_mat (n a : ℕ) : MeasurableAdd (Matrix (Fin n) (Fin a) F) := by
  refine ⟨fun x => meas_add n a x, fun x => ?_⟩
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((continuous_id.add continuous_const).measurable (f := fun t : F => t + x i j)).comp
      ((measurable_pi_apply j).comp (measurable_pi_apply i))

/- English proof (translation)
The claim follows from `(meas_add n a (-r)) (meas_ii O hO ϖ hϖ0 n a)`.
-/
theorem meas_piece (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ0 : ϖ ≠ 0) {n a : ℕ}
    (r : Matrix (Fin n) (Fin a) F) : MeasurableSet (piece O ϖ r) :=
  (meas_add n a (-r)) (meas_ii O hO ϖ hϖ0 n a)

/- English proof (translation)
Use `haveI := measurableAdd_mat (F := F) n a`. Unfold `piece`. Conclude with `measure_preimage_add ν (-r) _`.
-/
theorem measure_piece {n a : ℕ} (ν : Measure (Matrix (Fin n) (Fin a) F)) [ν.IsAddLeftInvariant]
    (O : Subring F) (ϖ : F) (r : Matrix (Fin n) (Fin a) F) :
    ν (piece O ϖ r) = ν (IIset O ϖ) := by
  haveI := measurableAdd_mat (F := F) n a
  unfold piece
  exact measure_preimage_add ν (-r) _

def repM (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) {n a : ℕ} (c : Fin n → Fin a → kF O ϖ hϖ) :
    Matrix (Fin n) (Fin a) F :=
  fun i j => ((Quotient.out (c i j) : O) : F)

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [intMat, Set.mem_setOf_eq, Set.mem_iUnion, mem_piece]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨fun i j => Ideal.Quotient.mk _ ⟨y i j, hy i j⟩, fun i j => ?_⟩` and prove the remaining obligations.

Use `show ∃ o ∈ O, y i j - ((Quotient.out (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨y i j, hy i j⟩) : O) : F) = ϖ * o`. Rewrite using `[sub_mem_iff hϖ (hy i j) (Quotient.out (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨y i j, hy i j⟩)).2, Subtype.coe_eta, Ideal.Quotient.mk_out]`. Introduce and unpack `⟨c, hc⟩ i j`. Take `⟨o, ho, e⟩` from `hc i j`. Establish `h1 : y i j = repM O ϖ hϖ c i j + ϖ * o` using `by rw [← e]; ring`.

Rewrite using `[h1]`. Conclude with `O.add_mem (Quotient.out (c i j)).2 (O.mul_mem hϖ ho)`.
-/
theorem intMat_eq_iUnion (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (n a : ℕ) :
    intMat O n a = ⋃ c : Fin n → Fin a → kF O ϖ hϖ, piece O ϖ (repM O ϖ hϖ c) := by
  ext y
  simp only [intMat, Set.mem_setOf_eq, Set.mem_iUnion, mem_piece]
  constructor
  · intro hy
    refine ⟨fun i j => Ideal.Quotient.mk _ ⟨y i j, hy i j⟩, fun i j => ?_⟩
    show ∃ o ∈ O, y i j - ((Quotient.out (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
      ⟨y i j, hy i j⟩) : O) : F) = ϖ * o
    rw [sub_mem_iff hϖ (hy i j) (Quotient.out (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
      ⟨y i j, hy i j⟩)).2, Subtype.coe_eta, Ideal.Quotient.mk_out]
  · rintro ⟨c, hc⟩ i j
    obtain ⟨o, ho, e⟩ := hc i j
    have h1 : y i j = repM O ϖ hϖ c i j + ϖ * o := by rw [← e]; ring
    rw [h1]
    exact O.add_mem (Quotient.out (c i j)).2 (O.mul_mem hϖ ho)

/- English proof (translation)
Introduce `c c' hne`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `y h1 h2`. Apply `hne` to reduce the goal to its premises. Rewrite `h1`, `h2` using `[mem_piece]`.

Use function extensionality and compare the values at `i j`. Take `⟨o, ho, e⟩` from `h1 i j`. Take `⟨o', ho', e'⟩` from `h2 i j`. Simplify using `only [repM] at e e'`. Establish `key : ∃ o ∈ O, ((Quotient.out (c' i j) : O) : F) - ((Quotient.out (c i j) : O) : F) = ϖ * o` using `⟨o - o', O.sub_mem ho ho', by linear_combination e - e'⟩`.

Rewrite `key` using `[sub_mem_iff hϖ (Quotient.out (c' i j)).2 (Quotient.out (c i j)).2, Subtype.coe_eta, Subtype.coe_eta, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]`. Conclude with `key.symm`.
-/
theorem piece_disjoint (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (n a : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun c : Fin n → Fin a → kF O ϖ hϖ => piece O ϖ (repM O ϖ hϖ c))) := by
  intro c c' hne
  rw [Function.onFun, Set.disjoint_left]
  intro y h1 h2
  apply hne
  rw [mem_piece] at h1 h2
  funext i j
  obtain ⟨o, ho, e⟩ := h1 i j
  obtain ⟨o', ho', e'⟩ := h2 i j
  simp only [repM] at e e'
  have key : ∃ o ∈ O, ((Quotient.out (c' i j) : O) : F) - ((Quotient.out (c i j) : O) : F) =
      ϖ * o := ⟨o - o', O.sub_mem ho ho', by linear_combination e - e'⟩
  rw [sub_mem_iff hϖ (Quotient.out (c' i j)).2 (Quotient.out (c i j)).2, Subtype.coe_eta, Subtype.coe_eta,
    Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at key
  exact key.symm

/- English proof (translation)
Use `haveI : Fintype (kF O ϖ hϖ) := Fintype.ofFinite _`. Rewrite using `[intMat_eq_iUnion O ϖ hϖ n a, measure_iUnion (piece_disjoint O ϖ hϖ n a) (fun c => meas_piece O hO ϖ hϖ0 _), tsum_fintype]`. Simplify using `only [measure_piece]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.card_eq_fintype_card]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem measure_uniformizerMatrixSet_mul_card (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    [Finite (kF O ϖ hϖ)] (n a : ℕ) (ν : Measure (Matrix (Fin n) (Fin a) F))
    [ν.IsAddLeftInvariant] :
    ν (IIset O ϖ) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (n * a) = ν (intMat O n a) := by
  classical
  haveI : Fintype (kF O ϖ hϖ) := Fintype.ofFinite _
  rw [intMat_eq_iUnion O ϖ hϖ n a,
    measure_iUnion (piece_disjoint O ϖ hϖ n a) (fun c => meas_piece O hO ϖ hϖ0 _), tsum_fintype]
  simp only [measure_piece]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.card_eq_fintype_card]
  push_cast
  ring

end PartC

section PartD

section J

variable {F : Type} [Field F]

/- English proof (translation)
Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Take `⟨k, hk, hkv⟩` from `piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hJ u.2) h`. Establish `h1 : (u : GL (Fin a) F) * k = v` using `Units.ext hkv`. Establish `hk' : k = (u : GL (Fin a) F)⁻¹ * v` using `by rw [← h1, inv_mul_cancel_left]`. Rewrite `hk` using `[hk']`.

Simplify using `using hk`.
-/
theorem coset_eq_of_mem_piece (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} {J' : Subgroup (GL (Fin a) F)} (hJ : J' ≤ GLint O a)
    (u v : J')
    (h : ((v : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∈
      piece O ϖ ((u : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)) :
    (u : J' ⧸ (congSub O ϖ a).subgroupOf J') = (v : J' ⧸ (congSub O ϖ a).subgroupOf J') := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  obtain ⟨k, hk, hkv⟩ := piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hJ u.2) h
  have h1 : (u : GL (Fin a) F) * k = v := Units.ext hkv
  have hk' : k = (u : GL (Fin a) F)⁻¹ * v := by rw [← h1, inv_mul_cancel_left]
  rw [hk'] at hk
  simpa using hk

variable [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Use `haveI := measurableAdd_mat (F := F) a a`. Use `haveI : Fintype (kF O ϖ hϖ) := Fintype.ofFinite _`. Use `set K := (congSub O ϖ a).subgroupOf J' with hKdef`. Establish `hoI : ∀ q : J' ⧸ K, ((Quotient.out q : J') : GL (Fin a) F) ∈ GLint O a` using `fun q => hJ (Quotient.out q).2`. Establish `hcos : ∀ q q' : J' ⧸ K, (((Quotient.out q' : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∈ piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) → q = q'`.

Introduce `q q' h`. Establish `h1` using `coset_eq_of_mem_piece O ϖ hϖ hϖ0 hloc hJ _ _ h`. Rewrite `h1` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis. Establish `hfinQ : Finite (J' ⧸ K)`. Set `f : J' ⧸ K → Fin a → Fin a → kF O ϖ hϖ` to `fun q i j => Ideal.Quotient.mk _ ⟨(((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j, (hoI q).1 i j⟩`.

Use `Finite.of_injective f ?_` and prove the remaining obligations. Introduce `q q' hqq`. Apply `hcos` to reduce the goal to its premises. Rewrite using `[mem_piece]`. Introduce `i j`.

Conclude with `(sub_mem_iff hϖ _ _).mpr (congrFun (congrFun hqq i) j).symm`. Use `haveI : Fintype (J' ⧸ K) := Fintype.ofFinite _`. Establish `hU : Jset J' = ⋃ q : J' ⧸ K, piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)`. Use extensionality with `m`. Simplify using `only [Jset, Set.mem_image, Set.mem_iUnion, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj, rfl⟩`. Use `⟨((⟨j, hj⟩ : J') : J' ⧸ K), ?_⟩` and prove the remaining obligations. Establish `hq : ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : J' ⧸ K) = ((⟨j, hj⟩ : J') : J' ⧸ K)` using `QuotientGroup.out_eq' _`. Rewrite `hq` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Establish `e : ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F) * (((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)⁻¹ * j) = j` using `mul_inv_cancel_left _ _`. Establish `h1` using `mul_cong_mem_piece O ϖ hϖ0 (hoI _) (g := ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)) (k := ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)⁻¹ * j) (by simpa using hq)`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Introduce and unpack `⟨q, hm⟩`. Take `⟨k, hk, hkm⟩` from `piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hoI q) hm`.

Conclude with `⟨_, J'.mul_mem (Quotient.out q).2 (hK hk), hkm⟩`. Establish `hdisj : Pairwise (Function.onFun Disjoint (fun q : J' ⧸ K => piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)))`. Introduce `q q' hne`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `y h1 h2`.

Apply `hne` to reduce the goal to its premises. Apply `hcos` to reduce the goal to its premises. Rewrite `h1`, `h2`, the goal using `[mem_piece]`. Introduce `i j`. Take `⟨o, ho, e⟩` from `h1 i j`.

Take `⟨o', ho', e'⟩` from `h2 i j`. Conclude with `⟨o - o', O.sub_mem ho ho', by linear_combination e - e'⟩`. Establish `hJ' : ν (Jset J') = (Nat.card (J' ⧸ K) : ENNReal) * ν (IIset O ϖ)`. Rewrite using `[hU, measure_iUnion hdisj (fun q => meas_piece O hO ϖ hϖ0 _), tsum_fintype]`. Simplify using `only [measure_piece]`.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`. Rewrite using `[hJ', mul_assoc, measure_uniformizerMatrixSet_mul_card O hO ϖ hϖ hϖ0 a a ν]`.
-/
theorem measure_subgroupMatrixSet_mul_card (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O)
    (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (a : ℕ)
    (ν : Measure (Matrix (Fin a) (Fin a) F)) [ν.IsAddLeftInvariant]
    (J' : Subgroup (GL (Fin a) F)) (hK : congSub O ϖ a ≤ J') (hJ : J' ≤ GLint O a) :
    ν (Jset J') * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (a * a) =
      (Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') : ENNReal) * ν (intMat O a a) := by
  classical
  haveI := measurableAdd_mat (F := F) a a
  haveI : Fintype (kF O ϖ hϖ) := Fintype.ofFinite _
  set K := (congSub O ϖ a).subgroupOf J' with hKdef
  have hoI : ∀ q : J' ⧸ K, ((Quotient.out q : J') : GL (Fin a) F) ∈ GLint O a :=
    fun q => hJ (Quotient.out q).2
  have hcos : ∀ q q' : J' ⧸ K,
      (((Quotient.out q' : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∈
        piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) → q = q' := by
    intro q q' h
    have h1 := coset_eq_of_mem_piece O ϖ hϖ hϖ0 hloc hJ _ _ h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
  have hfinQ : Finite (J' ⧸ K) := by
    let f : J' ⧸ K → Fin a → Fin a → kF O ϖ hϖ := fun q i j =>
      Ideal.Quotient.mk _
        ⟨(((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j, (hoI q).1 i j⟩
    refine Finite.of_injective f ?_
    intro q q' hqq
    apply hcos
    rw [mem_piece]
    intro i j
    exact (sub_mem_iff hϖ _ _).mpr (congrFun (congrFun hqq i) j).symm
  haveI : Fintype (J' ⧸ K) := Fintype.ofFinite _
  have hU : Jset J' = ⋃ q : J' ⧸ K,
      piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := by
    ext m
    simp only [Jset, Set.mem_image, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨((⟨j, hj⟩ : J') : J' ⧸ K), ?_⟩
      have hq : ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : J' ⧸ K) =
          ((⟨j, hj⟩ : J') : J' ⧸ K) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have e : ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F) *
          (((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)⁻¹ * j) = j :=
        mul_inv_cancel_left _ _
      have h1 := mul_cong_mem_piece O ϖ hϖ0 (hoI _)
        (g := ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F))
        (k := ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)⁻¹ * j)
        (by simpa using hq)
      rwa [e] at h1
    · rintro ⟨q, hm⟩
      obtain ⟨k, hk, hkm⟩ := piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hoI q) hm
      exact ⟨_, J'.mul_mem (Quotient.out q).2 (hK hk), hkm⟩
  have hdisj : Pairwise (Function.onFun Disjoint (fun q : J' ⧸ K =>
      piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F))) := by
    intro q q' hne
    rw [Function.onFun, Set.disjoint_left]
    intro y h1 h2
    apply hne
    apply hcos
    rw [mem_piece] at h1 h2 ⊢
    intro i j
    obtain ⟨o, ho, e⟩ := h1 i j
    obtain ⟨o', ho', e'⟩ := h2 i j
    exact ⟨o - o', O.sub_mem ho ho', by linear_combination e - e'⟩
  have hJ' : ν (Jset J') = (Nat.card (J' ⧸ K) : ENNReal) * ν (IIset O ϖ) := by
    rw [hU, measure_iUnion hdisj (fun q => meas_piece O hO ϖ hϖ0 _), tsum_fintype]
    simp only [measure_piece]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hJ', mul_assoc, measure_uniformizerMatrixSet_mul_card O hO ϖ hϖ hϖ0 a a ν]

end J

end PartD

end Formalism.DoubleCosetMeasures.P.Vol

namespace Formalism.DoubleCosetMeasures.P

/- English proof (translation)
Introduce `F _ _ _ _ _ O hO ϖ hϖ hϖ0 hfin n a ν _`. Use `haveI := hfin`. Conclude with `Vol.measure_uniformizerMatrixSet_mul_card O hO ϖ hϖ hϖ0 n a ν`.
-/
theorem volII : Formalism.DoubleCosetMeasures.VolII := by
  intro F _ _ _ _ _ O hO ϖ hϖ hϖ0 hfin n a ν _
  haveI := hfin
  exact Vol.measure_uniformizerMatrixSet_mul_card O hO ϖ hϖ hϖ0 n a ν

/- English proof (translation)
Introduce `F _ _ _ _ _ O hO ϖ hϖ hϖ0 hloc hfin a ν _ J' hK hJ`. Use `haveI := hfin`. Conclude with `Vol.measure_subgroupMatrixSet_mul_card O hO ϖ hϖ hϖ0 hloc a ν J' hK hJ`.
-/
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := by
  intro F _ _ _ _ _ O hO ϖ hϖ hϖ0 hloc hfin a ν _ J' hK hJ
  haveI := hfin
  exact Vol.measure_subgroupMatrixSet_mul_card O hO ϖ hϖ hϖ0 hloc a ν J' hK hJ

end Formalism.DoubleCosetMeasures.P
