import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FrameDom

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexOrder

variable {n : ℕ} {Hm x₀ : Mt n} {q : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem conjTranspose_map_conj (y : Mt n) : (y.map (starRingEnd ℂ))ᴴ = yᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem map_conj_conj (y : Mt n) : (y.map (starRingEnd ℂ)).map (starRingEnd ℂ) = y := by
  ext i j
  simp

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem det_map_conj_ne {y : Mt n} (h : y.det ≠ 0) : (y.map (starRingEnd ℂ)).det ≠ 0 := by
  have e : y.map (starRingEnd ℂ) = (yᴴ)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e, det_transpose, det_conjTranspose]
  intro h0
  exact h (star_eq_zero.mp h0)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem neg_gram_mul (Hm x b : Mt n) : -((x * b)ᴴ * Hm * (x * b)) = bᴴ * (-(xᴴ * Hm * x)) * b := by
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem neg_gram_orth (h : OrthFr Hm q x₀) : -(x₀ᴴ * Hm * x₀) = diagonal (sv q) := by
  rw [h.2, ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sgn_cast_eq q n, ← Matrix.diagonal_neg, neg_neg]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sv_mul_self (a : Fin n) : sv q a * sv q a = 1 := by
  simp only [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv]
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_diag_sv_ne : (diagonal (sv q) : Mt n).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => left_ne_zero_of_mul_eq_one (sv_mul_self a)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem det_ne_of_orth (h : OrthFr Hm q x₀) : x₀.det ≠ 0 ∧ Hm.det ≠ 0 := by
  have h1 : (x₀ᴴ * Hm * x₀).det ≠ 0 := by
    have e : x₀ᴴ * Hm * x₀ = -(diagonal (sv q)) := by rw [← neg_gram_orth h, neg_neg]
    rw [e, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) det_diag_sv_ne
  rw [det_mul, det_mul] at h1
  exact ⟨right_ne_zero_of_mul h1, right_ne_zero_of_mul (left_ne_zero_of_mul h1)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem neg_gram_isHermitian (h : OrthFr Hm q x₀) (x : Mt n) : (-(xᴴ * Hm * x)).IsHermitian := by
  obtain ⟨hx0, -⟩ := det_ne_of_orth h
  have hD : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [h.2, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp
  have hD' : x₀ᴴ * Hmᴴ * x₀ = x₀ᴴ * Hm * x₀ := by
    rw [← hD]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det x₀).mpr hx0.isUnit
  have hus : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [det_conjTranspose]
    have hs : star x₀.det ≠ 0 := fun h0 => hx0 (star_eq_zero.mp h0)
    exact hs.isUnit
  have hH : Hmᴴ = Hm := hus.mul_left_cancel (hu.mul_right_cancel hD')
  exact (Matrix.isHermitian_conjTranspose_mul_mul x (hH : Hm.IsHermitian)).neg

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem mul_upT_mem {x b : Mt n} (hx : x ∈ frDom Hm q) (hb : UpT b) : x * b ∈ frDom Hm q := by
  obtain ⟨hdet, hmin⟩ := hx
  refine ⟨by rw [det_mul]; exact mul_ne_zero hdet hb.1, fun i => ?_⟩
  have hbT : b.BlockTriangular id := fun a c hca => hb.2 a c hca
  have hN : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    simp [hb.2 a c hca]
  have hdiag : ∀ k, b k k ≠ 0 := by
    have := hb.1
    rw [Matrix.det_of_upperTriangular hbT] at this
    exact fun k => Finset.prod_ne_zero_iff.mp this k (Finset.mem_univ k)
  have e : -((x * b)ᴴ * Hm * (x * b)) =
      (b.map (starRingEnd ℂ))ᵀ * (-(xᴴ * Hm * x)) * (b.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
    rw [neg_gram_mul, ← conjTranspose_map_conj (b.map (starRingEnd ℂ)), map_conj_conj]
  rw [e, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj hN i]
  refine ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pos_conj_mul ?_ (hmin i)
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  simpa using hdiag _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unitary_mul_mem (hH : Hm.det ≠ 0) {u x : Mt n} (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) (hx : x ∈ frDom Hm q) :
    u * x ∈ frDom Hm q := by
  have hu' : uᴴ * Hm * u = Hm := hu
  have hg : (u * x)ᴴ * Hm * (u * x) = xᴴ * Hm * x := by
    have : (u * x)ᴴ * Hm * (u * x) = xᴴ * (uᴴ * Hm * u) * x := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hu']
  have hu0 : u.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hu'
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hH this.symm
  refine ⟨by rw [det_mul]; exact mul_ne_zero hu0 hx.1, fun i => ?_⟩
  rw [hg]
  exact hx.2 i

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem neg_gram_conj (h : OrthFr Hm q x₀) (y : Mt n) :
    -((x₀ * y.map (starRingEnd ℂ))ᴴ * Hm * (x₀ * y.map (starRingEnd ℂ))) = Gy q y := by
  rw [neg_gram_mul Hm x₀ (y.map (starRingEnd ℂ)), neg_gram_orth h, conjTranspose_map_conj]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_of_ok (h : OrthFr Hm q x₀) {y : Mt n} (hy : Ok q y) : x₀ * y.map (starRingEnd ℂ) ∈ frDom Hm q := by
  refine ⟨?_, fun i => ?_⟩
  · rw [det_mul]
    exact mul_ne_zero (det_ne_of_orth h).1 (det_map_conj_ne (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.det_ne_of_ok hy))
  · rw [neg_gram_conj h]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.lead_pos hy i (Nat.le_of_lt_succ i.isLt)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ok_of_gy {y : Mt n} (h : Gy q y = diagonal (sv q)) : Ok q y := by
  show (diagonal (sv q) * Gy q y).PosDef
  rw [h, diagonal_mul_diagonal]
  have e : (fun a : Fin n => sv q a * sv q a) = fun _ => (1 : ℂ) := funext sv_mul_self
  rw [e, diagonal_one]
  exact Matrix.PosDef.one

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ok_one : Ok q (1 : Mt n) := by
  refine ok_of_gy ?_
  show (1 : Mt n)ᵀ * diagonal (sv q) * (1 : Mt n).map (starRingEnd ℂ) = diagonal (sv q)
  rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem base_mem (h : OrthFr Hm q x₀) : x₀ ∈ frDom Hm q := by
  have := mem_of_ok h (ok_one (q := q) (n := n))
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isOpen_frDom (Hm : Mt n) (q : ℕ) : IsOpen (frDom Hm q) := by
  have e : frDom Hm q = {x : Mt n | x.det ≠ 0} ∩
      ⋂ i : Fin (n + 1), {x : Mt n | 0 < psgn q i * (lminor (-(xᴴ * Hm * x)) i).re} := by
    ext x
    simp only [frDom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsOpen.inter (isOpen_ne_fun continuous_id.matrix_det continuous_const) ?_
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  exact ((((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id).neg).matrix_submatrix _ _).matrix_det

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isPreconnected_frDom (h : OrthFr Hm q x₀) : IsPreconnected (frDom Hm q) := by
  have hOk : IsPreconnected {y : Mt n | Ok q y} := by
    have e : {y : Mt n | Ok q y} =
        (fun y : Unit → Mt n => y ()) '' {y : Unit → Mt n | ∀ i, Ok q (y i)} := by
      ext y
      constructor
      · intro hy
        exact ⟨fun _ => y, fun _ => hy, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz ()
    rw [e]
    exact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_ok (p0 := q) (r := n) (ι := Unit)).image _
      (continuous_apply _).continuousOn
  have hUp : IsPreconnected {b : Mt n | UpT b} := by
    have e : {b : Mt n | UpT b} =
        (fun b : Unit → Mt n => b ()) '' {b : Unit → Mt n |
          ∀ i, (b i).det ≠ 0 ∧ ∀ a c : Fin n, c < a → b i a c = 0} := by
      ext b
      constructor
      · intro hb
        exact ⟨fun _ => b, fun _ => hb, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz ()
    rw [e]
    exact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_upper (r := n) (ι := Unit)).image _
      (continuous_apply _).continuousOn
  have hT : IsPreconnected ((fun y : Mt n => x₀ * y.map (starRingEnd ℂ)) '' {y : Mt n | Ok q y}) :=
    hOk.image _ (continuous_const.matrix_mul
      (continuous_id.matrix_map Complex.continuous_conj)).continuousOn
  have hTsub : (fun y : Mt n => x₀ * y.map (starRingEnd ℂ)) '' {y : Mt n | Ok q y} ⊆ frDom Hm q := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_of_ok h hy
  refine isPreconnected_of_forall x₀ fun x hx => ?_
  have hxB : IsPreconnected ((fun b : Mt n => x * b) '' {b : Mt n | UpT b}) :=
    hUp.image _ (continuous_const.matrix_mul continuous_id).continuousOn
  have hxBsub : (fun b : Mt n => x * b) '' {b : Mt n | UpT b} ⊆ frDom Hm q := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_upT_mem hx hb

  obtain ⟨b, hbdet, hbT, hbeq⟩ := GlobalTheory.UnitFrames.exists_upper_conj_eq_signature q (-(xᴴ * Hm * x))
    (neg_gram_isHermitian h x) hx.2
  set c : Mt n := b.map (starRingEnd ℂ) with hc
  have hcU : UpT c := by
    refine ⟨det_map_conj_ne hbdet, fun a d hda => ?_⟩
    simp [hc, hbT hda]
  have hgc : -((x * c)ᴴ * Hm * (x * c)) = diagonal (sv q) := by
    rw [neg_gram_mul, hc, conjTranspose_map_conj, hbeq, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sgn_cast_eq]
  have hx0 := (det_ne_of_orth h).1
  set y : Mt n := (x₀⁻¹ * (x * c)).map (starRingEnd ℂ) with hy
  have hxy : x₀ * y.map (starRingEnd ℂ) = x * c := by
    rw [hy, map_conj_conj, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv x₀ hx0.isUnit, Matrix.one_mul]
  have hyOk : Ok q y := by
    refine ok_of_gy ?_
    rw [← neg_gram_conj h y, hxy, hgc]
  refine ⟨_ ∪ _, Set.union_subset hTsub hxBsub, Or.inl ⟨1, ok_one, ?_⟩,
    Or.inr ⟨1, ⟨by simp, fun a c hca => by simp [Matrix.one_apply_ne (ne_of_lt hca).symm]⟩, Matrix.mul_one x⟩,
    hT.union (x * c) ⟨y, hyOk, hxy⟩ ⟨c, hcU, rfl⟩ hxB⟩
  show x₀ * (1 : Mt n).map (starRingEnd ℂ) = x₀
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

end GlobalTheory.HolDict.FrameDom

open GlobalTheory.HolDict.FrameDom in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem GlobalTheory.HolDict.frDoms_open_preconnected_stable : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → IsOpen (frDoms Hm q) ∧ IsPreconnected (frDoms Hm q) ∧ (∀ u ∈ UG Hm, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → ∀ x ∈ frDoms Hm q, (fun τ => (u τ * Matrix.of (x τ) * b τ : Mt n)) ∈ frDoms Hm q) ∧ (fun τ => (x₀ τ : Mt n)) ∈ frDoms Hm q := by
  intro n ι _ _ Hm q x₀ h
  have e : frDoms Hm q = Set.univ.pi fun τ => frDom (Hm τ) (q τ) := by
    ext x
    exact ⟨fun hx τ _ => hx τ, fun hx τ => hx τ (Set.mem_univ τ)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e]
    exact isOpen_set_pi Set.finite_univ fun τ _ => isOpen_frDom (Hm τ) (q τ)
  · rw [e]
    exact isPreconnected_univ_pi fun τ => isPreconnected_frDom (h τ)
  · intro u hu b hb x hx τ
    exact mul_upT_mem (unitary_mul_mem (det_ne_of_orth (h τ)).2 (hu τ) (hx τ)) (hb τ)
  · intro τ
    exact base_mem (h τ)
