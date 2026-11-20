import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.FirstIdempotentAdjointThird
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.StageB
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ContinuousExpG

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKEnd.Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d j : ℕ}
  {W : Spc F E d} {u u' : Matrix (Fin d) (Fin j) E}

variable (σ) in

abbrev cR : AE F E →+* AE F E := (cA σ : AE F E →+* AE F E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incM_transpose_cuspidal_averages {a b : Type} (A : Matrix a b E) : incM F Aᵀ = (incM F A)ᵀ := rfl

/- English proof (translation)
The claim follows from `incM_conj A`.
-/
theorem incM_c {a b : Type} (A : Matrix a b E) : (incM F A).map (cR σ) = incM F (A.map (σ : E →+* E)) := incM_conj A

/- English proof (translation)
The claim follows from `Matrix.map_zero _ (map_zero _)`.
-/
theorem incM_zero {a b : Type} : incM F (0 : Matrix a b E) = 0 := Matrix.map_zero _ (map_zero _)

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_neg (inclR (F := F) (AF F)) _`.
-/
theorem incM_neg {a b : Type} (A : Matrix a b E) : incM F (-A) = -incM F A := Matrix.ext fun _ _ => map_neg (inclR (F := F) (AF F)) _

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_add (inclR (F := F) (AF F)) _ _`.
-/
theorem incM_add {a b : Type} (A B : Matrix a b E) : incM F (A + B) = incM F A + incM F B := Matrix.ext fun _ _ => map_add (inclR (F := F) (AF F)) _ _

/- English proof (translation)
Rewrite using `[row, row, incM_transpose_cuspidal_averages, incM_mul, incM_c]`.
-/
theorem incM_row (w : Matrix (Fin d) (Fin j) E) :
    incM F (row (σ : E →+* E) W.J w) = row (cR σ) (incM F W.J) (incM F w) := by
  rw [row, row, incM_transpose_cuspidal_averages, incM_mul, incM_c]

/- English proof (translation)
Rewrite using `[e1, e1, incM_mul, incM_row]`.
-/
theorem adelic_inclusion_first_idempotent : incM F (e1 (σ : E →+* E) W.J u u') = e1 (cR σ) (incM F W.J) (incM F u) (incM F u') := by
  rw [e1, e1, incM_mul, incM_row]

/- English proof (translation)
Rewrite using `[e3, e3, incM_neg, incM_mul, incM_row]`.
-/
theorem adelic_inclusion_third_idempotent : incM F (e3 (σ : E →+* E) W.J u u') = e3 (cR σ) (incM F W.J) (incM F u) (incM F u') := by
  rw [e3, e3, incM_neg, incM_mul, incM_row]

/- English proof (translation)
Simplify using `only [mid, incM_add, incM_mul, incM_sub, incM_one, adelic_inclusion_first_idempotent, adelic_inclusion_third_idempotent]`.
-/
theorem incM_mid (s : Matrix (Fin d) (Fin d) E) :
    incM F (mid (σ : E →+* E) W.J u u' s) = mid (cR σ) (incM F W.J) (incM F u) (incM F u') (incM F s) := by
  simp only [mid, incM_add, incM_mul, incM_sub, incM_one, adelic_inclusion_first_idempotent, adelic_inclusion_third_idempotent]

/- English proof (translation)
Simplify using `only [lv, incM_add, incM_mul, incM_sub, incM_one, incM_row]`.
-/
theorem incM_lv (g g' : Matrix (Fin j) (Fin j) E) :
    incM F (lv (σ : E →+* E) W.J u u' g g') = lv (cR σ) (incM F W.J) (incM F u) (incM F u') (incM F g) (incM F g') := by
  simp only [lv, incM_add, incM_mul, incM_sub, incM_one, incM_row]

/- English proof (translation)
Use `⟨fun r => ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h.cc x)`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.

Rewrite using `[incM_c, ← incM_transpose_cuspidal_averages, h.sk, incM_neg]`. Rewrite using `[incM_c, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, h.uu, incM_zero]`. Rewrite using `[incM_c, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, h.vv, incM_zero]`. Rewrite using `[incM_c, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, h.uv, incM_one]`.
-/
theorem frA (h : Fr (σ : E →+* E) W.J u u') : Fr (cR σ) (incM F W.J) (incM F u) (incM F u') := by
  refine ⟨fun r => ?_, ?_, ?_, ?_, ?_⟩
  · induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h.cc x)
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  · rw [incM_c, ← incM_transpose_cuspidal_averages, h.sk, incM_neg]
  · rw [incM_c, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, h.uu, incM_zero]
  · rw [incM_c, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, h.vv, incM_zero]
  · rw [incM_c, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, h.uv, incM_one]

/- English proof (translation)
The claim follows from `Adj.of_unit (mat_unit s) (mat_mul_inv s)`.
-/
theorem adj_mat (s : UA σ W.J) : Adj (cR σ) (incM F W.J) (mat s) (mat s⁻¹) := Adj.of_unit (mat_unit s) (mat_mul_inv s)

def mkU (x y : Matrix (Fin d) (Fin d) (AE F E)) (h : Adj (cR σ) (incM F W.J) x y) (e : x * y = 1) (e' : y * x = 1) : UA σ W.J :=
  ⟨⟨x, y, e, e'⟩, h.unit e'⟩

/- English proof (translation)
Establish `inj : Function.Injective (incM F : Matrix (Fin d) (Fin d) E → _)` using `Matrix.map_injective PositivityTheory.ThKF.inclR_inj`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨g, hg⟩` from `Subgroup.mem_subgroupOf.1 h`. Conclude with `⟨g.1, (g⁻¹).1, (congrArg Units.val hg).symm, (congrArg Units.inv hg).symm⟩`.

Introduce and unpack `⟨x, y, h1, h2⟩`. Conclude with `Subgroup.mem_subgroupOf.2 ⟨⟨x, y, inj (by rw [incM_mul, ← h1, ← h2, mat_mul_inv, incM_one]), inj (by rw [incM_mul, ← h1, ← h2, mat_inv_mul, incM_one])⟩, Units.ext h1.symm⟩`.
-/
theorem mem_ratU {s : UA σ W.J} : s ∈ ratU σ W.J ↔ ∃ x y : Matrix (Fin d) (Fin d) E, mat s = incM F x ∧ mat s⁻¹ = incM F y := by
  have inj : Function.Injective (incM F : Matrix (Fin d) (Fin d) E → _) := Matrix.map_injective PositivityTheory.ThKF.inclR_inj
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 h
    exact ⟨g.1, (g⁻¹).1, (congrArg Units.val hg).symm, (congrArg Units.inv hg).symm⟩
  · rintro ⟨x, y, h1, h2⟩
    exact Subgroup.mem_subgroupOf.2 ⟨⟨x, y, inj (by rw [incM_mul, ← h1, ← h2, mat_mul_inv, incM_one]),
      inj (by rw [incM_mul, ← h1, ← h2, mat_inv_mul, incM_one])⟩, Units.ext h1.symm⟩

def gs (c : AE F E →+* AE F E) (g : GL (Fin j) (AE F E)) : Matrix (Fin j) (Fin j) (AE F E) := ((g⁻¹).1.map c)ᵀ

/- English proof (translation)
Rewrite using `[gs, mul_inv_rev, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]`. Both sides reduce to the same expression.
-/
theorem gs_mul (c : AE F E →+* AE F E) (g k : GL (Fin j) (AE F E)) : gs c (g * k) = gs c g * gs c k := by
  rw [gs, mul_inv_rev, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]; rfl

/- English proof (translation)
Rewrite using `[gs, inv_one, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]`.
-/
theorem gs_one (c : AE F E →+* AE F E) : gs c (1 : GL (Fin j) (AE F E)) = 1 := by
  rw [gs, inv_one, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]

def lev (h : Fr (σ : E →+* E) W.J u u') : GL (Fin j) (AE F E) →* UA σ W.J :=
  MonoidHom.mk' (fun g => mkU (lv (cR σ) (incM F W.J) (incM F u) (incM F u') g.1 (gs (cR σ) g))
    (lv (cR σ) (incM F W.J) (incM F u) (incM F u') (g⁻¹).1 (gs (cR σ) g⁻¹))
    (by
      have := (frA h).lv_adj g.1 (gs (cR σ) g)
      rwa [gs, Matrix.transpose_map, map_map_c (frA h).cc, Matrix.transpose_transpose] at this)
    (by rw [(frA h).lv_mul, ← gs_mul, ← Units.val_mul, mul_inv_cancel, gs_one, Units.val_one, lv_one])
    (by rw [(frA h).lv_mul, ← gs_mul, ← Units.val_mul, inv_mul_cancel, gs_one, Units.val_one, lv_one]))
    fun g k => mat_inj (by
      change lv _ _ _ _ _ _ = lv _ _ _ _ _ _ * lv _ _ _ _ _ _
      rw [(frA h).lv_mul, gs_mul, Units.val_mul])

variable (h : Fr (σ : E →+* E) W.J u u')
include h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_lev (g : GL (Fin j) (AE F E)) :
    mat (lev h g) = lv (cR σ) (incM F W.J) (incM F u) (incM F u') g.1 (gs (cR σ) g) := rfl

/- English proof (translation)
Establish `c0 : Continuous (cR σ : AE F E → AE F E)` using `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`. Establish `c1 : Continuous fun g => mat (lev h g)`. Establish `a : Continuous fun g : GL (Fin j) (AE F E) => g.1` using `Units.continuous_val`. Establish `b : Continuous fun g : GL (Fin j) (AE F E) => gs (cR σ) g` using `(Units.continuous_coe_inv.matrix_map c0).matrix_transpose`. Conclude with `(continuous_const.add ((continuous_const.matrix_mul (a.sub continuous_const)).matrix_mul continuous_const)).sub ((continuous_const.matrix_mul (b.sub continuous_const)).matrix_mul continuous_const)`.

Use `⟨Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c1.comp continuous_inv⟩) _, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[mat_lev, lv, ← incM_row, ← incM_row]`. Both sides reduce to the same expression.
-/
theorem isLev : IsLev u u' (lev h) := by
  have c0 : Continuous (cR σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have c1 : Continuous fun g => mat (lev h g) := by
    have a : Continuous fun g : GL (Fin j) (AE F E) => g.1 := Units.continuous_val
    have b : Continuous fun g : GL (Fin j) (AE F E) => gs (cR σ) g := (Units.continuous_coe_inv.matrix_map c0).matrix_transpose
    exact (continuous_const.add ((continuous_const.matrix_mul (a.sub continuous_const)).matrix_mul continuous_const)).sub
      ((continuous_const.matrix_mul (b.sub continuous_const)).matrix_mul continuous_const)
  refine ⟨Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c1.comp continuous_inv⟩) _, fun g => ?_⟩
  rw [mat_lev, lv, ← incM_row, ← incM_row]; rfl

/- English proof (translation)
Establish `k : ∀ γ : GL (Fin j) E, mat (lev h (Matrix.GeneralLinearGroup.map (inclR (F` using `F) (AF F)) γ)) = incM F (lv (σ : E →+* E) W.J u u' γ.1 ((γ⁻¹).1.map (σ : E →+* E))ᵀ) := fun γ => by`. Rewrite using `[incM_lv, incM_transpose_cuspidal_averages, ← incM_c]`. Both sides reduce to the same expression. Conclude with `mem_ratU.2 ⟨_, _, k γ, by rw [← map_inv, ← map_inv]; exact k _⟩`.
-/
theorem lev_rat (γ : GL (Fin j) E) : lev h (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) γ) ∈ ratU σ W.J := by
  have k : ∀ γ : GL (Fin j) E, mat (lev h (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) γ)) =
      incM F (lv (σ : E →+* E) W.J u u' γ.1 ((γ⁻¹).1.map (σ : E →+* E))ᵀ) := fun γ => by
    rw [incM_lv, incM_transpose_cuspidal_averages, ← incM_c]; rfl
  exact mem_ratU.2 ⟨_, _, k γ, by rw [← map_inv, ← map_inv]; exact k _⟩

omit h in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span E (Set.range u.col) ↔ _`. Rewrite using `[← Matrix.range_mulVecLin]`. Both sides reduce to the same expression.
-/
theorem mem_colSp {z : Fin d → E} : z ∈ colSp u ↔ ∃ y, u *ᵥ y = z := by
  change z ∈ Submodule.span E (Set.range u.col) ↔ _
  rw [← Matrix.range_mulVecLin]; rfl

omit h in
/- English proof (translation)
Establish `k : ∀ y, form σ W.J z (u *ᵥ y) = (row (σ : E →+* E) W.J u *ᵥ z) ⬝ᵥ fun i => σ (y i)` using `fun y => by`. Establish `h3 : (fun i => σ ((u *ᵥ y) i)) = u.map σ *ᵥ fun i => σ (y i)` using `funext fun i => RingHom.map_mulVec (σ : E →+* E) u y i`. Rewrite using `[form, h3, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]`. Both sides reduce to the same expression. Use `⟨fun H => funext fun i => ?_, fun H x hx => ?_⟩` and prove the remaining obligations.

Use `H _ (mem_colSp.2 ⟨Pi.single i 1, rfl⟩)` as an intermediate fact. Rewrite using `[k, show (fun a => σ ((Pi.single i 1 : Fin j → E) a)) = Pi.single i 1 from funext fun a => by`. Apply the tactic sequence `by_cases e : a = i <;> simp [e]] at this`. Simplify using `using this`. Take `⟨y, rfl⟩` from `mem_colSp.1 hx`.

Rewrite using `[k, H, zero_dotProduct]`.
-/
theorem perp_iff {z : Fin d → E} : (∀ x ∈ colSp u, form σ W.J z x = 0) ↔ row (σ : E →+* E) W.J u *ᵥ z = 0 := by
  have k : ∀ y, form σ W.J z (u *ᵥ y) = (row (σ : E →+* E) W.J u *ᵥ z) ⬝ᵥ fun i => σ (y i) := fun y => by
    have h3 : (fun i => σ ((u *ᵥ y) i)) = u.map σ *ᵥ fun i => σ (y i) := funext fun i => RingHom.map_mulVec (σ : E →+* E) u y i
    rw [form, h3, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]; rfl
  refine ⟨fun H => funext fun i => ?_, fun H x hx => ?_⟩
  · have := H _ (mem_colSp.2 ⟨Pi.single i 1, rfl⟩)
    rw [k, show (fun a => σ ((Pi.single i 1 : Fin j → E) a)) = Pi.single i 1 from funext fun a => by
      by_cases e : a = i <;> simp [e]] at this
    simpa using this
  · obtain ⟨y, rfl⟩ := mem_colSp.1 hx
    rw [k, H, zero_dotProduct]

omit h in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `(Submodule.span_le (p := LinearMap.range (incM F u).mulVecLin)).2 ?_ H` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, rfl⟩` from `mem_colSp.1 hx`.

Conclude with `⟨incV F y, incM_mulVec u y⟩`. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[Matrix.mulVec_eq_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[op_smul_eq_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨u *ᵥ Pi.single i 1, mem_colSp.2 ⟨_, rfl⟩, by`. Use function extensionality and compare the values at `a`. Simplify using `[incM, incV]⟩)`.
-/
theorem mem_spanA {z : Fin d → AE F E} :
    z ∈ Submodule.span (AE F E) (incV F '' (colSp u : Set (Fin d → E))) ↔ ∃ y, incM F u *ᵥ y = z := by
  constructor
  · intro H
    refine (Submodule.span_le (p := LinearMap.range (incM F u).mulVecLin)).2 ?_ H
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := mem_colSp.1 hx
    exact ⟨incV F y, incM_mulVec u y⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_eq_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u *ᵥ Pi.single i 1, mem_colSp.2 ⟨_, rfl⟩, by
      funext a; simp [incM, incV]⟩)

/- English proof (translation)
Rewrite using `[(frA h).mid_iff]`. Use `set q := 1 - e1 (σ : E →+* E) W.J u u' - e3 (σ : E →+* E) W.J u u' with hq`. Establish `e : incM F q = 1 - e1 (cR σ) (incM F W.J) (incM F u) (incM F u') - e3 (cR σ) (incM F W.J) (incM F u) (incM F u')`. Rewrite using `[hq, incM_sub, incM_sub, incM_one, adelic_inclusion_first_idempotent, adelic_inclusion_third_idempotent]`. Use extensionality with `a b`.

Take `⟨y, hy⟩` from `mem_spanA.1 (H (q *ᵥ Pi.single b 1) (perp_iff.2 (by rw [Matrix.mulVec_mulVec, h.u_q, Matrix.zero_mulVec])))`. Use `congrArg (incM F q *ᵥ ·) hy` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, e, (frA h).q_u, Matrix.zero_mulVec] at this`. Rewrite `this` using `[← Matrix.one_mulVec (incV F _), Matrix.mulVec_mulVec, Matrix.mul_one, ← Matrix.sub_mulVec, Matrix.mulVec_mulVec, ← col_eq, e]`. Conclude with `(congrFun this a).symm`.
-/
theorem mid_of_move {s : Matrix (Fin d) (Fin d) (AE F E)} (H : ∀ z : Fin d → E, (∀ x ∈ colSp u, form σ W.J z x = 0) →
    s *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (colSp u : Set (Fin d → E)))) :
    mid (cR σ) (incM F W.J) (incM F u) (incM F u') s = 1 := by
  rw [(frA h).mid_iff]
  set q := 1 - e1 (σ : E →+* E) W.J u u' - e3 (σ : E →+* E) W.J u u' with hq
  have e : incM F q = 1 - e1 (cR σ) (incM F W.J) (incM F u) (incM F u') - e3 (cR σ) (incM F W.J) (incM F u) (incM F u') := by
    rw [hq, incM_sub, incM_sub, incM_one, adelic_inclusion_first_idempotent, adelic_inclusion_third_idempotent]
  ext a b
  obtain ⟨y, hy⟩ := mem_spanA.1 (H (q *ᵥ Pi.single b 1) (perp_iff.2 (by rw [Matrix.mulVec_mulVec, h.u_q, Matrix.zero_mulVec])))
  have := congrArg (incM F q *ᵥ ·) hy
  simp only [Matrix.mulVec_mulVec, e, (frA h).q_u, Matrix.zero_mulVec] at this
  rw [← Matrix.one_mulVec (incV F _), Matrix.mulVec_mulVec, Matrix.mul_one, ← Matrix.sub_mulVec, Matrix.mulVec_mulVec, ← col_eq, e] at this
  exact (congrFun this a).symm

/- English proof (translation)
Take `⟨-, -, -, k⟩` from `unipU_eq (σ := σ) (W := W) (colSp u)`. Rewrite using `[k]`. Use `⟨fun ⟨a, b⟩ => ⟨?_, mid_of_move h b⟩, fun ⟨a, b⟩ => ⟨fun x hx => ?_, fun z hz => ?_⟩⟩` and prove the remaining obligations. Use extensionality with `i l`. Use `congrFun (a _ (mem_colSp.2 ⟨Pi.single l 1, rfl⟩)) i` as an intermediate fact.

Simplify `this` using `[incM, incV, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Take `⟨y, rfl⟩` from `mem_colSp.1 hx`. Rewrite using `[← incM_mulVec, Matrix.mulVec_mulVec, a]`. Establish `a' : mat s⁻¹ * incM F u = incM F u` using `by conv_lhs => rw [← a, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]`. Establish `h1` using `congrArg (· *ᵥ incV F z) ((frA h).move (adj_mat s) a a' b)`.

Establish `h2 : (1 - e3 (cR σ) (incM F W.J) (incM F u) (incM F u')) *ᵥ incV F z = incV F z`. Rewrite using `[← adelic_inclusion_third_idempotent, Matrix.sub_mulVec, incM_mulVec, e3, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, perp_iff.1 hz]`. Use function extensionality and compare the values at `i`. Simplify using `[incV]`. Simplify using `only [← Matrix.mulVec_mulVec, h2] at h1`.

Rewrite `h1` using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `mem_spanA.2 ⟨_, h1.symm⟩`.
-/
theorem mem_N {s : UA σ W.J} : s ∈ unipU σ W (colSp u) ↔
    mat s * incM F u = incM F u ∧ mid (cR σ) (incM F W.J) (incM F u) (incM F u') (mat s) = 1 := by
  obtain ⟨-, -, -, k⟩ := unipU_eq (σ := σ) (W := W) (colSp u)
  rw [k]
  refine ⟨fun ⟨a, b⟩ => ⟨?_, mid_of_move h b⟩, fun ⟨a, b⟩ => ⟨fun x hx => ?_, fun z hz => ?_⟩⟩
  · ext i l
    have := congrFun (a _ (mem_colSp.2 ⟨Pi.single l 1, rfl⟩)) i
    simpa [incM, incV, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  · obtain ⟨y, rfl⟩ := mem_colSp.1 hx
    rw [← incM_mulVec, Matrix.mulVec_mulVec, a]
  · have a' : mat s⁻¹ * incM F u = incM F u := by
      conv_lhs => rw [← a, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    have h1 := congrArg (· *ᵥ incV F z) ((frA h).move (adj_mat s) a a' b)
    have h2 : (1 - e3 (cR σ) (incM F W.J) (incM F u) (incM F u')) *ᵥ incV F z = incV F z := by
      rw [← adelic_inclusion_third_idempotent, Matrix.sub_mulVec, incM_mulVec, e3, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, perp_iff.1 hz]
      funext i; simp [incV]
    simp only [← Matrix.mulVec_mulVec, h2] at h1
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact mem_spanA.2 ⟨_, h1.symm⟩

/- English proof (translation)
Rewrite using `[mem_N h, ← map_inv, mat_mul, mat_lev, Matrix.mul_assoc, (frA h).lv_u, ← Matrix.mul_assoc, a, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, ← b, ← (frA h).mid_lv 1 1 (g⁻¹).1 (gs (cR σ) g⁻¹) (mat s), lv_one, Matrix.one_mul]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem par_mem {s : UA σ W.J} {g : GL (Fin j) (AE F E)} (a : mat s * incM F u = incM F u * g.1)
    (b : mid (cR σ) (incM F W.J) (incM F u) (incM F u') (mat s) = 1) : s * (lev h g)⁻¹ ∈ unipU σ W (colSp u) := by
  rw [mem_N h, ← map_inv, mat_mul, mat_lev, Matrix.mul_assoc, (frA h).lv_u, ← Matrix.mul_assoc, a, Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one, ← b, ← (frA h).mid_lv 1 1 (g⁻¹).1 (gs (cR σ) g⁻¹) (mat s), lv_one, Matrix.one_mul]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Take `⟨a, b⟩` from `(mem_N h).1 hs`. Use `par_mem h (by rw [mat_mul, Matrix.mul_assoc, a, mat_lev, (frA h).lv_u]) ?_` and prove the remaining obligations. Rewrite using `[← b, ← (frA h).mid_lv g.1 (gs (cR σ) g) 1 1 (mat s), lv_one, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem lev_norm (g : GL (Fin j) (AE F E)) (s : UA σ W.J) (hs : s ∈ unipU σ W (colSp u)) :
    lev h g * s * (lev h g)⁻¹ ∈ unipU σ W (colSp u) := by
  obtain ⟨a, b⟩ := (mem_N h).1 hs
  refine par_mem h (by rw [mat_mul, Matrix.mul_assoc, a, mat_lev, (frA h).lv_u]) ?_
  rw [← b, ← (frA h).mid_lv g.1 (gs (cR σ) g) 1 1 (mat s), lv_one, Matrix.mul_one]; rfl

end PositivityTheory.ThKEnd.Cusp

end
