import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.NormSqLeSum

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Mean

variable {G : Type} [Group G]

def mn (S : Subgroup G) {E : Type} [AddCommGroup E] [Module ℝ E]
    (e : Quotient (QuotientGroup.rightRel S) → E) : E :=
  ((S.index : ℝ))⁻¹ • ∑ᶠ c, e c

/- English proof (translation)
Use `haveI : Finite (G ⧸ S) := Subgroup.index_ne_zero_iff_finite.mp h`. Conclude with `Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm`.
-/
theorem fin_of_ne {S : Subgroup G} (h : S.index ≠ 0) : Finite (Quotient (QuotientGroup.rightRel S)) := by
  haveI : Finite (G ⧸ S) := Subgroup.index_ne_zero_iff_finite.mp h
  exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm

/- English proof (translation)
Simplify using `[mn, h]`.
-/
theorem mn_zero {S : Subgroup G} (h : S.index = 0) {E : Type} [AddCommGroup E] [Module ℝ E]
    (e : Quotient (QuotientGroup.rightRel S) → E) : mn S e = 0 := by
  simp [mn, h]

/- English proof (translation)
Rewrite using `[mn, finsum_eq_sum_of_fintype]`.
-/
theorem mn_fin {S : Subgroup G} [Fintype (Quotient (QuotientGroup.rightRel S))] {E : Type} [AddCommGroup E]
    [Module ℝ E] (e : Quotient (QuotientGroup.rightRel S) → E) : mn S e = ((S.index : ℝ))⁻¹ • ∑ c, e c := by
  rw [mn, finsum_eq_sum_of_fintype]

/- English proof (translation)
Distinguish the cases in `h : S.index = 0`. Rewrite using `[mn_zero h, mn_zero h, map_zero]`. Use `haveI := fin_of_ne h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))`. Rewrite using `[mn_fin, mn_fin, map_smul, map_sum]`.
-/
theorem mn_map (S : Subgroup G) {E E' : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {F : Type} [FunLike F E E'] [LinearMapClass F ℝ E E'] (ℓ : F)
    (e : Quotient (QuotientGroup.rightRel S) → E) : ℓ (mn S e) = mn S fun c => ℓ (e c) := by
  by_cases h : S.index = 0
  · rw [mn_zero h, mn_zero h, map_zero]
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    rw [mn_fin, mn_fin, map_smul, map_sum]

/- English proof (translation)
Distinguish the cases in `h : S.index = 0`. Simplify using `only [mn_zero h, integral_zero]`. Use `haveI := fin_of_ne h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))`. Simplify using `only [mn_fin]`.

Rewrite using `[integral_smul, integral_finset_sum _ fun c _ => he c]`.
-/
theorem mn_integral (S : Subgroup G) {X E : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : Quotient (QuotientGroup.rightRel S) → X → E) (he : ∀ c, Integrable (e c) μ) :
    ∫ x, mn S (fun c => e c x) ∂μ = mn S fun c => ∫ x, e c x ∂μ := by
  by_cases h : S.index = 0
  · simp only [mn_zero h, integral_zero]
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [mn_fin]
    rw [integral_smul, integral_finset_sum _ fun c _ => he c]

/- English proof (translation)
Distinguish the cases in `h : S.index = 0`. Simplify using `only [mn_zero h]`. Conclude with `continuousOn_const`. Use `haveI := fin_of_ne h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))`.

Simplify using `only [mn_fin]`. Conclude with `(continuousOn_finset_sum _ fun c _ => he c).const_smul _`.
-/
theorem mn_contOn (S : Subgroup G) {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Quotient (QuotientGroup.rightRel S) → X → E) {s : Set X} (he : ∀ c, ContinuousOn (e c) s) :
    ContinuousOn (fun x => mn S fun c => e c x) s := by
  by_cases h : S.index = 0
  · simp only [mn_zero h]
    exact continuousOn_const
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [mn_fin]
    exact (continuousOn_finset_sum _ fun c _ => he c).const_smul _

/- English proof (translation)
Use function extensionality and compare the values at `y`. Distinguish the cases in `h : S.index = 0`. Simplify using `[dC, mn_zero h]`. Use `haveI := fin_of_ne h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))`.

Simplify using `only [dC, mn_fin, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dC_mn (S : Subgroup G) {Y : Type} {m : ℕ} (F : Quotient (QuotientGroup.rightRel S) → (Fin (m + 1) → Y) → ℝ) :
    dC (fun y => mn S fun c => F c y) = fun y => mn S fun c => dC (F c) y := by
  funext y
  by_cases h : S.index = 0
  · simp [dC, mn_zero h]
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [dC, mn_fin, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
    ring

end Mean

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

open ComplexOrder in
/- English proof (translation)
Unfold `Pos`. Use `convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ w => ?_` and prove the remaining obligations. Establish `e : mat (a • x + b • y) w = a • mat x w + b • mat y w`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `((hx w).smul ha).add ((hy w).smul hb)`.
-/
theorem pos_convex : Convex ℝ (Pos L N) := by
  unfold Pos
  refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ w => ?_
  have e : mat (a • x + b • y) w = a • mat x w + b • mat y w := by
    ext i j
    rfl
  rw [e]
  exact ((hx w).smul ha).add ((hy w).smul hb)

def pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) : Form (HS L N) q :=
  fun h => (ω (actL g h)).compContinuousLinearMap (actL g)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w i j`. Use `show (Matrix.conjTranspose (((k * g) w)⁻¹).val * mat h w * (((k * g) w)⁻¹).val) i j = (Matrix.conjTranspose ((k w)⁻¹).val * (Matrix.conjTranspose ((g w)⁻¹).val * mat h w * ((g w)⁻¹).val) * ((k w)⁻¹).val) i j`. Simplify using `only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]`.
-/
private theorem pb_pb_apply_eq_pb_mul (k g : Gp L N) (h : HS L N) : actL (k * g) h = actL k (actL g h) := by
  apply Subtype.ext
  funext w i j
  show (Matrix.conjTranspose (((k * g) w)⁻¹).val * mat h w * (((k * g) w)⁻¹).val) i j =
    (Matrix.conjTranspose ((k w)⁻¹).val * (Matrix.conjTranspose ((g w)⁻¹).val * mat h w * ((g w)⁻¹).val) *
      ((k w)⁻¹).val) i j
  simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [fr, pb, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, pb_pb_apply_eq_pb_mul]`.
-/
theorem fr_pb {q : ℕ} (g x : Gp L N) (ω : Form (HS L N) q) : fr (pb g ω) x = fr ω (g * x) := by
  ext v
  simp only [fr, pb, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, pb_pb_apply_eq_pb_mul]

/- English proof (translation)
Establish `hmaps : Set.MapsTo (actL g) (Pos L N) (Pos L N)` using `fun h hh => (g • (⟨h, hh⟩ : Pos L N)).2`. Conclude with `((ContinuousAlternatingMap.compContinuousLinearMapCLM (actL g)).continuous.comp_continuousOn (hω.comp (actL g).continuous.continuousOn hmaps)).congr fun _ _ => rfl`.
-/
theorem pb_contOn {q : ℕ} (g : Gp L N) {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) :
    ContinuousOn (pb g ω) (Pos L N) := by
  have hmaps : Set.MapsTo (actL g) (Pos L N) (Pos L N) := fun h hh => (g • (⟨h, hh⟩ : Pos L N)).2
  exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM (actL g)).continuous.comp_continuousOn
    (hω.comp (actL g).continuous.continuousOn hmaps)).congr fun _ _ => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intS_eq {q : ℕ} (ω : Form (HS L N) q) (y : Fin (q + 1) → HS L N) :
    intS ω y = ∫ t in sx q, ω (pt y t) fun j => y j.succ - y 0 := rfl

/- English proof (translation)
Simplify using `only [intS, pb, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, map_add, map_sum, map_smul, map_sub]`.
-/
theorem intS_pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) (y : Fin (q + 1) → HS L N) :
    intS (pb g ω) y = intS ω fun j => actL g (y j) := by
  simp only [intS, pb, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, map_add, map_sum,
    map_smul, map_sub]

/- English proof (translation)
The claim follows from `intS_pb g ω _`.
-/
theorem intP_pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) (y : Fin (q + 1) → Pos L N) :
    intP (pb g ω) y = intP ω fun j => g • y j :=
  intS_pb g ω _

/- English proof (translation)
Use `show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})`. Use `IsClosed.inter ?_ ?_` and prove the remaining obligations. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)`. Conclude with `isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const`.
-/
private theorem isClosed_sx (q : ℕ) : IsClosed (sx q) := by
  show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})
  refine IsClosed.inter ?_ ?_
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const

/- English proof (translation)
Use `(isCompact_Icc (a := (0 : Fin q → ℝ)) (b := 1)).of_isClosed_subset (isClosed_sx q) ?_` and prove the remaining obligations. Introduce `t ht`. Establish `ht' : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1` using `ht`. Conclude with `⟨fun j => ht'.1 j, fun j => (Finset.single_le_sum (fun i _ => ht'.1 i) (Finset.mem_univ j)).trans ht'.2⟩`.
-/
private theorem isCompact_sx (q : ℕ) : IsCompact (sx q) := by
  refine (isCompact_Icc (a := (0 : Fin q → ℝ)) (b := 1)).of_isClosed_subset (isClosed_sx q) ?_
  intro t ht
  have ht' : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1 := ht
  exact ⟨fun j => ht'.1 j, fun j => (Finset.single_le_sum (fun i _ => ht'.1 i) (Finset.mem_univ j)).trans ht'.2⟩

/- English proof (translation)
Establish `ht' : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1` using `ht`. Establish `hw : ∀ i ∈ Finset.univ, 0 ≤ (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i`. Introduce `i _`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simpa using ht'.2`.

Consider the case `succ j => simpa using ht'.1 j`. Establish `h1 : ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i = 1`. Simplify using `[Fin.sum_univ_succ]`. Establish `hmem` using `pos_convex.sum_mem hw h1 (fun i _ => (y i).2)`. Use `hmem using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [pt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
private theorem pt_mem_Pos_of_mem_sx {q : ℕ} (y : Fin (q + 1) → Pos L N) {t : Fin q → ℝ} (ht : t ∈ sx q) :
    pt (fun j => (y j).1) t ∈ Pos L N := by
  have ht' : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1 := ht
  have hw : ∀ i ∈ Finset.univ, 0 ≤ (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i := by
    intro i _
    induction i using Fin.cases with
    | zero => simpa using ht'.2
    | succ j => simpa using ht'.1 j
  have h1 : ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i = 1 := by
    simp [Fin.sum_univ_succ]
  have hmem := pos_convex.sum_mem hw h1 (fun i _ => (y i).2)
  convert hmem using 1
  simp only [pt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, sub_smul, one_smul]
  abel

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `ContinuousOn.integrableOn_compact (isCompact_sx q) ?_` and prove the remaining obligations. Establish `hpt : Continuous fun t : Fin q → ℝ => pt (fun j => (y j).1) t` using `by show Continuous fun t : Fin q → ℝ => (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) fun_prop`. Establish `hev : Continuous fun f : HS L N [⋀^Fin q]→L[ℝ] ℝ => f fun j => (y j.succ).1 - (y 0).1` using `by fun_prop`. Conclude with `hev.comp_continuousOn (hω.comp hpt.continuousOn fun t ht => pt_mem_Pos_of_mem_sx y ht)`.
-/
theorem intP_integ {q : ℕ} {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) (y : Fin (q + 1) → Pos L N) :
    IntegrableOn (fun t => ω (pt (fun j => (y j).1) t) fun j => (y j.succ).1 - (y 0).1) (sx q) := by
  refine ContinuousOn.integrableOn_compact (isCompact_sx q) ?_
  have hpt : Continuous fun t : Fin q → ℝ => pt (fun j => (y j).1) t := by
    show Continuous fun t : Fin q → ℝ => (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1)
    fun_prop
  have hev : Continuous fun f : HS L N [⋀^Fin q]→L[ℝ] ℝ => f fun j => (y j.succ).1 - (y 0).1 := by
    fun_prop
  exact hev.comp_continuousOn (hω.comp hpt.continuousOn fun t ht => pt_mem_Pos_of_mem_sx y ht)

/- English proof (translation)
Simplify using `only [intP, intS_eq, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]`. Conclude with `integral_sub (intP_integ hω y) (intP_integ hω' y)`.
-/
theorem intP_sub {q : ℕ} {ω ω' : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N))
    (hω' : ContinuousOn ω' (Pos L N)) (y : Fin (q + 1) → Pos L N) :
    intP (ω - ω') y = intP ω y - intP ω' y := by
  simp only [intP, intS_eq, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
  exact integral_sub (intP_integ hω y) (intP_integ hω' y)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Rewrite using `[← intP_pb]`. Simplify using `only [intP, intS_eq]`. Use `setIntegral_congr_fun (isClosed_sx q).measurableSet fun t ht => ?_` and prove the remaining obligations. Conclude with `DFunLike.congr_fun (hω _ (pt_mem_Pos_of_mem_sx y ht)) _`.
-/
theorem intP_inv {q : ℕ} {ω : Form (HS L N) q} {g : Gp L N} (hω : FInv ω g) (y : Fin (q + 1) → Pos L N) :
    intP ω (fun j => g • y j) = intP ω y := by
  rw [← intP_pb]
  simp only [intP, intS_eq]
  refine setIntegral_congr_fun (isClosed_sx q).measurableSet fun t ht => ?_
  exact DFunLike.congr_fun (hω _ (pt_mem_Pos_of_mem_sx y ht)) _

abbrev Sg (q : GK L N) : Subgroup (Gm L N) :=
  ((toK L N).range.map (MulAut.conj q⁻¹).toMonoidHom).comap (toK L N)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hecke_eq {Y H E : Type} [Group H] [MulAction H Y] [AddCommGroup E] [Module ℝ E] (τ : GK L N →* H)
    (q : GK L N) (f : Y → E) (y : Y) :
    hecke (toK L N) τ q f y = mn (Sg q) fun c => f (τ (q * toK L N (Quotient.out c)) • y) := rfl

def Hk {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) : Form (HS L N) k :=
  fun h => mn (Sg q) fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω h

/- English proof (translation)
Rewrite using `[hecke_eq]`. Simplify using `only [smul_eq_mul, ← fr_pb]`. Conclude with `mn_map (Sg q) ({ toFun := fun a : HS L N [⋀^Fin k]→L[ℝ] ℝ => a.compContinuousLinearMap (actL x) map_add' := fun a b => by ext; simp map_smul' := fun c a => by ext; simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (HS L N [⋀^Fin k]→L[ℝ] ℝ)) (fun c => pb (toP L N (q * toK L N (Quotient.out …`.
-/
theorem fr_Hk {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) (x : Gp L N) :
    fr (Hk q ω) x = hecke (toK L N) (toP L N) q (fr ω) x := by
  rw [hecke_eq]
  simp only [smul_eq_mul, ← fr_pb]
  exact mn_map (Sg q)
    ({ toFun := fun a : HS L N [⋀^Fin k]→L[ℝ] ℝ => a.compContinuousLinearMap (actL x)
       map_add' := fun a b => by ext; simp
       map_smul' := fun c a => by ext; simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (HS L N [⋀^Fin k]→L[ℝ] ℝ))
    (fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω (actL x (one L N)))

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[fr_Hk, hecke_eq, hecke_eq]`. Conclude with `mn_map (Sg q) ({ toFun := fun f : HS L N [⋀^Fin k]→L[ℝ] ℝ => f u map_add' := fun _ _ => by simp map_smul' := fun _ _ => by simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ) _`.
-/
theorem comp_Hk {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) (u : Fin k → HS L N) :
    (fun x => fr (Hk q ω) x u) = hecke (toK L N) (toP L N) q fun x => fr ω x u := by
  funext x
  rw [fr_Hk, hecke_eq, hecke_eq]
  exact mn_map (Sg q)
    ({ toFun := fun f : HS L N [⋀^Fin k]→L[ℝ] ℝ => f u
       map_add' := fun _ _ => by simp
       map_smul' := fun _ _ => by simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ) _

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rfl`. Consider the case `succ r ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', comp_Hk, ih]`.
-/
theorem comp_Hk_iter {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) (u : Fin k → HS L N) (r : ℕ) :
    (fun x => fr ((Hk q)^[r] ω) x u) = (hecke (toK L N) (toP L N) q)^[r] fun x => fr ω x u := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', comp_Hk, ih]

/- English proof (translation)
The claim follows from `mn_contOn (Sg q) _ fun c => pb_contOn _ hω`.
-/
theorem Hk_contOn {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ContinuousOn ω (Pos L N)) :
    ContinuousOn (Hk q ω) (Pos L N) :=
  mn_contOn (Sg q) _ fun c => pb_contOn _ hω

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `key : ∀ (h : HS L N) (v : Fin k → HS L N), Hk q ω h v = mn (Sg q) fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω h v` using `fun h v => mn_map (Sg q) ({ toFun := fun f : HS L N [⋀^Fin k]→L[ℝ] ℝ => f v map_add' := fun _ _ => by simp map_smul' := fun _ _ => by simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ) _`. Simplify using `only [intP, intS_eq, key]`. Conclude with `mn_integral (Sg q) _ fun c => intP_integ (pb_contOn _ hω) y`.
-/
theorem intP_Hk {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ContinuousOn ω (Pos L N))
    (y : Fin (k + 1) → Pos L N) :
    intP (Hk q ω) y = mn (Sg q) fun c => intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) y := by
  have key : ∀ (h : HS L N) (v : Fin k → HS L N),
      Hk q ω h v = mn (Sg q) fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω h v := fun h v =>
    mn_map (Sg q)
      ({ toFun := fun f : HS L N [⋀^Fin k]→L[ℝ] ℝ => f v
         map_add' := fun _ _ => by simp
         map_smul' := fun _ _ => by simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ) _
  simp only [intP, intS_eq, key]
  exact mn_integral (Sg q) _ fun c => intP_integ (pb_contOn _ hω) y

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `⟨Hk_contOn q hω.1, ?_⟩` and prove the remaining obligations. Establish `h1 : intP (Hk q ω) = fun y => mn (Sg q) fun c => intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) y`. Use function extensionality and compare the values at `fun y => intP_Hk q hω.1 y`. Rewrite using `[h1, dC_mn]`. Use function extensionality and compare the values at `y`.

Establish `h0 : ∀ c : Quotient (QuotientGroup.rightRel (Sg q)), dC (intP (pb (toP L N (q * toK L N (Quotient.out c))) ω)) y = 0` using `fun c => by`. Establish `e2 : intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) = fun z => intP ω fun j => toP L N (q * toK L N (Quotient.out c)) • z j`. Use function extensionality and compare the values at `fun z => intP_pb _ ω z`. Rewrite using `[e2]`. Conclude with `congrFun hω.2 (fun j => toP L N (q * toK L N (Quotient.out c)) • y j)`.

Simplify using `only [h0]`. Simplify using `[mn]`.
-/
theorem Hk_good {k : ℕ} (q : GK L N) {ω : Form (HS L N) (k + 1)} (hω : Good ω) : Good (Hk q ω) := by
  refine ⟨Hk_contOn q hω.1, ?_⟩
  have h1 : intP (Hk q ω) = fun y => mn (Sg q) fun c => intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) y :=
    funext fun y => intP_Hk q hω.1 y
  rw [h1, dC_mn]
  funext y
  have h0 : ∀ c : Quotient (QuotientGroup.rightRel (Sg q)),
      dC (intP (pb (toP L N (q * toK L N (Quotient.out c))) ω)) y = 0 := fun c => by
    have e2 : intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) =
        fun z => intP ω fun j => toP L N (q * toK L N (Quotient.out c)) • z j :=
      funext fun z => intP_pb _ ω z
    rw [e2]
    exact congrFun hω.2 (fun j => toP L N (q * toK L N (Quotient.out c)) • y j)
  simp only [h0]
  simp [mn]

end PositivityTheory.KB.JoinReconstruction

end
