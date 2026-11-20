import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulMemOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerSide
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IntegralDetModule

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Module.Basis (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) (Fin n → AE F E) :=
  Pi.basis fun _ => (Module.finBasis F E).baseChange (AF F)

def big {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) :
    Matrix (Σ _ : Fin n, Fin (Module.finrank F E)) (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) :=
  LinearMap.toMatrix (bas F E n) (bas F E n) ((Matrix.toLin' t).restrictScalars (AF F))

/- English proof (translation)
Rewrite using `[big, LinearMap.toMatrix_apply]`. Both sides reduce to the same expression.
-/
theorem big_apply {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) (x y) :
    big t x y = (bas F E n).repr (t *ᵥ bas F E n y) x := by
  rw [big, LinearMap.toMatrix_apply]
  rfl

/- English proof (translation)
Rewrite using `[big, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']`.
-/
theorem det_big {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) :
    (big t).det = Algebra.norm (AF F) t.det := by
  rw [big, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']

/- English proof (translation)
Rewrite using `[bas, Pi.basis_apply]`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = x.1`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same, Pi.single_eq_same, Module.Basis.baseChange_apply]`.

Both sides reduce to the same expression. Rewrite using `[Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]`.
-/
theorem bas_eq {n : ℕ} (x) :
    bas F E n x = fun i => inclR (F := F) (AF F) ((Pi.single x.1 (Module.finBasis F E x.2) : Fin n → E) i) := by
  rw [bas, Pi.basis_apply]
  funext i
  by_cases h : i = x.1
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, Module.Basis.baseChange_apply]
    rfl
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/- English proof (translation)
Rewrite using `[← det_big, RingHom.map_det]`. Establish `: φ.mapMatrix (big t) = 1`. Use extensionality with `x y`. Establish `h1 : u • (t *ᵥ bas F E n y) = u • bas F E n y`. Establish `h2 : (u • (t - 1)) *ᵥ bas F E n y = 0` using `by rw [ht, Matrix.zero_mulVec]`.

Rewrite `h2` using `[Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h3` using `congrArg (fun z => φ ((bas F E n).repr z x)) h1`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu, one_mul, Module.Basis.repr_self] at h3`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, big_apply, h3, Matrix.one_apply, Finsupp.single_apply]`. Distinguish the cases in `h : x = y`.

Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[this, Matrix.det_one]`.
-/
theorem map_norm_det {n : ℕ} {K : Type} [CommRing K] (φ : AF F →+* K) (t : Matrix (Fin n) (Fin n) (AE F E))
    (u : AF F) (hu : φ u = 1) (ht : u • (t - 1) = 0) : φ (Algebra.norm (AF F) t.det) = 1 := by
  rw [← det_big, RingHom.map_det]
  have : φ.mapMatrix (big t) = 1 := by
    ext x y
    have h1 : u • (t *ᵥ bas F E n y) = u • bas F E n y := by
      have h2 : (u • (t - 1)) *ᵥ bas F E n y = 0 := by rw [ht, Matrix.zero_mulVec]
      rwa [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, sub_eq_zero] at h2
    have h3 := congrArg (fun z => φ ((bas F E n).repr z x)) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu, one_mul, Module.Basis.repr_self] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, big_apply, h3, Matrix.one_apply, Finsupp.single_apply]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_one]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CoordinateEmbeddingMaps.main`. Consider the case `exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main`. Consider the case `(apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main ..)`.
-/
theorem exists_bound {n : ℕ} (W : Spc F E n) (hL : W.L.FG) (v : Pl F) :
    ∃ C : ℝ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ x, ‖evFin F v ((bas F E n).repr z x)‖ ≤ C := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main ..)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice`. Consider the case `exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice`. Consider the case `(apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice ..)`.
-/
theorem exists_mul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (y : Fin n → E) :
    ∃ D : ℤ, D ≠ 0 ∧ D • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
  | exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
  | (apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice ..)

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_bound W hL.fg v`. Use `choose D hD0 hD using fun x : (Σ _ : Fin n, Fin (Module.finrank F E)) => exists_mul_mem W.L hL (Pi.single x.1 (Module.finBasis F E x.2))`. Use `haveI : CharZero (Fv F v) := algebraRat.charZero _`. Use `⟨∑ y, |C| / ‖(D y : Fv F v)‖, fun t ht x y => ?_⟩` and prove the remaining obligations. Use `set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v) with he`.

Establish `he1 : evFin F v e = 1` using `GlobalTheory.EmbChart.evFin_atPlace v 1`. Establish `hmem : e • (D y • bas F E n y) ∈ GlobalTheory.InertSph.latAt W v`. Use `AddSubgroup.subset_closure ⟨e, ?_, ?_, _, hD y, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Rewrite using `[smul_eq_mul, mul_comm, he, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]`.

Rewrite using `[he1]`. Conclude with `one_mem _`. Rewrite using `[bas_eq]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, map_zsmul]`. Establish `h1` using `hC _ (ht _ hmem) x`. Rewrite `h1` using `[Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, map_zsmul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, map_mul, he1, one_mul, map_zsmul, zsmul_eq_mul, norm_mul, ← big_apply]`. Establish `hpos : 0 < ‖(D y : Fv F v)‖` using `norm_pos_iff.2 (Int.cast_ne_zero.2 (hD0 y))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[le_div_iff₀ hpos, mul_comm]`. Conclude with `h1.trans (le_abs_self C)`. Use `_ ≤ _ := Finset.single_le_sum (f := fun y => |C| / ‖(D y : Fv F v)‖) (fun y _ => div_nonneg (abs_nonneg _) (norm_nonneg _)) (Finset.mem_univ y)`.
-/
theorem exists_entry_bound {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) :
    ∃ C : ℝ, ∀ t : Matrix (Fin n) (Fin n) (AE F E),
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ x y, ‖evFin F v (big t x y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound W hL.fg v
  choose D hD0 hD using fun x : (Σ _ : Fin n, Fin (Module.finrank F E)) =>
    exists_mul_mem W.L hL (Pi.single x.1 (Module.finBasis F E x.2))
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  refine ⟨∑ y, |C| / ‖(D y : Fv F v)‖, fun t ht x y => ?_⟩
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v) with he
  have he1 : evFin F v e = 1 := GlobalTheory.EmbChart.evFin_atPlace v 1
  have hmem : e • (D y • bas F E n y) ∈ GlobalTheory.InertSph.latAt W v := by
    refine AddSubgroup.subset_closure ⟨e, ?_, ?_, _, hD y, ?_⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, he, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [he1]; exact one_mem _
    · rw [bas_eq]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_zsmul]
  have h1 := hC _ (ht _ hmem) x
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, map_zsmul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    map_mul, he1, one_mul, map_zsmul, zsmul_eq_mul, norm_mul, ← big_apply] at h1
  have hpos : 0 < ‖(D y : Fv F v)‖ := norm_pos_iff.2 (Int.cast_ne_zero.2 (hD0 y))
  calc ‖evFin F v (big t x y)‖ ≤ |C| / ‖(D y : Fv F v)‖ := by
        rw [le_div_iff₀ hpos, mul_comm]; exact h1.trans (le_abs_self C)
    _ ≤ _ := Finset.single_le_sum (f := fun y => |C| / ‖(D y : Fv F v)‖)
        (fun y _ => div_nonneg (abs_nonneg _) (norm_nonneg _)) (Finset.mem_univ y)

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_entry_bound W hL v`. Establish `hk : ∀ k : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ k) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z hz`.

Simplify using `using hz`. Consider the case `succ k ih => intro z hz`. Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec]`. Conclude with `ih _ (ht z hz)`. Establish `hb : ∃ B : ℝ, ∀ k : ℕ, ‖evFin F v (Algebra.norm (AF F) t.det)‖ ^ k ≤ B`.

Use `⟨(Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E))).factorial • C ^ Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E)), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← norm_pow, ← map_pow, ← map_pow, ← Matrix.det_pow, ← det_big]`. Use `Matrix.det_le (abv := (NormedField.toAbsoluteValue (Fv F v))) (A := (big (t ^ k)).map (evFin F v)) (x := C) (fun x y => hC _ (hk k) x y)` as an intermediate fact. Establish `e : evFin F v (big (t ^ k)).det = ((big (t ^ k)).map (evFin F v)).det` using `RingHom.map_det (evFin F v).toRingHom _`. Rewrite using `[e]`.

Conclude with `this`. Take `⟨B, hB⟩` from `hb`. Assume the negation of the conclusion as `h`. Take `⟨k, hk⟩` from `((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 h)).eventually_gt_atTop B).exists`. Conclude with `absurd (hB k) (not_le.2 hk)`.
-/
theorem norm_le_one {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) (t : Matrix (Fin n) (Fin n) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ‖evFin F v (Algebra.norm (AF F) t.det)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_entry_bound W hL v
  have hk : ∀ k : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ k) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih => intro z hz; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (ht z hz)
  have hb : ∃ B : ℝ, ∀ k : ℕ, ‖evFin F v (Algebra.norm (AF F) t.det)‖ ^ k ≤ B := by
    refine ⟨(Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E))).factorial •
      C ^ Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E)), fun k => ?_⟩
    rw [← norm_pow, ← map_pow, ← map_pow, ← Matrix.det_pow, ← det_big]
    have := Matrix.det_le (abv := (NormedField.toAbsoluteValue (Fv F v))) (A := (big (t ^ k)).map (evFin F v)) (x := C)
      (fun x y => hC _ (hk k) x y)
    have e : evFin F v (big (t ^ k)).det = ((big (t ^ k)).map (evFin F v)).det :=
      RingHom.map_det (evFin F v).toRingHom _
    rw [e]
    exact this
  obtain ⟨B, hB⟩ := hb
  by_contra h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 h)).eventually_gt_atTop B).exists
  exact absurd (hB k) (not_le.2 hk)

/- English proof (translation)
Apply `NNReal.eq` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) = _`. Rewrite using `[GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]`. Establish `h3 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(a : AF F).2 v‖ = 1` using `h2`. Establish `h4 : ∀ w : InfinitePlace F, ‖(a : AF F).1 w‖ = 1` using `fun w => by`.

Rewrite using `[h1]`. Conclude with `norm_one`. Simplify using `only [h3, h4, one_pow, Finset.prod_const_one, finprod_one, mul_one, NNReal.coe_one]`.
-/
theorem modu_eq_one (a : (AF F)ˣ) (h1 : (a : AF F).1 = 1) (h2 : ∀ v, ‖evFin F v a‖ = 1) :
    (adeleClass F).modu a = 1 := by
  apply NNReal.eq
  change (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(a : AF F).2 v‖ = 1 := h2
  have h4 : ∀ w : InfinitePlace F, ‖(a : AF F).1 w‖ = 1 := fun w => by
    rw [h1]; exact norm_one
  simp only [h3, h4, one_pow, Finset.prod_const_one, finprod_one, mul_one, NNReal.coe_one]

/- English proof (translation)
Establish `h0` using `h1 (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])`. Apply `modu_eq_one` to reduce the goal to its premises. Use `map_norm_det (fstA F).toRingHom _ _ ?_ h0` and prove the remaining obligations. Rewrite using `[map_sub, map_one, sub_eq_self]`. Both sides reduce to the same expression.

Introduce `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Establish `a1` using `norm_le_one W hL u _ fun z hz => (h2 z hz).1`. Establish `a2` using `norm_le_one W hL u _ fun z hz => (h2 z hz).2`.

Establish `a3 : ‖evFin F u (Algebra.norm (AF F) (t : Matrix (Fin n) (Fin n) (AE F E)).det)‖ * ‖evFin F u (Algebra.norm (AF F) ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).det)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, map_one, norm_one]`. Use `le_antisymm a1 ?_` and prove the remaining obligations. Rewrite using `[← a3]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) a2`.

Use `map_norm_det (evFin F u).toRingHom _ _ (by` as an intermediate fact. Rewrite using `[map_sub, map_one, sub_eq_self]`. Conclude with `evalV_singleFin_ne hu 1) h0`. Conclude with `(congrArg norm this).trans norm_one`.
-/
theorem modu_norm_det {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) (t : GL (Fin n) (AE F E))
    (h1 : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1))
    (h2 : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  have h0 := h1 (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  apply modu_eq_one
  · refine map_norm_det (fstA F).toRingHom _ _ ?_ h0
    rw [map_sub, map_one, sub_eq_self]
    rfl
  · intro u
    by_cases hu : u = v
    · subst hu
      have a1 := norm_le_one W hL u _ fun z hz => (h2 z hz).1
      have a2 := norm_le_one W hL u _ fun z hz => (h2 z hz).2
      have a3 : ‖evFin F u (Algebra.norm (AF F) (t : Matrix (Fin n) (Fin n) (AE F E)).det)‖ *
          ‖evFin F u (Algebra.norm (AF F) ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).det)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, map_one, norm_one]
      refine le_antisymm a1 ?_
      rw [← a3]
      exact mul_le_of_le_one_right (norm_nonneg _) a2
    · have := map_norm_det (evFin F u).toRingHom _ _ (by
        rw [map_sub, map_one, sub_eq_self]
        exact evalV_singleFin_ne hu 1) h0
      exact (congrArg norm this).trans norm_one

end GlobalTheory.IntegralDetModule

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ _ t ht`. Conclude with `GlobalTheory.IntegralDetModule.modu_norm_det G.W hT.geo.hW.lat v t ht.1 ht.2`.
-/
theorem GlobalTheory.IntegralDetModule.modu_norm_det_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ _ t ht
  exact GlobalTheory.IntegralDetModule.modu_norm_det G.W hT.geo.hW.lat v t ht.1 ht.2

end
