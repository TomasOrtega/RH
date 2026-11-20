import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelVolMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuationStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TupleJac

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Take `⟨ω, hω, e, he, hωe⟩` from `GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L`. Establish `hinj` using `GlobalTheory.UnramOrder.algebraMap_inj L`. Establish `hu : IsUnit (ω - L.cj ω)` using `IsUnit.of_mul_eq_one e hωe`. Establish `hli : LinearIndependent F ![(1 : E), ω]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `a b h`. Simplify using `only [Algebra.smul_def, mul_one] at h`. Establish `h'` using `congrArg L.cj h`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'`. Establish `hb : algebraMap F E b = 0` using `hu.mul_left_eq_zero.1 (by linear_combination h - h')`.

Establish `ha : algebraMap F E a = 0` using `by rw [hb] at h; simpa using h`. Conclude with `⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩`. Set `c : Module.Basis (Fin 2) F E` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])`. Establish `hc0 : c 0 = 1` using `by simp [c]`. Establish `hc1 : c 1 = ω` using `by simp [c]`.

Establish `hx : ∀ x, x = algebraMap F E (c.repr x 0) + algebraMap F E (c.repr x 1) * ω`. Introduce `x`. Use `c.sum_repr x` as an intermediate fact. Simplify using `only [Fin.sum_univ_two, hc0, hc1, Algebra.smul_def, mul_one] at this`. Conclude with `this.symm`.

Establish `hr : ∀ a b : F, c.repr (algebraMap F E a + algebraMap F E b * ω) 0 = a ∧ c.repr (algebraMap F E a + algebraMap F E b * ω) 1 = b`. Introduce `a b`. Establish `: algebraMap F E a + algebraMap F E b * ω = a • c 0 + b • c 1`. Simplify using `[hc0, hc1, Algebra.smul_def]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Use `⟨c, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg L.cj (hx x)`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes] at h1`. Establish `hb : algebraMap F E (c.repr x 1) ∈ L.O`.

Establish `: algebraMap F E (c.repr x 1) = (x - L.cj x) * e`. Take the linear combination `(-e) * hx x + e * h1 - algebraMap F E (c.repr x 1) * hωe`. Rewrite using `[this]`. Conclude with `L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he`. Establish `ha : algebraMap F E (c.repr x 0) ∈ L.O`.

Establish `: algebraMap F E (c.repr x 0) = x - algebraMap F E (c.repr x 1) * ω`. Take the linear combination `- hx x`. Rewrite using `[this]`. Conclude with `L.O.sub_mem h (L.O.mul_mem hb hω)`. Introduce `i`.

Use `fin_cases i`. Conclude with `(GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 ha`. Conclude with `(GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hb`. Rewrite using `[hx x]`. Conclude with `L.O.add_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 0)) (L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 1)) hω)`.

Take `⟨t, ht⟩` from `(L.cj_fix (ω + L.cj ω)).1 (by simp [L.cj_cj, add_comm])`. Take `⟨N, hN⟩` from `(L.cj_fix (ω * L.cj ω)).1 (by simp [L.cj_cj, mul_comm])`. Take `⟨a, b, rfl⟩ : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * ω` from `⟨_, _, hx x⟩`. Establish `h2 : (algebraMap F E a + algebraMap F E b * ω) * ω = algebraMap F E (-(b * N)) + algebraMap F E (a + b * t) * ω`. Simplify using `only [map_add, map_mul, map_neg, ht, hN]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Algebra.norm_eq_matrix_det c, Matrix.det_fin_two]`. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hc1, mul_one, h2, (hr _ _).1, (hr _ _).2]`. Simplify using `only [map_add, map_mul, map_neg, map_sub, ht, hN, AlgEquiv.commutes]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ c : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, c.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hu : IsUnit (ω - L.cj ω) := IsUnit.of_mul_eq_one e hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'
    have hb : algebraMap F E b = 0 := hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap F E a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  let c : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = ω := by simp [c]
  have hx : ∀ x, x = algebraMap F E (c.repr x 0) + algebraMap F E (c.repr x 1) * ω := by
    intro x
    have := c.sum_repr x
    simp only [Fin.sum_univ_two, hc0, hc1, Algebra.smul_def, mul_one] at this
    exact this.symm
  have hr : ∀ a b : F, c.repr (algebraMap F E a + algebraMap F E b * ω) 0 = a ∧
      c.repr (algebraMap F E a + algebraMap F E b * ω) 1 = b := by
    intro a b
    have : algebraMap F E a + algebraMap F E b * ω = a • c 0 + b • c 1 := by
      simp [hc0, hc1, Algebra.smul_def]
    rw [this]
    simp
  refine ⟨c, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg L.cj (hx x)
    simp only [map_add, map_mul, AlgEquiv.commutes] at h1
    have hb : algebraMap F E (c.repr x 1) ∈ L.O := by
      have : algebraMap F E (c.repr x 1) = (x - L.cj x) * e := by
        linear_combination (-e) * hx x + e * h1 - algebraMap F E (c.repr x 1) * hωe
      rw [this]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have ha : algebraMap F E (c.repr x 0) ∈ L.O := by
      have : algebraMap F E (c.repr x 0) = x - algebraMap F E (c.repr x 1) * ω := by
        linear_combination - hx x
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem hb hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 ha
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hb
  · rw [hx x]
    exact L.O.add_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 0))
      (L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 1)) hω)
  · obtain ⟨t, ht⟩ := (L.cj_fix (ω + L.cj ω)).1 (by simp [L.cj_cj, add_comm])
    obtain ⟨N, hN⟩ := (L.cj_fix (ω * L.cj ω)).1 (by simp [L.cj_cj, mul_comm])
    obtain ⟨a, b, rfl⟩ : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * ω := ⟨_, _, hx x⟩
    have h2 : (algebraMap F E a + algebraMap F E b * ω) * ω
        = algebraMap F E (-(b * N)) + algebraMap F E (a + b * t) * ω := by
      simp only [map_add, map_mul, map_neg, ht, hN]; ring
    rw [Algebra.norm_eq_matrix_det c, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hc1, mul_one, h2, (hr _ _).1, (hr _ _).2]
    simp only [map_add, map_mul, map_neg, map_sub, ht, hN, AlgEquiv.commutes]
    ring

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `(GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ`. Establish `hli : LinearIndependent E b`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Set `f : (Fin n → E) →ₗ[E] E` to `{ toFun := fun x => hf L Hm x (b j) map_add' := fun x y => by simp [hf, add_mul, Finset.sum_add_distrib] map_smul' := fun c x => by simp [hf, Finset.mul_sum, mul_assoc] }`.

Establish `hfb : ∀ i, f (b i) = if i = j then 1 else 0` using `fun i => hb i j`. Use `congrArg f hg` as an intermediate fact. Simplify `this` using `[map_sum, hfb]`. Establish `hsp : ⊤ ≤ Submodule.span E (Set.range b)`. Rewrite using `[← hΛ.1.2, Submodule.span_span_of_tower]`.

Use `⟨Module.Basis.mk hli hsp, fun x => ?_⟩` and prove the remaining obligations. Use `set B := Module.Basis.mk hli hsp with hB`. Establish `hBb : ∀ i, B i = b i` using `fun i => by simp [hB]`. Prove the components needed by the constructor for the conclusion. Introduce `hx i`.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hx`. Establish `: ∑ j, c j • b j = ∑ j, (c j : E) • B j` using `by simp only [hBb]; rfl`. Rewrite using `[this, B.repr_sum_self]`. Conclude with `(c i).2`. Introduce `hx`.

Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hx i⟩, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← B.sum_repr x]`. Simplify using `only [hBb]`. Both sides reduce to the same expression.
-/
theorem exists_lat_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) :
    ∃ B : Module.Basis (Fin n) E (Fin n → E), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ L.O := by
  obtain ⟨b, hb, rfl⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
  have hli : LinearIndependent E b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun x => hf L Hm x (b j)
        map_add' := fun x y => by simp [hf, add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [hf, Finset.mul_sum, mul_assoc] }
    have hfb : ∀ i, f (b i) = if i = j then 1 else 0 := fun i => hb i j
    have := congrArg f hg
    simpa [map_sum, hfb] using this
  have hsp : ⊤ ≤ Submodule.span E (Set.range b) := by
    rw [← hΛ.1.2, Submodule.span_span_of_tower]
  refine ⟨Module.Basis.mk hli hsp, fun x => ?_⟩
  set B := Module.Basis.mk hli hsp with hB
  have hBb : ∀ i, B i = b i := fun i => by simp [hB]
  constructor
  · intro hx i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    have : ∑ j, c j • b j = ∑ j, (c j : E) • B j := by simp only [hBb]; rfl
    rw [this, B.repr_sum_self]
    exact (c i).2
  · intro hx
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hx i⟩, ?_⟩
    conv_rhs => rw [← B.sum_repr x]
    simp only [hBb]; rfl

/- English proof (translation)
Take `⟨c, hc, hN⟩` from `exists_int_basis L`. Take `⟨B, hB⟩` from `exists_lat_basis L Hm hH Λ hΛ`. Use `L.free` as an intermediate fact. Establish `h` using `GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => c.smulTower B) (φ.restrictScalars F) a u (by`. Apply `GlobalTheory.UnramOrder.algebraMap_inj L` to reduce the goal to its premises.

Rewrite using `[← hd, ← hN, ← LinearMap.det_restrictScalars]`. Use the proof step `rfl) (tupLat L Λ m) (by`. Introduce `x`. Simplify using `only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_toAddSubgroup, hB, hc, Pi.basis_repr, Module.Basis.smulTower_repr]`. Conclude with `⟨fun h i => h _ _ _, fun h j i k => h ⟨j, (k, i)⟩⟩)`.

Introduce `T hT`. Establish `h2` using `GlobalTheory.HL.ContAut.cont_image (tupLat L Λ m) (φ.restrictScalars F).toAddEquiv h.1 h.2.1 T hT`. Rewrite `h2` using `[h.2.2]`. Conclude with `h2`.
-/
theorem cont_linearEquiv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (m : ℕ) (φ : (Fin m → Fin n → E) ≃ₗ[E] (Fin m → Fin n → E))
    (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det φ.toLinearMap * L.cj (LinearMap.det φ.toLinearMap)
      = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) (φ '' T) ∧
      cont (tupLat L Λ m) (φ '' T) = (resQ ϖ : ℝ) ^ (-a) * cont (tupLat L Λ m) T := by
  obtain ⟨c, hc, hN⟩ := exists_int_basis L
  obtain ⟨B, hB⟩ := exists_lat_basis L Hm hH Λ hΛ
  have := L.free
  have h := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => c.smulTower B) (φ.restrictScalars F) a u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hd, ← hN, ← LinearMap.det_restrictScalars]
      rfl) (tupLat L Λ m) (by
      intro x
      simp only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff,
        Submodule.mem_toAddSubgroup, hB, hc, Pi.basis_repr, Module.Basis.smulTower_repr]
      exact ⟨fun h i => h _ _ _, fun h j i k => h ⟨j, (k, i)⟩⟩)
  intro T hT
  have h2 := GlobalTheory.HL.ContAut.cont_image (tupLat L Λ m) (φ.restrictScalars F).toAddEquiv h.1 h.2.1 T hT
  rw [h.2.2] at h2
  exact h2

def rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (Fin m → Fin n → E) →ₗ[E] (Fin m → Fin n → E) where
  toFun x := rmul x A
  map_add' x y := by ext j k; simp [rmul, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext j k; simp [rmul, Finset.mul_sum, mul_left_comm]

def swapL (n m : ℕ) : (Fin n → Fin m → E) ≃ₗ[E] (Fin m → Fin n → E) where
  toFun x := fun j k => x k j
  invFun x := fun j k => x k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace E] in
/- English proof (translation)
Establish `h : rmulL (n` using `n) A = (swapL n m).toLinearMap ∘ₗ (LinearMap.pi fun i : Fin n => (Matrix.toLin' A.transpose) ∘ₗ LinearMap.proj i) ∘ₗ (swapL n m).symm.toLinearMap := by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use extensionality with `j k`. Simplify using `[rmulL, rmul, swapL, Matrix.mulVec, dotProduct]`. Rewrite using `[h, LinearMap.det_conj, LinearMap.det_pi]`.

Simplify using `[LinearMap.det_toLin']`.
-/
theorem det_rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulL (n := n) A) = A.det ^ n := by
  have h : rmulL (n := n) A = (swapL n m).toLinearMap ∘ₗ
      (LinearMap.pi fun i : Fin n => (Matrix.toLin' A.transpose) ∘ₗ LinearMap.proj i) ∘ₗ
      (swapL n m).symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    ext j k
    simp [rmulL, rmul, swapL, Matrix.mulVec, dotProduct]
  rw [h, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

/- English proof (translation)
Use `set M := LinearMap.toMatrix' g.toLinearMap with hM`. Establish `h : M.transpose * Hm * (L.cj.toRingEquiv.toRingHom.mapMatrix M) = Hm`. Use extensionality with `i j`. Establish `h1` using `hg (Pi.single i 1) (Pi.single j 1)`. Establish `h2 : hf L Hm (Pi.single i 1) (Pi.single j 1) = Hm i j`.

Simplify using `[hf, Pi.single_apply, apply_ite L.cj]`. Rewrite `h1` using `[h2]`. Rewrite using `[← h1, hf, Finset.sum_comm]`. Simplify using `[hM, Matrix.mul_apply, Finset.sum_mul, LinearMap.toMatrix'_apply]`. Establish `h3` using `congrArg Matrix.det h`.

Rewrite `h3` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hM, LinearMap.det_toMatrix']`. Use `hH.mul_left_cancel ?_` and prove the remaining obligations. Rewrite using `[mul_one]`. Use `conv_rhs => rw [← h3]`. Simplify using `only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.toRingEquiv_eq_coe]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_isom (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (hH : IsUnit Hm.det)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : g ∈ isomG L Hm) :
    LinearMap.det g.toLinearMap * L.cj (LinearMap.det g.toLinearMap) = 1 := by
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  have h : M.transpose * Hm * (L.cj.toRingEquiv.toRingHom.mapMatrix M) = Hm := by
    ext i j
    have h1 := hg (Pi.single i 1) (Pi.single j 1)
    have h2 : hf L Hm (Pi.single i 1) (Pi.single j 1) = Hm i j := by
      simp [hf, Pi.single_apply, apply_ite L.cj]
    rw [h2] at h1
    rw [← h1, hf, Finset.sum_comm]
    simp [hM, Matrix.mul_apply, Finset.sum_mul, LinearMap.toMatrix'_apply]
  have h3 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hM,
    LinearMap.det_toMatrix'] at h3
  refine hH.mul_left_cancel ?_
  rw [mul_one]
  conv_rhs => rw [← h3]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.toRingEquiv_eq_coe]
  ring

end GlobalTheory.HL.TupleJac

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m`. Use `⟨fun A hA => ?_, fun g hg T hT => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `(L.cj_fix (A.det * L.cj A.det)).1 (by simp [L.cj_cj, mul_comm])`. Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)`. Establish `hN0 : N ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hN` using `[map_zero]`. Conclude with `(hA.mul (hA.map L.cj)).ne_zero hN.symm`. Take `⟨u, hu⟩` from `(GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 N hN0`. Establish `hdet : IsUnit (LinearMap.det (TupleJac.rmulL (n` using `n) A)) := by`.

Rewrite using `[TupleJac.det_rmulL]`. Conclude with `hA.pow n`. Establish `hφ : (LinearMap.equivOfIsUnitDet hdet).toLinearMap = TupleJac.rmulL (n` using `n) A := LinearMap.coe_equivOfIsUnitDet hdet`. Establish `key` using `TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearMap.equivOfIsUnitDet hdet) (vE L ϖ (A.det * L.cj A.det) * n) (u ^ n) (by`. Rewrite using `[hφ, TupleJac.det_rmulL, map_pow, ← mul_pow, ← hN, ← map_pow]`.

Use `congr 1`. Use `conv_lhs => rw [hu]`. Rewrite using `[mul_pow, zpow_mul, zpow_natCast]`. Use the proof step `simp)`. Establish `hfun : (LinearMap.equivOfIsUnitDet hdet : _ → _) = fun x => rmul x A`.

Use function extensionality and compare the values at `fun x => LinearMap.congr_fun hφ x`. Rewrite `key` using `[hfun]`. Conclude with `key`. Establish `key` using `TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearEquiv.piCongrRight fun _ => g) 0 1 (by`. Establish `h : (LinearEquiv.piCongrRight fun _ : Fin m => g).toLinearMap = LinearMap.pi fun i : Fin m => g.toLinearMap ∘ₗ LinearMap.proj i` using `rfl`.

Rewrite using `[h, LinearMap.det_pi, Finset.prod_const, map_pow, ← mul_pow, TupleJac.det_isom L Hm hH.2 g hg]`. Use the proof step `simp) T hT`. Rewrite `key` using `[neg_zero, zpow_zero, one_mul]`. Conclude with `key`.
-/
theorem GlobalTheory.HL.TupleJac.tuple_jacobian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m
  refine ⟨fun A hA => ?_, fun g hg T hT => ?_⟩
  · obtain ⟨N, hN⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by simp [L.cj_cj, mul_comm])
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [map_zero] at hN
      exact (hA.mul (hA.map L.cj)).ne_zero hN.symm
    obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 N hN0
    have hdet : IsUnit (LinearMap.det (TupleJac.rmulL (n := n) A)) := by
      rw [TupleJac.det_rmulL]; exact hA.pow n
    have hφ : (LinearMap.equivOfIsUnitDet hdet).toLinearMap = TupleJac.rmulL (n := n) A :=
      LinearMap.coe_equivOfIsUnitDet hdet
    have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearMap.equivOfIsUnitDet hdet)
      (vE L ϖ (A.det * L.cj A.det) * n) (u ^ n) (by
        rw [hφ, TupleJac.det_rmulL, map_pow, ← mul_pow, ← hN, ← map_pow]
        congr 1
        conv_lhs => rw [hu]
        rw [mul_pow, zpow_mul, zpow_natCast]
        simp)
    have hfun : (LinearMap.equivOfIsUnitDet hdet : _ → _) = fun x => rmul x A :=
      funext fun x => LinearMap.congr_fun hφ x
    rw [hfun] at key
    exact key
  · have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m
      (LinearEquiv.piCongrRight fun _ => g) 0 1 (by
        have h : (LinearEquiv.piCongrRight fun _ : Fin m => g).toLinearMap =
            LinearMap.pi fun i : Fin m => g.toLinearMap ∘ₗ LinearMap.proj i := rfl
        rw [h, LinearMap.det_pi, Finset.prod_const, map_pow, ← mul_pow,
          TupleJac.det_isom L Hm hH.2 g hg]
        simp) T hT
    rw [neg_zero, zpow_zero, one_mul] at key
    exact key
