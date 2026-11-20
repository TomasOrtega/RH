import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LatticeCosetUniformizer

namespace GlobalTheory.MinusculeCosetsProof

open Matrix IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer

section General

variable {O F : Type} [CommRing O] [Field F] [Algebra O F] {n : ℕ}

def intLattice (F : Type) [Field F] [Algebra O F] (A : Matrix (Fin n) (Fin n) O) :
    Submodule O (Fin n → F) :=
  LinearMap.range ((inclVec O F n).comp A.mulVecLin)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_intLattice (A : Matrix (Fin n) (Fin n) O) (x : Fin n → F) :
    x ∈ intLattice F A ↔ ∃ v, inclVec O F n (A *ᵥ v) = x := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inclVec_apply (v : Fin n → O) (i : Fin n) : inclVec O F n v i = algebraMap O F (v i) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[inclVec_apply, Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem inclVec_mulVec (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O) :
    inclVec O F n (A *ᵥ v) = A.map (algebraMap O F) *ᵥ inclVec O F n v := by
  funext i
  simp [inclVec_apply, Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_scaleBy (a : O) (L : Submodule O (Fin n → F)) (x : Fin n → F) :
    x ∈ scaleBy O a L ↔ ∃ y ∈ L, a • y = x := Iff.rfl

/- English proof (translation)
Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `(mem_scaleBy a L' _).1 (h ((mem_scaleBy a L _).2 ⟨x, hx, rfl⟩))`. Establish `: y = x`. Use function extensionality and compare the values at `i`. Use `congrFun hxy i` as an intermediate fact.

Simplify using `only [Pi.smul_apply, Algebra.smul_def] at this`. Conclude with `mul_left_cancel₀ ha this`. Conclude with `this ▸ hy`.
-/
theorem le_of_scaleBy_le {a : O} (ha : algebraMap O F a ≠ 0) {L L' : Submodule O (Fin n → F)}
    (h : scaleBy O a L ≤ scaleBy O a L') : L ≤ L' := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_scaleBy a L' _).1 (h ((mem_scaleBy a L _).2 ⟨x, hx, rfl⟩))
  have : y = x := by
    funext i
    have := congrFun hxy i
    simp only [Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ ha this
  exact this ▸ hy

/- English proof (translation)
Establish `key : ∀ v : Fin n → O, a • (((Matrix.GeneralLinearGroup.map (algebraMap O F) k * t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i))) = inclVec O F n (((k : Matrix (Fin n) (Fin n) O) * D) *ᵥ v)`. Introduce `v`. Rewrite using `[inclVec_mulVec, Matrix.map_mul, ← hD, Matrix.mul_smul, Matrix.smul_mulVec]`. Both sides reduce to the same expression. Use extensionality with `x`.

Rewrite using `[mem_scaleBy, mem_intLattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨v, rfl⟩` from `(mem_latticeOf O _ _).1 hy`. Conclude with `⟨v, (key v).symm⟩`.

Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨_, (mem_latticeOf O _ _).2 ⟨v, rfl⟩, key v⟩`.
-/
theorem scaleBy_latticeOf {a : O} {t : GL (Fin n) F} {D : Matrix (Fin n) (Fin n) O}
    (hD : a • (t : Matrix (Fin n) (Fin n) F) = D.map (algebraMap O F)) (k : GL (Fin n) O) :
    scaleBy O a (latticeOf O (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t)) =
      intLattice F ((k : Matrix (Fin n) (Fin n) O) * D) := by
  have key : ∀ v : Fin n → O,
      a • (((Matrix.GeneralLinearGroup.map (algebraMap O F) k * t : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i))) =
      inclVec O F n (((k : Matrix (Fin n) (Fin n) O) * D) *ᵥ v) := by
    intro v
    rw [inclVec_mulVec, Matrix.map_mul, ← hD, Matrix.mul_smul, Matrix.smul_mulVec]
    rfl
  ext x
  rw [mem_scaleBy, mem_intLattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_latticeOf O _ _).1 hy
    exact ⟨v, (key v).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, (mem_latticeOf O _ _).2 ⟨v, rfl⟩, key v⟩

/- English proof (translation)
Take `⟨_, ⟨k, rfl⟩, k₂, hk₂, rfl⟩` from `hg`. Conclude with `⟨k, latticeOf_mul O _ _ hk₂⟩`.
-/
theorem exists_of_mem_doubleCosetK {t g : GL (Fin n) F} (hg : g ∈ doubleCosetK O t) :
    ∃ k : GL (Fin n) O,
      latticeOf O g = latticeOf O (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t) := by
  obtain ⟨_, ⟨k, rfl⟩, k₂, hk₂, rfl⟩ := hg
  exact ⟨k, latticeOf_mul O _ _ hk₂⟩

/- English proof (translation)
Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `⟨A *ᵥ v, rfl⟩`.
-/
theorem intLattice_le_std (A : Matrix (Fin n) (Fin n) O) : intLattice F A ≤ stdLattice O F n := by
  rintro _ ⟨v, rfl⟩
  exact ⟨A *ᵥ v, rfl⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨_, ⟨v, rfl⟩, rfl⟩` from `(mem_scaleBy _ _ _).1 hx`. Use `⟨(D' * ((k⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) *ᵥ v, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul]`. Express the relevant statement in the definitionally equal form `inclVec O F n _ = _`.

Use `congr 1`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc D, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Units.mul_inv, Matrix.smul_mulVec, Matrix.one_mulVec]`.
-/
theorem scaleBy_std_le_intLattice {ϖ : O} {D D' : Matrix (Fin n) (Fin n) O}
    (h : D * D' = ϖ • (1 : Matrix (Fin n) (Fin n) O)) (k : GL (Fin n) O) :
    scaleBy O ϖ (stdLattice O F n) ≤ intLattice F ((k : Matrix (Fin n) (Fin n) O) * D) := by
  intro x hx
  obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := (mem_scaleBy _ _ _).1 hx
  refine ⟨(D' * ((k⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) *ᵥ v, ?_⟩
  rw [← map_smul]
  change inclVec O F n _ = _
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc D, h,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Units.mul_inv, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/- English proof (translation)
Establish `: ∀ j : Fin n, ∃ v : Fin n → O, (g : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i)) = (g' : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F ((Pi.single j 1 : Fin n → O) i))` using `fun j => (mem_latticeOf O _ _).1 (h ((mem_latticeOf O _ _).2 ⟨_, rfl⟩))`. Use `choose v hv using this`. Use `⟨Matrix.of fun i j => v j i, ?_⟩` and prove the remaining obligations. Establish `h2 : (g : Matrix (Fin n) (Fin n) F) * (Matrix.of fun i j => v j i).map (algebraMap O F) = g'`. Use extensionality with `i j`.

Use `congrFun (hv j) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, apply_ite]`. Rewrite using `[Units.val_mul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`.
-/
theorem exists_int_of_latticeOf_le {g g' : GL (Fin n) F} (h : latticeOf O g' ≤ latticeOf O g) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A.map (algebraMap O F) := by
  have : ∀ j : Fin n, ∃ v : Fin n → O,
      (g : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i)) =
        (g' : Matrix (Fin n) (Fin n) F) *ᵥ
          (fun i => algebraMap O F ((Pi.single j 1 : Fin n → O) i)) := fun j =>
    (mem_latticeOf O _ _).1 (h ((mem_latticeOf O _ _).2 ⟨_, rfl⟩))
  choose v hv using this
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  have h2 : (g : Matrix (Fin n) (Fin n) F) *
      (Matrix.of fun i j => v j i).map (algebraMap O F) = g' := by
    ext i j
    have := congrFun (hv j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, apply_ite] using this
  rw [Units.val_mul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[QuotientGroup.eq]`. Take `⟨A, hA⟩` from `exists_int_of_latticeOf_le h.ge`. Take `⟨B, hB⟩` from `exists_int_of_latticeOf_le h.le`. Establish `hAB : A * B = 1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises.

Simplify using `only [Matrix.map_mul]`. Rewrite using `[← hA, ← hB, ← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `hBA : B * A = 1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises.

Simplify using `only [Matrix.map_mul]`. Rewrite using `[← hA, ← hB, ← Units.val_mul]`. Simplify using the standard rewrite rules. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Use `ext1`.

Conclude with `hA.symm`.
-/
theorem mk_eq_of_latticeOf_eq (hinj : Function.Injective (algebraMap O F)) {g g' : GL (Fin n) F}
    (h : latticeOf O g = latticeOf O g') :
    (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL O F n) = QuotientGroup.mk g' := by
  rw [QuotientGroup.eq]
  obtain ⟨A, hA⟩ := exists_int_of_latticeOf_le h.ge
  obtain ⟨B, hB⟩ := exists_int_of_latticeOf_le h.le
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    simp only [Matrix.map_mul]
    rw [← hA, ← hB, ← Units.val_mul]
    simp
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    simp only [Matrix.map_mul]
    rw [← hA, ← hB, ← Units.val_mul]
    simp
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext1
  exact hA.symm

variable [IsLocalRing O]

/- English proof (translation)
Introduce `v w h`. Use function extensionality and compare the values at `i`. Conclude with `hinj (congrFun h i)`.
-/
theorem inclVec_injective (hinj : Function.Injective (algebraMap O F)) :
    Function.Injective (inclVec O F n) := by
  intro v w h
  funext i
  exact hinj (congrFun h i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem residue_mulVec (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O) :
    (fun i => residue O ((A *ᵥ v) i)) = A.map (residue O) *ᵥ fun i => residue O (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, ⟨u, hu⟩, rfl⟩`. Establish `: A *ᵥ u = v` using `inclVec_injective hinj hu`. Substitute `this` using the available equality.

Conclude with `⟨_, (residue_mulVec A u).symm⟩`. Introduce and unpack `⟨u, rfl⟩ choose v hv using fun i => residue_surjective (u i)`. Use `⟨A *ᵥ v, ⟨v, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[residue_mulVec, Matrix.mulVecLin_apply]`. Use `congr 1`.

Conclude with `funext hv`.
-/
theorem reduction_intLattice (hinj : Function.Injective (algebraMap O F))
    (A : Matrix (Fin n) (Fin n) O) :
    reduction O (intLattice F A) = LinearMap.range (A.map (residue O)).mulVecLin := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, hu⟩, rfl⟩
    have : A *ᵥ u = v := inclVec_injective hinj hu
    subst this
    exact ⟨_, (residue_mulVec A u).symm⟩
  · rintro ⟨u, rfl⟩
    choose v hv using fun i => residue_surjective (u i)
    refine ⟨A *ᵥ v, ⟨v, rfl⟩, ?_⟩
    rw [residue_mulVec, Matrix.mulVecLin_apply]
    congr 1
    exact funext hv

/- English proof (translation)
Introduce `x hx`. Take `⟨v, rfl⟩` from `h1 hx`. Take `⟨v', hv', e⟩` from `h (show (fun i => residue O (v i)) ∈ reduction O L from ⟨v, hx, rfl⟩)`. Establish `: ∀ i, ∃ c, v i - v' i = ϖ * c` using `fun i => hm _ (by`. Rewrite using `[← residue_eq_zero_iff, map_sub, sub_eq_zero]`.

Conclude with `(congrFun e i).symm)`. Use `choose c hc using this`. Establish `hv : v = v' + ϖ • c`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hc i]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hv, map_add, map_smul]`. Conclude with `L'.add_mem hv' (h2 ((mem_scaleBy _ _ _).2 ⟨_, ⟨c, rfl⟩, rfl⟩))`.
-/
theorem le_of_reduction_le {ϖ : O} (hm : ∀ x ∈ maximalIdeal O, ϖ ∣ x)
    {L L' : Submodule O (Fin n → F)} (h1 : L ≤ stdLattice O F n)
    (h2 : scaleBy O ϖ (stdLattice O F n) ≤ L') (h : reduction O L ≤ reduction O L') : L ≤ L' := by
  intro x hx
  obtain ⟨v, rfl⟩ := h1 hx
  obtain ⟨v', hv', e⟩ := h (show (fun i => residue O (v i)) ∈ reduction O L from ⟨v, hx, rfl⟩)
  have : ∀ i, ∃ c, v i - v' i = ϖ * c := fun i => hm _ (by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact (congrFun e i).symm)
  choose c hc using this
  have hv : v = v' + ϖ • c := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hc i]
    ring
  rw [hv, map_add, map_smul]
  exact L'.add_mem hv' (h2 ((mem_scaleBy _ _ _).2 ⟨_, ⟨c, rfl⟩, rfl⟩))

/- English proof (translation)
Use `(Matrix.GeneralLinearGroup.map (residue O) k).isUnit` as an intermediate fact. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 this`.
-/
theorem isUnit_det_map (k : GL (Fin n) O) :
    IsUnit ((k : Matrix (Fin n) (Fin n) O).map (residue O)).det := by
  have := (Matrix.GeneralLinearGroup.map (residue O) k).isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).1 this

/- English proof (translation)
Use `choose A hA using fun i j => residue_surjective (M i j)`. Establish `hAM : (Matrix.of A).map (residue O) = M`. Use extensionality with `i j`. Conclude with `hA i j`. Establish `: IsUnit (Matrix.of A).det`.

Rewrite using `[← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hAM]`. Conclude with `hM.ne_zero`. Take `⟨k, hk⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 this`. Conclude with `⟨k, hk ▸ hAM⟩`.
-/
theorem exists_lift (M : Matrix (Fin n) (Fin n) (ResidueField O)) (hM : IsUnit M.det) :
    ∃ k : GL (Fin n) O, (k : Matrix (Fin n) (Fin n) O).map (residue O) = M := by
  choose A hA using fun i j => residue_surjective (M i j)
  have hAM : (Matrix.of A).map (residue O) = M := by
    ext i j
    exact hA i j
  have : IsUnit (Matrix.of A).det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hAM]
    exact hM.ne_zero
  obtain ⟨k, hk⟩ := (Matrix.isUnit_iff_isUnit_det _).2 this
  exact ⟨k, hk ▸ hAM⟩

/- English proof (translation)
Establish `f : LinearMap.range D.mulVecLin ≃ₗ[K] U` using `LinearEquiv.ofFinrankEq _ _ hU.symm`. Take `⟨e, he⟩` from `Submodule.exists_linearEquiv_restrict_eq f`. Use `⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.det_toMatrix']`. Conclude with `e.isUnit_det'`.

Rewrite using `[Matrix.mulVecLin_mul, ← Matrix.toLin'_apply' (LinearMap.toMatrix' _), Matrix.toLin'_toMatrix', LinearMap.range_comp]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `he ⟨y, hy⟩` as an intermediate fact.

Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[← this]`. Conclude with `(f ⟨y, hy⟩).2`. Introduce `hx`. Use `⟨(f.symm ⟨x, hx⟩ : _), (f.symm ⟨x, hx⟩).2, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[← he]`. Simplify using the standard rewrite rules.
-/
theorem exists_range_eq {K : Type} [Field K] (D : Matrix (Fin n) (Fin n) K)
    (U : Submodule K (Fin n → K)) (hU : Module.finrank K U = D.rank) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧ LinearMap.range (M * D).mulVecLin = U := by
  have f : LinearMap.range D.mulVecLin ≃ₗ[K] U := LinearEquiv.ofFinrankEq _ _ hU.symm
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact e.isUnit_det'
  · rw [Matrix.mulVecLin_mul, ← Matrix.toLin'_apply' (LinearMap.toMatrix' _),
      Matrix.toLin'_toMatrix', LinearMap.range_comp]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := he ⟨y, hy⟩
      simp only [LinearEquiv.coe_coe]
      rw [← this]
      exact (f ⟨y, hy⟩).2
    · intro hx
      refine ⟨(f.symm ⟨x, hx⟩ : _), (f.symm ⟨x, hx⟩).2, ?_⟩
      simp only [LinearEquiv.coe_coe]
      rw [← he]
      simp

/- English proof (translation)
Establish `h1 : ∀ g ∈ doubleCosetK O t, scaleBy O ϖ (stdLattice O F n) ≤ scaleBy O a (latticeOf O g) ∧ scaleBy O a (latticeOf O g) ≤ stdLattice O F n`. Introduce `g hg`. Take `⟨k, hk⟩` from `exists_of_mem_doubleCosetK hg`. Rewrite using `[hk, scaleBy_latticeOf hD]`. Conclude with `⟨scaleBy_std_le_intLattice h k, intLattice_le_std _⟩`.

Use `⟨h1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨k, hk⟩` from `exists_of_mem_doubleCosetK hg`. Simplify using `only [Set.mem_setOf_eq, latticeOfCoset_mk]`. Rewrite using `[hk, scaleBy_latticeOf hD, reduction_intLattice hinj, Matrix.map_mul]`.

Conclude with `Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_map k)`. Introduce and unpack `_ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ e`. Simplify using `only [latticeOfCoset_mk] at e`. Apply `mk_eq_of_latticeOf_eq hinj` to reduce the goal to its premises. Conclude with `le_antisymm (le_of_scaleBy_le ha (le_of_reduction_le hm (h1 g hg).2 (h1 g' hg').1 e.le)) (le_of_scaleBy_le ha (le_of_reduction_le hm (h1 g' hg').2 (h1 g hg).1 e.ge))`.

Introduce `U hU`. Take `⟨M, hM, hMU⟩` from `exists_range_eq _ U hU`. Take `⟨k, rfl⟩` from `exists_lift M hM`. Use `⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t), ⟨_, ⟨_, ⟨k, rfl⟩, 1, one_mem _, (mul_one _).symm⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [latticeOfCoset_mk]`.

Rewrite using `[scaleBy_latticeOf hD, reduction_intLattice hinj, Matrix.map_mul, hMU]`.
-/
theorem core (hinj : Function.Injective (algebraMap O F)) {ϖ : O}
    (hm : ∀ x ∈ maximalIdeal O, ϖ ∣ x) {a : O} (ha : algebraMap O F a ≠ 0)
    {t : GL (Fin n) F} {D D' : Matrix (Fin n) (Fin n) O}
    (hD : a • (t : Matrix (Fin n) (Fin n) F) = D.map (algebraMap O F))
    (h : D * D' = ϖ • (1 : Matrix (Fin n) (Fin n) O)) :
    (∀ g ∈ doubleCosetK O t, scaleBy O ϖ (stdLattice O F n) ≤ scaleBy O a (latticeOf O g) ∧
      scaleBy O a (latticeOf O g) ≤ stdLattice O F n) ∧
    Set.BijOn (fun c => reduction O (scaleBy O a (latticeOfCoset O c))) (cosetsIn O t)
      {U : Submodule (ResidueField O) (Fin n → ResidueField O) |
        Module.finrank (ResidueField O) U = (D.map (residue O)).rank} := by
  have h1 : ∀ g ∈ doubleCosetK O t,
      scaleBy O ϖ (stdLattice O F n) ≤ scaleBy O a (latticeOf O g) ∧
      scaleBy O a (latticeOf O g) ≤ stdLattice O F n := by
    intro g hg
    obtain ⟨k, hk⟩ := exists_of_mem_doubleCosetK hg
    rw [hk, scaleBy_latticeOf hD]
    exact ⟨scaleBy_std_le_intLattice h k, intLattice_le_std _⟩
  refine ⟨h1, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := exists_of_mem_doubleCosetK hg
    simp only [Set.mem_setOf_eq, latticeOfCoset_mk]
    rw [hk, scaleBy_latticeOf hD, reduction_intLattice hinj, Matrix.map_mul]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_map k)
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ e
    simp only [latticeOfCoset_mk] at e
    apply mk_eq_of_latticeOf_eq hinj
    exact le_antisymm
      (le_of_scaleBy_le ha (le_of_reduction_le hm (h1 g hg).2 (h1 g' hg').1 e.le))
      (le_of_scaleBy_le ha (le_of_reduction_le hm (h1 g' hg').2 (h1 g hg).1 e.ge))
  · intro U hU
    obtain ⟨M, hM, hMU⟩ := exists_range_eq _ U hU
    obtain ⟨k, rfl⟩ := exists_lift M hM
    refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap O F) k * t),
      ⟨_, ⟨_, ⟨k, rfl⟩, 1, one_mem _, (mul_one _).symm⟩, rfl⟩, ?_⟩
    simp only [latticeOfCoset_mk]
    rw [scaleBy_latticeOf hD, reduction_intLattice hinj, Matrix.map_mul, hMU]

end General

end GlobalTheory.MinusculeCosetsProof
