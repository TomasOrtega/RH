import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupLocal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExtensionEmbeddingOfIsRealAlgebraMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField NumberField.InfinitePlace GroundTheory.Global FiniteSubfield

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Norms

variable (v : InfinitePlace K.1)

/- English proof (translation)
Use extensionality with `c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨e.symm y, Algebra.norm_eq_of_algEquiv e.symm y⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨e y, Algebra.norm_eq_of_algEquiv e y⟩`.
-/
theorem range_norm_infAlgClosure_eq {F : FiniteSubfield} [Fact (K ≤ F)] (w : v.placesOver F.1)
    [(w : InfinitePlace F.1).LiesOver v]
    (e : (w : InfinitePlace F.1).Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion) :
    Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) =
      Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, Algebra.norm_eq_of_algEquiv e.symm y⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e y, Algebra.norm_eq_of_algEquiv e y⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[Algebra.norm_zero]`.

Conclude with `c.ne_zero hy.symm`. Conclude with `⟨Units.mk0 y hy0, Units.ext hy⟩`. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, congrArg Units.val hy⟩`.
-/
theorem mem_range_norm_iff_mem_normSubgroup {F : FiniteSubfield} [Fact (K ≤ F)] (w : v.placesOver F.1)
    [(w : InfinitePlace F.1).LiesOver v] (c : v.Completionˣ) :
    (c : v.Completion) ∈ Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) ↔
      c ∈ InfinitePlace.normSubgroup v (w : InfinitePlace F.1) := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact c.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Units.val hy⟩

/- English proof (translation)
Introduce `hL`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_eq_mul_self (-1 : L)`. Establish `h` using `congrArg f hz`. Rewrite `h` using `[map_neg, map_one, map_mul]`. Use polynomial arithmetic with `[mul_self_nonneg (f z)]`.
-/
theorem not_isAlgClosed_of_ringHom_real {L : Type*} [Field L] (f : L →+* ℝ) : ¬ IsAlgClosed L := by
  intro hL
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (-1 : L)
  have h := congrArg f hz
  rw [map_neg, map_one, map_mul] at h
  nlinarith [mul_self_nonneg (f z)]

/- English proof (translation)
Take `⟨F, _, w, ⟨e⟩⟩` from `exists_infCompletion_algEquiv v`. Establish `: (w : InfinitePlace F.1).LiesOver v` using `w.2`. Establish `hw : (w : InfinitePlace F.1).IsComplex`. Rewrite using `[← not_isReal_iff_isComplex]`. Introduce `hwr`.

Establish `hc : IsAlgClosed (w : InfinitePlace F.1).Completion` using `IsAlgClosed.of_ringEquiv (AlgebraicClosure v.Completion) _ e.toRingEquiv.symm`. Conclude with `not_isAlgClosed_of_ringHom_real (Completion.extensionEmbeddingOfIsReal hwr) hc`. Rewrite using `[range_norm_infAlgClosure_eq v w e, mem_range_norm_iff_mem_normSubgroup v w, InfinitePlace.mem_normSubgroup_iff hv hw]`.
-/
theorem infAlgClosure_mem_range_norm_iff_of_isReal (hv : v.IsReal) (c : v.Completionˣ) :
    (c : v.Completion) ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) ↔
      0 < Completion.extensionEmbeddingOfIsReal hv (c : v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have hw : (w : InfinitePlace F.1).IsComplex := by
    rw [← not_isReal_iff_isComplex]
    intro hwr
    have hc : IsAlgClosed (w : InfinitePlace F.1).Completion :=
      IsAlgClosed.of_ringEquiv (AlgebraicClosure v.Completion) _ e.toRingEquiv.symm
    exact not_isAlgClosed_of_ringHom_real (Completion.extensionEmbeddingOfIsReal hwr) hc
  rw [range_norm_infAlgClosure_eq v w e, mem_range_norm_iff_mem_normSubgroup v w,
    InfinitePlace.mem_normSubgroup_iff hv hw]

/- English proof (translation)
Take `⟨F, _, w, ⟨e⟩⟩` from `exists_infCompletion_algEquiv v`. Establish `: (w : InfinitePlace F.1).LiesOver v` using `w.2`. Establish `h : ¬ (v.IsReal ∧ (w : InfinitePlace F.1).IsComplex)` using `fun h => (not_isReal_iff_isComplex.2 hv) h.1`. Rewrite using `[range_norm_infAlgClosure_eq v w e, mem_range_norm_iff_mem_normSubgroup v w, InfinitePlace.normSubgroup_eq_top (w : InfinitePlace F.1) h]`. Conclude with `Subgroup.mem_top c`.
-/
theorem infAlgClosure_mem_range_norm_of_isComplex (hv : v.IsComplex) (c : v.Completionˣ) :
    (c : v.Completion) ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have h : ¬ (v.IsReal ∧ (w : InfinitePlace F.1).IsComplex) := fun h =>
    (not_isReal_iff_isComplex.2 hv) h.1
  rw [range_norm_infAlgClosure_eq v w e, mem_range_norm_iff_mem_normSubgroup v w,
    InfinitePlace.normSubgroup_eq_top (w : InfinitePlace F.1) h]
  exact Subgroup.mem_top c

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨z, hz⟩` from `(IsGalois.mem_range_algebraMap_iff_fixed s).2 h`. Establish `hz2 : z ^ 2 = -1`. Apply `(algebraMap v.Completion (AlgebraicClosure v.Completion)).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, hz, hs, map_neg, map_one]`. Establish `h2` using `congrArg (Completion.extensionEmbeddingOfIsReal hv) hz2`. Rewrite `h2` using `[map_pow, map_neg, map_one]`. Use polynomial arithmetic with `[sq_nonneg (Completion.extensionEmbeddingOfIsReal hv z)]`.
-/
theorem exists_gal_ne_of_sq_eq_neg_one (hv : v.IsReal) {s : AlgebraicClosure v.Completion}
    (hs : s ^ 2 = -1) : ∃ σ : Gal(AlgebraicClosure v.Completion/v.Completion), σ s ≠ s := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := (IsGalois.mem_range_algebraMap_iff_fixed s).2 h
  have hz2 : z ^ 2 = -1 := by
    apply (algebraMap v.Completion (AlgebraicClosure v.Completion)).injective
    rw [map_pow, hz, hs, map_neg, map_one]
  have h2 := congrArg (Completion.extensionEmbeddingOfIsReal hv) hz2
  rw [map_pow, map_neg, map_one] at h2
  nlinarith [sq_nonneg (Completion.extensionEmbeddingOfIsReal hv z)]

end Norms

section IChar

def sqrtNegOne : ℚ̄ := (IsAlgClosed.exists_eq_mul_self (-1 : ℚ̄)).choose

/- English proof (translation)
The claim follows from `(IsAlgClosed.exists_eq_mul_self (-1 : ℚ̄)).choose_spec.symm`.
-/
theorem sqrtNegOne_mul_self : sqrtNegOne * sqrtNegOne = -1 :=
  (IsAlgClosed.exists_eq_mul_self (-1 : ℚ̄)).choose_spec.symm

/- English proof (translation)
Rewrite using `[sq, sqrtNegOne_mul_self]`.
-/
theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 := by
  rw [sq, sqrtNegOne_mul_self]

/- English proof (translation)
Introduce `h`. Establish `h2 : (2 : ℚ̄) * sqrtNegOne = 0` using `by rw [two_mul]; nth_rw 2 [h]; exact add_neg_cancel _`. Break down `mul_eq_zero.1 h2 with h2 | h2` into its components or cases. Conclude with `two_ne_zero h2`. Use `sqrtNegOne_mul_self` as an intermediate fact.

Rewrite `this` using `[h2, zero_mul, eq_comm, neg_eq_zero]`. Conclude with `one_ne_zero this`.
-/
theorem sqrtNegOne_ne_neg : sqrtNegOne ≠ -sqrtNegOne := by
  intro h
  have h2 : (2 : ℚ̄) * sqrtNegOne = 0 := by rw [two_mul]; nth_rw 2 [h]; exact add_neg_cancel _
  rcases mul_eq_zero.1 h2 with h2 | h2
  · exact two_ne_zero h2
  · have := sqrtNegOne_mul_self
    rw [h2, zero_mul, eq_comm, neg_eq_zero] at this
    exact one_ne_zero this

/- English proof (translation)
Establish `h : (σ sqrtNegOne - sqrtNegOne) * (σ sqrtNegOne + sqrtNegOne) = 0`. Establish `h1 : σ sqrtNegOne * σ sqrtNegOne = -1` using `by rw [← map_mul, sqrtNegOne_mul_self, map_neg, map_one]`. Take the linear combination `h1 - sqrtNegOne_mul_self`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h)`.

Conclude with `Or.inr (eq_neg_of_add_eq_zero_left h)`.
-/
theorem apply_sqrtNegOne_eq_or (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : σ sqrtNegOne = sqrtNegOne ∨ σ sqrtNegOne = -sqrtNegOne := by
  have h : (σ sqrtNegOne - sqrtNegOne) * (σ sqrtNegOne + sqrtNegOne) = 0 := by
    have h1 : σ sqrtNegOne * σ sqrtNegOne = -1 := by rw [← map_mul, sqrtNegOne_mul_self, map_neg, map_one]
    linear_combination h1 - sqrtNegOne_mul_self
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

variable (K) in
open Classical in

def iCharFun (g : Additive K.1.fixingSubgroup) : QZ :=
  if ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne = sqrtNegOne then 0 else QZ.mk (1 / 2)

/- English proof (translation)
Simplify using `[iCharFun, h]`.
-/
theorem iCharFun_of_fix {g : Additive K.1.fixingSubgroup}
    (h : ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne = sqrtNegOne) : iCharFun K g = 0 := by
  simp [iCharFun, h]

/- English proof (translation)
Simplify using `[iCharFun, h]`.
-/
theorem iCharFun_of_not_fix {g : Additive K.1.fixingSubgroup}
    (h : ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne ≠ sqrtNegOne) :
    iCharFun K g = QZ.mk (1 / 2) := by
  simp [iCharFun, h]

/- English proof (translation)
Unfold `iCharFun`. Rewrite using `[hgh]`.
-/
theorem iCharFun_congr {g h : Additive K.1.fixingSubgroup}
    (hgh : ((Additive.toMul h : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne =
      ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne) : iCharFun K h = iCharFun K g := by
  unfold iCharFun
  rw [hgh]

/- English proof (translation)
Use `IsLocallyConstant.continuous ?_` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g`. Set `G` to `K.1.fixingSubgroup`. Set `g' : G` to `Additive.toMul g`.

Establish `hstab : IsOpen (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))` using `stabilizer_isOpen_of_isIntegral sqrtNegOne`. Establish `hopen : IsOpen ((fun h : G => g'⁻¹ * h) ⁻¹' ((G.subtype : G → ℚ̄ ≃ₐ[ℚ] ℚ̄) ⁻¹' (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))))` using `(hstab.preimage continuous_subtype_val).preimage (continuous_const_mul _)`. Use `⟨(fun h : G => g'⁻¹ * h) ⁻¹' ((G.subtype : G → ℚ̄ ≃ₐ[ℚ] ℚ̄) ⁻¹' (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))), hopen, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g'⁻¹ * g' : G).1 • sqrtNegOne = sqrtNegOne`. Rewrite using `[inv_mul_cancel]`.

Conclude with `one_smul _ _`. Introduce `h hh`. Express the relevant statement in the definitionally equal form `(g'⁻¹ * Additive.toMul h : G).1 • sqrtNegOne = sqrtNegOne at hh`. Apply `iCharFun_congr` to reduce the goal to its premises. Rewrite `hh` using `[Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_eq_iff]`.

Conclude with `hh`.
-/
theorem continuous_iCharFun : Continuous (iCharFun K) := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  let G := K.1.fixingSubgroup
  let g' : G := Additive.toMul g
  have hstab : IsOpen (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
    stabilizer_isOpen_of_isIntegral sqrtNegOne
  have hopen : IsOpen ((fun h : G => g'⁻¹ * h) ⁻¹' ((G.subtype : G → ℚ̄ ≃ₐ[ℚ] ℚ̄) ⁻¹'
      (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)))) :=
    (hstab.preimage continuous_subtype_val).preimage (continuous_const_mul _)
  refine ⟨(fun h : G => g'⁻¹ * h) ⁻¹' ((G.subtype : G → ℚ̄ ≃ₐ[ℚ] ℚ̄) ⁻¹'
      (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))), hopen, ?_, ?_⟩
  · change (g'⁻¹ * g' : G).1 • sqrtNegOne = sqrtNegOne
    rw [inv_mul_cancel]
    exact one_smul _ _
  · intro h hh
    change (g'⁻¹ * Additive.toMul h : G).1 • sqrtNegOne = sqrtNegOne at hh
    apply iCharFun_congr
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_eq_iff] at hh
    exact hh

variable (K) in

def iChar : Additive K.1.fixingSubgroup →ₜ+ QZ where
  toFun := iCharFun K
  map_zero' := iCharFun_of_fix rfl
  map_add' g h := by
    have hmul : ((Additive.toMul (g + h) : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne =
        ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄)
          (((Additive.toMul h : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne) := rfl
    rcases apply_sqrtNegOne_eq_or ((Additive.toMul h : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) with hh | hh
    · rw [hh] at hmul
      rw [iCharFun_of_fix hh, add_zero]
      exact iCharFun_congr hmul
    · rw [hh, map_neg] at hmul
      have hh' : iCharFun K h = QZ.mk (1 / 2) :=
        iCharFun_of_not_fix (by rw [hh]; exact sqrtNegOne_ne_neg.symm)
      rcases apply_sqrtNegOne_eq_or ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) with hg | hg
      · rw [hg] at hmul
        have hgh : iCharFun K (g + h) = QZ.mk (1 / 2) :=
          iCharFun_of_not_fix (by rw [hmul]; exact sqrtNegOne_ne_neg.symm)
        rw [hgh, hh', iCharFun_of_fix hg, zero_add]
      · rw [hg, neg_neg] at hmul
        have hg' : iCharFun K g = QZ.mk (1 / 2) :=
          iCharFun_of_not_fix (by rw [hg]; exact sqrtNegOne_ne_neg.symm)
        rw [iCharFun_of_fix hmul, hg', hh', QZ.mk_half_add_mk_half]
  continuous_toFun := continuous_iCharFun

/- English proof (translation)
The claim follows from `iCharFun_of_fix h`.
-/
theorem iChar_apply_of_fix (τ : K.1.fixingSubgroup) (h : (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne = sqrtNegOne) :
    iChar K (Additive.ofMul τ) = 0 :=
  iCharFun_of_fix h

/- English proof (translation)
The claim follows from `iCharFun_of_not_fix h`.
-/
theorem iChar_apply_of_not_fix (τ : K.1.fixingSubgroup) (h : (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne ≠ sqrtNegOne) :
    iChar K (Additive.ofMul τ) = QZ.mk (1 / 2) :=
  iCharFun_of_not_fix h

end IChar

section Invariants

variable (ι : LocalEmbeddings K) (a : K.1ˣ)

/- English proof (translation)
Rewrite using `[placeInv_brauerLocal_globalCupClass_inl ι v (iChar K) a 1 (iff_of_true rfl ha), map_one, ofMul_one, map_zero]`.
-/
theorem placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm (v : InfinitePlace K.1)
    (ha : algebraMap K.1 v.Completion (a : K.1) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = 0 := by
  rw [placeInv_brauerLocal_globalCupClass_inl ι v (iChar K) a 1 (iff_of_true rfl ha), map_one, ofMul_one,
    map_zero]

/- English proof (translation)
Establish `hs : (ι.inf v) sqrtNegOne ^ 2 = -1` using `by rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]`. Take `⟨σ, hσ⟩` from `exists_gal_ne_of_sq_eq_neg_one v hv hs`. Establish `hnorm : algebraMap K.1 v.Completion (a : K.1) ∉ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)`. Introduce `hmem`. Establish `hu` using `(infAlgClosure_mem_range_norm_iff_of_isReal v hv (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)).1 hmem`.

Rewrite `hu` using `[Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap]`. Conclude with `lt_asymm ha hu`. Establish `hσ1 : σ ≠ 1` using `fun h => hσ (by rw [h]; rfl)`. Rewrite using `[placeInv_brauerLocal_globalCupClass_inl ι v (iChar K) a σ (iff_of_false hσ1 hnorm)]`. Apply `iChar_apply_of_not_fix` to reduce the goal to its premises.

Introduce `hfix`. Apply `hσ` to reduce the goal to its premises. Rewrite using `[← globalDecomp_apply, hfix]`.
-/
theorem placeInv_brauerLocal_globalCupClass_iChar_of_neg (v : InfinitePlace K.1) (hv : v.IsReal)
    (ha : embedding_of_isReal hv (a : K.1) < 0) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = QZ.mk (1 / 2) := by
  have hs : (ι.inf v) sqrtNegOne ^ 2 = -1 := by rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]
  obtain ⟨σ, hσ⟩ := exists_gal_ne_of_sq_eq_neg_one v hv hs
  have hnorm : algebraMap K.1 v.Completion (a : K.1) ∉
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) := by
    intro hmem
    have hu := (infAlgClosure_mem_range_norm_iff_of_isReal v hv
      (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)).1 hmem
    rw [Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap] at hu
    exact lt_asymm ha hu
  have hσ1 : σ ≠ 1 := fun h => hσ (by rw [h]; rfl)
  rw [placeInv_brauerLocal_globalCupClass_inl ι v (iChar K) a σ (iff_of_false hσ1 hnorm)]
  apply iChar_apply_of_not_fix
  intro hfix
  apply hσ
  rw [← globalDecomp_apply, hfix]

/- English proof (translation)
Use `placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm ι a v ?_` and prove the remaining obligations. Establish `h` using `(infAlgClosure_mem_range_norm_iff_of_isReal v hv (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)).2 (by rw [Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap]; exact ha)`. Rewrite `h` using `[Units.coe_map, MonoidHom.coe_coe]`. Then use the resulting hypothesis.
-/
theorem placeInv_brauerLocal_globalCupClass_iChar_of_pos (v : InfinitePlace K.1) (hv : v.IsReal)
    (ha : 0 < embedding_of_isReal hv (a : K.1)) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = 0 := by
  refine placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm ι a v ?_
  have h := (infAlgClosure_mem_range_norm_iff_of_isReal v hv
    (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)).2
    (by rw [Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap]; exact ha)
  rwa [Units.coe_map, MonoidHom.coe_coe] at h

/- English proof (translation)
Use `placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm ι a v ?_` and prove the remaining obligations. Establish `h` using `infAlgClosure_mem_range_norm_of_isComplex v hv (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)`. Rewrite `h` using `[Units.coe_map, MonoidHom.coe_coe]`. Then use the resulting hypothesis.
-/
theorem placeInv_brauerLocal_globalCupClass_iChar_of_isComplex (v : InfinitePlace K.1) (hv : v.IsComplex) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = 0 := by
  refine placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm ι a v ?_
  have h := infAlgClosure_mem_range_norm_of_isComplex v hv
    (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)
  rwa [Units.coe_map, MonoidHom.coe_coe] at h

open Classical in

/- English proof (translation)
Distinguish the cases in `hv : v.IsReal`. Rewrite using `[dif_pos hv]`. Distinguish the cases in `ha : embedding_of_isReal hv (a : K.1) < 0`. Rewrite using `[if_pos ha]`. Conclude with `placeInv_brauerLocal_globalCupClass_iChar_of_neg ι a v hv ha`.

Rewrite using `[if_neg ha]`. Establish `hpos : 0 < embedding_of_isReal hv (a : K.1)` using `lt_of_le_of_ne (not_lt.1 ha) (fun h => a.ne_zero ((map_eq_zero _).1 h.symm))`. Conclude with `placeInv_brauerLocal_globalCupClass_iChar_of_pos ι a v hv hpos`. Rewrite using `[dif_neg hv]`. Conclude with `placeInv_brauerLocal_globalCupClass_iChar_of_isComplex ι a v (not_isReal_iff_isComplex.1 hv)`.
-/
theorem placeInv_brauerLocal_globalCupClass_iChar (v : InfinitePlace K.1) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) =
      if h : v.IsReal then (if v.embedding_of_isReal h (a : K.1) < 0 then QZ.mk (1 / 2) else 0) else 0 := by
  by_cases hv : v.IsReal
  · rw [dif_pos hv]
    by_cases ha : embedding_of_isReal hv (a : K.1) < 0
    · rw [if_pos ha]
      exact placeInv_brauerLocal_globalCupClass_iChar_of_neg ι a v hv ha
    · rw [if_neg ha]
      have hpos : 0 < embedding_of_isReal hv (a : K.1) :=
        lt_of_le_of_ne (not_lt.1 ha) (fun h => a.ne_zero ((map_eq_zero _).1 h.symm))
      exact placeInv_brauerLocal_globalCupClass_iChar_of_pos ι a v hv hpos
  · rw [dif_neg hv]
    exact placeInv_brauerLocal_globalCupClass_iChar_of_isComplex ι a v (not_isReal_iff_isComplex.1 hv)

end Invariants

section Bool

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_units_neg_iff_mem {v | s v = true}`. Conclude with `⟨a, fun v => (ha v).1⟩`.
-/
theorem exists_units_neg_iff {L : Type*} [Field L] [NumberField L] (s : {v : InfinitePlace L // v.IsReal} → Bool) :
    ∃ a : Lˣ, ∀ v : {v : InfinitePlace L // v.IsReal}, (v.1.embedding_of_isReal v.2 (a : L) < 0 ↔ s v = true) := by
  obtain ⟨a, ha⟩ := exists_units_neg_iff_mem {v | s v = true}
  exact ⟨a, fun v => (ha v).1⟩

/- English proof (translation)
The claim follows from `exists_units_neg_iff s`.
-/
example (s : {v : InfinitePlace K.1 // v.IsReal} → Bool) :
    ∃ a : K.1ˣ, ∀ v : {v : InfinitePlace K.1 // v.IsReal}, (v.1.embedding_of_isReal v.2 (a : K.1) < 0 ↔ s v = true) :=
  exists_units_neg_iff s

end Bool

end

end GroundTheory.ProfCoh
