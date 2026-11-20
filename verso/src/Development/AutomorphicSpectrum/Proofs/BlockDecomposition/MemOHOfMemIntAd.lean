import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisCol

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Unfold `TF.col`. Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem col_apply (i₀ : ι) (κ : GL ι 𝔸[k]) (j : ι) :
    TF.col i₀ κ j = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
  unfold TF.col
  rw [Matrix.mulVec_single_one]
  rfl

def finPart : 𝔸[k] →+* FiniteAdeleRing (𝓞 k) k := RingHom.snd _ _

/- English proof (translation)
Rewrite using `[mem_integralFiniteAdeles]`. Introduce `v`. Use `(Subring.mem_iInf.1 hx) v` as an intermediate fact. Conclude with `this`.
-/
theorem mem_OH_of_mem_intAd {x : 𝔸[k]} (hx : x ∈ intAd k) : x.2 ∈ OH k := by
  rw [mem_integralFiniteAdeles]
  intro v
  have := (Subring.mem_iInf.1 hx) v
  exact this

/- English proof (translation)
Establish `h` using `congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hg) i₀) i₀`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Establish `h2 : ∀ j, (star ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w))) i₀ j * ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w)) j i₀ = ((‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 : ℝ) : ℂ)`. Introduce `j`. Establish `e : ‖(adStd k).φ w ((g : Matrix ι ι 𝔸[k]) j i₀)‖ = ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖` using `(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _`.

Rewrite using `[← e, Matrix.star_apply, Matrix.map_apply, mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [h2] at h`. Conclude with `h` after adjusting the coercions.
-/
theorem sum_norm_sq {g : GL ι 𝔸[k]} {w : InfinitePlace k}
    (hg : (g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w) ∈ Matrix.unitaryGroup ι ℂ) (i₀ : ι) :
    ∑ j, ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hg) i₀) i₀
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ j, (star ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w))) i₀ j *
      ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w)) j i₀ =
      ((‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have e : ‖(adStd k).φ w ((g : Matrix ι ι 𝔸[k]) j i₀)‖ = ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    rw [← e, Matrix.star_apply, Matrix.map_apply, mul_comm, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  simp only [h2] at h
  exact_mod_cast h

/- English proof (translation)
The claim follows from `hp j hj i₀ rfl`.
-/
theorem stab_entry {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) {j : ι} (hj : j ≠ i₀) :
    (p : Matrix ι ι 𝔸[k]) j i₀ = 0 ∧ ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ = 0 :=
  hp j hj i₀ rfl

/- English proof (translation)
Establish `h : ((p : Matrix ι ι 𝔸[k]) * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single i₀]`. Conclude with `h`. Introduce `j _ hj`.

Apply the tactic sequence `rw [(stab_entry hp hj).2, mul_zero]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem stab_mul_inv {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (p : Matrix ι ι 𝔸[k]) i₀ i₀ * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ = 1 := by
  have h : ((p : Matrix ι ι 𝔸[k]) * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀] at h
  · exact h
  · intro j _ hj
    rw [(stab_entry hp hj).2, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/- English proof (translation)
Establish `key : ∀ (i₁ : DecidableEq ({i₀} : Set ι)) (i₂ : Fintype ({i₀} : Set ι)), @Matrix.det _ i₁ i₂ R _ ((p : Matrix ι ι R).submatrix (Subtype.val : ({i₀} : Set ι) → ι) Subtype.val) = (p : Matrix ι ι R) i₀ i₀` using `fun i₁ i₂ => @Matrix.det_eq_elem_of_subsingleton _ i₁ i₂ R _ _ _ (⟨i₀, rfl⟩ : ({i₀} : Set ι))`. Unfold `bdet`. Use `split_ifs with h`. Rewrite using `[IsUnit.unit_spec, key]`. Rewrite `h` using `[key]`.

Conclude with `absurd hu h`.
-/
theorem bdet_single {R : Type} [CommRing R] {p : GL ι R} {i₀ : ι} (hu : IsUnit ((p : Matrix ι ι R) i₀ i₀)) :
    ((bdet {i₀} p : Rˣ) : R) = (p : Matrix ι ι R) i₀ i₀ := by
  have key : ∀ (i₁ : DecidableEq ({i₀} : Set ι)) (i₂ : Fintype ({i₀} : Set ι)),
      @Matrix.det _ i₁ i₂ R _ ((p : Matrix ι ι R).submatrix (Subtype.val : ({i₀} : Set ι) → ι) Subtype.val) =
        (p : Matrix ι ι R) i₀ i₀ := fun i₁ i₂ =>
    @Matrix.det_eq_elem_of_subsingleton _ i₁ i₂ R _ _ _ (⟨i₀, rfl⟩ : ({i₀} : Set ι))
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, key]
  · rw [key] at h
    exact absurd hu h

/- English proof (translation)
The claim follows from `bdet_single (IsUnit.of_mul_eq_one _ (stab_mul_inv hp))`.
-/
theorem bdet_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ((bdet {i₀} p : 𝔸[k]ˣ) : 𝔸[k]) = (p : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  bdet_single (IsUnit.of_mul_eq_one _ (stab_mul_inv hp))

/- English proof (translation)
The claim follows from `Units.inv_eq_of_mul_eq_one_right (by rw [bdet_val hp]; exact stab_mul_inv hp)`.
-/
theorem bdet_inv_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) = ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_val hp]; exact stab_mul_inv hp)

/- English proof (translation)
Establish `h : ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1 = ((((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k])) • (Pi.single i₀ 1 : ι → 𝔸[k])` using `by ext1 j`. Establish `e : (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1) j = ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀`. Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Rewrite using `[e, bdet_inv_val hp, Pi.smul_apply]`.

Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same, smul_eq_mul, mul_one]`. Apply the tactic sequence `rw [(stab_entry hp hj).2, Pi.single_eq_of_ne hj, smul_zero]`. Unfold `TF.col`.

Rewrite using `[_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]`.
-/
theorem col_mul {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) (κ : GL ι 𝔸[k]) :
    TF.col i₀ (p * κ) = (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • TF.col i₀ κ := by
  have h : ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1 =
      ((((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k])) • (Pi.single i₀ 1 : ι → 𝔸[k]) := by
    ext1 j
    have e : (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1) j =
        ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [e, bdet_inv_val hp, Pi.smul_apply]
    by_cases hj : j = i₀
    · subst hj
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [(stab_entry hp hj).2, Pi.single_eq_of_ne hj, smul_zero]
  unfold TF.col
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]

/- English proof (translation)
Unfold `TF.col`. Conclude with `(Units.continuous_coe_inv).matrix_mulVec continuous_const`.
-/
theorem col_continuous (i₀ : ι) : Continuous fun κ : GL ι 𝔸[k] => TF.col i₀ κ := by
  unfold TF.col
  exact (Units.continuous_coe_inv).matrix_mulVec continuous_const

/- English proof (translation)
Unfold `TF.col`. Rewrite using `[inv_one, Units.val_one, Matrix.one_mulVec]`.
-/
theorem col_one (i₀ : ι) : TF.col (k := k) i₀ 1 = Pi.single i₀ 1 := by
  unfold TF.col
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Introduce `w`. Establish `h` using `sum_norm_sq ((((adStd k).kGL ι).inv_mem hκ).2 w) i₀`. Use `Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h` and prove the remaining obligations. Conclude with `congrArg (fun x : 𝔸[k] => ‖x.1 w‖ ^ 2) (col_apply i₀ κ j)`.
-/
theorem col_unitVec {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    UnitVec (fun j => (TF.col i₀ κ j).1) := by
  intro w
  have h := sum_norm_sq ((((adStd k).kGL ι).inv_mem hκ).2 w) i₀
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  exact congrArg (fun x : 𝔸[k] => ‖x.1 w‖ ^ 2) (col_apply i₀ κ j)

/- English proof (translation)
Use `⟨fun j => ?_, fun j => ((κ : Matrix ι ι 𝔸[k]) i₀ j).2, fun j => ?_, ?_⟩` and prove the remaining obligations. Conclude with `Eq.mpr (congrArg (fun x : 𝔸[k] => x.2 ∈ OH k) (col_apply i₀ κ j)) (mem_OH_of_mem_intAd (hκ.1 j i₀).2)`. Conclude with `mem_OH_of_mem_intAd (hκ.1 i₀ j).1`. Establish `h : ((κ : Matrix ι ι 𝔸[k]) * ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]`.

Rewrite `h` using `[Matrix.mul_apply]`. Establish `h2` using `congrArg (finPart (k := k)) h`. Rewrite `h2` using `[map_sum, map_one]`. Use `Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `congrArg (fun x : 𝔸[k] => finPart ((κ : Matrix ι ι 𝔸[k]) i₀ j) * finPart x) (col_apply i₀ κ j)`.
-/
theorem col_prim {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    Prim fun j => (TF.col i₀ κ j).2 := by
  refine ⟨fun j => ?_, fun j => ((κ : Matrix ι ι 𝔸[k]) i₀ j).2, fun j => ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun x : 𝔸[k] => x.2 ∈ OH k) (col_apply i₀ κ j))
      (mem_OH_of_mem_intAd (hκ.1 j i₀).2)
  · exact mem_OH_of_mem_intAd (hκ.1 i₀ j).1
  · have h : ((κ : Matrix ι ι 𝔸[k]) * ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at h
    have h2 := congrArg (finPart (k := k)) h
    rw [map_sum, map_one] at h2
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
    rw [map_mul]
    exact congrArg (fun x : 𝔸[k] => finPart ((κ : Matrix ι ι 𝔸[k]) i₀ j) * finPart x) (col_apply i₀ κ j)

/- English proof (translation)
Use `⟨toInfinite k (bdet {i₀} p), toFinite k (bdet {i₀} p), ?_, fun w => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ofFinite_mul_ofInfinite]`. Establish `hv : ((toInfinite k (bdet {i₀} p) : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) = ((p : Matrix ι ι 𝔸[k]) i₀ i₀).1`. Rewrite using `[← bdet_val hp]`. Both sides reduce to the same expression.

Rewrite using `[hv]`. Establish `h` using `sum_norm_sq (hk.2 w) i₀`. Rewrite using `[Finset.sum_eq_single i₀ (fun j _ hj => by`. Apply the tactic sequence `rw [(stab_entry hp hj).1]`. Use `show ‖(0 : w.Completion)‖ ^ 2 = 0`.

Use the proof step `simp)`. Use the proof step `(fun h' => absurd (Finset.mem_univ _) h')] at h`. Establish `h0 : 0 ≤ ‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖` using `norm_nonneg _`. Use polynomial arithmetic with `[h, h0, sq_nonneg (‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ - 1)]`. Rewrite using `[mem_finiteIntegralUnits]`.

Introduce `v`. Establish `h1 : ((toFinite k (bdet {i₀} p) : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) = ((p : Matrix ι ι 𝔸[k]) i₀ i₀).2`. Rewrite using `[← bdet_val hp]`. Both sides reduce to the same expression. Establish `h2 : (((toFinite k (bdet {i₀} p))⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) = (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀).2`.

Rewrite using `[← bdet_inv_val hp, ← map_inv]`. Both sides reduce to the same expression. Rewrite using `[h1, h2]`. Conclude with `⟨(mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).1)) v, (mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).2)) v⟩`.
-/
theorem bdet_split {p : GL ι 𝔸[k]} (hk : p ∈ (adStd k).kGL ι) {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ∃ (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ), bdet {i₀} p = ofInfinite a * ofFinite u ∧
      (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) ∧ u ∈ finiteIntegralUnits k := by
  refine ⟨toInfinite k (bdet {i₀} p), toFinite k (bdet {i₀} p), ?_, fun w => ?_, ?_⟩
  · rw [mul_comm, ofFinite_mul_ofInfinite]
  · have hv : ((toInfinite k (bdet {i₀} p) : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 := by
      rw [← bdet_val hp]; rfl
    rw [hv]
    have h := sum_norm_sq (hk.2 w) i₀
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by
      rw [(stab_entry hp hj).1]
      show ‖(0 : w.Completion)‖ ^ 2 = 0
      simp)
      (fun h' => absurd (Finset.mem_univ _) h')] at h
    have h0 : 0 ≤ ‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ := norm_nonneg _
    nlinarith [h, h0, sq_nonneg (‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ - 1)]
  · rw [mem_finiteIntegralUnits]
    intro v
    have h1 : ((toFinite k (bdet {i₀} p) : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_val hp]; rfl
    have h2 : (((toFinite k (bdet {i₀} p))⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_inv_val hp, ← map_inv]; rfl
    rw [h1, h2]
    exact ⟨(mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).1)) v,
      (mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).2)) v⟩

/- English proof (translation)
Introduce `k _ _ ι _ _ i₀`. Conclude with `⟨fun κ hκ => ⟨col_unitVec hκ i₀, col_prim hκ i₀⟩, col_continuous i₀, col_one i₀, fun p hk hp => ⟨col_mul hp, bdet_split hk hp⟩⟩`.
-/
theorem colLaw : ColLaw := by
  intro k _ _ ι _ _ i₀
  exact ⟨fun κ hκ => ⟨col_unitVec hκ i₀, col_prim hκ i₀⟩, col_continuous i₀, col_one i₀,
    fun p hk hp => ⟨col_mul hp, bdet_split hk hp⟩⟩

end GlobalTheory.CompanionTheory.EisCol
