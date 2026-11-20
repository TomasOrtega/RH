import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.Count.PerpStep

section Form

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

def toDual (J : Matrix (Fin n) (Fin n) K) : (Fin n → K) →+ Module.Dual K (Fin n → K) where
  toFun y :=
    { toFun := fun z => Formalism.UG.hform (starRingEnd K) J y z
      map_add' := fun z w => by simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
  map_zero' := by ext i; simp [Formalism.UG.hform]
  map_add' y y' := by
    refine LinearMap.ext fun z => ?_
    simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toDual_apply (J : Matrix (Fin n) (Fin n) K) (y z : Fin n → K) :
    toDual J y z = Formalism.UG.hform (starRingEnd K) J y z := rfl

omit [NumberField K] in
/- English proof (translation)
Establish `h : ∀ i j, star (J j i) = J i j` using `fun i j => congrFun (congrFun hJ i) j`. Simplify using `only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hform_swap {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (y z : Fin n → K) :
    Formalism.UG.hform (starRingEnd K) J y z = star (Formalism.UG.hform (starRingEnd K) J z y) := by
  have h : ∀ i j, star (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `f`. Use `⟨star ((fun j => f (Pi.single j 1)) ᵥ* J⁻¹), ?_⟩` and prove the remaining obligations. Use `(Pi.basisFun K (Fin n)).ext fun j => ?_` and prove the remaining obligations. Establish `h : ((fun j => f (Pi.single j 1)) ᵥ* J⁻¹) ᵥ* J = fun j => f (Pi.single j 1)`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.vecMul_one]`.

Establish `h2` using `congrFun h j`. Rewrite using `[toDual_apply, Pi.basisFun_apply, ← h2]`. Generalize the expression as in `((fun j => f (Pi.single j 1)) ᵥ* J⁻¹) = c`. Simplify using `[Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct, starRingEnd_apply, -star_trivial]`.
-/
theorem toDual_surj {J : Matrix (Fin n) (Fin n) K} (hJ : J.det ≠ 0) :
    Function.Surjective (toDual J) := by
  intro f
  refine ⟨star ((fun j => f (Pi.single j 1)) ᵥ* J⁻¹), ?_⟩
  refine (Pi.basisFun K (Fin n)).ext fun j => ?_
  have h : ((fun j => f (Pi.single j 1)) ᵥ* J⁻¹) ᵥ* J = fun j => f (Pi.single j 1) := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.vecMul_one]
  have h2 := congrFun h j
  rw [toDual_apply, Pi.basisFun_apply, ← h2]
  generalize ((fun j => f (Pi.single j 1)) ᵥ* J⁻¹) = c
  simp [Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct, starRingEnd_apply, -star_trivial]

/- English proof (translation)
Take `⟨r, rfl⟩` from `ha`. Establish `h : IsIntegral ℤ ((starRingEnd K).toIntAlgHom (algebraMap (𝓞 K) K r))` using `(RingOfIntegers.isIntegral_coe r).map _`. Conclude with `⟨⟨_, h⟩, rfl⟩`.
-/
theorem star_mem_range {a : K} (ha : a ∈ (algebraMap (𝓞 K) K).range) :
    star a ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨r, rfl⟩ := ha
  have h : IsIntegral ℤ ((starRingEnd K).toIntAlgHom (algebraMap (𝓞 K) K r)) :=
    (RingOfIntegers.isIntegral_coe r).map _
  exact ⟨⟨_, h⟩, rfl⟩

/- English proof (translation)
Establish `hn : ∀ v, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)).dualBasis (dualFrame X) v (toDual J y) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v y`. Introduce `v`. Take `⟨ε, hε⟩` from `hXJ v`. Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm`. Rewrite using `[DualPolygon.ident_fcoord_dual _ X hX]`.

Use `set u := Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v y with hu`. Establish `hy : X v *ᵥ u = fun i => v.embedding (y i)`. Rewrite using `[hu, Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.HermitianLatticesTheory.vecAt]`.

Establish `h1 : (fun i => v.embedding (toDual J y (Pi.basisFun K (Fin n) i))) = star (X v *ᵥ u) ᵥ* J.map v.embedding`. Use function extensionality and compare the values at `i`. Rewrite using `[hy, toDual_apply, Pi.basisFun_apply]`. Establish `hs' : ∀ a : K, v.embedding (starRingEnd K a) = star (v.embedding a)` using `fun a => hs _ a`. Simplify using `[Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct, hs']`.

Rewrite using `[h1, Matrix.mulVec_transpose, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hε]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Jm, Matrix.vecMul_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h2 : ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (dualFrame X) (toDual J y)‖ ^ 2 = ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X y‖ ^ 2`. Rewrite using `[PlaceOperatorNorms.norm_sq_realize, PlaceOperatorNorms.norm_sq_realize]`. Simplify using `only [hn]`. Establish `h3` using `congrArg Real.sqrt h2`. Rewrite `h3` using `[Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]`. Then use the resulting hypothesis.
-/
theorem norm_toDual {J : Matrix (Fin n) (Fin n) K}
    (hs : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (hXJ : ∀ v, ∃ ε, (X v)ᴴ * J.map v.embedding * X v = Jm ε) (y : Fin n → K) :
    ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (dualFrame X) (toDual J y)‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X y‖ := by
  have hn : ∀ v, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)).dualBasis (dualFrame X) v (toDual J y) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v y := by
    intro v
    obtain ⟨ε, hε⟩ := hXJ v
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
    rw [DualPolygon.ident_fcoord_dual _ X hX]
    set u := Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v y with hu
    have hy : X v *ᵥ u = fun i => v.embedding (y i) := by
      rw [hu, Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v),
        Matrix.one_mulVec]
      funext i
      simp [Formalism.HermitianLatticesTheory.vecAt]
    have h1 : (fun i => v.embedding (toDual J y (Pi.basisFun K (Fin n) i))) =
        star (X v *ᵥ u) ᵥ* J.map v.embedding := by
      funext i
      rw [hy, toDual_apply, Pi.basisFun_apply]
      have hs' : ∀ a : K, v.embedding (starRingEnd K a) = star (v.embedding a) := fun a => hs _ a
      simp [Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct, hs']
    rw [h1, Matrix.mulVec_transpose, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, hε]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Jm, Matrix.vecMul_diagonal]
    split_ifs <;> simp
  have h2 : ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (dualFrame X) (toDual J y)‖ ^ 2 =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X y‖ ^ 2 := by
    rw [PlaceOperatorNorms.norm_sq_realize, PlaceOperatorNorms.norm_sq_realize]
    simp only [hn]
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

def perp (J : Matrix (Fin n) (Fin n) K) (A S : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin n → K) :=
  A ⊓ (⨅ s ∈ S, LinearMap.ker (toDual J s) : Submodule K (Fin n → K)).restrictScalars (𝓞 K)

/- English proof (translation)
Simplify using `[perp, Submodule.mem_iInf, toDual_apply]`.
-/
theorem mem_perp (J : Matrix (Fin n) (Fin n) K) (A S : Submodule (𝓞 K) (Fin n → K)) (y : Fin n → K) :
    y ∈ perp J A S ↔ y ∈ A ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd K) J s y = 0 := by
  simp [perp, Submodule.mem_iInf, toDual_apply]

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Take `⟨hlat, -, -⟩` from `plLat K V ι b X hX A hA`. Rewrite using `[shiftInv_isSat_iff (Formalism.HermitianLatticesTheory.realize b X) hlat]`. Use `⟨inf_le_left, fun N h1 h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨-, hr1, -⟩` from `plLat K V ι b X hX N (Submodule.FG.of_le hA h2)`.

Take `⟨-, hr2, -⟩` from `plLat K V ι b X hX (A ⊓ W.restrictScalars (𝓞 K)) (Submodule.FG.of_le hA inf_le_left)`. Rewrite `h3` using `[hr1, hr2]`. Establish `h4` using `Nat.eq_of_mul_eq_mul_left Module.finrank_pos h3`. Establish `hsp : Submodule.span K ((A ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = Submodule.span K (N : Set V)` using `Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono h1) h4.symm`. Use `le_antisymm (fun x hx => ⟨h2 hx, ?_⟩) h1` and prove the remaining obligations.

Establish `h5 : Submodule.span K (N : Set V) ≤ W`. Rewrite using `[← hsp, Submodule.span_le]`. Conclude with `fun z hz => hz.2`. Conclude with `h5 (Submodule.subset_span hx)`.
-/
theorem sat_inf {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG) (W : Submodule K V) :
    IsSat (Formalism.HermitianLatticesTheory.realize b X) A (A ⊓ W.restrictScalars (𝓞 K)) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨hlat, -, -⟩ := plLat K V ι b X hX A hA
  rw [shiftInv_isSat_iff (Formalism.HermitianLatticesTheory.realize b X) hlat]
  refine ⟨inf_le_left, fun N h1 h2 h3 => ?_⟩
  obtain ⟨-, hr1, -⟩ := plLat K V ι b X hX N (Submodule.FG.of_le hA h2)
  obtain ⟨-, hr2, -⟩ := plLat K V ι b X hX (A ⊓ W.restrictScalars (𝓞 K))
    (Submodule.FG.of_le hA inf_le_left)
  rw [hr1, hr2] at h3
  have h4 := Nat.eq_of_mul_eq_mul_left Module.finrank_pos h3
  have hsp : Submodule.span K ((A ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (N : Set V) :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono h1) h4.symm
  refine le_antisymm (fun x hx => ⟨h2 hx, ?_⟩) h1
  have h5 : Submodule.span K (N : Set V) ≤ W := by
    rw [← hsp, Submodule.span_le]
    exact fun z hz => hz.2
  exact h5 (Submodule.subset_span hx)

/- English proof (translation)
Use `set b := Pi.basisFun K (Fin n) with hb`. Establish `hX'` using `DualPolygon.dualFrame_unit X hX`. Establish `hR : (dualLat A ⊓ DualPolygon.annO S).FG` using `Submodule.FG.of_le (DualPolygon.dualLat_fg A hsp) inf_le_left`. Establish `hP : (perp J A S).FG` using `Submodule.FG.of_le hA inf_le_left`. Take `⟨l1, r1, -⟩` from `plLat K _ _ b X hX _ hP`.

Take `⟨l2, r2, -⟩` from `plLat K _ _ b.dualBasis (dualFrame X) hX' _ hR`. Establish `hmem : ∀ y, toDual J y ∈ dualLat A ⊓ DualPolygon.annO S ↔ y ∈ perp J A S`. Introduce `y`. Rewrite using `[mem_perp, hd y]`. Use `and_congr (forall₂_congr fun z _ => ?_) (forall₂_congr fun z _ => ?_)` and prove the remaining obligations.

Rewrite using `[toDual_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hform_swap hJ]`. Conclude with `star_mem_range h`.

Introduce `h`. Rewrite using `[hform_swap hJ]`. Conclude with `star_mem_range h`. Rewrite using `[toDual_apply, hform_swap hJ, star_eq_zero]`. Establish `hzl : zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ DualPolygon.annO S) = ((perp J A S).toAddSubgroup.map ((Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)).comp (toDual J))).toIntSubmodule`.

Use extensionality with `w`. Rewrite using `[satR_mem_zl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Take `⟨y, rfl⟩` from `toDual_surj hdet f`.

Conclude with `⟨y, (hmem y).1 hf, rfl⟩`. Introduce `hw`. Take `⟨y, hy, rfl⟩` from `AddSubgroup.mem_map.1 hw`. Conclude with `⟨_, (hmem y).2 hy, rfl⟩`. Take `⟨c1, c2⟩` from `Rerealization.covol_rk_eq (Formalism.HermitianLatticesTheory.realize b X) ((Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)).comp (toDual J)) (fun y => norm_toDual hs X hX hXJ y) (perp J A S).toAddSubgroup l1.2 (hzl ▸ l2.2)`.

Rewrite `c1`, `c2` using `[← hzl]`. Establish `hrk : rkK (dualLat A ⊓ DualPolygon.annO S) = rkK (perp J A S)`. Establish `h : rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ DualPolygon.annO S) = rk (Formalism.HermitianLatticesTheory.realize b X) (perp J A S)` using `c2`. Rewrite `h` using `[r1, r2]`. Conclude with `Nat.eq_of_mul_eq_mul_left Module.finrank_pos h`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrk, (DualPolygon.key_lemma b X hX A hA hsp S hS).1]`. Simplify using the standard rewrite rules. Rewrite using `[← DualPolygon.ht_dual_ann b X hX A hA hsp S hS]`. Use `congr 1`.

Unfold `ht`. Rewrite using `[hrk, c1]`. Both sides reduce to the same expression.
-/
theorem perp_key [IsTotallyComplex K] {J : Matrix (Fin n) (Fin n) K}
    (hJ : Formalism.UG.IsHerm (starRingEnd K) J) (hdet : J.det ≠ 0)
    (hs : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (hXJ : ∀ v, ∃ ε, (X v)ᴴ * J.map v.embedding * X v = Jm ε)
    (A : Submodule (𝓞 K) (Fin n → K)) (hA : A.FG) (hsp : Submodule.span K (A : Set (Fin n → K)) = ⊤)
    (hd : ∀ y, y ∈ A ↔ ∀ z ∈ A, Formalism.UG.hform (starRingEnd K) J z y ∈ (algebraMap (𝓞 K) K).range)
    (S : Submodule (𝓞 K) (Fin n → K)) (hS : IsSat (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X) A S) :
    rkK (perp J A S) + rkK S = n ∧
      ht (Pi.basisFun K (Fin n)) X (perp J A S) * ht (Pi.basisFun K (Fin n)) X A =
        ht (Pi.basisFun K (Fin n)) X S := by
  set b := Pi.basisFun K (Fin n) with hb
  have hX' := DualPolygon.dualFrame_unit X hX
  have hR : (dualLat A ⊓ DualPolygon.annO S).FG :=
    Submodule.FG.of_le (DualPolygon.dualLat_fg A hsp) inf_le_left
  have hP : (perp J A S).FG := Submodule.FG.of_le hA inf_le_left
  obtain ⟨l1, r1, -⟩ := plLat K _ _ b X hX _ hP
  obtain ⟨l2, r2, -⟩ := plLat K _ _ b.dualBasis (dualFrame X) hX' _ hR
  have hmem : ∀ y, toDual J y ∈ dualLat A ⊓ DualPolygon.annO S ↔ y ∈ perp J A S := by
    intro y
    rw [mem_perp, hd y]
    refine and_congr (forall₂_congr fun z _ => ?_) (forall₂_congr fun z _ => ?_)
    · rw [toDual_apply]
      constructor
      · intro h
        rw [hform_swap hJ]
        exact star_mem_range h
      · intro h
        rw [hform_swap hJ]
        exact star_mem_range h
    · rw [toDual_apply, hform_swap hJ, star_eq_zero]
  have hzl : zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ DualPolygon.annO S) =
      ((perp J A S).toAddSubgroup.map
        ((Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)).comp (toDual J))).toIntSubmodule := by
    ext w
    rw [satR_mem_zl]
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨y, rfl⟩ := toDual_surj hdet f
      exact ⟨y, (hmem y).1 hf, rfl⟩
    · intro hw
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hw
      exact ⟨_, (hmem y).2 hy, rfl⟩
  obtain ⟨c1, c2⟩ := Rerealization.covol_rk_eq (Formalism.HermitianLatticesTheory.realize b X)
    ((Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)).comp (toDual J))
    (fun y => norm_toDual hs X hX hXJ y) (perp J A S).toAddSubgroup l1.2 (hzl ▸ l2.2)
  rw [← hzl] at c1 c2
  have hrk : rkK (dualLat A ⊓ DualPolygon.annO S) = rkK (perp J A S) := by
    have h : rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ DualPolygon.annO S) =
        rk (Formalism.HermitianLatticesTheory.realize b X) (perp J A S) := c2
    rw [r1, r2] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h
  refine ⟨?_, ?_⟩
  · rw [← hrk, (DualPolygon.key_lemma b X hX A hA hsp S hS).1]
    simp
  · rw [← DualPolygon.ht_dual_ann b X hX A hA hsp S hS]
    congr 1
    unfold ht
    rw [hrk, c1]
    rfl

end Form

section Slope

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)

variable (K) in

def cK : ℝ := Real.log 2 / 2 - logDisc K / (2 * (Module.finrank ℚ K : ℝ))

def nd (N : Submodule (𝓞 K) V) : ℝ :=
  deg (Formalism.HermitianLatticesTheory.realize b X) N - cK K * rk (Formalism.HermitianLatticesTheory.realize b X) N

/- English proof (translation)
Establish `hd : 0 < |(NumberField.discr K : ℝ)|` using `abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)`. Establish `hn : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hf : (nPl K : ℝ) = (Module.finrank ℚ K : ℝ) / 2`. Rewrite using `[sizeMu_finrank_eq K]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hd, ← Real.exp_add, hf]`. Use `congr 1`. Unfold `cK logDisc`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pre_eq (j : ℝ) :
    (2 : ℝ) ^ ((nPl K : ℝ) * j) * |(NumberField.discr K : ℝ)| ^ (-j / 2) =
      Real.exp (cK K * ((Module.finrank ℚ K : ℝ) * j)) := by
  have hd : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hf : (nPl K : ℝ) = (Module.finrank ℚ K : ℝ) / 2 := by
    rw [sizeMu_finrank_eq K]; push_cast; ring
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hd, ← Real.exp_add, hf]
  congr 1
  unfold cK logDisc
  field_simp
  ring

/- English proof (translation)
Take `⟨l, r, -⟩` from `plLat K V ι b X hX N hN`. Unfold `ht nd`. Rewrite using `[show (2 : ℝ) ^ (nPl K * rkK N) = (2 : ℝ) ^ ((nPl K : ℝ) * (rkK N : ℝ)) by`. Rewrite using `[← Real.rpow_natCast]`. Use `push_cast`.

Use the proof step `rfl, pre_eq, Rerealization.covol_eq_exp _ l.2,`. Use the proof step `← Real.exp_add, r]`. Use `congr 1`. Unfold `deg`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ht_eq (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (hN : N.FG) :
    ht b X N = Real.exp (-nd b X N) := by
  obtain ⟨l, r, -⟩ := plLat K V ι b X hX N hN
  unfold ht nd
  rw [show (2 : ℝ) ^ (nPl K * rkK N) = (2 : ℝ) ^ ((nPl K : ℝ) * (rkK N : ℝ)) by
      rw [← Real.rpow_natCast]; push_cast; rfl, pre_eq, Rerealization.covol_eq_exp _ l.2,
    ← Real.exp_add, r]
  congr 1
  unfold deg
  push_cast
  ring

/- English proof (translation)
Take `⟨l, r, -⟩` from `plLat K V ι b X hX N hN`. Take `⟨-, r', -⟩` from `plLat K V ι b X hX S (Submodule.FG.of_le hN hS.1)`. Take `⟨q1, -, q3⟩` from `Formalism.F.degQuot _ _ _ l.2 hS.2`. Unfold `htQ nd`. Rewrite using `[pre_eq, Rerealization.covol_eq_exp _ q1, ← Real.exp_add, r, r']`.

Use `congr 1`. Unfold `deg`. Rewrite using `[q3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem htQ_eq (hX : ∀ v, IsUnit (X v).det) (N S : Submodule (𝓞 K) V) (hN : N.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) N S) :
    htQ b X N S = Real.exp (nd b X S - nd b X N) := by
  obtain ⟨l, r, -⟩ := plLat K V ι b X hX N hN
  obtain ⟨-, r', -⟩ := plLat K V ι b X hX S (Submodule.FG.of_le hN hS.1)
  obtain ⟨q1, -, q3⟩ := Formalism.F.degQuot _ _ _ l.2 hS.2
  unfold htQ nd
  rw [pre_eq, Rerealization.covol_eq_exp _ q1, ← Real.exp_add, r, r']
  congr 1
  unfold deg
  rw [q3]
  push_cast
  ring

omit [IsTotallyComplex K] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨h1, shiftInv_zl_mono _ h1, fun x hx => hS.2.2 x (shiftInv_zl_mono _ h2 hx)⟩`.
-/
theorem sat_mono {A N S : Submodule (𝓞 K) V} (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S)
    (h1 : S ≤ N) (h2 : N ≤ A) : IsSat (Formalism.HermitianLatticesTheory.realize b X) N S :=
  ⟨h1, shiftInv_zl_mono _ h1, fun x hx => hS.2.2 x (shiftInv_zl_mono _ h2 hx)⟩

omit [IsTotallyComplex K] in
/- English proof (translation)
Take `⟨l, -, -⟩` from `plLat K V ι b X hX A hA`. Establish `hSB` using `satBasic (𝓞 K) V _ _ A l`. Establish `h` using `(hSB.2.1 S N h1.le h2).1`. Establish `h' : rk (Formalism.HermitianLatticesTheory.realize b X) N ≠ rk (Formalism.HermitianLatticesTheory.realize b X) S` using `fun e => h1.ne' (hSB.2.2.1 S N hS h1.le h2 e)`. Conclude with `lt_of_le_of_ne h h'.symm` after adjusting the coercions.
-/
theorem rk_lt (hX : ∀ v, IsUnit (X v).det) {A N S : Submodule (𝓞 K) V} (hA : A.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S) (h1 : S < N) (h2 : N ≤ A) :
    (rk (Formalism.HermitianLatticesTheory.realize b X) S : ℝ) < rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  obtain ⟨l, -, -⟩ := plLat K V ι b X hX A hA
  have hSB := satBasic (𝓞 K) V _ _ A l
  have h := (hSB.2.1 S N h1.le h2).1
  have h' : rk (Formalism.HermitianLatticesTheory.realize b X) N ≠ rk (Formalism.HermitianLatticesTheory.realize b X) S :=
    fun e => h1.ne' (hSB.2.2.1 S N hS h1.le h2 e)
  exact_mod_cast lt_of_le_of_ne h h'.symm

/- English proof (translation)
Establish `hN` using `Submodule.FG.of_le hA h2`. Take `⟨-, r, -⟩` from `plLat K V ι b X hX N hN`. Take `⟨-, r', -⟩` from `plLat K V ι b X hX S (Submodule.FG.of_le hA hS.1)`. Unfold `sizeQ`. Rewrite using `[htQ_eq b X hX N S hN (sat_mono b X hS h1.le h2), ← Real.exp_mul, r, r', sizeMu_finrank_eq K]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[mul_one_div]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_sizeQ (hX : ∀ v, IsUnit (X v).det) {A N S : Submodule (𝓞 K) V} (hA : A.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S) (h1 : S < N) (h2 : N ≤ A) :
    sizeQ b X N S = Real.exp ((nd b X S - nd b X N) /
      ((rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) - rk (Formalism.HermitianLatticesTheory.realize b X) S)) := by
  have hN := Submodule.FG.of_le hA h2
  obtain ⟨-, r, -⟩ := plLat K V ι b X hX N hN
  obtain ⟨-, r', -⟩ := plLat K V ι b X hX S (Submodule.FG.of_le hA hS.1)
  unfold sizeQ
  rw [htQ_eq b X hX N S hN (sat_mono b X hS h1.le h2), ← Real.exp_mul, r, r', sizeMu_finrank_eq K]
  congr 1
  push_cast
  rw [mul_one_div]
  congr 1
  ring

/- English proof (translation)
Take `⟨l, -, -⟩` from `plLat K V ι b X hX N hN`. Establish `h1 : largestSize b X N = Real.exp (cK K - muMin (Formalism.HermitianLatticesTheory.realize b X) N)` using `(sizeMu K V ι b X hX N hN hN0).2.2.2.2.1`. Establish `h2` using `((muChar (𝓞 K) V _ _ N l hN0).2.1 _).1 le_rfl M h`. Rewrite using `[h1, Real.log_exp]`. Use `⟨Real.exp_pos _, ?_⟩` and prove the remaining obligations.

Unfold `nd`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem largest_bound (hX : ∀ v, IsUnit (X v).det) {N M : Submodule (𝓞 K) V} (hN : N.FG)
    (hN0 : N ≠ ⊥) (h : M ≤ N) :
    0 < largestSize b X N ∧ nd b X M - nd b X N ≤ Real.log (largestSize b X N) *
      ((rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) - rk (Formalism.HermitianLatticesTheory.realize b X) M) := by
  obtain ⟨l, -, -⟩ := plLat K V ι b X hX N hN
  have h1 : largestSize b X N = Real.exp (cK K - muMin (Formalism.HermitianLatticesTheory.realize b X) N) :=
    (sizeMu K V ι b X hX N hN hN0).2.2.2.2.1
  have h2 := ((muChar (𝓞 K) V _ _ N l hN0).2.1 _).1 le_rfl M h
  rw [h1, Real.log_exp]
  refine ⟨Real.exp_pos _, ?_⟩
  unfold nd
  linarith

omit [IsTotallyComplex K] in
/- English proof (translation)
Use `⟨inf_le_left.trans hP.1, shiftInv_zl_mono _ (inf_le_left.trans hP.1), fun x hx hx' => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, rfl⟩` from `(satR_mem_zl _ _ _).1 (hP.2.2 x hx (Submodule.span_mono (shiftInv_zl_mono _ (inf_le_left : P ⊓ Q ≤ P)) hx'))`. Take `⟨q, hq, e⟩` from `(satR_mem_zl _ _ _).1 (hQ.2.2 _ hx (Submodule.span_mono (shiftInv_zl_mono _ (inf_le_right : P ⊓ Q ≤ Q)) hx'))`. Take `rfl` from `PlaceLattice.realize_injective b X hX e`. Conclude with `(satR_mem_zl _ _ _).2 ⟨q, ⟨hp, hq⟩, rfl⟩`.
-/
theorem sat_inf_sat (hX : ∀ v, IsUnit (X v).det) {A P Q : Submodule (𝓞 K) V}
    (hP : IsSat (Formalism.HermitianLatticesTheory.realize b X) A P) (hQ : IsSat (Formalism.HermitianLatticesTheory.realize b X) A Q) :
    IsSat (Formalism.HermitianLatticesTheory.realize b X) A (P ⊓ Q) := by
  refine ⟨inf_le_left.trans hP.1, shiftInv_zl_mono _ (inf_le_left.trans hP.1), fun x hx hx' => ?_⟩
  obtain ⟨p, hp, rfl⟩ := (satR_mem_zl _ _ _).1 (hP.2.2 x hx
    (Submodule.span_mono (shiftInv_zl_mono _ (inf_le_left : P ⊓ Q ≤ P)) hx'))
  obtain ⟨q, hq, e⟩ := (satR_mem_zl _ _ _).1 (hQ.2.2 _ hx
    (Submodule.span_mono (shiftInv_zl_mono _ (inf_le_right : P ⊓ Q ≤ Q)) hx'))
  obtain rfl := PlaceLattice.realize_injective b X hX e
  exact (satR_mem_zl _ _ _).2 ⟨q, ⟨hp, hq⟩, rfl⟩

/- English proof (translation)
Take `⟨N', h1, h2, h3, h4⟩` from `DualPolygon.sat_exists b X hX A hA N h`. Use `⟨N', h1, h2, h3, ?_⟩` and prove the remaining obligations. Unfold `nd`. Rewrite using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nd_sat (hX : ∀ v, IsUnit (X v).det) {A N : Submodule (𝓞 K) V} (hA : A.FG) (h : N ≤ A) :
    ∃ N', N ≤ N' ∧ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N' ∧
      rk (Formalism.HermitianLatticesTheory.realize b X) N' = rk (Formalism.HermitianLatticesTheory.realize b X) N ∧ nd b X N ≤ nd b X N' := by
  obtain ⟨N', h1, h2, h3, h4⟩ := DualPolygon.sat_exists b X hX A hA N h
  refine ⟨N', h1, h2, h3, ?_⟩
  unfold nd
  rw [h3]
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨lA, -, -⟩` from `plLat K V ι b X hX A hA`. Establish `hlt : P ⊓ Q < P` using `lt_of_le_of_ne inf_le_left fun e => hne (inf_eq_left.1 e)`. Establish `a1` using `h1 _ (sat_inf_sat b X hX hP hQ) hlt`. Take `⟨N, n1, n2, n3, n4⟩` from `nd_sat b X hX hA (sup_le hP.1 hQ.1)`.

Establish `a2` using `h2 N n2 (le_sup_right.trans n1)`. Take `⟨s1, s2⟩` from `degSupermod (𝓞 K) V _ _ A P Q lA hP.1 hQ.1`. Establish `s1' : (rk (Formalism.HermitianLatticesTheory.realize b X) (P ⊔ Q) : ℝ) + rk (Formalism.HermitianLatticesTheory.realize b X) (P ⊓ Q) = rk (Formalism.HermitianLatticesTheory.realize b X) P + rk (Formalism.HermitianLatticesTheory.realize b X) Q` using `by exact_mod_cast s1`. Rewrite `a2` using `[n3]`. Establish `e1` using `congrArg (fun t => l * t) s1'`.

Establish `e2` using `congrArg (fun t => cK K * t) s1'`. Simplify using `only [mul_add] at e1 e2`. Unfold `nd at a1 n4`. Unfold `nd at a2`. Rewrite `a2`, `n4` using `[n3]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_of_slopes (hX : ∀ v, IsUnit (X v).det) {A P Q : Submodule (𝓞 K) V} (hA : A.FG) (l : ℝ)
    (hP : IsSat (Formalism.HermitianLatticesTheory.realize b X) A P) (hQ : IsSat (Formalism.HermitianLatticesTheory.realize b X) A Q)
    (h1 : ∀ M, IsSat (Formalism.HermitianLatticesTheory.realize b X) A M → M < P →
      nd b X M - l * rk (Formalism.HermitianLatticesTheory.realize b X) M < nd b X P - l * rk (Formalism.HermitianLatticesTheory.realize b X) P)
    (h2 : ∀ M, IsSat (Formalism.HermitianLatticesTheory.realize b X) A M → Q ≤ M →
      nd b X M - l * rk (Formalism.HermitianLatticesTheory.realize b X) M ≤ nd b X Q - l * rk (Formalism.HermitianLatticesTheory.realize b X) Q) :
    P ≤ Q := by
  by_contra hne
  obtain ⟨lA, -, -⟩ := plLat K V ι b X hX A hA
  have hlt : P ⊓ Q < P := lt_of_le_of_ne inf_le_left fun e => hne (inf_eq_left.1 e)
  have a1 := h1 _ (sat_inf_sat b X hX hP hQ) hlt
  obtain ⟨N, n1, n2, n3, n4⟩ := nd_sat b X hX hA (sup_le hP.1 hQ.1)
  have a2 := h2 N n2 (le_sup_right.trans n1)
  obtain ⟨s1, s2⟩ := degSupermod (𝓞 K) V _ _ A P Q lA hP.1 hQ.1
  have s1' : (rk (Formalism.HermitianLatticesTheory.realize b X) (P ⊔ Q) : ℝ) + rk (Formalism.HermitianLatticesTheory.realize b X) (P ⊓ Q) =
      rk (Formalism.HermitianLatticesTheory.realize b X) P + rk (Formalism.HermitianLatticesTheory.realize b X) Q := by exact_mod_cast s1
  rw [n3] at a2
  have e1 := congrArg (fun t => l * t) s1'
  have e2 := congrArg (fun t => cK K * t) s1'
  simp only [mul_add] at e1 e2
  unfold nd at a1 n4
  unfold nd at a2
  rw [n3] at a2 n4
  linarith

end Slope

section Main

variable (I : AutInst) (x : I.GA)

/- English proof (translation)
Unfold `perpIn`. Rewrite using `[← Submodule.span_eq (perp I.J (lamX I x) S)]`. Use `congr 1`. Use extensionality with `y`. Conclude with `(mem_perp _ _ _ y).symm`.
-/
theorem perpIn_eq (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    perpIn I x S = perp I.J (lamX I x) S := by
  unfold perpIn
  rw [← Submodule.span_eq (perp I.J (lamX I x) S)]
  congr 1
  ext y
  exact (mem_perp _ _ _ y).symm

end Main

/- English proof (translation)
Introduce `I x`. Take `⟨-, hA, hsp, hd, -⟩` from `GlobalTheory.PointLattice.lamX_selfDual I x`. Take `⟨htc, -, -, -, hw⟩` from `GlobalTheory.Count.FrameMajorant.frames_give_majorants I x`. Establish `hX : ∀ v, IsUnit (frm I x v).det` using `fun v => (hw v).1`. Establish `key` using `perp_key I.J_herm I.J_det I.cm.cmUnram.2.1 (frm I x) hX (fun v => ⟨_, (hw v).2.1⟩) (lamX I x) hA hsp hd`.

Simplify using `only [perpIn_eq]`. Use `set A := lamX I x with hAdef`. Use `set X := frm I x with hXdef`. Use `set b := bas I with hb`. Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`.

Take `⟨lA, rA, pA⟩` from `plLat _ _ _ b X hX A hA`. Establish `hSB` using `satBasic (𝓞 I.E) _ _ ρ A lA`. Establish `hfg : ∀ {N}, N ≤ A → N.FG` using `fun h => Submodule.FG.of_le hA h`. Establish `psat : ∀ S, IsSat ρ A (perp I.J A S)` using `fun S => sat_inf b X hX A hA _`. Establish `panti : ∀ {S S'}, S ≤ S' → perp I.J A S' ≤ perp I.J A S`.

Introduce `S S' h y hy`. Rewrite `hy`, the goal using `[mem_perp]`. Conclude with `⟨hy.1, fun s hs => hy.2 s (h hs)⟩`. Establish `hrkA : rkK A = I.n`. Unfold `rkK`.

Rewrite using `[hsp, finrank_top]`. Simplify using the standard rewrite rules. Establish `prk : ∀ S, IsSat ρ A S → rk ρ (perp I.J A S) + rk ρ S = rk ρ A`. Introduce `S hS`. Rewrite using `[(plLat _ _ _ b X hX _ (hfg hS.1)).2.1, (plLat _ _ _ b X hX _ (hfg (psat S).1)).2.1, rA, hrkA, ← mul_add, (key S hS).1]`.

Establish `prk' : ∀ S, IsSat ρ A S → (rk ρ (perp I.J A S) : ℝ) = rk ρ A - rk ρ S`. Introduce `S hS`. Rewrite using `[← prk S hS]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `pp : ∀ S, IsSat ρ A S → perp I.J A (perp I.J A S) = S`. Introduce `S hS`. Use `hSB.2.2.1 S _ hS (fun y hy => ?_) (psat _).1 ?_` and prove the remaining obligations. Rewrite using `[mem_perp]`. Use `⟨hS.1 hy, fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[hform_swap I.J_herm, ((mem_perp _ _ _ _).1 hs).2 y hy, star_zero]`. Establish `h1` using `prk S hS`. Establish `h2` using `prk _ (psat S)`. Use linear arithmetic over natural numbers and integers. Establish `pbot : perp I.J A ⊥ = A`.

Use extensionality with `y`. Rewrite using `[mem_perp]`. Use `⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(Submodule.mem_bot _).1 hs]`. Simplify using `[Formalism.UG.hform]`.

Establish `ht1 : ht b X A = 1`. Establish `h` using `(key ⊥ hSB.2.2.2.2.2.1).2`. Rewrite `h` using `[pbot, DualPolygon.ht_bot]`. Express the relevant statement in the definitionally equal form `ht b X A * ht b X A = 1 at h`. Use the polynomial consequences of the given equalities and inequalities.

Establish `pnd : ∀ S, IsSat ρ A S → nd b X (perp I.J A S) = nd b X S`. Introduce `S hS`. Establish `h` using `(key S hS).2`. Express the relevant statement in the definitionally equal form `ht b X _ * ht b X A = ht b X S at h`. Rewrite `h` using `[ht1, mul_one, ht_eq b X hX _ (hfg hS.1), ht_eq b X hX _ (hfg (psat S).1)]`.

Conclude with `neg_injective (Real.exp_injective h)`. Establish `ndA : nd b X A = 0`. Rewrite `ht1` using `[ht_eq b X hX A hA, Real.exp_eq_one_iff]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `step : ∀ t : ℝ, 0 < t → perp I.J A (stepLe I x t) = stepLt I x t⁻¹`.

Introduce `t ht`. Take `⟨sB, -, -, -, b1, -, b2, -⟩` from `GlobalTheory.CountSteps.steps I x t ht`. Take `⟨-, sQ, -, -, -, q1, -, q2, -⟩` from `GlobalTheory.CountSteps.steps I x t⁻¹ (inv_pos.2 ht)`. Use `set B := stepLe I x t`. Use `set Q := stepLt I x t⁻¹`.

Apply `le_antisymm` to reduce the goal to its premises. Use `le_of_slopes b X hX hA (Real.log t) (psat B) sQ ?_ ?_` and prove the remaining obligations. Introduce `M hM hlt`. Establish `h1 : B < perp I.J A M`. Use `lt_of_le_of_ne ((pp B sB).symm.le.trans (panti hlt.le)) fun e => hlt.ne ?_` and prove the remaining obligations.

Rewrite using `[e, pp M hM]`. Establish `h2` using `b2 _ h1 (psat M).1`. Establish `h3` using `rk_lt b X hX hA sB h1 (psat M).1`. Rewrite `h2` using `[log_sizeQ b X hX hA sB h1 (psat M).1, ← Real.log_lt_iff_lt_exp ht, lt_div_iff₀ (sub_pos.2 h3), pnd M hM, prk' M hM]`. Rewrite using `[pnd B sB, prk' B sB]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `M hM hle`. Break down `hle.eq_or_lt with rfl | hlt` into its components or cases. Conclude with `le_rfl`. Establish `h2` using `q2 _ hlt hM.1`.

Establish `h3` using `rk_lt b X hX hA sQ hlt hM.1`. Rewrite `h2` using `[log_sizeQ b X hX hA sQ hlt hM.1, ← Real.log_le_iff_le_exp (inv_pos.2 ht), le_div_iff₀ (sub_pos.2 h3), Real.log_inv]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_of_slopes b X hX hA (Real.log t) sQ (psat B) ?_ ?_` and prove the remaining obligations. Introduce `M hM hlt`.

Establish `h0 : Q ≠ ⊥` using `ne_bot_of_gt hlt`. Take `⟨h1, h2⟩` from `largest_bound b X hX (hfg sQ.1) h0 hlt.le`. Establish `h3` using `rk_lt b X hX hA hM hlt sQ.1`. Establish `h4` using `Real.log_lt_log h1 (q1 h0)`. Rewrite `h4` using `[Real.log_inv]`.

Establish `h5` using `mul_lt_mul_of_pos_right h4 (sub_pos.2 h3)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `M hM hle`. Establish `h1 : perp I.J A M ≤ B` using `(panti hle).trans (pp B sB).le`. Rewrite using `[pnd B sB, prk' B sB, ← pnd M hM]`.

Establish `h6` using `prk' M hM`. Break down `h1.eq_or_lt with e | hlt` into its components or cases. Rewrite `h6`, the goal using `[e]`. Rewrite using `[h6]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h0 : B ≠ ⊥` using `ne_bot_of_gt hlt`. Take `⟨h1, h2⟩` from `largest_bound b X hX (hfg sB.1) h0 hlt.le`. Establish `h3` using `rk_lt b X hX hA (psat M) hlt sB.1`. Establish `h4` using `Real.log_le_log h1 (b1 h0)`. Establish `h5` using `mul_le_mul_of_nonneg_right h4 (sub_pos.2 h3).le`.

Rewrite `h2`, `h5` using `[h6]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨ht1, fun hn => ?_, fun t ht => ⟨step t ht, ?_⟩, fun S S' hS hS' hle => ⟨psat S, (key S hS).1, pp S hS, panti hle, ?_⟩⟩` and prove the remaining obligations. Establish `hA0 : A ≠ ⊥`. Introduce `e`.

Establish `h0 : rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0` using `by simp [rkK]`. Rewrite `hrkA` using `[e, h0]`. Use linear arithmetic over natural numbers and integers. Take `⟨-, -, -, s1, s2, -⟩` from `sizeMu _ _ _ b X hX A hA hA0`. Express the relevant statement in the definitionally equal form `leastSize b X A = Real.exp (cK I.E - muMax ρ A) at s1`.

Express the relevant statement in the definitionally equal form `largestSize b X A = Real.exp (cK I.E - muMin ρ A) at s2`. Express the relevant statement in the definitionally equal form `largestSize b X A = (leastSize b X A)⁻¹`. Take `⟨m1, m2, -⟩` from `muChar (𝓞 I.E) _ _ ρ A lA hA0`. Establish `e : muMin ρ A = 2 * cK I.E - muMax ρ A`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `h : muMax ρ A ≤ 2 * cK I.E - muMin ρ A`. Rewrite using `[m1]`. Introduce `N hN`. Take `⟨N', -, n2, n3, n4⟩` from `nd_sat b X hX hA hN`. Establish `h1` using `(m2 _).1 le_rfl _ (psat N').1`.

Establish `h2` using `pnd N' n2`. Establish `h3` using `prk' N' n2`. Unfold `nd at h2 n4 ndA`. Rewrite `h2`, `n4`, `ndA` using `[← hρ]`. Rewrite `h1`, `h2` using `[h3]`.

Rewrite `h1`, `h2`, `n4` using `[n3]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[m2]`. Introduce `N hN`.

Take `⟨N', -, n2, n3, n4⟩` from `nd_sat b X hX hA hN`. Establish `h1` using `(m1 _).1 le_rfl _ (psat N').1`. Establish `h2` using `pnd N' n2`. Establish `h3` using `prk' N' n2`. Unfold `nd at h2 n4 ndA`.

Rewrite `h2`, `n4`, `ndA` using `[← hρ]`. Rewrite `h1`, `h2` using `[h3]`. Rewrite `h1`, `h2`, `n4` using `[n3]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[s1, s2, e, ← Real.exp_neg]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `step t⁻¹ (inv_pos.2 ht)`. Rewrite `h` using `[inv_inv]`. Rewrite using `[← h, pp _ (GlobalTheory.CountSteps.steps I x t⁻¹ (inv_pos.2 ht)).1]`.

Rewrite using `[htQ_eq b X hX _ _ (hfg (psat S).1) (sat_mono b X (psat S') (panti hle) (psat S).1), htQ_eq b X hX _ _ (hfg hS'.1) (sat_mono b X hS hle hS'.1), pnd S hS, pnd S' hS', ← Real.exp_neg, neg_sub]`.
-/
theorem main : ∀ (I : AutInst) (x : I.GA), ht (bas I) (frm I x) (lamX I x) = 1 ∧ (1 ≤ I.n → largestSize (bas I) (frm I x) (lamX I x) = (least I x)⁻¹) ∧ (∀ t : ℝ, 0 < t → perpIn I x (stepLe I x t) = stepLt I x t⁻¹ ∧ perpIn I x (stepLt I x t) = stepLe I x t⁻¹) ∧ ∀ S S' : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S' → S ≤ S' → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (perpIn I x S) ∧ rkK (perpIn I x S) + rkK S = I.n ∧ perpIn I x (perpIn I x S) = S ∧ perpIn I x S' ≤ perpIn I x S ∧ htQ (bas I) (frm I x) (perpIn I x S) (perpIn I x S') = (htQ (bas I) (frm I x) S' S)⁻¹ := by
  intro I x
  obtain ⟨-, hA, hsp, hd, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨htc, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  have key := perp_key I.J_herm I.J_det I.cm.cmUnram.2.1 (frm I x) hX
    (fun v => ⟨_, (hw v).2.1⟩) (lamX I x) hA hsp hd
  simp only [perpIn_eq]
  set A := lamX I x with hAdef
  set X := frm I x with hXdef
  set b := bas I with hb
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  obtain ⟨lA, rA, pA⟩ := plLat _ _ _ b X hX A hA
  have hSB := satBasic (𝓞 I.E) _ _ ρ A lA
  have hfg : ∀ {N}, N ≤ A → N.FG := fun h => Submodule.FG.of_le hA h
  have psat : ∀ S, IsSat ρ A (perp I.J A S) := fun S => sat_inf b X hX A hA _
  have panti : ∀ {S S'}, S ≤ S' → perp I.J A S' ≤ perp I.J A S := by
    intro S S' h y hy
    rw [mem_perp] at hy ⊢
    exact ⟨hy.1, fun s hs => hy.2 s (h hs)⟩
  have hrkA : rkK A = I.n := by
    unfold rkK
    rw [hsp, finrank_top]
    simp
  have prk : ∀ S, IsSat ρ A S → rk ρ (perp I.J A S) + rk ρ S = rk ρ A := by
    intro S hS
    rw [(plLat _ _ _ b X hX _ (hfg hS.1)).2.1, (plLat _ _ _ b X hX _ (hfg (psat S).1)).2.1, rA,
      hrkA, ← mul_add, (key S hS).1]
  have prk' : ∀ S, IsSat ρ A S → (rk ρ (perp I.J A S) : ℝ) = rk ρ A - rk ρ S := by
    intro S hS
    rw [← prk S hS]
    push_cast
    ring
  have pp : ∀ S, IsSat ρ A S → perp I.J A (perp I.J A S) = S := by
    intro S hS
    refine hSB.2.2.1 S _ hS (fun y hy => ?_) (psat _).1 ?_
    · rw [mem_perp]
      refine ⟨hS.1 hy, fun s hs => ?_⟩
      rw [hform_swap I.J_herm, ((mem_perp _ _ _ _).1 hs).2 y hy, star_zero]
    · have h1 := prk S hS
      have h2 := prk _ (psat S)
      omega
  have pbot : perp I.J A ⊥ = A := by
    ext y
    rw [mem_perp]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp [Formalism.UG.hform]
  have ht1 : ht b X A = 1 := by
    have h := (key ⊥ hSB.2.2.2.2.2.1).2
    rw [pbot, DualPolygon.ht_bot] at h
    change ht b X A * ht b X A = 1 at h
    nlinarith
  have pnd : ∀ S, IsSat ρ A S → nd b X (perp I.J A S) = nd b X S := by
    intro S hS
    have h := (key S hS).2
    change ht b X _ * ht b X A = ht b X S at h
    rw [ht1, mul_one, ht_eq b X hX _ (hfg hS.1), ht_eq b X hX _ (hfg (psat S).1)] at h
    exact neg_injective (Real.exp_injective h)
  have ndA : nd b X A = 0 := by
    rw [ht_eq b X hX A hA, Real.exp_eq_one_iff] at ht1
    linarith
  have step : ∀ t : ℝ, 0 < t → perp I.J A (stepLe I x t) = stepLt I x t⁻¹ := by
    intro t ht
    obtain ⟨sB, -, -, -, b1, -, b2, -⟩ := GlobalTheory.CountSteps.steps I x t ht
    obtain ⟨-, sQ, -, -, -, q1, -, q2, -⟩ := GlobalTheory.CountSteps.steps I x t⁻¹ (inv_pos.2 ht)
    set B := stepLe I x t
    set Q := stepLt I x t⁻¹
    apply le_antisymm
    · refine le_of_slopes b X hX hA (Real.log t) (psat B) sQ ?_ ?_
      · intro M hM hlt
        have h1 : B < perp I.J A M := by
          refine lt_of_le_of_ne ((pp B sB).symm.le.trans (panti hlt.le)) fun e => hlt.ne ?_
          rw [e, pp M hM]
        have h2 := b2 _ h1 (psat M).1
        have h3 := rk_lt b X hX hA sB h1 (psat M).1
        rw [log_sizeQ b X hX hA sB h1 (psat M).1, ← Real.log_lt_iff_lt_exp ht,
          lt_div_iff₀ (sub_pos.2 h3), pnd M hM, prk' M hM] at h2
        rw [pnd B sB, prk' B sB]
        linarith
      · intro M hM hle
        rcases hle.eq_or_lt with rfl | hlt
        · exact le_rfl
        have h2 := q2 _ hlt hM.1
        have h3 := rk_lt b X hX hA sQ hlt hM.1
        rw [log_sizeQ b X hX hA sQ hlt hM.1, ← Real.log_le_iff_le_exp (inv_pos.2 ht),
          le_div_iff₀ (sub_pos.2 h3), Real.log_inv] at h2
        linarith
    · refine le_of_slopes b X hX hA (Real.log t) sQ (psat B) ?_ ?_
      · intro M hM hlt
        have h0 : Q ≠ ⊥ := ne_bot_of_gt hlt
        obtain ⟨h1, h2⟩ := largest_bound b X hX (hfg sQ.1) h0 hlt.le
        have h3 := rk_lt b X hX hA hM hlt sQ.1
        have h4 := Real.log_lt_log h1 (q1 h0)
        rw [Real.log_inv] at h4
        have h5 := mul_lt_mul_of_pos_right h4 (sub_pos.2 h3)
        linarith
      · intro M hM hle
        have h1 : perp I.J A M ≤ B := (panti hle).trans (pp B sB).le
        rw [pnd B sB, prk' B sB, ← pnd M hM]
        have h6 := prk' M hM
        rcases h1.eq_or_lt with e | hlt
        · rw [e] at h6 ⊢
          rw [h6]
          linarith
        have h0 : B ≠ ⊥ := ne_bot_of_gt hlt
        obtain ⟨h1, h2⟩ := largest_bound b X hX (hfg sB.1) h0 hlt.le
        have h3 := rk_lt b X hX hA (psat M) hlt sB.1
        have h4 := Real.log_le_log h1 (b1 h0)
        have h5 := mul_le_mul_of_nonneg_right h4 (sub_pos.2 h3).le
        rw [h6] at h2 h5
        linarith
  refine ⟨ht1, fun hn => ?_, fun t ht => ⟨step t ht, ?_⟩, fun S S' hS hS' hle =>
    ⟨psat S, (key S hS).1, pp S hS, panti hle, ?_⟩⟩
  · have hA0 : A ≠ ⊥ := by
      intro e
      have h0 : rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 := by simp [rkK]
      rw [e, h0] at hrkA
      omega
    obtain ⟨-, -, -, s1, s2, -⟩ := sizeMu _ _ _ b X hX A hA hA0
    change leastSize b X A = Real.exp (cK I.E - muMax ρ A) at s1
    change largestSize b X A = Real.exp (cK I.E - muMin ρ A) at s2
    change largestSize b X A = (leastSize b X A)⁻¹
    obtain ⟨m1, m2, -⟩ := muChar (𝓞 I.E) _ _ ρ A lA hA0
    have e : muMin ρ A = 2 * cK I.E - muMax ρ A := by
      apply le_antisymm
      · have h : muMax ρ A ≤ 2 * cK I.E - muMin ρ A := by
          rw [m1]
          intro N hN
          obtain ⟨N', -, n2, n3, n4⟩ := nd_sat b X hX hA hN
          have h1 := (m2 _).1 le_rfl _ (psat N').1
          have h2 := pnd N' n2
          have h3 := prk' N' n2
          unfold nd at h2 n4 ndA
          rw [← hρ] at h2 n4 ndA
          rw [h3] at h1 h2
          rw [n3] at h1 h2 n4
          linarith
        linarith
      · rw [m2]
        intro N hN
        obtain ⟨N', -, n2, n3, n4⟩ := nd_sat b X hX hA hN
        have h1 := (m1 _).1 le_rfl _ (psat N').1
        have h2 := pnd N' n2
        have h3 := prk' N' n2
        unfold nd at h2 n4 ndA
        rw [← hρ] at h2 n4 ndA
        rw [h3] at h1 h2
        rw [n3] at h1 h2 n4
        linarith
    rw [s1, s2, e, ← Real.exp_neg]
    congr 1
    ring
  · have h := step t⁻¹ (inv_pos.2 ht)
    rw [inv_inv] at h
    rw [← h, pp _ (GlobalTheory.CountSteps.steps I x t⁻¹ (inv_pos.2 ht)).1]
  · rw [htQ_eq b X hX _ _ (hfg (psat S).1) (sat_mono b X (psat S') (panti hle) (psat S).1),
      htQ_eq b X hX _ _ (hfg hS'.1) (sat_mono b X hS hle hS'.1), pnd S hS, pnd S' hS',
      ← Real.exp_neg, neg_sub]

end GlobalTheory.Count.PerpStep
