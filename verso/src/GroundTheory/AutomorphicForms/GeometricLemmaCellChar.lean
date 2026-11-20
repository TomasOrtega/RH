import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.AutomorphicForms.CuspidalAdmissible
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set MeasureTheory Cartan
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Pattern

variable (γ : Fin n → ℕ) (T : Fin n → Fin n → Prop) [DecidableRel T]

abbrev PatIdx : Type := {p : Fin n × Fin n // T p.1 p.2}

variable (F) in

def patMat (X : PatIdx T → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if h : T i j then X ⟨(i, j), h⟩ else 0

/- English proof (translation)
Simplify using `[patMat, h]`.
-/
theorem patMat_apply_of_not {X : PatIdx T → F} {i j : Fin n} (h : ¬ T i j) :
    patMat F T X i j = 0 := by
  simp [patMat, h]

/- English proof (translation)
Simplify using `[patMat, h]`.
-/
theorem patMat_apply_of_mem {X : PatIdx T → F} {i j : Fin n} (h : T i j) :
    patMat F T X i j = X ⟨(i, j), h⟩ := by
  simp [patMat, h]

variable {γ T}
variable (hT : ∀ i j, T i j → γ i < γ j)
include hT

/- English proof (translation)
Introduce `e` and use `by subst e exact lt_irrefl _ (hT i i h)`.
-/
theorem ne_of_pat {i j : Fin n} (h : T i j) : i ≠ j := fun e => by
  subst e
  exact lt_irrefl _ (hT i i h)

/- English proof (translation)
Introduce `i j hij`. Establish `hij' : ¬ T i j` using `fun h => lt_asymm hij (hT i j h)`. Rewrite using `[Matrix.add_apply, patMat_apply_of_not T hij', add_zero, one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.
-/
theorem blockTriangular_one_add_patMat (X : PatIdx T → F) :
    (1 + patMat F T X).BlockTriangular γ := by
  intro i j hij
  have hij' : ¬ T i j := fun h => lt_asymm hij (hT i j h)
  rw [Matrix.add_apply, patMat_apply_of_not T hij', add_zero, one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

/- English proof (translation)
Rewrite using `[(blockTriangular_one_add_patMat hT X).det]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `: (1 + patMat F T X).toSquareBlock γ a = 1`. Use extensionality with `i j`. Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply, one_apply]`.

Establish `hij : ¬ T i j` using `fun h => by`. Use `hT _ _ h` as an intermediate fact. Rewrite `this` using `[i.2, j.2]`. Conclude with `lt_irrefl _ this`. Rewrite using `[patMat_apply_of_not T hij, add_zero]`.

Simplify using `[Subtype.ext_iff]`. Rewrite using `[this, det_one]`.
-/
theorem det_one_add_patMat (X : PatIdx T → F) : (1 + patMat F T X).det = 1 := by
  classical
  rw [(blockTriangular_one_add_patMat hT X).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (1 + patMat F T X).toSquareBlock γ a = 1 := by
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply, one_apply]
    have hij : ¬ T i j := fun h => by
      have := hT _ _ h
      rw [i.2, j.2] at this
      exact lt_irrefl _ this
    rw [patMat_apply_of_not T hij, add_zero]
    simp [Subtype.ext_iff]
  rw [this, det_one]

variable (F) in

def patUnip (X : PatIdx T → F) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + patMat F T X)
    (by rw [det_one_add_patMat hT]; exact one_ne_zero)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_patUnip (X : PatIdx T → F) :
    ((patUnip F hT X : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + patMat F T X := rfl

omit hT in
variable (T) in

def patCoord (g : GL (Fin n) F) : PatIdx T → F := fun p => (g : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2

/- English proof (translation)
Use function extensionality and compare the values at `p`. Use `show (1 + patMat F T X) p.1.1 p.1.2 = X p`. Rewrite using `[Matrix.add_apply, one_apply_ne (ne_of_pat hT p.2), patMat_apply_of_mem T p.2, zero_add]`.
-/
theorem patCoord_patUnip (X : PatIdx T → F) : patCoord T (patUnip F hT X) = X := by
  funext p
  show (1 + patMat F T X) p.1.1 p.1.2 = X p
  rw [Matrix.add_apply, one_apply_ne (ne_of_pat hT p.2), patMat_apply_of_mem T p.2, zero_add]

abbrev IsPatternGroup (U : Subgroup (GL (Fin n) F)) : Prop :=
  ∀ g : GL (Fin n) F, g ∈ U ↔ ∀ i j, ¬ T i j → (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j

variable {U : Subgroup (GL (Fin n) F)} (hU : IsPatternGroup (F := F) (T := T) U)
include hU

/- English proof (translation)
Rewrite using `[hU]`. Introduce `i j h`. Rewrite using `[coe_patUnip, Matrix.add_apply, patMat_apply_of_not T h, add_zero]`.
-/
theorem patUnip_mem (X : PatIdx T → F) : patUnip F hT X ∈ U := by
  rw [hU]
  intro i j h
  rw [coe_patUnip, Matrix.add_apply, patMat_apply_of_not T h, add_zero]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[coe_patUnip, Matrix.add_apply]`. Distinguish the cases in `h : T i j`. Rewrite using `[patMat_apply_of_mem T h, one_apply_ne (ne_of_pat hT h), zero_add]`.

Both sides reduce to the same expression. Rewrite using `[patMat_apply_of_not T h, add_zero, (hU g).1 hg i j h]`.
-/
theorem patUnip_patCoord {g : GL (Fin n) F} (hg : g ∈ U) : patUnip F hT (patCoord T g) = g := by
  apply Units.ext
  ext i j
  rw [coe_patUnip, Matrix.add_apply]
  by_cases h : T i j
  · rw [patMat_apply_of_mem T h, one_apply_ne (ne_of_pat hT h), zero_add]
    rfl
  · rw [patMat_apply_of_not T h, add_zero, (hU g).1 hg i j h]

/- English proof (translation)
Rewrite using `[← patUnip_patCoord hT hU hg, ← patUnip_patCoord hT hU hg', h]`.
-/
theorem patCoord_injOn {g g' : GL (Fin n) F} (hg : g ∈ U) (hg' : g' ∈ U)
    (h : patCoord T g = patCoord T g') : g = g' := by
  rw [← patUnip_patCoord hT hU hg, ← patUnip_patCoord hT hU hg', h]

/- English proof (translation)
Rewrite using `[← patUnip_patCoord hT hU hg, coe_patUnip, det_one_add_patMat hT]`.
-/
theorem det_of_mem {g : GL (Fin n) F} (hg : g ∈ U) : (g : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [← patUnip_patCoord hT hU hg, coe_patUnip, det_one_add_patMat hT]

/- English proof (translation)
Establish `hdet` using `det_of_mem hT hU hg`. Establish `hinv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F).adjugate`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]`. Set `M' : Matrix (Fin n) (Fin n) 𝒪[F]` to `fun i j => ⟨(g : Matrix (Fin n) (Fin n) F) i j, hint i j⟩`. Establish `hM : (𝒪[F]).subtype.mapMatrix M' = (g : Matrix (Fin n) (Fin n) F)`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[hinv, ← hM, ← RingHom.map_adjugate]`. Conclude with `(M'.adjugate i j).2`.
-/
theorem inv_apply_mem_integer {g : GL (Fin n) F} (hg : g ∈ U)
    (hint : ∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) (i j : Fin n) :
    ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
  have hdet := det_of_mem hT hU hg
  have hinv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  let M' : Matrix (Fin n) (Fin n) 𝒪[F] := fun i j => ⟨(g : Matrix (Fin n) (Fin n) F) i j, hint i j⟩
  have hM : (𝒪[F]).subtype.mapMatrix M' = (g : Matrix (Fin n) (Fin n) F) := by
    ext i j
    rfl
  rw [hinv, ← hM, ← RingHom.map_adjugate]
  exact (M'.adjugate i j).2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h p`. Conclude with `((mem_integralGL_iff F n).1 h).1 p.1.1 p.1.2`. Introduce `h`. Establish `hint : ∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]`.

Introduce `i j`. Distinguish the cases in `hij : T i j`. Conclude with `h ⟨(i, j), hij⟩`. Rewrite using `[(hU g).1 hg i j hij, one_apply] split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Conclude with `(mem_integralGL_iff F n).2 ⟨hint, inv_apply_mem_integer hT hU hg hint⟩`.
-/
theorem mem_integralGL_iff_patCoord {g : GL (Fin n) F} (hg : g ∈ U) :
    g ∈ integralGL F n ↔ ∀ p : PatIdx T, patCoord T g p ∈ 𝒪[F] := by
  constructor
  · intro h p
    exact ((mem_integralGL_iff F n).1 h).1 p.1.1 p.1.2
  · intro h
    have hint : ∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
      intro i j
      by_cases hij : T i j
      · exact h ⟨(i, j), hij⟩
      · rw [(hU g).1 hg i j hij, one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    exact (mem_integralGL_iff F n).2 ⟨hint, inv_apply_mem_integer hT hU hg hint⟩

omit hT hU in
/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : T i j`. Simplify using `[patMat_apply_of_mem T h]`. Simplify using `[patMat_apply_of_not T h]`.
-/
theorem patMat_add (X Y : PatIdx T → F) : patMat F T (X + Y) = patMat F T X + patMat F T Y := by
  ext i j
  by_cases h : T i j
  · simp [patMat_apply_of_mem T h]
  · simp [patMat_apply_of_not T h]

omit hT hU in
/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : T i j`. Simplify using `[patMat_apply_of_mem T h]`. Simplify using `[patMat_apply_of_not T h]`.
-/
theorem patMat_smul (c : F) (X : PatIdx T → F) : patMat F T (c • X) = c • patMat F T X := by
  ext i j
  by_cases h : T i j
  · simp [patMat_apply_of_mem T h]
  · simp [patMat_apply_of_not T h]

omit hT hU in
variable (T) in

def patLeft (k : GL (Fin n) F) : (PatIdx T → F) →ₗ[F] (PatIdx T → F) where
  toFun X := fun p => ((k : Matrix (Fin n) (Fin n) F) * patMat F T X) p.1.1 p.1.2
  map_add' X Y := by
    funext p
    show ((k : Matrix (Fin n) (Fin n) F) * patMat F T (X + Y)) p.1.1 p.1.2 =
      ((k : Matrix (Fin n) (Fin n) F) * patMat F T X) p.1.1 p.1.2 +
        ((k : Matrix (Fin n) (Fin n) F) * patMat F T Y) p.1.1 p.1.2
    rw [patMat_add (T := T), Matrix.mul_add, Matrix.add_apply]
  map_smul' c X := by
    funext p
    show ((k : Matrix (Fin n) (Fin n) F) * patMat F T (c • X)) p.1.1 p.1.2 =
      c • ((k : Matrix (Fin n) (Fin n) F) * patMat F T X) p.1.1 p.1.2
    rw [patMat_smul (T := T), Matrix.mul_smul, Matrix.smul_apply]

variable (hTt : ∀ i j k, T i j → T j k → T i k)
include hTt

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : T i j`. Rewrite using `[patMat_apply_of_mem T h]`. Both sides reduce to the same expression. Rewrite using `[patMat_apply_of_not T h, mul_apply]`.

Use `(Finset.sum_eq_zero fun l _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `hlj : T l j`. Establish `hil : ¬ T i l` using `fun hil => h (hTt i l j hil hlj)`. Rewrite using `[(hU k).1 hk i l hil, one_apply_ne, zero_mul]`. Introduce and unpack `rfl`.

Conclude with `h hlj`. Rewrite using `[patMat_apply_of_not T hlj, mul_zero]`.
-/
theorem patMat_patLeft {k : GL (Fin n) F} (hk : k ∈ U) (X : PatIdx T → F) :
    patMat F T (patLeft T k X) = (k : Matrix (Fin n) (Fin n) F) * patMat F T X := by
  ext i j
  by_cases h : T i j
  · rw [patMat_apply_of_mem T h]
    rfl
  · rw [patMat_apply_of_not T h, mul_apply]
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases hlj : T l j
    · have hil : ¬ T i l := fun hil => h (hTt i l j hil hlj)
      rw [(hU k).1 hk i l hil, one_apply_ne, zero_mul]
      rintro rfl
      exact h hlj
    · rw [patMat_apply_of_not T hlj, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Use `show ((k * k' : GL (Fin n) F) * patMat F T X : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = ((k : Matrix (Fin n) (Fin n) F) * patMat F T (patLeft T k' X)) p.1.1 p.1.2`. Rewrite using `[patMat_patLeft hT hU hTt hk', Units.val_mul, Matrix.mul_assoc]`.
-/
theorem patLeft_mul {k k' : GL (Fin n) F} (hk' : k' ∈ U) (X : PatIdx T → F) :
    patLeft T (k * k') X = patLeft T k (patLeft T k' X) := by
  funext p
  show ((k * k' : GL (Fin n) F) * patMat F T X : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 =
    ((k : Matrix (Fin n) (Fin n) F) * patMat F T (patLeft T k' X)) p.1.1 p.1.2
  rw [patMat_patLeft hT hU hTt hk', Units.val_mul, Matrix.mul_assoc]

omit hTt in
/- English proof (translation)
Use function extensionality and compare the values at `p`. Use `show ((1 : GL (Fin n) F) * patMat F T X : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = X p`. Rewrite using `[Units.val_one, Matrix.one_mul, patMat_apply_of_mem T p.2]`.
-/
theorem patLeft_one (X : PatIdx T → F) : patLeft T (1 : GL (Fin n) F) X = X := by
  funext p
  show ((1 : GL (Fin n) F) * patMat F T X : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = X p
  rw [Units.val_one, Matrix.one_mul, patMat_apply_of_mem T p.2]

variable (T) in

def patLeftEquiv {k : GL (Fin n) F} (hk : k ∈ U) : (PatIdx T → F) ≃ₗ[F] (PatIdx T → F) where
  toLinearMap := patLeft T k
  invFun := patLeft T k⁻¹
  left_inv X := by
    show patLeft T k⁻¹ (patLeft T k X) = X
    rw [← patLeft_mul hT hU hTt hk, inv_mul_cancel, patLeft_one hT hU]
  right_inv X := by
    show patLeft T k (patLeft T k⁻¹ X) = X
    rw [← patLeft_mul hT hU hTt (U.inv_mem hk), mul_inv_cancel, patLeft_one hT hU]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_patLeftEquiv {k : GL (Fin n) F} (hk : k ∈ U) (X : PatIdx T → F) :
    patLeftEquiv T hT hU hTt hk X = patLeft T k X := rfl

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `hu'` using `patUnip_patCoord hT hU hu`. Use `show ((k * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = (k : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 + ((k : Matrix (Fin n) (Fin n) F) * patMat F T (patCoord T u)) p.1.1 p.1.2`. Use `conv_lhs => rw [← hu', Units.val_mul, coe_patUnip, Matrix.mul_add, Matrix.mul_one]`. Rewrite using `[Matrix.add_apply]`.
-/
theorem patCoord_mul {k u : GL (Fin n) F} (hu : u ∈ U) :
    patCoord T (k * u) = patCoord T k + patLeft T k (patCoord T u) := by
  funext p
  have hu' := patUnip_patCoord hT hU hu
  show ((k * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 =
    (k : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 +
      ((k : Matrix (Fin n) (Fin n) F) * patMat F T (patCoord T u)) p.1.1 p.1.2
  conv_lhs => rw [← hu', Units.val_mul, coe_patUnip, Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.add_apply]

/- English proof (translation)
Establish `hbox : ∀ {k' : GL (Fin n) F}, k' ∈ integralGL F n → ∀ X ∈ Measures.box F (PatIdx T), patLeft T k' X ∈ Measures.box F (PatIdx T)`. Introduce `k' hk' X hX`. Rewrite `hX`, the goal using `[Measures.mem_box]`. Introduce `p`. Use `show ((k' : Matrix (Fin n) (Fin n) F) * patMat F T X) p.1.1 p.1.2 ∈ 𝒪[F]`.

Rewrite using `[mul_apply]`. Use `sum_mem fun l _ => mul_mem (((mem_integralGL_iff F n).1 hk').1 _ _) ?_` and prove the remaining obligations. Distinguish the cases in `hl : T l p.1.2`. Rewrite using `[patMat_apply_of_mem T hl]`. Conclude with `hX _`.

Rewrite using `[patMat_apply_of_not T hl]`. Conclude with `zero_mem _`. Conclude with `Measures.distribHaarChar_eq_one_of_mapsTo_box (fun X hX => hbox hk.2 X hX) (fun X hX => hbox ((integralGL F n).inv_mem hk.2) X hX)`.
-/
theorem distribHaarChar_patLeftEquiv {k : GL (Fin n) F} (hk : k ∈ U ⊓ integralGL F n) :
    distribHaarChar (PatIdx T → F) (patLeftEquiv T hT hU hTt hk.1) = 1 := by
  have hbox : ∀ {k' : GL (Fin n) F}, k' ∈ integralGL F n → ∀ X ∈ Measures.box F (PatIdx T),
      patLeft T k' X ∈ Measures.box F (PatIdx T) := by
    intro k' hk' X hX
    rw [Measures.mem_box] at hX ⊢
    intro p
    show ((k' : Matrix (Fin n) (Fin n) F) * patMat F T X) p.1.1 p.1.2 ∈ 𝒪[F]
    rw [mul_apply]
    refine sum_mem fun l _ => mul_mem (((mem_integralGL_iff F n).1 hk').1 _ _) ?_
    by_cases hl : T l p.1.2
    · rw [patMat_apply_of_mem T hl]
      exact hX _
    · rw [patMat_apply_of_not T hl]
      exact zero_mem _
  exact Measures.distribHaarChar_eq_one_of_mapsTo_box (fun X hX => hbox hk.2 X hX)
    (fun X hX => hbox ((integralGL F n).inv_mem hk.2) X hX)

omit hT hU hTt in
/- English proof (translation)
The claim follows from `continuous_pi fun p => continuous_entry F n p.1.1 p.1.2`.
-/
theorem continuous_patCoord : Continuous (patCoord (F := F) T) :=
  continuous_pi fun p => continuous_entry F n p.1.1 p.1.2

/- English proof (translation)
Use `set U₀ := U ⊓ integralGL F n`. Use `set S : Subgroup U₀ := L.subgroupOf U₀`. Establish `hSi : S.index = L.relIndex U₀` using `rfl`. Establish `: S.FiniteIndex` using `⟨by rw [hSi]; exact hfin⟩`. Set `_` to `Fintype.ofFinite (U₀ ⧸ S)`.

Use `set piece : U₀ ⧸ S → Set (PatIdx T → F) := fun q => patCoord T '' ((fun l => ((Quotient.out q : U₀) : GL (Fin n) F) * l) '' (L : Set (GL (Fin n) F)))`. Establish `hbox : Measures.box F (PatIdx T) = ⋃ q, piece q`. Use extensionality with `X`. Simplify using `only [mem_iUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce `hX`. Establish `hgU : patUnip F hT X ∈ U` using `patUnip_mem hT hU X`. Establish `hcoord : patCoord T (patUnip F hT X) = X` using `patCoord_patUnip hT X`. Establish `hg0 : patUnip F hT X ∈ U₀` using `Subgroup.mem_inf.2 ⟨hgU, (mem_integralGL_iff_patCoord hT hU hgU).2 (by rw [hcoord]; exact Measures.mem_box.1 hX)⟩`. Take `⟨q, hq⟩ : ∃ q : U₀ ⧸ S, q = QuotientGroup.mk ⟨_, hg0⟩` from `⟨_, rfl⟩`.

Establish `hq' : (Quotient.out q : U₀)⁻¹ * ⟨_, hg0⟩ ∈ S` using `QuotientGroup.eq.1 ((QuotientGroup.out_eq' q).trans hq)`. Use `⟨q, patUnip F hT X, ⟨_, Subgroup.mem_subgroupOf.1 hq', ?_⟩, hcoord⟩` and prove the remaining obligations. Use `show ((Quotient.out q : U₀) : GL (Fin n) F) * (((Quotient.out q : U₀)⁻¹ * ⟨_, hg0⟩ : U₀) : GL (Fin n) F) = patUnip F hT X`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]`. Introduce and unpack `⟨q, _, ⟨l, hl, rfl⟩, rfl⟩`.

Establish `hmem : ((Quotient.out q : U₀) : GL (Fin n) F) * l ∈ U₀` using `U₀.mul_mem (Quotient.out q).2 (hL hl)`. Conclude with `Measures.mem_box.2 ((mem_integralGL_iff_patCoord hT hU hmem.1).1 hmem.2)`. Establish `hpiece : ∀ q, μ (piece q) = μ (patCoord T '' (L : Set (GL (Fin n) F)))`. Introduce `q`. Use `set k : GL (Fin n) F := ((Quotient.out q : U₀) : GL (Fin n) F)`.

Establish `hk : k ∈ U₀` using `(Quotient.out q).2`. Establish `hk1 : k ∈ U` using `(Subgroup.mem_inf.1 hk).1`. Establish `heq : piece q = (fun X => patCoord T k + X) '' (patLeftEquiv T hT hU hTt hk1 '' (patCoord T '' (L : Set (GL (Fin n) F))))`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨l, hl, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨patCoord T l, ⟨l, hl, rfl⟩, rfl⟩, (patCoord_mul hT hU hTt ((hL hl).1)).symm⟩`. Introduce and unpack `⟨_, ⟨_, ⟨l, hl, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨k * l, ⟨l, hl, rfl⟩, patCoord_mul hT hU hTt ((hL hl).1)⟩`. Rewrite using `[heq, Set.image_add_left, measure_preimage_add]`.

Establish `hsm : (⇑(patLeftEquiv T hT hU hTt hk1) '' (patCoord T '' (L : Set (GL (Fin n) F)))) = patLeftEquiv T hT hU hTt hk1 • (patCoord T '' (L : Set (GL (Fin n) F)))` using `rfl`. Rewrite using `[hsm, ← distribHaarChar_mul μ (patLeftEquiv T hT hU hTt hk1), distribHaarChar_patLeftEquiv hT hU hTt hk, ENNReal.coe_one, one_mul]`. Establish `hmeas : ∀ q, MeasurableSet (piece q)` using `fun q => (((hLc.image (continuous_const_mul _)).image (continuous_patCoord (T := T)))).isClosed.measurableSet`. Establish `hdisj : Pairwise (Function.onFun Disjoint piece)`. Introduce `q q' hqq'`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `_ ⟨_, ⟨l, hl, rfl⟩, rfl⟩ ⟨_, ⟨l', hl', rfl⟩, he⟩`. Apply `hqq'` to reduce the goal to its premises. Establish `h1` using `patCoord_injOn hT hU (U₀.mul_mem (Quotient.out q').2 (hL hl')).1 (U₀.mul_mem (Quotient.out q).2 (hL hl)).1 he`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]`.

Apply `Subgroup.mem_subgroupOf.2` to reduce the goal to its premises. Establish `: (((Quotient.out q : U₀)⁻¹ * Quotient.out q' : U₀) : GL (Fin n) F) = l * l'⁻¹`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq, mul_assoc, h1, inv_mul_cancel_left]`. Rewrite using `[this]`. Conclude with `L.mul_mem hl (L.inv_mem hl')`.

Rewrite using `[hbox, measure_iUnion hdisj hmeas, tsum_fintype]`. Simplify using `only [hpiece, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[← hSi, Subgroup.index_eq_card, Nat.card_eq_fintype_card]`.
-/
theorem measure_box_eq_relIndex_mul [MeasurableSpace F] [BorelSpace F]
    (μ : Measure (PatIdx T → F)) [μ.IsAddHaarMeasure] [μ.Regular] {L : Subgroup (GL (Fin n) F)}
    (hL : L ≤ U ⊓ integralGL F n) (hLc : IsCompact (L : Set (GL (Fin n) F)))
    (hfin : L.relIndex (U ⊓ integralGL F n) ≠ 0) :
    μ (Measures.box F (PatIdx T)) = (L.relIndex (U ⊓ integralGL F n) : ℝ≥0∞) *
      μ (patCoord T '' (L : Set (GL (Fin n) F))) := by
  classical
  set U₀ := U ⊓ integralGL F n
  set S : Subgroup U₀ := L.subgroupOf U₀
  have hSi : S.index = L.relIndex U₀ := rfl
  have : S.FiniteIndex := ⟨by rw [hSi]; exact hfin⟩
  let _ := Fintype.ofFinite (U₀ ⧸ S)
  set piece : U₀ ⧸ S → Set (PatIdx T → F) := fun q =>
    patCoord T '' ((fun l => ((Quotient.out q : U₀) : GL (Fin n) F) * l) '' (L : Set (GL (Fin n) F)))
  have hbox : Measures.box F (PatIdx T) = ⋃ q, piece q := by
    ext X
    simp only [mem_iUnion]
    constructor
    · intro hX
      have hgU : patUnip F hT X ∈ U := patUnip_mem hT hU X
      have hcoord : patCoord T (patUnip F hT X) = X := patCoord_patUnip hT X
      have hg0 : patUnip F hT X ∈ U₀ := Subgroup.mem_inf.2 ⟨hgU,
        (mem_integralGL_iff_patCoord hT hU hgU).2 (by rw [hcoord]; exact Measures.mem_box.1 hX)⟩
      obtain ⟨q, hq⟩ : ∃ q : U₀ ⧸ S, q = QuotientGroup.mk ⟨_, hg0⟩ := ⟨_, rfl⟩
      have hq' : (Quotient.out q : U₀)⁻¹ * ⟨_, hg0⟩ ∈ S :=
        QuotientGroup.eq.1 ((QuotientGroup.out_eq' q).trans hq)
      refine ⟨q, patUnip F hT X, ⟨_, Subgroup.mem_subgroupOf.1 hq', ?_⟩, hcoord⟩
      show ((Quotient.out q : U₀) : GL (Fin n) F) *
        (((Quotient.out q : U₀)⁻¹ * ⟨_, hg0⟩ : U₀) : GL (Fin n) F) = patUnip F hT X
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    · rintro ⟨q, _, ⟨l, hl, rfl⟩, rfl⟩
      have hmem : ((Quotient.out q : U₀) : GL (Fin n) F) * l ∈ U₀ :=
        U₀.mul_mem (Quotient.out q).2 (hL hl)
      exact Measures.mem_box.2 ((mem_integralGL_iff_patCoord hT hU hmem.1).1 hmem.2)
  have hpiece : ∀ q, μ (piece q) = μ (patCoord T '' (L : Set (GL (Fin n) F))) := by
    intro q
    set k : GL (Fin n) F := ((Quotient.out q : U₀) : GL (Fin n) F)
    have hk : k ∈ U₀ := (Quotient.out q).2
    have hk1 : k ∈ U := (Subgroup.mem_inf.1 hk).1
    have heq : piece q = (fun X => patCoord T k + X) ''
        (patLeftEquiv T hT hU hTt hk1 '' (patCoord T '' (L : Set (GL (Fin n) F)))) := by
      ext X
      constructor
      · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
        exact ⟨_, ⟨patCoord T l, ⟨l, hl, rfl⟩, rfl⟩,
          (patCoord_mul hT hU hTt ((hL hl).1)).symm⟩
      · rintro ⟨_, ⟨_, ⟨l, hl, rfl⟩, rfl⟩, rfl⟩
        exact ⟨k * l, ⟨l, hl, rfl⟩, patCoord_mul hT hU hTt ((hL hl).1)⟩
    rw [heq, Set.image_add_left, measure_preimage_add]
    have hsm : (⇑(patLeftEquiv T hT hU hTt hk1) '' (patCoord T '' (L : Set (GL (Fin n) F)))) =
        patLeftEquiv T hT hU hTt hk1 • (patCoord T '' (L : Set (GL (Fin n) F))) := rfl
    rw [hsm, ← distribHaarChar_mul μ (patLeftEquiv T hT hU hTt hk1),
      distribHaarChar_patLeftEquiv hT hU hTt hk, ENNReal.coe_one, one_mul]
  have hmeas : ∀ q, MeasurableSet (piece q) := fun q =>
    (((hLc.image (continuous_const_mul _)).image (continuous_patCoord (T := T)))).isClosed.measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩ ⟨_, ⟨l', hl', rfl⟩, he⟩
    apply hqq'
    have h1 := patCoord_injOn hT hU (U₀.mul_mem (Quotient.out q').2 (hL hl')).1
      (U₀.mul_mem (Quotient.out q).2 (hL hl)).1 he
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    apply Subgroup.mem_subgroupOf.2
    have : (((Quotient.out q : U₀)⁻¹ * Quotient.out q' : U₀) : GL (Fin n) F) = l * l'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq, mul_assoc, h1,
        inv_mul_cancel_left]
    rw [this]
    exact L.mul_mem hl (L.inv_mem hl')
  rw [hbox, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hpiece, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← hSi, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Pattern

section Conj

/- English proof (translation)
Establish `hϖ : (GLnLocal.uniformizer F : F) ≠ 0` using `Cartan.uniformizer_ne_zero F`. Rewrite using `[Set.mem_smul_set]`. Break down `le_or_gt 0 d with hd | hd` into its components or cases. Establish `hdn : ((d.toNat : ℕ) : ℤ) = d` using `Int.toNat_of_nonneg hd`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h⟩`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, ← mul_assoc, ← zpow_natCast, hdn, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, one_mul]`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨mul_mem (pow_mem (GLnLocal.uniformizer F).2 _) hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, ← mul_assoc, ← zpow_natCast, hdn, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero, one_mul]`. Conclude with `hy`. Establish `hdn : d.toNat = 0` using `Int.toNat_of_nonpos hd.le`. Rewrite using `[hdn, pow_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, -⟩`. Conclude with `⟨x, h, one_smul _ _⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[one_smul]`. Use `⟨hy, ?_⟩` and prove the remaining obligations.

Establish `: (GLnLocal.uniformizer F : F) ^ (-d) = (GLnLocal.uniformizer F : F) ^ (-d).toNat`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg (by omega)]`. Rewrite using `[this]`. Conclude with `mul_mem (pow_mem (GLnLocal.uniformizer F).2 _) hy`.
-/
theorem mem_smul_integer_iff (d : ℤ) (x : F) :
    (x ∈ 𝒪[F] ∧ (GLnLocal.uniformizer F : F) ^ (-d) * x ∈ 𝒪[F]) ↔
      x ∈ ((GLnLocal.uniformizer F : F) ^ d.toNat) • (𝒪[F] : Set F) := by
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  rw [Set.mem_smul_set]
  rcases le_or_gt 0 d with hd | hd
  · have hdn : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd
    constructor
    · rintro ⟨-, h⟩
      refine ⟨_, h, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, ← zpow_natCast, hdn, ← zpow_add₀ hϖ, add_neg_cancel,
        zpow_zero, one_mul]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨mul_mem (pow_mem (GLnLocal.uniformizer F).2 _) hy, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, ← zpow_natCast, hdn, ← zpow_add₀ hϖ, neg_add_cancel,
        zpow_zero, one_mul]
      exact hy
  · have hdn : d.toNat = 0 := Int.toNat_of_nonpos hd.le
    rw [hdn, pow_zero]
    constructor
    · rintro ⟨h, -⟩
      exact ⟨x, h, one_smul _ _⟩
    · rintro ⟨y, hy, rfl⟩
      rw [one_smul]
      refine ⟨hy, ?_⟩
      have : (GLnLocal.uniformizer F : F) ^ (-d) = (GLnLocal.uniformizer F : F) ^ (-d).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      rw [this]
      exact mul_mem (pow_mem (GLnLocal.uniformizer F).2 _) hy

variable {γ T : _} {U : Subgroup (GL (Fin n) F)}

/- English proof (translation)
Establish `h` using `diagPow_conj_apply (-ν) g i j`. Rewrite `h` using `[diagPow_neg, inv_inv]`. Rewrite using `[h]`. Use `congr 2`. Simplify using `only [Pi.neg_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_diagPow_apply (ν : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    ((diagPow F n ν)⁻¹ * g * diagPow F n ν : GL (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ (-(ν i - ν j)) * g i j := by
  have h := diagPow_conj_apply (-ν) g i j
  rw [diagPow_neg, inv_inv] at h
  rw [h]
  congr 2
  simp only [Pi.neg_apply]
  ring

end Conj

section PatternConj

variable {γ : Fin n → ℕ} {T : Fin n → Fin n → Prop} [DecidableRel T]
  (hT : ∀ i j, T i j → γ i < γ j)
  {U : Subgroup (GL (Fin n) F)} (hU : IsPatternGroup (F := F) (T := T) U)
include hT hU

/- English proof (translation)
Rewrite `hg`, the goal using `[hU]`. Introduce `i j h`. Rewrite using `[conj_diagPow_apply, hg i j h]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[one_apply_ne hij, mul_zero]`.
-/
theorem conj_diagPow_mem (ν : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ U) :
    (diagPow F n ν)⁻¹ * g * diagPow F n ν ∈ U := by
  rw [hU] at hg ⊢
  intro i j h
  rw [conj_diagPow_apply, hg i j h]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [one_apply_ne hij, mul_zero]

/- English proof (translation)
The claim follows from `conj_diagPow_apply ν g p.1.1 p.1.2`.
-/
theorem patCoord_conj_diagPow (ν : Fin n → ℤ) (g : GL (Fin n) F) (p : PatIdx T) :
    patCoord T ((diagPow F n ν)⁻¹ * g * diagPow F n ν) p =
      (GLnLocal.uniformizer F : F) ^ (-(ν p.1.1 - ν p.1.2)) * patCoord T g p :=
  conj_diagPow_apply ν g p.1.1 p.1.2

/- English proof (translation)
Establish `hx` using `conj_diagPow_mem hT hU ν hg`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyg⟩`. Establish `hyx : y = (diagPow F n ν)⁻¹ * g * diagPow F n ν`. Rewrite using `[← hyg]`.

Express the relevant statement in the definitionally equal form `y = (diagPow F n ν)⁻¹ * (diagPow F n ν * y * (diagPow F n ν)⁻¹) * diagPow F n ν`. Use `group`. Introduce `p`. Rewrite using `[← patCoord_conj_diagPow hT hU, ← hyx]`. Conclude with `(mem_integralGL_iff_patCoord hT hU (Subgroup.mem_inf.1 hy).1).1 (Subgroup.mem_inf.1 hy).2 p`.

Introduce `h`. Use `⟨(diagPow F n ν)⁻¹ * g * diagPow F n ν, Subgroup.mem_inf.2 ⟨hx, (mem_integralGL_iff_patCoord hT hU hx).2 fun p => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[patCoord_conj_diagPow hT hU]`. Conclude with `h p`. Express the relevant statement in the definitionally equal form `diagPow F n ν * ((diagPow F n ν)⁻¹ * g * diagPow F n ν) * (diagPow F n ν)⁻¹ = g group`.
-/
theorem mem_map_conj_diagPow_iff (ν : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ U) :
    g ∈ (U ⊓ integralGL F n).map (MulAut.conj (diagPow F n ν)).toMonoidHom ↔
      ∀ p : PatIdx T, (GLnLocal.uniformizer F : F) ^ (-(ν p.1.1 - ν p.1.2)) * patCoord T g p ∈ 𝒪[F] := by
  have hx := conj_diagPow_mem hT hU ν hg
  constructor
  · rintro ⟨y, hy, hyg⟩
    have hyx : y = (diagPow F n ν)⁻¹ * g * diagPow F n ν := by
      rw [← hyg]
      change y = (diagPow F n ν)⁻¹ * (diagPow F n ν * y * (diagPow F n ν)⁻¹) * diagPow F n ν
      group
    intro p
    rw [← patCoord_conj_diagPow hT hU, ← hyx]
    exact (mem_integralGL_iff_patCoord hT hU (Subgroup.mem_inf.1 hy).1).1
      (Subgroup.mem_inf.1 hy).2 p
  · intro h
    refine ⟨(diagPow F n ν)⁻¹ * g * diagPow F n ν, Subgroup.mem_inf.2 ⟨hx,
      (mem_integralGL_iff_patCoord hT hU hx).2 fun p => ?_⟩, ?_⟩
    · rw [patCoord_conj_diagPow hT hU]
      exact h p
    · change diagPow F n ν * ((diagPow F n ν)⁻¹ * g * diagPow F n ν) * (diagPow F n ν)⁻¹ = g
      group

/- English proof (translation)
Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Take `⟨hg0, hgm⟩` from `Subgroup.mem_inf.1 hg`. Establish `hgU` using `(Subgroup.mem_inf.1 hg0).1`.

Introduce `p _`. Conclude with `(mem_smul_integer_iff _ _).1 ⟨(mem_integralGL_iff_patCoord hT hU hgU).1 (Subgroup.mem_inf.1 hg0).2 p, (mem_map_conj_diagPow_iff hT hU ν hgU).1 hgm p⟩`. Introduce `hX`. Establish `hgU` using `patUnip_mem hT hU X`. Establish `hc` using `patCoord_patUnip (F := F) hT X`.

Establish `hp : ∀ p : PatIdx T, X p ∈ 𝒪[F] ∧ (GLnLocal.uniformizer F : F) ^ (-(ν p.1.1 - ν p.1.2)) * X p ∈ 𝒪[F]` using `fun p => (mem_smul_integer_iff _ _).2 (hX p (Set.mem_univ _))`. Use `⟨patUnip F hT X, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgU, (mem_integralGL_iff_patCoord hT hU hgU).2 fun p => by rw [hc]; exact (hp p).1⟩, (mem_map_conj_diagPow_iff hT hU ν hgU).2 fun p => by rw [hc]; exact (hp p).2⟩, hc⟩` and prove the remaining obligations.
-/
theorem patCoord_image_inf_map_conj (ν : Fin n → ℤ) :
    patCoord T '' (((U ⊓ integralGL F n) ⊓
        (U ⊓ integralGL F n).map (MulAut.conj (diagPow F n ν)).toMonoidHom :
          Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) =
      Set.univ.pi fun p : PatIdx T =>
        ((GLnLocal.uniformizer F : F) ^ (ν p.1.1 - ν p.1.2).toNat) • (𝒪[F] : Set F) := by
  ext X
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hg0, hgm⟩ := Subgroup.mem_inf.1 hg
    have hgU := (Subgroup.mem_inf.1 hg0).1
    intro p _
    exact (mem_smul_integer_iff _ _).1 ⟨(mem_integralGL_iff_patCoord hT hU hgU).1
      (Subgroup.mem_inf.1 hg0).2 p, (mem_map_conj_diagPow_iff hT hU ν hgU).1 hgm p⟩
  · intro hX
    have hgU := patUnip_mem hT hU X
    have hc := patCoord_patUnip (F := F) hT X
    have hp : ∀ p : PatIdx T, X p ∈ 𝒪[F] ∧
        (GLnLocal.uniformizer F : F) ^ (-(ν p.1.1 - ν p.1.2)) * X p ∈ 𝒪[F] :=
      fun p => (mem_smul_integer_iff _ _).2 (hX p (Set.mem_univ _))
    refine ⟨patUnip F hT X, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgU,
      (mem_integralGL_iff_patCoord hT hU hgU).2 fun p => by rw [hc]; exact (hp p).1⟩,
      (mem_map_conj_diagPow_iff hT hU ν hgU).2 fun p => by rw [hc]; exact (hp p).2⟩, hc⟩

end PatternConj

/- English proof (translation)
Use `borelize F`. Rewrite using `[show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, Measures.modulus_units, GroundTheory.LocalField.distribHaarChar_eq_modulus]`.
-/
theorem localField_modulus_eq {x : F} (hx : x ≠ 0) :
    GroundTheory.LocalField.modulus x = Measures.modulus x := by
  borelize F
  rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, Measures.modulus_units,
    GroundTheory.LocalField.distribHaarChar_eq_modulus]

section Volumes

variable {γ : Fin n → ℕ} {T : Fin n → Fin n → Prop} [DecidableRel T]
  (hT : ∀ i j, T i j → γ i < γ j) (hTt : ∀ i j k, T i j → T j k → T i k)
  {U : Subgroup (GL (Fin n) F)} (hU : IsPatternGroup (F := F) (T := T) U)
  (hUc : IsClosed (U : Set (GL (Fin n) F)))
include hT hTt hU hUc

/- English proof (translation)
Rewrite using `[Subgroup.coe_inf]`. Conclude with `(isCompact_integralGL F n).inter_left hUc`.
-/
theorem isCompact_inf_integralGL : IsCompact ((U ⊓ integralGL F n : Subgroup (GL (Fin n) F)) :
    Set (GL (Fin n) F)) := by
  rw [Subgroup.coe_inf]
  exact (isCompact_integralGL F n).inter_left hUc

/- English proof (translation)
Rewrite using `[Subgroup.relIndex, Subgroup.relIndex]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]`. Conclude with `⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩`.
-/
theorem relIndex_inf_left_eq (M K : Subgroup (GL (Fin n) F)) :
    (K ⊓ M).relIndex K = M.relIndex K := by
  rw [Subgroup.relIndex, Subgroup.relIndex]
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

/- English proof (translation)
Use `set U₀ := U ⊓ integralGL F n`. Use `set M := U₀.map (MulAut.conj (diagPow F n ν)).toMonoidHom`. Use `set H := (integralGL F n).map (MulAut.conj (diagPow F n ν)).toMonoidHom`. Establish `hHo : IsOpen (H : Set (GL (Fin n) F))`. Rewrite using `[Subgroup.coe_map]`.

Conclude with `(conjHomeomorph (diagPow F n ν)).isOpenMap _ (isOpen_integralGL F n)`. Establish `h1` using `relIndex_ne_zero_of_isCompact_of_isOpen (isCompact_inf_integralGL hT hTt hU hUc) hHo`. Establish `hle : H ⊓ U ≤ M`. Introduce and unpack `g ⟨⟨k, hk, hkg⟩, hgU⟩`. Use `⟨(diagPow F n ν)⁻¹ * g * diagPow F n ν, Subgroup.mem_inf.2 ⟨conj_diagPow_mem hT hU ν hgU, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `: (diagPow F n ν)⁻¹ * g * diagPow F n ν = k`. Rewrite using `[← hkg]`. Express the relevant statement in the definitionally equal form `(diagPow F n ν)⁻¹ * (diagPow F n ν * k * (diagPow F n ν)⁻¹) * diagPow F n ν = k`. Use `group`. Rewrite using `[this]`.

Conclude with `hk`. Express the relevant statement in the definitionally equal form `diagPow F n ν * ((diagPow F n ν)⁻¹ * g * diagPow F n ν) * (diagPow F n ν)⁻¹ = g group`. Establish `h2 : (H ⊓ U).relIndex U₀ = H.relIndex U₀`. Rewrite using `[Subgroup.relIndex, Subgroup.relIndex]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.1 x.2).1⟩⟩`. Introduce `h0`. Apply `h1` to reduce the goal to its premises.

Rewrite using `[← h2]`. Conclude with `Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left U₀ hle)`.
-/
theorem relIndex_map_conj_diagPow_ne_zero (ν : Fin n → ℤ) :
    ((U ⊓ integralGL F n).map (MulAut.conj (diagPow F n ν)).toMonoidHom).relIndex
      (U ⊓ integralGL F n) ≠ 0 := by
  set U₀ := U ⊓ integralGL F n
  set M := U₀.map (MulAut.conj (diagPow F n ν)).toMonoidHom
  set H := (integralGL F n).map (MulAut.conj (diagPow F n ν)).toMonoidHom
  have hHo : IsOpen (H : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact (conjHomeomorph (diagPow F n ν)).isOpenMap _ (isOpen_integralGL F n)
  have h1 := relIndex_ne_zero_of_isCompact_of_isOpen (isCompact_inf_integralGL hT hTt hU hUc) hHo
  have hle : H ⊓ U ≤ M := by
    rintro g ⟨⟨k, hk, hkg⟩, hgU⟩
    refine ⟨(diagPow F n ν)⁻¹ * g * diagPow F n ν, Subgroup.mem_inf.2 ⟨conj_diagPow_mem hT hU ν hgU, ?_⟩, ?_⟩
    · have : (diagPow F n ν)⁻¹ * g * diagPow F n ν = k := by
        rw [← hkg]
        change (diagPow F n ν)⁻¹ * (diagPow F n ν * k * (diagPow F n ν)⁻¹) * diagPow F n ν = k
        group
      rw [this]
      exact hk
    · change diagPow F n ν * ((diagPow F n ν)⁻¹ * g * diagPow F n ν) * (diagPow F n ν)⁻¹ = g
      group
  have h2 : (H ⊓ U).relIndex U₀ = H.relIndex U₀ := by
    rw [Subgroup.relIndex, Subgroup.relIndex]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.1 x.2).1⟩⟩
  intro h0
  apply h1
  rw [← h2]
  exact Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left U₀ hle)

/- English proof (translation)
Use `borelize F`. Use `set U₀ := U ⊓ integralGL F n`. Use `set M := U₀.map (MulAut.conj (diagPow F n ν)).toMonoidHom`. Set `μ : Measure (PatIdx T → F)` to `Measure.pi fun _ => GroundTheory.LocalField.haarIntegers F`. Use `Measures.metrizableSpace F` as an intermediate fact.

Use `Measures.sigmaCompactSpace F` as an intermediate fact. Establish `: μ.Regular` using `inferInstance`. Establish `hMc : IsCompact (M : Set (GL (Fin n) F))`. Rewrite using `[Subgroup.coe_map]`. Conclude with `(isCompact_inf_integralGL hT hTt hU hUc).image (conjHomeomorph _).continuous`.

Establish `hVc : IsCompact ((U₀ ⊓ M : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F))`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hMc.inter_left (isCompact_inf_integralGL hT hTt hU hUc).isClosed`. Establish `hfin : (U₀ ⊓ M).relIndex U₀ ≠ 0`. Rewrite using `[relIndex_inf_left_eq hT hTt hU hUc]`.

Conclude with `relIndex_map_conj_diagPow_ne_zero hT hTt hU hUc ν`. Establish `key` using `measure_box_eq_relIndex_mul hT hU hTt μ (L := U₀ ⊓ M) inf_le_left hVc hfin`. Rewrite `key` using `[patCoord_image_inf_map_conj hT hU ν]`. Establish `hbox : μ (Measures.box F (PatIdx T)) = 1`. Rewrite using `[Measures.box, Measure.pi_pi]`.

Simplify using `[GroundTheory.LocalField.haarIntegers_integers]`. Establish `hchart : μ (Set.univ.pi fun p : PatIdx T => ((GLnLocal.uniformizer F : F) ^ (ν p.1.1 - ν p.1.2).toNat) • (𝒪[F] : Set F)) = ∏ p : PatIdx T, ((Measures.modulus (GLnLocal.uniformizer F : F) ^ (ν p.1.1 - ν p.1.2).toNat : ℝ≥0) : ℝ≥0∞)`. Rewrite using `[Measure.pi_pi]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `hne : (GLnLocal.uniformizer F : F) ^ (ν p.1.1 - ν p.1.2).toNat ≠ 0` using `pow_ne_zero _ (Cartan.uniformizer_ne_zero F)`.

Rewrite using `[GroundTheory.LocalField.addHaar_smul _ hne, GroundTheory.LocalField.haarIntegers_integers, mul_one, localField_modulus_eq hne, map_pow]`. Rewrite `key` using `[hbox, hchart, relIndex_inf_left_eq hT hTt hU hUc]`. Establish `key'` using `congrArg ENNReal.toReal key`. Rewrite `key'` using `[ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_one, ENNReal.toReal_natCast]`. Simplify using `only [ENNReal.coe_toReal, NNReal.coe_pow] at key'`.

Establish `hpos : (∏ p : PatIdx T, (Measures.modulus (GLnLocal.uniformizer F : F) : ℝ) ^ (ν p.1.1 - ν p.1.2).toNat) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ ?_` and prove the remaining obligations. Conclude with `Measures.modulus_ne_zero (Cartan.uniformizer_ne_zero F)` after adjusting the coercions. Rewrite using `[Finset.prod_congr rfl fun p _ => inv_pow _ _, Finset.prod_inv_distrib]`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem relIndex_inf_map_conj_diagPow (ν : Fin n → ℤ) :
    (((U ⊓ integralGL F n).map (MulAut.conj (diagPow F n ν)).toMonoidHom).relIndex
      (U ⊓ integralGL F n) : ℝ) =
      ∏ p : PatIdx T, ((Measures.modulus (GLnLocal.uniformizer F : F) : ℝ)⁻¹) ^
        (ν p.1.1 - ν p.1.2).toNat := by
  classical
  borelize F
  set U₀ := U ⊓ integralGL F n
  set M := U₀.map (MulAut.conj (diagPow F n ν)).toMonoidHom
  let μ : Measure (PatIdx T → F) := Measure.pi fun _ => GroundTheory.LocalField.haarIntegers F
  have := Measures.metrizableSpace F
  have := Measures.sigmaCompactSpace F
  have : μ.Regular := inferInstance
  have hMc : IsCompact (M : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact (isCompact_inf_integralGL hT hTt hU hUc).image (conjHomeomorph _).continuous
  have hVc : IsCompact ((U₀ ⊓ M : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_inf]
    exact hMc.inter_left (isCompact_inf_integralGL hT hTt hU hUc).isClosed
  have hfin : (U₀ ⊓ M).relIndex U₀ ≠ 0 := by
    rw [relIndex_inf_left_eq hT hTt hU hUc]
    exact relIndex_map_conj_diagPow_ne_zero hT hTt hU hUc ν
  have key := measure_box_eq_relIndex_mul hT hU hTt μ (L := U₀ ⊓ M) inf_le_left hVc hfin
  rw [patCoord_image_inf_map_conj hT hU ν] at key
  have hbox : μ (Measures.box F (PatIdx T)) = 1 := by
    rw [Measures.box, Measure.pi_pi]
    simp [GroundTheory.LocalField.haarIntegers_integers]
  have hchart : μ (Set.univ.pi fun p : PatIdx T =>
      ((GLnLocal.uniformizer F : F) ^ (ν p.1.1 - ν p.1.2).toNat) • (𝒪[F] : Set F)) =
      ∏ p : PatIdx T, ((Measures.modulus (GLnLocal.uniformizer F : F) ^
        (ν p.1.1 - ν p.1.2).toNat : ℝ≥0) : ℝ≥0∞) := by
    rw [Measure.pi_pi]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hne : (GLnLocal.uniformizer F : F) ^ (ν p.1.1 - ν p.1.2).toNat ≠ 0 :=
      pow_ne_zero _ (Cartan.uniformizer_ne_zero F)
    rw [GroundTheory.LocalField.addHaar_smul _ hne, GroundTheory.LocalField.haarIntegers_integers, mul_one,
      localField_modulus_eq hne, map_pow]
  rw [hbox, hchart, relIndex_inf_left_eq hT hTt hU hUc] at key
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_one, ENNReal.toReal_natCast] at key'
  simp only [ENNReal.coe_toReal, NNReal.coe_pow] at key'
  have hpos : (∏ p : PatIdx T, (Measures.modulus (GLnLocal.uniformizer F : F) : ℝ) ^
      (ν p.1.1 - ν p.1.2).toNat) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ ?_
    exact_mod_cast Measures.modulus_ne_zero (Cartan.uniformizer_ne_zero F)
  rw [Finset.prod_congr rfl fun p _ => inv_pow _ _, Finset.prod_inv_distrib]
  field_simp
  linarith

omit hT hTt hU hUc in
/- English proof (translation)
Break down `le_or_gt 0 a with ha | ha` into its components or cases. Rewrite using `[Int.toNat_of_nonpos (by omega : -a ≤ 0), pow_zero, div_one, ← zpow_natCast, Int.toNat_of_nonneg ha]`. Rewrite using `[Int.toNat_of_nonpos ha.le, pow_zero, one_div, ← zpow_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ -a), _root_.zpow_neg, inv_inv]`.
-/
theorem pow_toNat_div_pow_toNat (x : ℝ) (a : ℤ) :
    x ^ a.toNat / x ^ (-a).toNat = x ^ a := by
  rcases le_or_gt 0 a with ha | ha
  · rw [Int.toNat_of_nonpos (by omega : -a ≤ 0), pow_zero, div_one, ← zpow_natCast,
      Int.toNat_of_nonneg ha]
  · rw [Int.toNat_of_nonpos ha.le, pow_zero, one_div, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega : 0 ≤ -a), _root_.zpow_neg, inv_inv]

/- English proof (translation)
Use `set U₀ := U ⊓ integralGL F n`. Establish `hinj : Function.Injective (MulAut.conj (diagPow F n ν)).toMonoidHom` using `(MulAut.conj (diagPow F n ν)).injective`. Establish `hback : (U₀.map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom).map (MulAut.conj (diagPow F n ν)).toMonoidHom = U₀`. Rewrite using `[Subgroup.map_map]`. Establish `: (MulAut.conj (diagPow F n ν)).toMonoidHom.comp (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom = MonoidHom.id (GL (Fin n) F)`.

Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Use `show diagPow F n ν * ((diagPow F n ν)⁻¹ * x * (diagPow F n ν)⁻¹⁻¹) * (diagPow F n ν)⁻¹ = x`. Use `group`. Rewrite using `[this, Subgroup.map_id]`. Establish `h1 : U₀.relIndex (U₀.map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom) = (U₀.map (MulAut.conj (diagPow F n ν)).toMonoidHom).relIndex U₀`.

Rewrite using `[← Subgroup.relIndex_map_map_of_injective _ _ hinj, hback]`. Establish `h2 : U₀.map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom = U₀.map (MulAut.conj (diagPow F n (-ν))).toMonoidHom`. Rewrite using `[diagPow_neg]`. Unfold `relVol`. Rewrite using `[h1, h2, relIndex_inf_map_conj_diagPow hT hTt hU hUc ν, relIndex_inf_map_conj_diagPow hT hTt hU hUc (-ν), ← Finset.prod_div_distrib]`.

Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.neg_apply]`. Rewrite using `[show -ν p.1.1 - -ν p.1.2 = -(ν p.1.1 - ν p.1.2) by ring, pow_toNat_div_pow_toNat, _root_.inv_zpow', neg_sub]`.
-/
theorem relVol_map_conj_diagPow (ν : Fin n → ℤ) :
    relVol (U ⊓ integralGL F n)
        ((U ⊓ integralGL F n).map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom) =
      ∏ p : PatIdx T, (Measures.modulus (GLnLocal.uniformizer F : F) : ℝ) ^ (ν p.1.2 - ν p.1.1) := by
  set U₀ := U ⊓ integralGL F n
  have hinj : Function.Injective (MulAut.conj (diagPow F n ν)).toMonoidHom :=
    (MulAut.conj (diagPow F n ν)).injective
  have hback : (U₀.map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom).map
      (MulAut.conj (diagPow F n ν)).toMonoidHom = U₀ := by
    rw [Subgroup.map_map]
    have : (MulAut.conj (diagPow F n ν)).toMonoidHom.comp
        (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom = MonoidHom.id (GL (Fin n) F) := by
      refine MonoidHom.ext fun x => ?_
      show diagPow F n ν * ((diagPow F n ν)⁻¹ * x * (diagPow F n ν)⁻¹⁻¹) * (diagPow F n ν)⁻¹ = x
      group
    rw [this, Subgroup.map_id]
  have h1 : U₀.relIndex (U₀.map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom) =
      (U₀.map (MulAut.conj (diagPow F n ν)).toMonoidHom).relIndex U₀ := by
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hback]
  have h2 : U₀.map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom =
      U₀.map (MulAut.conj (diagPow F n (-ν))).toMonoidHom := by
    rw [diagPow_neg]
  unfold relVol
  rw [h1, h2, relIndex_inf_map_conj_diagPow hT hTt hU hUc ν,
    relIndex_inf_map_conj_diagPow hT hTt hU hUc (-ν), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [Pi.neg_apply]
  rw [show -ν p.1.1 - -ν p.1.2 = -(ν p.1.1 - ν p.1.2) by ring, pow_toNat_div_pow_toNat,
    _root_.inv_zpow', neg_sub]

end Volumes

section Cell

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

/- English proof (translation)
Introduce `g`. Rewrite using `[mem_unipotentRadical]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, h1⟩ i j hij`. Break down `lt_trichotomy (γ i) (γ j) with h | h | h` into its components or cases.

Conclude with `absurd h hij`. Conclude with `h1 i j h`. Rewrite using `[hP h, one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ h`.

Introduce `h`. Use `⟨fun i j hij => ?_, fun i j hij => h i j (by omega)⟩` and prove the remaining obligations. Use `show (g : Matrix (Fin n) (Fin n) F) i j = 0`. Rewrite using `[h i j (by omega), one_apply_ne]`. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ hij`.
-/
theorem isPatternGroup_unipotentRadical :
    IsPatternGroup (F := F) (T := fun i j => γ i < γ j) (unipotentRadical F n γ) := by
  intro g
  rw [mem_unipotentRadical]
  constructor
  · rintro ⟨hP, h1⟩ i j hij
    rcases lt_trichotomy (γ i) (γ j) with h | h | h
    · exact absurd h hij
    · exact h1 i j h
    · rw [hP h, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
  · intro h
    refine ⟨fun i j hij => ?_, fun i j hij => h i j (by omega)⟩
    show (g : Matrix (Fin n) (Fin n) F) i j = 0
    rw [h i j (by omega), one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij

/- English proof (translation)
Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hN, hP⟩ i j hij`. Distinguish the cases in `h : γ i < γ j`. Establish `hβ : β (w j) < β (w i)`.

Assume the negation of the conclusion as `hβ`. Conclude with `hij ⟨h, hβ⟩`. Rewrite using `[hP hβ, one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hβ`.

Conclude with `(isPatternGroup_unipotentRadical g).1 hN i j h`. Introduce `h`. Use `⟨(isPatternGroup_unipotentRadical g).2 fun i j hij => h i j fun hT => hij hT.1, fun i j hij => ?_⟩` and prove the remaining obligations. Use `show (g : Matrix (Fin n) (Fin n) F) i j = 0`. Rewrite using `[h i j fun hT => hT.2 hij, one_apply_ne]`.

Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.
-/
theorem isPatternGroup_cellUnipotent :
    IsPatternGroup (F := F) (T := fun i j => γ i < γ j ∧ ¬ β (w j) < β (w i))
      (cellUnipotent F β γ w) := by
  intro g
  constructor
  · rintro ⟨hN, hP⟩ i j hij
    by_cases h : γ i < γ j
    · have hβ : β (w j) < β (w i) := by
        by_contra hβ
        exact hij ⟨h, hβ⟩
      rw [hP hβ, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hβ
    · exact (isPatternGroup_unipotentRadical g).1 hN i j h
  · intro h
    refine ⟨(isPatternGroup_unipotentRadical g).2 fun i j hij => h i j fun hT => hij hT.1,
      fun i j hij => ?_⟩
    show (g : Matrix (Fin n) (Fin n) F) i j = 0
    rw [h i j fun hT => hT.2 hij, one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij

/- English proof (translation)
Rewrite using `[unipotentCompactG_eq]`. Establish `h1 : rankTorus F n γ 0 = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[rankTorus, coe_torusPow, Units.val_one]`. Simplify using the standard rewrite rules.

Rewrite using `[h1, map_one]`. Both sides reduce to the same expression.
-/
theorem unipotentCompactG_zero :
    unipotentCompactG (F := F) γ 0 = unipotentRadical F n γ ⊓ integralGL F n := by
  rw [unipotentCompactG_eq]
  have h1 : rankTorus F n γ 0 = 1 := by
    apply Units.ext
    rw [rankTorus, coe_torusPow, Units.val_one]
    simp
  rw [h1, map_one]
  rfl

/- English proof (translation)
Rewrite using `[unipotentCompactG_zero]`. Use extensionality with `g`. Simplify using `only [Subgroup.mem_inf]`. Conclude with `⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨cellUnipotent_le_unipotentRadical h.1, h.2⟩, h.1⟩⟩`.
-/
theorem unipotentCompactG_zero_inf_cellUnipotent :
    unipotentCompactG (F := F) γ 0 ⊓ cellUnipotent F β γ w = cellUnipotent F β γ w ⊓ integralGL F n := by
  rw [unipotentCompactG_zero]
  ext g
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨cellUnipotent_le_unipotentRadical h.1, h.2⟩, h.1⟩⟩

/- English proof (translation)
Use `⟨diagPow_mem_levi ν, fun i j hij => ?_⟩` and prove the remaining obligations. Use `show (diagPow F n ν : Matrix (Fin n) (Fin n) F) i j = 0`. Rewrite using `[coe_diagPow, diagonal_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.
-/
theorem diagPow_mem_cellLeviParabolic (ν : Fin n → ℤ) :
    diagPow F n ν ∈ cellLeviParabolic F β γ w := by
  refine ⟨diagPow_mem_levi ν, fun i j hij => ?_⟩
  show (diagPow F n ν : Matrix (Fin n) (Fin n) F) i j = 0
  rw [coe_diagPow, diagonal_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

variable (β γ w) in

/- English proof (translation)
Establish `hkM` using `cellLeviParabolic_le_levi hk`. Establish `hmap : (unipotentCompactG (F` using `F) γ 0).map (MulAut.conj k⁻¹).toMonoidHom = unipotentCompactG γ 0 := by`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `conj_mem_unipotentCompactG ((levi F n γ).inv_mem hkM) ((integralGL F n).inv_mem hk') hu`.

Introduce `u hu`. Use `⟨k * u * k⁻¹, conj_mem_unipotentCompactG hkM hk' hu, ?_⟩` and prove the remaining obligations. Use `show k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u`. Use `group`. Rewrite using `[cellChar, hmap, div_self (cellNorm_pos (isCellCompact_unipotentCompactG 0)).ne']`.
-/
theorem cellChar_eq_one_of_mem_integralGL {k : GL (Fin n) F}
    (hk : k ∈ cellLeviParabolic F β γ w) (hk' : k ∈ integralGL F n) :
    cellChar F β γ w k = 1 := by
  have hkM := cellLeviParabolic_le_levi hk
  have hmap : (unipotentCompactG (F := F) γ 0).map (MulAut.conj k⁻¹).toMonoidHom =
      unipotentCompactG γ 0 := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact conj_mem_unipotentCompactG ((levi F n γ).inv_mem hkM) ((integralGL F n).inv_mem hk') hu
    · intro u hu
      refine ⟨k * u * k⁻¹, conj_mem_unipotentCompactG hkM hk' hu, ?_⟩
      show k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u
      group
  rw [cellChar, hmap, div_self (cellNorm_pos (isCellCompact_unipotentCompactG 0)).ne']

/- English proof (translation)
The claim follows from `(Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => P p.1 p.2) (fun p => by simp) f).symm`.
-/
theorem prod_patIdx {P : Fin n → Fin n → Prop} [DecidableRel P] (f : Fin n × Fin n → ℝ) :
    ∏ p : PatIdx P, f p.1 = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => P p.1 p.2), f p :=
  (Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => P p.1 p.2) (fun p => by simp)
    f).symm

variable (β γ w) in

/- English proof (translation)
Use `set m : ℝ := (Measures.modulus (GLnLocal.uniformizer F : F) : ℝ)`. Establish `hm : m ≠ 0` using `NNReal.coe_ne_zero.2 (Measures.modulus_ne_zero (Cartan.uniformizer_ne_zero F))`. Establish `ht` using `diagPow_mem_cellLeviParabolic (F := F) (β := β) (γ := γ) (w := w) ν`. Establish `htinv` using `(cellLeviParabolic F β γ w).inv_mem ht`. Establish `hinj : Function.Injective (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom` using `(MulAut.conj _).injective`.

Establish `hN` using `relVol_map_conj_diagPow (F := F) (T := fun i j => γ i < γ j) (γ := γ) (fun i j h => h) (fun i j k h h' => h.trans h') isPatternGroup_unipotentRadical isClosed_unipotentRadical ν`. Establish `hA` using `relVol_map_conj_diagPow (F := F) (T := fun i j => γ i < γ j ∧ ¬ β (w j) < β (w i)) (γ := γ) (fun i j h => h.1) (fun i j k h h' => ⟨h.1.trans h'.1, fun hc => by`. Use `not_lt.1 h.2` as an intermediate fact. Use `not_lt.1 h'.2` as an intermediate fact. Use the proof step `omega⟩)`.

Use `isPatternGroup_cellUnipotent isClosed_cellUnipotent ν`. Rewrite `hN` using `[← unipotentCompactG_zero]`. Rewrite `hA` using `[← unipotentCompactG_zero_inf_cellUnipotent (β := β) (w := w)]`. Establish `hmapA : ((unipotentCompactG (F` using `F) γ 0).map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom) ⊓ cellUnipotent F β γ w = (unipotentCompactG (F := F) γ 0 ⊓ cellUnipotent F β γ w).map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom := by`. Rewrite using `[Subgroup.map_inf_eq _ _ _ hinj, map_conj_cellUnipotent htinv]`.

Establish `h0 : cellNorm F β γ w (unipotentCompactG γ 0) = 1`. Rewrite using `[cellNorm, relVol_self, relVol_self, div_one]`. Rewrite using `[cellChar, h0, cellNorm, hmapA, hN, hA]`. Rewrite using `[prod_patIdx (P := fun i j => γ i < γ j) (fun p => m ^ (ν p.2 - ν p.1)), prod_patIdx (P := fun i j => γ i < γ j ∧ ¬ β (w j) < β (w i)) (fun p => m ^ (ν p.2 - ν p.1))]`. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun p : Fin n × Fin n => γ p.1 < γ p.2) (fun p => ¬ β (w p.2) < β (w p.1)), Finset.filter_filter, Finset.filter_filter]`.

Simplify using `only [not_not]`. Establish `hpos : ∀ s : Finset (Fin n × Fin n), ∏ p ∈ s, m ^ (ν p.2 - ν p.1) ≠ 0` using `fun s => Finset.prod_ne_zero_iff.2 fun p _ => zpow_ne_zero _ hm`. Rewrite using `[mul_div_cancel_left₀ _ (hpos _), one_div, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← _root_.zpow_neg, neg_sub]`.
-/
theorem cellChar_diagPow_eq_prod_zpow (ν : Fin n → ℤ) :
    cellChar F β γ w (diagPow F n ν) =
      ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => γ p.1 < γ p.2 ∧ β (w p.2) < β (w p.1)),
        (Measures.modulus (GLnLocal.uniformizer F : F) : ℝ) ^ (ν p.1 - ν p.2) := by
  classical
  set m : ℝ := (Measures.modulus (GLnLocal.uniformizer F : F) : ℝ)
  have hm : m ≠ 0 := NNReal.coe_ne_zero.2 (Measures.modulus_ne_zero (Cartan.uniformizer_ne_zero F))
  have ht := diagPow_mem_cellLeviParabolic (F := F) (β := β) (γ := γ) (w := w) ν
  have htinv := (cellLeviParabolic F β γ w).inv_mem ht
  have hinj : Function.Injective (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom :=
    (MulAut.conj _).injective

  have hN := relVol_map_conj_diagPow (F := F) (T := fun i j => γ i < γ j) (γ := γ)
    (fun i j h => h) (fun i j k h h' => h.trans h') isPatternGroup_unipotentRadical
    isClosed_unipotentRadical ν
  have hA := relVol_map_conj_diagPow (F := F) (T := fun i j => γ i < γ j ∧ ¬ β (w j) < β (w i))
    (γ := γ) (fun i j h => h.1)
    (fun i j k h h' => ⟨h.1.trans h'.1, fun hc => by
      have := not_lt.1 h.2
      have := not_lt.1 h'.2
      omega⟩)
    isPatternGroup_cellUnipotent isClosed_cellUnipotent ν
  rw [← unipotentCompactG_zero] at hN
  rw [← unipotentCompactG_zero_inf_cellUnipotent (β := β) (w := w)] at hA
  have hmapA : ((unipotentCompactG (F := F) γ 0).map (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom) ⊓
      cellUnipotent F β γ w = (unipotentCompactG (F := F) γ 0 ⊓ cellUnipotent F β γ w).map
        (MulAut.conj (diagPow F n ν)⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, map_conj_cellUnipotent htinv]
  have h0 : cellNorm F β γ w (unipotentCompactG γ 0) = 1 := by
    rw [cellNorm, relVol_self, relVol_self, div_one]
  rw [cellChar, h0, cellNorm, hmapA, hN, hA]
  rw [prod_patIdx (P := fun i j => γ i < γ j) (fun p => m ^ (ν p.2 - ν p.1)),
    prod_patIdx (P := fun i j => γ i < γ j ∧ ¬ β (w j) < β (w i)) (fun p => m ^ (ν p.2 - ν p.1))]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ.filter fun p : Fin n × Fin n => γ p.1 < γ p.2) (fun p => ¬ β (w p.2) < β (w p.1)),
    Finset.filter_filter, Finset.filter_filter]
  simp only [not_not]
  have hpos : ∀ s : Finset (Fin n × Fin n), ∏ p ∈ s, m ^ (ν p.2 - ν p.1) ≠ 0 :=
    fun s => Finset.prod_ne_zero_iff.2 fun p _ => zpow_ne_zero _ hm
  rw [mul_div_cancel_left₀ _ (hpos _), one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← _root_.zpow_neg, neg_sub]

variable (β γ w) in

/- English proof (translation)
Rewrite using `[cellChar_diagPow_eq_prod_zpow]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[coe_diagPow, diagonal_apply_eq, diagonal_apply_eq, map_zpow₀, map_zpow₀, NNReal.coe_div, NNReal.coe_zpow, NNReal.coe_zpow, zpow_sub₀]`. Conclude with `Measures.modulus_ne_zero (Cartan.uniformizer_ne_zero F)` after adjusting the coercions.
-/
theorem cellChar_diagPow (ν : Fin n → ℤ) :
    cellChar F β γ w (diagPow F n ν) =
      ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => γ p.1 < γ p.2 ∧ β (w p.2) < β (w p.1)),
        ((Measures.modulus ((diagPow F n ν : Matrix (Fin n) (Fin n) F) p.1 p.1) /
          Measures.modulus ((diagPow F n ν : Matrix (Fin n) (Fin n) F) p.2 p.2) : ℝ≥0) : ℝ) := by
  rw [cellChar_diagPow_eq_prod_zpow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [coe_diagPow, diagonal_apply_eq, diagonal_apply_eq, map_zpow₀, map_zpow₀, NNReal.coe_div,
    NNReal.coe_zpow, NNReal.coe_zpow, zpow_sub₀]
  exact_mod_cast Measures.modulus_ne_zero (Cartan.uniformizer_ne_zero F)

end Cell

end Parabolic

end GroundTheory.Automorphic
