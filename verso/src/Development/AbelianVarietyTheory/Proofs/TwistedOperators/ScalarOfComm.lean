import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContractMultilinearApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.Scal

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

def tform (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] ℂ := GlobalTheory.MultilinearContraction.prodForm w

/- English proof (translation)
Conclude with `GlobalTheory.MultilinearContraction.prodForm_tprod w v`.
-/
theorem tform_tprod (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    tform w (PiTensorProduct.tprod ℂ v) = ∏ i, w i (v i) := by
  exact GlobalTheory.MultilinearContraction.prodForm_tprod w v

/- English proof (translation)
Set `b` to `fun i => Module.Basis.ofVectorSpace ℂ (K i)`. Set `B` to `Basis.piTensorProduct b`. Use `B.ext_elem fun p => ?_` and prove the remaining obligations. Establish `: B.coord p = tform fun i => (b i).coord (p i)`. Use extensionality with `v`.

Simplify using `[tform_tprod, B, Basis.piTensorProduct_repr_tprod_apply]`. Establish `h2` using `h fun i => (b i).coord (p i)`. Rewrite `h2` using `[← this]`. Simplify using `using h2`.
-/
theorem eq_of_tform {t t' : ⨂[ℂ] i, K i} (h : ∀ w, tform w t = tform w t') : t = t' := by
  let b := fun i => Module.Basis.ofVectorSpace ℂ (K i)
  let B := Basis.piTensorProduct b
  refine B.ext_elem fun p => ?_
  have : B.coord p = tform fun i => (b i).coord (p i) := by
    ext v
    simp [tform_tprod, B, Basis.piTensorProduct_repr_tprod_apply]
  have h2 := h fun i => (b i).coord (p i)
  rw [← this] at h2
  simpa using h2

def ctrM (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : MultilinearMap ℂ K (K i) :=
  GlobalTheory.MultilinearContraction.contractMultilinear w i

def ctr (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (ctrM i w)

/- English proof (translation)
Simplify using `[ctr, ctrM]`.
-/
theorem ctr_tprod (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    ctr i w (PiTensorProduct.tprod ℂ v) = (∏ j ∈ Finset.univ.erase i, w j (v j)) • v i := by
  simp [ctr, ctrM]

/- English proof (translation)
Establish `: ctr i w ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ ctr i w`. Use extensionality with `v`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, ctr_tprod, Function.update_self, map_smul]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]`.

Conclude with `LinearMap.congr_fun this t`.
-/
theorem ctr_mapFactor (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (f : Module.End ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    ctr i w (intersection_update_fsHerm_neg_one i f t) = f (ctr i w t) := by
  have : ctr i w ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, ctr_tprod,
      Function.update_self, map_smul]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  exact LinearMap.congr_fun this t

/- English proof (translation)
Establish `: tform w = w i ∘ₗ ctr i w`. Use extensionality with `v`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tform_tprod, ctr_tprod, map_smul, smul_eq_mul]`. Rewrite using `[Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Conclude with `LinearMap.congr_fun this t`.
-/
theorem tform_eq (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    tform w t = w i (ctr i w t) := by
  have : tform w = w i ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tform_tprod, ctr_tprod,
      map_smul, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact LinearMap.congr_fun this t

/- English proof (translation)
Use `eq_of_tform fun w => ?_` and prove the remaining obligations. Rewrite using `[tform_eq i, tform_eq i, ctr_mapFactor]`. Use `congr 1`. Set `T : Module.End ℂ (K i)` to `ctr i w ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ (s := K)).toLinearMap x i`. Establish `hT : ∀ z, T z = ctr i w (Φ (PiTensorProduct.tprod ℂ (Function.update x i z)))` using `fun z => rfl`.

Take `⟨c, hc⟩` from `ha.2 T (fun g => by`. Use extensionality with `z`. Use `LinearMap.congr_fun (h g) (PiTensorProduct.tprod ℂ (Function.update x i z))` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, position_tprod, Function.update_self, Function.update_idem] at this`. Simplify using `only [LinearMap.comp_apply, hT, this, ctr_mapFactor])`.

Establish `h1` using `hT (x i)`. Rewrite `h1` using `[Function.update_eq_self]`. Rewrite using `[position_tprod, ← hT, ← h1, hc]`. Simplify using the standard rewrite rules.
-/
theorem comm_mapFactor_of_absIrr {G : Type} (i : ι) (a : G → Module.End ℂ (K i)) (ha : AbsIrr a)
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a g) = intersection_update_fsHerm_neg_one i (a g) ∘ₗ Φ)
    (f : Module.End ℂ (K i)) (x : ∀ i, K i) :
    Φ (intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ x)) = intersection_update_fsHerm_neg_one i f (Φ (PiTensorProduct.tprod ℂ x)) := by
  refine eq_of_tform fun w => ?_
  rw [tform_eq i, tform_eq i, ctr_mapFactor]
  congr 1
  let T : Module.End ℂ (K i) :=
    ctr i w ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ (s := K)).toLinearMap x i
  have hT : ∀ z, T z = ctr i w (Φ (PiTensorProduct.tprod ℂ (Function.update x i z))) := fun z => rfl
  obtain ⟨c, hc⟩ := ha.2 T (fun g => by
    ext z
    have := LinearMap.congr_fun (h g) (PiTensorProduct.tprod ℂ (Function.update x i z))
    simp only [LinearMap.comp_apply, position_tprod, Function.update_self, Function.update_idem] at this
    simp only [LinearMap.comp_apply, hT, this, ctr_mapFactor])
  have h1 := hT (x i)
  rw [Function.update_eq_self] at h1
  rw [position_tprod, ← hT, ← h1, hc]
  simp

/- English proof (translation)
Establish `key : ∀ s : Finset ι, Φ ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) = PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) ∘ₗ Φ`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`.

Establish `: PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) = intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id)`. Use extensionality with `v`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, position_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[hi]`. Simplify using `[hj]`. Rewrite using `[this, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ih, LinearMap.comp_assoc]`.

Simplify using `using key Finset.univ`.
-/
theorem comm_map (Φ : Module.End ℂ (⨂[ℂ] i, K i))
    (h : ∀ i (f : Module.End ℂ (K i)), Φ ∘ₗ intersection_update_fsHerm_neg_one i f = intersection_update_fsHerm_neg_one i f ∘ₗ Φ) (f : ∀ i, Module.End ℂ (K i)) :
    Φ ∘ₗ PiTensorProduct.map f = PiTensorProduct.map f ∘ₗ Φ := by
  have key : ∀ s : Finset ι,
      Φ ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) =
        PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) ∘ₗ Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [this, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  simpa using key Finset.univ

/- English proof (translation)
Distinguish the cases in `hn : ∀ i, ∃ e : K i, e ≠ 0`. Use `choose e he using hn`. Establish `: ∀ i, ∃ w : Module.Dual ℂ (K i), w (e i) = 1` using `fun i => Module.Projective.exists_dual_eq_one ℂ (he i)`. Use `choose w hw using this`. Use `⟨tform w (Φ (PiTensorProduct.tprod ℂ e)), ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Establish `hc` using `comm_map Φ (fun i f => by`. Use extensionality with `y`. Conclude with `comm_mapFactor_of_absIrr i (a i) (ha i) Φ (h i) f y) (fun i => (w i).smulRight (x i))`. Establish `hm : PiTensorProduct.map (fun i => (w i).smulRight (x i)) = (tform w).smulRight (PiTensorProduct.tprod ℂ x)`.

Use extensionality with `v`. Simplify using `[tform_tprod, MultilinearMap.map_smul_univ]`. Use `LinearMap.congr_fun hc (PiTensorProduct.tprod ℂ e)` as an intermediate fact. Rewrite `this` using `[hm]`. Simplify `this` using `[tform_tprod, hw]`.

Use `push Not at hn`. Take `⟨i, hi⟩` from `hn`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `: PiTensorProduct.tprod ℂ x = 0` using `MultilinearMap.map_coord_zero _ i (hi _)`.

Simplify using `[this]`.
-/
theorem scalar_of_comm (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)) (ha : ∀ i, AbsIrr (a i))
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ i g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a i g) = intersection_update_fsHerm_neg_one i (a i g) ∘ₗ Φ) :
    ∃ c : ℂ, Φ = c • LinearMap.id := by
  by_cases hn : ∀ i, ∃ e : K i, e ≠ 0
  · choose e he using hn
    have : ∀ i, ∃ w : Module.Dual ℂ (K i), w (e i) = 1 := fun i =>
      Module.Projective.exists_dual_eq_one ℂ (he i)
    choose w hw using this
    refine ⟨tform w (Φ (PiTensorProduct.tprod ℂ e)), ?_⟩
    ext x
    have hc := comm_map Φ (fun i f => by
      ext y
      exact comm_mapFactor_of_absIrr i (a i) (ha i) Φ (h i) f y) (fun i => (w i).smulRight (x i))
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (x i)) =
        (tform w).smulRight (PiTensorProduct.tprod ℂ x) := by
      ext v
      simp [tform_tprod, MultilinearMap.map_smul_univ]
    have := LinearMap.congr_fun hc (PiTensorProduct.tprod ℂ e)
    rw [hm] at this
    simpa [tform_tprod, hw] using this
  · push Not at hn
    obtain ⟨i, hi⟩ := hn
    refine ⟨0, ?_⟩
    ext x
    have : PiTensorProduct.tprod ℂ x = 0 := MultilinearMap.map_coord_zero _ i (hi _)
    simp [this]

end GlobalTheory.Chain.IoLift.Scal

end
