import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.OpenCrit

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

def vOf (g : UG c (stdJ ν E)) : Matrix ν ν E := (mat c g).toBlocks₂₂⁻¹ * (mat c g).toBlocks₂₁

/- English proof (translation)
Establish `h : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E` using `(mem_UG_iff c _).mp g.2`. Establish `h2` using `congrArg Matrix.toBlocks₂₂ h`. Rewrite `h2` using `[← fromBlocks_toBlocks (mat c g)]`. Simplify using `[stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply] at h2`. Rewrite `h2` using `[neg_add_eq_zero]`.

Conclude with `h2.symm`.
-/
theorem lower_rel (g : UG c (stdJ ν E)) :
    (mat c g).toBlocks₂₁ * ((mat c g).toBlocks₂₂.map c)ᵀ = (mat c g).toBlocks₂₂ * ((mat c g).toBlocks₂₁.map c)ᵀ := by
  have h : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [← fromBlocks_toBlocks (mat c g)] at h2
  simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply] at h2
  rw [neg_add_eq_zero] at h2
  exact h2.symm

/- English proof (translation)
Use `set D := (mat c g).toBlocks₂₂ with hD`. Use `set C := (mat c g).toBlocks₂₁ with hC`. Establish `hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ` using `lower_rel c g`. Establish `hdetc : ((D.map c)ᵀ).det = c D.det`. Rewrite using `[det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]`.

Both sides reduce to the same expression. Establish `hDs : IsUnit ((D.map c)ᵀ).det` using `by rw [hdetc]; exact hd.map c`. Establish `hV : vOf c g = D⁻¹ * C` using `rfl`. Establish `hDV : D * vOf c g = C` using `by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]`. Establish `hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ`.

Rewrite using `[← transpose_mul, ← hDV]`. Conclude with `congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm`. Establish `key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ`. Rewrite using `[Matrix.mul_assoc, hstar, hDV, hrel]`. Establish `h3 : ((vOf c g).map c)ᵀ = vOf c g`.

Use `congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key` as an intermediate fact. Simplify using `only [Matrix.mul_assoc] at this`. Rewrite `this` using `[nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_nonsing_inv _ hDs, Matrix.mul_one, Matrix.mul_one]`. Conclude with `this`. Rewrite using `[Matrix.map_neg _ (map_neg c), transpose_neg, h3]`.
-/
theorem vOf_herm (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) :
    ((-vOf c g).map c)ᵀ = -vOf c g := by
  set D := (mat c g).toBlocks₂₂ with hD
  set C := (mat c g).toBlocks₂₁ with hC
  have hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ := lower_rel c g
  have hdetc : ((D.map c)ᵀ).det = c D.det := by
    rw [det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]; rfl
  have hDs : IsUnit ((D.map c)ᵀ).det := by rw [hdetc]; exact hd.map c
  have hV : vOf c g = D⁻¹ * C := rfl
  have hDV : D * vOf c g = C := by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]
  have hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ := by
    rw [← transpose_mul, ← hDV]
    exact congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm
  have key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ := by
    rw [Matrix.mul_assoc, hstar, hDV, hrel]
  have h3 : ((vOf c g).map c)ᵀ = vOf c g := by
    have := congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key
    simp only [Matrix.mul_assoc] at this
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_nonsing_inv _ hDs, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h3]

open scoped Classical in

def nOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) :=
  if h : IsUnit (mat c g).toBlocks₂₂.det then unip c (-vOf c g) (vOf_herm c g h) else 1

def kOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := (weyl c ν)⁻¹ * nOf c g * weyl c ν

def pOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := g * (kOf c g)⁻¹

/- English proof (translation)
Unfold `nOf`. Use `split_ifs with h`. Rewrite using `[mem_sieg]`. Express the relevant statement in the definitionally equal form `(fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0`. Simplify using the standard rewrite rules.

Conclude with `(sieg c ν).one_mem`.
-/
theorem nOf_mem (g : UG c (stdJ ν E)) : nOf c g ∈ sieg c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_sieg]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (sieg c ν).one_mem

/- English proof (translation)
Rewrite using `[mem_sieg]`. Establish `hk : mat c (pOf c g) = mat c g * (-stdJ ν E * (fromBlocks 1 (-(-vOf c g)) 0 1 * stdJ ν E))`. Simplify using `only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dif_pos hd]`. Both sides reduce to the same expression. Rewrite using `[hk]`.

Establish `hDV : (mat c g).toBlocks₂₂ * vOf c g = (mat c g).toBlocks₂₁` using `mul_nonsing_inv_cancel_left _ _ hd`. Use `set M := mat c g`. Rewrite using `[← fromBlocks_toBlocks M]`. Simplify using `[stdJ, fromBlocks_multiply, fromBlocks_neg]`. Rewrite using `[hDV, add_neg_cancel]`.
-/
theorem pOf_mem (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) : pOf c g ∈ sieg c ν := by
  rw [mem_sieg]
  have hk : mat c (pOf c g) = mat c g * (-stdJ ν E * (fromBlocks 1 (-(-vOf c g)) 0 1 * stdJ ν E)) := by
    simp only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dif_pos hd]
    rfl
  rw [hk]
  have hDV : (mat c g).toBlocks₂₂ * vOf c g = (mat c g).toBlocks₂₁ := mul_nonsing_inv_cancel_left _ _ hd
  set M := mat c g
  rw [← fromBlocks_toBlocks M]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]
  rw [hDV, add_neg_cancel]

section Top

variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mat : Continuous (mat c : UG c (stdJ ν E) → Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _`.
-/
theorem continuous_blk₂₂ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

/- English proof (translation)
The claim follows from `continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _`.
-/
theorem continuous_blk₂₁ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₁ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[mat, toBlocks₂₂, one_apply]`.
-/
theorem blk₂₂_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₂ = 1 := by
  ext i j; simp [mat, toBlocks₂₂, one_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[mat, toBlocks₂₁, one_apply]`.
-/
theorem blk₂₁_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]

/- English proof (translation)
Establish `h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1)`. Use `((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))` as an intermediate fact. Rewrite `this` using `[blk₂₂_one, det_one]`. Then use the resulting hypothesis. Use `filter_upwards [h.eventually_ne one_ne_zero] with g hg`. Conclude with `isUnit_iff_ne_zero.mpr hg`.
-/
theorem eventually_isUnit : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg

/- English proof (translation)
Establish `hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1`. Use `ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt` and prove the remaining obligations. Apply `continuousAt_matrix_inv` to reduce the goal to its premises. Rewrite using `[Ring.inverse_eq_inv', blk₂₂_one, det_one]`. Conclude with `continuousAt_inv₀ one_ne_zero`.

Establish `h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1))` using `(hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto`. Establish `h0 : vOf c (1 : UG c (stdJ ν E)) = 0` using `by rw [vOf, blk₂₁_one, Matrix.mul_zero]`. Rewrite `h2` using `[h0]`. Then use the resulting hypothesis.
-/
theorem tendsto_vOf : Tendsto (vOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : UG c (stdJ ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2

/- English proof (translation)
Rewrite using `[tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]`. Establish `hv` using `tendsto_vOf c (ν := ν)`. Establish `hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1)`. Establish `hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)` using `continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const`. Use `(hc.tendsto 0).comp hv` as an intermediate fact.

Rewrite `this` using `[neg_zero, fromBlocks_one]`. Then use the resulting hypothesis. Establish `hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1)`. Establish `hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)` using `continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const`. Use `(hc.tendsto 0).comp hv` as an intermediate fact. Rewrite `this` using `[neg_zero, neg_zero, fromBlocks_one]`. Then use the resulting hypothesis.

Establish `hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E), MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1] (Units.embedProduct _ ∘ fun g => ((nOf c g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E))` using `by filter_upwards [eventually_isUnit c] with g hg`. Simplify using `only [Function.comp_apply, nOf, dif_pos hg]`. Both sides reduce to the same expression. Use `Tendsto.congr' hE ?_` and prove the remaining obligations. Establish `h1 : Units.embedProduct _ ((1 : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = (1, MulOpposite.op 1)` using `rfl`.

Rewrite using `[h1]`. Conclude with `hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)`.
-/
theorem tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hv := tendsto_vOf c (ν := ν)
  have hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, fromBlocks_one] at this
  have hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, neg_zero, fromBlocks_one] at this
  have hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E),
      MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1]
      (Units.embedProduct _ ∘ fun g => ((nOf c g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E)) := by
    filter_upwards [eventually_isUnit c] with g hg
    simp only [Function.comp_apply, nOf, dif_pos hg]
    rfl
  refine Tendsto.congr' hE ?_
  have h1 : Units.embedProduct _ ((1 : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = (1, MulOpposite.op 1) := rfl
  rw [h1]
  exact hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)

end Top

end GlobalTheory.KSp.OpenCrit

namespace GlobalTheory.KSp

open OpenCrit in

/- English proof (translation)
Take `⟨-, hTR, hCI, hT2, -⟩` from `GlobalTheory.T.quadExt_topological_properties F E c δ hE`. Use `haveI := hTR`. Use `haveI := hCI`. Use `haveI := hT2`. Use `Subgroup.isOpen_of_mem_nhds U (g := 1) ?_` and prove the remaining obligations.

Establish `hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1)` using `tendsto_nOf c`. Establish `hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1)`. Use `((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))` as an intermediate fact. Rewrite `this` using `[mul_one, inv_mul_cancel]`. Then use the resulting hypothesis. Establish `hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1)`.

Use `(tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv` as an intermediate fact. Rewrite `this` using `[inv_one, mul_one]`. Then use the resulting hypothesis. Use `filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd`. Establish `hg : g = pOf c g * kOf c g` using `by rw [pOf, inv_mul_cancel_right]`. Rewrite using `[hg]`.

Conclude with `U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))`.
-/
theorem isOpen_of_sieg_of_opp (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (h1 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U)
    (h2 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) :
    IsOpen (U : Set (UG c (stdJ ν E))) := by
  obtain ⟨-, hTR, hCI, hT2, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hTR
  haveI := hCI
  haveI := hT2
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))

end GlobalTheory.KSp
