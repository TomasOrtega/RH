import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemHermitianStandardLatticeIffPairingIntegral
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatF

open Alg

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

/- English proof (translation)
Establish `h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I ≤ J`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `s hs c hc`. Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hs`. Rewrite using `[Algebra.smul_def, mul_assoc, mul_comm x c]`.

Conclude with `LatA.fi_smul_mem (h c hc) z`. Establish `h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ J * I⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_inv_cancel₀ hI, mul_one]`. Use `_ ≤ J * I⁻¹ := FractionalIdeal.mul_le.mpr fun i hi j hj => FractionalIdeal.mul_mem_mul (h1 hi) hj`.

Conclude with `h2 (FractionalIdeal.mem_spanSingleton_self _ x)`.
-/
theorem mem_mul_inv_of {I J : FI} (hI : I ≠ 0) {x : D.host.E} (h : ∀ c ∈ I, c * x ∈ J) : x ∈ J * I⁻¹ := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I ≤ J := by
    rw [FractionalIdeal.mul_le]
    intro s hs c hc
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hs
    rw [Algebra.smul_def, mul_assoc, mul_comm x c]
    exact LatA.fi_smul_mem (h c hc) z
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ J * I⁻¹ := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ J * I⁻¹ := FractionalIdeal.mul_le.mpr fun i hi j hj => FractionalIdeal.mul_mem_mul (h1 hi) hj
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ x)

/- English proof (translation)
Establish `h` using `FractionalIdeal.mul_mem_mul hx hy`. Establish `e : I * K⁻¹ * (K * J) = I * J`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem mul_mem_cancel {I J K : FI} (hK : K ≠ 0) {x y : D.host.E} (hx : x ∈ I * K⁻¹) (hy : y ∈ K * J) :
    x * y ∈ I * J := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  have e : I * K⁻¹ * (K * J) = I * J := by
    calc I * K⁻¹ * (K * J) = I * J * (K⁻¹ * K) := by ring
      _ = I * J := by rw [inv_mul_cancel₀ hK, mul_one]
  rwa [e] at h

variable (X : HidaSetting D)

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.NcReal.JX.CovB.aaD_ne_zero Y a`.
-/
theorem aa_ne (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.aaD_ne_zero Y a

/- English proof (translation)
Rewrite using `[X.Lam_split]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, c, hc, rfl⟩))`.
-/
theorem e_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ aaD D a) : c • X.eX a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, c, hc, rfl⟩))

/- English proof (translation)
Rewrite using `[X.Lam_split]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩)`.
-/
theorem f_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ (aaD D a)⁻¹) : c • X.fY a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩)

variable {X}

/- English proof (translation)
Rewrite using `[← hL]`. Conclude with `⟨y, hy, rfl⟩`.
-/
theorem lattice_map_preserves_base {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    {y : (VS D).V} (hy : y ∈ (VS D).L0) : m y ∈ (VS D).L0 := by
  rw [← hL]; exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite `hz` using `[← hL]`. Take `⟨w, hw, rfl⟩` from `hz`.

Use `show m.symm (m w) ∈ (VS D).L0`. Simplify using `using hw`. Introduce `hy`. Conclude with `⟨m y, lattice_map_preserves_base hL hy, by simp⟩`.
-/
theorem gmap_symm {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0) :
    Formalism.HermitianLatticesTheory.gmap m.symm (VS D).L0 = (VS D).L0 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hL] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show m.symm (m w) ∈ (VS D).L0
    simpa using hw
  · intro hy
    exact ⟨m y, lattice_map_preserves_base hL hy, by simp⟩

/- English proof (translation)
Use `mem_mul_inv_of (aa_ne X d) fun c hc => ?_` and prove the remaining obligations. Establish `h` using `Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (e_mem X hc))`. Rewrite `h` using `[map_smul, map_smul, smul_eq_mul]`. Conclude with `h`.
-/
theorem ex_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b d : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.eX d)) ∈ aaD D b * (aaD D d)⁻¹ := by
  refine mem_mul_inv_of (aa_ne X d) fun c hc => ?_
  have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (e_mem X hc))
  rw [map_smul, map_smul, smul_eq_mul] at h
  exact h

/- English proof (translation)
Establish `hne : (aaD D a)⁻¹ ≠ 0` using `inv_ne_zero (aa_ne X a)`. Use `mem_mul_inv_of hne (J := aaD D b) (x := (VS D).hT (X.fY b) (m (X.fY a))) fun c hc => by` as an intermediate fact. Establish `h` using `Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (f_mem X hc))`. Rewrite `h` using `[map_smul, map_smul, smul_eq_mul]`. Conclude with `h`.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem fa_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b a : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.fY a)) ∈ aaD D b * aaD D a := by
  have hne : (aaD D a)⁻¹ ≠ 0 := inv_ne_zero (aa_ne X a)
  have := mem_mul_inv_of hne (J := aaD D b) (x := (VS D).hT (X.fY b) (m (X.fY a))) fun c hc => by
    have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (f_mem X hc))
    rw [map_smul, map_smul, smul_eq_mul] at h
    exact h
  rwa [inv_inv] at this

variable {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

/- English proof (translation)
Use `Matrix.ext fun b a => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Xq]`. Rewrite using `[Finset.sum_congr rfl fun d _ => mul_comm _ _, ← hT_sumR]`. Establish `e : ∑ d, (VS D).hT (X.fY d) (n (X.eX a)) • n.symm (X.eX d) = n.symm (n (X.eX a))` using `by conv_rhs => rw [Xq_expand hn a]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, Xq]`. Rewrite using `[e, LinearEquiv.symm_apply_apply, hfe, Matrix.one_apply]`.
-/
theorem Xinv (hn : NFl X u n) : Xq X n.symm * Xq X n = 1 := by
  refine Matrix.ext fun b a => ?_
  simp only [Matrix.mul_apply, Xq]
  rw [Finset.sum_congr rfl fun d _ => mul_comm _ _, ← hT_sumR]
  have e : ∑ d, (VS D).hT (X.fY d) (n (X.eX a)) • n.symm (X.eX d) = n.symm (n (X.eX a)) := by
    conv_rhs => rw [Xq_expand hn a]
    rw [map_sum]
    simp only [map_smul, Xq]
  rw [e, LinearEquiv.symm_apply_apply, hfe, Matrix.one_apply]

/- English proof (translation)
Establish `hβ : ∀ β ∈ (aaD D b)⁻¹, β • xq X n b ∈ X.Lb`. Introduce `β hβ`. Establish `h` using `lattice_map_preserves_base (gmap_symm hL) (f_mem X hβ)`. Rewrite `h` using `[map_smul]`. Use `((LatA.mem_hermitianStandardLattice_iff_pairing_integral X _).1 h).2.2` as an intermediate fact.

Rewrite `this` using `[pW_smul]`. Then use the resulting hypothesis. Establish `h1 : (1 : D.host.E) ∈ aaD D b * (aaD D b)⁻¹`. Rewrite using `[mul_inv_cancel₀ (aa_ne X b)]`. Conclude with `FractionalIdeal.one_mem_one _`. Establish `key : ∀ t ∈ ((aaD D b * (aaD D b)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E), t • xq X n b ∈ aaLb X b`.

Introduce `t ht`. Rewrite `ht` using `[FractionalIdeal.coe_mul]`. Use `Submodule.mul_induction_on ht (fun α hα β hβ' => ?_) (fun s t hs ht => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `Submodule.subset_span ⟨α, hα, β • xq X n b, hβ β hβ', rfl⟩`.

Rewrite using `[add_smul]`. Conclude with `add_mem hs ht`. Simplify using `using key 1 h1`.
-/
theorem rows_mem (hL : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) (b : Fin D.R.rS) : xq X n b ∈ aaLb X b := by
  have hβ : ∀ β ∈ (aaD D b)⁻¹, β • xq X n b ∈ X.Lb := by
    intro β hβ
    have h := lattice_map_preserves_base (gmap_symm hL) (f_mem X hβ)
    rw [map_smul] at h
    have := ((LatA.mem_hermitianStandardLattice_iff_pairing_integral X _).1 h).2.2
    rwa [pW_smul] at this
  have h1 : (1 : D.host.E) ∈ aaD D b * (aaD D b)⁻¹ := by
    rw [mul_inv_cancel₀ (aa_ne X b)]; exact FractionalIdeal.one_mem_one _
  have key : ∀ t ∈ ((aaD D b * (aaD D b)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E),
      t • xq X n b ∈ aaLb X b := by
    intro t ht
    rw [FractionalIdeal.coe_mul] at ht
    refine Submodule.mul_induction_on ht (fun α hα β hβ' => ?_) (fun s t hs ht => ?_)
    · rw [mul_smul]
      exact Submodule.subset_span ⟨α, hα, β • xq X n b, hβ β hβ', rfl⟩
    · rw [add_smul]; exact add_mem hs ht
  simpa using key 1 h1

end LatF

open Alg LatF in

/- English proof (translation)
Introduce `D X u n hn hL`. Use `⟨fun b a _ => ex_shape hL b a, fun b => rows_mem hL b, fun b a => ?_⟩` and prove the remaining obligations. Establish `hinv : (Xq X n)⁻¹ = Xq X n.symm` using `Matrix.inv_eq_left_inv (Xinv hn)`. Use `show ((Xq X n)⁻¹ * Aq X n) b a ∈ _`. Rewrite using `[hinv, Matrix.mul_apply]`.

Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Conclude with `mul_mem_cancel (aa_ne X d) (ex_shape (gmap_symm hL) b d) (fa_shape hL d a)`.
-/
theorem dictLatF_holds : DictLatF := by
  intro D X u n hn hL
  refine ⟨fun b a _ => ex_shape hL b a, fun b => rows_mem hL b, fun b a => ?_⟩
  have hinv : (Xq X n)⁻¹ = Xq X n.symm := Matrix.inv_eq_left_inv (Xinv hn)
  show ((Xq X n)⁻¹ * Aq X n) b a ∈ _
  rw [hinv, Matrix.mul_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  exact mul_mem_cancel (aa_ne X d) (ex_shape (gmap_symm hL) b d) (fa_shape hL d a)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
