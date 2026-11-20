import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

section VecShift

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def vecShift (n : ℕ) : End ℂ (Fin n → V) where
  toFun v i := if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v v' := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vecShift_apply {n : ℕ} (v : Fin n → V) (i : Fin n) :
    vecShift n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl

/- English proof (translation)
Proceed by induction on `k generalizing i with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', End.mul_apply, vecShift_apply]`. Distinguish the cases in `h1 : 1 ≤ (i : ℕ)`.

Rewrite using `[if_pos h1, ih]`. Distinguish the cases in `h2 : k + 1 ≤ (i : ℕ)`. Rewrite using `[if_pos h2, if_pos (by simp only; omega)]`. Use `congr 2`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h2, if_neg (by simp only; omega)]`. Rewrite using `[if_neg h1, if_neg (by omega)]`.
-/
theorem vecShift_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → V) (i : Fin n) :
    (vecShift n ^ k) v i = if k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', End.mul_apply, vecShift_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [if_pos h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [if_pos h2, if_pos (by simp only; omega)]
        congr 2
        simp only; omega
      · rw [if_neg h2, if_neg (by simp only; omega)]
    · rw [if_neg h1, if_neg (by omega)]

def scaledDiag {n : ℕ} (f : End ℂ V) (c : Fin n → ℂ) : End ℂ (Fin n → V) where
  toFun v i := c i • f (v i)
  map_add' v v' := by ext i; simp [smul_add]
  map_smul' a v := by ext i; simp [smul_comm (c i) a]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scaledDiag_apply {n : ℕ} (f : End ℂ V) (c : Fin n → ℂ) (v : Fin n → V) (i : Fin n) :
    scaledDiag f c v i = c i • f (v i) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv i hi`. Establish `hle : absSpace (scaledDiag f c) r ≤ LinearMap.ker (LinearMap.proj i : (Fin n → V) →ₗ[ℂ] V)`. Use `iSup₂_le fun α hα u hu => ?_` and prove the remaining obligations. Establish `h1` using `congrFun (End.mem_eigenspace_iff.mp hu) i`.

Simplify using `only [scaledDiag_apply, Pi.smul_apply] at h1`. Establish `h2 : u i ∈ absSpace f ‖α / c i‖`. Use `Submodule.mem_iSup_of_mem (α / c i) (Submodule.mem_iSup_of_mem rfl ?_)` and prove the remaining obligations. Rewrite using `[End.mem_eigenspace_iff]`. Establish `: f (u i) = (c i)⁻¹ • (α • u i)`.

Rewrite using `[← h1, smul_smul, inv_mul_cancel₀ (hc i), one_smul]`. Rewrite using `[this, smul_smul, div_eq_inv_mul]`. Establish `h3 : ‖α / c i‖ ≠ 1`. Rewrite using `[norm_div, Ne, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (hc i)), hα]`. Conclude with `fun h => hi h.symm`.

Rewrite `h2` using `[absSpace_eq_bot_of_norm_charpoly_roots hf h3, Submodule.mem_bot]`. Simplify using `[h2]`. Simplify using `using hle hv`. Introduce `hv`. Rewrite using `[← Finset.univ_sum_single v]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : ‖c i‖ = r`. Establish `hvi : v i ∈ absSpace f 1`. Rewrite using `[absSpace_one_eq_top_of_norm_charpoly_roots hs hf]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hle : (absSpace f 1).map (LinearMap.single ℂ (fun _ : Fin n => V) i) ≤ absSpace (scaledDiag f c) r`. Simplify using `only [absSpace, Submodule.map_iSup]`. Use `iSup₂_le fun β hβ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `Submodule.mem_iSup_of_mem (c i * β) (Submodule.mem_iSup_of_mem (by rw [norm_mul, hβ, mul_one, hi]) ?_)` and prove the remaining obligations.

Rewrite `hx` using `[SetLike.mem_coe, End.mem_eigenspace_iff]`. Rewrite using `[End.mem_eigenspace_iff]`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[scaledDiag_apply, hx, smul_smul]`. Simplify using `[scaledDiag_apply, hj]`. Conclude with `hle ⟨v i, hvi, by simp⟩`. Simplify using `[hv i hi]`.
-/
theorem mem_absSpace_scaledDiag [FiniteDimensional ℂ V] {f : End ℂ V} (hs : f.IsSemisimple)
    (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {n : ℕ} (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) (r : ℝ)
    (v : Fin n → V) : v ∈ absSpace (scaledDiag f c) r ↔ ∀ i, ‖c i‖ ≠ r → v i = 0 := by
  classical
  constructor
  · intro hv i hi
    have hle : absSpace (scaledDiag f c) r ≤
        LinearMap.ker (LinearMap.proj i : (Fin n → V) →ₗ[ℂ] V) := by
      refine iSup₂_le fun α hα u hu => ?_
      have h1 := congrFun (End.mem_eigenspace_iff.mp hu) i
      simp only [scaledDiag_apply, Pi.smul_apply] at h1
      have h2 : u i ∈ absSpace f ‖α / c i‖ := by
        refine Submodule.mem_iSup_of_mem (α / c i) (Submodule.mem_iSup_of_mem rfl ?_)
        rw [End.mem_eigenspace_iff]
        have : f (u i) = (c i)⁻¹ • (α • u i) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ (hc i), one_smul]
        rw [this, smul_smul, div_eq_inv_mul]
      have h3 : ‖α / c i‖ ≠ 1 := by
        rw [norm_div, Ne, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (hc i)), hα]
        exact fun h => hi h.symm
      rw [absSpace_eq_bot_of_norm_charpoly_roots hf h3, Submodule.mem_bot] at h2
      simp [h2]
    simpa using hle hv
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ‖c i‖ = r
    · have hvi : v i ∈ absSpace f 1 := by
        rw [absSpace_one_eq_top_of_norm_charpoly_roots hs hf]; trivial
      have hle : (absSpace f 1).map (LinearMap.single ℂ (fun _ : Fin n => V) i) ≤
          absSpace (scaledDiag f c) r := by
        simp only [absSpace, Submodule.map_iSup]
        refine iSup₂_le fun β hβ => ?_
        rintro _ ⟨x, hx, rfl⟩
        refine Submodule.mem_iSup_of_mem (c i * β)
          (Submodule.mem_iSup_of_mem (by rw [norm_mul, hβ, mul_one, hi]) ?_)
        rw [SetLike.mem_coe, End.mem_eigenspace_iff] at hx
        rw [End.mem_eigenspace_iff]
        ext j
        by_cases hj : j = i
        · subst hj; simp [scaledDiag_apply, hx, smul_smul]
        · simp [scaledDiag_apply, hj]
      exact hle ⟨v i, hvi, by simp⟩
    · simp [hv i hi]

/- English proof (translation)
Establish `hc0 : ∀ i, c i ≠ 0` using `fun i h0 => by`. Use `hc i` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `(Real.rpow_pos_of_pos (zero_lt_one.trans hq) _).ne this`. Establish `hmem : ∀ (j : ℤ) (v : Fin n → V), v ∈ absSpace (scaledDiag f c) (q ^ ((j : ℝ) / 2)) ↔ ∀ i : Fin n, 2 * ((i : ℕ) : ℤ) + 1 - n ≠ j → v i = 0`.

Introduce `j v`. Rewrite using `[mem_absSpace_scaledDiag hs hf c hc0]`. Use `forall_congr' fun i => imp_congr_left (not_congr ?_)` and prove the remaining obligations. Rewrite using `[hc, Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne', ← @Int.cast_inj ℝ]`. Use `push_cast`.

Apply the tactic sequence `constructor <;> intro h <;> linarith`. Use `⟨eq_top_iff.mpr fun v _ => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.univ_sum_single v]`. Use `Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (2 * ((i : ℕ) : ℤ) + 1 - n) ((hmem _ _).mpr fun j hj => ?_)` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne]`.

Introduce and unpack `rfl`. Conclude with `hj rfl`. Establish `e1 : (-(k : ℝ) / 2) = ((-(k : ℤ) : ℤ) : ℝ) / 2` using `by push_cast; ring`. Establish `e2 : ((k : ℝ) / 2) = (((k : ℤ) : ℤ) : ℝ) / 2` using `by push_cast; ring`. Rewrite using `[e1, e2]`.

Use `⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[SetLike.mem_coe, hmem]`. Introduce `i hi`. Rewrite using `[vecShift_pow_apply]`. Use `split_ifs with hk`.

Conclude with `hv _ (by simp only; omega)`. Both sides reduce to the same expression. Rewrite `hv`, `hv'`, `ext1`, `i` using `[SetLike.mem_coe, hmem]`. Distinguish the cases in `hi : 2 * ((i : ℕ) : ℤ) + 1 - n = -(k : ℤ)`. Use `congrFun hvv ⟨i + k, by omega⟩` as an intermediate fact.

Rewrite `this` using `[vecShift_pow_apply, vecShift_pow_apply, if_pos (by simp), if_pos (by simp)]`. Simplify using `using this`. Rewrite using `[hv i hi, hv' i hi]`. Rewrite `hv` using `[SetLike.mem_coe, hmem]`. Use `⟨fun i => if hi : (i : ℕ) + k < n then v ⟨i + k, hi⟩ else 0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, hmem]`. Introduce `i hi`. Use `split_ifs with hk`. Conclude with `hv _ (by simp only; omega)`. Both sides reduce to the same expression.

Use `ext1 i`. Rewrite using `[vecShift_pow_apply]`. Use `split_ifs with hk h2`. Use `congr 2`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Conclude with `(hv i (by omega)).symm`.
-/
theorem isPurePair_scaledDiag_vecShift [FiniteDimensional ℂ V] {q : ℝ} (hq : 1 < q)
    {f : End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {n : ℕ}
    (c : Fin n → ℂ) (hc : ∀ i : Fin n, ‖c i‖ = q ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)) :
    IsPurePair q (scaledDiag f c) (vecShift n) := by
  classical
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 => by
    have := hc i
    rw [h0, norm_zero] at this
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _).ne this
  have hmem : ∀ (j : ℤ) (v : Fin n → V), v ∈ absSpace (scaledDiag f c) (q ^ ((j : ℝ) / 2)) ↔
      ∀ i : Fin n, 2 * ((i : ℕ) : ℤ) + 1 - n ≠ j → v i = 0 := by
    intro j v
    rw [mem_absSpace_scaledDiag hs hf c hc0]
    refine forall_congr' fun i => imp_congr_left (not_congr ?_)
    rw [hc, Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne', ← @Int.cast_inj ℝ]
    push_cast
    constructor <;> intro h <;> linarith
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun k => ?_⟩
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem (2 * ((i : ℕ) : ℤ) + 1 - n) ((hmem _ _).mpr fun j hj => ?_)
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact hj rfl
  · have e1 : (-(k : ℝ) / 2) = ((-(k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    have e2 : ((k : ℝ) / 2) = (((k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, hmem] at hv ⊢
      intro i hi
      rw [vecShift_pow_apply]
      split_ifs with hk
      · exact hv _ (by simp only; omega)
      · rfl
    · rw [SetLike.mem_coe, hmem] at hv hv'
      ext1 i
      by_cases hi : 2 * ((i : ℕ) : ℤ) + 1 - n = -(k : ℤ)
      · have := congrFun hvv ⟨i + k, by omega⟩
        rw [vecShift_pow_apply, vecShift_pow_apply, if_pos (by simp), if_pos (by simp)] at this
        simpa using this
      · rw [hv i hi, hv' i hi]
    · rw [SetLike.mem_coe, hmem] at hv
      refine ⟨fun i => if hi : (i : ℕ) + k < n then v ⟨i + k, hi⟩ else 0, ?_, ?_⟩
      · rw [SetLike.mem_coe, hmem]
        intro i hi
        split_ifs with hk
        · exact hv _ (by simp only; omega)
        · rfl
      · ext1 i
        rw [vecShift_pow_apply]
        split_ifs with hk h2
        · congr 2
          simp only; omega
        · exfalso; apply h2; simp only; omega
        · exact (hv i (by omega)).symm

end VecShift

end GlobalTheory.WeilDeligne

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h x`. Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Introduce `hx heig l`. Establish `hN : a.N = 0` using `(WD.monodromyZero_ofWeilDeligneRepClass_iff a).mp hx`.

Rewrite using `[WD.lpSp, WD.lpChar_mk, WD.tempered_mk]`. Introduce `φ hφ`. Establish `hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1` using `fun α hα => heig φ hφ α (by rw [WD.eig_mk]; exact hα)`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `hp` using `isPurePair_scaledDiag_vecShift hq (a.semisimple φ) hroots (fun i => (WDRep.spEig w l i : ℂ)) (fun i => by rw [WDRep.spEig, norm_qPow])`.

Set `e` to `TensorProduct.piScalarRight ℂ ℂ (Fin n → ℂ) (Fin l)`. Establish `h1 : ∀ t, e ((a.tensor (WDRep.sp h l)).ρ φ t) = scaledDiag (a.ρ φ) (fun i => (WDRep.spEig w l i : ℂ)) (e t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y => ext1 i`. Simplify using `[e, TensorProduct.piScalarRightHom_tmul, scaledDiag_apply, hφ, smul_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `h2 : ∀ t, e ((a.tensor (WDRep.sp h l)).N t) = vecShift l (e t)`. Introduce `t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => ext1 i`. Apply the tactic sequence `by_cases hi : 1 ≤ (i : ℕ) <;>`. Simplify using `[e, TensorProduct.piScalarRightHom_tmul, vecShift_apply, shiftEnd_apply, hN, hi]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Use `hp.of_equiv e.symm (fun v => ?_) (fun v => ?_)` and prove the remaining obligations. Take `⟨t, rfl⟩` from `e.surjective v`. Rewrite using `[← h1, e.symm_apply_apply, e.symm_apply_apply]`. Take `⟨t, rfl⟩` from `e.surjective v`.

Rewrite using `[← h2, e.symm_apply_apply, e.symm_apply_apply]`.
-/
theorem GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp h l)).tempered := by
  intro E Ω _ _ _ _ _ A w h x
  induction x using WD.ind with
  | hP n a =>
  intro hx heig l
  have hN : a.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff a).mp hx
  rw [WD.lpSp, WD.lpChar_mk, WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := fun α hα =>
    heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hp := isPurePair_scaledDiag_vecShift hq (a.semisimple φ) hroots
    (fun i => (WDRep.spEig w l i : ℂ)) (fun i => by rw [WDRep.spEig, norm_qPow])
  let e := TensorProduct.piScalarRight ℂ ℂ (Fin n → ℂ) (Fin l)
  have h1 : ∀ t, e ((a.tensor (WDRep.sp h l)).ρ φ t) =
      scaledDiag (a.ρ φ) (fun i => (WDRep.spEig w l i : ℂ)) (e t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      ext1 i
      simp [e, TensorProduct.piScalarRightHom_tmul, scaledDiag_apply, hφ, smul_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ t, e ((a.tensor (WDRep.sp h l)).N t) = vecShift l (e t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      ext1 i
      by_cases hi : 1 ≤ (i : ℕ) <;>
        simp [e, TensorProduct.piScalarRightHom_tmul, vecShift_apply, shiftEnd_apply, hN, hi]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine hp.of_equiv e.symm (fun v => ?_) (fun v => ?_)
  · obtain ⟨t, rfl⟩ := e.surjective v
    rw [← h1, e.symm_apply_apply, e.symm_apply_apply]
  · obtain ⟨t, rfl⟩ := e.surjective v
    rw [← h2, e.symm_apply_apply, e.symm_apply_apply]
