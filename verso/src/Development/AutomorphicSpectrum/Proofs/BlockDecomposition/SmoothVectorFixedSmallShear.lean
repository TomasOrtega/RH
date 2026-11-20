import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m)`. Apply `continuous_matrix` to reduce the goal to its premises. Introduce `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Apply the tactic sequence `simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>`.

Use `first`. Consider the case `exact continuous_const`. Consider the case `exact continuous_id.matrix_elem _ _`. Consider the case `fun_prop`. Establish `hGL : Continuous (GlobalTheory.BZMir.glEmb k m)` using `Continuous.units_map _ hmat`.

Conclude with `continuous_induced_rng.2 hGL`.
-/
theorem continuous_leviMir (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

/- English proof (translation)
Establish `key : ∀ b : Fin (n + 1) → k, 1 + b (Fin.last n) ≠ 0 → ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b ∧ (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (F …`. Introduce `b hb`. Establish `hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n)`. Simplify using `[GlobalTheory.BZMir.eLast, dotProduct_single]`. Establish `hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b = b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b`.

Rewrite using `[vecMulVec_mul_vecMulVec, hd]`. Use extensionality with `i j`. Simplify using `only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1`.

Rewrite using `[← mul_one_add]`. Conclude with `inv_mul_cancel₀ hb`. Establish `hmul : (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) * (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) = 1`. Rewrite using `[mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc, one_smul, add_sub_cancel_right]`. Establish `hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b)` using `⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩`.

Establish `hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b`. Rewrite using `[GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hu]`. Conclude with `hu.unit_spec`. Use `⟨hcoe, Units.inv_eq_of_mul_eq_one_right ?_⟩` and prove the remaining obligations. Rewrite using `[hcoe]`.

Conclude with `hmul`. Establish `h0 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k)`. Establish `h` using `(IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial`. Simplify using `using h`. Establish `hev : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, 1 + b (Fin.last n) ≠ 0`.

Establish `h1 : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, valuation k (b (Fin.last n)) < 1` using `(continuous_apply (Fin.last n)).continuousAt.preimage_mem_nhds (show {x : k | valuation k x < 1} ∈ 𝓝 ((fun b : Fin (n + 1) → k => b (Fin.last n)) 0) from h0)`. Use `filter_upwards [h1] with b hb h`. Establish `h2` using `(valuation k).map_one_add_of_lt hb`. Rewrite `h2` using `[h, map_zero]`. Conclude with `zero_ne_one h2`.

Establish `hv : Continuous fun b : Fin (n + 1) → k => vecMulVec (GlobalTheory.BZMir.eLast k n) b` using `continuous_matrix fun i j => by`. Simplify using `only [vecMulVec_apply]`. Conclude with `continuous_const.mul (continuous_apply j)`. Establish `hv0 : vecMulVec (GlobalTheory.BZMir.eLast k n) (0 : Fin (n + 1) → k) = 0`. Use extensionality with `i j`.

Simplify using `[vecMulVec_apply]`. Establish `h1 : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) (𝓝 0) (𝓝 1)`. Establish `hc : Continuous fun b : Fin (n + 1) → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + vecMulVec (GlobalTheory.BZMir.eLast k n) b` using `continuous_const.add hv`. Simplify `hc.tendsto (0 : Fin (n + 1) → k)` using `[hv0]`. Establish `hinv0 : Filter.Tendsto (fun b : Fin (n + 1) → k => (1 + b (Fin.last n))⁻¹) (𝓝 0) (𝓝 1)`.

Establish `h : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + b (Fin.last n)) (𝓝 0) (𝓝 1)`. Establish `hc : Continuous fun b : Fin (n + 1) → k => (1 : k) + b (Fin.last n)` using `continuous_const.add (continuous_apply (Fin.last n))`. Simplify using `using hc.tendsto (0 : Fin (n + 1) → k)`. Simplify using `using h.inv₀ one_ne_zero`. Establish `h2 : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) (𝓝 0) (𝓝 1)`.

Establish `hconst : Filter.Tendsto (fun _ : Fin (n + 1) → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) (𝓝 0) (𝓝 1)` using `tendsto_const_nhds`. Establish `h` using `hconst.sub (hinv0.smul (hv.tendsto 0))`. Simplify `h` using `[hv0]`. Establish `h1' : Filter.Tendsto (fun b : Fin (n + 1) → k => ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) (𝓝 0) (𝓝 1)`. Use `h1.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [hev] with b hb`. Conclude with `(key b hb).1.symm`. Establish `h2' : Filter.Tendsto (fun b : Fin (n + 1) → k => (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) (𝓝 0) (𝓝 1)`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hev] with b hb`.

Conclude with `(key b hb).2.symm`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Simplify using `only [Function.comp_def, Units.embedProduct_apply, inv_one, Units.val_one]`. Conclude with `h1'.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2')`.
-/
theorem tendsto_shearGL_zero (n : ℕ) :
    Filter.Tendsto (shearGL (k := k) n) (𝓝 0) (𝓝 1) := by
  have key : ∀ b : Fin (n + 1) → k, 1 + b (Fin.last n) ≠ 0 →
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b ∧
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    intro b hb
    have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
      simp [GlobalTheory.BZMir.eLast, dotProduct_single]
    have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
        b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [vecMulVec_mul_vecMulVec, hd]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
      rw [← mul_one_add]
      exact inv_mul_cancel₀ hb
    have hmul : (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) *
        (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) = 1 := by
      rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
        one_smul, add_sub_cancel_right]
    have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
      ⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩
    have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hu]
      exact hu.unit_spec
    refine ⟨hcoe, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hcoe]
    exact hmul
  have h0 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) := by
    have h := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using h
  have hev : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, 1 + b (Fin.last n) ≠ 0 := by
    have h1 : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, valuation k (b (Fin.last n)) < 1 :=
      (continuous_apply (Fin.last n)).continuousAt.preimage_mem_nhds
        (show {x : k | valuation k x < 1} ∈ 𝓝 ((fun b : Fin (n + 1) → k => b (Fin.last n)) 0) from h0)
    filter_upwards [h1] with b hb h
    have h2 := (valuation k).map_one_add_of_lt hb
    rw [h, map_zero] at h2
    exact zero_ne_one h2
  have hv : Continuous fun b : Fin (n + 1) → k => vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul (continuous_apply j)
  have hv0 : vecMulVec (GlobalTheory.BZMir.eLast k n) (0 : Fin (n + 1) → k) = 0 := by
    ext i j
    simp [vecMulVec_apply]
  have h1 : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b)
      (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun b : Fin (n + 1) → k =>
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
      continuous_const.add hv
    simpa [hv0] using hc.tendsto (0 : Fin (n + 1) → k)
  have hinv0 : Filter.Tendsto (fun b : Fin (n + 1) → k => (1 + b (Fin.last n))⁻¹) (𝓝 0) (𝓝 1) := by
    have h : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + b (Fin.last n)) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun b : Fin (n + 1) → k => (1 : k) + b (Fin.last n) :=
        continuous_const.add (continuous_apply (Fin.last n))
      simpa using hc.tendsto (0 : Fin (n + 1) → k)
    simpa using h.inv₀ one_ne_zero
  have h2 : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) (𝓝 0) (𝓝 1) := by
    have hconst : Filter.Tendsto (fun _ : Fin (n + 1) → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
        (𝓝 0) (𝓝 1) := tendsto_const_nhds
    have h := hconst.sub (hinv0.smul (hv.tendsto 0))
    simpa [hv0] using h
  have h1' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h1.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).1.symm
  have h2' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).2.symm
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply, inv_one, Units.val_one]
  exact h1'.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2')

/- English proof (translation)
Establish `hopen : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v}` using `hT v`. Establish `htend : Filter.Tendsto (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) (𝓝 0) (𝓝 1)`. Establish `h` using `((GlobalTheory.CompanionTheory.MirPair.continuous_leviMir (k := k) (n + 1)).tendsto 1).comp (GlobalTheory.CompanionTheory.MirPair.tendsto_shearGL_zero (k := k) n)`. Rewrite `h` using `[map_one]`. Conclude with `h`.

Establish `hΩ : (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) ⁻¹' {g | T g v = v} ∈ 𝓝 (0 : Fin (n + 1) → k)` using `htend (hopen.mem_nhds (by simp))`. Take `⟨r, hr⟩` from `GlobalTheory.CompanionTheory.BZOnto.PerpSmall.exists_box_subset hΩ`. Use `haveI : (valuation k).IsNontrivial := (ValuativeRel.isNontrivial_iff_isNontrivial (valuation k)).1 inferInstance`. Take `⟨x, hx0, hx1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`. Distinguish the cases in `hr1 : valuation k (r : k) < 1`.

Conclude with `⟨r, hr1, fun b hb => hr hb⟩`. Use `⟨Units.mk0 x hx0, by simpa using hx1, fun b hb => hr ?_⟩` and prove the remaining obligations. Introduce `j`. Establish `h1 : valuation k (b j) ≤ valuation k x` using `hb j`. Use `show valuation k (b j) ≤ valuation k (r : k)`.

Conclude with `le_trans h1 (le_trans hx1.le (not_lt.mp hr1))`.
-/
theorem shear_fix_vector {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) :
    ∃ r : kˣ, valuation k (r : k) < 1 ∧
      ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  have hopen : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have htend : Filter.Tendsto (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b))
      (𝓝 0) (𝓝 1) := by
    have h := ((GlobalTheory.CompanionTheory.MirPair.continuous_leviMir (k := k) (n + 1)).tendsto 1).comp (GlobalTheory.CompanionTheory.MirPair.tendsto_shearGL_zero (k := k) n)
    rw [map_one] at h
    exact h
  have hΩ : (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) ⁻¹'
      {g | T g v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) :=
    htend (hopen.mem_nhds (by simp))
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.exists_box_subset hΩ
  haveI : (valuation k).IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (valuation k)).1 inferInstance
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  by_cases hr1 : valuation k (r : k) < 1
  · exact ⟨r, hr1, fun b hb => hr hb⟩
  · refine ⟨Units.mk0 x hx0, by simpa using hx1, fun b hb => hr ?_⟩
    intro j
    have h1 : valuation k (b j) ≤ valuation k x := hb j
    show valuation k (b j) ≤ valuation k (r : k)
    exact le_trans h1 (le_trans hx1.le (not_lt.mp hr1))

end GlobalTheory.CompanionTheory.MirPair

end
