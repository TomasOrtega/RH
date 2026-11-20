import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCoker
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLeftInverseOfPhiModuleExactTriple

noncomputable section

namespace GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {ι κ μ : Type} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K) (isUnit_one_sub_mul_l l) _ h`. Use `⟨n, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hn (Submodule.Quotient.mk ⟨y, hy⟩)`. Rewrite `h1` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `_ ∈ (G.imM).comap T.M.subtype at h1`.

Rewrite `h1` using `[Submodule.mem_comap, Hom.imM, Submodule.mem_map]`. Take `⟨x, hx, hxy⟩` from `h1`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Rewrite `hxy` using `[LinearMap.restrictScalars_apply]`. Rewrite using `[hxy]`.

Use extensionality with `τ i`. Simplify using `[Algebra.smul_def]`.
-/
theorem exists_pow_of_coker (G : Hom Q T) (h : IsFiniteLength (A O K) G.coker) :
    ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]

open IntegralLeftInverseExactTriple in

/- English proof (translation)
Establish `h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ)` using `fun j => hG _ (mem_M_single T τ _ fun i => by`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _)`. Use `choose x hxM hx using h1`. Set `Xm : Matrix κ μ K⟦X⟧` to `Matrix.of fun k j => x j τ k`. Establish `hXA : ∀ k j, Xm k j ∈ A O K` using `fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k`.

Establish `hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hx j) τ) i` as an intermediate fact. Rewrite `this` using `[Hom.app_apply, Pi.smul_apply, Pi.single_eq_same]`. Rewrite using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]`.

Simplify `this` using `[Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm]`. Set `Z : Matrix κ κ K⟦X⟧` to `((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ`. Establish `hZA : ∀ k k', Z k k' ∈ A O K` using `fun k k' => sub_mem (smul_one_mem κ n k k') (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))`. Establish `hGZ : G.mat τ * Z = 0`. Simplify using `only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX, Matrix.smul_mul, Matrix.one_mul, sub_self]`.

Establish `h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k)`. Introduce `k`. Establish `hm` using `mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k`. Establish `hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0`. Use function extensionality and compare the values at `i`.

Use `congrFun (congrFun hGZ i) k` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Take `⟨w, hw, h⟩` from `(hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])`. Conclude with `⟨w, hw, h⟩`. Use `choose w hwM hw using h2`.

Set `W : Matrix ι κ K⟦X⟧` to `Matrix.of fun i k => w k τ i`. Establish `hWA : ∀ i k, W i k ∈ A O K` using `fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i`. Establish `hFW : F.mat τ * W = Z`. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hw k) τ) i` as an intermediate fact.

Rewrite `this` using `[Hom.app_apply, Pi.single_eq_same]`. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, W]`. Use `⟨W, Xm, hWA, hXA, ?_⟩` and prove the remaining obligations. Rewrite using `[hFW, sub_add_cancel]`.
-/
theorem exists_split (F : Hom P Q) (G : Hom Q T) (hFG : IsExactTriple F G) (n : ℕ)
    (hG : ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) (τ : ZMod a) :
    ∃ (W : Matrix ι κ K⟦X⟧) (Xm : Matrix κ μ K⟦X⟧), (∀ i k, W i k ∈ A O K) ∧
      (∀ k j, Xm k j ∈ A O K) ∧
      F.mat τ * W + Xm * G.mat τ = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, Xm, hWA, hXA, ?_⟩
  rw [hFW, sub_add_cancel]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_frob_smul_one (n : ℕ) :
    ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.BK.ExtExact

namespace GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {ι κ μ : Type} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_pow_of_coker G hFG.finiteLength`. Establish `hAB : ∀ f ∈ A O K, f ∈ invL l (S O K e)` using `fun f hf => le_away _ _ (A_le_S l e hf)`. Take `⟨c, hc, hvc⟩` from `Q.mem_extc.1 (mem_tot.1 hv τ)`. Take `⟨W, Xm, hWA, -, hsplit⟩` from `exists_split F G hFG n hn (τ - 1)`. Establish `hGc : (G.mat (τ - 1)).map (frob K l) *ᵥ c = 0`.

Establish `h1` using `congrFun hGv τ`. Rewrite `h1` using `[Pi.zero_apply, Hom.app_apply, hvc, Matrix.mulVec_mulVec, G.comm, ← Matrix.mulVec_mulVec]`. Establish `h2 : (T.mxInv τ * T.mx τ) *ᵥ ((G.mat (τ - 1)).map (frob K l) *ᵥ c) = 0`. Rewrite using `[← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]`. Rewrite `h2` using `[T.mxInv_mul_mx, Matrix.one_mulVec]`. Then use the resulting hypothesis.

Establish `hs : (F.mat (τ - 1)).map (frob K l) * W.map (frob K l) + Xm.map (frob K l) * (G.mat (τ - 1)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)`. Establish `: (F.mat (τ - 1) * W + Xm * G.mat (τ - 1)).map (frob K l).toRingHom = ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l).toRingHom` using `by rw [hsplit]`. Rewrite `this` using `[Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]`. Rewrite using `[← map_frob_smul_one]`. Conclude with `this`.

Establish `hc2 : (l : K) ^ n • c = (F.mat (τ - 1)).map (frob K l) *ᵥ (W.map (frob K l) *ᵥ c)`. Use `congrArg (· *ᵥ c) hs` as an intermediate fact. Rewrite `this` using `[Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGc, Matrix.mulVec_zero, add_zero, Matrix.smul_mulVec, Matrix.one_mulVec]`. Conclude with `this.symm`. Use `⟨((l : K) ^ n)⁻¹ • (W.map (frob K l) *ᵥ c), fun i => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, PowerSeries.smul_eq_C_mul]`. Use `mul_mem (HasK.C_mem _) (Subalgebra.sum_mem _ fun k _ => mul_mem ?_ (hc k))` and prove the remaining obligations. Conclude with `hAB _ (frob_mem_A l (hWA i k))`. Rewrite using `[hvc, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, ← hc2, inv_smul_smul₀ (pow_ne_zero _ (l_ne_zero l))]`.
-/
theorem exists_comp [NeZero e] (F : Hom P Q) (G : Hom Q T) (hFG : IsExactTriple F G)
    {v : Vec K a κ} (hv : v ∈ Q.ext (invL l (S O K e))) (hGv : G.app v = 0) (τ : ZMod a) :
    ∃ c' ∈ vecs ι (invL l (S O K e)), v τ = F.mat τ *ᵥ (P.mx τ *ᵥ c') := by
  obtain ⟨n, hn⟩ := exists_pow_of_coker G hFG.finiteLength
  have hAB : ∀ f ∈ A O K, f ∈ invL l (S O K e) := fun f hf => le_away _ _ (A_le_S l e hf)
  obtain ⟨c, hc, hvc⟩ := Q.mem_extc.1 (mem_tot.1 hv τ)
  obtain ⟨W, Xm, hWA, -, hsplit⟩ := exists_split F G hFG n hn (τ - 1)
  have hGc : (G.mat (τ - 1)).map (frob K l) *ᵥ c = 0 := by
    have h1 := congrFun hGv τ
    rw [Pi.zero_apply, Hom.app_apply, hvc, Matrix.mulVec_mulVec, G.comm,
      ← Matrix.mulVec_mulVec] at h1
    have h2 : (T.mxInv τ * T.mx τ) *ᵥ ((G.mat (τ - 1)).map (frob K l) *ᵥ c) = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rwa [T.mxInv_mul_mx, Matrix.one_mulVec] at h2
  have hs : (F.mat (τ - 1)).map (frob K l) * W.map (frob K l) +
      Xm.map (frob K l) * (G.mat (τ - 1)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
    have : (F.mat (τ - 1) * W + Xm * G.mat (τ - 1)).map (frob K l).toRingHom =
        ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l).toRingHom := by rw [hsplit]
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul] at this
    rw [← map_frob_smul_one]
    exact this
  have hc2 : (l : K) ^ n • c = (F.mat (τ - 1)).map (frob K l) *ᵥ (W.map (frob K l) *ᵥ c) := by
    have := congrArg (· *ᵥ c) hs
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGc, Matrix.mulVec_zero,
      add_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this.symm
  refine ⟨((l : K) ^ n)⁻¹ • (W.map (frob K l) *ᵥ c), fun i => ?_, ?_⟩
  · rw [Pi.smul_apply, PowerSeries.smul_eq_C_mul]
    refine mul_mem (HasK.C_mem _) (Subalgebra.sum_mem _ fun k _ => mul_mem ?_ (hc k))
    exact hAB _ (frob_mem_A l (hWA i k))
  · rw [hvc, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, ← hc2,
      inv_smul_smul₀ (pow_ne_zero _ (l_ne_zero l))]

end GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix in

/- English proof (translation)
Introduce `O K _ _ _ _ _ l e a _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG v hv hGv`. Use `choose c' hc' hvc' using fun τ => ExtExact.exists_comp F G hFG hv hGv τ`. Use `⟨fun τ => P.mx τ *ᵥ c' τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨_, hc' τ, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Rewrite using `[Hom.app_apply]`.

Conclude with `(hvc' τ).symm`.
-/
theorem GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e]
    [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ)
    (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G →
    ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  intro O K _ _ _ _ _ l e a _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG v hv hGv
  choose c' hc' hvc' using fun τ => ExtExact.exists_comp F G hFG hv hGv τ
  refine ⟨fun τ => P.mx τ *ᵥ c' τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨_, hc' τ, rfl⟩, ?_⟩
  funext τ
  rw [Hom.app_apply]
  exact (hvc' τ).symm
