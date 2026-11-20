import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

noncomputable section

open NumberField Filter Topology Matrix
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.SiegelEscape

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Use `set s : IdeleGroup K := posIdele (Real.exp 1) (Real.exp_pos _) with hs`. Establish `hz : (tor K fun _ : Fin n => (1 : ℝ)) = scalarUnits K n s` using `rfl`. Establish `hN : (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))).Normal`. Use `⟨fun x hx g => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hx`.

Rewrite using `[hz, ← map_zpow, ← scalarUnits_mul_comm, mul_inv_cancel_right, map_zpow]`. Conclude with `Subgroup.zpow_mem_zpowers _ _`. Establish `h` using `Subgroup.mul_normal (AdelicGLn.diagonal K n).range (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ)))`. Establish `hγ' : γ ∈ (↑((AdelicGLn.diagonal K n).range ⊔ Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))) : Set (AdelicGLn.AdelicGL K n))` using `hγ`. Rewrite `hγ'` using `[h]`.

Take `⟨a, ⟨γ₀, rfl⟩, b, hb, rfl⟩` from `Set.mem_mul.1 hγ'`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hb`. Conclude with `⟨γ₀, s ^ k, by rw [hz, map_zpow]⟩`.
-/
theorem exists_eq_of_mem_lat {γ : AdelicGLn.AdelicGL K n} (hγ : γ ∈ lat K n) :
    ∃ (γ₀ : GL (Fin n) K) (u : IdeleGroup K),
      γ = AdelicGLn.diagonal K n γ₀ * scalarUnits K n u := by
  set s : IdeleGroup K := posIdele (Real.exp 1) (Real.exp_pos _) with hs
  have hz : (tor K fun _ : Fin n => (1 : ℝ)) = scalarUnits K n s := rfl
  have hN : (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hz, ← map_zpow, ← scalarUnits_mul_comm, mul_inv_cancel_right, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have h := Subgroup.mul_normal (AdelicGLn.diagonal K n).range
    (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ)))
  have hγ' : γ ∈ (↑((AdelicGLn.diagonal K n).range ⊔
      Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))) : Set (AdelicGLn.AdelicGL K n)) := hγ
  rw [h] at hγ'
  obtain ⟨a, ⟨γ₀, rfl⟩, b, hb, rfl⟩ := Set.mem_mul.1 hγ'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ⟨γ₀, s ^ k, by rw [hz, map_zpow]⟩

/- English proof (translation)
Rewrite using `[detModule, MonoidHom.comp_apply, scalarUnits_apply, det_diagUnits, map_prod, coe_finset_prod_pos]`. Simplify using the standard rewrite rules.
-/
theorem detModule_scalarUnits (u : IdeleGroup K) :
    (detModule K n (scalarUnits K n u) : ℝ) = (ideleModule K u : ℝ) ^ n := by
  rw [detModule, MonoidHom.comp_apply, scalarUnits_apply, det_diagUnits, map_prod,
    coe_finset_prod_pos]
  simp

/- English proof (translation)
The claim follows from `mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL X)`.
-/
theorem detModule_unipGL {r : ℕ} (X : UPos n r → 𝔸[K]) : detModule K n (unipGL X) = 1 :=
  mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL X)

/- English proof (translation)
The claim follows from `mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)`.
-/
theorem detModule_diagonal (γ₀ : GL (Fin n) K) : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)

/- English proof (translation)
Establish `h` using `ideleModule_det_diagUnits_posIdele (K := K) (n := n) (fun i : Fin n => Real.exp (if (i : ℕ) < r then t else 0)) (fun _ => Real.exp_pos _)`. Establish `h2 : ∏ i : Fin n, Real.exp (if (i : ℕ) < r then t else 0) = Real.exp (r * t)`. Rewrite using `[← Real.exp_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`.

Use `congr 2`. Simplify using `[Fin.card_filter_val_lt, hr]`. Rewrite `h` using `[h2]`. Conclude with `h`.
-/
theorem detModule_aR {r : ℕ} (hr : r ≤ n) (t : ℝ) :
    (detModule K n (aR K n r t) : ℝ) = Real.exp (r * t) ^ Module.finrank ℚ K := by
  have h := ideleModule_det_diagUnits_posIdele (K := K) (n := n)
    (fun i : Fin n => Real.exp (if (i : ℕ) < r then t else 0)) (fun _ => Real.exp_pos _)
  have h2 : ∏ i : Fin n, Real.exp (if (i : ℕ) < r then t else 0) = Real.exp (r * t) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    simp [Fin.card_filter_val_lt, hr]
  rw [h2] at h
  exact h

/- English proof (translation)
Use `ext1 i`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using `[ratVec]`. Simplify using `[ratVec, h]`.
-/
theorem ratVec_single (l : Fin n) : ratVec (Pi.single l (1 : K)) = Pi.single l (1 : 𝔸[K]) := by
  ext1 i
  by_cases h : i = l
  · subst h; simp [ratVec]
  · simp [ratVec, h]

/- English proof (translation)
Establish `h : ¬ ((l : ℕ) < r)` using `by omega`. Use `ext1 j`. Rewrite using `[Matrix.single_one_vecMul]`. Simplify using `[unipMatrix, blockEntry_apply, h, Matrix.one_apply, Pi.single_apply, eq_comm]`.
-/
theorem single_vecMul_unipMatrix {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (X : UPos n r → 𝔸[K]) :
    Pi.single l (1 : 𝔸[K]) ᵥ* unipMatrix X = Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  ext1 j
  rw [Matrix.single_one_vecMul]
  simp [unipMatrix, blockEntry_apply, h, Matrix.one_apply, Pi.single_apply, eq_comm]

/- English proof (translation)
Establish `h : ¬ ((l : ℕ) < r)` using `by omega`. Establish `h1 : ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ = 1 → posIdele (K` using `K) ρ hρ = 1 := by`. Introduce and unpack `_ _ rfl`. Conclude with `map_one (posIdeleHom K)`. Rewrite using `[aR, tor, coe_diagUnits]`.

Use `ext1 j`. Rewrite using `[Matrix.vecMul_diagonal]`. Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality. Rewrite using `[h1 _ _ (by simp [h])]`.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`.
-/
theorem single_vecMul_aR {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (t : ℝ) :
    Pi.single l (1 : 𝔸[K]) ᵥ* ((aR K n r t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  have h1 : ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ = 1 → posIdele (K := K) ρ hρ = 1 := by
    rintro _ _ rfl
    exact map_one (posIdeleHom K)
  rw [aR, tor, coe_diagUnits]
  ext1 j
  rw [Matrix.vecMul_diagonal]
  by_cases hj : j = l
  · subst hj
    rw [h1 _ _ (by simp [h])]
    simp
  · simp [Pi.single_apply, hj]

/- English proof (translation)
Rewrite using `[mul_assoc, height_diagonal_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one, Reduction.height, ratVec_single, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, coe_unip …`. Establish `h0 : Pi.single l (1 : 𝔸[K]) ᵥ* Matrix.diagonal (fun _ : Fin n => ((u : IdeleGroup K) : 𝔸[K])) = ((u : IdeleGroup K) : 𝔸[K]) • Pi.single l (1 : 𝔸[K])` using `by ext1 j`. Rewrite using `[Matrix.vecMul_diagonal]`. Simplify using `[mul_comm]`. Rewrite using `[h0, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, single_vecMul_unipMatrix hl, single_vecMul_aR hl]`.

Establish `hne : (Pi.single l (1 : K) : Fin n → K) ≠ 0`. Introduce `h`. Use `congrFun h l` as an intermediate fact. Simplify using `at this`. Establish `hfc` using `hasFiniteContent_height q hne`.

Rewrite `hfc` using `[ratVec_single]`. Conclude with `adelicNorm_smul hfc u`.
-/
theorem height_eq {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (γ₀ : GL (Fin n) K) (u : IdeleGroup K)
    (X : UPos n r → 𝔸[K]) (t : ℝ) (q : AdelicGLn.AdelicGL K n) :
    Reduction.height (AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q))
        (Pi.single l (1 : K) ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (ideleModule K u : ℝ) *
        adelicNorm (Pi.single l (1 : 𝔸[K]) ᵥ* (q : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [mul_assoc, height_diagonal_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.vecMul_one, Reduction.height, ratVec_single, Units.val_mul, Units.val_mul,
    Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    coe_unipGL, scalarUnits_apply, coe_diagUnits]
  have h0 : Pi.single l (1 : 𝔸[K]) ᵥ* Matrix.diagonal (fun _ : Fin n => ((u : IdeleGroup K) : 𝔸[K])) =
      ((u : IdeleGroup K) : 𝔸[K]) • Pi.single l (1 : 𝔸[K]) := by
    ext1 j
    rw [Matrix.vecMul_diagonal]
    simp [mul_comm]
  rw [h0, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, single_vecMul_unipMatrix hl,
    single_vecMul_aR hl]
  have hne : (Pi.single l (1 : K) : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h l
    simp at this
  have hfc := hasFiniteContent_height q hne
  rw [ratVec_single] at hfc
  exact adelicNorm_smul hfc u

/- English proof (translation)
Introduce `K _ _ n r hr hrn D Q T hD hQ hT`. Establish `hn : 0 < n` using `by omega`. Use `set l : Fin n := ⟨n - 1, by omega⟩ with hldef`. Establish `hl : r ≤ (l : ℕ)` using `by simp only [hldef]; omega`. Use `set e : Fin n → K := Pi.single l 1 with he`.

Establish `he0 : e ≠ 0`. Introduce `h`. Use `congrFun h l` as an intermediate fact. Simplify using `[he] at this`. Take `⟨ε, hε, hheight⟩` from `exists_pos_le_height hT`.

Take `⟨P, hP, hvec⟩` from `exists_adelicNorm_vecMul_le_mul hQ`. Use `set A : ℝ := adelicNorm (ratVec e) with hA`. Establish `hA1 : 1 ≤ A` using `one_le_adelicNorm_ratVec he0`. Establish `hcont : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ)` using `continuous_subtype_val.comp continuous_detModule`. Take `⟨_, B, -, -, hB⟩` from `exists_pos_bounds hT hcont fun g _ => (detModule K n g).2`.

Take `⟨b, _, hb, -, hb'⟩` from `exists_pos_bounds hQ hcont fun g _ => (detModule K n g).2`. Use `set c : ℝ := ε / (P * A) with hc`. Establish `hPA : 0 < P * A` using `mul_pos hP (by linarith)`. Establish `hcpos : 0 < c` using `div_pos hε hPA`. Use `set d := Module.finrank ℚ K with hd`.

Establish `hd0 : d ≠ 0` using `Module.finrank_pos.ne'`. Establish `hr0 : (0 : ℝ) < r` using `Nat.cast_pos.2 hr`. Establish `htend : Tendsto (fun t : ℝ => Real.exp (r * t) ^ d) atTop atTop` using `(tendsto_pow_atTop hd0).comp (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))`. Use `filter_upwards [htend.eventually_gt_atTop (B / (c ^ n * b))] with t ht γ hγ X _ q hq hmem`. Take `⟨γ₀, u, rfl⟩` from `exists_eq_of_mem_lat hγ`.

Use `set E : ℝ := (ideleModule K u : ℝ) with hE`. Establish `hEpos : 0 < E` using `(ideleModule K u).2`. Use `set τ := AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q) with hτ`. Establish `hx0 : (e ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 0`. Introduce `h`.

Apply `he0` to reduce the goal to its premises. Establish `h2` using `congrArg (· ᵥ* ((γ₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h`. Simplify `h2` using `[Matrix.vecMul_vecMul, ← Units.val_mul]`. Establish `h1 : ε ≤ E * (P * A)`. Establish `h2` using `hheight τ hmem _ hx0`.

Rewrite `h2` using `[hτ, height_eq hl]`. Establish `h3` using `hvec q hq (ratVec e) (hasFiniteContent_ratVec he0)`. Rewrite `h3` using `[he, ratVec_single]`. Rewrite using `[hA, he, ratVec_single]`. Conclude with `h2.trans (mul_le_mul_of_nonneg_left h3 hEpos.le)`.

Establish `hcE : c ≤ E` using `(div_le_iff₀ hPA).2 h1`. Establish `hdet : (detModule K n τ : ℝ) = E ^ n * (Real.exp (r * t) ^ d * (detModule K n q : ℝ))`. Rewrite using `[hτ, map_mul, map_mul, map_mul, map_mul, detModule_diagonal, detModule_unipGL, one_mul, one_mul, Positive.val_mul, Positive.val_mul, detModule_scalarUnits, detModule_aR hrn.le]`. Establish `hle` using `(hB τ hmem).2`. Rewrite `hle` using `[hdet]`.

Establish `hbq` using `(hb' q hq).1`. Establish `hexp : 0 < Real.exp (r * t) ^ d` using `pow_pos (Real.exp_pos _) _`. Establish `hcn : 0 < c ^ n` using `pow_pos hcpos _`. Establish `h4 : c ^ n * (Real.exp (r * t) ^ d * b) ≤ B`. Use `le_trans ?_ hle` and prove the remaining obligations.

Conclude with `mul_le_mul (pow_le_pow_left₀ hcpos.le hcE n) (mul_le_mul_of_nonneg_left hbq hexp.le) (mul_pos hexp hb).le (pow_pos hEpos _).le`. Rewrite `ht` using `[div_lt_iff₀ (mul_pos hcn hb)]`. Use polynomial arithmetic with `[ht, h4]`.
-/
theorem escape : Escape := by
  intro K _ _ n r hr hrn D Q T hD hQ hT
  have hn : 0 < n := by omega
  set l : Fin n := ⟨n - 1, by omega⟩ with hldef
  have hl : r ≤ (l : ℕ) := by simp only [hldef]; omega
  set e : Fin n → K := Pi.single l 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h l
    simp [he] at this
  obtain ⟨ε, hε, hheight⟩ := exists_pos_le_height hT
  obtain ⟨P, hP, hvec⟩ := exists_adelicNorm_vecMul_le_mul hQ
  set A : ℝ := adelicNorm (ratVec e) with hA
  have hA1 : 1 ≤ A := one_le_adelicNorm_ratVec he0
  have hcont : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨_, B, -, -, hB⟩ := exists_pos_bounds hT hcont fun g _ => (detModule K n g).2
  obtain ⟨b, _, hb, -, hb'⟩ := exists_pos_bounds hQ hcont fun g _ => (detModule K n g).2
  set c : ℝ := ε / (P * A) with hc
  have hPA : 0 < P * A := mul_pos hP (by linarith)
  have hcpos : 0 < c := div_pos hε hPA
  set d := Module.finrank ℚ K with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have htend : Tendsto (fun t : ℝ => Real.exp (r * t) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd0).comp
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))
  filter_upwards [htend.eventually_gt_atTop (B / (c ^ n * b))] with t ht γ hγ X _ q hq hmem
  obtain ⟨γ₀, u, rfl⟩ := exists_eq_of_mem_lat hγ
  set E : ℝ := (ideleModule K u : ℝ) with hE
  have hEpos : 0 < E := (ideleModule K u).2
  set τ := AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q) with hτ
  have hx0 : (e ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 0 := by
    intro h
    apply he0
    have h2 := congrArg (· ᵥ* ((γ₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using h2
  have h1 : ε ≤ E * (P * A) := by
    have h2 := hheight τ hmem _ hx0
    rw [hτ, height_eq hl] at h2
    have h3 := hvec q hq (ratVec e) (hasFiniteContent_ratVec he0)
    rw [he, ratVec_single] at h3
    rw [hA, he, ratVec_single]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hEpos.le)
  have hcE : c ≤ E := (div_le_iff₀ hPA).2 h1
  have hdet : (detModule K n τ : ℝ) = E ^ n * (Real.exp (r * t) ^ d * (detModule K n q : ℝ)) := by
    rw [hτ, map_mul, map_mul, map_mul, map_mul, detModule_diagonal, detModule_unipGL, one_mul,
      one_mul, Positive.val_mul, Positive.val_mul, detModule_scalarUnits, detModule_aR hrn.le]
  have hle := (hB τ hmem).2
  rw [hdet] at hle
  have hbq := (hb' q hq).1
  have hexp : 0 < Real.exp (r * t) ^ d := pow_pos (Real.exp_pos _) _
  have hcn : 0 < c ^ n := pow_pos hcpos _
  have h4 : c ^ n * (Real.exp (r * t) ^ d * b) ≤ B := by
    refine le_trans ?_ hle
    exact mul_le_mul (pow_le_pow_left₀ hcpos.le hcE n)
      (mul_le_mul_of_nonneg_left hbq hexp.le) (mul_pos hexp hb).le (pow_pos hEpos _).le
  rw [div_lt_iff₀ (mul_pos hcn hb)] at ht
  nlinarith [ht, h4]

end GlobalTheory.CompanionTheory.SiegelEscape

end
