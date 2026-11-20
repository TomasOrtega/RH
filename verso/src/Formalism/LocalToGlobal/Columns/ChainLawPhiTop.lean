import Formalism.LocalToGlobal.Columns.ChainLawPhiPf
import Formalism.LocalToGlobal.Columns.ChainTopLawB

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

section ClPfT

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Unfold `clPfUV`. Rewrite using `[dif_pos isUnit_one]`. Establish `: (isUnit_one : IsUnit (1 : k)).unit = 1` using `Units.ext rfl`. Rewrite using `[this, map_one, Units.val_one]`.
-/
theorem clPfUV_one {k : Type} [CommRing k] (χ : kˣ →* Kˣ) : clPfUV χ (1 : k) = 1 := by
  classical
  unfold clPfUV
  rw [dif_pos isUnit_one]
  have : (isUnit_one : IsUnit (1 : k)).unit = 1 := Units.ext rfl
  rw [this, map_one, Units.val_one]

/- English proof (translation)
Unfold `LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem fIdx_lt' {k₀ c n s : ℕ} (hk : k₀ ≤ n) (hs : s < n + c) : LocE.fIdx k₀ c n s < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `LocE.fIdx at h`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
private theorem fIdx_injective {k₀ c n s s' : ℕ} (hk : k₀ ≤ n) (hs : s < n + c) (hs' : s' < n + c)
    (h : LocE.fIdx k₀ c n s = LocE.fIdx k₀ c n s') : s = s' := by
  unfold LocE.fIdx at h
  split_ifs at h <;> omega

/- English proof (translation)
Unfold `clPfRed LocE.entB`. Establish `hf` using `fIdx_lt' (k₀ := k₀) (c := c) hk hp`. Simplify using `only [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_one, id]`. Unfold `Loc.atN Loc.eN`. Rewrite using `[dif_pos hf]`.

Distinguish the cases in `h : p = p'`. Substitute `h` using the available equality. Simplify using `[redP_one]`. Establish `h2 : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p'` using `fun h3 => h (fIdx_injective hk hp hp' h3)`. Simplify using `[h, h2, redP_zero]`.
-/
private theorem clPfRed_one_eq_ite {k₀ n c : ℕ} (hk : k₀ ≤ n) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    clPfRed P q k₀ c n c n (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap p p' = if p = p' then 1 else 0 := by
  unfold clPfRed LocE.entB
  have hf := fIdx_lt' (k₀ := k₀) (c := c) hk hp
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_one, id]
  unfold Loc.atN Loc.eN
  rw [dif_pos hf]
  by_cases h : p = p'
  · subst h
    simp [redP_one]
  · have h2 : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p' := fun h3 => h (fIdx_injective hk hp hp' h3)
    simp [h, h2, redP_zero]

/- English proof (translation)
Establish `h1 : (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)` using `Subgroup.one_mem _`. Rewrite using `[clPf_lamGBS hq0 ψ₀ χ hk hkr hJ h1]`. Rewrite using `[clPf_lam_congr ψ₀ χ (A := n + c) (Y := fun p p' : ℕ => if p = p' then (1 : 𝓞 E ⧸ P.asIdeal) else 0) hkr.le hJ (fun p p' hp hp' => clPfRed_one_eq_ite hk hp hp')]`. Establish `hb : ∀ i, diagonalBlockMatrix r t i (fun p p' : ℕ => if p = p' then (1 : 𝓞 E ⧸ P.asIdeal) else 0) = 1`. Introduce `i`.

Use extensionality with `s s'`. Simplify using `[diagonalBlockMatrix, Matrix.one_apply, Fin.ext_iff]`. Unfold `clPfLam`. Simplify using `only [hb, Matrix.det_one, clPfUV_one, Finset.prod_const_one, mul_one]`. Simplify using `[clPfS]`.
-/
theorem clPfT_lamGBS_one (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ r t J n c : ℕ} (hk : k₀ ≤ n) (hkr : k₀ < r) (hJ : r + J * t ≤ n + c) :
    LocE.lamGBS q ψ₀ χ k₀ r t J n c (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap = 1 := by
  have h1 : (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) :=
    Subgroup.one_mem _
  rw [clPf_lamGBS hq0 ψ₀ χ hk hkr hJ h1]
  rw [clPf_lam_congr ψ₀ χ (A := n + c) (Y := fun p p' : ℕ => if p = p' then (1 : 𝓞 E ⧸ P.asIdeal) else 0)
    hkr.le hJ (fun p p' hp hp' => clPfRed_one_eq_ite hk hp hp')]
  have hb : ∀ i, diagonalBlockMatrix r t i (fun p p' : ℕ => if p = p' then (1 : 𝓞 E ⧸ P.asIdeal) else 0) = 1 := by
    intro i
    ext s s'
    simp [diagonalBlockMatrix, Matrix.one_apply, Fin.ext_iff]
  unfold clPfLam
  simp only [hb, Matrix.det_one, clPfUV_one, Finset.prod_const_one, mul_one]
  simp [clPfS]

/- English proof (translation)
Establish `h` using `redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by`. Introduce `i _`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb)`.

Simplify `h` using `[Fin.prod_univ_two]`.
-/
private theorem reduction_mul_of_integral' {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a * b) = redP Q a * redP Q b := by
  have h := redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.prod_univ_two] using h

/- English proof (translation)
Establish `hqn : q ≠ 0`. Introduce and unpack `rfl`. Conclude with `hu (by simp)`. Establish `hq0 : ((q : ℕ) : E) ≠ 0` using `Nat.cast_ne_zero.mpr hqn`. Establish `hrN : r ≤ n + c` using `le_trans (Nat.le_add_right r (J * t)) hJ`.

Establish `hs : γ.symm ∈ LocE.JGsym P q k₀ rS r t n c` using `(LocE.JGsym P q k₀ rS r t n c).inv_mem hγ`. Establish `hγL` using `(Subgroup.mem_inf.mp hγ).1`. Establish `hsL` using `(Subgroup.mem_inf.mp hs).1`. Establish `hkr : k₀ < r` using `by omega`. Establish `hG` using `clPf_pat_JGsym hq hu hk hr hrN hs`.

Establish `hX` using `clPf_pat_JGsym hq hu hk hr hrN hγ`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[clPf_lamGBS hq0 ψ₀ χ hk hkr hJ hsL, clPf_lamGBS hq0 ψ₀ χ hk hkr hJ hγL]`. Establish `hcomp : ∀ p p', p < n + c → p' < n + c → clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap) (clPfRed P q k₀ c n c n γ.toLinearMap) p p' = clPfRed P q k₀ c n c n (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap p p'`. Introduce `p p' hp hp'`.

Establish `he : (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap = γ.symm.toLinearMap ∘ₗ γ.toLinearMap`. Use extensionality with `v`. Simplify using the standard rewrite rules. Rewrite using `[he]`. Unfold `clPfRed`.

Rewrite using `[clPf_entB_compL hq0 hk hk _ _ hp hp']`. Rewrite using `[redP_sum _ _ (fun u hu' => IntAt.mul (frameEntry_integral_of_stabilizer hq0 hk hp (Finset.mem_range.mp hu') hsL) (frameEntry_integral_of_stabilizer hq0 hk (Finset.mem_range.mp hu') hp' hγL))]`. Unfold `clPfMul`. Use `Finset.sum_congr rfl (fun u hu' => ?_)` and prove the remaining obligations. Conclude with `(reduction_mul_of_integral' (frameEntry_integral_of_stabilizer hq0 hk hp (Finset.mem_range.mp hu') hsL) (frameEntry_integral_of_stabilizer hq0 hk (Finset.mem_range.mp hu') hp' hγL)).symm`.

Establish `hmul : clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.symm.toLinearMap) * clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.toLinearMap) = clPfLam ψ₀ χ k₀ r t J (clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap) (clPfRed P q k₀ c n c n γ.toLinearMap))`. Unfold `clPfLam`. Rewrite using `[clPf_S_mulL hr hrN le_rfl hG hX, AddChar.map_add_eq_mul]`. Establish `hblk : ∀ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i (clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap) (clPfRed P q k₀ c n c n γ.toLinearMap))).det = clPfUV (χ i) (diagonalBlockMatrix r t i (clPfRed P q k₀ c n c n γ.symm.toLinearMap)).det * clPfUV (χ i) …`. Introduce `i hi`.

Establish `hi' : r + i * t + t ≤ n + c`. Establish `h3 : (i + 1) * t ≤ J * t` using `Nat.mul_le_mul_right t (Finset.mem_range.mp hi)`. Rewrite `h3` using `[Nat.add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[clPf_blk_mulL hr ht le_rfl hG hX hi', Matrix.det_mul, clPfUV_mul]`.

Rewrite using `[Finset.prod_congr rfl hblk, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmul, clPf_lam_congr ψ₀ χ hkr.le hJ hcomp, ← clPf_lamGBS hq0 ψ₀ χ hk hkr hJ (Subgroup.one_mem _)]`. Conclude with `clPfT_lamGBS_one hq0 ψ₀ χ hk hkr hJ`.
-/
theorem clPfT_lamGBS_symm (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t J n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS < r) (hJ : r + J * t ≤ n + c) (ht : 0 < t)
    {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hγ : γ ∈ LocE.JGsym P q k₀ rS r t n c) :
    LocE.lamGBS q ψ₀ χ k₀ r t J n c γ.symm.toLinearMap = (LocE.lamGBS q ψ₀ χ k₀ r t J n c γ.toLinearMap)⁻¹ := by
  have hqn : q ≠ 0 := by
    rintro rfl
    exact hu (by simp)
  have hq0 : ((q : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr hqn
  have hrN : r ≤ n + c := le_trans (Nat.le_add_right r (J * t)) hJ
  have hs : γ.symm ∈ LocE.JGsym P q k₀ rS r t n c := (LocE.JGsym P q k₀ rS r t n c).inv_mem hγ
  have hγL := (Subgroup.mem_inf.mp hγ).1
  have hsL := (Subgroup.mem_inf.mp hs).1
  have hkr : k₀ < r := by omega
  have hG := clPf_pat_JGsym hq hu hk hr hrN hs
  have hX := clPf_pat_JGsym hq hu hk hr hrN hγ
  apply eq_inv_of_mul_eq_one_left
  rw [clPf_lamGBS hq0 ψ₀ χ hk hkr hJ hsL, clPf_lamGBS hq0 ψ₀ χ hk hkr hJ hγL]
  have hcomp : ∀ p p', p < n + c → p' < n + c →
      clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap) (clPfRed P q k₀ c n c n γ.toLinearMap) p p' =
      clPfRed P q k₀ c n c n (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap p p' := by
    intro p p' hp hp'
    have he : (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap = γ.symm.toLinearMap ∘ₗ γ.toLinearMap := by
      ext v
      simp
    rw [he]
    unfold clPfRed
    rw [clPf_entB_compL hq0 hk hk _ _ hp hp']
    rw [redP_sum _ _ (fun u hu' => IntAt.mul (frameEntry_integral_of_stabilizer hq0 hk hp (Finset.mem_range.mp hu') hsL)
      (frameEntry_integral_of_stabilizer hq0 hk (Finset.mem_range.mp hu') hp' hγL))]
    unfold clPfMul
    refine Finset.sum_congr rfl (fun u hu' => ?_)
    exact (reduction_mul_of_integral' (frameEntry_integral_of_stabilizer hq0 hk hp (Finset.mem_range.mp hu') hsL)
      (frameEntry_integral_of_stabilizer hq0 hk (Finset.mem_range.mp hu') hp' hγL)).symm
  have hmul : clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.symm.toLinearMap) *
      clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.toLinearMap) =
      clPfLam ψ₀ χ k₀ r t J (clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap)
        (clPfRed P q k₀ c n c n γ.toLinearMap)) := by
    unfold clPfLam
    rw [clPf_S_mulL hr hrN le_rfl hG hX, AddChar.map_add_eq_mul]
    have hblk : ∀ i ∈ Finset.range J,
        clPfUV (χ i) (diagonalBlockMatrix r t i (clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap)
          (clPfRed P q k₀ c n c n γ.toLinearMap))).det =
        clPfUV (χ i) (diagonalBlockMatrix r t i (clPfRed P q k₀ c n c n γ.symm.toLinearMap)).det *
          clPfUV (χ i) (diagonalBlockMatrix r t i (clPfRed P q k₀ c n c n γ.toLinearMap)).det := by
      intro i hi
      have hi' : r + i * t + t ≤ n + c := by
        have h3 : (i + 1) * t ≤ J * t := Nat.mul_le_mul_right t (Finset.mem_range.mp hi)
        rw [Nat.add_mul, one_mul] at h3
        omega
      rw [clPf_blk_mulL hr ht le_rfl hG hX hi', Matrix.det_mul, clPfUV_mul]
    rw [Finset.prod_congr rfl hblk, Finset.prod_mul_distrib]
    ring
  rw [hmul, clPf_lam_congr ψ₀ χ hkr.le hJ hcomp, ← clPf_lamGBS hq0 ψ₀ χ hk hkr hJ (Subgroup.one_mem _)]
  exact clPfT_lamGBS_one hq0 ψ₀ χ hk hkr hJ

/- English proof (translation)
Unfold `redP at h`. Use `split_ifs at h with hex`. Take `⟨c, r, s, hs, h1, -⟩` from `hex`. Conclude with `⟨r, s, hs, h1⟩`. Conclude with `absurd rfl h`.
-/
private theorem intAt_of_redP_ne_zero {F : Type} [Field F] {Q : HeightOneSpectrum (𝓞 F)} {a : F}
    (h : redP Q a ≠ 0) : IntAt Q a := by
  unfold redP at h
  split_ifs at h with hex
  · obtain ⟨c, r, s, hs, h1, -⟩ := hex
    exact ⟨r, s, hs, h1⟩
  · exact absurd rfl h

/- English proof (translation)
Establish `h` using `redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by`. Introduce `i _`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb)`.

Simplify `h` using `[Fin.prod_univ_two]`.
-/
private theorem redP_mul_of_intAt {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a * b) = redP Q a * redP Q b := by
  have h := redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.prod_univ_two] using h

/- English proof (translation)
Establish `hs : γ.symm ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)` using `(stabL E (n + c) _).inv_mem hγ`. Establish `hu1` using `clPf_det_unit (k₀ := k₀) hq0 hk hγ`. Establish `hu2` using `clPf_det_unit (k₀ := k₀) hq0 hk hs`. Rewrite `hu1` using `[← clPf_det_red hq0 hk hγ]`. Rewrite `hu2` using `[← clPf_det_red hq0 hk hs]`.

Establish `i1` using `intAt_of_redP_ne_zero hu1.ne_zero`. Establish `i2` using `intAt_of_redP_ne_zero hu2.ne_zero`. Establish `hm : ((LinearEquiv.det γ.symm : Eˣ) : E) * ((LinearEquiv.det γ : Eˣ) : E) = 1`. Rewrite using `[← Units.val_mul, ← map_mul]`. Establish `h1 : γ.symm * γ = 1`.

Use extensionality with `v`. Simplify using the standard rewrite rules. Rewrite using `[h1, map_one, Units.val_one]`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[clPf_unitV, clPf_unitV, ← clPfUV_mul, ← redP_mul_of_intAt i2 i1, hm, redP_one, clPfUV_one]`.
-/
theorem clPfT_unitV_symm (hq0 : (q : E) ≠ 0) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ n c : ℕ} (hk : k₀ ≤ n)
    {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hγ : γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)) :
    (LocE.unitV χ ((LinearEquiv.det γ.symm : Eˣ) : E))⁻¹ = LocE.unitV χ ((LinearEquiv.det γ : Eˣ) : E) := by
  have hs : γ.symm ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) :=
    (stabL E (n + c) _).inv_mem hγ
  have hu1 := clPf_det_unit (k₀ := k₀) hq0 hk hγ
  have hu2 := clPf_det_unit (k₀ := k₀) hq0 hk hs
  rw [← clPf_det_red hq0 hk hγ] at hu1
  rw [← clPf_det_red hq0 hk hs] at hu2
  have i1 := intAt_of_redP_ne_zero hu1.ne_zero
  have i2 := intAt_of_redP_ne_zero hu2.ne_zero
  have hm : ((LinearEquiv.det γ.symm : Eˣ) : E) * ((LinearEquiv.det γ : Eˣ) : E) = 1 := by
    rw [← Units.val_mul, ← map_mul]
    have h1 : γ.symm * γ = 1 := by
      ext v
      simp
    rw [h1, map_one, Units.val_one]
  apply inv_eq_of_mul_eq_one_right
  rw [clPf_unitV, clPf_unitV, ← clPfUV_mul, ← redP_mul_of_intAt i2 i1, hm, redP_one, clPfUV_one]

/- English proof (translation)
Introduce `E K _ _ _ _ P q ψ₀ χ k₀ rS t j n' n hq hu hj ht hn' hn γ κ hγ hκ x`. Establish `hH : PhiGSLawHyp P q k₀ rS (k₀ + 2 * rS + 1) t j 0 n' 0 n` using `⟨hq, hu, hj, by omega, by omega, by omega, ht, by omega, by omega⟩`. Establish `h` using `clPf_phiGSLaw hH ψ₀ χ γ.symm (Subgroup.inv_mem _ hγ) κ hκ x`. Rewrite using `[h, clPfT_lamGBS_symm hq hu ψ₀ χ (k₀ := k₀) (rS := rS) (r := k₀ + 2 * rS + 1) (J := j) (n := n) (c := 0) (by omega) (by omega) (by omega) ht hγ, clPfT_unitV_symm (ciQ_ne_zero hu) (χ (j - 1)) (k₀ := k₀) (n := n) (c := 0) (by omega) hγ.1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem control_phi_law : CtlPhiLaw := by
  intro E K _ _ _ _ P q ψ₀ χ k₀ rS t j n' n hq hu hj ht hn' hn γ κ hγ hκ x
  have hH : PhiGSLawHyp P q k₀ rS (k₀ + 2 * rS + 1) t j 0 n' 0 n :=
    ⟨hq, hu, hj, by omega, by omega, by omega, ht, by omega, by omega⟩
  have h := clPf_phiGSLaw hH ψ₀ χ γ.symm (Subgroup.inv_mem _ hγ) κ hκ x
  rw [h, clPfT_lamGBS_symm hq hu ψ₀ χ (k₀ := k₀) (rS := rS) (r := k₀ + 2 * rS + 1) (J := j) (n := n) (c := 0) (by omega) (by omega) (by omega) ht hγ,
    clPfT_unitV_symm (ciQ_ne_zero hu) (χ (j - 1)) (k₀ := k₀) (n := n) (c := 0) (by omega) hγ.1]
  ring

end ClPfT

end Formalism.L2.Col
