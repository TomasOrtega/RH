import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.IsotropicSubspaceEqPrimed

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section herm

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_add]`.
-/
lemma hm_add_l (x y w : Fin m → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, Matrix.mulVec_add]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_sub]`.
-/
lemma hm_sub_l (x y w : Fin m → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  simp [herm, Matrix.mulVec_sub]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_smul]`.
-/
lemma hm_smul_l (c : ℂ) (x w : Fin m → ℂ) : herm H (c • x) w = c * herm H x w := by
  simp [herm, Matrix.mulVec_smul]

/- English proof (translation)
Simplify using `[herm]`.
-/
lemma hm_add_r (x w w' : Fin m → ℂ) : herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm]

/- English proof (translation)
Simplify using `[herm]`.
-/
lemma hm_sub_r (x w w' : Fin m → ℂ) : herm H x (w - w') = herm H x w - herm H x w' := by
  simp [herm]

/- English proof (translation)
Simplify using `[herm]`.
-/
lemma hm_smul_r (c : ℂ) (x w : Fin m → ℂ) : herm H x (c • w) = star c * herm H x w := by
  simp [herm]

/- English proof (translation)
Establish `hij : ∀ i j, H j i = star (H i j)` using `fun i j => by`. Use `congrFun (congrFun hH j) i` as an intermediate fact. Simplify `this.symm` using `[Matrix.conjTranspose_apply]`. Simplify using `only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[hij]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hm_symm (hH : Hᴴ = H) (x y : Fin m → ℂ) : herm H y x = star (herm H x y) := by
  have hij : ∀ i j, H j i = star (H i j) := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hij]
  ring

/- English proof (translation)
Establish `h` using `hm_symm H hH x x`. Conclude with `(Complex.conj_eq_iff_re.mp h.symm).symm`.
-/
lemma hm_self_re (hH : Hᴴ = H) (x : Fin m → ℂ) : herm H x x = ((herm H x x).re : ℂ) := by
  have h := hm_symm H hH x x
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

end herm

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Hb, Matrix.conjTranspose_apply]`. Apply the tactic sequence `try (split_ifs <;> simp)`.

Simplify using `[Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]`.
-/
lemma Hb_ct (k : ℕ) : (Hb k)ᴴ = Hb k := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Hb, Matrix.conjTranspose_apply]
    try (split_ifs <;> simp)
  · simp [Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]

/- English proof (translation)
Establish `hne : ∀ i : Fin k, (Fin.castSucc i = Fin.last k) = False` using `fun i => eq_false (ne_of_lt (Fin.castSucc_lt_last i))`. Apply the tactic sequence `simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Complex.re_sum, Complex.normSq_apply, hne] <;> ring`.
-/
lemma re_Hb (k : ℕ) (u : Fin (k + 1) → ℂ) :
    (herm (Hb k) u u).re = (∑ i : Fin k, Complex.normSq (u i.castSucc)) - Complex.normSq (u (Fin.last k)) := by
  have hne : ∀ i : Fin k, (Fin.castSucc i = Fin.last k) = False :=
    fun i => eq_false (ne_of_lt (Fin.castSucc_lt_last i))
  simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Complex.re_sum,
    Complex.normSq_apply, hne] <;> ring

/- English proof (translation)
Assume the negation of the conclusion as `hle`. Use `push Not at hle`. Distinguish the cases in `hl : u (Fin.last k) = 0`. Apply `hu0` to reduce the goal to its premises. Rewrite `hle` using `[re_Hb, hl]`.

Simplify using `only [map_zero, sub_zero] at hle`. Establish `hs : ∀ i ∈ (Finset.univ : Finset (Fin k)), Complex.normSq (u i.castSucc) = 0` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 (le_antisymm hle (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _))`. Use function extensionality and compare the values at `i`. Use `Fin.lastCases hl (fun j => ?_) i` and prove the remaining obligations. Conclude with `Complex.normSq_eq_zero.1 (hs j (Finset.mem_univ _))`.

Use `set a := zb (Fin.last k) set b := -(u (Fin.last k)) set v := a • u + b • zb with hv`. Establish `hzu : herm (Hb k) zb u = 0` using `by rw [hm_symm _ (Hb_ct k), hu, star_zero]`. Establish `hvv : herm (Hb k) v v = a * star a * herm (Hb k) u u + b * star b * herm (Hb k) zb zb`. Simplify using `only [hv, hm_add_l, hm_add_r, hm_smul_l, hm_smul_r, hu, hzu]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hvl : v (Fin.last k) = 0`. Simplify using `only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : 0 ≤ (herm (Hb k) v v).re`. Rewrite using `[re_Hb, hvl]`.

Simplify using `only [map_zero, sub_zero]`. Conclude with `Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _`. Establish `hb : 0 < Complex.normSq b` using `Complex.normSq_pos.2 (neg_ne_zero.2 hl)`. Establish `h2 : (herm (Hb k) v v).re = Complex.normSq a * (herm (Hb k) u u).re + Complex.normSq b * (herm (Hb k) zb zb).re`. Rewrite using `[hvv, Complex.add_re]`.

Simplify using `only [Complex.star_def]`. Rewrite using `[Complex.mul_conj, Complex.mul_conj, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Establish `: Complex.normSq a * (herm (Hb k) u u).re ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma pos_b {k : ℕ} {zb u : Fin (k + 1) → ℂ} (hz : (herm (Hb k) zb zb).re < 0) (hu : herm (Hb k) u zb = 0)
    (hu0 : u ≠ 0) : 0 < (herm (Hb k) u u).re := by
  by_contra hle
  push Not at hle
  by_cases hl : u (Fin.last k) = 0
  · apply hu0
    rw [re_Hb, hl] at hle
    simp only [map_zero, sub_zero] at hle
    have hs : ∀ i ∈ (Finset.univ : Finset (Fin k)), Complex.normSq (u i.castSucc) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1
        (le_antisymm hle (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _))
    funext i
    refine Fin.lastCases hl (fun j => ?_) i
    exact Complex.normSq_eq_zero.1 (hs j (Finset.mem_univ _))
  · set a := zb (Fin.last k)
    set b := -(u (Fin.last k))
    set v := a • u + b • zb with hv
    have hzu : herm (Hb k) zb u = 0 := by rw [hm_symm _ (Hb_ct k), hu, star_zero]
    have hvv : herm (Hb k) v v = a * star a * herm (Hb k) u u + b * star b * herm (Hb k) zb zb := by
      simp only [hv, hm_add_l, hm_add_r, hm_smul_l, hm_smul_r, hu, hzu]
      ring
    have hvl : v (Fin.last k) = 0 := by
      simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b]; ring
    have h1 : 0 ≤ (herm (Hb k) v v).re := by
      rw [re_Hb, hvl]; simp only [map_zero, sub_zero]
      exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hb : 0 < Complex.normSq b := Complex.normSq_pos.2 (neg_ne_zero.2 hl)
    have h2 : (herm (Hb k) v v).re = Complex.normSq a * (herm (Hb k) u u).re +
        Complex.normSq b * (herm (Hb k) zb zb).re := by
      rw [hvv, Complex.add_re]
      simp only [Complex.star_def]
      rw [Complex.mul_conj, Complex.mul_conj, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : Complex.normSq a * (herm (Hb k) u u).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle
    nlinarith

section vec

variable {k r : ℕ}

/- English proof (translation)
Establish `eu` using `Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hu`. Establish `ez` using `Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz.1`. Rewrite `huz` using `[← eu, ← ez, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]`. Rewrite using `[← eu, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]`. Use `pos_b ?_ huz ?_` and prove the remaining obligations.

Establish `h2` using `hz.2`. Unfold `Tz at h2`. Rewrite `h2` using `[← ez, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`.

Apply `hu0` to reduce the goal to its premises. Rewrite using `[← eu, h]`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.jV]`.
-/
lemma posV {z u : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hu : inWb k r u)
    (huz : herm (Hpk k r) u z = 0) (hu0 : u ≠ 0) : 0 < (herm (Hpk k r) u u).re := by
  have eu := Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hu
  have ez := Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz.1
  rw [← eu, ← ez, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV] at huz
  rw [← eu, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]
  refine pos_b ?_ huz ?_
  · have h2 := hz.2
    unfold Tz at h2
    rw [← ez, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV] at h2
    linarith
  · intro h
    apply hu0
    rw [← eu, h]
    funext i
    simp [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV]

def pOut (k r : ℕ) (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  v - (herm (Hpk k r) v z / herm (Hpk k r) z z) • z

def nz (k r : ℕ) (p : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  (((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ) • p

/- English proof (translation)
Introduce `h`. Establish `h2 : 0 < Tz k r z`. Unfold `C2.StdZ at hz`. Conclude with `hz.2`. Unfold `Tz at h2`.

Rewrite `h2` using `[h]`. Simplify using `at h2`.
-/
lemma hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  have h2 : 0 < Tz k r z := by
    unfold C2.StdZ at hz
    exact hz.2
  unfold Tz at h2
  rw [h] at h2
  simp at h2

/- English proof (translation)
Introduce `h`. Apply `hzz_ne hz` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using `[herm]`.
-/
lemma z_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : z ≠ 0 := by
  intro h
  apply hzz_ne hz
  rw [h]
  simp [herm]

/- English proof (translation)
Unfold `pOut`. Rewrite using `[hm_sub_l, hm_smul_l, div_mul_cancel₀ _ (hzz_ne hz), sub_self]`.
-/
lemma pOut_orth {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (pOut k r z v) z = 0 := by
  unfold pOut
  rw [hm_sub_l, hm_smul_l, div_mul_cancel₀ _ (hzz_ne hz), sub_self]

/- English proof (translation)
Unfold `pOut`. Introduce `i hi`. Simplify using `[hv i hi, hz i hi]`.
-/
lemma pOut_inWb {z v : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hv : inWb k r v) : inWb k r (pOut k r z v) := by
  unfold pOut
  intro i hi
  simp [hv i hi, hz i hi]

/- English proof (translation)
Unfold `pOut`. Rewrite using `[hm_sub_r, hm_smul_r]`.
-/
lemma pOut_herm (u z v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u (pOut k r z v) =
      herm (Hpk k r) u v - star (herm (Hpk k r) v z / herm (Hpk k r) z z) * herm (Hpk k r) u z := by
  unfold pOut
  rw [hm_sub_r, hm_smul_r]

/- English proof (translation)
Unfold `nz`. Introduce `i hi`. Simplify using `[hp i hi]`.
-/
lemma nz_inWb {p : Fin (2 * r + k + 1) → ℂ} (hp : inWb k r p) : inWb k r (nz k r p) := by
  unfold nz
  intro i hi
  simp [hp i hi]

/- English proof (translation)
Unfold `nz`. Rewrite using `[hm_smul_l]`.
-/
lemma nz_herm_l (p w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (nz k r p) w = (((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ) * herm (Hpk k r) p w := by
  unfold nz
  rw [hm_smul_l]

/- English proof (translation)
Unfold `nz`. Rewrite using `[hm_smul_r]`. Establish `hc : star ((((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ)) ≠ 0`. Rewrite using `[star_ne_zero]`. Conclude with `(inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'` after adjusting the coercions.

Conclude with `⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by rw [h, mul_zero]⟩`.
-/
lemma nz_orth {p : Fin (2 * r + k + 1) → ℂ} (hp : 0 < (herm (Hpk k r) p p).re) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u (nz k r p) = 0 ↔ herm (Hpk k r) u p = 0 := by
  unfold nz
  rw [hm_smul_r]
  have hc : star ((((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    rw [star_ne_zero]
    exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by rw [h, mul_zero]⟩

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `(Formalism.QuantumDeterminants.hpkFacts k r).1`. Unfold `nz`. Rewrite using `[hm_smul_l, hm_smul_r, hm_self_re _ hH p]`. Use `set t := (herm (Hpk k r) p p).re with ht`. Establish `hst : Real.sqrt t * Real.sqrt t = t` using `Real.mul_self_sqrt hp.le`.

Establish `hs0 : Real.sqrt t ≠ 0` using `(Real.sqrt_pos.2 hp).ne'`. Rewrite using `[Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]`. Use `norm_cast`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma nz_unit {p : Fin (2 * r + k + 1) → ℂ} (hp : 0 < (herm (Hpk k r) p p).re) :
    herm (Hpk k r) (nz k r p) (nz k r p) = 1 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  unfold nz
  rw [hm_smul_l, hm_smul_r, hm_self_re _ hH p]
  set t := (herm (Hpk k r) p p).re with ht
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt hp.le
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  norm_cast
  field_simp
  linarith

end vec

/- English proof (translation)
Introduce `k r z z' hk hr hz hz'`. Establish `hz0` using `z_ne hz`. Establish `hz0'` using `z_ne hz'`. Distinguish the cases in `hc : ∃ c : ℂ, z' = c • z`. Take `⟨c, hcz⟩` from `hc`.

Establish `hc0 : c ≠ 0` using `by rintro rfl; apply hz0'; rw [hcz, zero_smul]`. Use `set e0 : Fin (2 * r + k + 1) → ℂ := Formalism.FourierDecayAlt.P.TwoByOneBlock.jV k r (Pi.single (0 : Fin (k + 1)) (1 : ℂ)) with he0d`. Establish `he0 : inWb k r e0` using `Formalism.FourierDecayAlt.P.TwoByOneBlock.inWb_jV _`. Establish `hne : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `he0u : herm (Hpk k r) e0 e0 = 1`. Rewrite using `[he0d, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]`.

Simplify using `[herm, Hb, Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hne]`. Use `set p := pOut k r z e0 with hpd`. Establish `hp0 : p ≠ 0`. Introduce `h`. Establish `e : e0 = (herm (Hpk k r) e0 z / herm (Hpk k r) z z) • z` using `sub_eq_zero.1 h`.

Use `set α := herm (Hpk k r) e0 z / herm (Hpk k r) z z`. Rewrite `he0u` using `[e, hm_smul_l, hm_smul_r, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, Complex.star_def, ← mul_assoc, Complex.mul_conj]`. Use `congrArg Complex.re he0u` as an intermediate fact. Simplify using `only [Complex.one_re] at this`. Rewrite `this` using `[← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]`.

Use polynomial arithmetic with `[Complex.normSq_nonneg α, hz.2]`. Establish `hpp : 0 < (herm (Hpk k r) p p).re` using `posV hz (pOut_inWb hz.1 he0) (pOut_orth hz e0) hp0`. Establish `hνz : herm (Hpk k r) (nz k r p) z = 0` using `by rw [nz_herm_l, pOut_orth hz, mul_zero]`. Establish `hWiff : ∀ u, u ∈ Wsp k r z ↔ u ∈ Wsp k r z'`. Introduce `u`.

Use `show (inWb k r u ∧ _) ↔ (inWb k r u ∧ _)`. Rewrite using `[hcz, hm_smul_r]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩; exact ⟨h1, by rw [h2, mul_zero]⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, (mul_eq_zero.1 h2).resolve_left (star_ne_zero.2 hc0)⟩`. Use `⟨GfBaseD.mk (nz k r p) (nz k r p) {u | u ∈ Wsp k r z ∧ herm (Hpk k r) u (nz k r p) = 0} ⟨nz_inWb (pOut_inWb hz.1 he0), hνz⟩ (nz_unit hpp) ((hWiff _).1 ⟨nz_inWb (pOut_inWb hz.1 he0), hνz⟩) (nz_unit hpp) (fun u => Iff.rfl) ?_⟩` and prove the remaining obligations. Introduce `u`. Use `show (u ∈ Wsp k r z ∧ _) ↔ (u ∈ Wsp k r z' ∧ _)`. Rewrite using `[hWiff u]`.

Use `set p := pOut k r z z' with hpd set p' := pOut k r z' z with hpd'`. Establish `hp0 : p ≠ 0`. Introduce `h`. Conclude with `hc ⟨_, sub_eq_zero.1 h⟩`. Establish `hp0' : p' ≠ 0`.

Introduce `h`. Establish `e : z = (herm (Hpk k r) z z' / herm (Hpk k r) z' z') • z'` using `sub_eq_zero.1 h`. Use `set β := herm (Hpk k r) z z' / herm (Hpk k r) z' z'`. Establish `hβ : β ≠ 0` using `by rintro hb; apply hz0; rw [e, hb, zero_smul]`. Conclude with `hc ⟨β⁻¹, by rw [e, smul_smul, inv_mul_cancel₀ hβ, one_smul]⟩`.

Establish `hpp : 0 < (herm (Hpk k r) p p).re` using `posV hz (pOut_inWb hz.1 hz'.1) (pOut_orth hz z') hp0`. Establish `hpp' : 0 < (herm (Hpk k r) p' p').re` using `posV hz' (pOut_inWb hz'.1 hz.1) (pOut_orth hz' z) hp0'`. Use `⟨GfBaseD.mk (nz k r p) (nz k r p') {u | u ∈ Wsp k r z ∧ herm (Hpk k r) u (nz k r p) = 0} ⟨nz_inWb (pOut_inWb hz.1 hz'.1), by rw [nz_herm_l, pOut_orth hz, mul_zero]⟩ (nz_unit hpp) ⟨nz_inWb (pOut_inWb hz'.1 hz.1), by rw [nz_herm_l, pOut_orth hz', mul_zero]⟩ (nz_unit hpp') (fun u => …` and prove the remaining obligations. Introduce `u`. Use `show ((inWb k r u ∧ _) ∧ _) ↔ ((inWb k r u ∧ _) ∧ _)`.

Rewrite using `[nz_orth hpp, nz_orth hpp', pOut_herm, pOut_herm]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Rewrite `h3` using `[h2, mul_zero, sub_zero]`. Conclude with `⟨⟨h1, h3⟩, by rw [h2, h3, mul_zero, sub_zero]⟩`.

Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Rewrite `h3` using `[h2, mul_zero, sub_zero]`. Conclude with `⟨⟨h1, h3⟩, by rw [h2, h3, mul_zero, sub_zero]⟩`.
-/
theorem gfBase : GfBase := by
  intro k r z z' hk hr hz hz'
  have hz0 := z_ne hz
  have hz0' := z_ne hz'
  by_cases hc : ∃ c : ℂ, z' = c • z
  · obtain ⟨c, hcz⟩ := hc
    have hc0 : c ≠ 0 := by rintro rfl; apply hz0'; rw [hcz, zero_smul]
    set e0 : Fin (2 * r + k + 1) → ℂ := Formalism.FourierDecayAlt.P.TwoByOneBlock.jV k r (Pi.single (0 : Fin (k + 1)) (1 : ℂ)) with he0d
    have he0 : inWb k r e0 := Formalism.FourierDecayAlt.P.TwoByOneBlock.inWb_jV _
    have hne : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have he0u : herm (Hpk k r) e0 e0 = 1 := by
      rw [he0d, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]
      simp [herm, Hb, Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hne]
    set p := pOut k r z e0 with hpd
    have hp0 : p ≠ 0 := by
      intro h
      have e : e0 = (herm (Hpk k r) e0 z / herm (Hpk k r) z z) • z := sub_eq_zero.1 h
      set α := herm (Hpk k r) e0 z / herm (Hpk k r) z z
      rw [e, hm_smul_l, hm_smul_r, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, Complex.star_def, ← mul_assoc,
        Complex.mul_conj] at he0u
      have := congrArg Complex.re he0u
      simp only [Complex.one_re] at this
      rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re] at this
      nlinarith [Complex.normSq_nonneg α, hz.2]
    have hpp : 0 < (herm (Hpk k r) p p).re := posV hz (pOut_inWb hz.1 he0) (pOut_orth hz e0) hp0
    have hνz : herm (Hpk k r) (nz k r p) z = 0 := by rw [nz_herm_l, pOut_orth hz, mul_zero]
    have hWiff : ∀ u, u ∈ Wsp k r z ↔ u ∈ Wsp k r z' := by
      intro u
      show (inWb k r u ∧ _) ↔ (inWb k r u ∧ _)
      rw [hcz, hm_smul_r]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, mul_zero]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (mul_eq_zero.1 h2).resolve_left (star_ne_zero.2 hc0)⟩
    refine ⟨GfBaseD.mk (nz k r p) (nz k r p) {u | u ∈ Wsp k r z ∧ herm (Hpk k r) u (nz k r p) = 0}
      ⟨nz_inWb (pOut_inWb hz.1 he0), hνz⟩ (nz_unit hpp) ((hWiff _).1 ⟨nz_inWb (pOut_inWb hz.1 he0), hνz⟩)
      (nz_unit hpp) (fun u => Iff.rfl) ?_⟩
    intro u
    show (u ∈ Wsp k r z ∧ _) ↔ (u ∈ Wsp k r z' ∧ _)
    rw [hWiff u]
  · set p := pOut k r z z' with hpd
    set p' := pOut k r z' z with hpd'
    have hp0 : p ≠ 0 := by
      intro h; exact hc ⟨_, sub_eq_zero.1 h⟩
    have hp0' : p' ≠ 0 := by
      intro h
      have e : z = (herm (Hpk k r) z z' / herm (Hpk k r) z' z') • z' := sub_eq_zero.1 h
      set β := herm (Hpk k r) z z' / herm (Hpk k r) z' z'
      have hβ : β ≠ 0 := by rintro hb; apply hz0; rw [e, hb, zero_smul]
      exact hc ⟨β⁻¹, by rw [e, smul_smul, inv_mul_cancel₀ hβ, one_smul]⟩
    have hpp : 0 < (herm (Hpk k r) p p).re := posV hz (pOut_inWb hz.1 hz'.1) (pOut_orth hz z') hp0
    have hpp' : 0 < (herm (Hpk k r) p' p').re := posV hz' (pOut_inWb hz'.1 hz.1) (pOut_orth hz' z) hp0'
    refine ⟨GfBaseD.mk (nz k r p) (nz k r p') {u | u ∈ Wsp k r z ∧ herm (Hpk k r) u (nz k r p) = 0}
      ⟨nz_inWb (pOut_inWb hz.1 hz'.1), by rw [nz_herm_l, pOut_orth hz, mul_zero]⟩ (nz_unit hpp)
      ⟨nz_inWb (pOut_inWb hz'.1 hz.1), by rw [nz_herm_l, pOut_orth hz', mul_zero]⟩ (nz_unit hpp')
      (fun u => Iff.rfl) ?_⟩
    intro u
    show ((inWb k r u ∧ _) ∧ _) ↔ ((inWb k r u ∧ _) ∧ _)
    rw [nz_orth hpp, nz_orth hpp', pOut_herm, pOut_herm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [h2, mul_zero, sub_zero] at h3
      exact ⟨⟨h1, h3⟩, by rw [h2, h3, mul_zero, sub_zero]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [h2, mul_zero, sub_zero] at h3
      exact ⟨⟨h1, h3⟩, by rw [h2, h3, mul_zero, sub_zero]⟩

end PI.UnitaryGroupMassFormula.GsFr
