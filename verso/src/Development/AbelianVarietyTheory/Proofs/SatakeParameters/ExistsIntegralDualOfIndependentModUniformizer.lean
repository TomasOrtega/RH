import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `zero_le`. Rewrite `h`, the goal using `[← WithZero.exp_log hx]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Establish `h1` using `congrArg (fun y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring => Valued.v (y : L)) u.mul_inv`. Simplify using `only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h1`. Establish `hu : Valued.v ((u : _) : L) ≤ 1` using `((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)).2`.

Establish `hw : Valued.v ((u⁻¹ : _) : L) ≤ 1` using `((u⁻¹ : _) : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).2`. Use `le_antisymm hu ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Establish `hx0 : (x : L) ≠ 0`.

Introduce `h0`. Rewrite `h` using `[h0, map_zero]`. Conclude with `zero_ne_one h`. Set `y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring` to `⟨(x : L)⁻¹, by show Valued.v (x : L)⁻¹ ≤ 1`. Rewrite using `[map_inv₀, h, inv_one]⟩`.

Establish `hxy : x * y = 1` using `Subtype.ext (mul_inv_cancel₀ hx0)`. Conclude with `⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩`.
-/
theorem isUnit_valuationSubring_iff (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := congrArg (fun y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring =>
      Valued.v (y : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h1
    have hu : Valued.v ((u : _) : L) ≤ 1 := ((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)).2
    have hw : Valued.v ((u⁻¹ : _) : L) ≤ 1 := ((u⁻¹ : _) : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).2
    refine le_antisymm hu ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ Valued.v ((u : _) : L) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    let y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring :=
      ⟨(x : L)⁻¹, by
        show Valued.v (x : L)⁻¹ ≤ 1
        rw [map_inv₀, h, inv_one]⟩
    have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_valuationSubring_iff]`. Establish `hx : Valued.v (x : L) ≤ 1` using `x.2`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`. Rewrite `hϖ` using `[h0, map_zero]`.

Conclude with `WithZero.zero_ne_coe hϖ`. Prove the components needed by the constructor for the conclusion. Introduce `hne`. Establish `hlt : Valued.v (x : L) < 1` using `lt_of_le_of_ne hx hne`. Establish `hle` using `le_exp_neg_one_of_lt_one' hlt`.

Use `⟨(x : L) / ϖ, ?_, by field_simp⟩` and prove the remaining obligations. Use `show Valued.v ((x : L) / ϖ) ≤ 1`. Rewrite using `[map_div₀, hϖ]`. Establish `hpos : (0 : WithZero (Multiplicative ℤ)) < ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))` using `WithZero.zero_lt_coe _`. Conclude with `(div_le_one₀ hpos).2 hle`.

Introduce and unpack `⟨b, hb, hxb⟩ h1`. Establish `hb' : Valued.v b ≤ 1` using `hb`. Rewrite `h1` using `[hxb, pow_one, map_mul, hϖ]`. Establish `: ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * Valued.v b ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * 1` using `by gcongr`. Rewrite `this` using `[h1, mul_one]`.

Conclude with `absurd this (by decide)`.
-/
theorem residue_eq_zero_iff_dvdPow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsLocalRing.residue _ x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_valuationSubring_iff]
  have hx : Valued.v (x : L) ≤ 1 := x.2
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  constructor
  · intro hne
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx hne
    have hle := le_exp_neg_one_of_lt_one' hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀, hϖ]
    have hpos : (0 : WithZero (Multiplicative ℤ)) < ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
      WithZero.zero_lt_coe _
    exact (div_le_one₀ hpos).2 hle
  · rintro ⟨b, hb, hxb⟩ h1
    have hb' : Valued.v b ≤ 1 := hb
    rw [hxb, pow_one, map_mul, hϖ] at h1
    have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * Valued.v b ≤
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * 1 := by gcongr
    rw [h1, mul_one] at this
    exact absurd this (by decide)

/- English proof (translation)
Introduce `L _ _ ϖ hϖ m ι _ _ z hz hind`. Set `O` to `(Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring`. Set `k` to `IsLocalRing.ResidueField O`. Set `res : O →+* k` to `IsLocalRing.residue O`. Establish `hres : Function.Surjective res` using `IsLocalRing.residue_surjective`.

Set `Z : Matrix ι (Fin m) O` to `fun i r => ⟨z i r, hz i r⟩`. Set `Zb : Matrix ι (Fin m) k` to `Z.map res`. Establish `hinj : LinearMap.ker (Matrix.mulVecLin Zbᵀ) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `w hw`.

Set `d : ι → O` to `fun i => (hres (w i)).choose`. Establish `hd : ∀ i, res (d i) = w i` using `fun i => (hres (w i)).choose_spec`. Establish `hsum : ∀ r, DvdPow ϖ 1 (∑ i, ((d i : O) : L) * z i r)`. Introduce `r`. Establish `h1 : res (∑ i, d i * Z i r) = 0`.

Use `congrFun hw r` as an intermediate fact. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this`. Rewrite using `[map_sum]`. Simplify `this` using `[Zb, hd, mul_comm]`. Establish `h2` using `(residue_eq_zero_iff_dvdPow hϖ _).1 h1`.

Simplify `h2` using `[Z]`. Establish `hdi` using `hind (fun i => (d i : L)) (fun i => (d i).2) hsum`. Use function extensionality and compare the values at `i`. Rewrite using `[← hd i]`. Conclude with `(residue_eq_zero_iff_dvdPow hϖ _).2 (hdi i)`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hinj`. Set `B : Matrix ι (Fin m) k` to `LinearMap.toMatrix' g`. Establish `hB : B * Zbᵀ = 1`. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Then use the resulting hypothesis.

Set `Bo : Matrix ι (Fin m) O` to `fun i r => (hres (B i r)).choose`. Establish `hBo : Bo.map res = B`. Use extensionality with `i r`. Conclude with `(hres (B i r)).choose_spec`. Set `M : Matrix ι ι O` to `Bo * Zᵀ`.

Establish `hM : M.map res = 1`. Simplify using `only [M, Matrix.map_mul, Matrix.transpose_map, hBo]`. Conclude with `hB`. Establish `hdet : IsUnit M.det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit]`.

Establish `: res M.det = 1`. Rewrite using `[RingHom.map_det]`. Express the relevant statement in the definitionally equal form `(M.map res).det = 1`. Rewrite using `[hM, Matrix.det_one]`. Rewrite using `[show IsLocalRing.residue O M.det = res M.det from rfl, this]`.

Conclude with `one_ne_zero`. Set `A : Matrix ι (Fin m) O` to `M⁻¹ * Bo`. Establish `hA : A * Zᵀ = 1`. Simplify using `only [A, Matrix.mul_assoc]`. Conclude with `Matrix.nonsing_inv_mul M hdet`.

Use `⟨fun i r => (A i r : L), fun i r => (A i r).2, fun i j => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun x : O => (x : L)) (congrFun (congrFun hA i) j)`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h`. Establish `h2 : ((∑ r, A i r * Z j r : O) : L) = ∑ r, (A i r : L) * z j r`. Simplify using `[Z, O]`.

Rewrite `h` using `[h2]`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem exists_dual_of_indepMod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  intro L _ _ ϖ hϖ m ι _ _ z hz hind
  classical
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  let Z : Matrix ι (Fin m) O := fun i r => ⟨z i r, hz i r⟩
  let Zb : Matrix ι (Fin m) k := Z.map res

  have hinj : LinearMap.ker (Matrix.mulVecLin Zbᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    let d : ι → O := fun i => (hres (w i)).choose
    have hd : ∀ i, res (d i) = w i := fun i => (hres (w i)).choose_spec
    have hsum : ∀ r, DvdPow ϖ 1 (∑ i, ((d i : O) : L) * z i r) := by
      intro r
      have h1 : res (∑ i, d i * Z i r) = 0 := by
        have := congrFun hw r
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
        rw [map_sum]
        simpa [Zb, hd, mul_comm] using this
      have h2 := (residue_eq_zero_iff_dvdPow hϖ _).1 h1
      simpa [Z] using h2
    have hdi := hind (fun i => (d i : L)) (fun i => (d i).2) hsum
    funext i
    rw [← hd i]
    exact (residue_eq_zero_iff_dvdPow hϖ _).2 (hdi i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  let B : Matrix ι (Fin m) k := LinearMap.toMatrix' g
  have hB : B * Zbᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  let Bo : Matrix ι (Fin m) O := fun i r => (hres (B i r)).choose
  have hBo : Bo.map res = B := by
    ext i r; exact (hres (B i r)).choose_spec
  let M : Matrix ι ι O := Bo * Zᵀ
  have hM : M.map res = 1 := by
    simp only [M, Matrix.map_mul, Matrix.transpose_map, hBo]
    exact hB
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : res M.det = 1 := by
      rw [RingHom.map_det]
      change (M.map res).det = 1
      rw [hM, Matrix.det_one]
    rw [show IsLocalRing.residue O M.det = res M.det from rfl, this]
    exact one_ne_zero
  let A : Matrix ι (Fin m) O := M⁻¹ * Bo
  have hA : A * Zᵀ = 1 := by
    simp only [A, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul M hdet
  refine ⟨fun i r => (A i r : L), fun i r => (A i r).2, fun i j => ?_⟩
  have h := congrArg (fun x : O => (x : L)) (congrFun (congrFun hA i) j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have h2 : ((∑ r, A i r * Z j r : O) : L) = ∑ r, (A i r : L) * z j r := by
    simp [Z, O]
  rw [h2] at h
  rw [h]
  split_ifs <;> simp

end GlobalTheory.Hk3.IntWitt
