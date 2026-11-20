import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CircleHomEqZpow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIsotropicOrOneClass
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UCharDet
open GlobalTheory.UTrans
open scoped ComplexOrder

/- English proof (translation)
Simplify using `only [hf, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) x y = starRingEnd ℂ (star x ⬝ᵥ (H *ᵥ y)) := by
  simp only [hf, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Set `i : Fin n` to `⟨0, hn⟩`. Establish `e` using `hH.mulVec_eigenvectorBasis i`. Establish `hl : hH.eigenvalues i ≠ 0`. Introduce `h0`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[hH.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0]; simp)`. Establish `hv : (hH.eigenvectorBasis i).ofLp ≠ 0`. Introduce `h0`. Use `hH.eigenvectorBasis.orthonormal.ne_zero i` as an intermediate fact.

Apply `this` to reduce the goal to its premises. Rewrite using `[← WithLp.ofLp_eq_zero]`. Conclude with `h0`. Use `⟨(hH.eigenvectorBasis i).ofLp, ?_⟩` and prove the remaining obligations. Rewrite using `[e, dotProduct_smul]`.

Introduce `h0`. Break down `smul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `hl h`. Conclude with `hv (dotProduct_star_self_eq_zero.1 h)`.
-/
theorem exists_aniso {n : ℕ} (hn : 0 < n) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) :
    ∃ v : Fin n → ℂ, star v ⬝ᵥ (H *ᵥ v) ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  have e := hH.mulVec_eigenvectorBasis i
  have hl : hH.eigenvalues i ≠ 0 := by
    intro h0
    apply hd
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0]; simp)
  have hv : (hH.eigenvectorBasis i).ofLp ≠ 0 := by
    intro h0
    have := hH.eigenvectorBasis.orthonormal.ne_zero i
    apply this
    rw [← WithLp.ofLp_eq_zero]
    exact h0
  refine ⟨(hH.eigenvectorBasis i).ofLp, ?_⟩
  rw [e, dotProduct_smul]
  intro h0
  rcases smul_eq_zero.1 h0 with h | h
  · exact hl h
  · exact hv (dotProduct_star_self_eq_zero.1 h)

/- English proof (translation)
Establish `key : ∀ x y : Fin n → ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) (g *ᵥ x) (g *ᵥ y) = starRingEnd ℂ (star x ⬝ᵥ ((gᴴ * H * g) *ᵥ y))` using `fun x y => by`. Rewrite using `[hf_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `h show gᴴ * H * g = H`. Use extensionality with `i j`.

Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[key, hf_eq]`. Use `congrArg (starRingEnd ℂ) this` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single, Pi.single_apply]`. Introduce `h x y`.

Establish `h' : gᴴ * H * g = H` using `h`. Rewrite using `[key, h', hf_eq]`.
-/
theorem isU_iff {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) :
    IsU (starRingEnd ℂ) (H.map (starRingEnd ℂ)) g ↔ g ∈ Formalism.QuantumDeterminants.UH H := by
  have key : ∀ x y : Fin n → ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) (g *ᵥ x) (g *ᵥ y) =
      starRingEnd ℂ (star x ⬝ᵥ ((gᴴ * H * g) *ᵥ y)) := fun x y => by
    rw [hf_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  constructor
  · intro h
    show gᴴ * H * g = H
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [key, hf_eq] at this
    have := congrArg (starRingEnd ℂ) this
    simpa [Matrix.mulVec_single, Pi.single_apply] using this
  · intro h x y
    have h' : gᴴ * H * g = H := h
    rw [key, h', hf_eq]

/- English proof (translation)
The claim follows from `Complex.conj_conj a ne_id := ⟨Complex.I, by intro h have := congrArg Complex.im h norm_num at this⟩ herm a b := by simp only [Matrix.map_apply, Complex.conj_conj] have := congrFun (congrFun hH b) a simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this rw [← this, Comple …`.
-/
theorem isHerm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) :
    IsHerm (starRingEnd ℂ) (H.map (starRingEnd ℂ)) where
  invol a := Complex.conj_conj a
  ne_id := ⟨Complex.I, by
    intro h
    have := congrArg Complex.im h
    norm_num at this⟩
  herm a b := by
    simp only [Matrix.map_apply, Complex.conj_conj]
    have := congrFun (congrFun hH b) a
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    rw [← this, Complex.conj_conj]
  det_ne := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hd

/- English proof (translation)
The claim follows from `GlobalTheory.UTrans.real_isotropic_or_one_class ℝ ℂ (starRingEnd ℂ) Complex.I (fun a => by simp) Complex.I_ne_zero (by simp) (fun x => ⟨x.re, x.im, by simp [Complex.re_add_im]⟩) ⟨RingEquiv.refl ℝ⟩ n _ (isHerm H hH hd).herm`.
-/
theorem iso_or_one_class {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) :
    (∃ z : Fin n → ℂ, z ≠ 0 ∧ hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) z z = 0) ∨
      ∀ x y : Fin n → ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) x x ≠ 0 →
        hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) y y ≠ 0 →
        ∃ a : ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) y y =
          starRingEnd ℂ a * a * hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) x x :=
  GlobalTheory.UTrans.real_isotropic_or_one_class ℝ ℂ (starRingEnd ℂ) Complex.I
    (fun a => by simp) Complex.I_ne_zero (by simp)
    (fun x => ⟨x.re, x.im, by simp [Complex.re_add_im]⟩) ⟨RingEquiv.refl ℝ⟩ n _
    (isHerm H hH hd).herm

/- English proof (translation)
Establish `ha' : aᴴ * H * a = H` using `ha`. Establish `hb' : bᴴ * H * b = H` using `hb`. Use `show (a * b)ᴴ * H * (a * b) = H`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

/- English proof (translation)
Use `show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H`. Simplify using the standard rewrite rules.
-/
theorem one_mem {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

/- English proof (translation)
Establish `hne : ∀ g ∈ Formalism.QuantumDeterminants.UH H, c g ≠ 0` using `fun g hg h0 => by`. Use `h1 g hg` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Set `X : Matrix (Fin n) (Fin n) ℂ → ℂˣ` to `fun g => if h : c g = 0 then 1 else Units.mk0 (c g) h`.

Establish `hX : ∀ g ∈ Formalism.QuantumDeterminants.UH H, (X g : ℂ) = c g` using `fun g hg => by`. Simplify using `only [X, dif_neg (hne g hg), Units.val_mk0]`. Establish `key` using `GlobalTheory.UTrans.char_eq_one_of_det_eq_one ℂ n (starRingEnd ℂ) (H.map (starRingEnd ℂ)) (isHerm H hH hd) (iso_or_one_class H hH hd) ℂˣ X (fun a b ha hb => by`. Rewrite `ha`, `hb` using `[isU_iff]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, hX _ ha, hX _ hb, hX _ (mul_mem ha hb), hm _ ha _ hb])`. Use `γ ((isU_iff H γ).2 hγ) hdet`. Rewrite using `[← hX γ hγ, key, Units.val_one]`.
-/
theorem kill {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) (c : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ g' ∈ Formalism.QuantumDeterminants.UH H, c (g * g') = c g * c g')
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ‖c g‖ = 1) (γ : Matrix (Fin n) (Fin n) ℂ) (hγ : γ ∈ Formalism.QuantumDeterminants.UH H)
    (hdet : γ.det = 1) : c γ = 1 := by
  have hne : ∀ g ∈ Formalism.QuantumDeterminants.UH H, c g ≠ 0 := fun g hg h0 => by
    have := h1 g hg
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  let X : Matrix (Fin n) (Fin n) ℂ → ℂˣ := fun g => if h : c g = 0 then 1 else Units.mk0 (c g) h
  have hX : ∀ g ∈ Formalism.QuantumDeterminants.UH H, (X g : ℂ) = c g := fun g hg => by
    simp only [X, dif_neg (hne g hg), Units.val_mk0]
  have key := GlobalTheory.UTrans.char_eq_one_of_det_eq_one ℂ n (starRingEnd ℂ) (H.map (starRingEnd ℂ)) (isHerm H hH hd)
    (iso_or_one_class H hH hd) ℂˣ X (fun a b ha hb => by
      rw [isU_iff] at ha hb
      apply Units.ext
      rw [Units.val_mul, hX _ ha, hX _ hb, hX _ (mul_mem ha hb), hm _ ha _ hb])
    γ ((isU_iff H γ).2 hγ) hdet
  rw [← hX γ hγ, key, Units.val_one]

/- English proof (translation)
Establish `hg' : gᴴ * H * g = H` using `hg`. Establish `e` using `congrArg Matrix.det hg'`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `e2 : star g.det * g.det = 1`. Apply `mul_right_cancel₀ hd` to reduce the goal to its premises.

Take the linear combination `e`. Establish `e3 : Complex.normSq g.det = 1`. Use `Complex.mul_conj g.det` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Conclude with `(this.symm.trans e2)` after adjusting the coercions.

Rewrite `e3` using `[Complex.normSq_eq_norm_sq]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e3`.
-/
theorem norm_det {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hd : H.det ≠ 0) (hg : g ∈ Formalism.QuantumDeterminants.UH H) :
    ‖g.det‖ = 1 := by
  have hg' : gᴴ * H * g = H := hg
  have e := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at e
  have e2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hd
    linear_combination e
  have e3 : Complex.normSq g.det = 1 := by
    have := Complex.mul_conj g.det
    rw [mul_comm] at this
    exact_mod_cast (this.symm.trans e2)
  rw [Complex.normSq_eq_norm_sq] at e3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e3

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨0, fun g hg => by rw [zpow_zero]; exact kill H hH hd c hm h1 g hg (Matrix.det_isEmpty)⟩`. Take `⟨v, hv⟩` from `exists_aniso hn H hH hd`. Use `set σ := starRingEnd ℂ`. Use `set G := H.map σ`.

Establish `hG` using `isHerm H hH hd`. Establish `hx : hf σ G v v ≠ 0`. Rewrite using `[hf_eq]`. Conclude with `(map_ne_zero _).2 hv`. Set `refl : Circle → Matrix (Fin n) (Fin n) ℂ` to `fun t => tv σ G v (((t : ℂ) - 1) / hf σ G v v)`.

Establish `hu : ∀ t : Circle, (t : ℂ) * σ t = 1` using `fun t => by`. Rewrite using `[Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]`. Establish `hU : ∀ t, refl t ∈ Formalism.QuantumDeterminants.UH H` using `fun t => (isU_iff H _).1 (CharDet.isU_refl hG hx (hu t))`. Establish `hcont : Continuous refl`. Simplify using `only [refl, tv]`.

Use `fun_prop`. Establish `c1 : c 1 = 1` using `kill H hH hd c hm h1 1 (one_mem H) Matrix.det_one`. Set `ψ : Circle →* Circle` to `{ toFun := fun t => ⟨c (refl t), by simpa [Submonoid.unitSphere] using h1 _ (hU t)⟩ map_one' := by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show c (refl 1) = 1`.

Simplify using `only [refl, Circle.coe_one]`. Rewrite using `[CharDet.refl_one, c1]`. Use the proof step `map_mul' := fun s t => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show c (refl (s * t)) = c (refl s) * c (refl t)`.

Rewrite using `[← hm _ (hU s) _ (hU t)]`. Simplify using `only [refl, Circle.coe_mul]`. Rewrite using `[CharDet.refl_mul _ _ hx] }`. Establish `hψ : Continuous ψ` using `Continuous.subtype_mk (hc.comp_continuous hcont hU) _`. Take `⟨m, hm'⟩` from `GlobalTheory.circle_hom_eq_zpow ψ hψ`.

Establish `hr : ∀ t : Circle, c (refl t) = (t : ℂ) ^ m` using `fun t => by`. Use `congrArg (fun s : Circle => (s : ℂ)) (hm' t)` as an intermediate fact. Rewrite `this` using `[Circle.coe_zpow]`. Conclude with `this`. Use `⟨m, fun g hg => ?_⟩` and prove the remaining obligations.

Set `e : Circle` to `⟨g.det, by simpa [Submonoid.unitSphere] using norm_det hd hg⟩`. Establish `hd0 : g.det ≠ 0` using `fun h0 => by`. Use `norm_det hd hg` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `k` using `kill H hH hd c hm h1 _ (mul_mem (hU e⁻¹) hg) (by`. Rewrite using `[Matrix.det_mul]`. Simplify using `only [refl]`. Rewrite using `[CharDet.refl_det _ hx, Circle.coe_inv]`. Conclude with `inv_mul_cancel₀ hd0)`.

Rewrite `k` using `[hm _ (hU _) _ hg, hr, Circle.coe_inv]`. Establish `k2` using `eq_inv_of_mul_eq_one_right k`. Rewrite using `[k2, _root_.inv_zpow, inv_inv]`.
-/
theorem char_eq_det_zpow {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0)
    (c : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ g' ∈ Formalism.QuantumDeterminants.UH H, c (g * g') = c g * c g')
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ‖c g‖ = 1) (hc : ContinuousOn c (Formalism.QuantumDeterminants.UH H)) :
    ∃ m : ℤ, ∀ g ∈ Formalism.QuantumDeterminants.UH H, c g = g.det ^ m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun g hg => by rw [zpow_zero]; exact kill H hH hd c hm h1 g hg (Matrix.det_isEmpty)⟩
  obtain ⟨v, hv⟩ := exists_aniso hn H hH hd
  set σ := starRingEnd ℂ
  set G := H.map σ
  have hG := isHerm H hH hd
  have hx : hf σ G v v ≠ 0 := by
    rw [hf_eq]
    exact (map_ne_zero _).2 hv
  let refl : Circle → Matrix (Fin n) (Fin n) ℂ := fun t => tv σ G v (((t : ℂ) - 1) / hf σ G v v)
  have hu : ∀ t : Circle, (t : ℂ) * σ t = 1 := fun t => by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hU : ∀ t, refl t ∈ Formalism.QuantumDeterminants.UH H := fun t => (isU_iff H _).1 (CharDet.isU_refl hG hx (hu t))
  have hcont : Continuous refl := by
    simp only [refl, tv]
    fun_prop
  have c1 : c 1 = 1 := kill H hH hd c hm h1 1 (one_mem H) Matrix.det_one
  let ψ : Circle →* Circle :=
    { toFun := fun t => ⟨c (refl t), by simpa [Submonoid.unitSphere] using h1 _ (hU t)⟩
      map_one' := by
        apply Subtype.ext
        show c (refl 1) = 1
        simp only [refl, Circle.coe_one]
        rw [CharDet.refl_one, c1]
      map_mul' := fun s t => by
        apply Subtype.ext
        show c (refl (s * t)) = c (refl s) * c (refl t)
        rw [← hm _ (hU s) _ (hU t)]
        simp only [refl, Circle.coe_mul]
        rw [CharDet.refl_mul _ _ hx] }
  have hψ : Continuous ψ := Continuous.subtype_mk (hc.comp_continuous hcont hU) _
  obtain ⟨m, hm'⟩ := GlobalTheory.circle_hom_eq_zpow ψ hψ
  have hr : ∀ t : Circle, c (refl t) = (t : ℂ) ^ m := fun t => by
    have := congrArg (fun s : Circle => (s : ℂ)) (hm' t)
    rw [Circle.coe_zpow] at this
    exact this
  refine ⟨m, fun g hg => ?_⟩
  let e : Circle := ⟨g.det, by simpa [Submonoid.unitSphere] using norm_det hd hg⟩
  have hd0 : g.det ≠ 0 := fun h0 => by
    have := norm_det hd hg
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have k := kill H hH hd c hm h1 _ (mul_mem (hU e⁻¹) hg) (by
    rw [Matrix.det_mul]
    simp only [refl]
    rw [CharDet.refl_det _ hx, Circle.coe_inv]
    exact inv_mul_cancel₀ hd0)
  rw [hm _ (hU _) _ hg, hr, Circle.coe_inv] at k
  have k2 := eq_inv_of_mul_eq_one_right k
  rw [k2, _root_.inv_zpow, inv_inv]

end GlobalTheory.UCharDet

namespace GlobalTheory.AdSpan

/- English proof (translation)
Introduce `D θ V hθ _ z hz hz1 hzc`. Take `⟨L, hL1, hLmul, hLc, hLarch, hLinv, -, -, -, hHd⟩` from `GlobalTheory.RealLift.exists_real_lift D θ V hθ`. Establish `hsing : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), (Pi.mulSingle τ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D V)`. Introduce `τ g hg ρ`. Distinguish the cases in `h : ρ = τ`.

Substitute `h` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]` and apply the resulting hypothesis. Rewrite using `[Pi.mulSingle_eq_of_ne h]`. Conclude with `GlobalTheory.UCharDet.one_mem _`. Establish `hc : ∀ τ, ∃ m : ℤ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), z (L (Pi.mulSingle τ g)) = g.det ^ m`.

Introduce `τ`. Use `GlobalTheory.UCharDet.char_eq_det_zpow (gramAt D V τ) (hHd τ).1 (hHd τ).2 (fun g => z (L (Pi.mulSingle τ g))) (fun g hg g' hg' => ?_) (fun g hg => hz1 _ (hL1 _ (hsing τ g hg)).1) ?_` and prove the remaining obligations. Use `show z (L (Pi.mulSingle τ (g * g'))) = z (L (Pi.mulSingle τ g)) * z (L (Pi.mulSingle τ g'))`. Rewrite using `[Pi.mulSingle_mul, hLmul _ (hsing τ g hg) _ (hsing τ g' hg'), hz _ (hL1 _ (hsing τ g hg)).1 _ (hL1 _ (hsing τ g' hg')).1]`. Establish `hcs : Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ => (Pi.mulSingle τ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)`.

Use `continuous_pi fun ρ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ρ = τ`. Substitute `h` using the available equality. Simplify using `only [Pi.mulSingle_eq_same]`. Conclude with `continuous_id`.

Simplify using `only [Pi.mulSingle_eq_of_ne h]`. Conclude with `continuous_const`. Conclude with `hzc.comp (hLc.comp hcs.continuousOn fun g hg => hsing τ g hg) fun g hg => (hL1 _ (hsing τ g hg)).1`. Use `choose m hm using hc`. Use `⟨m, fun a ha => ?_⟩` and prove the remaining obligations.

Use `set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => Formalism.L2.Pj.archM V (θ τ) a with hu_def`. Establish `hu : u ∈ GlobalTheory.HolDict.UG (gramAt D V)` using `hLarch a`. Establish `hz0 : ∀ b ∈ GinfC V, z b ≠ 0` using `fun b hb h0 => by`. Use `hz1 b hb` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `zero_ne_one this`. Establish `hone : (1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D V)` using `fun τ => GlobalTheory.UCharDet.one_mem _`. Establish `zL1 : z (L 1) = 1`. Establish `e1 : L 1 = L 1 * L 1` using `by simpa using hLmul 1 hone 1 hone`. Establish `m1` using `(hL1 _ hone).1`.

Establish `e2` using `hz _ m1 _ m1`. Rewrite `e2` using `[← e1]`. Conclude with `(mul_eq_left₀ (hz0 _ m1)).1 e2.symm`. Set `fam : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ` to `fun s τ => if τ ∈ s then u τ else 1`. Establish `hfam : ∀ s, fam s ∈ GlobalTheory.HolDict.UG (gramAt D V)` using `fun s τ => by`.

Simplify using `only [fam]`. Use `split_ifs`. Conclude with `hu τ`. Conclude with `GlobalTheory.UCharDet.one_mem _`. Establish `key : ∀ s : Finset D.what₂.Tau, z (L (fam s)) = ∏ τ ∈ s, (u τ).det ^ m τ`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `: fam ∅ = 1` using `funext fun τ => by simp [fam]`. Rewrite using `[this, Finset.prod_empty]`.

Conclude with `zL1`. Consider the case `insert b s hb ih`. Establish `e : fam (insert b s) = Pi.mulSingle b (u b) * fam s` using `funext fun τ => by`. Distinguish the cases in `h : τ = b`. Substitute `h` using the available equality.

Simplify using `[fam, hb]`. Simplify using `[fam, h]`. Rewrite using `[e, hLmul _ (hsing b _ (hu b)) _ (hfam s), hz _ (hL1 _ (hsing b _ (hu b))).1 _ (hL1 _ (hfam s)).1, hm b _ (hu b), ih, Finset.prod_insert hb]`. Establish `hall : fam Finset.univ = u` using `funext fun τ => by simp [fam]`. Use `key Finset.univ` as an intermediate fact.

Rewrite `this` using `[hall, hLinv a ha]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem char_eq_detPow : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → V.SigOK → ∀ z : GA D V → ℂ, (∀ a ∈ GinfC V, ∀ a' ∈ GinfC V, z (a * a') = z a * z a') → (∀ a ∈ GinfC V, ‖z a‖ = 1) → ContinuousOn z (GinfC V : Set (GA D V)) → ∃ m : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, z a = detPow θ V m a := by
  intro D θ V hθ _ z hz hz1 hzc
  obtain ⟨L, hL1, hLmul, hLc, hLarch, hLinv, -, -, -, hHd⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hsing : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      (Pi.mulSingle τ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
    intro τ g hg ρ
    by_cases h : ρ = τ
    · subst h
      rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h]
      exact GlobalTheory.UCharDet.one_mem _
  have hc : ∀ τ, ∃ m : ℤ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), z (L (Pi.mulSingle τ g)) = g.det ^ m := by
    intro τ
    refine GlobalTheory.UCharDet.char_eq_det_zpow (gramAt D V τ) (hHd τ).1 (hHd τ).2 (fun g => z (L (Pi.mulSingle τ g)))
      (fun g hg g' hg' => ?_) (fun g hg => hz1 _ (hL1 _ (hsing τ g hg)).1) ?_
    · show z (L (Pi.mulSingle τ (g * g'))) = z (L (Pi.mulSingle τ g)) * z (L (Pi.mulSingle τ g'))
      rw [Pi.mulSingle_mul, hLmul _ (hsing τ g hg) _ (hsing τ g' hg'),
        hz _ (hL1 _ (hsing τ g hg)).1 _ (hL1 _ (hsing τ g' hg')).1]
    · have hcs : Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
          (Pi.mulSingle τ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
        refine continuous_pi fun ρ => ?_
        by_cases h : ρ = τ
        · subst h
          simp only [Pi.mulSingle_eq_same]
          exact continuous_id
        · simp only [Pi.mulSingle_eq_of_ne h]
          exact continuous_const
      exact hzc.comp (hLc.comp hcs.continuousOn fun g hg => hsing τ g hg) fun g hg => (hL1 _ (hsing τ g hg)).1
  choose m hm using hc
  refine ⟨m, fun a ha => ?_⟩
  set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => Formalism.L2.Pj.archM V (θ τ) a with hu_def
  have hu : u ∈ GlobalTheory.HolDict.UG (gramAt D V) := hLarch a
  have hz0 : ∀ b ∈ GinfC V, z b ≠ 0 := fun b hb h0 => by
    have := hz1 b hb
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hone : (1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D V) :=
    fun τ => GlobalTheory.UCharDet.one_mem _
  have zL1 : z (L 1) = 1 := by
    have e1 : L 1 = L 1 * L 1 := by simpa using hLmul 1 hone 1 hone
    have m1 := (hL1 _ hone).1
    have e2 := hz _ m1 _ m1
    rw [← e1] at e2
    exact (mul_eq_left₀ (hz0 _ m1)).1 e2.symm
  let fam : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun s τ => if τ ∈ s then u τ else 1
  have hfam : ∀ s, fam s ∈ GlobalTheory.HolDict.UG (gramAt D V) := fun s τ => by
    simp only [fam]
    split_ifs
    · exact hu τ
    · exact GlobalTheory.UCharDet.one_mem _
  have key : ∀ s : Finset D.what₂.Tau, z (L (fam s)) = ∏ τ ∈ s, (u τ).det ^ m τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : fam ∅ = 1 := funext fun τ => by simp [fam]
      rw [this, Finset.prod_empty]
      exact zL1
    | insert b s hb ih =>
      have e : fam (insert b s) = Pi.mulSingle b (u b) * fam s := funext fun τ => by
        by_cases h : τ = b
        · subst h
          simp [fam, hb]
        · simp [fam, h]
      rw [e, hLmul _ (hsing b _ (hu b)) _ (hfam s), hz _ (hL1 _ (hsing b _ (hu b))).1 _ (hL1 _ (hfam s)).1,
        hm b _ (hu b), ih, Finset.prod_insert hb]
  have hall : fam Finset.univ = u := funext fun τ => by simp [fam]
  have := key Finset.univ
  rw [hall, hLinv a ha] at this
  rw [this]
  rfl

end GlobalTheory.AdSpan
