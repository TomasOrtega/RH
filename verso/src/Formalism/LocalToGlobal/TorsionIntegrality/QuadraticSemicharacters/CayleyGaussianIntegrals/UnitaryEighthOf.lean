import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace Cay

section Det

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv, hM⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`. Establish `hHw : H (∑ i, v i • e i) = 0`. Apply `e.ext` to reduce the goal to its premises. Introduce `j`.

Establish `h` using `congrFun hM j`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]`. Conclude with `h`. Establish `hw0 : (∑ i, v i • e i) ≠ 0`.

Introduce `h0`. Conclude with `hv (funext fun i => Fintype.linearIndependent_iff.1 e.linearIndependent v h0 i)`. Establish `h` using `hpos _ hw0`. Rewrite `h` using `[hHw, LinearMap.zero_apply, Complex.zero_re]`. Conclude with `lt_irrefl _ h`.
-/
theorem gram_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (H : Sesq V) (hpos : IsPosDef H)
    (e : Module.Basis ι ℂ V) : (Matrix.of fun i j => H (e i) (e j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hHw : H (∑ i, v i • e i) = 0 := by
    apply e.ext
    intro j
    have h := congrFun hM j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    exact h
  have hw0 : (∑ i, v i • e i) ≠ 0 := by
    intro h0
    exact hv (funext fun i => Fintype.linearIndependent_iff.1 e.linearIndependent v h0 i)
  have h := hpos _ hw0
  rw [hHw, LinearMap.zero_apply, Complex.zero_re] at h
  exact lt_irrefl _ h

/- English proof (translation)
Set `e` to `Module.finBasis ℂ V`. Establish `hG` using `gram_det_ne_zero H hpos e`. Establish `hfe : ∀ (g : V →ₗ[ℂ] V) j, g (e j) = ∑ k, LinearMap.toMatrix e e g k j • e k` using `fun g j => by`. Simplify using `only [LinearMap.toMatrix_apply]`. Conclude with `(e.sum_repr (g (e j))).symm`.

Establish `hmat : (LinearMap.toMatrix e e f).transpose * (Matrix.of fun i j => H (e i) (e j)) = (Matrix.of fun i j => H (e i) (e j)) * (LinearMap.toMatrix e e f').map (starRingEnd ℂ)`. Use extensionality with `i j`. Establish `h1` using `h (e i) (e j)`. Rewrite `h1` using `[hfe f i, hfe f' j]`. Simplify using `only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]`. Conclude with `h1.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)`. Establish `hc : ((LinearMap.toMatrix e e f').map (starRingEnd ℂ)).det = starRingEnd ℂ (LinearMap.toMatrix e e f').det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Establish `hdet` using `congrArg Matrix.det hmat`.

Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]`. Rewrite using `[← LinearMap.det_toMatrix e f, ← LinearMap.det_toMatrix e f']`. Conclude with `mul_right_cancel₀ hG (hdet.trans (mul_comm _ _))`.
-/
theorem det_adj (H : Sesq V) (hpos : IsPosDef H) (f f' : V →ₗ[ℂ] V) (h : ∀ x y, H (f x) y = H x (f' y)) :
    LinearMap.det f = conj (LinearMap.det f') := by
  classical
  let e := Module.finBasis ℂ V
  have hG := gram_det_ne_zero H hpos e
  have hfe : ∀ (g : V →ₗ[ℂ] V) j, g (e j) = ∑ k, LinearMap.toMatrix e e g k j • e k := fun g j => by
    simp only [LinearMap.toMatrix_apply]; exact (e.sum_repr (g (e j))).symm
  have hmat : (LinearMap.toMatrix e e f).transpose * (Matrix.of fun i j => H (e i) (e j))
      = (Matrix.of fun i j => H (e i) (e j)) * (LinearMap.toMatrix e e f').map (starRingEnd ℂ) := by
    ext i j
    have h1 := h (e i) (e j)
    rw [hfe f i, hfe f' j] at h1
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]
    exact h1.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)
  have hc : ((LinearMap.toMatrix e e f').map (starRingEnd ℂ)).det
      = starRingEnd ℂ (LinearMap.toMatrix e e f').det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc] at hdet
  rw [← LinearMap.det_toMatrix e f, ← LinearMap.det_toMatrix e f']
  exact mul_right_cancel₀ hG (hdet.trans (mul_comm _ _))

end Det

end Cay

/- English proof (translation)
Introduce `V _ _ _ H hH hpos δ Ae hI hA`. Establish `hi : ∀ a b, H (δ a) (δ b) = H a b` using `fun a b => hI a b`. Establish `hadj : ∀ x y, H ((Ae : V →ₗ[ℂ] V) x) y = H x (((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) y)`. Introduce `x y`. Take `⟨x, rfl⟩ : ∃ x', x = δ x'` from `⟨δ.symm x, by simp⟩`.

Simplify using `only [LinearEquiv.coe_coe, hA, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hi]`. Establish `h1` using `Cay.det_adj H hpos _ _ hadj`. Establish `h2 : ((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) = ((-1 : ℂ) • (δ : V →ₗ[ℂ] V)) ∘ₗ (Ae : V →ₗ[ℂ] V)`. Use extensionality with `x`. Simplify using `[hA]`.

Use `conv_lhs => rw [h1, Complex.conj_conj, h2, LinearMap.det_comp, LinearMap.det_smul]`.
-/
theorem cayleyDet : DetCayley := by
  intro V _ _ _ H hH hpos δ Ae hI hA
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hI a b
  have hadj : ∀ x y, H ((Ae : V →ₗ[ℂ] V) x) y = H x (((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) y) := by
    intro x y
    obtain ⟨x, rfl⟩ : ∃ x', x = δ x' := ⟨δ.symm x, by simp⟩
    simp only [LinearEquiv.coe_coe, hA, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, hi]
  have h1 := Cay.det_adj H hpos _ _ hadj
  have h2 : ((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) = ((-1 : ℂ) • (δ : V →ₗ[ℂ] V)) ∘ₗ (Ae : V →ₗ[ℂ] V) := by
    ext x
    simp [hA]
  conv_lhs => rw [h1, Complex.conj_conj, h2, LinearMap.det_comp, LinearMap.det_smul]

namespace Cay

/- English proof (translation)
Establish `hi : ∀ a b, H (δ a) (δ b) = H a b` using `fun a b => hδ a b`. Unfold `IsSelfDual at hΛ ⊢`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hx' : ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H x y = m` using `hx`. Rewrite using `[imgLat, AddSubgroup.mem_map]`. Use `⟨δ.symm x, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← hΛ]`. Use `show ∀ y ∈ Λ, ∃ m : ℤ, altE H (δ.symm x) y = m`.

Introduce `y hy`. Take `⟨m, hm⟩` from `hx' (δ y) (by rw [imgLat, AddSubgroup.mem_map]; exact ⟨y, hy, rfl⟩)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `e` using `hi (δ.symm x) y`. Rewrite `e` using `[LinearEquiv.apply_symm_apply]`.

Use `show (H (δ.symm x) y).im = m`. Rewrite using `[← e]`. Conclude with `hm`. Introduce `hx`. Rewrite `hx` using `[imgLat, AddSubgroup.mem_map]`.

Take `⟨a, ha, rfl⟩` from `hx`. Rewrite `ha` using `[← hΛ]`. Establish `ha' : ∀ y ∈ Λ, ∃ m : ℤ, altE H a y = m` using `ha`. Use `show ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H (δ a) y = m`. Introduce `y hy`.

Rewrite `hy` using `[imgLat, AddSubgroup.mem_map]`. Take `⟨b, hb, rfl⟩` from `hy`. Take `⟨m, hm⟩` from `ha' b hb`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `show (H (δ a) (δ b)).im = m`.

Rewrite using `[hi]`. Conclude with `hm`.
-/
theorem selfDual_img {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (δ : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hΛ : IsSelfDual H Λ) :
    IsSelfDual H (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hδ a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  constructor
  · intro hx
    have hx' : ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H x y = m := hx
    rw [imgLat, AddSubgroup.mem_map]
    refine ⟨δ.symm x, ?_, by simp⟩
    rw [← hΛ]
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H (δ.symm x) y = m
    intro y hy
    obtain ⟨m, hm⟩ := hx' (δ y) (by rw [imgLat, AddSubgroup.mem_map]; exact ⟨y, hy, rfl⟩)
    refine ⟨m, ?_⟩
    have e := hi (δ.symm x) y
    rw [LinearEquiv.apply_symm_apply] at e
    show (H (δ.symm x) y).im = m
    rw [← e]; exact hm
  · intro hx
    rw [imgLat, AddSubgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← hΛ] at ha
    have ha' : ∀ y ∈ Λ, ∃ m : ℤ, altE H a y = m := ha
    show ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H (δ a) y = m
    intro y hy
    rw [imgLat, AddSubgroup.mem_map] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨m, hm⟩ := ha' b hb
    refine ⟨m, ?_⟩
    show (H (δ a) (δ b)).im = m
    rw [hi]; exact hm

end Cay

/- English proof (translation)
Introduce `V _ _ _ H Λ α δ Ae hL hU hAML θ hθ hθ0 c hc`. Establish `hd : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0` using `(LinearEquiv.isUnit_det' Ae).ne_zero`. Take `⟨_, hidx⟩` from `hI V H Λ α δ Ae hL hU`. Establish `hne : relIdx (latA Λ δ Ae) Λ ≠ 0`. Introduce `h0`.

Rewrite `hidx` using `[h0, Nat.cast_zero]`. Establish `h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0` using `by exact_mod_cast hU.idx₁`. Conclude with `mul_ne_zero h1 (pow_ne_zero _ (norm_ne_zero_iff.2 hd)) hidx.symm`. Take `⟨S, hS⟩` from `(cosetRepsExist V (latA Λ δ Ae) Λ hne).1`. Establish `hc'` using `hC V H Λ α δ Ae hL hU hAML S hS θ hθ`.

Establish `hg` using `hG V H Λ α δ Ae hU S hS`. Establish `hI0 : inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ ≠ 0`. Introduce `h0`. Rewrite `hc` using `[h0, smul_zero]`. Apply `hθ0` to reduce the goal to its premises.

Use function extensionality and compare the values at `z`. Establish `h1` using `congrFun hc (δ z)`. Simplify `h1` using `[pullInv]`. Establish `hceq : c = (‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V) * gaussC H α Ae S` using `smul_left_injective ℂ hI0 (hc.symm.trans hc')`. Establish `hdc` using `cayleyDet V H hU.herm hU.pos δ Ae hU.isom hU.cay`.

Rewrite using `[hceq, mul_pow, hg, mul_one, div_pow]`. Generalize the expression as in `LinearMap.det (Ae : V →ₗ[ℂ] V) = d at *`. Generalize the expression as in `LinearMap.det (δ : V →ₗ[ℂ] V) = D at *`. Establish `hn2 : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]`.

Establish `hs : ((-1 : ℂ) ^ Module.finrank ℂ V) ^ 4 = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul]`. Evaluate the numerical expressions. Rewrite using `[show ((‖d‖ : ℝ) : ℂ) ^ 8 = (((‖d‖ : ℝ) : ℂ) ^ 2) ^ 4 by ring, hn2, hdc, div_eq_iff (pow_ne_zero _ hd)]`. Take the linear combination `(D ^ 4 * d ^ 8) * hs`.
-/
theorem UnitaryEighth_of (hC : UnitaryConstant) (hG : UnitaryGauss) (hI : UnitaryIndex) : UnitaryEighth := by
  intro V _ _ _ H Λ α δ Ae hL hU hAML θ hθ hθ0 c hc
  have hd : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  obtain ⟨_, hidx⟩ := hI V H Λ α δ Ae hL hU
  have hne : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
    exact mul_ne_zero h1 (pow_ne_zero _ (norm_ne_zero_iff.2 hd)) hidx.symm
  obtain ⟨S, hS⟩ := (cosetRepsExist V (latA Λ δ Ae) Λ hne).1
  have hc' := hC V H Λ α δ Ae hL hU hAML S hS θ hθ
  have hg := hG V H Λ α δ Ae hU S hS
  have hI0 : inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hc
    apply hθ0
    funext z
    have h1 := congrFun hc (δ z)
    simpa [pullInv] using h1
  have hceq : c = (‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
      * gaussC H α Ae S := smul_left_injective ℂ hI0 (hc.symm.trans hc')
  have hdc := cayleyDet V H hU.herm hU.pos δ Ae hU.isom hU.cay
  rw [hceq, mul_pow, hg, mul_one, div_pow]
  generalize LinearMap.det (Ae : V →ₗ[ℂ] V) = d at *
  generalize LinearMap.det (δ : V →ₗ[ℂ] V) = D at *
  have hn2 : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hs : ((-1 : ℂ) ^ Module.finrank ℂ V) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [show ((‖d‖ : ℝ) : ℂ) ^ 8 = (((‖d‖ : ℝ) : ℂ) ^ 2) ^ 4 by ring, hn2, hdc, div_eq_iff (pow_ne_zero _ hd)]
  linear_combination (D ^ 4 * d ^ 8) * hs

end Formalism.L2.Th1.H
