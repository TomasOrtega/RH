import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable

noncomputable section

namespace GlobalTheory.LieFock

section Abstract

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Real ComplexConjugate

/- English proof (translation)
Establish `hd : ∀ (c : ℂ) u, d (c • u) = (c.re : ℂ) • d u + (c.im : ℂ) • d (I • u)` using `fun c u => by`. Rewrite using `[← hs, ← hs, ← ha, smul_smul, ← add_smul, re_add_im]`. Establish `hd' : ∀ (c : ℂ) u, d (I • c • u) = (-c.im : ℂ) • d u + (c.re : ℂ) • d (I • u)` using `fun c u => by`. Rewrite using `[smul_smul, hd]`. Simplify using the standard rewrite rules.

Establish `h1 : ∀ u v : ι → ℂ, star v ⬝ᵥ H *ᵥ (I • u) = I * (star v ⬝ᵥ H *ᵥ u)` using `fun u v => by`. Rewrite using `[mulVec_smul, dotProduct_smul, smul_eq_mul]`. Establish `h2 : ∀ u v : ι → ℂ, star (I • v) ⬝ᵥ H *ᵥ u = -I * (star v ⬝ᵥ H *ᵥ u)` using `fun u v => by`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul, star_def, conj_I]`. Use `⟨⟨⟨fun v => d v - I • d (I • v), fun u v => ?_⟩, fun c v => ?_⟩, ⟨⟨fun v => d v + I • d (I • v), fun u v => ?_⟩, fun c v => ?_⟩, fun _ => rfl, fun _ => rfl, fun u v => ?_, fun u v => ?_, fun u v => ?_⟩` and prove the remaining obligations.

Simplify using `only [smul_add, ha]`. Normalize the expressions using the abelian group laws. Simplify using `only [RingHom.id_apply]`. Rewrite using `[hd', hd c]`. Use `match_scalars`.

Take the linear combination `re_add_im c`. Take the linear combination `(-I) * re_add_im c + (c.im : ℂ) * I_mul_I`. Simplify using `only [smul_add, ha]`. Normalize the expressions using the abelian group laws. Apply the tactic sequence `have e : conj c = c.re - c.im * I := by apply Complex.ext <;> simp`.

Simplify using `only`. Rewrite using `[hd', hd c, e]`. Use `match_scalars`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(c.im : ℂ) * I_mul_I`.

Use `all_goals`. Simplify using `only [LinearMap.coe_mk, AddHom.coe_mk, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm]`. Rewrite using `[hc u v, hc u (I • v), hc (I • u) v, hc (I • u) (I • v)]`. Simplify using `only [h1, h2]`. Generalize the expression as in `star v ⬝ᵥ H *ᵥ u = h`.

Apply the tactic sequence `have e : conj h = h.re - h.im * I := by apply Complex.ext <;> simp`. Simplify using `only [e, mul_im, mul_re, neg_re, neg_im, I_re, I_im]`. Use `match_scalars`. Apply the tactic sequence `all_goals first | ring1 | (ring_nf; simp only [I_sq, I_pow_three]; ring1)`.
-/
theorem exists_parts {ι A : Type} [Fintype ι] [Ring A] [Algebra ℂ A] (H : Matrix ι ι ℂ) (d : (ι → ℂ) → A)
    (ha : ∀ u v, d (u + v) = d u + d v) (hs : ∀ (r : ℝ) u, d ((r : ℂ) • u) = (r : ℂ) • d u)
    (hc : ∀ u v, d u * d v = d v * d u + (2 * π * I * ((star v ⬝ᵥ H *ᵥ u).im : ℂ)) • (1 : A)) :
    ∃ (x : (ι → ℂ) →ₗ[ℂ] A) (y : (ι → ℂ) →ₛₗ[starRingEnd ℂ] A), (∀ v, x v = d v - I • d (I • v)) ∧
      (∀ v, y v = d v + I • d (I • v)) ∧ (∀ u v, x u * x v = x v * x u) ∧ (∀ u v, y u * y v = y v * y u) ∧
      ∀ u v, y u * x v = x v * y u + (-(4 * π) * conj (star v ⬝ᵥ H *ᵥ u)) • (1 : A) := by
  have hd : ∀ (c : ℂ) u, d (c • u) = (c.re : ℂ) • d u + (c.im : ℂ) • d (I • u) := fun c u => by
    rw [← hs, ← hs, ← ha, smul_smul, ← add_smul, re_add_im]
  have hd' : ∀ (c : ℂ) u, d (I • c • u) = (-c.im : ℂ) • d u + (c.re : ℂ) • d (I • u) := fun c u => by
    rw [smul_smul, hd]
    simp
  have h1 : ∀ u v : ι → ℂ, star v ⬝ᵥ H *ᵥ (I • u) = I * (star v ⬝ᵥ H *ᵥ u) := fun u v => by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : ∀ u v : ι → ℂ, star (I • v) ⬝ᵥ H *ᵥ u = -I * (star v ⬝ᵥ H *ᵥ u) := fun u v => by
    rw [star_smul, smul_dotProduct, smul_eq_mul, star_def, conj_I]
  refine ⟨⟨⟨fun v => d v - I • d (I • v), fun u v => ?_⟩, fun c v => ?_⟩,
    ⟨⟨fun v => d v + I • d (I • v), fun u v => ?_⟩, fun c v => ?_⟩, fun _ => rfl, fun _ => rfl, fun u v => ?_,
    fun u v => ?_, fun u v => ?_⟩
  · simp only [smul_add, ha]
    abel
  · simp only [RingHom.id_apply]
    rw [hd', hd c]
    match_scalars
    · linear_combination re_add_im c
    · linear_combination (-I) * re_add_im c + (c.im : ℂ) * I_mul_I
  · simp only [smul_add, ha]
    abel
  · have e : conj c = c.re - c.im * I := by apply Complex.ext <;> simp
    simp only
    rw [hd', hd c, e]
    match_scalars
    · ring
    · linear_combination (c.im : ℂ) * I_mul_I
  all_goals
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    rw [hc u v, hc u (I • v), hc (I • u) v, hc (I • u) (I • v)]
    simp only [h1, h2]
    generalize star v ⬝ᵥ H *ᵥ u = h
    have e : conj h = h.re - h.im * I := by apply Complex.ext <;> simp
    simp only [e, mul_im, mul_re, neg_re, neg_im, I_re, I_im]
    match_scalars
    all_goals first | ring1 | (ring_nf; simp only [I_sq, I_pow_three]; ring1)

/- English proof (translation)
Establish `e : ∀ (M : Matrix ι ι ℂ) l, M *ᵥ Pi.single l 1 = ∑ a, M a l • (Pi.single a 1 : ι → ℂ)` using `fun M l => by`. Use function extensionality and compare the values at `b`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `e1 : ∀ l, y ((U * Δ * Uᴴ) *ᵥ Pi.single l 1) = ∑ a, U l a • y ((U * Δ) *ᵥ Pi.single a 1)` using `fun l => by`. Rewrite using `[← mulVec_mulVec, e Uᴴ, mulVec_sum, map_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mulVec_smul, map_smulₛₗ, conjTranspose_apply, star_def, conj_conj]`. Establish `e2 : ∀ k, x (U *ᵥ Pi.single k 1) = ∑ a, U a k • x (Pi.single a 1)` using `fun k => by`. Rewrite using `[e, map_sum]`. Simplify using `only [map_smul]`.

Simplify using `only [e1, e2]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, Finset.mul_sum, mul_smul_comm, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun _ _ => by congr 1; ring`. Use `_ = _ := by`. Rewrite using `[h]`.

Simplify using `only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, Finset.sum_mul, smul_mul_assoc, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by`. Rewrite using `[mul_comm]`.
-/
theorem quad_basis {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (x : (ι → ℂ) →ₗ[ℂ] A)
    (y : (ι → ℂ) →ₛₗ[starRingEnd ℂ] A) (c : ℂ) {U Δ X X' : Matrix ι ι ℂ} (h : X * U = U * X') :
    ∑ k, ∑ l, X k l • (x (Pi.single k 1) * c • y ((U * Δ * Uᴴ) *ᵥ Pi.single l 1)) =
      ∑ k, ∑ l, X' k l • (x (U *ᵥ Pi.single k 1) * c • y ((U * Δ) *ᵥ Pi.single l 1)) := by
  have e : ∀ (M : Matrix ι ι ℂ) l, M *ᵥ Pi.single l 1 = ∑ a, M a l • (Pi.single a 1 : ι → ℂ) := fun M l => by
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  have e1 : ∀ l, y ((U * Δ * Uᴴ) *ᵥ Pi.single l 1) = ∑ a, U l a • y ((U * Δ) *ᵥ Pi.single a 1) := fun l => by
    rw [← mulVec_mulVec, e Uᴴ, mulVec_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mulVec_smul, map_smulₛₗ, conjTranspose_apply, star_def, conj_conj]
  have e2 : ∀ k, x (U *ᵥ Pi.single k 1) = ∑ a, U a k • x (Pi.single a 1) := fun k => by
    rw [e, map_sum]
    simp only [map_smul]
  simp only [e1, e2]
  calc _ = ∑ k, ∑ a, (X * U) k a • (x (Pi.single k 1) * c • y ((U * Δ) *ᵥ Pi.single a 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, Finset.mul_sum, mul_smul_comm, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.sum_mul, Finset.sum_smul]
        exact Finset.sum_congr rfl fun _ _ => by congr 1; ring
    _ = _ := by
        rw [h]
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, Finset.sum_mul, smul_mul_assoc, smul_smul]
        rw [Finset.sum_comm]
        refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
          rw [mul_comm]

/- English proof (translation)
Use `choose d₀ hd₀ using hk`. Set `d : (ι → ℂ) → Module.End ℂ Θ` to `fun v => { toFun := d₀ v map_add' := fun f g => hJ (by rw [map_add, hd₀, hd₀, hd₀, map_add, dH_add v (hs f) (hs g)]) map_smul' := fun c f => hJ (by rw [RingHom.id_apply, map_smul, hd₀, hd₀, map_smul, dH_smul v c (hs f)]) }`. Establish `hd : ∀ v f, J (d v f) = dH ρ v (J f)` using `hd₀`. Use `clear_value d`. Take `⟨om, hom⟩` from `Ccr.exists_om H`.

Establish `hρ' : IsHeis (fun x y => om x y) ρ` using `by simpa only [hom] using hρ`. Establish `C` using `DCalc.dH_calculus _ B om ρ (fun x => by rw [hom, Ccr.im_self hH]) hρ'`. Establish `hsm : ∀ (r : ℝ) u, d ((r : ℂ) • u) = (r : ℂ) • d u` using `fun r u => LinearMap.ext fun f => hJ (by`. Rewrite using `[LinearMap.smul_apply, map_smul, hd, hd, Complex.coe_smul, Complex.coe_smul, dH_smul_left])`. Take `⟨x, y, hx, hy, c1, c2, c3⟩` from `exists_parts H d (fun u v => LinearMap.ext fun f => hJ (by rw [LinearMap.add_apply, map_add, hd, hd, hd, dH_add_left])) hsm (fun u v => LinearMap.ext fun f => hJ (by`.

Use `(C _ (hs f)).2.2.2.2 u v` as an intermediate fact. Rewrite `this` using `[sub_eq_iff_eq_add', hom]`. Simplify `this))` using `only [LinearMap.add_apply, map_add, Module.End.mul_apply, hd, LinearMap.smul_apply, map_smul, Module.End.one_apply]`. Use `⟨d, x, y, hd, fun v => by simpa using hsm (-1) v, hx, hy, c1, c2, c3, fun X f => ?_⟩` and prove the remaining obligations. Simplify using `only [nOp, xOp, dOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, hx, hy, LinearMap.sub_apply, LinearMap.add_apply]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [← hd, ← map_smul, ← map_add, ← map_sub]`.
-/
theorem exists_der {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B)
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {Θ : Type} [AddCommGroup Θ] [Module ℂ Θ] (J : Θ →ₗ[ℂ] B)
    (hJ : Function.Injective J) (hs : ∀ f, Sm ρ (J f)) (hk : ∀ v f, ∃ g, J g = dH ρ v (J f)) :
    ∃ (d : (ι → ℂ) → Module.End ℂ Θ) (x : (ι → ℂ) →ₗ[ℂ] Module.End ℂ Θ)
      (y : (ι → ℂ) →ₛₗ[starRingEnd ℂ] Module.End ℂ Θ), (∀ v f, J (d v f) = dH ρ v (J f)) ∧ (∀ v, d (-v) = -d v) ∧
      (∀ v, x v = d v - I • d (I • v)) ∧
      (∀ v, y v = d v + I • d (I • v)) ∧ (∀ u v, x u * x v = x v * x u) ∧ (∀ u v, y u * y v = y v * y u) ∧
      (∀ u v, y u * x v = x v * y u + (-(4 * π) * conj (star v ⬝ᵥ H *ᵥ u)) • 1) ∧
      ∀ (X : Matrix ι ι ℂ) f, nOp ρ H X (J f) =
        J ((∑ k, ∑ l, X k l • (x (Pi.single k 1) * (-(1 / (4 * π)) : ℂ) • y (H⁻¹ *ᵥ Pi.single l 1))) f) := by
  choose d₀ hd₀ using hk
  let d : (ι → ℂ) → Module.End ℂ Θ := fun v =>
    { toFun := d₀ v
      map_add' := fun f g => hJ (by rw [map_add, hd₀, hd₀, hd₀, map_add, dH_add v (hs f) (hs g)])
      map_smul' := fun c f => hJ (by rw [RingHom.id_apply, map_smul, hd₀, hd₀, map_smul, dH_smul v c (hs f)]) }
  have hd : ∀ v f, J (d v f) = dH ρ v (J f) := hd₀
  clear_value d
  obtain ⟨om, hom⟩ := Ccr.exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have C := DCalc.dH_calculus _ B om ρ (fun x => by rw [hom, Ccr.im_self hH]) hρ'
  have hsm : ∀ (r : ℝ) u, d ((r : ℂ) • u) = (r : ℂ) • d u := fun r u => LinearMap.ext fun f => hJ (by
    rw [LinearMap.smul_apply, map_smul, hd, hd, Complex.coe_smul, Complex.coe_smul, dH_smul_left])
  obtain ⟨x, y, hx, hy, c1, c2, c3⟩ := exists_parts H d
    (fun u v => LinearMap.ext fun f => hJ (by rw [LinearMap.add_apply, map_add, hd, hd, hd, dH_add_left])) hsm
    (fun u v => LinearMap.ext fun f => hJ (by
      have := (C _ (hs f)).2.2.2.2 u v
      rw [sub_eq_iff_eq_add', hom] at this
      simpa only [LinearMap.add_apply, map_add, Module.End.mul_apply, hd, LinearMap.smul_apply, map_smul,
        Module.End.one_apply] using this))
  refine ⟨d, x, y, hd, fun v => by simpa using hsm (-1) v, hx, hy, c1, c2, c3, fun X f => ?_⟩
  simp only [nOp, xOp, dOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, hx, hy,
    LinearMap.sub_apply, LinearMap.add_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [← hd, ← map_smul, ← map_add, ← map_sub]

/- English proof (translation)
Establish `c4 : ∀ k l, k ≠ l → y k * x l = x l * y k` using `fun k l h => by rw [c3, if_neg h, zero_smul, add_zero]`. Use `⟨fun k l => ?_, fun k l => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : k = l`. Rewrite using `[h]`. Simplify using `only [ha, smul_mul_assoc, mul_smul_comm]`.

Rewrite using `[smul_comm]`. Use `split_ifs`. Rewrite using `[c1]`. Rewrite using `[c4 l k (Ne.symm h)]`. Rewrite using `[c4 k l h]`.

Rewrite using `[c2]`. Simplify using `only [ha, hb, smul_mul_assoc, mul_smul_comm]`. Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Use `hs k` as an intermediate fact.

Establish `e` using `c3 k k`. Simplify using `only [eq_self, if_true] at e ⊢`. Use `split_ifs at e ⊢`. Apply the tactic sequence `rw [e] match_scalars <;> field_simp`. Apply the tactic sequence `rw [e] match_scalars <;> field_simp <;> ring`.

Rewrite using `[if_neg h, zero_smul, add_zero, smul_comm] split_ifs`. Rewrite using `[c4 k l h]`. Rewrite using `[c2]`. Rewrite using `[c1]`. Rewrite using `[c4 l k (Ne.symm h)]`.
-/
theorem ccr_of_sign {κ A : Type} [DecidableEq κ] [Ring A] [Algebra ℂ A] (x y : κ → A) (p : κ → Prop) [DecidablePred p]
    (s : κ → ℂ) (hs : ∀ k, s k ≠ 0) (c1 : ∀ k l, x k * x l = x l * x k) (c2 : ∀ k l, y k * y l = y l * y k)
    (c3 : ∀ k l, y k * x l = x l * y k + (if k = l then -(s k * s k) * (if p k then 1 else -1) else 0 : ℂ) • 1)
    {a b : κ → A} (ha : ∀ k, a k = (s k)⁻¹ • if p k then x k else y k)
    (hb : ∀ k, b k = -(s k)⁻¹ • if p k then y k else x k) :
    (∀ k l, a k * a l = a l * a k) ∧ ∀ k l, b k * a l = a l * b k + (if k = l then (1 : ℂ) else 0) • 1 := by
  have c4 : ∀ k l, k ≠ l → y k * x l = x l * y k := fun k l h => by rw [c3, if_neg h, zero_smul, add_zero]
  refine ⟨fun k l => ?_, fun k l => ?_⟩
  · by_cases h : k = l
    · rw [h]
    simp only [ha, smul_mul_assoc, mul_smul_comm]
    rw [smul_comm]
    split_ifs
    · rw [c1]
    · rw [c4 l k (Ne.symm h)]
    · rw [c4 k l h]
    · rw [c2]
  · simp only [ha, hb, smul_mul_assoc, mul_smul_comm]
    by_cases h : k = l
    · subst h
      have := hs k
      have e := c3 k k
      simp only [eq_self, if_true] at e ⊢
      split_ifs at e ⊢
      · rw [e]
        match_scalars <;> field_simp
      · rw [e]
        match_scalars <;> field_simp <;> ring
    · rw [if_neg h, zero_smul, add_zero, smul_comm]
      split_ifs
      · rw [c4 k l h]
      · rw [c2]
      · rw [c1]
      · rw [c4 l k (Ne.symm h)]

open Formalism.IndefR.Datum in

/- English proof (translation)
Establish `h1 : ∀ i g, g ∈ M → A i g ∈ M` using `fun i g hg => by rw [hA i ⟨g, hg⟩]; exact Subtype.prop _`. Establish `hm` using `GlobalTheory.FockIndep.pure_mem (P := (· ∈ M)) (fun _ _ => add_mem) (fun c _ => M.smul_mem c) h1 f.2`. Establish `hX` using `GlobalTheory.FockIndep.pure_X_mul (P := (· ∈ M)) (fun _ _ => add_mem) (fun c _ => M.smul_mem c) h1 (fun i j g hg => by`. Rewrite using `[hA j ⟨g, hg⟩, hA i ⟨g, hg⟩, hA, hA]`. Conclude with `congrArg Subtype.val (LinearMap.congr_fun (haa i j) ⟨g, hg⟩))`.

Use the proof step `(fun i g g' hg hg' => by`. Rewrite using `[hA i ⟨g, hg⟩, hA i ⟨g', hg'⟩, ← Submodule.coe_add, ← map_add, ← hA]`. Use the proof step `rfl)`. Use the proof step `(fun i c g hg => by rw [hA i ⟨g, hg⟩, ← Submodule.coe_smul, ← map_smul, ← hA]; rfl) f.2`. Set `E : MvPolynomial ι ℂ →ₗ[ℂ] M` to `(pureTensorL A (f : X → ℂ)).codRestrict M hm`.

Establish `hE : ∀ v Q, E (MvPolynomial.X v * Q) = a v (E Q)` using `fun v Q => Subtype.ext ((hX Q v).trans (hA v (E Q)))`. Establish `h0 : E 1 = f` using `Subtype.ext (GlobalTheory.FockIndep.pure_one _)`. Use `⟨E, fun _ => rfl, hE, fun i Q => Eq.symm ?_⟩` and prove the remaining obligations. Use `clear_value E`. Proceed by induction on `Q using MvPolynomial.induction_on with`.

Consider the case `C r => rw [MvPolynomial.pderiv_C, map_zero, MvPolynomial.C_eq_smul_one, map_smul, map_smul, h0, hf, smul_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p j hp`. Rewrite using `[mul_comm, hE, ← Module.End.mul_apply, hba, LinearMap.add_apply, Module.End.mul_apply, hp, MvPolynomial.pderiv_mul, map_add, hE, add_comm]`. Use `congr 1`.

Use `split_ifs with h`. Rewrite using `[h, MvPolynomial.pderiv_X_self, one_mul, one_smul, Module.End.one_apply]`. Rewrite using `[MvPolynomial.pderiv_X_of_ne (Ne.symm h), zero_mul, map_zero, zero_smul, LinearMap.zero_apply]`.
-/
theorem exists_lift {ι X : Type} [DecidableEq ι] (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a b : ι → Module.End ℂ M) (hA : ∀ i (g : M), A i g = a i g) (haa : ∀ i j, a i * a j = a j * a i)
    (hba : ∀ i j, b i * a j = a j * b i + (if i = j then (1 : ℂ) else 0) • 1) (f : M) (hf : ∀ i, b i f = 0) :
    ∃ E : MvPolynomial ι ℂ →ₗ[ℂ] M, (∀ Q, pureTensorL A (f : X → ℂ) Q = E Q) ∧
      (∀ v Q, E (MvPolynomial.X v * Q) = a v (E Q)) ∧ ∀ v Q, E (MvPolynomial.pderiv v Q) = b v (E Q) := by
  have h1 : ∀ i g, g ∈ M → A i g ∈ M := fun i g hg => by rw [hA i ⟨g, hg⟩]; exact Subtype.prop _
  have hm := GlobalTheory.FockIndep.pure_mem (P := (· ∈ M)) (fun _ _ => add_mem) (fun c _ => M.smul_mem c) h1 f.2
  have hX := GlobalTheory.FockIndep.pure_X_mul (P := (· ∈ M)) (fun _ _ => add_mem) (fun c _ => M.smul_mem c) h1
    (fun i j g hg => by
      rw [hA j ⟨g, hg⟩, hA i ⟨g, hg⟩, hA, hA]
      exact congrArg Subtype.val (LinearMap.congr_fun (haa i j) ⟨g, hg⟩))
    (fun i g g' hg hg' => by
      rw [hA i ⟨g, hg⟩, hA i ⟨g', hg'⟩, ← Submodule.coe_add, ← map_add, ← hA]; rfl)
    (fun i c g hg => by rw [hA i ⟨g, hg⟩, ← Submodule.coe_smul, ← map_smul, ← hA]; rfl) f.2
  let E : MvPolynomial ι ℂ →ₗ[ℂ] M := (pureTensorL A (f : X → ℂ)).codRestrict M hm
  have hE : ∀ v Q, E (MvPolynomial.X v * Q) = a v (E Q) := fun v Q => Subtype.ext ((hX Q v).trans (hA v (E Q)))
  have h0 : E 1 = f := Subtype.ext (GlobalTheory.FockIndep.pure_one _)
  refine ⟨E, fun _ => rfl, hE, fun i Q => Eq.symm ?_⟩
  clear_value E
  induction Q using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.pderiv_C, map_zero, MvPolynomial.C_eq_smul_one, map_smul, map_smul, h0, hf, smul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [mul_comm, hE, ← Module.End.mul_apply, hba, LinearMap.add_apply, Module.End.mul_apply, hp,
      MvPolynomial.pderiv_mul, map_add, hE, add_comm]
    congr 1
    split_ifs with h
    · rw [h, MvPolynomial.pderiv_X_self, one_mul, one_smul, Module.End.one_apply]
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), zero_mul, map_zero, zero_smul, LinearMap.zero_apply]

end Abstract

section Mat

open Matrix GlobalTheory.RealWeil GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `⟨⟨i, j⟩, t⟩`. Establish `e` using `congrFun (congrFun (cpt_blk b a (vecL (Pi.single τ u : O → Matrix (Fin m) (Fin n) ℂ)) t) i) j`. Establish `e' : ∀ y : O → Matrix (Fin m) (Fin n) ℂ, cpt (vecL y) t = y t` using `fun y => rfl`. Rewrite `e` using `[e']`. Use `e.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = (Pi.single τ (b τ * u * a τ) : O → Matrix (Fin m) (Fin n) ℂ) t i j`. Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`. Simplify using `only [Pi.single_eq_of_ne h, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem blk_vecL (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) (τ : O)
    (u : Matrix (Fin m) (Fin n) ℂ) :
    blk b a *ᵥ vecL (Pi.single τ u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ (b τ * u * a τ) : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext ⟨⟨i, j⟩, t⟩
  have e := congrFun (congrFun (cpt_blk b a (vecL (Pi.single τ u : O → Matrix (Fin m) (Fin n) ℂ)) t) i) j
  have e' : ∀ y : O → Matrix (Fin m) (Fin n) ℂ, cpt (vecL y) t = y t := fun y => rfl
  rw [e'] at e
  refine e.trans ?_
  change _ = (Pi.single τ (b τ * u * a τ) : O → Matrix (Fin m) (Fin n) ℂ) t i j
  by_cases h : t = τ
  · subst h
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype O] in
/- English proof (translation)
Use function extensionality and compare the values at `⟨⟨a, a'⟩, t⟩`. Express the relevant statement in the definitionally equal form `_ = (Pi.single τ (Matrix.single i j 1) : O → Matrix (Fin m) (Fin n) ℂ) t a a'`. Distinguish the cases in `ht : t = τ`. Substitute `ht` using the available equality. Simplify using `[Pi.single_apply, Matrix.single_apply, eq_comm]`.

Simplify using `[ht]`.
-/
theorem single_eq_vecL (τ : O) (i : Fin m) (j : Fin n) : (Pi.single ((i, j), τ) 1 : (Fin m × Fin n) × O → ℂ) =
    vecL (Pi.single τ (Matrix.single i j 1) : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext ⟨⟨a, a'⟩, t⟩
  change _ = (Pi.single τ (Matrix.single i j 1) : O → Matrix (Fin m) (Fin n) ℂ) t a a'
  by_cases ht : t = τ
  · subst ht
    simp [Pi.single_apply, Matrix.single_apply, eq_comm]
  · simp [ht]

omit [Fintype O] in
/- English proof (translation)
Rewrite using `[Pi.single_smul']`. Both sides reduce to the same expression.
-/
theorem vecL_smul (τ : O) (c : ℂ) (u : Matrix (Fin m) (Fin n) ℂ) :
    vecL (Pi.single τ (c • u) : O → Matrix (Fin m) (Fin n) ℂ) =
      c • vecL (Pi.single τ u : O → Matrix (Fin m) (Fin n) ℂ) := by
  rw [Pi.single_smul']
  rfl

omit [Fintype O] in
/- English proof (translation)
Use extensionality with `⟨⟨i, j⟩, t⟩ ⟨⟨i', j'⟩, t'⟩`. Rewrite using `[GlobalTheory.Mem.Lift.WeylAction.blk_apply]`. Simplify using `only [diagonal_apply, Prod.mk.injEq]`. Apply the tactic sequence `by_cases h1 : t = t' <;> by_cases h2 : i = i' <;> by_cases h3 : j = j' <;> simp [h1, h2, h3, eq_comm]`.
-/
theorem blk_diagonal (b : O → Fin m → ℂ) (a : O → Fin n → ℂ) :
    blk (fun τ => diagonal (b τ)) (fun τ => diagonal (a τ)) = diagonal fun k => b k.2 k.1.1 * a k.2 k.1.2 := by
  ext ⟨⟨i, j⟩, t⟩ ⟨⟨i', j'⟩, t'⟩
  rw [GlobalTheory.Mem.Lift.WeylAction.blk_apply]
  simp only [diagonal_apply, Prod.mk.injEq]
  by_cases h1 : t = t' <;> by_cases h2 : i = i' <;> by_cases h3 : j = j' <;> simp [h1, h2, h3, eq_comm]

/- English proof (translation)
Apply the tactic sequence `cases e <;> simp [sgn]`.
-/
theorem sgn_mul_self (e : Bool) : sgn e * sgn e = 1 := by cases e <;> simp [sgn]

/- English proof (translation)
Apply the tactic sequence `cases e <;> simp [sgn]`.
-/
theorem conj_sgn (e : Bool) : starRingEnd ℂ (sgn e) = sgn e := by cases e <;> simp [sgn]

/- English proof (translation)
Apply the tactic sequence `cases e <;> cases e' <;> simp [sgn]`.
-/
theorem sgn_mul (e e' : Bool) : sgn e * sgn e' = if e = e' then 1 else -1 := by cases e <;> cases e' <;> simp [sgn]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Jm_eq (ε : Fin n → Bool) : Formalism.REAL.Jm ε = diagonal fun a => sgn (ε a) := rfl

/- English proof (translation)
Simplify using `only [Jm_eq, diagonal_mul_diagonal, sgn_mul_self, diagonal_one]`.
-/
theorem Jm_mul_self (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  simp only [Jm_eq, diagonal_mul_diagonal, sgn_mul_self, diagonal_one]

variable {F G X : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool}

/- English proof (translation)
Rewrite using `[← hG, mul_nonsing_inv_cancel_right_gram hF]`. Use `where mul_nonsing_inv_cancel_right_gram {F J : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F.det) : (F⁻¹)ᴴ * (Fᴴ * J * F) * F⁻¹ = J := by`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_onb (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) : (F⁻¹)ᴴ * G * F⁻¹ = Formalism.REAL.Jm ε := by
  rw [← hG, mul_nonsing_inv_cancel_right_gram hF]
where
  mul_nonsing_inv_cancel_right_gram {F J : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F.det) :
      (F⁻¹)ᴴ * (Fᴴ * J * F) * F⁻¹ = J := by
    calc _ = (F * F⁻¹)ᴴ * J * (F * F⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hF, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[← hG, Matrix.mul_assoc F⁻¹, Matrix.mul_assoc _ F, mul_nonsing_inv_cancel_left _ _ hF, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.REAL.Jm ε), Jm_mul_self, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hF, conjTranspose_one]`.
-/
theorem gram_mul (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) :
    G * (F⁻¹ * Formalism.REAL.Jm ε * (F⁻¹)ᴴ) = 1 := by
  rw [← hG, Matrix.mul_assoc F⁻¹, Matrix.mul_assoc _ F, mul_nonsing_inv_cancel_left _ _ hF, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Formalism.REAL.Jm ε), Jm_mul_self, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hF,
    conjTranspose_one]

/- English proof (translation)
Rewrite using `[inv_eq_right_inv (gram_mul hF hG), ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hF, Matrix.one_mul, Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hF, conjTranspose_one, Matrix.mul_one]`.
-/
theorem gram_inv (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) : F * G⁻¹ * Fᴴ = Formalism.REAL.Jm ε := by
  rw [inv_eq_right_inv (gram_mul hF hG), ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hF, Matrix.one_mul,
    Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hF, conjTranspose_one, Matrix.mul_one]

/- English proof (translation)
Establish `e : (F * X * F⁻¹)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (F * X * F⁻¹) = 0`. Establish `h1 : (F⁻¹)ᴴ * Fᴴ = 1` using `by rw [← conjTranspose_mul, mul_nonsing_inv _ hF, conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG, Matrix.mul_add, Matrix.add_mul]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv _ hF, Matrix.mul_one]`.

Rewrite using `[← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h1, Matrix.one_mul]`. Use `_ = _ := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]`. Establish `e'` using `congrFun (congrFun e k) j`. Rewrite `e'` using `[Matrix.add_apply, Jm_eq, mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.zero_apply, Complex.star_def]`. Take the linear combination `sgn (ε j) * e' - starRingEnd ℂ ((F * X * F⁻¹) j k) * sgn_mul_self (ε j)`.
-/
theorem lie_entry (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hX : Xᴴ * G + G * X = 0) (j k : Fin n) :
    starRingEnd ℂ ((F * X * F⁻¹) j k) = -(sgn (ε j) * sgn (ε k)) * (F * X * F⁻¹) k j := by
  have e : (F * X * F⁻¹)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (F * X * F⁻¹) = 0 := by
    have h1 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hF, conjTranspose_one]
    calc _ = (F⁻¹)ᴴ * (Xᴴ * G + G * X) * F⁻¹ := by
          rw [← hG, Matrix.mul_add, Matrix.add_mul]
          simp only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv _ hF, Matrix.mul_one]
          rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h1, Matrix.one_mul]
      _ = _ := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]
  have e' := congrFun (congrFun e k) j
  rw [Matrix.add_apply, Jm_eq, mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.zero_apply, Complex.star_def] at e'
  linear_combination sgn (ε j) * e' - starRingEnd ℂ ((F * X * F⁻¹) j k) * sgn_mul_self (ε j)

end Mat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators Complex
open scoped Classical Real ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} (A : Fr V) (B : Fr W)

/- English proof (translation)
The claim follows from `(isUnit_iff_isUnit_det _).1 (A.fr_unit τ)`.
-/
theorem fr_det (τ : D.what₂.Tau) : IsUnit (A.fr τ).det := (isUnit_iff_isUnit_det _).1 (A.fr_unit τ)

def uM : Matrix (Ix V W) (Ix V W) ℂ := blk (fun τ => (B.fr τ)⁻¹) A.fr

def cc (D : D7) (τ : D.what₂.Tau) : ℂ := ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ)

/- English proof (translation)
Rewrite using `[← blk_diagonal (fun τ i => cc D τ * sgn (B.ε τ i)) fun τ j => sgn (A.ε τ j), uM, HM, blk_conjTranspose, blk_mul, blk_mul]`. Apply the tactic sequence `congr 1 <;> funext τ`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, gram_onb (fr_det B τ) (B.fr_gram τ), Jm_eq, ← diagonal_smul]`. Both sides reduce to the same expression. Rewrite using `[← Matrix.mul_assoc, gram_inv (fr_det A τ) (A.fr_gram τ), Jm_eq]`.
-/
theorem uM_gram : (uM A B)ᴴ * HM V W * uM A B =
    diagonal fun k => cc D k.2 * sgn (B.ε k.2 k.1.1) * sgn (A.ε k.2 k.1.2) := by
  rw [← blk_diagonal (fun τ i => cc D τ * sgn (B.ε τ i)) fun τ j => sgn (A.ε τ j), uM, HM, blk_conjTranspose, blk_mul,
    blk_mul]
  congr 1 <;> funext τ
  · rw [Matrix.mul_smul, Matrix.smul_mul, gram_onb (fr_det B τ) (B.fr_gram τ), Jm_eq, ← diagonal_smul]
    rfl
  · rw [← Matrix.mul_assoc, gram_inv (fr_det A τ) (A.fr_gram τ), Jm_eq]

/- English proof (translation)
Use `inv_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[← blk_diagonal (fun τ i => (cc D τ)⁻¹ * sgn (B.ε τ i)) fun τ j => sgn (A.ε τ j), uM, HM, blk_conjTranspose, blk_mul, blk_mul, blk_mul, ← blk_one]`. Apply the tactic sequence `congr 1 <;> funext τ`. Establish `e : (diagonal fun i => (cc D τ)⁻¹ * sgn (B.ε τ i)) = (cc D τ)⁻¹ • Formalism.REAL.Jm (B.ε τ)`. Rewrite using `[Jm_eq, ← diagonal_smul]`.

Both sides reduce to the same expression. Rewrite using `[e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, gram_mul (fr_det B τ) (B.fr_gram τ), smul_smul]`. Conclude with `(congrArg (· • (1 : Matrix _ _ ℂ)) (mul_inv_cancel₀ (two_im_pos τ).ne')).trans (one_smul _ _)`. Rewrite using `[← Jm_eq, ← Matrix.mul_assoc, A.fr_gram, mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)]`.
-/
theorem HM_inv : (HM V W)⁻¹ = uM A B *
    (diagonal fun k => (cc D k.2)⁻¹ * sgn (B.ε k.2 k.1.1) * sgn (A.ε k.2 k.1.2)) * (uM A B)ᴴ := by
  refine inv_eq_right_inv ?_
  rw [← blk_diagonal (fun τ i => (cc D τ)⁻¹ * sgn (B.ε τ i)) fun τ j => sgn (A.ε τ j), uM, HM, blk_conjTranspose,
    blk_mul, blk_mul, blk_mul, ← blk_one]
  congr 1 <;> funext τ
  · have e : (diagonal fun i => (cc D τ)⁻¹ * sgn (B.ε τ i)) = (cc D τ)⁻¹ • Formalism.REAL.Jm (B.ε τ) := by
      rw [Jm_eq, ← diagonal_smul]
      rfl
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, gram_mul (fr_det B τ) (B.fr_gram τ),
      smul_smul]
    exact (congrArg (· • (1 : Matrix _ _ ℂ)) (mul_inv_cancel₀ (two_im_pos τ).ne')).trans (one_smul _ _)
  · rw [← Jm_eq, ← Matrix.mul_assoc, A.fr_gram, mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)]

/- English proof (translation)
Rewrite using `[single_eq_vecL, uM, blk_vecL, unitMap, Fr.onb, Fr.onb, nonsing_inv_nonsing_inv _ (fr_det A τ)]`.
-/
theorem uM_single (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) : uM A B *ᵥ Pi.single ((i, j), τ) 1 =
    vecL (Pi.single τ (unitMap (A.onb τ) (B.onb τ) i j) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := by
  rw [single_eq_vecL, uM, blk_vecL, unitMap, Fr.onb, Fr.onb, nonsing_inv_nonsing_inv _ (fr_det A τ)]

/- English proof (translation)
Rewrite using `[Fr.cart, Fr.onb, mul_nonsing_inv_cancel_right _ _ (fr_det A τ), Jm_eq]`.
-/
theorem cart_onb (τ : D.what₂.Tau) : A.cart τ * A.onb τ = A.onb τ * diagonal fun a => sgn (A.ε τ a) := by
  rw [Fr.cart, Fr.onb, mul_nonsing_inv_cancel_right _ _ (fr_det A τ), Jm_eq]

/- English proof (translation)
Rewrite using `[GlobalTheory.FockVecInj.cplxO_unitMap (B := A.onb τ) (isUnit_nonsing_inv_det _ (fr_det A τ)) (cart_onb A τ) (cart_onb B τ), sgn_mul, smul_smul, mul_comm]`.
-/
theorem cplxO_unit (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j) =
      (if B.ε τ i = A.ε τ j then (1 : ℂ) else -1) • I • unitMap (A.onb τ) (B.onb τ) i j := by
  rw [GlobalTheory.FockVecInj.cplxO_unitMap (B := A.onb τ) (isUnit_nonsing_inv_det _ (fr_det A τ)) (cart_onb A τ) (cart_onb B τ), sgn_mul,
    smul_smul, mul_comm]

variable {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}

/- English proof (translation)
Set `J : thetaSub ψ V W →ₗ[ℂ] BB ψ V W` to `{ toFun := fun f => toB hψ f.1 f.2 map_add' := fun f g => QB_ext fun x => rfl map_smul' := fun a f => QB_ext fun x => rfl }`. Establish `hc : ∀ f, ((J f).1 : WO V W → ℂ) = f.1` using `fun f => coe_toB hψ f.1 f.2`. Establish `hJ : Function.Injective J` using `fun f g e => Subtype.ext (by rw [← hc, ← hc, e])`. Establish `ht : ∀ f, IsThetaFunO ψ V W (J f).1` using `fun f => (hc f).symm ▸ f.2`. Take `⟨d, x, y, hd, hn, hx, hy, c1, c2, c3, hN⟩` from `exists_der (HM V W) HM_herm (rhoV hψ σ V W) (isHeis_rhoB h hψ) J hJ (fun f => sm_of_theta h hψ _ (ht f)) fun v f => ⟨⟨_, GlobalTheory.DefLift.Gen.theta_dH h hψ (J f) (ht f) v⟩, QB_ext fun w => congrFun (hc _) w⟩`.

Establish `hD : ∀ τ z (g : thetaSub ψ V W), Datum.dRho (heisO ψ V W) θ τ z g = d (vecL (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)) g` using `fun τ z g => by`. Rewrite using `[← hc (d _ g), hd, GlobalTheory.DefLift.Gen.coe_dH h hψ _ (ht g), hc]`. Set `u : FVar D W.rank V.rank → Ix V W → ℂ` to `fun k => uM A B *ᵥ Pi.single (k.2, k.1) 1`. Set `p : FVar D W.rank V.rank → Prop` to `fun k => B.ε k.1 k.2.1 = A.ε k.1 k.2.2`. Establish `s2 : ∀ τ, (fockScale D τ : ℂ) * fockScale D τ = 4 * π * cc D τ` using `fun τ => by`.

Rewrite using `[GlobalTheory.VacuumFockLaws.fockScale_sq, cc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `sn` using `GlobalTheory.VacuumFockLaws.fockScale_ne (D := D)`. Establish `cs : ∀ τ, starRingEnd ℂ (cc D τ) = cc D τ` using `fun τ => conj_ofReal _`.

Set `a : FVar D W.rank V.rank → Module.End ℂ (thetaSub ψ V W)` to `fun k => (fockScale D k.1 : ℂ)⁻¹ • if p k then x (u k) else y (u k)`. Set `b : FVar D W.rank V.rank → Module.End ℂ (thetaSub ψ V W)` to `fun k => -(fockScale D k.1 : ℂ)⁻¹ • if p k then y (u k) else x (u k)`. Take `⟨haa, hba⟩` from `ccr_of_sign (fun k => x (u k)) (fun k => y (u k)) p (fun k => (fockScale D k.1 : ℂ)) (fun k => sn _) (fun _ _ => c1 _ _) (fun _ _ => c2 _ _) (fun k l => by`. Rewrite using `[c3]`. Use `congr 2`.

Establish `e : star (u l) ⬝ᵥ HM V W *ᵥ u k = ((uM A B)ᴴ * HM V W * uM A B) (l.2, l.1) (k.2, k.1)`. Simplify using `only [u]`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`. Simplify using `[← Pi.single_star]`. Rewrite using `[e, uM_gram, diagonal_apply]`.

Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, s2, map_mul, map_mul, cs, conj_sgn, conj_sgn, mul_assoc (cc D _), sgn_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hkl, if_neg fun e : (l.2, l.1) = (k.2, k.1) => hkl (Prod.swap_injective e).symm, map_zero, mul_zero])`.

Use the proof step `(a := a) (b := b) (fun _ => rfl) fun _ => rfl`. Establish `hdJ : ∀ (k : FVar D W.rank V.rank) (g : thetaSub ψ V W), Datum.dRho (heisO ψ V W) θ k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) g = d (u k) g ∧ Datum.dRho (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)) g = (if p k then (1 …` using `fun k g => by`. Establish `e` using `uM_single A B k.1 k.2.1 k.2.2`. Rewrite using `[hD, hD, cplxO_unit, vecL_smul, vecL_smul, ← e]`. Use `⟨rfl, ?_⟩` and prove the remaining obligations.

Simplify using `only [p]`. Use `split_ifs`. Rewrite using `[one_smul, one_smul]`. Rewrite using `[neg_one_smul, neg_one_smul, hn]`. Both sides reduce to the same expression.

Use `⟨fun i j => (sgn (A.ε τ j) * (fockScale D τ : ℂ)⁻¹) • x (u (τ, i, j)), fun i j => (-sgn (B.ε τ i) * (fockScale D τ : ℂ)⁻¹) • y (u (τ, i, j)), fun k l => x (uM A B *ᵥ Pi.single k 1) * (-(1 / (4 * π)) : ℂ) • y ((uM A B * diagonal fun k => (cc D k.2)⁻¹ * sgn (B.ε k.2 k.1.1) * sgn (A …` and prove the remaining obligations. Take `⟨E, h1, h2, h3⟩` from `exists_lift (thetaSub ψ V W) (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) a b (fun k g => by`. Rewrite using `[aPlusAll, aPlus, crea, (hdJ k g).1, (hdJ k g).2]`. Simplify using `only [a]`. Use `split_ifs`.

Rewrite using `[hx, one_smul]`. Both sides reduce to the same expression. Rewrite using `[hy, neg_one_smul, smul_neg, sub_neg_eq_add] rfl) haa hba ⟨f, hf.1⟩ (fun k => by`. Establish `e` using `hf.2 k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)`. Rewrite `e` using `[annih, (hdJ k ⟨f, hf.1⟩).1, (hdJ k ⟨f, hf.1⟩).2]`.

Simplify using `only [b, LinearMap.smul_apply]`. Rewrite using `[smul_eq_zero]`. Use `Or.inr (Subtype.ext ?_)` and prove the remaining obligations. Use `split_ifs at e ⊢`. Rewrite `e` using `[one_smul]`.

Rewrite using `[hy]`. Conclude with `e`. Rewrite `e` using `[neg_one_smul, smul_neg, ← sub_eq_add_neg]`. Rewrite using `[hx]`. Conclude with `e)`.

Use `⟨E, h1, fun i j P => ?_, fun i j P => ?_⟩` and prove the remaining obligations. Unfold `raiO`. Distinguish the cases in `hp : B.ε τ i = A.ε τ j`. Simplify using `only [if_pos hp, LinearMap.smul_apply, map_smul, LinearMap.mulLeft_apply, h2, a, p, smul_smul]`. Simplify using `only [if_neg hp, LinearMap.smul_apply, map_smul, LinearMap.neg_apply, map_neg, Derivation.coeFn_coe, h3, b, p, smul_smul, neg_smul, neg_neg]`.

Unfold `lowO`. Distinguish the cases in `hp : B.ε τ i = A.ε τ j`. Simplify using `only [if_pos hp, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe, h3, b, p, smul_smul]`. Rewrite using `[hp, neg_mul, mul_neg]`. Establish `e : sgn (A.ε τ j) = -sgn (B.ε τ i)` using `by revert hp`.

Apply the tactic sequence `cases B.ε τ i <;> cases A.ε τ j <;> simp [sgn]`. Simplify using `only [if_neg hp, LinearMap.smul_apply, map_smul, LinearMap.mulLeft_apply, h2, a, p, smul_smul, e]`. Use `beta_reduce`. Rewrite using `[← mulVec_mulVec, diagonal_mulVec_single, ← smul_eq_mul _ (1 : ℂ), Pi.single_smul', mulVec_smul, map_smulₛₗ, map_mul, map_mul, map_inv₀, cs, conj_sgn, conj_sgn]`. Simplify using `only [u, smul_mul_assoc, mul_smul_comm, smul_smul]`.

Use `congr 1`. Establish `h1` using `sn τ`. Establish `h2 : cc D τ = fockScale D τ * fockScale D τ / (4 * π)`. Rewrite using `[s2]`. Clear the denominators using the available nonvanishing facts.

Establish `h3 : (π : ℂ) ≠ 0` using `ofReal_ne_zero.2 Real.pi_ne_zero`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(sgn (B.ε τ l) * sgn (A.ε τ k)) * sgn_mul_self (A.ε τ j)`. Use `beta_reduce`.

Rewrite using `[← quad_basis x y _ hX, ← HM_inv]`. Conclude with `(congrArg (fun F : BB ψ V W => (F.1 : WO V W → ℂ)) (hN X g)).trans (hc _)`.
-/
theorem exists_raise_lower (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau) :
    ∃ (R L : Fin W.rank → Fin V.rank → Module.End ℂ (thetaSub ψ V W))
      (w : Ix V W → Ix V W → Module.End ℂ (thetaSub ψ V W)),
      (∀ f, IsVacF ψ θ A B f → ∃ E : PolF D W.rank V.rank →ₗ[ℂ] thetaSub ψ V W, (∀ P, ptF ψ θ A B f P = E P) ∧
        (∀ i j P, E (raiO τ (A.ε τ) (B.ε τ) i j P) = R i j (E P)) ∧
        ∀ i j P, E (lowO τ (A.ε τ) (B.ε τ) i j P) = L i j (E P)) ∧
      (∀ i j l k, w ((i, j), τ) ((l, k), τ) = (sgn (A.ε τ j) * sgn (A.ε τ k)) • (R i j * L l k)) ∧
      ∀ X X' : Matrix (Ix V W) (Ix V W) ℂ, X * uM A B = uM A B * X' → ∀ g : thetaSub ψ V W,
        ((nOp (rhoV hψ σ V W) (HM V W) X (toB hψ g.1 g.2)).1 : WO V W → ℂ) = ((∑ k, ∑ l, X' k l • w k l) g).1 := by
  let J : thetaSub ψ V W →ₗ[ℂ] BB ψ V W :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO V W → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ V W (J f).1 := fun f => (hc f).symm ▸ f.2
  obtain ⟨d, x, y, hd, hn, hx, hy, c1, c2, c3, hN⟩ := exists_der (HM V W) HM_herm (rhoV hψ σ V W) (isHeis_rhoB h hψ)
    J hJ (fun f => sm_of_theta h hψ _ (ht f))
    fun v f => ⟨⟨_, GlobalTheory.DefLift.Gen.theta_dH h hψ (J f) (ht f) v⟩, QB_ext fun w => congrFun (hc _) w⟩
  have hD : ∀ τ z (g : thetaSub ψ V W), Datum.dRho (heisO ψ V W) θ τ z g =
      d (vecL (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)) g := fun τ z g => by
    rw [← hc (d _ g), hd, GlobalTheory.DefLift.Gen.coe_dH h hψ _ (ht g), hc]
  let u : FVar D W.rank V.rank → Ix V W → ℂ := fun k => uM A B *ᵥ Pi.single (k.2, k.1) 1
  let p : FVar D W.rank V.rank → Prop := fun k => B.ε k.1 k.2.1 = A.ε k.1 k.2.2
  have s2 : ∀ τ, (fockScale D τ : ℂ) * fockScale D τ = 4 * π * cc D τ := fun τ => by
    rw [GlobalTheory.VacuumFockLaws.fockScale_sq, cc]
    push_cast
    ring
  have sn := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D)
  have cs : ∀ τ, starRingEnd ℂ (cc D τ) = cc D τ := fun τ => conj_ofReal _
  let a : FVar D W.rank V.rank → Module.End ℂ (thetaSub ψ V W) := fun k =>
    (fockScale D k.1 : ℂ)⁻¹ • if p k then x (u k) else y (u k)
  let b : FVar D W.rank V.rank → Module.End ℂ (thetaSub ψ V W) := fun k =>
    -(fockScale D k.1 : ℂ)⁻¹ • if p k then y (u k) else x (u k)
  obtain ⟨haa, hba⟩ := ccr_of_sign (fun k => x (u k)) (fun k => y (u k)) p (fun k => (fockScale D k.1 : ℂ))
    (fun k => sn _) (fun _ _ => c1 _ _) (fun _ _ => c2 _ _) (fun k l => by
      rw [c3]
      congr 2
      have e : star (u l) ⬝ᵥ HM V W *ᵥ u k = ((uM A B)ᴴ * HM V W * uM A B) (l.2, l.1) (k.2, k.1) := by
        simp only [u]
        rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
        simp [← Pi.single_star]
      rw [e, uM_gram, diagonal_apply]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, s2, map_mul, map_mul, cs, conj_sgn, conj_sgn, mul_assoc (cc D _), sgn_mul]
        ring
      · rw [if_neg hkl, if_neg fun e : (l.2, l.1) = (k.2, k.1) => hkl (Prod.swap_injective e).symm, map_zero, mul_zero])
    (a := a) (b := b) (fun _ => rfl) fun _ => rfl
  have hdJ : ∀ (k : FVar D W.rank V.rank) (g : thetaSub ψ V W),
      Datum.dRho (heisO ψ V W) θ k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) g = d (u k) g ∧
      Datum.dRho (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)) g =
        (if p k then (1 : ℂ) else -1) • (d (I • u k) g).1 := fun k g => by
    have e := uM_single A B k.1 k.2.1 k.2.2
    rw [hD, hD, cplxO_unit, vecL_smul, vecL_smul, ← e]
    refine ⟨rfl, ?_⟩
    simp only [p]
    split_ifs
    · rw [one_smul, one_smul]
    · rw [neg_one_smul, neg_one_smul, hn]
      rfl
  refine ⟨fun i j => (sgn (A.ε τ j) * (fockScale D τ : ℂ)⁻¹) • x (u (τ, i, j)),
    fun i j => (-sgn (B.ε τ i) * (fockScale D τ : ℂ)⁻¹) • y (u (τ, i, j)),
    fun k l => x (uM A B *ᵥ Pi.single k 1) * (-(1 / (4 * π)) : ℂ) • y ((uM A B * diagonal fun k =>
      (cc D k.2)⁻¹ * sgn (B.ε k.2 k.1.1) * sgn (A.ε k.2 k.1.2)) *ᵥ Pi.single l 1),
    fun f hf => ?_, fun i j l k => ?_, fun X X' hX g => ?_⟩
  · obtain ⟨E, h1, h2, h3⟩ := exists_lift (thetaSub ψ V W)
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) a b (fun k g => by
        rw [aPlusAll, aPlus, crea, (hdJ k g).1, (hdJ k g).2]
        simp only [a]
        split_ifs
        · rw [hx, one_smul]
          rfl
        · rw [hy, neg_one_smul, smul_neg, sub_neg_eq_add]
          rfl) haa hba ⟨f, hf.1⟩ (fun k => by
        have e := hf.2 k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
        rw [annih, (hdJ k ⟨f, hf.1⟩).1, (hdJ k ⟨f, hf.1⟩).2] at e
        simp only [b, LinearMap.smul_apply]
        rw [smul_eq_zero]
        refine Or.inr (Subtype.ext ?_)
        split_ifs at e ⊢
        · rw [one_smul] at e
          rw [hy]
          exact e
        · rw [neg_one_smul, smul_neg, ← sub_eq_add_neg] at e
          rw [hx]
          exact e)
    refine ⟨E, h1, fun i j P => ?_, fun i j P => ?_⟩
    · unfold raiO
      by_cases hp : B.ε τ i = A.ε τ j
      · simp only [if_pos hp, LinearMap.smul_apply, map_smul, LinearMap.mulLeft_apply, h2, a, p, smul_smul]
      · simp only [if_neg hp, LinearMap.smul_apply, map_smul, LinearMap.neg_apply, map_neg, Derivation.coeFn_coe, h3,
          b, p, smul_smul, neg_smul, neg_neg]
    · unfold lowO
      by_cases hp : B.ε τ i = A.ε τ j
      · simp only [if_pos hp, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe, h3, b, p, smul_smul]
        rw [hp, neg_mul, mul_neg]
      · have e : sgn (A.ε τ j) = -sgn (B.ε τ i) := by
          revert hp
          cases B.ε τ i <;> cases A.ε τ j <;> simp [sgn]
        simp only [if_neg hp, LinearMap.smul_apply, map_smul, LinearMap.mulLeft_apply, h2, a, p, smul_smul, e]
  · beta_reduce
    rw [← mulVec_mulVec, diagonal_mulVec_single, ← smul_eq_mul _ (1 : ℂ), Pi.single_smul',
      mulVec_smul, map_smulₛₗ, map_mul, map_mul, map_inv₀, cs, conj_sgn, conj_sgn]
    simp only [u, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    have h1 := sn τ
    have h2 : cc D τ = fockScale D τ * fockScale D τ / (4 * π) := by
      rw [s2]
      field_simp
    have h3 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [h2]
    field_simp
    linear_combination (sgn (B.ε τ l) * sgn (A.ε τ k)) * sgn_mul_self (A.ε τ j)
  · beta_reduce
    rw [← quad_basis x y _ hX, ← HM_inv]
    exact (congrArg (fun F : BB ψ V W => (F.1 : WO V W → ℂ)) (hN X g)).trans (hc _)

/- English proof (translation)
Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same, Pi.single_eq_same, nonsing_inv_mul_cancel_right _ _ (hF t)]`. Rewrite using `[Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem blk_single_congr {O : Type} [DecidableEq O] {n : ℕ} (F : O → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ t, IsUnit (F t).det)
    (τ t : O) (X : Matrix (Fin n) (Fin n) ℂ) :
    F t * (Pi.single τ X : O → Matrix (Fin n) (Fin n) ℂ) t =
      (Pi.single τ (F τ * X * (F τ)⁻¹) : O → Matrix (Fin n) (Fin n) ℂ) t * F t := by
  by_cases h : t = τ
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, nonsing_inv_mul_cancel_right _ _ (hF t)]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply, map_sum, map_smul, map_add, hr, hl, Finset.sum_smul, mul_smul, ← Finset.sum_add_distrib, ← smul_add]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => congrArg _ (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lift_quad {M N ι κ : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [Fintype ι]
    [DecidableEq ι] [Fintype κ] (E : M →ₗ[ℂ] N) (r l : ι → κ → Module.End ℂ M) (R L : ι → κ → Module.End ℂ N)
    (hr : ∀ i j P, E (r i j P) = R i j (E P)) (hl : ∀ i j P, E (l i j P) = L i j (E P)) (Y : Matrix ι ι ℂ) (P : M) :
    E ((∑ i, ∑ k, Y i k • ∑ j, (r i j * l k j + if i = k then (1 / 2 : ℂ) • 1 else 0)) P) =
      (∑ i, ∑ k, Y i k • ∑ j, R i j * L k j) (E P) +
        (∑ i, ∑ k, Y i k * ∑ _j : κ, if i = k then (1 / 2 : ℂ) else 0) • E P := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply, map_sum, map_smul,
    map_add, hr, hl, Finset.sum_smul, mul_smul, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  split_ifs <;> simp

/- English proof (translation)
Introduce `D V W A B θ ψ χS χT ω τ hθ hω`. Establish `hψ` using `hω.std`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Take `⟨R, L, w, hE, hw, hN⟩` from `exists_raise_lower A B h hψ τ`. Establish `key : ∀ γ : ℝ → GA D V × GA D W, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC V ∧ (γ t).2 ∈ GinfC W) → ∀ X X' : Matrix (Ix V W) (Ix V W) ℂ, (∀ k l, HasDerivAt (fun t => mM θ V W (γ t) k l) (X k l) 0) → X * uM A B = uM A B * X' → ∃ lam : ℂ, ∀ (g : thetaSub …`.

Introduce `γ h1 h2 h3 X X' h4 h5`. Take `⟨lam, hl⟩` from `GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ V W ω (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont γ h1 h2 h3 X h4`. Use `⟨lam, fun g z => ?_⟩` and prove the remaining obligations. Establish `e` using `coe_toB hψ g.1 g.2`. Establish `h6` using `hl (toB hψ g.1 g.2) (e.symm ▸ g.2) 1 z`.

Simplify using `only [one_mul, map_one, Module.End.one_apply] at h6`. Rewrite `h6` using `[← GlobalTheory.DefLift.Gen.coe_add_smul, hN X X' h5, e]`. Conclude with `h6`. Establish `hS : ∀ X, ∃ κ : ℂ, X ∈ lieAt V τ → ∀ f, IsVacF ψ θ A B f → ∀ (P : PolF D W.rank V.rank) (z : WO V W), HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptF ψ θ A B f P) z) (ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κ • P) z) 0`. Introduce `X`.

Distinguish the cases in `hX : X ∈ lieAt V τ`. Use `swap`. Conclude with `⟨0, fun h => absurd h hX⟩`. Take `⟨lam, hl⟩` from `key (fun t => (oneP θ V τ X t, 1)) ((continuous_oneP hθ hX).prodMk continuous_const) (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul]) (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X))) (blk (fun _ => 1) (Pi.single τ (-(A.fr τ * X * …`. Simplify using `only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]`.

Use `split_ifs`. Conclude with `(WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _`. Conclude with `hasDerivAt_const _ _) (by`. Rewrite using `[uM, blk_mul, blk_mul]`. Apply the tactic sequence `congr 1 <;> funext t`.

Rewrite using `[Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[blk_single_congr A.fr (fr_det A), Matrix.mul_neg, Matrix.neg_mul])`. Use `⟨lam - ∑ i, ∑ k, (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) i k * ∑ _j : Fin W.rank, if i = k then (1 / 2 : ℂ) else 0, fun _ f hf P z => ?_⟩` and prove the remaining obligations. Take `⟨E, h1, h2, h3⟩` from `hE f hf`. Establish `e : ∑ k, ∑ l, blk (fun _ => 1) (Pi.single τ (-(A.fr τ * X * (A.fr τ)⁻¹))) k l • w k l = ∑ j, ∑ k, (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) j k • ∑ i, R i j * L i k`.

Rewrite using `[WeylAction.sum_right, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [Matrix.map_apply, lie_entry (fr_det A τ) (A.fr_gram τ) hX]`. Simplify using `only [hw, ← Finset.smul_sum]`. Use `module`.

Rewrite using `[h1, h1, map_add, map_smul, fockS, lift_quad E (fun j i => raiO τ (A.ε τ) (B.ε τ) i j) (fun j i => lowO τ (A.ε τ) (B.ε τ) i j) (fun j i => R i j) (fun j i => L i j) (fun j i => h2 i j) (fun j i => h3 i j), add_assoc, ← add_smul, add_sub_cancel, ← e]`. Conclude with `hl (E P) z`. Establish `hT : ∀ Y, ∃ κ : ℂ, Y ∈ lieAt W τ → ∀ f, IsVacF ψ θ A B f → ∀ (P : PolF D W.rank V.rank) (z : WO V W), HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptF ψ θ A B f P) z) (ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + κ • P) z) 0`. Introduce `Y`. Distinguish the cases in `hY : Y ∈ lieAt W τ`.

Use `swap`. Conclude with `⟨0, fun h => absurd h hY⟩`. Take `⟨lam, hl⟩` from `key (fun t => (1, oneP θ W τ Y t)) (continuous_const.prodMk (continuous_oneP hθ hY)) (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul]) (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1) (blk (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) fun _ = …`. Simplify using `only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]`. Use `split_ifs`.

Conclude with `(WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _`. Conclude with `hasDerivAt_const _ _) (by`. Rewrite using `[uM, blk_mul, blk_mul]`. Apply the tactic sequence `congr 1 <;> funext t`. Rewrite using `[← nonsing_inv_mul_cancel_left _ (_ * (B.fr t)⁻¹) (fr_det B t), ← Matrix.mul_assoc (B.fr t), blk_single_congr B.fr (fr_det B), mul_nonsing_inv_cancel_right _ _ (fr_det B t)]`.

Rewrite using `[Matrix.one_mul, Matrix.mul_one])`. Use `⟨lam - ∑ i, ∑ k, (B.fr τ * Y * (B.fr τ)⁻¹) i k * ∑ _j : Fin V.rank, if i = k then (1 / 2 : ℂ) else 0, fun _ f hf P z => ?_⟩` and prove the remaining obligations. Take `⟨E, h1, h2, h3⟩` from `hE f hf`. Establish `e : ∑ k, ∑ l, blk (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) (fun _ => 1) k l • w k l = ∑ i, ∑ k, (B.fr τ * Y * (B.fr τ)⁻¹) i k • ∑ j, R i j * L k j`. Rewrite using `[WeylAction.sum_left]`.

Simplify using `only [hw, sgn_mul_self, one_smul]`. Rewrite using `[h1, h1, map_add, map_smul, fockT, lift_quad E _ _ R L h2 h3, add_assoc, ← add_smul, add_sub_cancel, ← e]`. Conclude with `hl (E P) z`. Use `choose κS hS using hS`. Use `choose κT hT using hT`.

Conclude with `⟨κS, κT, fun f hf => ⟨fun X hX => hS X hX f hf, fun Y hY => hT Y hY f hf⟩⟩`.
-/
theorem lieFockUpTo : ∀ D : D7, GlobalTheory.ChainFr.LieFockUpTo D := by
  intro D V W A B θ ψ χS χT ω τ hθ hω
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨R, L, w, hE, hw, hN⟩ := exists_raise_lower A B h hψ τ
  have key : ∀ γ : ℝ → GA D V × GA D W, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) →
      (∀ t, (γ t).1 ∈ GinfC V ∧ (γ t).2 ∈ GinfC W) → ∀ X X' : Matrix (Ix V W) (Ix V W) ℂ,
      (∀ k l, HasDerivAt (fun t => mM θ V W (γ t) k l) (X k l) 0) → X * uM A B = uM A B * X' →
      ∃ lam : ℂ, ∀ (g : thetaSub ψ V W) z,
        HasDerivAt (fun t => ω (γ t) g.1 z) (((∑ k, ∑ l, X' k l • w k l) g + lam • g).1 z) 0 := by
    intro γ h1 h2 h3 X X' h4 h5
    obtain ⟨lam, hl⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ V W ω (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
      γ h1 h2 h3 X h4
    refine ⟨lam, fun g z => ?_⟩
    have e := coe_toB hψ g.1 g.2
    have h6 := hl (toB hψ g.1 g.2) (e.symm ▸ g.2) 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h6
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul, hN X X' h5, e] at h6
    exact h6
  have hS : ∀ X, ∃ κ : ℂ, X ∈ lieAt V τ → ∀ f, IsVacF ψ θ A B f → ∀ (P : PolF D W.rank V.rank) (z : WO V W),
      HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κ • P) z) 0 := by
    intro X
    by_cases hX : X ∈ lieAt V τ
    swap
    · exact ⟨0, fun h => absurd h hX⟩
    obtain ⟨lam, hl⟩ := key (fun t => (oneP θ V τ X t, 1)) ((continuous_oneP hθ hX).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X)))
      (blk (fun _ => 1) (Pi.single τ (-(A.fr τ * X * (A.fr τ)⁻¹)))) (fun k l => by
        simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
          WeylAction.blk_apply]
        split_ifs
        · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
        · exact hasDerivAt_const _ _) (by
        rw [uM, blk_mul, blk_mul]
        congr 1 <;> funext t
        · rw [Matrix.one_mul, Matrix.mul_one]
        · rw [blk_single_congr A.fr (fr_det A), Matrix.mul_neg, Matrix.neg_mul])
    refine ⟨lam - ∑ i, ∑ k, (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) i k *
      ∑ _j : Fin W.rank, if i = k then (1 / 2 : ℂ) else 0, fun _ f hf P z => ?_⟩
    obtain ⟨E, h1, h2, h3⟩ := hE f hf
    have e : ∑ k, ∑ l, blk (fun _ => 1) (Pi.single τ (-(A.fr τ * X * (A.fr τ)⁻¹))) k l • w k l =
        ∑ j, ∑ k, (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) j k • ∑ i, R i j * L i k := by
      rw [WeylAction.sum_right, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply, lie_entry (fr_det A τ) (A.fr_gram τ) hX]
      simp only [hw, ← Finset.smul_sum]
      module
    rw [h1, h1, map_add, map_smul, fockS, lift_quad E (fun j i => raiO τ (A.ε τ) (B.ε τ) i j)
      (fun j i => lowO τ (A.ε τ) (B.ε τ) i j) (fun j i => R i j) (fun j i => L i j) (fun j i => h2 i j)
      (fun j i => h3 i j), add_assoc, ← add_smul, add_sub_cancel, ← e]
    exact hl (E P) z
  have hT : ∀ Y, ∃ κ : ℂ, Y ∈ lieAt W τ → ∀ f, IsVacF ψ θ A B f → ∀ (P : PolF D W.rank V.rank) (z : WO V W),
      HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + κ • P) z) 0 := by
    intro Y
    by_cases hY : Y ∈ lieAt W τ
    swap
    · exact ⟨0, fun h => absurd h hY⟩
    obtain ⟨lam, hl⟩ := key (fun t => (1, oneP θ W τ Y t)) (continuous_const.prodMk (continuous_oneP hθ hY))
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1)
      (blk (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) fun _ => 1) (fun k l => by
        simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
        split_ifs
        · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
        · exact hasDerivAt_const _ _) (by
        rw [uM, blk_mul, blk_mul]
        congr 1 <;> funext t
        · rw [← nonsing_inv_mul_cancel_left _ (_ * (B.fr t)⁻¹) (fr_det B t), ← Matrix.mul_assoc (B.fr t),
            blk_single_congr B.fr (fr_det B), mul_nonsing_inv_cancel_right _ _ (fr_det B t)]
        · rw [Matrix.one_mul, Matrix.mul_one])
    refine ⟨lam - ∑ i, ∑ k, (B.fr τ * Y * (B.fr τ)⁻¹) i k *
      ∑ _j : Fin V.rank, if i = k then (1 / 2 : ℂ) else 0, fun _ f hf P z => ?_⟩
    obtain ⟨E, h1, h2, h3⟩ := hE f hf
    have e : ∑ k, ∑ l, blk (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) (fun _ => 1) k l • w k l =
        ∑ i, ∑ k, (B.fr τ * Y * (B.fr τ)⁻¹) i k • ∑ j, R i j * L k j := by
      rw [WeylAction.sum_left]
      simp only [hw, sgn_mul_self, one_smul]
    rw [h1, h1, map_add, map_smul, fockT, lift_quad E _ _ R L h2 h3, add_assoc, ← add_smul, add_sub_cancel, ← e]
    exact hl (E P) z
  choose κS hS using hS
  choose κT hT using hT
  exact ⟨κS, κT, fun f hf => ⟨fun X hX => hS X hX f hf, fun Y hY => hT Y hY f hf⟩⟩

end GlobalTheory.LieFock

end
