import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDualFormIndep
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder
open MonObj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.RiemProd

open RiemIndep

section Frames

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

/- English proof (translation)
Use `fin_cases k`. Express the relevant statement in the definitionally equal form `u'.ex (T z + T z) = u.ex z ≫ (ψ * ψ)`. Rewrite using `[u'.ex_add, hT, MonObj.comp_mul]`. Conclude with `hT z`. Express the relevant statement in the definitionally equal form `u'.ex 0 = u.ex z ≫ 1`.

Rewrite using `[MonObj.comp_one]`. Conclude with `(u'.ker 0).2 (zero_mem _)`.
-/
theorem covers₂ (u : HolUnif A L g) (u' : HolUnif A' L' g') (ψ : A ⟶ A') (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) (k : Fin 3) (z : Fin g → ℂ) :
    u'.ex (![T + T, T, 0] k z) = u.ex z ≫ ![ψ * ψ, ψ, 1] k := by
  fin_cases k
  · change u'.ex (T z + T z) = u.ex z ≫ (ψ * ψ)
    rw [u'.ex_add, hT, MonObj.comp_mul]
  · exact hT z
  · change u'.ex 0 = u.ex z ≫ 1
    rw [MonObj.comp_one]
    exact (u'.ker 0).2 (zero_mem _)

/- English proof (translation)
Establish `hl : T l ∈ u'.Λ`. Rewrite using `[← u'.ker, hT, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hT, map_zero]`. Conclude with `(u'.ker 0).2 u'.Λ.zero_mem`. Establish `hχ` using `hA.2.2.1`. Use `⟨χ ⟨T l + T l, add_mem hl hl⟩ / χ ⟨T l, hl⟩ ^ 2, by simp [hχ], fun i z hz => ?_⟩` and prove the remaining obligations.

Establish `hc : ∀ k, ⊤ ≤ (u'.ex (![T + T, T, 0] k z)).left ⁻¹ᵁ L'.U (i k)` using `fun k => by`. Rewrite using `[covers₂ u u' ψ T hT]`. Conclude with `(CubeValues.le_preimage_wchart (u.ex z).left L' _ i).1 hz k`. Establish `h0` using `hA.2.2.2 ⟨T l + T l, add_mem hl hl⟩ (i 0) (T z + T z) (hc 0)`. Establish `h1` using `hA.2.2.2 ⟨T l, hl⟩ (i 1) (T z) (hc 1)`.

Establish `h4 : χ ⟨T l, hl⟩ ≠ 0` using `norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)`. Express the relevant statement in the definitionally equal form `∏ k, u'.fr (i k) (![T + T, T, 0] k z) ^ (![1, -2, 1] k : ℤ) = _ * ∏ k, u'.fr (i k) (![T + T, T, 0] k (z + l)) ^ (![1, -2, 1] k : ℤ)`. Simplify using `only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LinearMap.add_apply, LinearMap.zero_apply, map_add, zpow_one, zpow_neg, zpow_ofNat]`. Rewrite using `[h0, h1, add_zero]`. Simplify using `only [hermForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]`.

Generalize the expression as in `(T z ⬝ᵥ H.mulVec (star (T l))) = a`. Generalize the expression as in `(T l ⬝ᵥ H.mulVec (star (T l))) = b`. Establish `e : Complex.exp (Real.pi * (a + a + (a + a)) + Real.pi / 2 * (b + b + (b + b))) = Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) * Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ 2`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h6` using `Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)`. Rewrite using `[e]`. Generalize the expression as in `Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6`.

Simplify using `only [mul_pow, mul_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem factor_diag₂ (u : HolUnif A L g) (u' : HolUnif A' L' g') (ψ : A ⟶ A')
    (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ)
    {H : Matrix (Fin g') (Fin g') ℂ} {χ : u'.Λ → ℂ}
    (hA : u'.IsAH H χ) (l : u.Λ) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (diagLB L' ψ).U i →
      (linCombUnif u u' _ _ ![1, -2, 1] (covers₂ u u' ψ T hT)).fr i z =
        c * Complex.exp (Real.pi * (2 * hermForm H (T z) (T l)) + Real.pi / 2 * (2 * hermForm H (T l) (T l))) *
          (linCombUnif u u' _ _ ![1, -2, 1] (covers₂ u u' ψ T hT)).fr i (z + l) := by
  have hl : T l ∈ u'.Λ := by
    rw [← u'.ker, hT, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hT, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hχ := hA.2.2.1
  refine ⟨χ ⟨T l + T l, add_mem hl hl⟩ / χ ⟨T l, hl⟩ ^ 2, by simp [hχ], fun i z hz => ?_⟩
  have hc : ∀ k, ⊤ ≤ (u'.ex (![T + T, T, 0] k z)).left ⁻¹ᵁ L'.U (i k) := fun k => by
    rw [covers₂ u u' ψ T hT]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' _ i).1 hz k
  have h0 := hA.2.2.2 ⟨T l + T l, add_mem hl hl⟩ (i 0) (T z + T z) (hc 0)
  have h1 := hA.2.2.2 ⟨T l, hl⟩ (i 1) (T z) (hc 1)
  have h4 : χ ⟨T l, hl⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)
  change ∏ k, u'.fr (i k) (![T + T, T, 0] k z) ^ (![1, -2, 1] k : ℤ) =
    _ * ∏ k, u'.fr (i k) (![T + T, T, 0] k (z + l)) ^ (![1, -2, 1] k : ℤ)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LinearMap.add_apply,
    LinearMap.zero_apply, map_add, zpow_one, zpow_neg, zpow_ofNat]
  rw [h0, h1, add_zero]
  simp only [hermForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  generalize (T z ⬝ᵥ H.mulVec (star (T l))) = a
  generalize (T l ⬝ᵥ H.mulVec (star (T l))) = b
  have e : Complex.exp (Real.pi * (a + a + (a + a)) + Real.pi / 2 * (b + b + (b + b))) =
      Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) * Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
  rw [e]
  generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
  simp only [mul_pow, mul_inv]
  field_simp

end Frames

section Sum

open PullHermitian

variable {A A₁ A₂ : Over (Sp ℂ)} [GrpObj A] [GrpObj A₁] [GrpObj A₂] {L : LB A.left} {L₁ : LB A₁.left}
  {L₂ : LB A₂.left} {g g₁ g₂ : ℕ}

/- English proof (translation)
Establish `hI : ∀ z, u.ex (LinearMap.id (R` using `ℂ) z) = u.ex z ≫ 𝟙 A := fun z => (Category.comp_id _).symm`. Use `choose c hc hf using factor_diag₂ u u (𝟙 A) LinearMap.id hI hA`. Use `choose c₁ hc₁ hf₁ using factor_diag₂ u u₁ ψ₁ T₁ hT₁ hA₁`. Use `choose c₂ hc₂ hf₂ using factor_diag₂ u u₂ ψ₂ T₂ hT₂ hA₂`. Establish `d : (diagLB L (𝟙 A)).IsLB` using `LB.isLB_linComb hL _ _`.

Establish `d₁ : (diagLB L₁ ψ₁).IsLB` using `LB.isLB_linComb hL₁ _ _`. Establish `d₂ : (diagLB L₂ ψ₂).IsLB` using `LB.isLB_linComb hL₂ _ _`. Establish `dd : (LB.div (diagLB L (𝟙 A)) (diagLB L₁ ψ₁)).IsLB` using `LB.isLB_div d d₁`. Use `set G₁ := (LinearMap.toMatrix' T₁).transpose * H₁ * (LinearMap.toMatrix' T₁).transpose.conjTranspose with hG₁`. Use `set G₂ := (LinearMap.toMatrix' T₂).transpose * H₂ * (LinearMap.toMatrix' T₂).transpose.conjTranspose with hG₂`.

Establish `hG₁h : G₁.IsHermitian` using `Matrix.isHermitian_mul_mul_conjTranspose _ hA₁.1`. Establish `hG₂h : G₂.IsHermitian` using `Matrix.isHermitian_mul_mul_conjTranspose _ hA₂.1`. Establish `hs : ∀ z w, hermForm ((2 : ℂ) • H - (2 : ℂ) • G₁ - (2 : ℂ) • G₂) z w = 2 * hermForm H z w - 2 * hermForm H₁ (T₁ z) (T₁ w) - 2 * hermForm H₂ (T₂ z) (T₂ w)` using `fun z w => by`. Rewrite using `[← hermForm_pull H₁ T₁, ← hermForm_pull H₂ T₂, ← hG₁, ← hG₂]`. Simplify using `[hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec]`.

Establish `two : IsSelfAdjoint (2 : ℂ)` using `by simp [IsSelfAdjoint]`. Establish `key` using `herm_eq_zero (LB.isLB_div dd d₂) (by rw [CechPic.cls_div dd d₂, CechPic.cls_div d d₁, cls_diagLB _ hL, cls_diagLB ψ₁ hL₁, cls_diagLB ψ₂ hL₂, h, add_sub_cancel_left, sub_self]) (SameFactor.divUnif (linCombUnif u u₂ _ _ ![1, -2, 1] (covers₂ u u₂ ψ₂ T₂ hT₂)) (SameFactor.divUnif (lin …`. Take `⟨h12, h3⟩` from `(top_le_preimage_inf _ _ _).1 hz`. Take `⟨h1, h2⟩` from `(top_le_preimage_inf _ _ _).1 h12`. Establish `e1` using `hf l i.1.1 z h1`.

Establish `e2` using `hf₁ l i.1.2 z h2`. Establish `e3` using `hf₂ l i.2 z h3`. Use `(congrArg₂ (fun a b => a * b) (congrArg₂ (fun a b => a * b⁻¹) e1 e2) (congrArg (·⁻¹) e3)).trans ?_` and prove the remaining obligations. Rewrite using `[hs, hs]`. Simplify using `only [LinearMap.id_apply]`.

Establish `ex : ∀ a a₁ a₂ b b₁ b₂ : ℂ, Complex.exp (Real.pi * (2 * a - 2 * a₁ - 2 * a₂) + Real.pi / 2 * (2 * b - 2 * b₁ - 2 * b₂)) = Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) / Complex.exp (Real.pi * (2 * a₁) + Real.pi / 2 * (2 * b₁)) / Complex.exp (Real.pi * (2 * a₂) + Real.p …` using `fun a a₁ a₂ b b₁ b₂ => by`. Rewrite using `[← Complex.exp_sub, ← Complex.exp_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ex]`.

Express the relevant statement in the definitionally equal form `_ = _ * (_ * _⁻¹ * _⁻¹)`. Simplify using `only [mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `hs z w` as an intermediate fact. Rewrite `this` using `[key]`.

Simplify using `only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at this ⊢`. Take the linear combination `(-1 / 2 : ℂ) * this`.
-/
theorem hermForm_eq_add_of_lam (u : HolUnif A L g) (u₁ : HolUnif A₁ L₁ g₁) (u₂ : HolUnif A₂ L₂ g₂)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) (T₁ : (Fin g → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ)) (T₂ : (Fin g → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ))
    (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (hT₁ : ∀ z, u₁.ex (T₁ z) = u.ex z ≫ ψ₁) (hT₂ : ∀ z, u₂.ex (T₂ z) = u.ex z ≫ ψ₂)
    {H : Matrix (Fin g) (Fin g) ℂ} {H₁ : Matrix (Fin g₁) (Fin g₁) ℂ} {H₂ : Matrix (Fin g₂) (Fin g₂) ℂ}
    {χ : u.Λ → ℂ} {χ₁ : u₁.Λ → ℂ} {χ₂ : u₂.Λ → ℂ} (hA : u.IsAH H χ) (hA₁ : u₁.IsAH H₁ χ₁)
    (hA₂ : u₂.IsAH H₂ χ₂)
    (h : lam (cls L hL) (𝟙 A) (𝟙 A) = lam (cls L₁ hL₁) ψ₁ ψ₁ + lam (cls L₂ hL₂) ψ₂ ψ₂) (z w : Fin g → ℂ) :
    hermForm H z w = hermForm H₁ (T₁ z) (T₁ w) + hermForm H₂ (T₂ z) (T₂ w) := by
  have hI : ∀ z, u.ex (LinearMap.id (R := ℂ) z) = u.ex z ≫ 𝟙 A := fun z => (Category.comp_id _).symm
  choose c hc hf using factor_diag₂ u u (𝟙 A) LinearMap.id hI hA
  choose c₁ hc₁ hf₁ using factor_diag₂ u u₁ ψ₁ T₁ hT₁ hA₁
  choose c₂ hc₂ hf₂ using factor_diag₂ u u₂ ψ₂ T₂ hT₂ hA₂
  have d : (diagLB L (𝟙 A)).IsLB := LB.isLB_linComb hL _ _
  have d₁ : (diagLB L₁ ψ₁).IsLB := LB.isLB_linComb hL₁ _ _
  have d₂ : (diagLB L₂ ψ₂).IsLB := LB.isLB_linComb hL₂ _ _
  have dd : (LB.div (diagLB L (𝟙 A)) (diagLB L₁ ψ₁)).IsLB := LB.isLB_div d d₁
  set G₁ := (LinearMap.toMatrix' T₁).transpose * H₁ * (LinearMap.toMatrix' T₁).transpose.conjTranspose with hG₁
  set G₂ := (LinearMap.toMatrix' T₂).transpose * H₂ * (LinearMap.toMatrix' T₂).transpose.conjTranspose with hG₂
  have hG₁h : G₁.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hA₁.1
  have hG₂h : G₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hA₂.1
  have hs : ∀ z w, hermForm ((2 : ℂ) • H - (2 : ℂ) • G₁ - (2 : ℂ) • G₂) z w =
      2 * hermForm H z w - 2 * hermForm H₁ (T₁ z) (T₁ w) - 2 * hermForm H₂ (T₂ z) (T₂ w) := fun z w => by
    rw [← hermForm_pull H₁ T₁, ← hermForm_pull H₂ T₂, ← hG₁, ← hG₂]
    simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec]
  have two : IsSelfAdjoint (2 : ℂ) := by simp [IsSelfAdjoint]
  have key := herm_eq_zero (LB.isLB_div dd d₂)
    (by rw [CechPic.cls_div dd d₂, CechPic.cls_div d d₁, cls_diagLB _ hL, cls_diagLB ψ₁ hL₁,
      cls_diagLB ψ₂ hL₂, h, add_sub_cancel_left, sub_self])
    (SameFactor.divUnif (linCombUnif u u₂ _ _ ![1, -2, 1] (covers₂ u u₂ ψ₂ T₂ hT₂))
      (SameFactor.divUnif (linCombUnif u u₁ _ _ ![1, -2, 1] (covers₂ u u₁ ψ₁ T₁ hT₁))
        (linCombUnif u u _ _ ![1, -2, 1] (covers₂ u u _ _ hI)) rfl) rfl)
    ((2 : ℂ) • H - (2 : ℂ) • G₁ - (2 : ℂ) • G₂) (fun l => c l / c₁ l / c₂ l)
    (((hA.1.smul two).sub (hG₁h.smul two)).sub (hG₂h.smul two))
    (fun l => by rw [norm_div, norm_div, hc l, hc₁ l, hc₂ l]; norm_num) fun l i z hz => by
      obtain ⟨h12, h3⟩ := (top_le_preimage_inf _ _ _).1 hz
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 h12
      have e1 := hf l i.1.1 z h1
      have e2 := hf₁ l i.1.2 z h2
      have e3 := hf₂ l i.2 z h3
      refine (congrArg₂ (fun a b => a * b) (congrArg₂ (fun a b => a * b⁻¹) e1 e2) (congrArg (·⁻¹) e3)).trans ?_
      rw [hs, hs]
      simp only [LinearMap.id_apply]
      have ex : ∀ a a₁ a₂ b b₁ b₂ : ℂ, Complex.exp (Real.pi * (2 * a - 2 * a₁ - 2 * a₂) +
          Real.pi / 2 * (2 * b - 2 * b₁ - 2 * b₂)) = Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) /
          Complex.exp (Real.pi * (2 * a₁) + Real.pi / 2 * (2 * b₁)) /
          Complex.exp (Real.pi * (2 * a₂) + Real.pi / 2 * (2 * b₂)) := fun a a₁ a₂ b b₁ b₂ => by
        rw [← Complex.exp_sub, ← Complex.exp_sub]
        congr 1
        ring
      rw [ex]
      change _ = _ * (_ * _⁻¹ * _⁻¹)
      simp only [mul_inv, div_eq_mul_inv]
      ring
  have := hs z w
  rw [key] at this
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at this ⊢
  linear_combination (-1 / 2 : ℂ) * this

end Sum

section Main

variable {S : Scheme.{0}} {y : Sp ℂ ⟶ S}

/- English proof (translation)
Rewrite using `[CechPic.pull_comp, b.pol, CechPic.pull_lam, lift_fst, lift_snd]`.
-/
theorem lam_eq_pull {P Q : PPAS S} (d : P.RiemannData y) (b : Q.RiemannData y) (x : d.B ⟶ b.B) :
    lam (cls b.L b.isLB) x x = CechPic.pull ((lift x x).left ≫ sqMap b.isPull.1.w) Q.c := by
  rw [CechPic.pull_comp, b.pol, CechPic.pull_lam, lift_fst, lift_snd]

/- English proof (translation)
Use `(Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _)).trans ?_)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_fst x x))`.
-/
theorem lift_sqMap_fst {P Q : PPAS S} (d : P.RiemannData y) (b : Q.RiemannData y) (x : d.B ⟶ b.B) :
    ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.fst _ _ = x.left ≫ b.φ := by
  refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _)).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_fst x x))

/- English proof (translation)
Use `(Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_snd _ _ _)).trans ?_)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_snd x x))`.
-/
theorem lift_sqMap_snd {P Q : PPAS S} (d : P.RiemannData y) (b : Q.RiemannData y) (x : d.B ⟶ b.B) :
    ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.snd _ _ = x.left ≫ b.φ := by
  refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_snd _ _ _)).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_snd x x))

/- English proof (translation)
Rewrite using `[lam_eq_pull d b ψ, ← CechPic.pull_comp]`. Use `congrArg (fun f => CechPic.pull f Q.c) ?_` and prove the remaining obligations. Establish `tf : (π ⊗ₘ π).left ≫ pullback.fst Q.A.hom Q.A.hom = pullback.fst P.A.hom P.A.hom ≫ π.left` using `congrArg CommaMorphism.left (tensorHom_fst π π)`. Establish `ts : (π ⊗ₘ π).left ≫ pullback.snd Q.A.hom Q.A.hom = pullback.snd P.A.hom P.A.hom ≫ π.left` using `congrArg CommaMorphism.left (tensorHom_snd π π)`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, tf, ← Category.assoc, lift_sqMap_fst d d, lift_sqMap_fst d b, e]`. Both sides reduce to the same expression. Rewrite using `[Category.assoc, ts, ← Category.assoc, lift_sqMap_snd d d, lift_sqMap_snd d b, e]`. Both sides reduce to the same expression.
-/
theorem pull_diag_eq {P Q : PPAS S} (d : P.RiemannData y) (b : Q.RiemannData y) (π : P.A ⟶ Q.A)
    (ψ : d.B ⟶ b.B) (e : ψ.left ≫ b.φ = d.φ ≫ π.left) :
    CechPic.pull ((lift (𝟙 d.B) (𝟙 d.B)).left ≫ sqMap d.isPull.1.w) (CechPic.pull (π ⊗ₘ π).left Q.c) =
      lam (cls b.L b.isLB) ψ ψ := by
  rw [lam_eq_pull d b ψ, ← CechPic.pull_comp]
  refine congrArg (fun f => CechPic.pull f Q.c) ?_
  have tf : (π ⊗ₘ π).left ≫ pullback.fst Q.A.hom Q.A.hom = pullback.fst P.A.hom P.A.hom ≫ π.left :=
    congrArg CommaMorphism.left (tensorHom_fst π π)
  have ts : (π ⊗ₘ π).left ≫ pullback.snd Q.A.hom Q.A.hom = pullback.snd P.A.hom P.A.hom ≫ π.left :=
    congrArg CommaMorphism.left (tensorHom_snd π π)
  apply pullback.hom_ext
  · rw [Category.assoc, tf, ← Category.assoc, lift_sqMap_fst d d, lift_sqMap_fst d b, e]
    rfl
  · rw [Category.assoc, ts, ← Category.assoc, lift_sqMap_snd d d, lift_sqMap_snd d b, e]
    rfl

end Main

/- English proof (translation)
Introduce `S P P₁ P₂ π₁ π₂ hπ₁ hπ₂ hc y d d₁ d₂`. Take `⟨ψ₁, e₁⟩` from `SharpPull.exists_lift d.isPull d₁.isPull π₁`. Take `⟨ψ₂, e₂⟩` from `SharpPull.exists_lift d.isPull d₂.isPull π₂`. Establish `hψ₁` using `SharpPull.isMonHom_lift (p := π₁) d.isPull d₁.isPull e₁`. Establish `hψ₂` using `SharpPull.isMonHom_lift (p := π₂) d.isPull d₂.isPull e₂`.

Establish `hA` using `PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull`. Establish `hA₁` using `PolPull.isAbelianScheme_of_isGrpPullback P₁.isAb d₁.isPull`. Establish `hA₂` using `PolPull.isAbelianScheme_of_isGrpPullback P₂.isAb d₂.isPull`. Take `⟨t₁, t₂⟩` from `TorusTransfer.tangent_bijective d₁.u ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d₁.isPull.1 P₁.smoothDim)`. Take `⟨s₁, s₂⟩` from `TorusTransfer.tangent_bijective d₂.u ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d₂.isPull.1 P₂.smoothDim)`.

Take `⟨Q₁, hQ₁, -⟩` from `HomLinear.exists_linear_of_isMonHom d.B d₁.B hA hA₁ d.L d₁.L P.g P₁.g d.u d₁.u t₁ t₂ ψ₁ hψ₁`. Take `⟨Q₂, hQ₂, -⟩` from `HomLinear.exists_linear_of_isMonHom d.B d₂.B hA hA₂ d.L d₂.L P.g P₂.g d.u d₂.u s₁ s₂ ψ₂ hψ₂`. Establish `hlam : lam (cls d.L d.isLB) (𝟙 d.B) (𝟙 d.B) = lam (cls d₁.L d₁.isLB) ψ₁ ψ₁ + lam (cls d₂.L d₂.isLB) ψ₂ ψ₂`. Rewrite using `[lam_eq_pull d d (𝟙 d.B), hc, map_add, pull_diag_eq d d₁ π₁ ψ₁ e₁, pull_diag_eq d d₂ π₂ ψ₂ e₂]`. Use `⟨Q₁, Q₂, fun z => ?_, fun z => ?_, fun z w => ?_⟩` and prove the remaining obligations.

Rewrite using `[hQ₁, Over.comp_left, Category.assoc, e₁]`. Rewrite using `[hQ₂, Over.comp_left, Category.assoc, e₂]`. Conclude with `hermForm_eq_add_of_lam d.u d₁.u d₂.u ψ₁ ψ₂ Q₁ Q₂ d.isLB d₁.isLB d₂.isLB hQ₁ hQ₂ d.isAH d₁.isAH d₂.isAH hlam z w`.
-/
theorem exists_lin_add : ∀ (S : Scheme.{0}) (P P₁ P₂ : PPAS S) (π₁ : P.A ⟶ P₁.A) (π₂ : P.A ⟶ P₂.A), IsMonHom π₁ →
    IsMonHom π₂ → P.c = CechPic.pull (π₁ ⊗ₘ π₁).left P₁.c + CechPic.pull (π₂ ⊗ₘ π₂).left P₂.c →
    ∀ (y : Sp ℂ ⟶ S) (d : P.RiemannData y) (d₁ : P₁.RiemannData y) (d₂ : P₂.RiemannData y),
    ∃ (Q₁ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₁.g → ℂ)) (Q₂ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₂.g → ℂ)),
      (∀ z, (d₁.u.ex (Q₁ z)).left ≫ d₁.φ = (d.u.ex z).left ≫ d.φ ≫ π₁.left) ∧
      (∀ z, (d₂.u.ex (Q₂ z)).left ≫ d₂.φ = (d.u.ex z).left ≫ d.φ ≫ π₂.left) ∧
      ∀ z w, HermFrame.form d.H z w = HermFrame.form d₁.H (Q₁ z) (Q₁ w) + HermFrame.form d₂.H (Q₂ z) (Q₂ w) := by
  intro S P P₁ P₂ π₁ π₂ hπ₁ hπ₂ hc y d d₁ d₂
  obtain ⟨ψ₁, e₁⟩ := SharpPull.exists_lift d.isPull d₁.isPull π₁
  obtain ⟨ψ₂, e₂⟩ := SharpPull.exists_lift d.isPull d₂.isPull π₂
  have hψ₁ := SharpPull.isMonHom_lift (p := π₁) d.isPull d₁.isPull e₁
  have hψ₂ := SharpPull.isMonHom_lift (p := π₂) d.isPull d₂.isPull e₂
  have hA := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull
  have hA₁ := PolPull.isAbelianScheme_of_isGrpPullback P₁.isAb d₁.isPull
  have hA₂ := PolPull.isAbelianScheme_of_isGrpPullback P₂.isAb d₂.isPull
  obtain ⟨t₁, t₂⟩ := TorusTransfer.tangent_bijective d₁.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d₁.isPull.1 P₁.smoothDim)
  obtain ⟨s₁, s₂⟩ := TorusTransfer.tangent_bijective d₂.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d₂.isPull.1 P₂.smoothDim)
  obtain ⟨Q₁, hQ₁, -⟩ := HomLinear.exists_linear_of_isMonHom d.B d₁.B hA hA₁ d.L d₁.L P.g P₁.g d.u d₁.u t₁ t₂
    ψ₁ hψ₁
  obtain ⟨Q₂, hQ₂, -⟩ := HomLinear.exists_linear_of_isMonHom d.B d₂.B hA hA₂ d.L d₂.L P.g P₂.g d.u d₂.u s₁ s₂
    ψ₂ hψ₂
  have hlam : lam (cls d.L d.isLB) (𝟙 d.B) (𝟙 d.B) =
      lam (cls d₁.L d₁.isLB) ψ₁ ψ₁ + lam (cls d₂.L d₂.isLB) ψ₂ ψ₂ := by
    rw [lam_eq_pull d d (𝟙 d.B), hc, map_add, pull_diag_eq d d₁ π₁ ψ₁ e₁, pull_diag_eq d d₂ π₂ ψ₂ e₂]
  refine ⟨Q₁, Q₂, fun z => ?_, fun z => ?_, fun z w => ?_⟩
  · rw [hQ₁, Over.comp_left, Category.assoc, e₁]
  · rw [hQ₂, Over.comp_left, Category.assoc, e₂]
  · exact hermForm_eq_add_of_lam d.u d₁.u d₂.u ψ₁ ψ₂ Q₁ Q₂ d.isLB d₁.isLB d₂.isLB hQ₁ hQ₂ d.isAH d₁.isAH d₂.isAH
      hlam z w

end GlobalTheory.RiemProd
