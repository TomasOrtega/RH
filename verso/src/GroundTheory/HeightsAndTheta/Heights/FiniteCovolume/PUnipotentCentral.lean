import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StRationalUnipotent
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipRadicalOfRational
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StImaginaryLatticeCocompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] archMulAction

namespace UnipotentCentral

omit [DecidableEq ι] in

/- English proof (translation)
Establish `hg' : gᴴ * G * g = G`. Conclude with `hg`. Rewrite using `[star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hg', ← dotProduct_mulVec]`.
-/
theorem pair_map {G g : Matrix ι ι ℂ} (hg : (g.map (starRingEnd ℂ))ᵀ * G * g = G)
    (a b : ι → ℂ) : star (g *ᵥ a) ⬝ᵥ (G *ᵥ (g *ᵥ b)) = star a ⬝ᵥ (G *ᵥ b) := by
  have hg' : gᴴ * G * g = G := by
    exact hg
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hg',
    ← dotProduct_mulVec]

omit [DecidableEq ι] in

/- English proof (translation)
Rewrite using `[← star_dotProduct, star_mulVec, hG.eq, dotProduct_mulVec, dotProduct_comm]`.
-/
theorem pair_swap {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a b : ι → ℂ) :
    star b ⬝ᵥ (G *ᵥ a) = star (star a ⬝ᵥ (G *ᵥ b)) := by
  rw [← star_dotProduct, star_mulVec, hG.eq, dotProduct_mulVec, dotProduct_comm]

/- English proof (translation)
Introduce `D La x₀ w₀ hD hx₀ hp K₁ hK₁`. Take `⟨m, hm, hm'⟩` from `h0 D La x₀ w₀ hD hx₀ hp`. Take `⟨R, hR⟩` from `h6 m hm`. Establish `HP` using `HermAtPlace.proof h v`. Establish `GD` using `GramAtData.proof h v`.

Establish `hXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0` using `fun w => by`. Rewrite using `[← HP w, hp.1, map_zero]`. Establish `hYY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0` using `fun w => by`. Rewrite using `[← HP w, hp.2.1, map_zero]`. Establish `hXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1` using `fun w => by`.

Rewrite using `[← HP w, hp.2.2, map_one]`. Establish `hYX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1` using `fun w => by`. Rewrite using `[pair_swap (GD w).1, hXY, star_one]`. Set `f : (InfinitePlace E → ι → ℂ) → InfinitePlace E → ℂ` to `fun k w => star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) + star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2`. Establish `hf : Continuous f`.

Use `continuous_pi fun w => ?_` and prove the remaining obligations. Establish `hk : Continuous fun k : InfinitePlace E → ι → ℂ => k w` using `continuous_apply w`. Conclude with `(continuous_const.dotProduct (continuous_const.matrix_mulVec hk)).add ((hk.star.dotProduct (continuous_const.matrix_mulVec hk)).div_const 2)`. Take `⟨B, hB⟩` from `hK₁.exists_bound_of_continuousOn hf.continuousOn`. Set `box : Set ℂ` to `(fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) '' (Set.Icc (-B) B ×ˢ Set.Icc (-R) R)`.

Establish `hbox : IsCompact box` using `(isCompact_Icc.prod isCompact_Icc).image (by fun_prop)`. Set `T : Set (InfinitePlace E → ℂ)` to `Set.univ.pi fun _ => box`. Establish `hT : IsCompact T` using `isCompact_univ_pi fun _ => hbox`. Set `Φ : (InfinitePlace E → ι → ℂ) × (InfinitePlace E → ℂ) → InfinitePlace E → ι → ℂ` to `fun p => p.1 + fun w => p.2 w • vecAt v x₀ w`. Establish `hΦ : Continuous Φ` using `continuous_fst.add (continuous_pi fun w => ((continuous_apply w).comp continuous_snd).smul continuous_const)`.

Use `⟨Φ '' (K₁ ×ˢ T), (hK₁.prod hT).image hΦ, ?_⟩` and prove the remaining obligations. Introduce and unpack `n ⟨t, ht⟩`. Take `⟨k, hkK, hku⟩ : ∃ k ∈ K₁, unipCoord h v x₀ w₀ n = k + fun w => t w • vecAt v x₀ w` from `⟨_, ht, (sub_add_cancel _ _).symm⟩`. Establish `hnN` using `mem_unipRadical.1 n.2`. Establish `hnU` using `mem_archUnitary.1 (n : archUnitary h v).2`.

Establish `hu : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + (k w + t w • vecAt v x₀ w)`. Introduce `w`. Establish `e` using `congrFun hku w`. Rewrite `e` using `[unipCoord_apply, Pi.add_apply]`. Rewrite using `[← e]`.

Normalize the expressions using the abelian group laws. Establish `hXk : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) = 0`. Introduce `w`. Establish `e` using `pair_map (hnU w) (vecAt v x₀ w) (vecAt v w₀ w)`. Rewrite `e` using `[(hnN w).1, hu w]`.

Simplify using `only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hXX, mul_zero, add_zero] at e`. Take the linear combination `e`. Establish `hkX : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0` using `fun w => by`. Rewrite using `[pair_swap (GD w).1, hXk, star_zero]`. Establish `hkY : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = star (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w))` using `fun w => pair_swap (GD w).1 _ _`.

Establish `hre : ∀ w, (t w).re = -(f k w).re`. Introduce `w`. Establish `e` using `pair_map (hnU w) (vecAt v w₀ w) (vecAt v w₀ w)`. Rewrite `e` using `[hu w, hYY w]`. Simplify using `only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXY, hXk, hkX, hkY, hYY] at e`.

Establish `e2` using `congrArg Complex.re e`. Simplify using `only [mul_one, mul_zero, add_zero, zero_add, Complex.add_re, Complex.zero_re, Complex.star_def, Complex.conj_re] at e2`. Use `show (t w).re = -(star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) + star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2).re`. Rewrite using `[Complex.add_re, Complex.div_ofNat_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hreB : ∀ w, |(t w).re| ≤ B` using `fun w => by`. Rewrite using `[hre w, abs_neg]`. Conclude with `(Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (f k) w).trans (hB k hkK))`. Take `⟨a, ha, hRa⟩` from `hR fun w => -(t w).im`. Establish `hcre : ∀ w : InfinitePlace E, (w.embedding ((m : E) * a)).re = 0`.

Introduce `w`. Establish `e` using `congrArg w.embedding ha`. Rewrite `e` using `[map_add, embedding_conj (F := F) w.embedding, map_zero, Complex.add_conj]`. Establish `e2` using `congrArg Complex.re e`. Simplify using `only [Complex.ofReal_re, Complex.zero_re, mul_eq_zero, two_ne_zero, false_or] at e2`.

Conclude with `e2`. Take `⟨γ, hγLa, hγx, hγw, hγz⟩` from `hm' 0 ((m : E) * a) (Submodule.zero_mem _) ⟨0, zero_mem _, (smul_zero _).symm⟩ ⟨a, rfl⟩ (by rw [ha]; simp)`. Establish `hsymm : h.toSesq w₀ x₀ = 1` using `by rw [← h.isSymm.eq x₀ w₀, hp.2.2, map_one]`. Establish `hγN : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀`. Introduce `z hz`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀`. Rewrite using `[mem_hypComplement, map_sub, map_sub, map_smul, map_smul, hz, hp.1, hsymm]`. Simplify using the standard rewrite rules. Establish `e : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) = z - h.toSesq w₀ z • x₀`.

Use `hγz _ hz'` as an intermediate fact. Rewrite `this` using `[map_zero, LinearMap.zero_apply, zero_smul, sub_zero]`. Conclude with `this`. Establish `hγx' : (γ : W ≃ₗ[E] W) x₀ = x₀` using `hγx`. Establish `hdec : z = h.toSesq w₀ z • x₀ + (z - h.toSesq w₀ z • x₀)` using `by abel`.

Use `show (γ : W ≃ₗ[E] W) z = z + (0 : E) • x₀`. Use `conv_lhs => rw [hdec]`. Rewrite using `[map_add, map_smul, hγx', e, zero_smul, add_zero]`. Normalize the expressions using the abelian group laws. Establish `hδN : archEmbed h v γ ∈ unipRadical h v x₀` using `h4 x₀ γ hγx hγN`.

Use `⟨⟨archEmbed h v γ, hδN⟩, ⟨⟨γ, hγLa⟩, hγx, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hDU` using `mem_archUnitary.1 (archEmbed h v γ).2`. Establish `hD : ∀ (x : W) (w : InfinitePlace E), (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x w = vecAt v (γ • x) w` using `fun x w => by`. Rewrite using `[← archSmul_apply, archEmbed_smul_vecAt]`. Establish `hDY : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + w.embedding ((m : E) * a) • vecAt v x₀ w`.

Introduce `w`. Rewrite using `[hD, hγw]`. Use function extensionality and compare the values at `i`. Simplify using `[vecAt]`. Establish `hDX : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w` using `fun w => by rw [hD, hγx]`.

Establish `hDk : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ k w = k w`. Introduce `w`. Take `⟨b, hb⟩` from `(mem_unipRadical.1 hδN w).2 (k w) (hXk w)`. Establish `e` using `pair_map (hDU w) (vecAt v w₀ w) (k w)`. Rewrite `e` using `[hb, hDY w]`.

Simplify using `only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXk] at e`. Establish `hb0 : b = 0` using `by linear_combination e`. Rewrite using `[hb, hb0, zero_smul, add_zero]`. Establish `hcoord : unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδN⟩ * n) = Φ (k, fun w => t w + w.embedding ((m : E) * a))`. Use function extensionality and compare the values at `w`.

Rewrite using `[unipCoord_apply]`. Express the relevant statement in the definitionally equal form `((((archEmbed h v γ : archUnitary h v) * (n : archUnitary h v) : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w - vecAt v w₀ w = k w + (t w + w.embedding ((m : E) * a)) • vecAt v x₀ w`. Rewrite using `[Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← mulVec_mulVec, hu w, mulVec_add, mulVec_add, mulVec_smul, hDY w, hDX w, hDk w, add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hcoord]`.

Use `Set.mem_image_of_mem Φ ⟨hkK, fun w _ => ?_⟩` and prove the remaining obligations. Use `⟨((t w + w.embedding ((m : E) * a)).re, (t w + w.embedding ((m : E) * a)).im), ⟨?_, ?_⟩, Complex.re_add_im (t w + w.embedding ((m : E) * a))⟩` and prove the remaining obligations. Rewrite using `[Complex.add_re, hcre w, add_zero]`. Conclude with `abs_le.1 (hreB w)`. Rewrite using `[Complex.add_im]`.

Use `abs_le.1 (hRa w)` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.
-/
theorem proof (h : HermitianForm F E W) (v : Basis ι E W) (h0 : RationalUnipotent.Statement h)
    (h4 : UnipRadicalOfRational.Statement h v) (h6 : ImaginaryLatticeCocompact.Statement F E) :
    UnipotentCentral.Statement h v := by
  intro D La x₀ w₀ hD hx₀ hp K₁ hK₁
  obtain ⟨m, hm, hm'⟩ := h0 D La x₀ w₀ hD hx₀ hp
  obtain ⟨R, hR⟩ := h6 m hm
  have HP := HermAtPlace.proof h v
  have GD := GramAtData.proof h v
  have hXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← HP w, hp.1, map_zero]
  have hYY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 := fun w => by
    rw [← HP w, hp.2.1, map_zero]
  have hXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 := fun w => by
    rw [← HP w, hp.2.2, map_one]
  have hYX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1 := fun w => by
    rw [pair_swap (GD w).1, hXY, star_one]

  let f : (InfinitePlace E → ι → ℂ) → InfinitePlace E → ℂ := fun k w =>
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) + star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2
  have hf : Continuous f := by
    refine continuous_pi fun w => ?_
    have hk : Continuous fun k : InfinitePlace E → ι → ℂ => k w := continuous_apply w
    exact (continuous_const.dotProduct (continuous_const.matrix_mulVec hk)).add
      ((hk.star.dotProduct (continuous_const.matrix_mulVec hk)).div_const 2)
  obtain ⟨B, hB⟩ := hK₁.exists_bound_of_continuousOn hf.continuousOn

  let box : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) ''
    (Set.Icc (-B) B ×ˢ Set.Icc (-R) R)
  have hbox : IsCompact box := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  let T : Set (InfinitePlace E → ℂ) := Set.univ.pi fun _ => box
  have hT : IsCompact T := isCompact_univ_pi fun _ => hbox
  let Φ : (InfinitePlace E → ι → ℂ) × (InfinitePlace E → ℂ) → InfinitePlace E → ι → ℂ :=
    fun p => p.1 + fun w => p.2 w • vecAt v x₀ w
  have hΦ : Continuous Φ := continuous_fst.add (continuous_pi fun w =>
    ((continuous_apply w).comp continuous_snd).smul continuous_const)
  refine ⟨Φ '' (K₁ ×ˢ T), (hK₁.prod hT).image hΦ, ?_⟩
  rintro n ⟨t, ht⟩
  obtain ⟨k, hkK, hku⟩ : ∃ k ∈ K₁, unipCoord h v x₀ w₀ n = k + fun w => t w • vecAt v x₀ w :=
    ⟨_, ht, (sub_add_cancel _ _).symm⟩

  have hnN := mem_unipRadical.1 n.2
  have hnU := mem_archUnitary.1 (n : archUnitary h v).2
  have hu : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      vecAt v w₀ w = vecAt v w₀ w + (k w + t w • vecAt v x₀ w) := by
    intro w
    have e := congrFun hku w
    rw [unipCoord_apply, Pi.add_apply] at e
    rw [← e]
    abel
  have hXk : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) = 0 := by
    intro w
    have e := pair_map (hnU w) (vecAt v x₀ w) (vecAt v w₀ w)
    rw [(hnN w).1, hu w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hXX,
      mul_zero, add_zero] at e
    linear_combination e
  have hkX : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [pair_swap (GD w).1, hXk, star_zero]
  have hkY : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) =
      star (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w)) := fun w => pair_swap (GD w).1 _ _
  have hre : ∀ w, (t w).re = -(f k w).re := by
    intro w
    have e := pair_map (hnU w) (vecAt v w₀ w) (vecAt v w₀ w)
    rw [hu w, hYY w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXY, hXk, hkX, hkY, hYY] at e
    have e2 := congrArg Complex.re e
    simp only [mul_one, mul_zero, add_zero, zero_add, Complex.add_re, Complex.zero_re,
      Complex.star_def, Complex.conj_re] at e2
    show (t w).re = -(star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) +
      star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2).re
    rw [Complex.add_re, Complex.div_ofNat_re]
    linarith
  have hreB : ∀ w, |(t w).re| ≤ B := fun w => by
    rw [hre w, abs_neg]
    exact (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (f k) w).trans (hB k hkK))

  obtain ⟨a, ha, hRa⟩ := hR fun w => -(t w).im
  have hcre : ∀ w : InfinitePlace E, (w.embedding ((m : E) * a)).re = 0 := by
    intro w
    have e := congrArg w.embedding ha
    rw [map_add, embedding_conj (F := F) w.embedding, map_zero, Complex.add_conj] at e
    have e2 := congrArg Complex.re e
    simp only [Complex.ofReal_re, Complex.zero_re, mul_eq_zero, two_ne_zero, false_or] at e2
    exact e2
  obtain ⟨γ, hγLa, hγx, hγw, hγz⟩ := hm' 0 ((m : E) * a) (Submodule.zero_mem _)
    ⟨0, zero_mem _, (smul_zero _).symm⟩ ⟨a, rfl⟩
    (by rw [ha]; simp)
  have hsymm : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hp.2.2, map_one]
  have hγN : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀ := by
    intro z hz
    refine ⟨0, ?_⟩
    have hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀ := by
      rw [mem_hypComplement, map_sub, map_sub, map_smul, map_smul, hz, hp.1, hsymm]
      simp
    have e : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) = z - h.toSesq w₀ z • x₀ := by
      have := hγz _ hz'
      rw [map_zero, LinearMap.zero_apply, zero_smul, sub_zero] at this
      exact this
    have hγx' : (γ : W ≃ₗ[E] W) x₀ = x₀ := hγx
    have hdec : z = h.toSesq w₀ z • x₀ + (z - h.toSesq w₀ z • x₀) := by abel
    show (γ : W ≃ₗ[E] W) z = z + (0 : E) • x₀
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hγx', e, zero_smul, add_zero]
    abel
  have hδN : archEmbed h v γ ∈ unipRadical h v x₀ := h4 x₀ γ hγx hγN
  refine ⟨⟨archEmbed h v γ, hδN⟩, ⟨⟨γ, hγLa⟩, hγx, rfl⟩, ?_⟩
  have hDU := mem_archUnitary.1 (archEmbed h v γ).2
  have hD : ∀ (x : W) (w : InfinitePlace E),
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w = vecAt v (γ • x) w := fun x w => by
    rw [← archSmul_apply, archEmbed_smul_vecAt]
  have hDY : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + w.embedding ((m : E) * a) • vecAt v x₀ w := by
    intro w
    rw [hD, hγw]
    funext i
    simp [vecAt]
  have hDX : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w := fun w => by rw [hD, hγx]
  have hDk : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ k w = k w := by
    intro w
    obtain ⟨b, hb⟩ := (mem_unipRadical.1 hδN w).2 (k w) (hXk w)
    have e := pair_map (hDU w) (vecAt v w₀ w) (k w)
    rw [hb, hDY w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXk] at e
    have hb0 : b = 0 := by linear_combination e
    rw [hb, hb0, zero_smul, add_zero]
  have hcoord : unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδN⟩ * n) =
      Φ (k, fun w => t w + w.embedding ((m : E) * a)) := by
    funext w
    rw [unipCoord_apply]
    change ((((archEmbed h v γ : archUnitary h v) * (n : archUnitary h v) : archUnitary h v) :
      InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w - vecAt v w₀ w =
      k w + (t w + w.embedding ((m : E) * a)) • vecAt v x₀ w
    rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← mulVec_mulVec, hu w, mulVec_add,
      mulVec_add, mulVec_smul, hDY w, hDX w, hDk w, add_smul]
    abel
  rw [hcoord]
  refine Set.mem_image_of_mem Φ ⟨hkK, fun w _ => ?_⟩
  refine ⟨((t w + w.embedding ((m : E) * a)).re, (t w + w.embedding ((m : E) * a)).im),
    ⟨?_, ?_⟩, Complex.re_add_im (t w + w.embedding ((m : E) * a))⟩
  · rw [Complex.add_re, hcre w, add_zero]
    exact abs_le.1 (hreB w)
  · rw [Complex.add_im]
    have := abs_le.1 (hRa w)
    constructor <;> linarith [this.1, this.2]

end UnipotentCentral

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
