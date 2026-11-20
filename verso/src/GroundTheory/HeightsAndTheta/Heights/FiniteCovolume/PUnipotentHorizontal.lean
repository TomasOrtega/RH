import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StRationalUnipotent
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipRadicalOfRational
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementArchCocompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviPlaces
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMahlerCompactness
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

/- English proof (translation)
Use `ArchInvariant.proof h v g⁻¹ (fun _ => a) (fun _ => b) w` as an intermediate fact. Simplify `this` using `only [invApply, inv_inv]`.
-/
theorem archUnitary_preserves_form (h : HermitianForm F E W) (v : Basis ι E W)
    (g : archUnitary h v) (w : InfinitePlace E) (a b : ι → ℂ) :
    star (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ a) ⬝ᵥ
        (gramAt h v w *ᵥ (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ b)) =
      star a ⬝ᵥ (gramAt h v w *ᵥ b) := by
  have := ArchInvariant.proof h v g⁻¹ (fun _ => a) (fun _ => b) w
  simpa only [invApply, inv_inv] using this

/- English proof (translation)
Introduce `D La x₀ w₀ hD hx₀ hp`. Take `⟨m, hm, hγ⟩` from `h0 D La x₀ w₀ hD hx₀ hp`. Take `⟨K5, hK5, hK⟩` from `h5 La x₀ w₀ (2 * m) hD.isLattice hp (by omega)`. Use `⟨-K5, hK5.neg, fun n => ?_⟩` and prove the remaining obligations. Take `⟨hxx, -, hxw⟩` from `hp`.

Establish `hwx : h.toSesq w₀ x₀ = 1`. Rewrite using `[← LinearMap.isSymm_def.mp h.isSymm x₀ w₀, hxw, map_one]`. Establish `hH` using `HermAtPlace.proof h v`. Establish `bXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0` using `fun w => by`. Rewrite using `[← hH, hxx, map_zero]`.

Establish `bWX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1` using `fun w => by`. Rewrite using `[← hH, hwx, map_one]`. Establish `hn` using `mem_unipRadical.1 n.2`. Take `⟨u, hu⟩ : ∃ u, u = unipCoord h v x₀ w₀ n` from `⟨_, rfl⟩`. Establish `bXu : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) = 0` using `fun w => by`.

Establish `e` using `archUnitary_preserves_form h v n w (vecAt v x₀ w) (vecAt v w₀ w)`. Rewrite `e` using `[(hn w).1]`. Rewrite using `[hu, unipCoord_apply, mulVec_sub, dotProduct_sub, e, sub_self]`. Take `⟨t0, ht0⟩ : ∃ t0 : InfinitePlace E → ℂ, ∀ w, t0 w = star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w)` from `⟨fun _ => _, fun _ => rfl⟩`. Take `⟨Y, hY⟩ : ∃ Y : InfinitePlace E → ι → ℂ, ∀ w, Y w = u w - t0 w • vecAt v x₀ w` from `⟨fun _ => _, fun _ => rfl⟩`.

Establish `bXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0` using `fun w => by`. Rewrite using `[hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bXu, bXX, smul_zero, sub_zero]`. Establish `bWY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0` using `fun w => by`. Rewrite using `[hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bWX, ← ht0, smul_eq_mul, mul_one, sub_self]`. Take `⟨y, hyW, ⟨z, hzLa, hyz⟩, hyK⟩` from `hK (-Y) fun w => by`.

Simplify using `only [Pi.neg_apply, mulVec_neg, dotProduct_neg, neg_eq_zero]`. Conclude with `⟨bXY w, bWY w⟩`. Establish `hzz : h.toSesq z z ∈ integralClosure ℤ E` using `hD.integral z hzLa z hzLa`. Establish `hzzc : conj F E (h.toSesq z z) = h.toSesq z z` using `LinearMap.isSymm_def.mp h.isSymm z z`. Set `a : 𝓞 E` to `-((2 * m : ℕ) : 𝓞 E) * ⟨h.toSesq z z, hzz⟩`.

Establish `haE : (a : E) = -((2 * m : ℕ) : E) * h.toSesq z z`. Establish `h2 : (((2 * m : ℕ) : 𝓞 E) : E) = ((2 * m : ℕ) : E)` using `map_natCast (algebraMap (𝓞 E) E) (2 * m)`. Rewrite using `[show (a : E) = -(((2 * m : ℕ) : 𝓞 E) : E) * h.toSesq z z from rfl, h2]`. Set `c : E` to `(m : E) * (a : E)`. Establish `hyy : h.toSesq y y = ((2 * m : ℕ) : E) * ((2 * m : ℕ) : E) * h.toSesq z z`.

Rewrite using `[hyz]`. Simplify using `only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : c + conj F E c = -h.toSesq y y`. Simplify using `only [c, hyy, haE, map_mul, map_neg, map_natCast, hzzc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨γ, hγLa, hγx, hγw, hγz⟩` from `hγ y c hyW ⟨2 • z, nsmul_mem hzLa 2, by rw [hyz, smul_smul, mul_comm]⟩ ⟨a, rfl⟩ hc`. Establish `hgood : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀`. Introduce `z hz`.

Establish `hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀`. Rewrite using `[mem_hypComplement]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[map_sub, map_smul, hz, hxx, smul_zero, sub_zero]`. Rewrite using `[map_sub, map_smul, hwx, smul_eq_mul, mul_one, sub_self]`.

Use `⟨-h.toSesq y (z - h.toSesq w₀ z • x₀), ?_⟩` and prove the remaining obligations. Establish `e : (γ : W ≃ₗ[E] W) z = (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) + h.toSesq w₀ z • (γ : W ≃ₗ[E] W) x₀`. Rewrite using `[← map_smul, ← map_add, sub_add_cancel]`. Establish `e1 : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) = (z - h.toSesq w₀ z • x₀) - h.toSesq y (z - h.toSesq w₀ z • x₀) • x₀` using `hγz _ hz'`. Establish `e2 : (γ : W ≃ₗ[E] W) x₀ = x₀` using `hγx`.

Express the relevant statement in the definitionally equal form `(γ : W ≃ₗ[E] W) z = _`. Rewrite using `[e, e1, e2, neg_smul]`. Normalize the expressions using the abelian group laws. Establish `hδ` using `h4 x₀ γ hγx hgood`. Establish `hδw` using `mem_unipRadical.1 hδ`.

Establish `hs : ∀ w, ∃ s : ℂ, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ Y w = Y w + s • vecAt v x₀ w` using `fun w => (hδw w).2 (Y w) (bXY w)`. Use `choose s hs using hs`. Use `⟨⟨archEmbed h v γ, hδ⟩, Subgroup.mem_map.2 ⟨⟨γ, hγLa⟩, MulAction.mem_stabilizer_iff.2 hγx, rfl⟩, fun w => w.embedding c + t0 w + s w, ?_⟩` and prove the remaining obligations. Establish `hprod : ∀ w, unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδ⟩ * n) w = (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ ((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w) - vecAt v w₀ w` using `fun w => by`. Rewrite using `[unipCoord_apply, Matrix.mulVec_mulVec]`.

Both sides reduce to the same expression. Establish `hdW : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + vecAt v y w + w.embedding c • vecAt v x₀ w` using `fun w => by`. Rewrite using `[← vecAt_unitary, show (γ : W ≃ₗ[E] W) w₀ = γ • w₀ from rfl, hγw, StabilizerLevi.vecAt_add, StabilizerLevi.vecAt_add, StabilizerLevi.vecAt_smul]`. Establish `hgW : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = u w + vecAt v w₀ w` using `fun w => by`. Rewrite using `[hu, unipCoord_apply, sub_add_cancel]`.

Establish `huY : ∀ w, u w = Y w + t0 w • vecAt v x₀ w` using `fun w => by rw [hY, sub_add_cancel]`. Rewrite using `[Set.mem_neg]`. Use `hyK using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.neg_apply, Pi.sub_apply, hprod w, hgW w, huY w, mulVec_add, mulVec_smul, hs w, (hδw w).1, hdW w, add_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem UnipotentHorizontal.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h0 : RationalUnipotent.Statement h) (h4 : UnipRadicalOfRational.Statement h v)
    (h5 : ComplementArchCocompact.Statement h v) : UnipotentHorizontal.Statement h v := by
  intro D La x₀ w₀ hD hx₀ hp
  obtain ⟨m, hm, hγ⟩ := h0 D La x₀ w₀ hD hx₀ hp
  obtain ⟨K5, hK5, hK⟩ := h5 La x₀ w₀ (2 * m) hD.isLattice hp (by omega)
  refine ⟨-K5, hK5.neg, fun n => ?_⟩
  obtain ⟨hxx, -, hxw⟩ := hp
  have hwx : h.toSesq w₀ x₀ = 1 := by
    rw [← LinearMap.isSymm_def.mp h.isSymm x₀ w₀, hxw, map_one]
  have hH := HermAtPlace.proof h v
  have bXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← hH, hxx, map_zero]
  have bWX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1 := fun w => by
    rw [← hH, hwx, map_one]
  have hn := mem_unipRadical.1 n.2

  obtain ⟨u, hu⟩ : ∃ u, u = unipCoord h v x₀ w₀ n := ⟨_, rfl⟩
  have bXu : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) = 0 := fun w => by
    have e := archUnitary_preserves_form h v n w (vecAt v x₀ w) (vecAt v w₀ w)
    rw [(hn w).1] at e
    rw [hu, unipCoord_apply, mulVec_sub, dotProduct_sub, e, sub_self]
  obtain ⟨t0, ht0⟩ : ∃ t0 : InfinitePlace E → ℂ,
      ∀ w, t0 w = star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) := ⟨fun _ => _, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : InfinitePlace E → ι → ℂ,
      ∀ w, Y w = u w - t0 w • vecAt v x₀ w := ⟨fun _ => _, fun _ => rfl⟩
  have bXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 := fun w => by
    rw [hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bXu, bXX, smul_zero,
      sub_zero]
  have bWY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 := fun w => by
    rw [hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bWX, ← ht0, smul_eq_mul,
      mul_one, sub_self]

  obtain ⟨y, hyW, ⟨z, hzLa, hyz⟩, hyK⟩ := hK (-Y) fun w => by
    simp only [Pi.neg_apply, mulVec_neg, dotProduct_neg, neg_eq_zero]
    exact ⟨bXY w, bWY w⟩
  have hzz : h.toSesq z z ∈ integralClosure ℤ E := hD.integral z hzLa z hzLa
  have hzzc : conj F E (h.toSesq z z) = h.toSesq z z := LinearMap.isSymm_def.mp h.isSymm z z
  let a : 𝓞 E := -((2 * m : ℕ) : 𝓞 E) * ⟨h.toSesq z z, hzz⟩
  have haE : (a : E) = -((2 * m : ℕ) : E) * h.toSesq z z := by
    have h2 : (((2 * m : ℕ) : 𝓞 E) : E) = ((2 * m : ℕ) : E) :=
      map_natCast (algebraMap (𝓞 E) E) (2 * m)
    rw [show (a : E) = -(((2 * m : ℕ) : 𝓞 E) : E) * h.toSesq z z from rfl, h2]
  let c : E := (m : E) * (a : E)
  have hyy : h.toSesq y y = ((2 * m : ℕ) : E) * ((2 * m : ℕ) : E) * h.toSesq z z := by
    rw [hyz]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hc : c + conj F E c = -h.toSesq y y := by
    simp only [c, hyy, haE, map_mul, map_neg, map_natCast, hzzc]
    push_cast
    ring
  obtain ⟨γ, hγLa, hγx, hγw, hγz⟩ := hγ y c hyW
    ⟨2 • z, nsmul_mem hzLa 2, by rw [hyz, smul_smul, mul_comm]⟩ ⟨a, rfl⟩ hc

  have hgood : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀ := by
    intro z hz
    have hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀ := by
      rw [mem_hypComplement]
      constructor
      · rw [map_sub, map_smul, hz, hxx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hwx, smul_eq_mul, mul_one, sub_self]
    refine ⟨-h.toSesq y (z - h.toSesq w₀ z • x₀), ?_⟩
    have e : (γ : W ≃ₗ[E] W) z = (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) +
        h.toSesq w₀ z • (γ : W ≃ₗ[E] W) x₀ := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    have e1 : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) =
        (z - h.toSesq w₀ z • x₀) - h.toSesq y (z - h.toSesq w₀ z • x₀) • x₀ := hγz _ hz'
    have e2 : (γ : W ≃ₗ[E] W) x₀ = x₀ := hγx
    change (γ : W ≃ₗ[E] W) z = _
    rw [e, e1, e2, neg_smul]
    abel
  have hδ := h4 x₀ γ hγx hgood
  have hδw := mem_unipRadical.1 hδ
  have hs : ∀ w, ∃ s : ℂ, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ Y w = Y w + s • vecAt v x₀ w := fun w => (hδw w).2 (Y w) (bXY w)
  choose s hs using hs
  refine ⟨⟨archEmbed h v γ, hδ⟩, Subgroup.mem_map.2 ⟨⟨γ, hγLa⟩, MulAction.mem_stabilizer_iff.2 hγx,
    rfl⟩, fun w => w.embedding c + t0 w + s w, ?_⟩
  have hprod : ∀ w, unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδ⟩ * n) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        ((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w) -
          vecAt v w₀ w := fun w => by
    rw [unipCoord_apply, Matrix.mulVec_mulVec]
    rfl
  have hdW : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + vecAt v y w + w.embedding c • vecAt v x₀ w :=
    fun w => by
      rw [← vecAt_unitary, show (γ : W ≃ₗ[E] W) w₀ = γ • w₀ from rfl, hγw, StabilizerLevi.vecAt_add,
        StabilizerLevi.vecAt_add, StabilizerLevi.vecAt_smul]
  have hgW : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      vecAt v w₀ w = u w + vecAt v w₀ w := fun w => by
    rw [hu, unipCoord_apply, sub_add_cancel]
  have huY : ∀ w, u w = Y w + t0 w • vecAt v x₀ w := fun w => by rw [hY, sub_add_cancel]
  rw [Set.mem_neg]
  convert hyK using 1
  funext w
  simp only [Pi.neg_apply, Pi.sub_apply, hprod w, hgW w, huY w, mulVec_add, mulVec_smul, hs w,
    (hδw w).1, hdW w, add_smul]
  abel

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
