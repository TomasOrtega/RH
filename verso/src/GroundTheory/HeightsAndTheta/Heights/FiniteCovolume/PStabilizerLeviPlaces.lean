import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviMatrices
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def colMat (v : Basis ι E W) {κ : Type*} (u : κ → W) (w : InfinitePlace E) : Matrix ι κ ℂ :=
  Matrix.of fun i k => vecAt v (u k) w i

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecAt]`.
-/
theorem vecAt_add (v : Basis ι E W) (x y : W) (w : InfinitePlace E) :
    vecAt v (x + y) w = vecAt v x w + vecAt v y w := by
  funext i; simp [vecAt]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecAt]`.
-/
theorem vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[vecAt, Finsupp.single_apply, Pi.single_apply, eq_comm]`.
-/
theorem vecAt_basis (v : Basis ι E W) (i : ι) (w : InfinitePlace E) :
    vecAt v (v i) w = Pi.single i 1 := by
  funext j; simp [vecAt, Finsupp.single_apply, Pi.single_apply, eq_comm]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecAt, colMat, mulVec, dotProduct, map_sum, mul_comm]`.
-/
theorem vecAt_sum_smul (v : Basis ι E W) {κ : Type*} [Fintype κ] (c : κ → E) (u : κ → W)
    (w : InfinitePlace E) :
    vecAt v (∑ k, c k • u k) w = colMat v u w *ᵥ fun k => w.embedding (c k) := by
  funext i
  simp [vecAt, colMat, mulVec, dotProduct, map_sum, mul_comm]

/- English proof (translation)
Use `conv_lhs => rw [← v'.sum_repr x]`. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Conclude with `vecAt_sum_smul v _ _ w`.
-/
theorem vecAt_coe {W' : Submodule E W} {n : ℕ} (v : Basis ι E W) (v' : Basis (Fin n) E W') (x : W')
    (w : InfinitePlace E) :
    vecAt v (x : W) w = colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' x w := by
  conv_lhs => rw [← v'.sum_repr x]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  exact vecAt_sum_smul v _ _ w

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjTranspose_mulVec_colMat (v : Basis ι E W) {κ : Type*} [Fintype κ] (u : κ → W)
    (w : InfinitePlace E) (z : ι → ℂ) (k : κ) :
    ((colMat v u w)ᴴ *ᵥ z) k = star (vecAt v (u k) w) ⬝ᵥ z := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[conjTranspose_apply]`.
-/
theorem conjT_eq {m n : Type*} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j
  simp [conjTranspose_apply]

/- English proof (translation)
Rewrite using `[← unitaryGroupEquivMatrix_apply]`. Both sides reduce to the same expression.
-/
theorem archEmbed_apply (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (w : InfinitePlace E) :
    (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `_ = w.embedding (v.repr (f x) i)`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem map_toMatrix_mulVec_vecAt (v : Basis ι E W) (f : W →ₗ[E] W) (x : W)
    (w : InfinitePlace E) :
    (LinearMap.toMatrix v v f).map w.embedding *ᵥ vecAt v x w = vecAt v (f x) w := by
  funext i
  change _ = w.embedding (v.repr (f x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

variable {h : HermitianForm F E W} {x₀ w₀ : W} {n : ℕ}

/- English proof (translation)
Use extensionality with `k l`. Establish `e` using `sesq_mul (gramAt h v w) (colMat v (fun k => (v' k : W)) w) (colMat v (fun k => (v' k : W)) w) (Pi.single k 1) (Pi.single l 1)`. Rewrite `e` using `[← vecAt_basis v' k w, ← vecAt_basis v' l w, ← vecAt_coe, ← vecAt_coe, ← HermAtPlace.proof, ← hh', vecAt_basis, vecAt_basis]`. Express the relevant statement in the definitionally equal form `w.embedding (h'.toSesq (v' k) (v' l)) = _`. Rewrite using `[← e]`.

Simplify using `[dotProduct, Pi.single_apply]`.
-/
theorem gramAt_complement (v : Basis ι E W) (h' : HermitianForm F E (hypComplement h x₀ w₀))
    (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) (v' : Basis (Fin n) E (hypComplement h x₀ w₀))
    (w : InfinitePlace E) :
    gramAt h' v' w = (colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w := by
  ext k l
  have e := sesq_mul (gramAt h v w) (colMat v (fun k => (v' k : W)) w)
    (colMat v (fun k => (v' k : W)) w) (Pi.single k 1) (Pi.single l 1)
  rw [← vecAt_basis v' k w, ← vecAt_basis v' l w, ← vecAt_coe, ← vecAt_coe,
    ← HermAtPlace.proof, ← hh', vecAt_basis, vecAt_basis] at e
  change w.embedding (h'.toSesq (v' k) (v' l)) = _
  rw [← e]
  simp [dotProduct, Pi.single_apply]

/- English proof (translation)
Use `⟨(GramAtData.proof h v w).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← gramAt_complement v h' hh' v' w]`. Conclude with `(GramAtData.proof h' v' w).2`. Use function extensionality and compare the values at `k`. Rewrite using `[conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply, ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).1, map_zero]`.

Use function extensionality and compare the values at `k`. Rewrite using `[conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply, ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).2, map_zero]`. Rewrite using `[← HermAtPlace.proof, hp.1, map_zero]`. Rewrite using `[← HermAtPlace.proof, hp.2.1, map_zero]`. Rewrite using `[← HermAtPlace.proof, hp.2.2, map_one]`.

Establish `hx : ∀ x : W, vecAt v x w = w.embedding (h.toSesq w₀ x) • vecAt v x₀ w + w.embedding (h.toSesq x₀ x) • vecAt v w₀ w + colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' (ComplementExtension.proj hp x) w`. Introduce `x`. Use `conv_lhs => rw [← ComplementExtension.split hp x]`. Rewrite using `[vecAt_add, vecAt_add, vecAt_smul, vecAt_smul, vecAt_coe v v']`. Normalize the expressions using the abelian group laws.

Introduce `z`. Establish `hz : z = ∑ i, z i • vecAt v (v i) w`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, vecAt_basis, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `⟨∑ i, z i * w.embedding (h.toSesq w₀ (v i)), ∑ i, z i * w.embedding (h.toSesq x₀ (v i)), ∑ i, z i • vecAt v' (ComplementExtension.proj hp (v i)) w, ?_⟩` and prove the remaining obligations.

Establish `hx' : ∀ i, vecAt v (v i) w = _` using `fun i => hx (v i)`. Use `conv_lhs => rw [hz]`. Simplify using `only [hx', smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, mulVec_sum, mulVec_smul]`.
-/
theorem frame (v : Basis ι E W) (hp : IsHyperbolicPair h x₀ w₀)
    (h' : HermitianForm F E (hypComplement h x₀ w₀)) (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y)
    (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    (gramAt h v w)ᴴ = gramAt h v w ∧
    IsUnit ((colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w).det ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 ∧
    ∀ z, ∃ (a b : ℂ) (c : Fin n → ℂ), z = a • vecAt v x₀ w + b • vecAt v w₀ w +
      colMat v (fun k => (v' k : W)) w *ᵥ c := by
  refine ⟨(GramAtData.proof h v w).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← gramAt_complement v h' hh' v' w]
    exact (GramAtData.proof h' v' w).2
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).1, map_zero]
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).2, map_zero]
  · rw [← HermAtPlace.proof, hp.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.2, map_one]
  · have hx : ∀ x : W, vecAt v x w = w.embedding (h.toSesq w₀ x) • vecAt v x₀ w +
        w.embedding (h.toSesq x₀ x) • vecAt v w₀ w +
        colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' (ComplementExtension.proj hp x) w := by
      intro x
      conv_lhs => rw [← ComplementExtension.split hp x]
      rw [vecAt_add, vecAt_add, vecAt_smul, vecAt_smul, vecAt_coe v v']
      abel
    intro z
    have hz : z = ∑ i, z i • vecAt v (v i) w := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, vecAt_basis, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine ⟨∑ i, z i * w.embedding (h.toSesq w₀ (v i)), ∑ i, z i * w.embedding (h.toSesq x₀ (v i)),
      ∑ i, z i • vecAt v' (ComplementExtension.proj hp (v i)) w, ?_⟩
    have hx' : ∀ i, vecAt v (v i) w = _ := fun i => hx (v i)
    conv_lhs => rw [hz]
    simp only [hx', smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, mulVec_sum,
      mulVec_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
