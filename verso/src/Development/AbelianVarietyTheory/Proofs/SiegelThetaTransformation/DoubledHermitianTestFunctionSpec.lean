import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetOfThickPoints
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFnStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMapStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaMulConjEqBlockThetaStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticDoubledHermitianCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianQuadFormRationalCoordsHermitianStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetDoubledCoordinatesToRationalCoordsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplecticStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblEx

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N Z d b k s t hd hs`. Use function extensionality and compare the values at `⟨a, j⟩`. Establish `h1 : ((s (a, j) : ℚ) : ℂ) = ∑ τ : Ψ, (τ.1 (b k a) * conj (τ.1 (Module.finBasis ℚ E j)) + conj (τ.1 (b k a)) * τ.1 (Module.finBasis ℚ E j))`. Use `trace_eq_sum_embeddings ℂ (K := ℚ) (x := b k a * cc (Module.finBasis ℚ E j))` as an intermediate fact. Rewrite using `[hs, ← eq_ratCast (algebraMap ℚ ℂ), this, ← (RingHom.equivRatAlgHom E ℂ).sum_comp, Dict.sum_type hΨ]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ.1 _ + conj (τ.1 _) = _`. Simplify using `[Base.map_cc]`. Establish `h2 : ∀ (τ : Ψ) c, τ.1 (d k c) = ∑ l, (t (c, l) : ℂ) * τ.1 (Module.finBasis ℚ E l)`. Introduce `τ c`.

Rewrite using `[hd, map_sum]`. Simplify using `[Rat.smul_def]`. Simplify using `only [zetaOf, Pi.add_apply, qv, h1, mulVec, dotProduct, tauOf, Matrix.of_apply, Finset.sum_mul, Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using `only [h2, Fintype.sum_prod_type, map_sum, map_mul, map_ratCast, Finset.sum_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]`. Rewrite using `[add_add_add_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem zetaOf_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (Z : CM Ψ N N) (d b : Matrix (Fin n) (Fin N) E) (k : Fin n) (s t : QI E N → ℚ), (∀ a, d k a = ∑ j, t (a, j) • Module.finBasis ℚ E j) → (∀ a j, s (a, j) = Algebra.trace ℚ E (b k a * cc (Module.finBasis ℚ E j))) → zetaOf Ψ (fun τ => (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) (fun τ => b.map τ.1 + d.map τ.1 * Z τ) k = qv s + tauOf Ψ Z *ᵥ qv t := by
  intro E _ _ _ Ψ hΨ n N Z d b k s t hd hs
  funext ⟨a, j⟩
  have h1 : ((s (a, j) : ℚ) : ℂ) = ∑ τ : Ψ, (τ.1 (b k a) * conj (τ.1 (Module.finBasis ℚ E j)) +
      conj (τ.1 (b k a)) * τ.1 (Module.finBasis ℚ E j)) := by
    have := trace_eq_sum_embeddings ℂ (K := ℚ) (x := b k a * cc (Module.finBasis ℚ E j))
    rw [hs, ← eq_ratCast (algebraMap ℚ ℂ), this,
      ← (RingHom.equivRatAlgHom E ℂ).sum_comp, Dict.sum_type hΨ]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change τ.1 _ + conj (τ.1 _) = _
    simp [Base.map_cc]
  have h2 : ∀ (τ : Ψ) c, τ.1 (d k c) = ∑ l, (t (c, l) : ℂ) * τ.1 (Module.finBasis ℚ E l) := by
    intro τ c
    rw [hd, map_sum]
    simp [Rat.smul_def]
  simp only [zetaOf, Pi.add_apply, qv, h1, mulVec, dotProduct, tauOf, Matrix.of_apply,
    Finset.sum_mul, Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [h2, Fintype.sum_prod_type, map_sum, map_mul, map_ratCast, Finset.sum_mul, mul_add,
    add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  rw [add_add_add_comm]
  congr 1
  · ring
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Introduce `E _ _ _ r X g idx n x₁ hx₁ x₂ hx₂ z z'`. Establish `hk : ∀ τ : X.Ψ, τ.1 X.κ0 ≠ 0` using `fun τ => (map_ne_zero _).2 (DblPer.kappa_ne X)`. Establish `hG : ∀ τ : X.Ψ, IsUnit (X.Gm.map τ.1).det` using `fun τ => (DblPer.det_Gm X τ.1).isUnit`. Establish `hA : ∀ τ, IsUnit (aLin X x₁ x₂ τ).det` using `fun τ => (DblPoint.det_aLin_ne_zero hx₁ hx₂ τ).isUnit`. Establish `hB : ∀ τ, IsUnit (aAnti X x₁ x₂ τ).det` using `fun τ => (DblPoint.det_aAnti_ne_zero hx₁ hx₂ τ).isUnit`.

Set `u : Fin n → X.Ψ → Fin r → ℂ` to `fun k τ => aAnti X x₁ x₂ τ *ᵥ (X.Gm.map τ.1)⁻¹ *ᵥ ((-(τ.1 X.κ0 / 2))⁻¹ • z τ k)`. Set `v : Fin n → X.Ψ → Fin r → ℂ` to `fun k τ => aLin X x₁ x₂ τ *ᵥ (((τ.1 X.κ0 / 2)⁻¹ • z' τ k) ᵥ* (X.Gm.map τ.1)⁻¹)`. Use `⟨fun k i => if ((idx i).2 : ℕ) < X.p0 then u k (idx i).1 (idx i).2 else v k (idx i).1 (idx i).2, fun k i => if ((idx i).2 : ℕ) < X.p0 then v k (idx i).1 (idx i).2 else u k (idx i).1 (idx i).2, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ k`. Simplify using `only [dblz, DblPer.of_row, Equiv.apply_symm_apply]`.

Rewrite using `[show (fun a : Fin r => if (a : ℕ) < X.p0 then (if (a : ℕ) < X.p0 then u k τ a else v k τ a) else (if (a : ℕ) < X.p0 then v k τ a else u k τ a)) = u k τ from`. Apply the tactic sequence `funext fun a => by split_ifs <;> rfl]`. Simplify using `only [u, mulVec_mulVec, ← Matrix.mul_assoc]`. Rewrite using `[nonsing_inv_mul_cancel_right _ _ (hB τ), mul_nonsing_inv _ (hG τ), one_mulVec, smul_inv_smul₀ (neg_ne_zero.2 (div_ne_zero (hk τ) two_ne_zero))]`. Use function extensionality and compare the values at `τ k`.

Simplify using `only [dblz', DblPer.of_row, Equiv.apply_symm_apply]`. Rewrite using `[show (fun a : Fin r => if (a : ℕ) < X.p0 then (if (a : ℕ) < X.p0 then v k τ a else u k τ a) else (if (a : ℕ) < X.p0 then u k τ a else v k τ a)) = v k τ from`. Apply the tactic sequence `funext fun a => by split_ifs <;> rfl]`. Simplify using `only [v, mulVec_mulVec]`. Rewrite using `[nonsing_inv_mul _ (hA τ), one_mulVec, vecMul_vecMul, nonsing_inv_mul _ (hG τ), vecMul_one, smul_inv_smul₀ (div_ne_zero (hk τ) two_ne_zero)]`.
-/
theorem dblz_surj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z z' : CM X.Ψ n r, ∃ z₁ w : Fin n → Fin g → ℂ, dblz X idx x₁ x₂ z₁ w = z ∧ dblz' X idx x₁ x₂ z₁ w = z' := by
  intro E _ _ _ r X g idx n x₁ hx₁ x₂ hx₂ z z'
  have hk : ∀ τ : X.Ψ, τ.1 X.κ0 ≠ 0 := fun τ => (map_ne_zero _).2 (DblPer.kappa_ne X)
  have hG : ∀ τ : X.Ψ, IsUnit (X.Gm.map τ.1).det := fun τ => (DblPer.det_Gm X τ.1).isUnit
  have hA : ∀ τ, IsUnit (aLin X x₁ x₂ τ).det := fun τ =>
    (DblPoint.det_aLin_ne_zero hx₁ hx₂ τ).isUnit
  have hB : ∀ τ, IsUnit (aAnti X x₁ x₂ τ).det := fun τ =>
    (DblPoint.det_aAnti_ne_zero hx₁ hx₂ τ).isUnit
  let u : Fin n → X.Ψ → Fin r → ℂ := fun k τ =>
    aAnti X x₁ x₂ τ *ᵥ (X.Gm.map τ.1)⁻¹ *ᵥ ((-(τ.1 X.κ0 / 2))⁻¹ • z τ k)
  let v : Fin n → X.Ψ → Fin r → ℂ := fun k τ =>
    aLin X x₁ x₂ τ *ᵥ (((τ.1 X.κ0 / 2)⁻¹ • z' τ k) ᵥ* (X.Gm.map τ.1)⁻¹)
  refine ⟨fun k i => if ((idx i).2 : ℕ) < X.p0 then u k (idx i).1 (idx i).2 else v k (idx i).1 (idx i).2,
    fun k i => if ((idx i).2 : ℕ) < X.p0 then v k (idx i).1 (idx i).2 else u k (idx i).1 (idx i).2,
    ?_, ?_⟩
  · funext τ k
    simp only [dblz, DblPer.of_row, Equiv.apply_symm_apply]
    rw [show (fun a : Fin r => if (a : ℕ) < X.p0 then (if (a : ℕ) < X.p0 then u k τ a else v k τ a)
      else (if (a : ℕ) < X.p0 then v k τ a else u k τ a)) = u k τ from
      funext fun a => by split_ifs <;> rfl]
    simp only [u, mulVec_mulVec, ← Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_right _ _ (hB τ), mul_nonsing_inv _ (hG τ), one_mulVec,
      smul_inv_smul₀ (neg_ne_zero.2 (div_ne_zero (hk τ) two_ne_zero))]
  · funext τ k
    simp only [dblz', DblPer.of_row, Equiv.apply_symm_apply]
    rw [show (fun a : Fin r => if (a : ℕ) < X.p0 then (if (a : ℕ) < X.p0 then v k τ a else u k τ a)
      else (if (a : ℕ) < X.p0 then u k τ a else v k τ a)) = v k τ from
      funext fun a => by split_ifs <;> rfl]
    simp only [v, mulVec_mulVec]
    rw [nonsing_inv_mul _ (hA τ), one_mulVec, vecMul_vecMul, nonsing_inv_mul _ (hG τ), vecMul_one,
      smul_inv_smul₀ (div_ne_zero (hk τ) two_ne_zero)]

/- English proof (translation)
Unfold `thS`. Rewrite using `[← (Matrix.reindex (Equiv.refl κ) e).tsum_eq]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `congrArg φ (by ext i j; simp)`.

Use `congr 2`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [dotProduct, mulVec, ← e.sum_comp, qv]`. Simplify using the standard rewrite rules.
-/
theorem thS_reindex {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι' ι' ℂ) (ζ : κ → ι' → ℂ) :
    thS (fun m : Matrix κ ι' ℚ => φ (m.submatrix id e)) τ ζ =
      thS φ (τ.submatrix e e) fun k => ζ k ∘ e := by
  unfold thS
  rw [← (Matrix.reindex (Equiv.refl κ) e).tsum_eq]
  refine tsum_congr fun x => ?_
  congr 1
  · exact congrArg φ (by ext i j; simp)
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [dotProduct, mulVec, ← e.sum_comp, qv]
  simp

/- English proof (translation)
Take `⟨R, hR, h1, h2⟩` from `h`. Use `⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Simplify using `using h1 _ hx k (e.symm i)`. Conclude with `h2 (x.submatrix id e) (y.submatrix id e) fun k i => hy k (e i)`.
-/
theorem isSB_reindex {κ ι ι' : Type} (e : ι ≃ ι')
    {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) :
    IsSB (fun m : Matrix κ ι' ℚ => φ (m.submatrix id e)) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩
  · simpa using h1 _ hx k (e.symm i)
  · exact h2 (x.submatrix id e) (y.submatrix id e) fun k i => hy k (e i)

/- English proof (translation)
Set `R : ((ι' → ℚ) × (ι' → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ))` to `(LinearMap.funLeft ℚ ℚ e).prodMap (LinearMap.funLeft ℚ ℚ e)`. Establish `hd : ∀ a b : ι' → ℚ, (a ∘ e) ⬝ᵥ (b ∘ e) = a ⬝ᵥ b` using `fun a b => e.sum_comp fun i => a i * b i`. Take `⟨σ, hσ, H⟩` from `GlobalTheory.T.exists_symplectic_action_of_period_lattice_map ι (R ∘ₗ F) (fun u v => by`. Rewrite using `[← hF u v, ← hd, ← hd (F u).2]`. Use the proof step `rfl)`.

Take `⟨ω, hω⟩` from `GlobalTheory.T.exists_weil_of_symplectic' κ ι σ hκ hσ`. Take `⟨h1, h2, -⟩` from `hω φ hφ`. Use `⟨_, isSB_reindex e h1, fun τ hτ τ' M hs hM ζ => ?_⟩` and prove the remaining obligations. Take `⟨e1, e2⟩` from `H τ hτ (τ'.submatrix e e) (M.submatrix e id) (hs.submatrix e) (fun u => by`. Use `congrArg (· ∘ e) (hM u)` as an intermediate fact.

Use function extensionality and compare the values at `i`. Establish `h3` using `congrFun (hM u) (e i)`. Simplify using `only [Pi.add_apply, mulVec, dotProduct, ← e.sum_comp] at h3 ⊢`. Conclude with `h3)`. Establish `hD` using `(GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ τ hτ).1`.

Establish `hζ : ∀ k, (M *ᵥ ζ k) ∘ e = ζ k ᵥ* (spDen σ τ)⁻¹` using `fun k => by`. Rewrite using `[← mulVec_transpose, ← e2]`. Both sides reduce to the same expression. Establish `hq : ∀ k, (M *ᵥ ζ k) ⬝ᵥ (τ'.map fun t => (t.im : ℂ))⁻¹ *ᵥ (M *ᵥ ζ k) = (ζ k ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ k ᵥ* (spDen σ τ)⁻¹)` using `fun k => by`. Rewrite using `[← hζ, ← e1, ← submatrix_map, inv_submatrix_equiv]`.

Simplify using `only [mulVec, dotProduct, ← e.sum_comp]`. Both sides reduce to the same expression. Rewrite using `[thS_reindex, e2, e1]`. Simplify using `only [hζ, hq]`. Rewrite using `[h2 τ hτ ζ, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.

Simplify using `only [← GlobalTheory.T.canonicalThetaExponent_symplectic_invariant ι σ hσ τ hτ, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, Complex.exp_add]`. Establish `: (π / 2 * (2 * I * ∑ k, ζ k ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ k) : ℂ) = π * I * ∑ k, ζ k ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ k` using `by ring`. Rewrite using `[this, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem can_trans {κ ι ι' : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι' → ℚ) × (ι' → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1)
    (hκ : Even (Fintype.card κ)) {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) :
    ∃ ψ : Matrix κ ι' ℚ → ℂ, IsSB ψ ∧ ∀ τ ∈ Siegel ι, ∀ (τ' : Matrix ι' ι' ℂ) (M : Matrix ι' ι ℂ),
      τ'.IsSymm → (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      ∀ ζ : κ → ι → ℂ,
        cexp (π / 2 * ∑ k, ζ k ⬝ᵥ (τ.map fun t => (t.im : ℂ))⁻¹ *ᵥ ζ k) * thS φ τ ζ =
          (M.submatrix e id).det ^ (Fintype.card κ / 2) *
            cexp (π / 2 * ∑ k, (M *ᵥ ζ k) ⬝ᵥ (τ'.map fun t => (t.im : ℂ))⁻¹ *ᵥ (M *ᵥ ζ k)) *
              thS ψ τ' fun k => M *ᵥ ζ k := by
  let R : ((ι' → ℚ) × (ι' → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)) :=
    (LinearMap.funLeft ℚ ℚ e).prodMap (LinearMap.funLeft ℚ ℚ e)
  have hd : ∀ a b : ι' → ℚ, (a ∘ e) ⬝ᵥ (b ∘ e) = a ⬝ᵥ b := fun a b => e.sum_comp fun i => a i * b i
  obtain ⟨σ, hσ, H⟩ := GlobalTheory.T.exists_symplectic_action_of_period_lattice_map ι (R ∘ₗ F) (fun u v => by
    rw [← hF u v, ← hd, ← hd (F u).2]; rfl)
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' κ ι σ hκ hσ
  obtain ⟨h1, h2, -⟩ := hω φ hφ
  refine ⟨_, isSB_reindex e h1, fun τ hτ τ' M hs hM ζ => ?_⟩
  obtain ⟨e1, e2⟩ := H τ hτ (τ'.submatrix e e) (M.submatrix e id) (hs.submatrix e) (fun u => by
    have := congrArg (· ∘ e) (hM u)
    funext i
    have h3 := congrFun (hM u) (e i)
    simp only [Pi.add_apply, mulVec, dotProduct, ← e.sum_comp] at h3 ⊢
    exact h3)
  have hD := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ τ hτ).1
  have hζ : ∀ k, (M *ᵥ ζ k) ∘ e = ζ k ᵥ* (spDen σ τ)⁻¹ := fun k => by
    rw [← mulVec_transpose, ← e2]; rfl
  have hq : ∀ k, (M *ᵥ ζ k) ⬝ᵥ (τ'.map fun t => (t.im : ℂ))⁻¹ *ᵥ (M *ᵥ ζ k) =
      (ζ k ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ
        (ζ k ᵥ* (spDen σ τ)⁻¹) := fun k => by
    rw [← hζ, ← e1, ← submatrix_map, inv_submatrix_equiv]
    simp only [mulVec, dotProduct, ← e.sum_comp]
    rfl
  rw [thS_reindex, e2, e1]
  simp only [hζ, hq]
  rw [h2 τ hτ ζ, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  simp only [← GlobalTheory.T.canonicalThetaExponent_symplectic_invariant ι σ hσ τ hτ, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add,
    Complex.exp_add]
  have : (π / 2 * (2 * I * ∑ k, ζ k ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ k) : ℂ) =
      π * I * ∑ k, ζ k ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ k := by ring
  rw [this, inv_pow]
  field_simp

/- English proof (translation)
Establish `h1` using `Dict.sum_type (Base.isType_data X) (fun _ => 1)`. Establish `h2` using `Fintype.card_congr idx`. Simplify using `only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, mul_one, Fintype.card_prod, Fintype.card_fin] at h1 h2`. Establish `h3 : Module.finrank ℚ E = Fintype.card X.Ψ * 2`. Rewrite `h1` using `[one_add_one_eq_two]`.

Conclude with `h1` after adjusting the coercions. Use `Fintype.card_eq.1 ?_` and prove the remaining obligations. Simplify using `only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, h3, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nonempty_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) : Nonempty ((Fin g ⊕ Fin g) ≃ QI E r) := by
  have h1 := Dict.sum_type (Base.isType_data X) (fun _ => 1)
  have h2 := Fintype.card_congr idx
  simp only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_fin] at h1 h2
  have h3 : Module.finrank ℚ E = Fintype.card X.Ψ * 2 := by
    rw [one_add_one_eq_two] at h1; exact_mod_cast h1
  refine Fintype.card_eq.1 ?_
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, h3, h2]
  ring

/- English proof (translation)
Establish `u : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (τ : Matrix ι ι ℂ), τ ∈ Siegel ι → IsUnit (τ.map fun t => (t.im : ℂ)).det` using `fun τ h => by`. Establish `: (τ.map fun t => (t.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im)` using `rfl`. Rewrite using `[this, ← RingHom.map_det]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _ |>.1 h.2.isUnit).map _`. Establish `e : ((Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map fun t => (t.im : ℂ)) = Matrix.fromBlocks (τ₁.map fun t => (t.im : ℂ)) 0 0 (τ₂.map fun t => (t.im : ℂ))`.

Apply the tactic sequence `ext (i | i) (j | j) <;> simp`. Establish `c : ((τ₂.map fun t => (t.im : ℂ))⁻¹).map conj = (τ₂.map fun t => (t.im : ℂ))⁻¹`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Establish `: (τ₂.map fun t => (t.im : ℂ)) = (τ₂.map fun t => (t.im : ℂ)).map conj`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Use `conv_lhs => rw [this]`. Use `enter [1]`. Rewrite using `[← this]`. Rewrite using `[← Matrix.map_mul, nonsing_inv_mul _ (u τ₂ h₂)]`.

Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.inv_eq_left_inv (B := Matrix.fromBlocks (τ₁.map fun t => (t.im : ℂ))⁻¹ 0 0 (τ₂.map fun t => (t.im : ℂ))⁻¹) (by`. Simplify using `[fromBlocks_multiply, nonsing_inv_mul _ (u τ₁ h₁), nonsing_inv_mul _ (u τ₂ h₂)])]`. Rewrite using `[fromBlocks_mulVec, sumElim_dotProduct_sumElim]`. Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]`.

Use `congr 1`. Use `conv_lhs => rw [← c]`. Simplify using `[dotProduct, mulVec]`.
-/
theorem quad_blocks {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (τ₁ : Matrix ι₁ ι₁ ℂ) (τ₂ : Matrix ι₂ ι₂ ℂ) (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂)
    (a : ι₁ → ℂ) (b : ι₂ → ℂ) :
    Sum.elim a (star b) ⬝ᵥ ((Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map
      fun t => (t.im : ℂ))⁻¹ *ᵥ Sum.elim a (star b) =
      a ⬝ᵥ (τ₁.map fun t => (t.im : ℂ))⁻¹ *ᵥ a +
        conj (b ⬝ᵥ (τ₂.map fun t => (t.im : ℂ))⁻¹ *ᵥ b) := by
  have u : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (τ : Matrix ι ι ℂ), τ ∈ Siegel ι →
      IsUnit (τ.map fun t => (t.im : ℂ)).det := fun τ h => by
    have : (τ.map fun t => (t.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := rfl
    rw [this, ← RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 h.2.isUnit).map _
  have e : ((Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map fun t => (t.im : ℂ)) =
      Matrix.fromBlocks (τ₁.map fun t => (t.im : ℂ)) 0 0 (τ₂.map fun t => (t.im : ℂ)) := by
    ext (i | i) (j | j) <;> simp
  have c : ((τ₂.map fun t => (t.im : ℂ))⁻¹).map conj = (τ₂.map fun t => (t.im : ℂ))⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    have : (τ₂.map fun t => (t.im : ℂ)) = (τ₂.map fun t => (t.im : ℂ)).map conj := by
      ext i j; simp
    conv_lhs => rw [this]; enter [1]; rw [← this]
    rw [← Matrix.map_mul, nonsing_inv_mul _ (u τ₂ h₂)]
    simp
  rw [e, Matrix.inv_eq_left_inv (B := Matrix.fromBlocks (τ₁.map fun t => (t.im : ℂ))⁻¹ 0 0
    (τ₂.map fun t => (t.im : ℂ))⁻¹) (by
      simp [fromBlocks_multiply, nonsing_inv_mul _ (u τ₁ h₁), nonsing_inv_mul _ (u τ₂ h₂)])]
  rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  congr 1
  conv_lhs => rw [← c]
  simp [dotProduct, mulVec]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

/- English proof (translation)
Take `⟨e⟩` from `nonempty_equiv X idx`. Establish `hΨ` using `Base.isType_data X`. Take `⟨F, hF, hFu⟩` from `GlobalTheory.T.exists_symplectic_doubled_hermitian_coordinates E r X g bas hs`. Take `⟨hφ, hprod⟩` from `GlobalTheory.T.siegelTheta_mul_conj_eq_blockTheta (Fin n) (Fin g) (Fin g) φ₁ φ₂ h₁ h₂`. Take `⟨ψ, hψ, H⟩` from `can_trans e F hF (by simpa using hn) hφ`.

Take `⟨c, hc⟩` from `GlobalTheory.T.det_doubledCoordinates_to_rationalCoords E r X g idx e`. Set `ψ' : Matrix (Fin n) (Fin r) E → ℂ` to `fun x => c ^ (n / 2) * ψ ((Dict.ofQEquiv E n r).symm x)`. Establish `hψ' : (fun m : Matrix (Fin n) (QI E r) ℚ => ψ' (ofQ m)) = fun m => c ^ (n / 2) * ψ m`. Use function extensionality and compare the values at `m`. Conclude with `congrArg (fun t => c ^ (n / 2) * ψ t) ((Dict.ofQEquiv E n r).symm_apply_apply m)`.

Use `⟨ψ', ?_, fun x₁ hx₁ x₂ hx₂ z₁ w => ?_⟩` and prove the remaining obligations. Rewrite using `[Dict.isSB_iff, hψ']`. Take `⟨R, hR, a, b⟩` from `hψ`. Conclude with `⟨R, hR, fun x hx => a x (right_ne_zero_of_mul hx), fun x y hy => congrArg _ (b x y hy)⟩`. Take `⟨L, hL, hLz⟩` from `hc x₁ x₂`.

Establish `t₁ : tauMat X bas idx x₁ ∈ Siegel (Fin g)` using `⟨tauMat_isSymm idx hs hx₁, tauMat_im_posDef idx hs hx₁⟩`. Establish `t₂ : tauMat X bas idx x₂ ∈ Siegel (Fin g)` using `⟨tauMat_isSymm idx hs hx₂, tauMat_im_posDef idx hs hx₂⟩`. Take `⟨hτ, hth⟩` from `hprod _ t₁ _ t₂`. Establish `hZ` using `DblPoint.dblZ_mem hx₁ hx₂`. Use `set h := Matrix.fromBlocks (hMat X bas idx x₁) 0 0 ((hMat X bas idx x₂).map conj) with hh`.

Establish `hdet : h.det = (hMat X bas idx x₁).det * conj (hMat X bas idx x₂).det`. Rewrite using `[hh, det_fromBlocks_zero₂₁, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hu : IsUnit h.det`. Rewrite using `[hdet]`.

Conclude with `(isUnit_det_hMat idx hs hx₁).mul ((isUnit_det_hMat idx hs hx₂).map _)`. Establish `hv : ∀ a b : Fin g → ℂ, h *ᵥ Sum.elim a (star b) = Sum.elim (hMat X bas idx x₁ *ᵥ a) (star (hMat X bas idx x₂ *ᵥ b))` using `fun a b => by`. Rewrite using `[hh, fromBlocks_mulVec]`. Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[dotProduct, mulVec]`. Establish `hM : ∀ a, (L * h⁻¹) *ᵥ (h *ᵥ a) = L *ᵥ a` using `fun a => by`. Rewrite using `[mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]`. Establish `key` using `H _ hτ (tauOf X.Ψ (dblZ X x₁ x₂)) (L * h⁻¹) (Dict.tauOf_mem hΨ _ hZ).1 (fun u => by`.

Take `⟨a, b⟩` from `hFu u _ _ rfl rfl`. Use `set y₁ := vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) with hy₁`. Use `set y₂ := vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) with hy₂`. Establish `p : qv u.1 + Matrix.fromBlocks (tauMat X bas idx x₁) 0 0 (-((tauMat X bas idx x₂).map conj)) *ᵥ qv u.2 = h *ᵥ Sum.elim (per X x₁ y₁ ∘ idx) (star (per X x₂ y₂ ∘ idx))`. Rewrite using `[hv, hMat_mulVec_per_crd idx hs hx₁, hMat_mulVec_per_crd idx hs hx₂, hy₁, hy₂, crd_vecQ hs, crd_vecQ hs, fromBlocks_mulVec]`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> simp [qv, mulVec, dotProduct]`. Take `⟨d1, d2, -⟩` from `DblPer.dbl_per E r X g bas idx 2 hs even_two x₁ hx₁ x₂ hx₂ (Matrix.of fun _ => y₁) (Matrix.of fun _ => y₂)`. Rewrite using `[p, hM, ← zetaOf_period E X.Ψ hΨ 2 r (dblZ X x₁ x₂) (Matrix.fromCols (Matrix.of fun _ => y₁) (Matrix.of fun _ => y₂) * dblT X).toCols₁ (Matrix.fromCols (Matrix.of fun _ => y₁) (Matrix.of fun _ => y₂) * dblT X).toCols₂ 0 (F u).1 (F u).2 a b, ← funext d1, ← funext d2, hLz]`. Use the proof step `rfl) (fun k => h *ᵥ Sum.elim (z₁ k) (w k))`.

Establish `hw : ∀ k, h *ᵥ Sum.elim (z₁ k) (w k) = Sum.elim (hMat X bas idx x₁ *ᵥ z₁ k) (star (hMat X bas idx x₂ *ᵥ fun i => conj (w k i)))` using `fun k => by`. Rewrite using `[← hv]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `hd2 : ((L * h⁻¹).submatrix e id).det = (L.submatrix e id).det * (h.det)⁻¹`. Rewrite using `[← Ring.inverse_eq_inv', ← Matrix.det_nonsing_inv, ← Matrix.det_mul]`. Both sides reduce to the same expression. Simplify using `only [hM, ← hLz, GlobalTheory.T.gaussian_quadForm_rationalCoords_hermitian E X.Ψ hΨ n r _ hZ, hd2, hL, Fintype.card_fin] at key`. Simplify using `only [hw, quad_blocks _ _ t₁ t₂, ← hth, Finset.sum_add_distrib, mul_add, Complex.exp_add] at key`.

Rewrite using `[Dict.thH_eq, hψ']`. Establish `e1 : thS (fun m => c ^ (n / 2) * ψ m) (tauOf X.Ψ (dblZ X x₁ x₂)) (zetaOf X.Ψ (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = c ^ (n / 2) * thS ψ (tauOf X.Ψ (dblZ X x₁ x₂)) (zetaOf X.Ψ (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w))`. Simplify using `only [thS, mul_assoc, tsum_mul_left]`. Establish `e2 : kZero X idx x₁ x₂ z₁ w = (∏ τ : X.Ψ, ((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det)⁻¹) ^ (n / 2) * cexp (π / 2 * ∑ k, 2 * ∑ τ : X.Ψ, dblz' X idx x₁ x₂ z₁ w τ k ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ dblz X idx x₁ x₂ z₁ w τ k)`. Rewrite using `[kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.prod_pow, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]`.

Simplify using `only [inv_pow]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, thA, thA, imInv_eq, imInv_eq]`. Simplify using `only [map_mul, map_pow, ← Complex.exp_conj, map_div₀, conj_ofReal, map_ofNat, map_sum (starRingEnd ℂ)]`.

Establish `hne : h.det ^ (n / 2) * (h.det⁻¹) ^ (n / 2) = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ hu.ne_zero, one_pow]`. Rewrite `key` using `[mul_pow, mul_pow]`. Establish `hp : (hMat X bas idx x₁).det ^ (n / 2) * conj (hMat X bas idx x₂).det ^ (n / 2) = h.det ^ (n / 2)` using `by rw [hdet, mul_pow]`. Establish `fin : ∀ a₁ a₂ d i c P A A₁ A₂ T T₁ T₂ : ℂ, d * i = 1 → a₁ * a₂ = d → A₁ * A₂ * (T₁ * T₂) = c * P * i * A * T → a₁ * A₁ * T₁ * (a₂ * A₂ * T₂) = P * A * (c * T)`.

Introduce `a₁ a₂ d i c P A A₁ A₂ T T₁ T₂ p q s`. Take the linear combination `(A₁ * A₂ * T₁ * T₂) * q + d * s + (c * P * A * T) * p`. Conclude with `fin _ _ _ _ _ _ _ _ _ _ _ _ hne hp key`.
-/
theorem exists_isDbl (hs : IsSympl X bas) (hn : Even n) {φ₁ φ₂ : TF n g} (h₁ : IsSB φ₁)
    (h₂ : IsSB φ₂) : ∃ ψ, IsSB ψ ∧ IsDbl X bas idx φ₁ φ₂ ψ := by
  obtain ⟨e⟩ := nonempty_equiv X idx
  have hΨ := Base.isType_data X
  obtain ⟨F, hF, hFu⟩ := GlobalTheory.T.exists_symplectic_doubled_hermitian_coordinates E r X g bas hs
  obtain ⟨hφ, hprod⟩ := GlobalTheory.T.siegelTheta_mul_conj_eq_blockTheta (Fin n) (Fin g) (Fin g) φ₁ φ₂ h₁ h₂
  obtain ⟨ψ, hψ, H⟩ := can_trans e F hF (by simpa using hn) hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.det_doubledCoordinates_to_rationalCoords E r X g idx e
  let ψ' : Matrix (Fin n) (Fin r) E → ℂ := fun x => c ^ (n / 2) * ψ ((Dict.ofQEquiv E n r).symm x)
  have hψ' : (fun m : Matrix (Fin n) (QI E r) ℚ => ψ' (ofQ m)) = fun m => c ^ (n / 2) * ψ m := by
    funext m
    exact congrArg (fun t => c ^ (n / 2) * ψ t) ((Dict.ofQEquiv E n r).symm_apply_apply m)
  refine ⟨ψ', ?_, fun x₁ hx₁ x₂ hx₂ z₁ w => ?_⟩
  · rw [Dict.isSB_iff, hψ']
    obtain ⟨R, hR, a, b⟩ := hψ
    exact ⟨R, hR, fun x hx => a x (right_ne_zero_of_mul hx), fun x y hy => congrArg _ (b x y hy)⟩
  obtain ⟨L, hL, hLz⟩ := hc x₁ x₂
  have t₁ : tauMat X bas idx x₁ ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm idx hs hx₁, tauMat_im_posDef idx hs hx₁⟩
  have t₂ : tauMat X bas idx x₂ ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm idx hs hx₂, tauMat_im_posDef idx hs hx₂⟩
  obtain ⟨hτ, hth⟩ := hprod _ t₁ _ t₂
  have hZ := DblPoint.dblZ_mem hx₁ hx₂
  set h := Matrix.fromBlocks (hMat X bas idx x₁) 0 0 ((hMat X bas idx x₂).map conj) with hh
  have hdet : h.det = (hMat X bas idx x₁).det * conj (hMat X bas idx x₂).det := by
    rw [hh, det_fromBlocks_zero₂₁, RingHom.map_det]; rfl
  have hu : IsUnit h.det := by
    rw [hdet]; exact (isUnit_det_hMat idx hs hx₁).mul ((isUnit_det_hMat idx hs hx₂).map _)
  have hv : ∀ a b : Fin g → ℂ, h *ᵥ Sum.elim a (star b) =
      Sum.elim (hMat X bas idx x₁ *ᵥ a) (star (hMat X bas idx x₂ *ᵥ b)) := fun a b => by
    rw [hh, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
    congr 1
    funext i
    simp [dotProduct, mulVec]
  have hM : ∀ a, (L * h⁻¹) *ᵥ (h *ᵥ a) = L *ᵥ a := fun a => by
    rw [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have key := H _ hτ (tauOf X.Ψ (dblZ X x₁ x₂)) (L * h⁻¹) (Dict.tauOf_mem hΨ _ hZ).1 (fun u => by
    obtain ⟨a, b⟩ := hFu u _ _ rfl rfl
    set y₁ := vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) with hy₁
    set y₂ := vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) with hy₂
    have p : qv u.1 + Matrix.fromBlocks (tauMat X bas idx x₁) 0 0
        (-((tauMat X bas idx x₂).map conj)) *ᵥ qv u.2 =
        h *ᵥ Sum.elim (per X x₁ y₁ ∘ idx) (star (per X x₂ y₂ ∘ idx)) := by
      rw [hv, hMat_mulVec_per_crd idx hs hx₁, hMat_mulVec_per_crd idx hs hx₂, hy₁, hy₂,
        crd_vecQ hs, crd_vecQ hs, fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [qv, mulVec, dotProduct]
    obtain ⟨d1, d2, -⟩ := DblPer.dbl_per E r X g bas idx 2 hs even_two x₁ hx₁ x₂ hx₂
      (Matrix.of fun _ => y₁) (Matrix.of fun _ => y₂)
    rw [p, hM, ← zetaOf_period E X.Ψ hΨ 2 r (dblZ X x₁ x₂)
      (Matrix.fromCols (Matrix.of fun _ => y₁) (Matrix.of fun _ => y₂) * dblT X).toCols₁
      (Matrix.fromCols (Matrix.of fun _ => y₁) (Matrix.of fun _ => y₂) * dblT X).toCols₂ 0
      (F u).1 (F u).2 a b, ← funext d1, ← funext d2, hLz]
    rfl) (fun k => h *ᵥ Sum.elim (z₁ k) (w k))
  have hw : ∀ k, h *ᵥ Sum.elim (z₁ k) (w k) = Sum.elim (hMat X bas idx x₁ *ᵥ z₁ k)
      (star (hMat X bas idx x₂ *ᵥ fun i => conj (w k i))) := fun k => by
    rw [← hv]; congr 2; funext i; simp
  have hd2 : ((L * h⁻¹).submatrix e id).det = (L.submatrix e id).det * (h.det)⁻¹ := by
    rw [← Ring.inverse_eq_inv', ← Matrix.det_nonsing_inv, ← Matrix.det_mul]; rfl
  simp only [hM, ← hLz, GlobalTheory.T.gaussian_quadForm_rationalCoords_hermitian E X.Ψ hΨ n r _ hZ, hd2, hL, Fintype.card_fin] at key
  simp only [hw, quad_blocks _ _ t₁ t₂, ← hth, Finset.sum_add_distrib, mul_add,
    Complex.exp_add] at key
  rw [Dict.thH_eq, hψ']
  have e1 : thS (fun m => c ^ (n / 2) * ψ m) (tauOf X.Ψ (dblZ X x₁ x₂))
      (zetaOf X.Ψ (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = c ^ (n / 2) *
      thS ψ (tauOf X.Ψ (dblZ X x₁ x₂))
      (zetaOf X.Ψ (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) := by
    simp only [thS, mul_assoc, tsum_mul_left]
  have e2 : kZero X idx x₁ x₂ z₁ w =
      (∏ τ : X.Ψ, ((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det)⁻¹) ^ (n / 2) *
      cexp (π / 2 * ∑ k, 2 * ∑ τ : X.Ψ, dblz' X idx x₁ x₂ z₁ w τ k ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ
        dblz X idx x₁ x₂ z₁ w τ k) := by
    rw [kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.prod_pow, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_comm]
    simp only [inv_pow]
    congr 2
    ring
  rw [e1, e2, thA, thA, imInv_eq, imInv_eq]
  simp only [map_mul, map_pow, ← Complex.exp_conj, map_div₀, conj_ofReal, map_ofNat, map_sum (starRingEnd ℂ)]
  have hne : h.det ^ (n / 2) * (h.det⁻¹) ^ (n / 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hu.ne_zero, one_pow]
  rw [mul_pow, mul_pow] at key
  have hp : (hMat X bas idx x₁).det ^ (n / 2) * conj (hMat X bas idx x₂).det ^ (n / 2) =
      h.det ^ (n / 2) := by rw [hdet, mul_pow]
  have fin : ∀ a₁ a₂ d i c P A A₁ A₂ T T₁ T₂ : ℂ, d * i = 1 → a₁ * a₂ = d →
      A₁ * A₂ * (T₁ * T₂) = c * P * i * A * T →
      a₁ * A₁ * T₁ * (a₂ * A₂ * T₂) = P * A * (c * T) := by
    intro a₁ a₂ d i c P A A₁ A₂ T T₁ T₂ p q s
    linear_combination (A₁ * A₂ * T₁ * T₂) * q + d * s + (c * P * A * T) * p
  exact fin _ _ _ _ _ _ _ _ _ _ _ _ hne hp key

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs hn φ₁ φ₂ h₁ h₂`. Establish `h` using `exists_isDbl X bas idx hs hn h₁ h₂`. Establish `hd : dbl X bas idx φ₁ φ₂ = h.choose` using `dif_pos h`. Take `⟨a, b⟩` from `hd ▸ h.choose_spec`. Use `⟨a, b, fun ψ hψ hψ' => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `FiniteNet.dom_nonempty X`. Use `(GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E X.Ψ (Base.isType_data X) n r ψ hψ _ (DblPoint.dblZ_mem hx hx)).2 _ a fun z z' => ?_` and prove the remaining obligations. Take `⟨z₁, w, rfl, rfl⟩` from `dblz_surj E r X g idx n x hx x hx z z'`. Establish `hk : kZero X idx x x z₁ w ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => mul_ne_zero (inv_ne_zero (pow_ne_zero _ (mul_ne_zero (DblPoint.det_aLin_ne_zero hx hx τ) (DblPoint.det_aAnti_ne_zero hx hx τ)))) (Complex.exp_ne_zero _)`. Conclude with `mul_left_cancel₀ hk ((hψ' x hx x hx z₁ w).symm.trans (b x hx x hx z₁ w))`.
-/
theorem dbl_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → IsSB (dbl X bas idx φ₁ φ₂) ∧ IsDbl X bas idx φ₁ φ₂ (dbl X bas idx φ₁ φ₂) ∧ ∀ ψ, IsSB ψ → IsDbl X bas idx φ₁ φ₂ ψ → ψ = dbl X bas idx φ₁ φ₂ := by
  intro E _ _ _ r X g bas idx n hs hn φ₁ φ₂ h₁ h₂
  have h := exists_isDbl X bas idx hs hn h₁ h₂
  have hd : dbl X bas idx φ₁ φ₂ = h.choose := dif_pos h
  obtain ⟨a, b⟩ := hd ▸ h.choose_spec
  refine ⟨a, b, fun ψ hψ hψ' => ?_⟩
  obtain ⟨x, hx⟩ := FiniteNet.dom_nonempty X
  refine (GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E X.Ψ (Base.isType_data X) n r ψ hψ _ (DblPoint.dblZ_mem hx hx)).2 _ a
    fun z z' => ?_
  obtain ⟨z₁, w, rfl, rfl⟩ := dblz_surj E r X g idx n x hx x hx z z'
  have hk : kZero X idx x x z₁ w ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ =>
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ (mul_ne_zero (DblPoint.det_aLin_ne_zero hx hx τ)
      (DblPoint.det_aAnti_ne_zero hx hx τ)))) (Complex.exp_ne_zero _)
  exact mul_left_cancel₀ hk ((hψ' x hx x hx z₁ w).symm.trans (b x hx x hx z₁ w))

end GlobalTheory.SW.DblEx
