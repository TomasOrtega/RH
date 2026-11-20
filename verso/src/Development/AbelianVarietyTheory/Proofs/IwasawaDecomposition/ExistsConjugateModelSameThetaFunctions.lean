import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyDerivRenameOfConvex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConvexAndDifferentiableOnTsumCexp

noncomputable section

namespace GlobalTheory.OneMapRef.Flip

section Generic

open NumberField Matrix Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Unfold `sgn`. Rewrite using `[Fin.val_rev]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`.
-/
theorem sgn_rev {p q : ℕ} (h : p + q = r) (a : Fin r) : sgn p (a : ℕ) = -sgn q (Fin.rev a : ℕ) := by
  have := a.isLt
  unfold sgn
  rw [Fin.val_rev]
  split_ifs <;> first | omega | simp

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Simplify using `[hermC, ComplexEmbedding.conjugate_coe_eq, map_sum]`.
-/
theorem hermC_flip (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC (ComplexEmbedding.conjugate τ) (-G) (fun a => conj (u a)) (fun a => conj (v a)) =
      -conj (hermC τ G u v) := by
  simp [hermC, ComplexEmbedding.conjugate_coe_eq, map_sum]

/- English proof (translation)
Establish `h : ∀ a b, conj (τ (X.Gm a b)) = τ (X.Gm b a)` using `fun a b => by`. Rewrite using `[← X.Gm_herm a b, cc, IsCMField.complexEmbedding_complexConj]`. Simplify using `only [hermC, map_sum, map_mul, h, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem conj_hermC (X : Data E r) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    conj (hermC τ X.Gm u v) = hermC τ X.Gm v u := by
  have h : ∀ a b, conj (τ (X.Gm a b)) = τ (X.Gm b a) := fun a b => by
    rw [← X.Gm_herm a b, cc, IsCMField.complexEmbedding_complexConj]
  simp only [hermC, map_sum, map_mul, h, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_neg (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) : herm (-G) u v = -herm G u v := by
  simp [herm]

/- English proof (translation)
Establish `hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `fun σ => star_star σ`. Establish `hmem : ∀ σ, σ ∈ X.Ψ.image ComplexEmbedding.conjugate ↔ ComplexEmbedding.conjugate σ ∈ X.Ψ` using `fun σ => by`. Rewrite using `[Finset.mem_image]`. Conclude with `⟨fun ⟨τ, h, e⟩ => by rwa [← e, hcc], fun h => ⟨_, h, hcc σ⟩⟩`. Establish `halg : IsAlgebraic ℤ (X.κ0 / (X.den : E))` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)`.

Take `⟨k, hk, hki⟩` from `halg.exists_integral_multiple`. Establish `hki' : IsIntegral ℤ ((k.natAbs : E) * (X.κ0 / (X.den : E)))`. Rewrite `hki` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq k with h | h` into its components or cases. Rewrite `hki` using `[h, Int.cast_natCast]`.

Conclude with `hki`. Rewrite `hki` using `[h, Int.cast_neg, Int.cast_natCast, neg_mul]`. Simplify using `using hki.neg`. Establish `hd : (X.den : E) ≠ 0` using `by exact_mod_cast X.den_ne`. Take `⟨X', h1, h2, h3, h4, -, h5, -⟩` from `GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski E r p 3 (3 * k.natAbs) (X.Ψ.image ComplexEmbedding.conjugate) (-X.Gm) X.Λ X.ξ0 (-X.κ0) (fun σ => by rw [hmem, hmem]; exact X.cmType _) (fun a b => by rw [Matrix.neg_apply, Matrix.neg_apply, ← X.Gm_herm a b, cc, cc, map_n …`.

Take `⟨τ, hτ, rfl⟩` from `Finset.mem_image.1 hσ`. Take `⟨P, hP0, hP⟩` from `X.signature ⟨τ, hτ⟩`. Use `⟨(P.map conj).submatrix id Fin.revPerm, ?_, ?_⟩` and prove the remaining obligations. Use `RingHom.map_det (starRingEnd ℂ) P` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply]`.

Rewrite using `[Matrix.det_permute', ← this]`. Use `mul_ne_zero ?_ (by simpa using hP0)` and prove the remaining obligations. Conclude with `Units.ne_zero _` after adjusting the coercions. Use extensionality with `a b`. Use `(hermC_flip τ X.Gm (FD.col P a.rev) (FD.col P b.rev)).trans ?_` and prove the remaining obligations.

Use `congrFun (congrFun hP a.rev) b.rev` as an intermediate fact. Rewrite using `[show hermC τ X.Gm (FD.col P a.rev) (FD.col P b.rev) = _ from this, Matrix.diagonal_apply, Matrix.diagonal_apply, sgn_rev (show p + X.p0 = r by omega) a]`. Apply the tactic sequence `by_cases h : a = b <;> simp [h])`. Use the proof step `X.Λ_fg X.Λ_span le_rfl X.ξ0_im X.ξ0_ne`. Apply the tactic sequence `(by rcases X.κ0_xi with h | h <;> simp [h])`.

Use the proof step `(fun σ hσ => by`. Take `⟨τ, hτ, rfl⟩` from `Finset.mem_image.1 hσ`. Simplify `X.κ0_sign ⟨τ, hτ⟩)` using `[ComplexEmbedding.conjugate_coe_eq]`. Use the proof step `(by omega)`. Use the proof step `(fun x hx y hy => by`.

Establish `e : ((3 * k.natAbs : ℕ) : E) / ((3 : ℕ) : E) * -X.κ0 * herm (-X.Gm) x y = (k.natAbs : E) * (X.κ0 / (X.den : E)) * ((X.den : E) * herm X.Gm x y)`. Rewrite using `[herm_neg, Nat.cast_mul, Nat.cast_ofNat]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `hki'.mul (X.Λ_int x hx y hy))`.

Conclude with `⟨X', h1, h2, h3, h4, h5⟩`.
-/
theorem exists_flip (X : Data E r) {p : ℕ} (hq : X.p0 + p = r) : ∃ X' : Data E r,
    X'.Ψ = X.Ψ.image ComplexEmbedding.conjugate ∧ X'.Gm = -X.Gm ∧ X'.p0 = p ∧ X'.Λ = X.Λ ∧ X'.κ0 = -X.κ0 := by
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ := fun σ => star_star σ
  have hmem : ∀ σ, σ ∈ X.Ψ.image ComplexEmbedding.conjugate ↔ ComplexEmbedding.conjugate σ ∈ X.Ψ := fun σ => by
    rw [Finset.mem_image]
    exact ⟨fun ⟨τ, h, e⟩ => by rwa [← e, hcc], fun h => ⟨_, h, hcc σ⟩⟩
  have halg : IsAlgebraic ℤ (X.κ0 / (X.den : E)) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  have hki' : IsIntegral ℤ ((k.natAbs : E) * (X.κ0 / (X.den : E))) := by
    rw [zsmul_eq_mul] at hki
    rcases Int.natAbs_eq k with h | h
    · rw [h, Int.cast_natCast] at hki; exact hki
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at hki; simpa using hki.neg
  have hd : (X.den : E) ≠ 0 := by exact_mod_cast X.den_ne
  obtain ⟨X', h1, h2, h3, h4, -, h5, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski E r p 3 (3 * k.natAbs)
    (X.Ψ.image ComplexEmbedding.conjugate) (-X.Gm) X.Λ X.ξ0 (-X.κ0)
    (fun σ => by rw [hmem, hmem]; exact X.cmType _)
    (fun a b => by rw [Matrix.neg_apply, Matrix.neg_apply, ← X.Gm_herm a b, cc, cc, map_neg])
    (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) X.Gm_det)
    (by omega)
    (fun σ hσ => by
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
      obtain ⟨P, hP0, hP⟩ := X.signature ⟨τ, hτ⟩
      refine ⟨(P.map conj).submatrix id Fin.revPerm, ?_, ?_⟩
      · have := RingHom.map_det (starRingEnd ℂ) P
        rw [RingHom.mapMatrix_apply] at this
        rw [Matrix.det_permute', ← this]
        refine mul_ne_zero ?_ (by simpa using hP0)
        exact_mod_cast Units.ne_zero _
      · ext a b
        refine (hermC_flip τ X.Gm (FD.col P a.rev) (FD.col P b.rev)).trans ?_
        have := congrFun (congrFun hP a.rev) b.rev
        rw [show hermC τ X.Gm (FD.col P a.rev) (FD.col P b.rev) = _ from this,
          Matrix.diagonal_apply, Matrix.diagonal_apply, sgn_rev (show p + X.p0 = r by omega) a]
        by_cases h : a = b <;> simp [h])
    X.Λ_fg X.Λ_span le_rfl X.ξ0_im X.ξ0_ne
    (by rcases X.κ0_xi with h | h <;> simp [h])
    (fun σ hσ => by
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
      simpa [ComplexEmbedding.conjugate_coe_eq] using X.κ0_sign ⟨τ, hτ⟩)
    (by omega)
    (fun x hx y hy => by
      have e : ((3 * k.natAbs : ℕ) : E) / ((3 : ℕ) : E) * -X.κ0 * herm (-X.Gm) x y =
          (k.natAbs : E) * (X.κ0 / (X.den : E)) * ((X.den : E) * herm X.Gm x y) := by
        rw [herm_neg, Nat.cast_mul, Nat.cast_ofNat]
        field_simp
      rw [e]
      exact hki'.mul (X.Λ_int x hx y hy))
  exact ⟨X', h1, h2, h3, h4, h5⟩

/- English proof (translation)
Establish `e : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ), hermC τ X.Gm w (FD.col N a) = ((Nᴴ * (X.Gm.map τ)ᵀ) *ᵥ w) a` using `fun N w => by`. Simplify using `only [hermC, FD.col, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, transpose_apply, map_apply, Finset.sum_mul, RCLike.star_def]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Establish `h2 : Mᴴ * (X.Gm.map τ)ᵀ * M = sgnM X`. Establish `ht : (sgnM X)ᵀ = sgnM X` using `Matrix.diagonal_transpose _`.

Rewrite using `[← ht, ← h]`. Use extensionality with `a b`. Simplify using `only [FD.gram, hermC, FD.col, Matrix.mul_apply, conjTranspose_apply, transpose_apply, map_apply, Finset.sum_mul, RCLike.star_def, of_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `⟨Ker.ONBasis.isUnit_det (Ker.ONBasis.sgnM_sq X) h2, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, Ker.ONBasis.adj_mul (Ker.ONBasis.sgnM_sq X) h2, ← mulVec_mulVec, sgnM, mulVec_diagonal]`.
-/
theorem herm_col {X : Data E r} {τ : E →+* ℂ} {M : Matrix (Fin r) (Fin r) ℂ} (h : FD.gram τ X.Gm M = sgnM X)
    (v : Fin r → ℂ) (a : Fin r) :
    IsUnit M.det ∧ hermC τ X.Gm v (FD.col M a) = (sgn X.p0 a : ℝ) * (M⁻¹ *ᵥ v) a := by
  have e : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ),
      hermC τ X.Gm w (FD.col N a) = ((Nᴴ * (X.Gm.map τ)ᵀ) *ᵥ w) a := fun N w => by
    simp only [hermC, FD.col, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, transpose_apply,
      map_apply, Finset.sum_mul, RCLike.star_def]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : Mᴴ * (X.Gm.map τ)ᵀ * M = sgnM X := by
    have ht : (sgnM X)ᵀ = sgnM X := Matrix.diagonal_transpose _
    rw [← ht, ← h]
    ext a b
    simp only [FD.gram, hermC, FD.col, Matrix.mul_apply, conjTranspose_apply, transpose_apply,
      map_apply, Finset.sum_mul, RCLike.star_def, of_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨Ker.ONBasis.isUnit_det (Ker.ONBasis.sgnM_sq X) h2, ?_⟩
  rw [e, Ker.ONBasis.adj_mul (Ker.ONBasis.sgnM_sq X) h2, ← mulVec_mulVec, sgnM, mulVec_diagonal]

variable {X X' : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ}
  {idx : Fin g ≃ X.Ψ × Fin r} {idx' : Fin g ≃ X'.Ψ × Fin r} {x : Frame X.Ψ r} {x' : Frame X'.Ψ r}

/- English proof (translation)
Use function extensionality and compare the values at `k j`. Unfold `Ker.zR`. Rewrite using `[hi j]`. Generalize the expression as in `idx j = t`. Take `⟨τ, a⟩` from `t`.

Establish `ha` using `a.isLt`. Take `⟨hu, h1⟩` from `herm_col (hx τ) (v τ k) a`. Establish `hm : mat x' (e τ) = ((mat x τ).map conj).submatrix id Fin.revPerm`. Use extensionality with `a b`. Conclude with `hx' τ a b`.

Establish `hv' : v' (e τ) k = fun a => conj (v τ k a)` using `funext (hv τ k)`. Simplify using `only`. Rewrite using `[hm, hv', Fin.val_rev]`. Distinguish the cases in `h : (a : ℕ) < X.p0`. Rewrite using `[if_pos h, if_neg (by omega), ← conj_hermC, h1, sgn, if_pos h]`.

Use `Matrix.inv_submatrix_equiv ((mat x τ).map conj) (Equiv.refl _) Fin.revPerm` as an intermediate fact. Rewrite `this` using `[Equiv.coe_refl]`. Rewrite using `[this, Ker.ONBasis.inv_map_conj hu]`. Simplify using `[mulVec, dotProduct]`. Rewrite using `[if_neg h, if_pos (by omega), he, hG]`.

Establish `e2 : FD.col (((mat x τ).map conj).submatrix id Fin.revPerm) a.rev = fun i => conj (FD.col (mat x τ) a i)`. Use function extensionality and compare the values at `i`. Simplify using `[FD.col]`. Rewrite using `[e2, hermC_flip, conj_hermC, h1, sgn, if_neg h]`. Simplify using the standard rewrite rules.
-/
theorem zR_flip (e : X.Ψ → X'.Ψ) (he : ∀ τ, (e τ).1 = ComplexEmbedding.conjugate τ.1) (hG : X'.Gm = -X.Gm)
    (hp : X'.p0 + X.p0 = r) (hi : ∀ j, idx' j = (e (idx j).1, (idx j).2.rev)) (hx : Ker.IsONFr X x)
    (hx' : ∀ τ a b, x' (e τ) a b = conj (x τ a b.rev)) {v : Ker.WR X n} {v' : Ker.WR X' n}
    (hv : ∀ τ k a, v' (e τ) k a = conj (v τ k a)) : Ker.zR X' idx' x' v' = Ker.zR X idx x v := by
  funext k j
  unfold Ker.zR
  rw [hi j]
  generalize idx j = t
  obtain ⟨τ, a⟩ := t
  have ha := a.isLt
  obtain ⟨hu, h1⟩ := herm_col (hx τ) (v τ k) a
  have hm : mat x' (e τ) = ((mat x τ).map conj).submatrix id Fin.revPerm := by
    ext a b; exact hx' τ a b
  have hv' : v' (e τ) k = fun a => conj (v τ k a) := funext (hv τ k)
  dsimp only
  rw [hm, hv', Fin.val_rev]
  by_cases h : (a : ℕ) < X.p0
  · rw [if_pos h, if_neg (by omega), ← conj_hermC, h1, sgn, if_pos h]
    have := Matrix.inv_submatrix_equiv ((mat x τ).map conj) (Equiv.refl _) Fin.revPerm
    rw [Equiv.coe_refl] at this
    rw [this, Ker.ONBasis.inv_map_conj hu]
    simp [mulVec, dotProduct]
  · rw [if_neg h, if_pos (by omega), he, hG]
    have e2 : FD.col (((mat x τ).map conj).submatrix id Fin.revPerm) a.rev = fun i => conj (FD.col (mat x τ) a i) := by
      funext i; simp [FD.col]
    rw [e2, hermC_flip, conj_hermC, h1, sgn, if_neg h]
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `z`. Simplify using `only [thA, imInv, tauMat, hMat, hb]`. Use function extensionality and compare the values at `z`. Simplify using `only [Ker.gaussR, Dict.hx, imInv, tauMat, hMat, hb]`.
-/
theorem thA_congr (hb : ∀ s, perMat X' bas' idx' s x' = perMat X bas idx s x) (φ : TF n g) :
    thA X' bas' idx' φ x' = thA X bas idx φ x ∧ Ker.gaussR (n := n) X' bas' idx' x' = Ker.gaussR X bas idx x := by
  constructor
  · funext z
    simp only [thA, imInv, tauMat, hMat, hb]
  · funext z
    simp only [Ker.gaussR, Dict.hx, imInv, tauMat, hMat, hb]

/- English proof (translation)
Establish `: vecQ X' bas' = vecQ X bas`. Use function extensionality and compare the values at `m`. Simplify using `only [vecQ, hb]`. Simplify using `only [heisG, crd, this]`.
-/
theorem heisG_congr (hb : ∀ m, (bas' m : Fin r → E) = bas m) (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) :
    heisG X' bas' y φ = heisG X bas y φ := by
  have : vecQ X' bas' = vecQ X bas := by
    funext m
    simp only [vecQ, hb]
  simp only [heisG, crd, this]

/- English proof (translation)
Rewrite using `[EF_def, EF_def, hG, hk, herm_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EF_flip (hG : X'.Gm = -X.Gm) (hk : X'.κ0 = -X.κ0) (u v : Fin r → E) : EF X' u v = EF X u v := by
  rw [EF_def, EF_def, hG, hk, herm_neg]
  congr 1
  ring

omit [IsCMField E] in
/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨b, fun _ => rfl⟩`.
-/
theorem exists_bas {Λ Λ' : Submodule (𝓞 E) (Fin r → E)} (h : Λ' = Λ) (b : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) :
    ∃ b' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ', ∀ m, (b' m : Fin r → E) = b m := by
  subst h
  exact ⟨b, fun _ => rfl⟩

/- English proof (translation)
Set `L : Matrix (Fin n) (Fin g) ℚ → (Fin n → Fin g → ℂ) →ₗ[ℂ] ℂ` to `fun y => { toFun := fun z => Real.pi * I * ∑ k, 2 * (qv (y k) ⬝ᵥ hMat X bas idx x *ᵥ z k) map_add' := fun z w => by simp [mulVec_add, mul_add, Finset.sum_add_distrib] map_smul' := fun c z => by`. Simplify using `only [Pi.smul_apply, mulVec_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring }`. Set `c : Matrix (Fin n) (Fin g) ℚ → ℂ` to `fun y => φ y * cexp (Real.pi * I * ∑ k, qv (y k) ⬝ᵥ tauMat X bas idx x *ᵥ qv (y k))`. Establish `e : ∀ z : Fin n → Fin g → ℂ, thS φ (tauMat X bas idx x) (fun k => hMat X bas idx x *ᵥ z k) = ∑' y, c y * cexp (L y z)` using `fun z => tsum_congr fun y => by`.

Rewrite using `[Finset.sum_add_distrib, mul_add, Complex.exp_add, ← mul_assoc]`. Both sides reduce to the same expression. Take `⟨h1, h2⟩` from `GlobalTheory.ExpSeries.convex_and_differentiableOn_tsum_cexp _ _ c L`. Use `GlobalTheory.ConvexCutOff.polyDeriv_rename_of_convex _ _ _ h1 (fun z hz => ?_) ?_ 0 _ _ ρ hρ Q u` and prove the remaining obligations. Rewrite using `[thA, e, tsum_eq_zero_of_not_summable hz, mul_zero]`.

Unfold `thA`. Simplify using `only [e]`. Use `DifferentiableOn.mul (Differentiable.differentiableOn (Differentiable.const_mul (Differentiable.cexp ?_) _)) h2` and prove the remaining obligations. Simplify using `only [mulVec, dotProduct]`. Use `fun_prop`.
-/
theorem polyDeriv_thA_rename (φ : TF n g) {ι κ : Type} (ρ : ι → κ) (hρ : Function.Injective ρ)
    (Q : MvPolynomial ι ℂ) (u : κ → Fin n → Fin g → ℂ) :
    polyDeriv (MvPolynomial.rename ρ Q) u (thA X bas idx φ x) 0 = polyDeriv Q (u ∘ ρ) (thA X bas idx φ x) 0 := by
  let L : Matrix (Fin n) (Fin g) ℚ → (Fin n → Fin g → ℂ) →ₗ[ℂ] ℂ := fun y =>
    { toFun := fun z => Real.pi * I * ∑ k, 2 * (qv (y k) ⬝ᵥ hMat X bas idx x *ᵥ z k)
      map_add' := fun z w => by simp [mulVec_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [Pi.smul_apply, mulVec_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  let c : Matrix (Fin n) (Fin g) ℚ → ℂ := fun y =>
    φ y * cexp (Real.pi * I * ∑ k, qv (y k) ⬝ᵥ tauMat X bas idx x *ᵥ qv (y k))
  have e : ∀ z : Fin n → Fin g → ℂ, thS φ (tauMat X bas idx x) (fun k => hMat X bas idx x *ᵥ z k) =
      ∑' y, c y * cexp (L y z) := fun z => tsum_congr fun y => by
    rw [Finset.sum_add_distrib, mul_add, Complex.exp_add, ← mul_assoc]
    rfl
  obtain ⟨h1, h2⟩ := GlobalTheory.ExpSeries.convex_and_differentiableOn_tsum_cexp _ _ c L
  refine GlobalTheory.ConvexCutOff.polyDeriv_rename_of_convex _ _ _ h1 (fun z hz => ?_) ?_ 0 _ _ ρ hρ Q u
  · rw [thA, e, tsum_eq_zero_of_not_summable hz, mul_zero]
  · unfold thA
    simp only [e]
    refine DifferentiableOn.mul (Differentiable.differentiableOn
      (Differentiable.const_mul (Differentiable.cexp ?_) _)) h2
    simp only [mulVec, dotProduct]
    fun_prop

end Generic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

/- English proof (translation)
Introduce `τ`. Take `⟨ρ, rfl⟩` from `eT.surjective τ`. Use extensionality with `a b`. Establish `h` using `congrFun (congrFun (hZ ρ) b) a`. Establish `e : FD.gram (eT ρ).1 X.Gm (mat (frOf rfl eT Z) (eT ρ)) a b = -((Z ρ)ᴴ * gramAt D T ρ * Z ρ) b a`.

Simplify using `only [FD.gram, hermC, FD.col, mat, frOf, Matrix.mul_apply, conjTranspose_apply, transpose_apply, map_apply, Finset.sum_mul, RCLike.star_def, of_apply, hG, he, gramAt, Matrix.neg_apply, map_neg, Equiv.symm_apply_apply, Fin.cast_eq_self, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e, h, negM, sgnM, Matrix.diagonal_apply, Matrix.diagonal_apply]`. Distinguish the cases in `h : a = b`. Simplify using `[h]`.

Simplify using `[h, Ne.symm h]`.
-/
theorem gram_frOf {D : D7} {T : HSp D} {X : Data D.host.E T.rank} (eT : D.what₂.Tau ≃ X.Ψ)
    (hG : X.Gm = -T.gramᵀ) (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) :
    Ker.IsONFr X (frOf rfl eT Z) := by
  intro τ
  obtain ⟨ρ, rfl⟩ := eT.surjective τ
  ext a b
  have h := congrFun (congrFun (hZ ρ) b) a
  have e : FD.gram (eT ρ).1 X.Gm (mat (frOf rfl eT Z) (eT ρ)) a b = -((Z ρ)ᴴ * gramAt D T ρ * Z ρ) b a := by
    simp only [FD.gram, hermC, FD.col, mat, frOf, Matrix.mul_apply, conjTranspose_apply, transpose_apply,
      map_apply, Finset.sum_mul, RCLike.star_def, of_apply, hG, he, gramAt, Matrix.neg_apply, map_neg,
      Equiv.symm_apply_apply, Fin.cast_eq_self, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e, h, negM, sgnM, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Rewrite using `[negM, Matrix.submatrix_diagonal_equiv, sgnM]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[sgn_rev hq a]`. Both sides reduce to the same expression.
-/
theorem negM_rev {D : D7} {T : HSp D} (X' : Data D.host.E T.rank) {q : ℕ} (hq : X'.p0 + q = T.rank) :
    (negM T q).submatrix Fin.revPerm Fin.revPerm = sgnM X' := by
  rw [negM, Matrix.submatrix_diagonal_equiv, sgnM]
  congr 1
  funext a
  rw [sgn_rev hq a]
  rfl

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add P Q hP hQ => simp only [map_add, hP, hQ]`. Consider the case `mul_X P v hP => simp only [map_mul, hP, MvPolynomial.rename_X, MvPolynomial.aeval_X, MvPolynomial.rename_C, hc, h]`.
-/
theorem aeval_rename_eq {ι κ κ' : Type} (f : ι → ι) (ρ : κ → κ') (c : ι → ℂ) (s : ι → κ) (s' : ι → κ')
    (hc : ∀ v, c (f v) = c v) (h : ∀ v, s' (f v) = ρ (s v)) (Q : MvPolynomial ι ℂ) :
    MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (s' v) : ι → MvPolynomial κ' ℂ)
        (MvPolynomial.rename f Q) =
      MvPolynomial.rename ρ (MvPolynomial.aeval
        (fun v => MvPolynomial.C (c v) * MvPolynomial.X (s v) : ι → MvPolynomial κ ℂ) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP => simp only [map_mul, hP, MvPolynomial.rename_X, MvPolynomial.aeval_X, MvPolynomial.rename_C, hc, h]

/- English proof (translation)
Introduce `D S T r g hr ψ θ X eT bas idx hS q0 hq`. Substitute `hr` using the available equality. Take `⟨X', hΨ, hG, hp, hΛ, hκ⟩` from `exists_flip X hq`. Establish `hGm : X.Gm = -T.gramᵀ` using `by simpa using hS.2.2.2.2.1.1`. Establish `hcc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `fun σ => star_star σ`.

Set `e : X.Ψ ≃ X'.Ψ` to `{ toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by rw [hΨ]; exact Finset.mem_image_of_mem _ τ.2⟩ invFun := fun σ => ⟨ComplexEmbedding.conjugate σ.1, by`. Take `⟨τ, h1, h2⟩` from `Finset.mem_image.1 (hΨ.le σ.2)`. Rewrite using `[← h2, hcc]⟩` and apply the resulting hypothesis. Use `left_inv := fun τ => Subtype.ext (hcc _)`. Use `right_inv := fun τ => Subtype.ext (hcc _) }`.

Establish `he : ∀ τ, (e τ).1 = ComplexEmbedding.conjugate τ.1` using `fun _ => rfl`. Set `m : GlobalTheory.Ker.Match S T X'` to `⟨hS.2.2.1, by rw [hG, hGm, neg_neg], eT.trans e, fun τ => by rw [Equiv.trans_apply, he, hS.2.2.2.2.2.2.1], by rw [hκ, hS.2.2.2.2.2.1, neg_neg]⟩`. Establish `hq' : X'.p0 + X.p0 = T.rank` using `by omega`. Take `⟨bas', hb⟩` from `exists_bas hΛ bas`. Set `idx' : Fin g ≃ X'.Ψ × Fin T.rank` to `idx.trans (e.prodCongr Fin.revPerm)`.

Establish `hi : ∀ j, idx' j = (e (idx j).1, (idx j).2.rev)` using `fun _ => rfl`. Establish `hs : IsSympl X' bas'` using `fun a b => by`. Rewrite using `[EF_flip hG hκ, hb, hb]`. Conclude with `hS.2.2.2.2.2.2.2 a b`. Use `⟨X', m, hq', bas', idx', hs, Fin.revPerm, hΛ, EF_flip hG hκ, heisG_congr hb, fun Z => ⟨?_, fun hZ => ?_⟩⟩` and prove the remaining obligations.

Use `forall_congr' fun ρ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ↔ ((Z ρ).submatrix id Fin.revPerm)ᴴ * gramAt D T ρ * (Z ρ).submatrix id Fin.revPerm = sgnM X'`. Rewrite using `[← negM_rev X' hq']`. Express the relevant statement in the definitionally equal form `_ ↔ ((Z ρ)ᴴ * gramAt D T ρ * Z ρ).submatrix Fin.revPerm Fin.revPerm = _`. Conclude with `⟨fun h => by rw [h], fun h => (Matrix.reindex Fin.revPerm.symm Fin.revPerm.symm).injective h⟩`.

Use `set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC`. Use `set x' : Frame X'.Ψ T.rank := C.xB fun ρ => (Z ρ).submatrix id Fin.revPerm with hx'`. Establish `hx` using `gram_frOf eT hGm hS.2.2.2.2.2.2.1 hZ`. Establish `hxx : ∀ τ a b, x' (e τ) a b = conj (frOf rfl eT Z τ a b.rev)` using `fun τ a b => by`. Express the relevant statement in the definitionally equal form `conj (Z (eT.symm (e.symm (e τ))) a b.rev) = _`.

Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hper : ∀ s, perMat X' bas' idx' s x' = perMat X bas idx s (frOf rfl eT Z)` using `fun s => by`. Use extensionality with `i k`. Use `zR_flip (n := 1) e he hG hq' hi hx hxx (v := Ker.embR X (Matrix.of fun _ => (bas (Pi.single (s k) 1) : Fin T.rank → D.host.E))) (v' := Ker.embR X' (Matrix.of fun _ => (bas (Pi.single (s k) 1) : Fin T.rank → D.host.E))) (fun τ k a => ComplexEmbedding.conjugate_coe_eq _ _)` as an intermediate fact.

Rewrite using `[perMat_apply, perMat_apply, hb]`. Conclude with `congrFun (congrFun this 0) i`. Use `⟨funext fun ρ => ?_, fun φ f => ?_, fun φ Q => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Z ρ).submatrix id Fin.revPerm * sgnM X' * ((Z ρ).submatrix id Fin.revPerm)⁻¹ = _`. Use `Matrix.inv_submatrix_equiv (Z ρ) (Equiv.refl _) Fin.revPerm` as an intermediate fact.

Rewrite `this` using `[Equiv.coe_refl]`. Rewrite using `[this, ← negM_rev X' hq', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`. Both sides reduce to the same expression. Use `and_congr Iff.rfl (forall_congr' fun w => imp_congr_right fun _ => ?_)` and prove the remaining obligations. Establish `hz : Ker.zR X' idx' x' (C.realPt w) = Ker.zR X idx (frOf rfl eT Z) (rePt θ rfl eT w)` using `zR_flip e he hG hq' hi hx hxx fun τ k a => by`.

Express the relevant statement in the definitionally equal form `conj (compAt θ (eT.symm (e.symm (e τ))) w a k) = _`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `f w = Ker.thR X' bas' idx' φ x' (C.realPt w) ↔ _`. Unfold `Ker.thR`.

Rewrite using `[hz, (thA_congr hper φ).1, (thA_congr hper φ).2]`. Set `ρ : Harm.Var X.Ψ q0 X.p0 (Fin S.rank) ≃ Harm.Var X'.Ψ X.p0 X'.p0 (Fin S.rank)` to `e.prodCongr (((rowIdx hq).trans (Fin.revPerm.trans (rowIdx hq').symm)).prodCongr (Equiv.refl _))`. Establish `h1 : C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, Fin.revPerm.symm v.2.1, v.2.2)) Q) = MvPolynomial.rename ρ (toP S rfl eT hq Q)`. Use `aeval_rename_eq (ι := FVar D T.rank S.rank) (fun v => (v.1, Fin.revPerm.symm v.2.1, v.2.2)) ρ (fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)) (fun v => (eT v.1, (rowIdx hq).symm v.2.1, v.2.2)) (fun v => (e (eT v.1), (rowIdx hq').symm v.2.1, v.2.2)) (fun _ => rfl) (fun v => ?_) Q` and prove the remaining obligations. Use `Prod.ext rfl (Prod.ext ?_ rfl)` and prove the remaining obligations.

Conclude with `congrArg (fun a => (rowIdx hq').symm (Fin.rev a)) ((rowIdx hq).apply_symm_apply _).symm`. Establish `h2 : letterDir X' hq' idx' ∘ ρ = letterDir X hq idx`. Use function extensionality and compare the values at `l`. Use `congrArg (fun i : Fin g => (Pi.single l.2.2 (Pi.single i 1) : Fin S.rank → Fin g → ℂ)) ?_` and prove the remaining obligations. Rewrite using `[Equiv.symm_apply_eq, hi, Equiv.apply_symm_apply]`.

Conclude with `Prod.ext rfl ((rowIdx hq').apply_symm_apply _)`. Unfold `thP`. Rewrite using `[h1, polyDeriv_thA_rename φ ρ ρ.injective, h2, (thA_congr hper φ).1]`.
-/
theorem exists_flip_model : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ (q0 : ℕ) (hq : X.p0 + q0 = r), ∃ (X' : Data D.host.E T.rank) (m : GlobalTheory.Ker.Match S T X') (hq' : X'.p0 + X.p0 = T.rank) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') (π : Equiv.Perm (Fin T.rank)), X'.Λ = latW hr X.Λ ∧ (∀ u v : Fin T.rank → D.host.E, EF X' u v = EF X (u ∘ Fin.cast hr.symm) (v ∘ Fin.cast hr.symm)) ∧ (∀ (y : Matrix (Fin S.rank) (Fin r) D.host.E) (φ : TF S.rank g), heisG X' bas' (y.submatrix id (Fin.cast hr)) φ = heisG X bas y φ) ∧ ∀ Z : Fam T, (IsONeg T X.p0 Z ↔ (ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).IsB (fun ρ => (Z ρ).submatrix id π)) ∧ (IsONeg T X.p0 Z → (ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).sB (fun ρ => (Z ρ).submatrix id π) = cartZ T X.p0 Z ∧ (∀ (φ : TF S.rank g) (f : WO S T → ℂ), (ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).IsZak ((ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).xB (fun ρ => (Z ρ).submatrix id π)) φ f ↔ Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) ∧ ∀ (φ : TF S.rank g) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), thP X' hq' bas' idx' φ ((ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).toH (MvPolynomial.rename (fun v => (v.1, π.symm v.2.1, v.2.2)) Q)) ((ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).xB (fun ρ => (Z ρ).submatrix id π)) = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT Z)) := by
  classical
  intro D S T r g hr ψ θ X eT bas idx hS q0 hq
  subst hr
  obtain ⟨X', hΨ, hG, hp, hΛ, hκ⟩ := exists_flip X hq
  have hGm : X.Gm = -T.gramᵀ := by simpa using hS.2.2.2.2.1.1
  have hcc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  let e : X.Ψ ≃ X'.Ψ :=
    { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by rw [hΨ]; exact Finset.mem_image_of_mem _ τ.2⟩
      invFun := fun σ => ⟨ComplexEmbedding.conjugate σ.1, by
        obtain ⟨τ, h1, h2⟩ := Finset.mem_image.1 (hΨ.le σ.2)
        rwa [← h2, hcc]⟩
      left_inv := fun τ => Subtype.ext (hcc _)
      right_inv := fun τ => Subtype.ext (hcc _) }
  have he : ∀ τ, (e τ).1 = ComplexEmbedding.conjugate τ.1 := fun _ => rfl
  let m : GlobalTheory.Ker.Match S T X' :=
    ⟨hS.2.2.1, by rw [hG, hGm, neg_neg], eT.trans e,
      fun τ => by rw [Equiv.trans_apply, he, hS.2.2.2.2.2.2.1], by rw [hκ, hS.2.2.2.2.2.1, neg_neg]⟩
  have hq' : X'.p0 + X.p0 = T.rank := by omega
  obtain ⟨bas', hb⟩ := exists_bas hΛ bas
  let idx' : Fin g ≃ X'.Ψ × Fin T.rank := idx.trans (e.prodCongr Fin.revPerm)
  have hi : ∀ j, idx' j = (e (idx j).1, (idx j).2.rev) := fun _ => rfl
  have hs : IsSympl X' bas' := fun a b => by
    rw [EF_flip hG hκ, hb, hb]; exact hS.2.2.2.2.2.2.2 a b
  refine ⟨X', m, hq', bas', idx', hs, Fin.revPerm, hΛ, EF_flip hG hκ, heisG_congr hb, fun Z => ⟨?_, fun hZ => ?_⟩⟩
  · refine forall_congr' fun ρ => ?_
    change _ ↔ ((Z ρ).submatrix id Fin.revPerm)ᴴ * gramAt D T ρ * (Z ρ).submatrix id Fin.revPerm = sgnM X'
    rw [← negM_rev X' hq']
    change _ ↔ ((Z ρ)ᴴ * gramAt D T ρ * Z ρ).submatrix Fin.revPerm Fin.revPerm = _
    exact ⟨fun h => by rw [h], fun h => (Matrix.reindex Fin.revPerm.symm Fin.revPerm.symm).injective h⟩
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  set x' : Frame X'.Ψ T.rank := C.xB fun ρ => (Z ρ).submatrix id Fin.revPerm with hx'
  have hx := gram_frOf eT hGm hS.2.2.2.2.2.2.1 hZ
  have hxx : ∀ τ a b, x' (e τ) a b = conj (frOf rfl eT Z τ a b.rev) := fun τ a b => by
    change conj (Z (eT.symm (e.symm (e τ))) a b.rev) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hper : ∀ s, perMat X' bas' idx' s x' = perMat X bas idx s (frOf rfl eT Z) := fun s => by
    ext i k
    have := zR_flip (n := 1) e he hG hq' hi hx hxx
      (v := Ker.embR X (Matrix.of fun _ => (bas (Pi.single (s k) 1) : Fin T.rank → D.host.E)))
      (v' := Ker.embR X' (Matrix.of fun _ => (bas (Pi.single (s k) 1) : Fin T.rank → D.host.E)))
      (fun τ k a => ComplexEmbedding.conjugate_coe_eq _ _)
    rw [perMat_apply, perMat_apply, hb]
    exact congrFun (congrFun this 0) i
  refine ⟨funext fun ρ => ?_, fun φ f => ?_, fun φ Q => ?_⟩
  · change (Z ρ).submatrix id Fin.revPerm * sgnM X' * ((Z ρ).submatrix id Fin.revPerm)⁻¹ = _
    have := Matrix.inv_submatrix_equiv (Z ρ) (Equiv.refl _) Fin.revPerm
    rw [Equiv.coe_refl] at this
    rw [this, ← negM_rev X' hq', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  · refine and_congr Iff.rfl (forall_congr' fun w => imp_congr_right fun _ => ?_)
    have hz : Ker.zR X' idx' x' (C.realPt w) = Ker.zR X idx (frOf rfl eT Z) (rePt θ rfl eT w) :=
      zR_flip e he hG hq' hi hx hxx fun τ k a => by
        change conj (compAt θ (eT.symm (e.symm (e τ))) w a k) = _
        rw [Equiv.symm_apply_apply]
        rfl
    change f w = Ker.thR X' bas' idx' φ x' (C.realPt w) ↔ _
    unfold Ker.thR
    rw [hz, (thA_congr hper φ).1, (thA_congr hper φ).2]
  · let ρ : Harm.Var X.Ψ q0 X.p0 (Fin S.rank) ≃ Harm.Var X'.Ψ X.p0 X'.p0 (Fin S.rank) :=
      e.prodCongr (((rowIdx hq).trans (Fin.revPerm.trans (rowIdx hq').symm)).prodCongr (Equiv.refl _))
    have h1 : C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, Fin.revPerm.symm v.2.1, v.2.2)) Q) =
        MvPolynomial.rename ρ (toP S rfl eT hq Q) := by
      refine aeval_rename_eq (ι := FVar D T.rank S.rank) (fun v => (v.1, Fin.revPerm.symm v.2.1, v.2.2)) ρ
        (fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)) (fun v => (eT v.1, (rowIdx hq).symm v.2.1, v.2.2))
        (fun v => (e (eT v.1), (rowIdx hq').symm v.2.1, v.2.2)) (fun _ => rfl) (fun v => ?_) Q
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      exact congrArg (fun a => (rowIdx hq').symm (Fin.rev a)) ((rowIdx hq).apply_symm_apply _).symm
    have h2 : letterDir X' hq' idx' ∘ ρ = letterDir X hq idx := by
      funext l
      refine congrArg (fun i : Fin g => (Pi.single l.2.2 (Pi.single i 1) : Fin S.rank → Fin g → ℂ)) ?_
      rw [Equiv.symm_apply_eq, hi, Equiv.apply_symm_apply]
      exact Prod.ext rfl ((rowIdx hq').apply_symm_apply _)
    unfold thP
    rw [h1, polyDeriv_thA_rename φ ρ ρ.injective, h2, (thA_congr hper φ).1]

end GlobalTheory.OneMapRef.Flip

end
