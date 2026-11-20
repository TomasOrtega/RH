import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecayCoord

/- English proof (translation)
Establish `h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x`. Simplify using `[infPart, incA, inclR, Algebra.TensorProduct.map_tmul]`. Rewrite using `[h]`. Conclude with `(hθ τ).1 x`.
-/
theorem theta_incA {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [h]
  exact (hθ τ).1 x

/- English proof (translation)
Establish `hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), compAt θ τ M = M.map ((θ τ).comp (infPart D))` using `fun M => rfl`. Establish `hE : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (M.map (incA D)).map ((θ τ).comp (infPart D)) = M.map (tauE D τ)`. Introduce `m n M`. Use extensionality with `i j`. Simplify using `[theta_incA θ hθ]`.

Rewrite using `[hm, hm, GlobalTheory.IsoMean.emb, Matrix.map_mul, Matrix.map_mul, hE, hE]`.
-/
theorem compAt_emb {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V W : HSp D) {a b : ℕ}
    (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) :
    compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y) = P.map (tauE D τ) * compAt θ τ y * Q.map (tauE D τ) := by
  have hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), compAt θ τ M = M.map ((θ τ).comp (infPart D)) :=
    fun M => rfl
  have hE : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map ((θ τ).comp (infPart D)) = M.map (tauE D τ) := by
    intro m n M; ext i j; simp [theta_incA θ hθ]
  rw [hm, hm, GlobalTheory.IsoMean.emb, Matrix.map_mul, Matrix.map_mul, hE, hE]

/- English proof (translation)
Establish `hker : LinearMap.ker P.mulVecLin = ⊥`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker P.mulVecLin`. Rewrite `hP` using `[Matrix.rank]`. Rewrite `h1` using `[hP, Module.finrank_fin_fun]`. Conclude with `Submodule.finrank_eq_zero.1 (by omega)`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hker`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg LinearMap.toMatrix' hg`. Rewrite `h2` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id]`. Establish `h3 : LinearMap.toMatrix' P.mulVecLin = P` using `LinearMap.toMatrix'_toLin' P`.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
theorem exists_left_inv {K : Type*} [Field K] {n a : ℕ} (P : Matrix (Fin n) (Fin a) K) (hP : P.rank = a) :
    ∃ P' : Matrix (Fin a) (Fin n) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [Matrix.rank] at hP
    rw [hP, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
  have h3 : LinearMap.toMatrix' P.mulVecLin = P := LinearMap.toMatrix'_toLin' P
  rwa [h3] at h2

/- English proof (translation)
Take `⟨R, hR⟩` from `exists_left_inv Qᵀ (by rw [Matrix.rank_transpose, hQ])`. Use `⟨Rᵀ, ?_⟩` and prove the remaining obligations. Use `congrArg Matrix.transpose hR` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis.
-/
theorem exists_right_inv {K : Type*} [Field K] {n b : ℕ} (Q : Matrix (Fin b) (Fin n) K) (hQ : Q.rank = b) :
    ∃ Q' : Matrix (Fin n) (Fin b) K, Q * Q' = 1 := by
  obtain ⟨R, hR⟩ := exists_left_inv Qᵀ (by rw [Matrix.rank_transpose, hQ])
  refine ⟨Rᵀ, ?_⟩
  have := congrArg Matrix.transpose hR
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

/- English proof (translation)
Take `⟨j, -, hj⟩` from `Finset.exists_max_image Finset.univ u Finset.univ_nonempty`. Establish `h1 : ∑ k, u k ≤ Fintype.card κ * u j`. Use `Finset.sum_le_card_nsmul Finset.univ u (u j) (fun k _ => hj k (Finset.mem_univ _))` as an intermediate fact. Simplify `this` using `[nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Finset.single_le_sum (f := fun k => u k ^ N) (fun k _ => pow_nonneg (hu k) N) (Finset.mem_univ j)`.
-/
theorem sum_pow_le {κ : Type*} [Fintype κ] [Nonempty κ] (u : κ → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ) :
    (∑ k, u k) ^ N ≤ (Fintype.card κ : ℝ) ^ N * ∑ k, u k ^ N := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  have h1 : ∑ k, u k ≤ Fintype.card κ * u j := by
    have := Finset.sum_le_card_nsmul Finset.univ u (u j) (fun k _ => hj k (Finset.mem_univ _))
    simpa [nsmul_eq_mul] using this
  calc (∑ k, u k) ^ N ≤ (Fintype.card κ * u j) ^ N :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hu k) h1 N
    _ = (Fintype.card κ : ℝ) ^ N * u j ^ N := mul_pow _ _ _
    _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (f := fun k => u k ^ N) (fun k _ => pow_nonneg (hu k) N) (Finset.mem_univ j)

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]`. Rewrite using `[Finset.sum_eq_single l, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Ne.symm hj]`.

Simplify using the standard rewrite rules. Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Simplify using `[Ne.symm hi]`.

Simplify using the standard rewrite rules.
-/
theorem trace_single {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℂ) (k : Fin a) (l : Fin b) (α : ℂ) :
    (Yᴴ * Matrix.single k l α).trace = star (Y k l) * α := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
  · simp

/- English proof (translation)
Establish `e1 : c * (star w * c⁻¹) = star w` using `by field_simp`. Establish `e2 : c * (star w * (Complex.I * c⁻¹)) = Complex.I * star w` using `by field_simp`. Rewrite using `[e1, e2]`. Use `Complex.norm_le_abs_re_add_abs_im w` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_im, abs_mul]`.

Evaluate the numerical expressions. Combine the linear relations using `[abs_nonneg w.re, abs_nonneg w.im]`.
-/
theorem norm_le_re (c w : ℂ) (hc : c ≠ 0) :
    ‖w‖ ≤ |2 * (c * (star w * c⁻¹)).re| + |2 * (c * (star w * (Complex.I * c⁻¹))).re| := by
  have e1 : c * (star w * c⁻¹) = star w := by field_simp
  have e2 : c * (star w * (Complex.I * c⁻¹)) = Complex.I * star w := by field_simp
  rw [e1, e2]
  have := Complex.norm_le_abs_re_add_abs_im w
  simp only [Complex.star_def, Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_im, abs_mul]
  norm_num
  linarith [abs_nonneg w.re, abs_nonneg w.im]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

/- English proof (translation)
Unfold `gramAt`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)`.
-/
theorem det_gramAt_ne {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ).det ≠ 0 := by
  unfold gramAt
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt`. Use `set GV := gramAt D V τ`. Use `set GW := gramAt D W τ`. Establish `hW : GW * GW⁻¹ = 1` using `Matrix.mul_nonsing_inv GW (Ne.isUnit (det_gramAt_ne W τ))`. Establish `hV : GV * GV⁻¹ = 1` using `Matrix.mul_nonsing_inv GV (Ne.isUnit (det_gramAt_ne V τ))`.

Establish `hP' : Pcᴴ * Plᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hP, Matrix.conjTranspose_one]`. Establish `hQ' : Qrᴴ * Qcᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]`. Establish `e : GV⁻¹ * (Pc * Y * Qc)ᴴ * GW * (GW⁻¹ * Plᴴ * X * Qrᴴ * GV) = GV⁻¹ * ((Qcᴴ * Yᴴ * X * Qrᴴ) * GV)`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc GW GW⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc Pcᴴ Plᴴ, hP', Matrix.one_mul]`.

Rewrite using `[e, Matrix.trace_mul_comm, Matrix.mul_assoc _ GV, hV, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul]`.
-/
theorem herm_key {D : D7} (V W : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (Pc : Matrix (Fin W.rank) (Fin a) ℂ)
    (Pl : Matrix (Fin a) (Fin W.rank) ℂ) (hP : Pl * Pc = 1) (Qc : Matrix (Fin b) (Fin V.rank) ℂ)
    (Qr : Matrix (Fin V.rank) (Fin b) ℂ) (hQ : Qc * Qr = 1) (Y X : Matrix (Fin a) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ ((gramAt D W τ)⁻¹ * Plᴴ * X * Qrᴴ * gramAt D V τ) (Pc * Y * Qc) =
      (Yᴴ * X).trace := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  set GV := gramAt D V τ
  set GW := gramAt D W τ
  have hW : GW * GW⁻¹ = 1 := Matrix.mul_nonsing_inv GW (Ne.isUnit (det_gramAt_ne W τ))
  have hV : GV * GV⁻¹ = 1 := Matrix.mul_nonsing_inv GV (Ne.isUnit (det_gramAt_ne V τ))
  have hP' : Pcᴴ * Plᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hP, Matrix.conjTranspose_one]
  have hQ' : Qrᴴ * Qcᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
  have e : GV⁻¹ * (Pc * Y * Qc)ᴴ * GW * (GW⁻¹ * Plᴴ * X * Qrᴴ * GV) = GV⁻¹ * ((Qcᴴ * Yᴴ * X * Qrᴴ) * GV) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc GW GW⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc Pcᴴ Plᴴ, hP', Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc _ GV, hV, Matrix.mul_one, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

/- English proof (translation)
Introduce `D V W a b P Q hP hQ θ hθ f hf N`. Take `⟨Pl, hPl⟩` from `exists_left_inv P hP`. Take `⟨Qr, hQr⟩` from `exists_right_inv Q hQ`. Establish `hPlτ : ∀ τ, Pl.map (tauE D τ) * P.map (tauE D τ) = 1` using `fun τ => by`. Rewrite using `[← Matrix.map_mul, hPl, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hQrτ : ∀ τ, Q.map (tauE D τ) * Qr.map (tauE D τ) = 1` using `fun τ => by`. Rewrite using `[← Matrix.map_mul, hQr, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `c : D.what₂.Tau → ℂ` to `fun τ => tauE D τ D.host.xi0`. Establish `hc : ∀ τ, c τ ≠ 0` using `fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)`. Set `zOf : D.what₂.Tau → Matrix (Fin a) (Fin b) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ` to `fun τ X => (gramAt D W τ)⁻¹ * (Pl.map (tauE D τ))ᴴ * X * (Qr.map (tauE D τ))ᴴ * gramAt D V τ`.

Set `zι : D.what₂.Tau × Fin a × Fin b × Bool → Matrix (Fin W.rank) (Fin V.rank) ℂ` to `fun i => zOf i.1 (Matrix.single i.2.1 i.2.2.1 (if i.2.2.2 then Complex.I * (c i.1)⁻¹ else (c i.1)⁻¹))`. Set `ℓ : D.what₂.Tau × Fin a × Fin b × Bool → Mx D a b → ℝ` to `fun i y => |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W i.1 (zι i) (compAt θ i.1 (GlobalTheory.IsoMean.emb V W P Q y))|`. Establish `hterm : ∀ (y : Mx D a b) (τ : D.what₂.Tau) (k : Fin a) (l : Fin b), ‖θ τ (infPart D (y k l))‖ ≤ ∑ β : Bool, ℓ (τ, k, l, β) y`. Introduce `y τ k l`. Establish `hs : ∀ α : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ (zOf τ (Matrix.single k l α)) (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y)) = 2 * (c τ * (star (compAt θ τ y k l) * α)).re`.

Introduce `α`. Rewrite using `[compAt_emb θ hθ τ V W P Q y]`. Use `show 2 * (c τ * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ _ _).re = _`. Rewrite using `[herm_key V W τ _ _ (hPlτ τ) _ _ (hQrτ τ), trace_single]`. Rewrite using `[Fintype.sum_bool]`.

Simplify using `only [ℓ, zι, if_true, if_false, Bool.false_eq_true]`. Rewrite using `[hs, hs]`. Use `norm_le_re (c τ) (compAt θ τ y k l) (hc τ)` as an intermediate fact. Rewrite using `[add_comm]`. Conclude with `this`.

Establish `hS : ∀ y : Mx D a b, (∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ≤ ∑ i, ℓ i y`. Introduce `y`. Simplify using `only [Fintype.sum_prod_type]`. Use `gcongr with τ _ k _ l _`. Conclude with `hterm y τ k l`.

Take `⟨τ0⟩ : Nonempty D.what₂.Tau` from `⟨D.eTau.symm 1⟩`. Take `⟨C0, hC0⟩` from `hf τ0 0 0`. Use `choose Cf hCf using fun i : D.what₂.Tau × Fin a × Fin b × Bool => hf i.1 (zι i) N`. Use `⟨(Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * (C0 + ∑ i, Cf i), fun y => ?_⟩` and prove the remaining obligations. Set `u : Option (D.what₂.Tau × Fin a × Fin b × Bool) → ℝ` to `fun o => o.elim 1 fun i => ℓ i y`.

Apply the tactic sequence `have hu : ∀ o, 0 ≤ u o := fun o => by cases o <;> simp [u, ℓ]`. Establish `hsum : ∑ o, u o = 1 + ∑ i, ℓ i y` using `by rw [Fintype.sum_option]; rfl`. Establish `hpow : ∑ o, u o ^ N = 1 + ∑ i, ℓ i y ^ N` using `by rw [Fintype.sum_option]; simp [u]`. Establish `hS0 : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖` using `by positivity`. Establish `hf0 : 0 ≤ ‖f y‖` using `norm_nonneg _`.

Establish `hC0' : ‖f y‖ ≤ C0` using `by simpa using hC0 y`. Establish `hCf' : ∑ i, ℓ i y ^ N * ‖f y‖ ≤ ∑ i, Cf i` using `Finset.sum_le_sum fun i _ => hCf i y`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decay_real_coords : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, (∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ y : Mx D a b, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y))| ^ m * ‖f y‖ ≤ C) → ∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C := by
  intro D V W a b P Q hP hQ θ hθ f hf N
  classical
  obtain ⟨Pl, hPl⟩ := exists_left_inv P hP
  obtain ⟨Qr, hQr⟩ := exists_right_inv Q hQ
  have hPlτ : ∀ τ, Pl.map (tauE D τ) * P.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hPl, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQrτ : ∀ τ, Q.map (tauE D τ) * Qr.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hQr, Matrix.map_one _ (map_zero _) (map_one _)]
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let zOf : D.what₂.Tau → Matrix (Fin a) (Fin b) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun τ X =>
    (gramAt D W τ)⁻¹ * (Pl.map (tauE D τ))ᴴ * X * (Qr.map (tauE D τ))ᴴ * gramAt D V τ
  let zι : D.what₂.Tau × Fin a × Fin b × Bool → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun i =>
    zOf i.1 (Matrix.single i.2.1 i.2.2.1 (if i.2.2.2 then Complex.I * (c i.1)⁻¹ else (c i.1)⁻¹))
  let ℓ : D.what₂.Tau × Fin a × Fin b × Bool → Mx D a b → ℝ := fun i y =>
    |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W i.1 (zι i) (compAt θ i.1 (GlobalTheory.IsoMean.emb V W P Q y))|
  have hterm : ∀ (y : Mx D a b) (τ : D.what₂.Tau) (k : Fin a) (l : Fin b),
      ‖θ τ (infPart D (y k l))‖ ≤ ∑ β : Bool, ℓ (τ, k, l, β) y := by
    intro y τ k l
    have hs : ∀ α : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ (zOf τ (Matrix.single k l α))
        (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y)) = 2 * (c τ * (star (compAt θ τ y k l) * α)).re := by
      intro α
      rw [compAt_emb θ hθ τ V W P Q y]
      show 2 * (c τ * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ _ _).re = _
      rw [herm_key V W τ _ _ (hPlτ τ) _ _ (hQrτ τ), trace_single]
    rw [Fintype.sum_bool]
    simp only [ℓ, zι, if_true, if_false, Bool.false_eq_true]
    rw [hs, hs]
    have := norm_le_re (c τ) (compAt θ τ y k l) (hc τ)
    rw [add_comm]
    exact this
  have hS : ∀ y : Mx D a b, (∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ≤ ∑ i, ℓ i y := by
    intro y
    simp only [Fintype.sum_prod_type]
    gcongr with τ _ k _ l _
    exact hterm y τ k l
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨C0, hC0⟩ := hf τ0 0 0
  choose Cf hCf using fun i : D.what₂.Tau × Fin a × Fin b × Bool => hf i.1 (zι i) N
  refine ⟨(Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * (C0 + ∑ i, Cf i), fun y => ?_⟩
  let u : Option (D.what₂.Tau × Fin a × Fin b × Bool) → ℝ := fun o => o.elim 1 fun i => ℓ i y
  have hu : ∀ o, 0 ≤ u o := fun o => by cases o <;> simp [u, ℓ]
  have hsum : ∑ o, u o = 1 + ∑ i, ℓ i y := by rw [Fintype.sum_option]; rfl
  have hpow : ∑ o, u o ^ N = 1 + ∑ i, ℓ i y ^ N := by rw [Fintype.sum_option]; simp [u]
  have hS0 : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by positivity
  have hf0 : 0 ≤ ‖f y‖ := norm_nonneg _
  have hC0' : ‖f y‖ ≤ C0 := by simpa using hC0 y
  have hCf' : ∑ i, ℓ i y ^ N * ‖f y‖ ≤ ∑ i, Cf i := Finset.sum_le_sum fun i _ => hCf i y
  calc (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖
      ≤ (1 + ∑ i, ℓ i y) ^ N * ‖f y‖ := by gcongr; exact hS y
    _ = (∑ o, u o) ^ N * ‖f y‖ := by rw [hsum]
    _ ≤ ((Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * ∑ o, u o ^ N) * ‖f y‖ := by
        gcongr; exact sum_pow_le u hu N
    _ = (Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N *
          (‖f y‖ + ∑ i, ℓ i y ^ N * ‖f y‖) := by rw [hpow, ← Finset.sum_mul]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.DecayCoord
