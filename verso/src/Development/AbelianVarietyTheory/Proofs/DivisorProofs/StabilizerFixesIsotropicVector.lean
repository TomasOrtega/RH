import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.StabDec

open Matrix GlobalTheory.LeviElem

section Abstract

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `set P := fromCols ι (cols2 x y) with hP`. Use `set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) R := fromBlocks J₁ 0 0 swap2 with hKdef`. Use `set D := Q * M * P with hD`. Establish `hPD : P * D = M * P`. Rewrite using `[hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]`.

Establish `hDK : Dᵀ * K * D.map s = K`. Establish `h1 : Dᵀ * (Pᵀ * J * P.map s) * D.map s = (P * D)ᵀ * J * (P * D).map s`. Simplify using `only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`. Establish `h2 : (M * P)ᵀ * J * (M * P).map s = Pᵀ * (Mᵀ * J * M.map s) * P.map s`. Simplify using `only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`.

Rewrite using `[← hK, h1, hPD, h2, hM]`. Establish `hPx : P *ᵥ Pi.single (Sum.inr 0) 1 = x`. Rewrite using `[mulVec_single_one]`. Use extensionality with `i`. Simplify using `[P, cols2, Matrix.col]`.

Establish `hDe : D *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1`. Rewrite using `[hD, ← mulVec_mulVec, hPx, ← mulVec_mulVec, hx, ← hPx, mulVec_mulVec, hQP, one_mulVec]`. Establish `hcol : ∀ i, D i (Sum.inr 0) = (Pi.single (Sum.inr 0) 1 : Fin b ⊕ Fin 2 → R) i` using `fun i => by`. Use `congrFun hDe i` as an intermediate fact. Rewrite `this` using `[mulVec_single_one]`. Then use the resulting hypothesis.

Establish `hrow : ∀ j, D (Sum.inr 1) (Sum.inl j) = 0` using `fun j => by`. Establish `h` using `congrFun (congrFun hDK (Sum.inl j)) (Sum.inr 0)`. Rewrite `h` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.map_apply, hcol] at h`. Rewrite `h` using `[Finset.sum_eq_single (Sum.inr 0) (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]`.

Simplify `h` using `[Matrix.mul_apply, K, Fintype.sum_sum_type, Fin.sum_univ_two, swap2]`. Use `⟨D.toBlocks₁₁, fun j => D (Sum.inr 0) (Sum.inl j), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hPD i) (Sum.inl j)`. Establish `h' : (M * P) i (Sum.inl j) = (M * ι) i j` using `by simp [Matrix.mul_apply, P]`.

Rewrite using `[← h', ← h]`. Simplify using `[Matrix.mul_apply, P, Fintype.sum_sum_type, Fin.sum_univ_two, hrow, cols2, toBlocks₁₁, vecMulVec_apply]`. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hDK (Sum.inl i)) (Sum.inl j)`. Simplify `h` using `[Matrix.mul_apply, K, Fintype.sum_sum_type, Fin.sum_univ_two, swap2, hrow, toBlocks₁₁]`.

Introduce `c hc`. Establish `h : c • (D - 1) = 0`. Establish `: D - 1 = Q * (M - 1) * P`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP]`. Rewrite using `[this, ← Matrix.smul_mul, ← Matrix.mul_smul, hc, Matrix.mul_zero, Matrix.zero_mul]`.

Use extensionality with `i j`. Establish `h'` using `congrFun (congrFun h (Sum.inl i)) (Sum.inl j)`. Simplify `h'` using `[toBlocks₁₁, Matrix.one_apply]`.
-/
theorem stab_blk {b n : ℕ} (s : R →+* R) (ι : Matrix (Fin n) (Fin b) R) (x y : Fin n → R)
    (J : Matrix (Fin n) (Fin n) R) (J₁ : Matrix (Fin b) (Fin b) R) (Q : Matrix (Fin b ⊕ Fin 2) (Fin n) R)
    (hQP : Q * fromCols ι (cols2 x y) = 1) (hPQ : fromCols ι (cols2 x y) * Q = 1)
    (hK : (fromCols ι (cols2 x y))ᵀ * J * (fromCols ι (cols2 x y)).map s = fromBlocks J₁ 0 0 swap2)
    (M : Matrix (Fin n) (Fin n) R) (hM : Mᵀ * J * M.map s = J) (hx : M *ᵥ x = x) :
    ∃ (β : Matrix (Fin b) (Fin b) R) (w : Fin b → R), M * ι = ι * β + vecMulVec x w ∧ βᵀ * J₁ * β.map s = J₁ ∧
      ∀ c : R, c • (M - 1) = 0 → c • (β - 1) = 0 := by
  set P := fromCols ι (cols2 x y) with hP
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) R := fromBlocks J₁ 0 0 swap2 with hKdef
  set D := Q * M * P with hD
  have hPD : P * D = M * P := by
    rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hDK : Dᵀ * K * D.map s = K := by
    have h1 : Dᵀ * (Pᵀ * J * P.map s) * D.map s = (P * D)ᵀ * J * (P * D).map s := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    have h2 : (M * P)ᵀ * J * (M * P).map s = Pᵀ * (Mᵀ * J * M.map s) * P.map s := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [← hK, h1, hPD, h2, hM]
  have hPx : P *ᵥ Pi.single (Sum.inr 0) 1 = x := by
    rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
  have hDe : D *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
    rw [hD, ← mulVec_mulVec, hPx, ← mulVec_mulVec, hx, ← hPx, mulVec_mulVec, hQP, one_mulVec]
  have hcol : ∀ i, D i (Sum.inr 0) = (Pi.single (Sum.inr 0) 1 : Fin b ⊕ Fin 2 → R) i := fun i => by
    have := congrFun hDe i
    rwa [mulVec_single_one] at this
  have hrow : ∀ j, D (Sum.inr 1) (Sum.inl j) = 0 := fun j => by
    have h := congrFun (congrFun hDK (Sum.inl j)) (Sum.inr 0)
    rw [Matrix.mul_apply] at h
    simp only [Matrix.map_apply, hcol] at h
    rw [Finset.sum_eq_single (Sum.inr 0) (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)] at h
    simpa [Matrix.mul_apply, K, Fintype.sum_sum_type, Fin.sum_univ_two, swap2] using h
  refine ⟨D.toBlocks₁₁, fun j => D (Sum.inr 0) (Sum.inl j), ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (congrFun hPD i) (Sum.inl j)
    have h' : (M * P) i (Sum.inl j) = (M * ι) i j := by simp [Matrix.mul_apply, P]
    rw [← h', ← h]
    simp [Matrix.mul_apply, P, Fintype.sum_sum_type, Fin.sum_univ_two, hrow, cols2, toBlocks₁₁, vecMulVec_apply]
  · ext i j
    have h := congrFun (congrFun hDK (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, K, Fintype.sum_sum_type, Fin.sum_univ_two, swap2, hrow, toBlocks₁₁] using h
  · intro c hc
    have h : c • (D - 1) = 0 := by
      have : D - 1 = Q * (M - 1) * P := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP]
      rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, hc, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have h' := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
    simpa [toBlocks₁₁, Matrix.one_apply] using h'

/- English proof (translation)
Establish `h2 : (m - 1) * cols2 x y = 0`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Use extensionality with `i k`. Use `fin_cases k`. Use `congrFun hx i` as an intermediate fact.

Simplify using `only [mulVec, dotProduct] at this`. Simplify using `[Matrix.mul_apply, cols2, this]`. Use `congrFun hy i` as an intermediate fact. Simplify using `only [mulVec, dotProduct] at this`. Simplify using `[Matrix.mul_apply, cols2, this]`.

Establish `h1 : (c • (m - 1)) * ι = 0`. Rewrite using `[Matrix.smul_mul, Matrix.sub_mul, hι, Matrix.one_mul]`. Establish `: ι * g - ι = ι * (g - 1)` using `by rw [Matrix.mul_sub, Matrix.mul_one]`. Rewrite using `[this, ← Matrix.mul_smul, hc, Matrix.mul_zero]`. Establish `h3 : (c • (m - 1)) * fromCols ι (cols2 x y) = 0`.

Rewrite using `[mul_fromCols, h1, Matrix.smul_mul, h2, smul_zero, fromCols_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem levi_supp {b n : ℕ} (ι : Matrix (Fin n) (Fin b) R) (x y : Fin n → R) (Q : Matrix (Fin b ⊕ Fin 2) (Fin n) R)
    (hPQ : fromCols ι (cols2 x y) * Q = 1) (m : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin b) (Fin b) R)
    (hx : m *ᵥ x = x) (hy : m *ᵥ y = y) (hι : m * ι = ι * g) (c : R) (hc : c • (g - 1) = 0) : c • (m - 1) = 0 := by
  have h2 : (m - 1) * cols2 x y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]
    ext i k
    fin_cases k
    · have := congrFun hx i
      simp only [mulVec, dotProduct] at this
      simp [Matrix.mul_apply, cols2, this]
    · have := congrFun hy i
      simp only [mulVec, dotProduct] at this
      simp [Matrix.mul_apply, cols2, this]
  have h1 : (c • (m - 1)) * ι = 0 := by
    rw [Matrix.smul_mul, Matrix.sub_mul, hι, Matrix.one_mul]
    have : ι * g - ι = ι * (g - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [this, ← Matrix.mul_smul, hc, Matrix.mul_zero]
  have h3 : (c • (m - 1)) * fromCols ι (cols2 x y) = 0 := by
    rw [mul_fromCols, h1, Matrix.smul_mul, h2, smul_zero, fromCols_zero]
  calc c • (m - 1) = (c • (m - 1)) * (fromCols ι (cols2 x y) * Q) := by rw [hPQ, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det hβ`. Rewrite `h` using `[det_mul, det_mul, det_transpose]`. Rewrite `hJ` using `[← h]`. Conclude with `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hJ)`.
-/
theorem isUnit_det_of_unitary {b : ℕ} (s : R →+* R) (J₁ β : Matrix (Fin b) (Fin b) R) (hJ : IsUnit J₁.det)
    (hβ : βᵀ * J₁ * β.map s = J₁) : IsUnit β.det := by
  have h := congrArg Matrix.det hβ
  rw [det_mul, det_mul, det_transpose] at h
  rw [← h] at hJ
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hJ)

end Abstract

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v q hq hqx`. Establish `hB` using `hT.base`. Establish `hG` using `hT.geo`. Establish `hG₁` using `hT₁.geo`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Establish `hdet : G₁.V.J.det ≠ 0`. Establish `h` using `det_ne_of_sig _ (hG₁.hV.sig w)`. Introduce `h0`. Apply `h` to reduce the goal to its premises.

Establish `: (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det` using `(RingHom.map_det (B.emb w).1 _).symm`. Rewrite using `[this, h0, map_zero]`. Use `set P := fromCols H.ι (cols2 H.x H.y) with hP`. Establish `hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2` using `gram_block σ hσ B hG.hV.herm hC.hH`. Use `set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef`.

Establish `hKdet : IsUnit Kᵀ.det`. Rewrite using `[det_transpose, hKdef, det_fromBlocks_zero₂₁]`. Simplify using `[swap2, det_fin_two, hdet]`. Use `set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ`. Establish `hQP : Q * P = 1`.

Establish `: (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ`. Rewrite using `[← hK]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`.

Establish `hcf : ∀ e, cA σ (f e) = f (σ e)` using `fun e => by simp [cA, hf, inclR]`. Establish `hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))`. Use extensionality with `i (j | j)`. Both sides reduce to the same expression. Apply the tactic sequence `fin_cases j <;> rfl`.

Establish `hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1`. Rewrite using `[← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `hPQ' : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * Q.map f = 1` using `(Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'`. Establish `hK' : (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)))ᵀ * incM F G.V.J * (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))).map (cA σ).toRingHom = fromBlocks (incM F G₁.V.J) 0 0 swap2`. Rewrite using `[← hPf]`.

Establish `h1 : (P.map f).map (cA σ).toRingHom = (P.map σ).map f`. Use extensionality with `i j`. Simplify using `[hcf]`. Establish `h2 : incM F G.V.J = G.V.J.map f` using `rfl`. Rewrite using `[h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]`.

Use `congr 1`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]`. Take `⟨β, α, hβι, hβU, hβs⟩` from `stab_blk (cA σ).toRingHom (incM F H.ι) (incV F H.x) (incV F H.y) (incM F G.V.J) (incM F G₁.V.J) (Q.map f) hQP' hPQ' hK' (mat q) q.2 hqx`.

Establish `hJA : IsUnit (incM F G₁.V.J).det`. Establish `: (incM F G₁.V.J).det = f G₁.V.J.det` using `(RingHom.map_det f _).symm`. Rewrite using `[this]`. Conclude with `(isUnit_iff_ne_zero.2 hdet).map f`. Establish `hβd : IsUnit β` using `(Matrix.isUnit_iff_isUnit_det β).2 (isUnit_det_of_unitary _ _ β hJA hβU)`.

Take `⟨βu, rfl⟩` from `hβd`. Set `g₀ : UA σ G₁.V.J` to `⟨βu, hβU⟩`. Establish `hg₀ : mat g₀ = (βu : Matrix (Fin b) (Fin b) (AE F E))` using `rfl`. Take `⟨m, hm⟩` from `levi_exists F E σ B b a' G G₁ H H' hC hB hG hG₁`. Use `set g := m 1 g₀ with hg`.

Establish `hlev : IsLevi H 1 g₀ g` using `hm 1 g₀`. Take `⟨hgx, hgy, hgι⟩` from `id hlev`. Establish `hgx' : mat g *ᵥ incV F H.x = incV F H.x` using `by rw [hgx]; simp`. Establish `hgy' : mat g *ᵥ incV F H.y = incV F H.y` using `by rw [hgy]; simp`. Establish `hsm : ∀ {k : ℕ} (a : AF F) (Z : Matrix (Fin k) (Fin k) (AE F E)), a • Z = (algebraMap (AF F) (AE F E) a) • Z` using `fun a Z => (algebraMap_smul (AE F E) a Z).symm`.

Establish `hg₀s : g₀ ∈ UAt σ G₁.V (evFin F v)` using `fun a ha => by`. Rewrite using `[hsm, hg₀]`. Conclude with `hβs _ (by rw [← hsm]; exact hq a ha)`. Establish `hgs : g ∈ UAt σ G.V (evFin F v)` using `fun a ha => by`. Rewrite using `[hsm]`.

Conclude with `levi_supp _ _ _ _ hPQ' (mat g) (mat g₀) hgx' hgy' hgι _ (by rw [← hsm]; exact hg₀s a ha)`. Establish `hinv : mat g⁻¹ * mat g = 1` using `by show (g.1⁻¹ * g.1 : GL (Fin (b + 2)) (AE F E)).1 = 1`. Simplify using the standard rewrite rules. Establish `hinv' : mat g * mat g⁻¹ = 1` using `by show (g.1 * g.1⁻¹ : GL (Fin (b + 2)) (AE F E)).1 = 1`. Simplify using the standard rewrite rules.

Establish `hmu : mat (q * g⁻¹) = mat q * mat g⁻¹` using `rfl`. Use `⟨q * g⁻¹, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, fun a ha => ?_, g₀, g, hlev, hgs, hg₀s, by simp⟩` and prove the remaining obligations. Rewrite using `[hmu, ← mulVec_mulVec] conv_lhs => rw [← hgx']`. Rewrite using `[mulVec_mulVec _ (mat g⁻¹), hinv, one_mulVec, hqx]`. Use `set z' := ((βu⁻¹ : (Matrix (Fin b) (Fin b) (AE F E))ˣ) : Matrix (Fin b) (Fin b) (AE F E)) *ᵥ z with hz'`.

Establish `hz : (βu : Matrix (Fin b) (Fin b) (AE F E)) *ᵥ z' = z`. Rewrite using `[hz', mulVec_mulVec, Units.mul_inv, one_mulVec]`. Use `⟨α ⬝ᵥ z', ?_⟩` and prove the remaining obligations. Establish `h1 : incM F H.ι *ᵥ z = mat g *ᵥ (incM F H.ι *ᵥ z')`. Rewrite using `[mulVec_mulVec, hgι, ← mulVec_mulVec, hg₀, hz]`.

Establish `h2 : mat (q * g⁻¹) *ᵥ (incM F H.ι *ᵥ z) = mat q *ᵥ (incM F H.ι *ᵥ z')`. Rewrite using `[h1, mulVec_mulVec, hmu, Matrix.mul_assoc, hinv, Matrix.mul_one]`. Rewrite using `[h2, mulVec_mulVec, hβι, add_mulVec, ← mulVec_mulVec, hz]`. Use `congr 1`. Use extensionality with `i`.

Simplify using `[vecMulVec_mulVec, mul_comm]`. Establish `h : mat (q * g⁻¹) - 1 = ((mat q - 1) - (mat g - 1)) * mat g⁻¹`. Rewrite using `[hmu, sub_sub_sub_cancel_right, Matrix.sub_mul, hinv']`. Rewrite using `[h, ← Matrix.smul_mul, smul_sub, hq a ha, hgs a ha, sub_zero, Matrix.zero_mul]`.
-/
theorem stab_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (q : UA σ G.V.J), q ∈ UAt σ G.V (evFin F v) → mat q *ᵥ incV F H.x = incV F H.x →
      ∃ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evFin F v) ∧ ∃ (g₀ : UA σ G₁.V.J) (g : UA σ G.V.J), IsLevi H 1 g₀ g ∧
        g ∈ UAt σ G.V (evFin F v) ∧ g₀ ∈ UAt σ G₁.V (evFin F v) ∧ q = u * g := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v q hq hqx
  have hB := hT.base
  have hG := hT.geo
  have hG₁ := hT₁.geo
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * Q.map f = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  have hK' : (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)))ᵀ * incM F G.V.J *
      (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))).map (cA σ).toRingHom =
      fromBlocks (incM F G₁.V.J) 0 0 swap2 := by
    rw [← hPf]
    have h1 : (P.map f).map (cA σ).toRingHom = (P.map σ).map f := by
      ext i j; simp [hcf]
    have h2 : incM F G.V.J = G.V.J.map f := rfl
    rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]
    congr 1
    · simp
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]
  obtain ⟨β, α, hβι, hβU, hβs⟩ := stab_blk (cA σ).toRingHom (incM F H.ι) (incV F H.x) (incV F H.y) (incM F G.V.J)
    (incM F G₁.V.J) (Q.map f) hQP' hPQ' hK' (mat q) q.2 hqx
  have hJA : IsUnit (incM F G₁.V.J).det := by
    have : (incM F G₁.V.J).det = f G₁.V.J.det := (RingHom.map_det f _).symm
    rw [this]
    exact (isUnit_iff_ne_zero.2 hdet).map f
  have hβd : IsUnit β := (Matrix.isUnit_iff_isUnit_det β).2 (isUnit_det_of_unitary _ _ β hJA hβU)
  obtain ⟨βu, rfl⟩ := hβd
  let g₀ : UA σ G₁.V.J := ⟨βu, hβU⟩
  have hg₀ : mat g₀ = (βu : Matrix (Fin b) (Fin b) (AE F E)) := rfl
  obtain ⟨m, hm⟩ := levi_exists F E σ B b a' G G₁ H H' hC hB hG hG₁
  set g := m 1 g₀ with hg
  have hlev : IsLevi H 1 g₀ g := hm 1 g₀
  obtain ⟨hgx, hgy, hgι⟩ := id hlev
  have hgx' : mat g *ᵥ incV F H.x = incV F H.x := by rw [hgx]; simp
  have hgy' : mat g *ᵥ incV F H.y = incV F H.y := by rw [hgy]; simp
  have hsm : ∀ {k : ℕ} (a : AF F) (Z : Matrix (Fin k) (Fin k) (AE F E)), a • Z = (algebraMap (AF F) (AE F E) a) • Z :=
    fun a Z => (algebraMap_smul (AE F E) a Z).symm
  have hg₀s : g₀ ∈ UAt σ G₁.V (evFin F v) := fun a ha => by
    rw [hsm, hg₀]
    exact hβs _ (by rw [← hsm]; exact hq a ha)
  have hgs : g ∈ UAt σ G.V (evFin F v) := fun a ha => by
    rw [hsm]
    exact levi_supp _ _ _ _ hPQ' (mat g) (mat g₀) hgx' hgy' hgι _ (by rw [← hsm]; exact hg₀s a ha)
  have hinv : mat g⁻¹ * mat g = 1 := by
    show (g.1⁻¹ * g.1 : GL (Fin (b + 2)) (AE F E)).1 = 1
    simp
  have hinv' : mat g * mat g⁻¹ = 1 := by
    show (g.1 * g.1⁻¹ : GL (Fin (b + 2)) (AE F E)).1 = 1
    simp
  have hmu : mat (q * g⁻¹) = mat q * mat g⁻¹ := rfl
  refine ⟨q * g⁻¹, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, fun a ha => ?_, g₀, g, hlev, hgs, hg₀s, by simp⟩
  · rw [hmu, ← mulVec_mulVec]
    conv_lhs => rw [← hgx']
    rw [mulVec_mulVec _ (mat g⁻¹), hinv, one_mulVec, hqx]
  · set z' := ((βu⁻¹ : (Matrix (Fin b) (Fin b) (AE F E))ˣ) : Matrix (Fin b) (Fin b) (AE F E)) *ᵥ z with hz'
    have hz : (βu : Matrix (Fin b) (Fin b) (AE F E)) *ᵥ z' = z := by
      rw [hz', mulVec_mulVec, Units.mul_inv, one_mulVec]
    refine ⟨α ⬝ᵥ z', ?_⟩
    have h1 : incM F H.ι *ᵥ z = mat g *ᵥ (incM F H.ι *ᵥ z') := by
      rw [mulVec_mulVec, hgι, ← mulVec_mulVec, hg₀, hz]
    have h2 : mat (q * g⁻¹) *ᵥ (incM F H.ι *ᵥ z) = mat q *ᵥ (incM F H.ι *ᵥ z') := by
      rw [h1, mulVec_mulVec, hmu, Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [h2, mulVec_mulVec, hβι, add_mulVec, ← mulVec_mulVec, hz]
    congr 1
    ext i
    simp [vecMulVec_mulVec, mul_comm]
  · have h : mat (q * g⁻¹) - 1 = ((mat q - 1) - (mat g - 1)) * mat g⁻¹ := by
      rw [hmu, sub_sub_sub_cancel_right, Matrix.sub_mul, hinv']
    rw [h, ← Matrix.smul_mul, smul_sub, hq a ha, hgs a ha, sub_zero, Matrix.zero_mul]

end GlobalTheory.ThK.LemF.StabDec
