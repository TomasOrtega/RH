import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLeviClosureMem
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviDecompGen

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviDecomp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX _ hH m hm q hqr hqx`. Take `rfl` from `hH.rank`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Use `set P := fromCols H.ι (cols2 H.x H.y) with hP`.

Establish `hK : Pᵀ * X.J * P.map σ = fromBlocks X₁.J 0 0 swap2` using `gram_block σ hσ B (Y := reS X Y) hX.herm hH`. Use `set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef`. Establish `hsurj : ∀ v : Fin (n₁ + 2) → E, ∃ u, P *ᵥ u = v`. Establish `hle : Submodule.span E (X.L : Set (Fin (n₁ + 2) → E)) ≤ LinearMap.range (Matrix.mulVecLin P)`. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Take `⟨s', t', u, -, -, -, hz'⟩` from `hH.split z hz`. Use `⟨Sum.elim u ![s', t'], ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, hP, fromCols_mulVec]`. Establish `e1 : (Sum.elim u ![s', t'] : Fin n₁ ⊕ Fin 2 → E) ∘ Sum.inl = u` using `rfl`.

Establish `e2 : (Sum.elim u ![s', t'] : Fin n₁ ⊕ Fin 2 → E) ∘ Sum.inr = ![s', t']` using `rfl`. Rewrite using `[e1, e2, two_cols_mulVec, hz']`. Normalize the expressions using the abelian group laws. Establish `htop : Submodule.span E (X.L : Set (Fin (n₁ + 2) → E)) = ⊤` using `hX.lat.span_eq_top`. Introduce `v`.

Establish `hv : v ∈ LinearMap.range (Matrix.mulVecLin P)` using `hle (htop ▸ Submodule.mem_top)`. Take `⟨u, hu⟩` from `hv`. Conclude with `⟨u, hu⟩`. Use `choose wv hwv using hsurj`. Use `set Q : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := Matrix.of fun k j => wv (Pi.single j 1) k with hQ`.

Establish `hPQ : P * Q = 1`. Use extensionality with `i j`. Establish `h` using `congrFun (hwv (Pi.single j 1)) i`. Simplify using `only [mulVec, dotProduct] at h`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`.

Simplify using `only [hQ, Matrix.of_apply]`. Rewrite using `[h, Pi.single_apply]`. Establish `hQP : Q * P = 1` using `(Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv.symm).1 hPQ`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`. Establish `hfi : Function.Injective f` using `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)`.

Establish `hcf : ∀ e, cA σ (f e) = f (σ e)` using `fun e => by simp [cA, hf, inclR]`. Establish `hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))`. Use extensionality with `i (j | j)`. Both sides reduce to the same expression. Apply the tactic sequence `fin_cases j <;> rfl`.

Establish `hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1`. Rewrite using `[← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `hmapσ : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) E), (A.map f).map (cA σ) = (A.map σ).map f` using `fun A => by`. Use extensionality with `i j`. Simplify using `[hcf]`.

Establish `hinj : ∀ (z z' : Fin n₁ → AE F E) (a : AE F E), incM F H.ι *ᵥ z' = incM F H.ι *ᵥ z + a • incV F H.x → z' = z`. Introduce `z z' a h`. Use `set v : Fin n₁ ⊕ Fin 2 → AE F E := Sum.elim (z' - z) ![-a, 0] with hv`. Establish `h1 : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) *ᵥ v = 0`. Rewrite using `[fromCols_mulVec]`.

Establish `e1 : v ∘ Sum.inl = z' - z` using `rfl`. Establish `e2 : v ∘ Sum.inr = ![-a, 0]` using `rfl`. Rewrite using `[e1, e2, two_cols_mulVec, mulVec_sub, h]`. Simplify using the standard rewrite rules. Establish `h2 : v = 0`.

Rewrite using `[← Matrix.one_mulVec v, ← hQP', ← mulVec_mulVec, h1, mulVec_zero]`. Use function extensionality and compare the values at `i`. Use `congrFun h2 (Sum.inl i)` as an intermediate fact. Simplify `this` using `[hv, sub_eq_zero]`. Take `⟨g, hg⟩` from `(Subgroup.mem_subgroupOf).1 hqr`.

Establish `hmq : mat q = (g : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E).map f` using `by show ((q : GL (Fin (n₁ + 2)) (AE F E)) : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) (AE F E)) = _`. Rewrite using `[← hg]`. Both sides reduce to the same expression. Use `set g' : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E := (g : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) with hg'`. Establish `hgx : g' *ᵥ H.x = H.x`.

Use function extensionality and compare the values at `i`. Apply `hfi` to reduce the goal to its premises. Use `congrFun hqx i` as an intermediate fact. Rewrite `this` using `[hmq]`. Rewrite using `[RingHom.map_mulVec]`.

Conclude with `this`. Establish `hgu : g'ᵀ * X.J * g'.map σ = X.J`. Establish `h2 : (mat q)ᵀ * incM F X.J * (mat q).map (cA σ) = incM F X.J` using `q.2`. Rewrite `h2` using `[hmq, hmapσ]`. Establish `h3 : (g'ᵀ * X.J * g'.map σ).map f = X.J.map f`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Conclude with `h2`. Conclude with `Matrix.map_injective hfi h3`. Use `set C := Q * g' * P with hCdef`. Establish `hgP : g' * P = P * C`.

Rewrite using `[hCdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]`. Establish `hCu : Cᵀ * K * C.map σ = K`. Rewrite using `[← hK]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.transpose_mul, map_mul_alg, Matrix.mul_assoc]`.

Use `_ = (g' * P)ᵀ * X.J * (g' * P).map σ := by rw [hgP]`. Use `_ = Pᵀ * (g'ᵀ * X.J * g'.map σ) * P.map σ := by`. Simplify using `only [Matrix.transpose_mul, map_mul_alg, Matrix.mul_assoc]`. Use `_ = Pᵀ * X.J * P.map σ := by rw [hgu]`. Establish `hPx : P *ᵥ Pi.single (Sum.inr 0) 1 = H.x`.

Rewrite using `[mulVec_single_one]`. Use extensionality with `i`. Simplify using `[P, cols2]`. Establish `hC0 : C *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1`. Rewrite using `[hCdef, ← mulVec_mulVec, ← mulVec_mulVec, hPx, hgx, ← hPx, mulVec_mulVec, hQP, one_mulVec]`.

Establish `hCc : ∀ a, C a (Sum.inr 0) = (Pi.single (Sum.inr 0) 1 : Fin n₁ ⊕ Fin 2 → E) a` using `fun a => by`. Simplify `congrFun hC0 a` using `[mulVec_single_one]`. Establish `hc1 : ∀ j, C (Sum.inr 1) (Sum.inl j) = 0`. Introduce `j`. Establish `h` using `congrFun (congrFun hCu (Sum.inl j)) (Sum.inr 0)`.

Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hKdef, swap2, hCc] at h`. Conclude with `h`. Use `set g₀ : Matrix (Fin n₁) (Fin n₁) E := Matrix.of fun i j => C (Sum.inl i) (Sum.inl j) with hg₀`. Use `set a₀ : Fin n₁ → E := fun j => C (Sum.inr 0) (Sum.inl j) with ha₀`. Establish `hgι : g' * H.ι = H.ι * g₀ + vecMulVec H.x a₀`.

Use extensionality with `r j`. Establish `h` using `congrFun (congrFun hgP r) (Sum.inl j)`. Simplify using `[Matrix.mul_apply, hP, Fintype.sum_sum_type, Fin.sum_univ_two, cols2, hc1, vecMulVec, hg₀, ha₀] at h ⊢`. Take the linear combination `h`. Establish `hg₀u : g₀ᵀ * X₁.J * g₀.map σ = X₁.J`.

Use extensionality with `i j`. Establish `h'` using `congrFun (congrFun hCu (Sum.inl i)) (Sum.inl j)`. Simplify using `[Matrix.mul_apply, hKdef, Fintype.sum_sum_type, Fin.sum_univ_two, swap2, hc1, hg₀] at h' ⊢`. Take the linear combination `h'`. Establish `hJdet : X.J.det ≠ 0`.

Establish `h` using `GlobalTheory.LeviElem.det_ne_of_sig _ (hX.sig w)`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `: (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det` using `(RingHom.map_det (B.emb w).1 _).symm`. Rewrite using `[this, h0, map_zero]`.

Establish `hJu : IsUnit X.J.det` using `isUnit_iff_ne_zero.2 hJdet`. Establish `hKr : K * (Q.map σ * X.J⁻¹ * Qᵀ) = 1`. Rewrite using `[← hK]`. Establish `hPQσ : P.map σ * Q.map σ = 1`. Rewrite using `[← map_mul_alg, hPQ]`.

Conclude with `Matrix.map_one _ (map_zero σ) (map_one σ)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (Q * P)ᵀ := by`. Rewrite using `[hPQσ, Matrix.mul_one, Matrix.mul_assoc Pᵀ, mul_nonsing_inv _ hJu, Matrix.mul_one, Matrix.transpose_mul]`.

Use `_ = 1 := by rw [hQP, Matrix.transpose_one]`. Establish `hdet : X₁.J.det ≠ 0`. Establish `h` using `Matrix.det_ne_zero_of_right_inverse hKr`. Rewrite `h` using `[hKdef, det_fromBlocks_zero₂₁]`. Conclude with `left_ne_zero_of_mul h`.

Establish `hdet0 : g₀.det ≠ 0`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises. Use `congrArg Matrix.det hg₀u` as an intermediate fact. Rewrite `this` using `[det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul]`.

Conclude with `this.symm`. Use `set G0 : GL (Fin n₁) E := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀ hdet0 with hG0`. Establish `hG0v : (G0 : Matrix (Fin n₁) (Fin n₁) E) = g₀` using `rfl`. Establish `hγmem : Matrix.GeneralLinearGroup.map f G0 ∈ UG (cA σ) (incM F X₁.J)` using `by show ((G0 : Matrix (Fin n₁) (Fin n₁) E).map f)ᵀ * incM F X₁.J * ((G0 : Matrix (Fin n₁) (Fin n₁) E).map f).map (cA σ) = incM F X₁.J`. Rewrite using `[hG0v, hmapσ, show incM F X₁.J = X₁.J.map f from rfl, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg₀u]`.

Use `set γU : UA σ X₁.J := ⟨Matrix.GeneralLinearGroup.map f G0, hγmem⟩ with hγU`. Establish `hmatγ : mat γU = g₀.map f` using `rfl`. Establish `hγr : γU ∈ ratU σ X₁.J` using `Subgroup.mem_subgroupOf.2 ⟨G0, rfl⟩`. Establish `hqι : mat q * incM F H.ι = incM F H.ι * mat γU + vecMulVec (incV F H.x) (fun j => f (a₀ j))`. Rewrite using `[hmq, hmatγ]`.

Use `show g'.map f * H.ι.map f = H.ι.map f * g₀.map f + _`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hgι]`. Use extensionality with `r j`. Rewrite using `[Matrix.map_apply, Matrix.add_apply, map_add, Matrix.add_apply, Matrix.map_apply, vecMulVec_apply, vecMulVec_apply, map_mul]`. Both sides reduce to the same expression.

Take `⟨hmx, -, hmι⟩` from `hm 1 γU`. Simplify using `only [Units.val_one, one_smul] at hmx`. Establish `hmix : mat (m 1 γU)⁻¹ *ᵥ incV F H.x = incV F H.x`. Combine the equalities or inequalities in the displayed calculation. Establish `hγN : (m 1 γU)⁻¹ * q ∈ unip σ X H`.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨?_, fun z => ⟨(fun j => f (a₀ j)) ⬝ᵥ z, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mat_mul', ← mulVec_mulVec, hqx, hmix]`. Establish `e : mat ((m 1 γU)⁻¹ * q) * incM F H.ι = incM F H.ι + vecMulVec (incV F H.x) (fun j => f (a₀ j))`. Rewrite using `[mat_mul', Matrix.mul_assoc, hqι, ← hmι, Matrix.mul_add, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul, Matrix.mul_vecMulVec, hmix]`.

Rewrite using `[mulVec_mulVec, e, add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]`. Use `⟨⟨γU, hγr⟩, hγN, ?_⟩` and prove the remaining obligations. Introduce `γ' hγ'`. Establish `hd` using `(unip σ X H).mul_mem hγ' ((unip σ X H).inv_mem hγN)`. Establish `hde : (m 1 (γ' : UA σ X₁.J))⁻¹ * q * ((m 1 γU)⁻¹ * q)⁻¹ = (m 1 (γ' : UA σ X₁.J))⁻¹ * m 1 γU` using `by group`.

Rewrite `hd` using `[hde]`. Take `⟨-, hdz⟩` from `prop_of_mem_unip H hd`. Take `⟨-, -, hmι'⟩` from `hm 1 (γ' : UA σ X₁.J)`. Establish `hinv' : mat (m 1 (γ' : UA σ X₁.J))⁻¹ * incM F H.ι = incM F H.ι * mat (γ' : UA σ X₁.J)⁻¹` using `inv_intertwine (mat_inv_mul' _) (mat_mul_inv' _) hmι'`. Establish `hdι : mat ((m 1 (γ' : UA σ X₁.J))⁻¹ * m 1 γU) * incM F H.ι = incM F H.ι * mat ((γ' : UA σ X₁.J)⁻¹ * γU)`.

Rewrite using `[mat_mul', mat_mul', Matrix.mul_assoc, hmι, ← Matrix.mul_assoc, hinv', Matrix.mul_assoc]`. Establish `hfix : ∀ z, mat ((γ' : UA σ X₁.J)⁻¹ * γU) *ᵥ z = z`. Introduce `z`. Take `⟨a, ha⟩` from `hdz z`. Rewrite `ha` using `[mulVec_mulVec, hdι, ← mulVec_mulVec]`.

Conclude with `hinj z _ a ha`. Establish `h1 : (γ' : UA σ X₁.J)⁻¹ * γU = 1`. Apply `eq_of_mat_eq` to reduce the goal to its premises. Use extensionality with `i j`. Use `congrFun (hfix (Pi.single j 1)) i` as an intermediate fact.

Rewrite `this` using `[mulVec_single_one]`. Simplify `this` using `[mat_one', Matrix.one_apply, Pi.single_apply, eq_comm]`. Conclude with `Subtype.ext (inv_mul_eq_one.1 h1)`.
-/
theorem decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ q ∈ ratU σ X.J, mat q *ᵥ incV F H.x = incV F H.x → ∃! γ : ratU σ X₁.J, (m 1 γ.1)⁻¹ * q ∈ unip σ X H := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX _ hH m hm q hqr hqx
  obtain rfl := hH.rank
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * X.J * P.map σ = fromBlocks X₁.J 0 0 swap2 := gram_block σ hσ B (Y := reS X Y) hX.herm hH
  set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef

  have hsurj : ∀ v : Fin (n₁ + 2) → E, ∃ u, P *ᵥ u = v := by
    have hle : Submodule.span E (X.L : Set (Fin (n₁ + 2) → E)) ≤ LinearMap.range (Matrix.mulVecLin P) := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨s', t', u, -, -, -, hz'⟩ := hH.split z hz
      refine ⟨Sum.elim u ![s', t'], ?_⟩
      rw [Matrix.mulVecLin_apply, hP, fromCols_mulVec]
      have e1 : (Sum.elim u ![s', t'] : Fin n₁ ⊕ Fin 2 → E) ∘ Sum.inl = u := rfl
      have e2 : (Sum.elim u ![s', t'] : Fin n₁ ⊕ Fin 2 → E) ∘ Sum.inr = ![s', t'] := rfl
      rw [e1, e2, two_cols_mulVec, hz']
      abel
    have htop : Submodule.span E (X.L : Set (Fin (n₁ + 2) → E)) = ⊤ := hX.lat.span_eq_top
    intro v
    have hv : v ∈ LinearMap.range (Matrix.mulVecLin P) := hle (htop ▸ Submodule.mem_top)
    obtain ⟨u, hu⟩ := hv
    exact ⟨u, hu⟩
  choose wv hwv using hsurj
  set Q : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := Matrix.of fun k j => wv (Pi.single j 1) k with hQ
  have hPQ : P * Q = 1 := by
    ext i j
    have h := congrFun (hwv (Pi.single j 1)) i
    simp only [mulVec, dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hQ, Matrix.of_apply]
    rw [h, Pi.single_apply]
  have hQP : Q * P = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv.symm).1 hPQ
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hfi : Function.Injective f := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hmapσ : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) E), (A.map f).map (cA σ) = (A.map σ).map f := fun A => by
    ext i j; simp [hcf]

  have hinj : ∀ (z z' : Fin n₁ → AE F E) (a : AE F E), incM F H.ι *ᵥ z' = incM F H.ι *ᵥ z + a • incV F H.x → z' = z := by
    intro z z' a h
    set v : Fin n₁ ⊕ Fin 2 → AE F E := Sum.elim (z' - z) ![-a, 0] with hv
    have h1 : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) *ᵥ v = 0 := by
      rw [fromCols_mulVec]
      have e1 : v ∘ Sum.inl = z' - z := rfl
      have e2 : v ∘ Sum.inr = ![-a, 0] := rfl
      rw [e1, e2, two_cols_mulVec, mulVec_sub, h]
      simp
    have h2 : v = 0 := by
      rw [← Matrix.one_mulVec v, ← hQP', ← mulVec_mulVec, h1, mulVec_zero]
    funext i
    have := congrFun h2 (Sum.inl i)
    simpa [hv, sub_eq_zero] using this

  obtain ⟨g, hg⟩ := (Subgroup.mem_subgroupOf).1 hqr
  have hmq : mat q = (g : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E).map f := by
    show ((q : GL (Fin (n₁ + 2)) (AE F E)) : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) (AE F E)) = _
    rw [← hg]; rfl
  set g' : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E := (g : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) with hg'
  have hgx : g' *ᵥ H.x = H.x := by
    funext i
    apply hfi
    have := congrFun hqx i
    rw [hmq] at this
    rw [RingHom.map_mulVec]
    exact this
  have hgu : g'ᵀ * X.J * g'.map σ = X.J := by
    have h2 : (mat q)ᵀ * incM F X.J * (mat q).map (cA σ) = incM F X.J := q.2
    rw [hmq, hmapσ] at h2
    have h3 : (g'ᵀ * X.J * g'.map σ).map f = X.J.map f := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]; exact h2
    exact Matrix.map_injective hfi h3
  set C := Q * g' * P with hCdef
  have hgP : g' * P = P * C := by
    rw [hCdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hCu : Cᵀ * K * C.map σ = K := by
    rw [← hK]
    calc Cᵀ * (Pᵀ * X.J * P.map σ) * C.map σ = (P * C)ᵀ * X.J * (P * C).map σ := by
          simp only [Matrix.transpose_mul, map_mul_alg, Matrix.mul_assoc]
      _ = (g' * P)ᵀ * X.J * (g' * P).map σ := by rw [hgP]
      _ = Pᵀ * (g'ᵀ * X.J * g'.map σ) * P.map σ := by
          simp only [Matrix.transpose_mul, map_mul_alg, Matrix.mul_assoc]
      _ = Pᵀ * X.J * P.map σ := by rw [hgu]
  have hPx : P *ᵥ Pi.single (Sum.inr 0) 1 = H.x := by
    rw [mulVec_single_one]; ext i; simp [P, cols2]
  have hC0 : C *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
    rw [hCdef, ← mulVec_mulVec, ← mulVec_mulVec, hPx, hgx, ← hPx, mulVec_mulVec, hQP, one_mulVec]
  have hCc : ∀ a, C a (Sum.inr 0) = (Pi.single (Sum.inr 0) 1 : Fin n₁ ⊕ Fin 2 → E) a := fun a => by
    simpa [mulVec_single_one] using congrFun hC0 a
  have hc1 : ∀ j, C (Sum.inr 1) (Sum.inl j) = 0 := by
    intro j
    have h := congrFun (congrFun hCu (Sum.inl j)) (Sum.inr 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hKdef, swap2, hCc] at h
    exact h
  set g₀ : Matrix (Fin n₁) (Fin n₁) E := Matrix.of fun i j => C (Sum.inl i) (Sum.inl j) with hg₀
  set a₀ : Fin n₁ → E := fun j => C (Sum.inr 0) (Sum.inl j) with ha₀
  have hgι : g' * H.ι = H.ι * g₀ + vecMulVec H.x a₀ := by
    ext r j
    have h := congrFun (congrFun hgP r) (Sum.inl j)
    simp [Matrix.mul_apply, hP, Fintype.sum_sum_type, Fin.sum_univ_two, cols2, hc1, vecMulVec, hg₀, ha₀] at h ⊢
    linear_combination h
  have hg₀u : g₀ᵀ * X₁.J * g₀.map σ = X₁.J := by
    ext i j
    have h' := congrFun (congrFun hCu (Sum.inl i)) (Sum.inl j)
    simp [Matrix.mul_apply, hKdef, Fintype.sum_sum_type, Fin.sum_univ_two, swap2, hc1, hg₀] at h' ⊢
    linear_combination h'
  have hJdet : X.J.det ≠ 0 := by
    have h := GlobalTheory.LeviElem.det_ne_of_sig _ (hX.sig w)
    intro h0
    apply h
    have : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  have hJu : IsUnit X.J.det := isUnit_iff_ne_zero.2 hJdet
  have hKr : K * (Q.map σ * X.J⁻¹ * Qᵀ) = 1 := by
    rw [← hK]
    have hPQσ : P.map σ * Q.map σ = 1 := by
      rw [← map_mul_alg, hPQ]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
    calc Pᵀ * X.J * P.map σ * (Q.map σ * X.J⁻¹ * Qᵀ) = Pᵀ * X.J * (P.map σ * Q.map σ) * X.J⁻¹ * Qᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Q * P)ᵀ := by
          rw [hPQσ, Matrix.mul_one, Matrix.mul_assoc Pᵀ, mul_nonsing_inv _ hJu, Matrix.mul_one, Matrix.transpose_mul]
      _ = 1 := by rw [hQP, Matrix.transpose_one]
  have hdet : X₁.J.det ≠ 0 := by
    have h := Matrix.det_ne_zero_of_right_inverse hKr
    rw [hKdef, det_fromBlocks_zero₂₁] at h
    exact left_ne_zero_of_mul h
  have hdet0 : g₀.det ≠ 0 := by
    intro h0; apply hdet
    have := congrArg Matrix.det hg₀u
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at this
    exact this.symm
  set G0 : GL (Fin n₁) E := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀ hdet0 with hG0
  have hG0v : (G0 : Matrix (Fin n₁) (Fin n₁) E) = g₀ := rfl
  have hγmem : Matrix.GeneralLinearGroup.map f G0 ∈ UG (cA σ) (incM F X₁.J) := by
    show ((G0 : Matrix (Fin n₁) (Fin n₁) E).map f)ᵀ * incM F X₁.J * ((G0 : Matrix (Fin n₁) (Fin n₁) E).map f).map (cA σ) = incM F X₁.J
    rw [hG0v, hmapσ, show incM F X₁.J = X₁.J.map f from rfl, ← Matrix.transpose_map, ← Matrix.map_mul,
      ← Matrix.map_mul, hg₀u]
  set γU : UA σ X₁.J := ⟨Matrix.GeneralLinearGroup.map f G0, hγmem⟩ with hγU
  have hmatγ : mat γU = g₀.map f := rfl
  have hγr : γU ∈ ratU σ X₁.J := Subgroup.mem_subgroupOf.2 ⟨G0, rfl⟩
  have hqι : mat q * incM F H.ι = incM F H.ι * mat γU + vecMulVec (incV F H.x) (fun j => f (a₀ j)) := by
    rw [hmq, hmatγ]
    show g'.map f * H.ι.map f = H.ι.map f * g₀.map f + _
    rw [← Matrix.map_mul, ← Matrix.map_mul, hgι]
    ext r j
    rw [Matrix.map_apply, Matrix.add_apply, map_add, Matrix.add_apply, Matrix.map_apply, vecMulVec_apply, vecMulVec_apply,
      map_mul]
    rfl
  obtain ⟨hmx, -, hmι⟩ := hm 1 γU
  simp only [Units.val_one, one_smul] at hmx
  have hmix : mat (m 1 γU)⁻¹ *ᵥ incV F H.x = incV F H.x := by
    calc mat (m 1 γU)⁻¹ *ᵥ incV F H.x = mat (m 1 γU)⁻¹ *ᵥ (mat (m 1 γU) *ᵥ incV F H.x) := by rw [hmx]
      _ = incV F H.x := by rw [mulVec_mulVec, mat_inv_mul', one_mulVec]
  have hγN : (m 1 γU)⁻¹ * q ∈ unip σ X H := by
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ⟨(fun j => f (a₀ j)) ⬝ᵥ z, ?_⟩⟩
    · rw [mat_mul', ← mulVec_mulVec, hqx, hmix]
    · have e : mat ((m 1 γU)⁻¹ * q) * incM F H.ι = incM F H.ι + vecMulVec (incV F H.x) (fun j => f (a₀ j)) := by
        rw [mat_mul', Matrix.mul_assoc, hqι, ← hmι, Matrix.mul_add, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul,
          Matrix.mul_vecMulVec, hmix]
      rw [mulVec_mulVec, e, add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  refine ⟨⟨γU, hγr⟩, hγN, ?_⟩
  intro γ' hγ'
  have hd := (unip σ X H).mul_mem hγ' ((unip σ X H).inv_mem hγN)
  have hde : (m 1 (γ' : UA σ X₁.J))⁻¹ * q * ((m 1 γU)⁻¹ * q)⁻¹ = (m 1 (γ' : UA σ X₁.J))⁻¹ * m 1 γU := by group
  rw [hde] at hd
  obtain ⟨-, hdz⟩ := prop_of_mem_unip H hd
  obtain ⟨-, -, hmι'⟩ := hm 1 (γ' : UA σ X₁.J)
  have hinv' : mat (m 1 (γ' : UA σ X₁.J))⁻¹ * incM F H.ι = incM F H.ι * mat (γ' : UA σ X₁.J)⁻¹ :=
    inv_intertwine (mat_inv_mul' _) (mat_mul_inv' _) hmι'
  have hdι : mat ((m 1 (γ' : UA σ X₁.J))⁻¹ * m 1 γU) * incM F H.ι = incM F H.ι * mat ((γ' : UA σ X₁.J)⁻¹ * γU) := by
    rw [mat_mul', mat_mul', Matrix.mul_assoc, hmι, ← Matrix.mul_assoc, hinv', Matrix.mul_assoc]
  have hfix : ∀ z, mat ((γ' : UA σ X₁.J)⁻¹ * γU) *ᵥ z = z := by
    intro z
    obtain ⟨a, ha⟩ := hdz z
    rw [mulVec_mulVec, hdι, ← mulVec_mulVec] at ha
    exact hinj z _ a ha
  have h1 : (γ' : UA σ X₁.J)⁻¹ * γU = 1 := by
    apply eq_of_mat_eq
    ext i j
    have := congrFun (hfix (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    simpa [mat_one', Matrix.one_apply, Pi.single_apply, eq_comm] using this
  exact Subtype.ext (inv_mul_eq_one.1 h1)

end GlobalTheory.LeviDecompGen
