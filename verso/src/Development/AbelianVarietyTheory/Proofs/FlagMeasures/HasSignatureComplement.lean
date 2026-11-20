import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.AutInhab

namespace GlobalTheory.AdaptedExists

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by simp | a + 1, j, f, h => by have := telescope a (fun i => j i.castSucc) (fun i => f i.castSucc) fun i => h i.castSucc rw [Fin.sum_univ_castSucc, ← Fin.succ_last, h, this, add_assoc] rfl`.
-/
theorem telescope : ∀ (a : ℕ) (j : Fin a → ℕ) (f : Fin (a + 1) → ℕ), (∀ i : Fin a, f i.succ = f i.castSucc + j i) →
    f (Fin.last a) = f 0 + ∑ i, j i
  | 0, _, _, _ => by simp
  | a + 1, j, f, h => by
    have := telescope a (fun i => j i.castSucc) (fun i => f i.castSucc) fun i => h i.castSucc
    rw [Fin.sum_univ_castSucc, ← Fin.succ_last, h, this, add_assoc]
    rfl

section

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

/- English proof (translation)
Simplify using `[Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]`.
-/
theorem hform_eq (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

/- English proof (translation)
Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`.
-/
theorem form_mulVec {k l : Type} [Fintype k] [Fintype l] (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) k E)
    (B : Matrix (Fin n) l E) (x : k → E) (y : l → E) :
    star (A *ᵥ x) ⬝ᵥ (J *ᵥ (B *ᵥ y)) = star x ⬝ᵥ ((Aᴴ * J * B) *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

/- English proof (translation)
Use extensionality with `r s`. Use `h (Pi.single r 1) (Pi.single s 1)` as an intermediate fact. Rewrite `this` using `[form_mulVec]`. Simplify `this` using `[Pi.star_single]`.
-/
theorem gram_eq_zero {k l : Type} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]
    (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) k E) (B : Matrix (Fin n) l E)
    (h : ∀ x y, star (A *ᵥ x) ⬝ᵥ (J *ᵥ (B *ᵥ y)) = 0) : Aᴴ * J * B = 0 := by
  ext r s
  have := h (Pi.single r 1) (Pi.single s 1)
  rw [form_mulVec] at this
  simpa [Pi.star_single] using this

/- English proof (translation)
Simplify using `[hJ, Matrix.mul_assoc]`.
-/
theorem gram_swap {k l : Type} [Fintype k] [Fintype l] {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J)
    (A : Matrix (Fin n) k E) (B : Matrix (Fin n) l E) : Bᴴ * J * A = (Aᴴ * J * B)ᴴ := by
  simp [hJ, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map φ hφ]`.
-/
theorem map_gram {E' : Type} [Field E'] [StarRing E'] (φ : E →+* E') (hφ : ∀ x, φ (star x) = star (φ x))
    {k l : Type} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) k E) (B : Matrix (Fin n) l E) :
    (A.map φ)ᴴ * J.map φ * B.map φ = (Aᴴ * J * B).map φ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map φ hφ]

end

/- English proof (translation)
Use `I.J_herm` as an intermediate fact. Use extensionality with `r s`. Simplify `congrFun (congrFun this r) s` using `[Formalism.UG.cT, starRingEnd_apply]`.
-/
theorem J_herm (I : AutInst) : I.Jᴴ = I.J := by
  have := I.J_herm
  ext r s
  simpa [Formalism.UG.cT, starRingEnd_apply] using congrFun (congrFun this r) s

/- English proof (translation)
Introduce `I p q hI φ`. Use `I.cm.totReal` as an intermediate fact. Use `set v := InfinitePlace.mk (φ.comp (algebraMap I.F I.E))`. Establish `hv : v.embedding = φ.comp (algebraMap I.F I.E)`. Break down `InfinitePlace.embedding_mk_eq (φ.comp (algebraMap I.F I.E)) with h | h` into its components or cases.

Conclude with `h`. Conclude with `h.trans (IsTotallyReal.complexEmbedding_isReal _)`. Establish `hn : ∀ (ψ : I.E →+* ℂ) (x : I.E), ψ (x * star x) = ((‖ψ x‖ ^ 2 : ℝ) : ℂ)` using `fun ψ x => by`. Rewrite using `[map_mul, I.cm.cmUnram.2.1, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hmk : InfinitePlace.mk (I.φ v) = InfinitePlace.mk φ`.

Use extensionality with `x`. Take `⟨a, ha⟩` from `(I.cm.fixed (x * star x)).1 (by simp [mul_comm])`. Establish `h1 : I.φ v (x * star x) = φ (x * star x)` using `by rw [← ha, I.φ_over, hv]; rfl`. Rewrite `h1` using `[hn, hn, Complex.ofReal_inj, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]`. Conclude with `h1`.

Rewrite using `[← (hI v).1, ← (hI v).2]`. Break down `InfinitePlace.mk_eq_iff.1 hmk with h | h` into its components or cases. Conclude with `h ▸ hasSignature_inst I v`. Use `hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_` and prove the remaining obligations. Use `map_gram (starRingEnd ℂ) (fun _ => rfl) (I.J.map (I.φ v)) (I.P v) (I.P v)` as an intermediate fact.

Rewrite `this` using `[I.P_spec]`. Rewrite using `[← h]`. Use `this.trans ?_` and prove the remaining obligations. Use extensionality with `r s`. Simplify using `only [Formalism.REAL.Jm, map_apply, diagonal_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hasSignature_map : ∀ (I : AutInst) (p q : ℕ), HasSig I p q → ∀ φ : I.E →+* ℂ, Formalism.UG.HasSignature (I.J.map φ) p q := by
  intro I p q hI φ
  have := I.cm.totReal
  set v := InfinitePlace.mk (φ.comp (algebraMap I.F I.E))
  have hv : v.embedding = φ.comp (algebraMap I.F I.E) := by
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap I.F I.E)) with h | h
    · exact h
    · exact h.trans (IsTotallyReal.complexEmbedding_isReal _)
  have hn : ∀ (ψ : I.E →+* ℂ) (x : I.E), ψ (x * star x) = ((‖ψ x‖ ^ 2 : ℝ) : ℂ) := fun ψ x => by
    rw [map_mul, I.cm.cmUnram.2.1, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hmk : InfinitePlace.mk (I.φ v) = InfinitePlace.mk φ := by
    ext x
    obtain ⟨a, ha⟩ := (I.cm.fixed (x * star x)).1 (by simp [mul_comm])
    have h1 : I.φ v (x * star x) = φ (x * star x) := by rw [← ha, I.φ_over, hv]; rfl
    rw [hn, hn, Complex.ofReal_inj, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] at h1
    exact h1
  rw [← (hI v).1, ← (hI v).2]
  rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
  · exact h ▸ hasSignature_inst I v
  · refine hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ))
      ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_
    have := map_gram (starRingEnd ℂ) (fun _ => rfl) (I.J.map (I.φ v)) (I.P v) (I.P v)
    rw [I.P_spec] at this
    rw [← h]
    refine this.trans ?_
    ext r s
    simp only [Formalism.REAL.Jm, map_apply, diagonal_apply]
    split_ifs <;> simp

/- English proof (translation)
Introduce `n m p q κ _ _ J T T' B hJ hs hn h1 h2 h3 h4 h5 h6`. Establish `hG : (Bᴴ * J * B)ᴴ = Bᴴ * J * B` using `(gram_swap hJ B B).symm`. Take `⟨ε, P, hP, hPG⟩` from `exists_frame (G := Bᴴ * J * B) (by unfold Formalism.UG.IsHerm; rw [Formalism.UG.P.cT_conj_eq, hG]) (IsUnit.mk0 _ h6)`. Establish `h3' : T'ᴴ * J * T = 1` using `by rw [gram_swap hJ, h3, conjTranspose_one]`. Establish `h4' : Bᴴ * J * T = 0` using `by rw [gram_swap hJ, h4, conjTranspose_zero]`.

Establish `h5' : Bᴴ * J * T' = 0` using `by rw [gram_swap hJ, h5, conjTranspose_zero]`. Take `⟨f⟩ : Nonempty (Fin n ≃ (κ ⊕ κ) ⊕ Fin m)` from `Fintype.card_eq.1 (by simp; omega)`. Use `set Q : Matrix (Fin n) ((κ ⊕ κ) ⊕ Fin m) ℂ := fromCols (fromCols (T + (1 / 2 : ℂ) • T') (T - (1 / 2 : ℂ) • T')) (B * P) with hQ`. Use `set δ : (κ ⊕ κ) ⊕ Fin m → Bool := Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε with hδ`. Establish `hQJ : Qᴴ * J * Q = fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (Formalism.REAL.Jm ε)`.

Rewrite `h1`, `h2`, `h3`, `h4`, `h5`, `h3'`, `h4'`, `h5'` using `[Matrix.mul_assoc]`. Establish `a1 : Tᴴ * (J * (B * P)) = 0` using `by rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, h4, Matrix.zero_mul]`. Establish `a2 : T'ᴴ * (J * (B * P)) = 0` using `by rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, h5, Matrix.zero_mul]`. Establish `a3 : Pᴴ * (Bᴴ * (J * (B * P))) = Formalism.REAL.Jm ε` using `by rw [← hPG]; simp only [Matrix.mul_assoc]`. Simplify using `only [hQ, conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc, mul_fromCols, fromRows_mul, conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, …`.

Apply the tactic sequence `ext ((r | r) | r) ((s | s) | s) <;> simp [Matrix.one_apply] <;> split_ifs <;> norm_num`. Establish `hF : (Q.submatrix id f)ᴴ * J * Q.submatrix id f = Formalism.REAL.Jm (δ ∘ f)`. Establish `: (Q.submatrix id f)ᴴ * J * Q.submatrix id f = (Qᴴ * J * Q).submatrix f f`. Use extensionality with `r s`. Simplify using `[Matrix.mul_apply]`.

Establish `hD : fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (Formalism.REAL.Jm ε) = diagonal fun a => if δ a = true then (1 : ℂ) else -1`. Apply the tactic sequence `ext ((r | r) | r) ((s | s) | s) <;> simp [hδ, Formalism.REAL.Jm, Matrix.one_apply, diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Both sides reduce to the same expression. Rewrite using `[this, hQJ, hD, submatrix_diagonal_equiv]`.

Both sides reduce to the same expression. Establish `hU : IsUnit (Q.submatrix id f)` using `IsUnit.of_mul_eq_one_right (Formalism.REAL.Jm (δ ∘ f) * ((Q.submatrix id f)ᴴ * J)) (by rw [Matrix.mul_assoc, hF, Formalism.REAL.Jm_mul_self])`. Take `⟨e1, e2⟩` from `Formalism.UG.P.signature_unique _ J _ _ _ _ hs (hasSignature_of_frame hU hF)`. Establish `hc : ∀ b : Bool, (univ.filter fun a => (δ ∘ f) a = b).card = (univ.filter fun a => ε a = b).card + Fintype.card κ` using `fun b => by`. Rewrite using `[Finset.card_filter, Finset.card_filter]`.

Use `(Equiv.sum_comp f fun a => if δ a = b then 1 else 0).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_sum_type, Fintype.sum_sum_type]`. Apply the tactic sequence `cases b <;> simp [hδ, add_comm]`. Rewrite using `[e1, e2, hc, hc, Nat.add_sub_cancel, Nat.add_sub_cancel]`. Conclude with `hasSignature_of_frame hP hPG`.
-/
theorem hasSignature_complement : ∀ (n m p q : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] (J : Matrix (Fin n) (Fin n) ℂ) (T T' : Matrix (Fin n) κ ℂ) (B : Matrix (Fin n) (Fin m) ℂ), Jᴴ = J → Formalism.UG.HasSignature J p q → n = m + 2 * Fintype.card κ → Tᴴ * J * T = 0 → T'ᴴ * J * T' = 0 → Tᴴ * J * T' = 1 → Tᴴ * J * B = 0 → T'ᴴ * J * B = 0 → (Bᴴ * J * B).det ≠ 0 → Formalism.UG.HasSignature (Bᴴ * J * B) (p - Fintype.card κ) (q - Fintype.card κ) := by
  intro n m p q κ _ _ J T T' B hJ hs hn h1 h2 h3 h4 h5 h6
  have hG : (Bᴴ * J * B)ᴴ = Bᴴ * J * B := (gram_swap hJ B B).symm
  obtain ⟨ε, P, hP, hPG⟩ := exists_frame (G := Bᴴ * J * B)
    (by unfold Formalism.UG.IsHerm; rw [Formalism.UG.P.cT_conj_eq, hG]) (IsUnit.mk0 _ h6)
  have h3' : T'ᴴ * J * T = 1 := by rw [gram_swap hJ, h3, conjTranspose_one]
  have h4' : Bᴴ * J * T = 0 := by rw [gram_swap hJ, h4, conjTranspose_zero]
  have h5' : Bᴴ * J * T' = 0 := by rw [gram_swap hJ, h5, conjTranspose_zero]
  obtain ⟨f⟩ : Nonempty (Fin n ≃ (κ ⊕ κ) ⊕ Fin m) := Fintype.card_eq.1 (by simp; omega)
  set Q : Matrix (Fin n) ((κ ⊕ κ) ⊕ Fin m) ℂ :=
    fromCols (fromCols (T + (1 / 2 : ℂ) • T') (T - (1 / 2 : ℂ) • T')) (B * P) with hQ
  set δ : (κ ⊕ κ) ⊕ Fin m → Bool := Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε with hδ
  have hQJ : Qᴴ * J * Q = fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (Formalism.REAL.Jm ε) := by
    rw [Matrix.mul_assoc] at h1 h2 h3 h4 h5 h3' h4' h5'
    have a1 : Tᴴ * (J * (B * P)) = 0 := by rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, h4, Matrix.zero_mul]
    have a2 : T'ᴴ * (J * (B * P)) = 0 := by rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, h5, Matrix.zero_mul]
    have a3 : Pᴴ * (Bᴴ * (J * (B * P))) = Formalism.REAL.Jm ε := by rw [← hPG]; simp only [Matrix.mul_assoc]
    simp only [hQ, conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc, mul_fromCols, fromRows_mul,
      conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2, h3, h3', h4', h5', a1, a2, a3]
    ext ((r | r) | r) ((s | s) | s) <;> simp [Matrix.one_apply] <;> split_ifs <;> norm_num
  have hF : (Q.submatrix id f)ᴴ * J * Q.submatrix id f = Formalism.REAL.Jm (δ ∘ f) := by
    have : (Q.submatrix id f)ᴴ * J * Q.submatrix id f = (Qᴴ * J * Q).submatrix f f := by
      ext r s; simp [Matrix.mul_apply]
    have hD : fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (Formalism.REAL.Jm ε) =
        diagonal fun a => if δ a = true then (1 : ℂ) else -1 := by
      ext ((r | r) | r) ((s | s) | s) <;> simp [hδ, Formalism.REAL.Jm, Matrix.one_apply, diagonal_apply]
      · split_ifs <;> simp
      · rfl
    rw [this, hQJ, hD, submatrix_diagonal_equiv]
    rfl
  have hU : IsUnit (Q.submatrix id f) :=
    IsUnit.of_mul_eq_one_right (Formalism.REAL.Jm (δ ∘ f) * ((Q.submatrix id f)ᴴ * J))
      (by rw [Matrix.mul_assoc, hF, Formalism.REAL.Jm_mul_self])
  obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ J _ _ _ _ hs (hasSignature_of_frame hU hF)
  have hc : ∀ b : Bool, (univ.filter fun a => (δ ∘ f) a = b).card =
      (univ.filter fun a => ε a = b).card + Fintype.card κ := fun b => by
    rw [Finset.card_filter, Finset.card_filter]
    refine (Equiv.sum_comp f fun a => if δ a = b then 1 else 0).trans ?_
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    cases b <;> simp [hδ, add_comm]
  rw [e1, e2, hc, hc, Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact hasSignature_of_frame hP hPG

section Blocks

variable {E : Type} [Field E] {n : ℕ}

/- English proof (translation)
Set `f : (k → E) ≃ₗ[E] U` to `LinearEquiv.ofFinrankEq _ _ (by simp [hU])`. Use `⟨LinearMap.toMatrix' (U.subtype ∘ₗ f.toLinearMap), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']`. Conclude with `⟨U.injective_subtype.comp f.injective, by simp [LinearMap.range_comp]⟩`.
-/
theorem exists_matrix_range {k : Type} [Fintype k] [DecidableEq k] (U : Submodule E (Fin n → E))
    (hU : Module.finrank E U = Fintype.card k) :
    ∃ T : Matrix (Fin n) k E, Function.Injective T.mulVecLin ∧ LinearMap.range T.mulVecLin = U := by
  let f : (k → E) ≃ₗ[E] U := LinearEquiv.ofFinrankEq _ _ (by simp [hU])
  refine ⟨LinearMap.toMatrix' (U.subtype ∘ₗ f.toLinearMap), ?_⟩
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  exact ⟨U.injective_subtype.comp f.injective, by simp [LinearMap.range_comp]⟩

variable [NumberField E]

/- English proof (translation)
Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ x hx`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩`.
-/
theorem exists_smul_mem {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ L := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

/- English proof (translation)
Establish `h1 : Submodule.span E (A : Set (Fin n → E)) ⊓ Submodule.span E (S : Set (Fin n → E)) = ⊥`. Use `eq_bot_iff.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨c, hc, hA⟩` from `exists_smul_mem hx.1`. Take `⟨d, hd, hS⟩` from `exists_smul_mem hx.2`. Establish `: (c * d) • x ∈ A ⊓ S` using `⟨by rw [mul_comm, mul_smul]; exact A.smul_mem _ hA, by rw [mul_smul]; exact S.smul_mem _ hS⟩`.

Rewrite `this` using `[h, Submodule.mem_bot, smul_eq_zero]`. Conclude with `this.resolve_left (mul_ne_zero hc hd)`. Establish `h2 : Submodule.span E ((A ⊔ S : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = Submodule.span E (A : Set (Fin n → E)) ⊔ Submodule.span E (S : Set (Fin n → E))`. Use `le_antisymm (Submodule.span_le.2 fun x hx => ?_) (sup_le (Submodule.span_mono (le_sup_left : A ≤ A ⊔ S)) (Submodule.span_mono (le_sup_right : S ≤ A ⊔ S)))` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`.

Conclude with `Submodule.add_mem_sup (Submodule.subset_span hy) (Submodule.subset_span hz)`. Use `Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span E (A : Set (Fin n → E))) (Submodule.span E (S : Set (Fin n → E)))` as an intermediate fact. Rewrite `this` using `[h1, finrank_bot, ← h2]`. Unfold `Formalism.HN.rkK`. Use linear arithmetic over natural numbers and integers.
-/
theorem rkK_add {A S : Submodule (𝓞 E) (Fin n → E)} (h : A ⊓ S = ⊥) :
    Formalism.HN.rkK (A ⊔ S) = Formalism.HN.rkK S + Formalism.HN.rkK A := by
  have h1 : Submodule.span E (A : Set (Fin n → E)) ⊓ Submodule.span E (S : Set (Fin n → E)) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨c, hc, hA⟩ := exists_smul_mem hx.1
    obtain ⟨d, hd, hS⟩ := exists_smul_mem hx.2
    have : (c * d) • x ∈ A ⊓ S := ⟨by rw [mul_comm, mul_smul]; exact A.smul_mem _ hA,
      by rw [mul_smul]; exact S.smul_mem _ hS⟩
    rw [h, Submodule.mem_bot, smul_eq_zero] at this
    exact this.resolve_left (mul_ne_zero hc hd)
  have h2 : Submodule.span E ((A ⊔ S : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      Submodule.span E (A : Set (Fin n → E)) ⊔ Submodule.span E (S : Set (Fin n → E)) := by
    refine le_antisymm (Submodule.span_le.2 fun x hx => ?_)
      (sup_le (Submodule.span_mono (le_sup_left : A ≤ A ⊔ S)) (Submodule.span_mono (le_sup_right : S ≤ A ⊔ S)))
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.add_mem_sup (Submodule.subset_span hy) (Submodule.subset_span hz)
  have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span E (A : Set (Fin n → E)))
    (Submodule.span E (S : Set (Fin n → E)))
  rw [h1, finrank_bot, ← h2] at this
  unfold Formalism.HN.rkK
  omega

/- English proof (translation)
Take `⟨T, hT, hr⟩` from `exists_matrix_range (k := Fin k) (Submodule.span E (A : Set (Fin n → E))) (hk.trans (Fintype.card_fin k).symm)`. Use `⟨A.comap (T.mulVecLin.restrictScalars (𝓞 E)), T, ⟨?_, ?_⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Submodule.fg_of_fg_map_injective (T.mulVecLin.restrictScalars (𝓞 E)) hT (hA.of_le (Submodule.map_comap_le _ _))`. Use `eq_top_iff.2 fun u _ => ?_` and prove the remaining obligations. Take `⟨c, hc, h⟩` from `exists_smul_mem (L := A) (hr ▸ ⟨u, rfl⟩ : T.mulVecLin u ∈ _)`.

Establish `h1 : c • u ∈ A.comap (T.mulVecLin.restrictScalars (𝓞 E))`. Rewrite using `[Submodule.mem_comap, map_smul]`. Conclude with `h`. Establish `hc' : (c : E) ≠ 0` using `by simpa using hc`. Rewrite using `[← Submodule.smul_mem_iff _ hc']`.

Conclude with `Submodule.subset_span h1`. Take `⟨u, rfl⟩ : z ∈ LinearMap.range T.mulVecLin` from `hr ▸ Submodule.subset_span hz`. Conclude with `⟨u, hz, rfl⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `hu`.
-/
theorem exists_model {k : ℕ} (A : Submodule (𝓞 E) (Fin n → E)) (hA : A.FG) (hk : Formalism.HN.rkK A = k) :
    ∃ (Λ : Submodule (𝓞 E) (Fin k → E)) (T : Matrix (Fin n) (Fin k) E), Submodule.IsLattice E Λ ∧
      ∀ z, z ∈ A ↔ ∃ u ∈ Λ, z = T *ᵥ u := by
  obtain ⟨T, hT, hr⟩ := exists_matrix_range (k := Fin k) (Submodule.span E (A : Set (Fin n → E)))
    (hk.trans (Fintype.card_fin k).symm)
  refine ⟨A.comap (T.mulVecLin.restrictScalars (𝓞 E)), T, ⟨?_, ?_⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · exact Submodule.fg_of_fg_map_injective (T.mulVecLin.restrictScalars (𝓞 E)) hT
      (hA.of_le (Submodule.map_comap_le _ _))
  · refine eq_top_iff.2 fun u _ => ?_
    obtain ⟨c, hc, h⟩ := exists_smul_mem (L := A) (hr ▸ ⟨u, rfl⟩ : T.mulVecLin u ∈ _)
    have h1 : c • u ∈ A.comap (T.mulVecLin.restrictScalars (𝓞 E)) := by
      rw [Submodule.mem_comap, map_smul]; exact h
    have hc' : (c : E) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span h1
  · obtain ⟨u, rfl⟩ : z ∈ LinearMap.range T.mulVecLin := hr ▸ Submodule.subset_span hz
    exact ⟨u, hz, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact hu

end Blocks

/- English proof (translation)
Introduce `E _ _ n a j S A h0 hmono hfg hrk hA`. Establish `hle : ∀ i, A i ≤ S i.succ` using `fun i => (hA i).2 ▸ le_sup_left`. Use `choose Λ T hΛ hT using fun i => exists_model (k := j i) (A i) (hfg.of_le ((hle i).trans (hmono (Fin.le_last _)))) (by`. Use `rkK_add (hA i).1` as an intermediate fact. Rewrite `this` using `[(hA i).2, hrk]`.

Use the proof step `omega)`. Use `⟨Λ, T, hΛ, fun k z => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Proceed by induction on `k using Fin.induction generalizing z with`. Consider the case `zero`. Introduce `hz`.

Rewrite `hz` using `[h0, Submodule.mem_bot]`. Conclude with `⟨0, fun i => zero_mem _, fun _ _ => rfl, by simp [hz]⟩`. Consider the case `succ k ih`. Introduce `hz`. Rewrite `hz` using `[← (hA k).2]`.

Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hz`. Take `⟨t, ht, rfl⟩` from `(hT k x).1 hx`. Take `⟨u, hu, hu0, rfl⟩` from `ih y hy`. Use `⟨Pi.single k t + u, fun i => add_mem ?_ (hu i), fun i hi => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = k`.

Substitute `h` using the available equality. Simplify using `using ht`. Simplify using `[h]`. Establish `h : i ≠ k` using `by rintro rfl; exact hi Fin.castSucc_lt_succ`. Simplify using `[h, hu0 i fun h' => hi (h'.trans Fin.castSucc_lt_succ)]`.

Simplify using `only [Pi.add_apply, mulVec_add, Finset.sum_add_distrib, add_left_inj]`. Apply the tactic sequence `rw [Finset.sum_eq_single k] <;> simp +contextual`. Introduce and unpack `⟨u, hu, hu0, rfl⟩`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i.castSucc < k`.

Conclude with `hmono (Fin.castSucc_lt_iff_succ_le.1 h) (hle i ((hT i _).2 ⟨_, hu i, rfl⟩))`. Simplify using `[hu0 i h]`.
-/
theorem exists_blocks : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)) (A : Fin a → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i : Fin a, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i) → (∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ) → ∃ (Λ : ∀ i, Submodule (𝓞 E) (Fin (j i) → E)) (T : ∀ i, Matrix (Fin n) (Fin (j i)) E), (∀ i, Submodule.IsLattice E (Λ i)) ∧ ∀ k z, z ∈ S k ↔ ∃ u : ∀ i, Fin (j i) → E, (∀ i, u i ∈ Λ i) ∧ (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧ z = ∑ i, T i *ᵥ u i := by
  intro E _ _ n a j S A h0 hmono hfg hrk hA
  have hle : ∀ i, A i ≤ S i.succ := fun i => (hA i).2 ▸ le_sup_left
  choose Λ T hΛ hT using fun i => exists_model (k := j i) (A i)
    (hfg.of_le ((hle i).trans (hmono (Fin.le_last _)))) (by
      have := rkK_add (hA i).1
      rw [(hA i).2, hrk] at this
      omega)
  refine ⟨Λ, T, hΛ, fun k z => ⟨?_, ?_⟩⟩
  · induction k using Fin.induction generalizing z with
    | zero =>
      intro hz
      rw [h0, Submodule.mem_bot] at hz
      exact ⟨0, fun i => zero_mem _, fun _ _ => rfl, by simp [hz]⟩
    | succ k ih =>
      intro hz
      rw [← (hA k).2] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨t, ht, rfl⟩ := (hT k x).1 hx
      obtain ⟨u, hu, hu0, rfl⟩ := ih y hy
      refine ⟨Pi.single k t + u, fun i => add_mem ?_ (hu i), fun i hi => ?_, ?_⟩
      · by_cases h : i = k
        · subst h; simpa using ht
        · simp [h]
      · have h : i ≠ k := by rintro rfl; exact hi Fin.castSucc_lt_succ
        simp [h, hu0 i fun h' => hi (h'.trans Fin.castSucc_lt_succ)]
      · simp only [Pi.add_apply, mulVec_add, Finset.sum_add_distrib, add_left_inj]
        rw [Finset.sum_eq_single k] <;> simp +contextual
  · rintro ⟨u, hu, hu0, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : i.castSucc < k
    · exact hmono (Fin.castSucc_lt_iff_succ_le.1 h) (hle i ((hT i _).2 ⟨_, hu i, rfl⟩))
    · simp [hu0 i h]

/- English proof (translation)
Introduce `E _ _ n m κ _ _ J T W W' hJ hd hn hT hW hW' iW iW' hnd`. Establish `pair : ∀ {l : Type} [Fintype l] (M : Matrix (Fin n) l E) (u : l → E) (z : Fin n → E), star (M *ᵥ u) ⬝ᵥ (J *ᵥ z) = star u ⬝ᵥ ((Mᴴ * J) *ᵥ z)` using `fun M u z => by`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]`. Establish `zero : ∀ (M : Matrix (Fin n) κ E) (z : Fin n → E), (∀ x ∈ LinearMap.range M.mulVecLin, star x ⬝ᵥ (J *ᵥ z) = 0) ↔ (Mᴴ * J) *ᵥ z = 0` using `fun M z => by`. Use `⟨fun h => funext fun s => ?_, ?_⟩` and prove the remaining obligations.

Use `h _ ⟨Pi.single s 1, rfl⟩` as an intermediate fact. Rewrite `this` using `[mulVecLin_apply, pair]`. Simplify `this` using `[Pi.star_single]`. Introduce and unpack `h _ ⟨u, rfl⟩`. Rewrite using `[mulVecLin_apply, pair, h, dotProduct_zero]`.

Set `g : W' →ₗ[E] κ → E` to `(Tᴴ * J).mulVecLin ∘ₗ W'.subtype`. Establish `hg : Function.Injective g` using `(injective_iff_map_eq_zero g).2 fun y hy => Subtype.ext (hnd y y.2 (hT ▸ (zero T y).2 hy))`. Set `f` to `LinearEquiv.ofInjectiveOfFinrankEq g hg (by simp [hW'])`. Take `⟨T', hT'⟩ : ∃ T' : Matrix (Fin n) κ E, T'.mulVecLin = W'.subtype ∘ₗ f.symm.toLinearMap` from `⟨LinearMap.toMatrix' _, by rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']⟩`. Establish `hr : LinearMap.range T'.mulVecLin = W'` using `by simp [hT', LinearMap.range_comp]`.

Establish `h3 : Tᴴ * J * T' = 1`. Use `Matrix.ext_of_mulVec_single fun s => ?_` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec, ← mulVecLin_apply T', hT', one_mulVec]`. Conclude with `f.apply_symm_apply _`. Establish `h3' : T'ᴴ * J * T = 1` using `by rw [gram_swap hJ, h3, conjTranspose_one]`.

Establish `h1 : Tᴴ * J * T = 0` using `gram_eq_zero _ _ _ fun x y => iW _ (hT ▸ ⟨x, rfl⟩) _ (hT ▸ ⟨y, rfl⟩)`. Establish `h2 : T'ᴴ * J * T' = 0` using `gram_eq_zero _ _ _ fun x y => iW' _ (hr ▸ ⟨x, rfl⟩) _ (hr ▸ ⟨y, rfl⟩)`. Set `π : (Fin n → E) →ₗ[E] (κ → E) × (κ → E)` to `(Tᴴ * J).mulVecLin.prod (T'ᴴ * J).mulVecLin`. Establish `hπ : ∀ a b, π (T' *ᵥ a + T *ᵥ b) = (a, b)` using `fun a b => by`. Simplify using `[π, mulVec_add, ← Matrix.mul_assoc, h1, h2, h3, h3']`.

Establish `hK : Module.finrank E (LinearMap.ker π) = Fintype.card (Fin m)`. Use `π.finrank_range_add_finrank_ker` as an intermediate fact. Rewrite `this` using `[LinearMap.range_eq_top.2 fun x => ⟨_, hπ x.1 x.2⟩]`. Simplify using `at this ⊢`. Use linear arithmetic over natural numbers and integers.

Take `⟨B, hB, hBr⟩` from `exists_matrix_range _ hK`. Establish `hmem : ∀ z, z ∈ LinearMap.ker π ↔ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ z) = 0` using `fun z => by`. Establish `: z ∈ LinearMap.ker π ↔ (Tᴴ * J) *ᵥ z = 0 ∧ (T'ᴴ * J) *ᵥ z = 0` using `by simp [π]`. Rewrite using `[this, ← zero, ← zero, hT, hr]`. Use `⟨fun h t ht => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx), fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩` and prove the remaining obligations.

Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 ht`. Rewrite using `[star_add, add_dotProduct, h.1 x hx, h.2 y hy, add_zero]`. Use `⟨T', B, hr, h3, fun h => ?_, fun z => hBr ▸ hmem z⟩` and prove the remaining obligations. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Establish `hall : ∀ x, star x ⬝ᵥ (J *ᵥ (B *ᵥ v)) = 0` using `fun x => by`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : x - (T' *ᵥ (π x).1 + T *ᵥ (π x).2) ∈ LinearMap.range B.mulVecLin := by`. Rewrite using `[hBr, LinearMap.mem_ker, map_sub, hπ, sub_self]`. Rewrite `hw` using `[eq_sub_iff_add_eq]`. Rewrite using `[← hw, star_add, add_dotProduct, mulVecLin_apply, form_mulVec, hv0, dotProduct_zero, zero_add]`. Conclude with `(hmem _).1 (hBr ▸ ⟨v, rfl⟩) _ (add_mem (Submodule.mem_sup_right (hr ▸ ⟨_, rfl⟩)) (Submodule.mem_sup_left (hT ▸ ⟨_, rfl⟩)))`.

Establish `hz : J *ᵥ (B *ᵥ v) = 0` using `funext fun s => by simpa [Pi.star_single] using hall (Pi.single s 1)`. Conclude with `hv (hB ((Matrix.eq_zero_of_mulVec_eq_zero hd hz).trans (map_zero B.mulVecLin).symm))`.
-/
theorem exists_witt : ∀ (E : Type) [Field E] [StarRing E] (n m : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] (J : Matrix (Fin n) (Fin n) E) (T : Matrix (Fin n) κ E) (W W' : Submodule E (Fin n → E)), Jᴴ = J → J.det ≠ 0 → n = m + 2 * Fintype.card κ → LinearMap.range T.mulVecLin = W → Module.finrank E W = Fintype.card κ → Module.finrank E W' = Fintype.card κ → (∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) → (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) → ∃ (T' : Matrix (Fin n) κ E) (B : Matrix (Fin n) (Fin m) E), LinearMap.range T'.mulVecLin = W' ∧ Tᴴ * J * T' = 1 ∧ (Bᴴ * J * B).det ≠ 0 ∧ ∀ z, z ∈ LinearMap.range B.mulVecLin ↔ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ z) = 0 := by
  intro E _ _ n m κ _ _ J T W W' hJ hd hn hT hW hW' iW iW' hnd
  have pair : ∀ {l : Type} [Fintype l] (M : Matrix (Fin n) l E) (u : l → E) (z : Fin n → E),
      star (M *ᵥ u) ⬝ᵥ (J *ᵥ z) = star u ⬝ᵥ ((Mᴴ * J) *ᵥ z) := fun M u z => by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  have zero : ∀ (M : Matrix (Fin n) κ E) (z : Fin n → E),
      (∀ x ∈ LinearMap.range M.mulVecLin, star x ⬝ᵥ (J *ᵥ z) = 0) ↔ (Mᴴ * J) *ᵥ z = 0 := fun M z => by
    refine ⟨fun h => funext fun s => ?_, ?_⟩
    · have := h _ ⟨Pi.single s 1, rfl⟩
      rw [mulVecLin_apply, pair] at this
      simpa [Pi.star_single] using this
    · rintro h _ ⟨u, rfl⟩
      rw [mulVecLin_apply, pair, h, dotProduct_zero]
  let g : W' →ₗ[E] κ → E := (Tᴴ * J).mulVecLin ∘ₗ W'.subtype
  have hg : Function.Injective g := (injective_iff_map_eq_zero g).2 fun y hy =>
    Subtype.ext (hnd y y.2 (hT ▸ (zero T y).2 hy))
  let f := LinearEquiv.ofInjectiveOfFinrankEq g hg (by simp [hW'])
  obtain ⟨T', hT'⟩ : ∃ T' : Matrix (Fin n) κ E, T'.mulVecLin = W'.subtype ∘ₗ f.symm.toLinearMap :=
    ⟨LinearMap.toMatrix' _, by rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']⟩
  have hr : LinearMap.range T'.mulVecLin = W' := by simp [hT', LinearMap.range_comp]
  have h3 : Tᴴ * J * T' = 1 := by
    refine Matrix.ext_of_mulVec_single fun s => ?_
    rw [← mulVec_mulVec, ← mulVecLin_apply T', hT', one_mulVec]
    exact f.apply_symm_apply _
  have h3' : T'ᴴ * J * T = 1 := by rw [gram_swap hJ, h3, conjTranspose_one]
  have h1 : Tᴴ * J * T = 0 := gram_eq_zero _ _ _ fun x y => iW _ (hT ▸ ⟨x, rfl⟩) _ (hT ▸ ⟨y, rfl⟩)
  have h2 : T'ᴴ * J * T' = 0 := gram_eq_zero _ _ _ fun x y => iW' _ (hr ▸ ⟨x, rfl⟩) _ (hr ▸ ⟨y, rfl⟩)
  let π : (Fin n → E) →ₗ[E] (κ → E) × (κ → E) := (Tᴴ * J).mulVecLin.prod (T'ᴴ * J).mulVecLin
  have hπ : ∀ a b, π (T' *ᵥ a + T *ᵥ b) = (a, b) := fun a b => by
    simp [π, mulVec_add, ← Matrix.mul_assoc, h1, h2, h3, h3']
  have hK : Module.finrank E (LinearMap.ker π) = Fintype.card (Fin m) := by
    have := π.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 fun x => ⟨_, hπ x.1 x.2⟩] at this
    simp at this ⊢
    omega
  obtain ⟨B, hB, hBr⟩ := exists_matrix_range _ hK
  have hmem : ∀ z, z ∈ LinearMap.ker π ↔ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ z) = 0 := fun z => by
    have : z ∈ LinearMap.ker π ↔ (Tᴴ * J) *ᵥ z = 0 ∧ (T'ᴴ * J) *ᵥ z = 0 := by simp [π]
    rw [this, ← zero, ← zero, hT, hr]
    refine ⟨fun h t ht => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
      fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ht
    rw [star_add, add_dotProduct, h.1 x hx, h.2 y hy, add_zero]
  refine ⟨T', B, hr, h3, fun h => ?_, fun z => hBr ▸ hmem z⟩
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hall : ∀ x, star x ⬝ᵥ (J *ᵥ (B *ᵥ v)) = 0 := fun x => by
    obtain ⟨w, hw⟩ : x - (T' *ᵥ (π x).1 + T *ᵥ (π x).2) ∈ LinearMap.range B.mulVecLin := by
      rw [hBr, LinearMap.mem_ker, map_sub, hπ, sub_self]
    rw [eq_sub_iff_add_eq] at hw
    rw [← hw, star_add, add_dotProduct, mulVecLin_apply, form_mulVec, hv0, dotProduct_zero, zero_add]
    exact (hmem _).1 (hBr ▸ ⟨v, rfl⟩) _ (add_mem (Submodule.mem_sup_right (hr ▸ ⟨_, rfl⟩))
      (Submodule.mem_sup_left (hT ▸ ⟨_, rfl⟩)))
  have hz : J *ᵥ (B *ᵥ v) = 0 := funext fun s => by simpa [Pi.star_single] using hall (Pi.single s 1)
  exact hv (hB ((Matrix.eq_zero_of_mulVec_eq_zero hd hz).trans (map_zero B.mulVecLin).symm))

/- English proof (translation)
Introduce `E E₀ _ _ _ _ _ _ e he n m J B G Λ hJ hG hd hΛ hdual hproj`. Set `f : (Fin m → E₀) →ₗ[ℤ] (Fin n → E)` to `{ toFun := fun y => B *ᵥ fun l => e (y l) map_add' := fun x y => by rw [← mulVec_add]; congr 1; ext l; simp map_smul' := fun c x => by rw [RingHom.id_apply, ← mulVec_smul]; congr 1; ext l; simp }`. Establish `hsm : ∀ (c : 𝓞 E₀) y, f (c • y) = RingOfIntegers.mapRingEquiv e c • f y` using `fun c y => by`. Express the relevant statement in the definitionally equal form `B *ᵥ _ = (e c) • (B *ᵥ _)`. Rewrite using `[← mulVec_smul]`.

Use `congr 1`. Use extensionality with `l`. Conclude with `map_mul e _ _`. Establish `hform : ∀ x y, star (f x) ⬝ᵥ (J *ᵥ f y) = e (star x ⬝ᵥ (G *ᵥ y))` using `fun x y => by`. Express the relevant statement in the definitionally equal form `star (B *ᵥ _) ⬝ᵥ (J *ᵥ (B *ᵥ _)) = _`.

Rewrite using `[form_mulVec, hG]`. Simplify using `[dotProduct, mulVec, he]`. Establish `hint : ∀ c, e c ∈ (algebraMap (𝓞 E) E).range ↔ c ∈ (algebraMap (𝓞 E₀) E₀).range` using `fun c => ⟨fun ⟨b, hb⟩ => ⟨RingOfIntegers.mapRingEquiv e.symm b, e.injective ((e.apply_symm_apply _).trans hb)⟩, fun ⟨b, hb⟩ => ⟨RingOfIntegers.mapRingEquiv e b, hb ▸ rfl⟩⟩`. Establish `hf : Function.Injective f` using `(injective_iff_map_eq_zero f).2 fun y hy => Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun s => by`. Use `hform (Pi.single s 1) y` as an intermediate fact.

Rewrite `this` using `[hy]`. Simplify `this.symm)` using `[Pi.star_single]`. Set `L : Submodule (𝓞 E₀) (Fin m → E₀)` to `{ carrier := {y | f y ∈ Λ} add_mem' := fun hx hy => by simpa using add_mem hx hy zero_mem' := by simp smul_mem' := fun c y hy => by`. Express the relevant statement in the definitionally equal form `f (c • y) ∈ Λ`. Rewrite using `[hsm]`.

Conclude with `Λ.smul_mem _ hy }`. Use `⟨L, ⟨?_, ?_⟩, fun y => Iff.rfl, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (Λ.restrictScalars ℤ).FG` using `hΛ.fg.restrictScalars`. Use `Submodule.FG.of_restrictScalars ℤ (Submodule.fg_of_fg_map_injective f hf (h1.of_le ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `hy`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Take `⟨c, hc, h⟩` from `exists_smul_mem (L := Λ) (x := f y) (hΛ.span_eq_top ▸ Submodule.mem_top)`. Take `⟨c, rfl⟩` from `(RingOfIntegers.mapRingEquiv e).surjective c`. Establish `hc' : (c : E₀) ≠ 0` using `by simpa using hc`.

Rewrite using `[← Submodule.smul_mem_iff _ hc']`. Conclude with `Submodule.subset_span (show f (c • y) ∈ Λ from hsm c y ▸ h)`. Rewrite using `[← hint, ← hform]`. Conclude with `(hdual _).1 hx _ hy`. Use `(hdual (f x)).2 fun z hz => ?_` and prove the remaining obligations.

Take `⟨y, hy, h0⟩` from `hproj z hz`. Establish `hy' : f (fun l => e.symm (y l)) = B *ᵥ y`. Express the relevant statement in the definitionally equal form `B *ᵥ _ = _`. Simplify using the standard rewrite rules. Establish `h1 : star (z - B *ᵥ y) ⬝ᵥ (J *ᵥ f x) = 0`.

Express the relevant statement in the definitionally equal form `star _ ⬝ᵥ (J *ᵥ (B *ᵥ _)) = 0`. Establish `: star (z - B *ᵥ y) ᵥ* (J * B) = 0`. Use `congrArg star h0` as an intermediate fact. Rewrite `this` using `[star_mulVec, conjTranspose_mul, hJ, conjTranspose_conjTranspose, star_zero]`. Then use the resulting hypothesis. Rewrite using `[mulVec_mulVec, dotProduct_mulVec, this, zero_dotProduct]`.

Rewrite `h1` using `[star_sub, sub_dotProduct, sub_eq_zero]`. Rewrite using `[h1, ← hy', hform, hint]`. Conclude with `hx _ (show f _ ∈ Λ from hy' ▸ hy)`.
-/
theorem exists_factor_lattice : ∀ (E E₀ : Type) [Field E] [NumberField E] [StarRing E] [Field E₀] [NumberField E₀] [StarRing E₀] (e : E₀ ≃+* E), (∀ y, e (star y) = star (e y)) → ∀ (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (B : Matrix (Fin n) (Fin m) E) (G : Matrix (Fin m) (Fin m) E₀) (Λ : Submodule (𝓞 E) (Fin n → E)), Jᴴ = J → Bᴴ * J * B = G.map e → G.det ≠ 0 → Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → (∀ z ∈ Λ, ∃ y : Fin m → E, B *ᵥ y ∈ Λ ∧ (Bᴴ * J) *ᵥ (z - B *ᵥ y) = 0) → ∃ L : Submodule (𝓞 E₀) (Fin m → E₀), Submodule.IsLattice E₀ L ∧ (∀ y, y ∈ L ↔ (B *ᵥ fun l => e (y l)) ∈ Λ) ∧ ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (G *ᵥ x) ∈ (algebraMap (𝓞 E₀) E₀).range := by
  intro E E₀ _ _ _ _ _ _ e he n m J B G Λ hJ hG hd hΛ hdual hproj
  let f : (Fin m → E₀) →ₗ[ℤ] (Fin n → E) :=
    { toFun := fun y => B *ᵥ fun l => e (y l)
      map_add' := fun x y => by rw [← mulVec_add]; congr 1; ext l; simp
      map_smul' := fun c x => by rw [RingHom.id_apply, ← mulVec_smul]; congr 1; ext l; simp }
  have hsm : ∀ (c : 𝓞 E₀) y, f (c • y) = RingOfIntegers.mapRingEquiv e c • f y := fun c y => by
    change B *ᵥ _ = (e c) • (B *ᵥ _)
    rw [← mulVec_smul]; congr 1; ext l
    exact map_mul e _ _
  have hform : ∀ x y, star (f x) ⬝ᵥ (J *ᵥ f y) = e (star x ⬝ᵥ (G *ᵥ y)) := fun x y => by
    change star (B *ᵥ _) ⬝ᵥ (J *ᵥ (B *ᵥ _)) = _
    rw [form_mulVec, hG]
    simp [dotProduct, mulVec, he]
  have hint : ∀ c, e c ∈ (algebraMap (𝓞 E) E).range ↔ c ∈ (algebraMap (𝓞 E₀) E₀).range := fun c =>
    ⟨fun ⟨b, hb⟩ => ⟨RingOfIntegers.mapRingEquiv e.symm b, e.injective ((e.apply_symm_apply _).trans hb)⟩,
      fun ⟨b, hb⟩ => ⟨RingOfIntegers.mapRingEquiv e b, hb ▸ rfl⟩⟩
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).2 fun y hy =>
    Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun s => by
      have := hform (Pi.single s 1) y
      rw [hy] at this
      simpa [Pi.star_single] using this.symm)
  let L : Submodule (𝓞 E₀) (Fin m → E₀) :=
    { carrier := {y | f y ∈ Λ}
      add_mem' := fun hx hy => by simpa using add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        change f (c • y) ∈ Λ
        rw [hsm]; exact Λ.smul_mem _ hy }
  refine ⟨L, ⟨?_, ?_⟩, fun y => Iff.rfl, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩
  · have h1 : (Λ.restrictScalars ℤ).FG := hΛ.fg.restrictScalars
    refine Submodule.FG.of_restrictScalars ℤ (Submodule.fg_of_fg_map_injective f hf (h1.of_le ?_))
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨c, hc, h⟩ := exists_smul_mem (L := Λ) (x := f y) (hΛ.span_eq_top ▸ Submodule.mem_top)
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv e).surjective c
    have hc' : (c : E₀) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span (show f (c • y) ∈ Λ from hsm c y ▸ h)
  · rw [← hint, ← hform]
    exact (hdual _).1 hx _ hy
  · refine (hdual (f x)).2 fun z hz => ?_
    obtain ⟨y, hy, h0⟩ := hproj z hz
    have hy' : f (fun l => e.symm (y l)) = B *ᵥ y := by
      change B *ᵥ _ = _
      simp
    have h1 : star (z - B *ᵥ y) ⬝ᵥ (J *ᵥ f x) = 0 := by
      change star _ ⬝ᵥ (J *ᵥ (B *ᵥ _)) = 0
      have : star (z - B *ᵥ y) ᵥ* (J * B) = 0 := by
        have := congrArg star h0
        rwa [star_mulVec, conjTranspose_mul, hJ, conjTranspose_conjTranspose, star_zero] at this
      rw [mulVec_mulVec, dotProduct_mulVec, this, zero_dotProduct]
    rw [star_sub, sub_dotProduct, sub_eq_zero] at h1
    rw [h1, ← hy', hform, hint]
    exact hx _ (show f _ ∈ Λ from hy' ▸ hy)

end GlobalTheory.AdaptedExists
