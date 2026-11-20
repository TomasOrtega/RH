import ReciprocityTheory.DualLattices.EigenLengthFrobeniusStatement
import ReciprocityTheory.DualLattices.UpSmith
import ReciprocityTheory.DualLattices.ProdDvdOfIso

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

namespace Tot

section len

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Take `⟨m, c, ⟨f⟩, hx⟩` from `h`. Conclude with `⟨m, c, ⟨e.trans f⟩, hx⟩`.
-/
theorem hasLen_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨f⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans f⟩, hx⟩

/- English proof (translation)
Use `choose n c he hX using h`. Set `e : ∀ i, M i ≃ₗ[R] ((j : Fin (n i)) → R ⧸ Ideal.span {c i j})` to `fun i => (he i).some`. Set `σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i))` to `(Fintype.equivFin _).symm`. Use `⟨Fintype.card (Σ i, Fin (n i)), fun k => c (σ k).1 (σ k).2, ⟨?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(LinearEquiv.piCongrRight e).trans ((LinearEquiv.piCurry R (fun i j => R ⧸ Ideal.span {c i j})).symm.trans (LinearEquiv.piCongrLeft R (fun p : Σ i, Fin (n i) => R ⧸ Ideal.span {c p.1 p.2}) σ).symm)`.

Rewrite using `[Fintype.prod_equiv σ (fun k => v (algebraMap R C (c (σ k).1 (σ k).2))) (fun p => v (algebraMap R C (c p.1 p.2))) (fun k => rfl), Fintype.prod_sigma]`. Conclude with `Finset.prod_congr rfl fun i _ => hX i`.
-/
theorem hasLen_pi {m : ℕ} (M : Fin m → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (X : Fin m → NNReal) (h : ∀ i, HasLen v R (M i) (X i)) :
    HasLen v R ((i : Fin m) → M i) (∏ i, X i) := by
  classical
  choose n c he hX using h
  let e : ∀ i, M i ≃ₗ[R] ((j : Fin (n i)) → R ⧸ Ideal.span {c i j}) := fun i => (he i).some
  let σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (n i)), fun k => c (σ k).1 (σ k).2, ⟨?_⟩, ?_⟩
  · exact (LinearEquiv.piCongrRight e).trans
      ((LinearEquiv.piCurry R (fun i j => R ⧸ Ideal.span {c i j})).symm.trans
        (LinearEquiv.piCongrLeft R (fun p : Σ i, Fin (n i) => R ⧸ Ideal.span {c p.1 p.2}) σ).symm)
  · rw [Fintype.prod_equiv σ (fun k => v (algebraMap R C (c (σ k).1 (σ k).2)))
      (fun p => v (algebraMap R C (c p.1 p.2))) (fun k => rfl), Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => hX i

end len

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [fromBlocks_zero]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, fromBlocks_add, add_zero]`.
-/
theorem sum_fromBlocks_diag {g : ℕ} {ι : Type} (s : Finset ι)
    (A D : ι → Matrix (Fin g) (Fin g) R) :
    ∑ i ∈ s, fromBlocks (A i) 0 0 (D i) = fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fromBlocks_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, fromBlocks_add,
      add_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]`.
-/
theorem sum_mulVec' {n : Type} [Fintype n] {ι : Type} (s : Finset ι) (A : ι → Matrix n n R)
    (w : n → R) : (∑ i ∈ s, A i) *ᵥ w = ∑ i ∈ s, A i *ᵥ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

end Tot

open Tot in
/- English proof (translation)
Introduce `C _ v R _ _ hv g m Ht Bt εT εL π hπ hTo hTs hLo hLs hHt hBt X hX`. Use `set Φ := fromRows Ht Bt with hΦ`. Use `set Pm : Fin m → Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R := fun i => fromBlocks ((εL (π i))ᵀ) 0 0 (εL i) with hPm`. Establish `hPmv : ∀ i w, Pm i *ᵥ w = Sum.elim ((εL (π i))ᵀ *ᵥ (w ∘ Sum.inl)) (εL i *ᵥ (w ∘ Sum.inr))`. Introduce `i w`.

Simplify using `only [hPm, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]`. Establish `hmem : ∀ i w, Pm i *ᵥ w ∈ qE εL i (π i)`. Introduce `i w`. Use `Submodule.mem_inf.2 ⟨⟨w ∘ Sum.inl, ?_⟩, ⟨w ∘ Sum.inr, ?_⟩⟩` and prove the remaining obligations. Use `show (εL (π i))ᵀ *ᵥ (w ∘ Sum.inl) = (Pm i *ᵥ w) ∘ Sum.inl`.

Rewrite using `[hPmv]`. Both sides reduce to the same expression. Use `show εL i *ᵥ (w ∘ Sum.inr) = (Pm i *ᵥ w) ∘ Sum.inr`. Rewrite using `[hPmv]`. Both sides reduce to the same expression.

Establish `hsel : ∀ i k w, w ∈ qE εL i (π i) → Pm k *ᵥ w = if k = i then w else 0`. Introduce `i k w hw`. Take `⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩` from `Submodule.mem_inf.1 hw`. Establish `e1 : w ∘ Sum.inl = (εL (π i))ᵀ *ᵥ y1` using `hy1.symm`. Establish `e2 : w ∘ Sum.inr = εL i *ᵥ y2` using `hy2.symm`.

Rewrite using `[hPmv, e1, e2, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hLo, hLo]`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Simplify using `only [if_true]`. Rewrite using `[← e1, ← e2, Sum.elim_comp_inl_inr]`.

Establish `hne : π i ≠ π k` using `fun h => hki (π.injective h).symm`. Simplify using `only [hki, hne, if_false, transpose_zero, zero_mulVec]`. Apply the tactic sequence `ext s; cases s <;> rfl`. Establish `hT : ∑ i, (εL (π i))ᵀ = 1`. Rewrite using `[← transpose_sum, Equiv.sum_comp π εL, hLs, transpose_one]`.

Establish `hPsum : ∑ i, Pm i = 1`. Simplify using `only [hPm]`. Rewrite using `[sum_fromBlocks_diag, hT, hLs, fromBlocks_one]`. Establish `hsum : ∀ w, ∑ i, Pm i *ᵥ w = w`. Introduce `w`.

Rewrite using `[← sum_mulVec', hPsum, one_mulVec]`. Establish `hPΦ : ∀ i, Pm i * Φ = Φ * εT i`. Introduce `i`. Rewrite using `[hΦ, hPm, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero, zero_add, hHt, hBt]`. Use `set Ψ : (Fin g ⊕ Fin g → R) →ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i) := LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (qE εL i (π i)) (mulVecLin (Pm i)) (hmem i) with hΨdef`.

Establish `hΨ : ∀ w i, Ψ w i = Submodule.Quotient.mk ⟨Pm i *ᵥ w, hmem i w⟩` using `fun _ _ => rfl`. Establish `hsurj : Function.Surjective Ψ`. Introduce `q`. Use `choose w hw using fun i => Submodule.Quotient.mk_surjective _ (q i)`. Use `⟨∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R), funext fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[hΨ, ← hw k]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Pm k *ᵥ ∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R) = (w k : Fin g ⊕ Fin g → R)`. Rewrite using `[mulVec_sum]`.

Simplify using `only [fun i => hsel i k _ (w i).2]`. Simplify using the standard rewrite rules. Establish `hker : LinearMap.ker Ψ = LinearMap.range (mulVecLin Φ)`. Use extensionality with `w`. Rewrite using `[LinearMap.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hi : ∀ i, ∃ t, Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ w`. Introduce `i`. Use `congrFun h i` as an intermediate fact.

Rewrite `this` using `[hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨y, ⟨t, rfl⟩, hy⟩` from `this`. Conclude with `⟨t, hy⟩`. Use `choose t ht using hi`. Use `⟨∑ i, εT i *ᵥ t i, ?_⟩` and prove the remaining obligations.

Use `show Φ *ᵥ ∑ i, εT i *ᵥ t i = w`. Rewrite using `[mulVec_sum]`. Simplify using `only [ht]`. Conclude with `hsum w`. Introduce and unpack `⟨t, rfl⟩`.

Use function extensionality and compare the values at `i`. Rewrite using `[hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]`. Use `⟨εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ (Φ *ᵥ t)`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, hPΦ]`.

Establish `iso : ((Fin g ⊕ Fin g → R) ⧸ LinearMap.range (mulVecLin Φ)) ≃ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i)` using `(Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hsurj)`. Use `set e : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he`. Use `set Φ' := reindex e e Φ with hΦ'`. Establish `hdet : Φ'.det = Φ.det` using `det_reindex_self e Φ`. Use `set F : (Fin (g + g) → R) ≃ₗ[R] (Fin g ⊕ Fin g → R) := LinearEquiv.funCongrLeft R R e with hF`.

Establish `hFapp : ∀ y, F y = y ∘ e` using `fun y => rfl`. Establish `hcomm : ∀ y, F (Φ' *ᵥ y) = Φ *ᵥ F y`. Introduce `y`. Rewrite using `[hFapp, hFapp, hΦ', reindex_apply, submatrix_mulVec_equiv]`. Use extensionality with `s`.

Simplify using the standard rewrite rules. Establish `hmap : (LinearMap.range (mulVecLin Φ')).map F.toLinearMap = LinearMap.range (mulVecLin Φ)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, rfl⟩, rfl⟩`.

Conclude with `⟨F y, (hcomm y).symm⟩`. Introduce and unpack `⟨t, rfl⟩`. Use `⟨Φ' *ᵥ F.symm t, ⟨F.symm t, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show F (Φ' *ᵥ F.symm t) = Φ *ᵥ t`. Rewrite using `[hcomm, LinearEquiv.apply_symm_apply]`.

Establish `hcok` using `Submodule.Quotient.equiv _ _ F hmap`. Establish `hL1` using `Smith.hasLen_coker_det (C := C) (v := v) hv Φ'`. Establish `hL2 : HasLen v R ((Fin (g + g) → R) ⧸ LinearMap.range (mulVecLin Φ')) (∏ i, X i)` using `hasLen_equiv (hcok.trans iso) (hasLen_pi _ X hX)`. Rewrite using `[hasLen_unique hv hL2 hL1, hdet]`.
-/
theorem eigenLengthProductStatement_holds : EigenLengthProductStatement := by
  intro C _ v R _ _ hv g m Ht Bt εT εL π hπ hTo hTs hLo hLs hHt hBt X hX
  classical
  set Φ := fromRows Ht Bt with hΦ
  set Pm : Fin m → Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fun i => fromBlocks ((εL (π i))ᵀ) 0 0 (εL i) with hPm
  have hPmv : ∀ i w, Pm i *ᵥ w =
      Sum.elim ((εL (π i))ᵀ *ᵥ (w ∘ Sum.inl)) (εL i *ᵥ (w ∘ Sum.inr)) := by
    intro i w
    simp only [hPm, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  have hmem : ∀ i w, Pm i *ᵥ w ∈ qE εL i (π i) := by
    intro i w
    refine Submodule.mem_inf.2 ⟨⟨w ∘ Sum.inl, ?_⟩, ⟨w ∘ Sum.inr, ?_⟩⟩
    · show (εL (π i))ᵀ *ᵥ (w ∘ Sum.inl) = (Pm i *ᵥ w) ∘ Sum.inl
      rw [hPmv]; rfl
    · show εL i *ᵥ (w ∘ Sum.inr) = (Pm i *ᵥ w) ∘ Sum.inr
      rw [hPmv]; rfl
  have hsel : ∀ i k w, w ∈ qE εL i (π i) → Pm k *ᵥ w = if k = i then w else 0 := by
    intro i k w hw
    obtain ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := Submodule.mem_inf.1 hw
    have e1 : w ∘ Sum.inl = (εL (π i))ᵀ *ᵥ y1 := hy1.symm
    have e2 : w ∘ Sum.inr = εL i *ᵥ y2 := hy2.symm
    rw [hPmv, e1, e2, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hLo, hLo]
    by_cases hki : k = i
    · subst hki
      simp only [if_true]
      rw [← e1, ← e2, Sum.elim_comp_inl_inr]
    · have hne : π i ≠ π k := fun h => hki (π.injective h).symm
      simp only [hki, hne, if_false, transpose_zero, zero_mulVec]
      ext s; cases s <;> rfl
  have hT : ∑ i, (εL (π i))ᵀ = 1 := by
    rw [← transpose_sum, Equiv.sum_comp π εL, hLs, transpose_one]
  have hPsum : ∑ i, Pm i = 1 := by
    simp only [hPm]
    rw [sum_fromBlocks_diag, hT, hLs, fromBlocks_one]
  have hsum : ∀ w, ∑ i, Pm i *ᵥ w = w := by
    intro w
    rw [← sum_mulVec', hPsum, one_mulVec]
  have hPΦ : ∀ i, Pm i * Φ = Φ * εT i := by
    intro i
    rw [hΦ, hPm, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero,
      zero_add,
      hHt, hBt]
  set Ψ : (Fin g ⊕ Fin g → R) →ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
      LinearMap.codRestrict (qE εL i (π i)) (mulVecLin (Pm i)) (hmem i) with hΨdef
  have hΨ : ∀ w i, Ψ w i = Submodule.Quotient.mk ⟨Pm i *ᵥ w, hmem i w⟩ := fun _ _ => rfl
  have hsurj : Function.Surjective Ψ := by
    intro q
    choose w hw using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R), funext fun k => ?_⟩
    rw [hΨ, ← hw k]
    congr 1
    apply Subtype.ext
    show Pm k *ᵥ ∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R) = (w k : Fin g ⊕ Fin g → R)
    rw [mulVec_sum]
    simp only [fun i => hsel i k _ (w i).2]
    simp
  have hker : LinearMap.ker Ψ = LinearMap.range (mulVecLin Φ) := by
    ext w
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have hi : ∀ i, ∃ t, Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ w := by
        intro i
        have := congrFun h i
        rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨y, ⟨t, rfl⟩, hy⟩ := this
        exact ⟨t, hy⟩
      choose t ht using hi
      refine ⟨∑ i, εT i *ᵥ t i, ?_⟩
      show Φ *ᵥ ∑ i, εT i *ᵥ t i = w
      rw [mulVec_sum]
      simp only [ht]
      exact hsum w
    · rintro ⟨t, rfl⟩
      funext i
      rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
      show Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ (Φ *ᵥ t)
      rw [mulVec_mulVec, mulVec_mulVec, hPΦ]
  have iso : ((Fin g ⊕ Fin g → R) ⧸ LinearMap.range (mulVecLin Φ)) ≃ₗ[R]
      ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hsurj)
  set e : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he
  set Φ' := reindex e e Φ with hΦ'
  have hdet : Φ'.det = Φ.det := det_reindex_self e Φ
  set F : (Fin (g + g) → R) ≃ₗ[R] (Fin g ⊕ Fin g → R) := LinearEquiv.funCongrLeft R R e with hF
  have hFapp : ∀ y, F y = y ∘ e := fun y => rfl
  have hcomm : ∀ y, F (Φ' *ᵥ y) = Φ *ᵥ F y := by
    intro y
    rw [hFapp, hFapp, hΦ', reindex_apply, submatrix_mulVec_equiv]
    ext s
    simp
  have hmap : (LinearMap.range (mulVecLin Φ')).map F.toLinearMap = LinearMap.range (mulVecLin Φ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨F y, (hcomm y).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨Φ' *ᵥ F.symm t, ⟨F.symm t, rfl⟩, ?_⟩
      show F (Φ' *ᵥ F.symm t) = Φ *ᵥ t
      rw [hcomm, LinearEquiv.apply_symm_apply]
  have hcok := Submodule.Quotient.equiv _ _ F hmap
  have hL1 := Smith.hasLen_coker_det (C := C) (v := v) hv Φ'
  have hL2 : HasLen v R ((Fin (g + g) → R) ⧸ LinearMap.range (mulVecLin Φ')) (∏ i, X i) :=
    hasLen_equiv (hcok.trans iso) (hasLen_pi _ X hX)
  rw [hasLen_unique hv hL2 hL1, hdet]

end ReciprocityTheory.PGsh.Up
