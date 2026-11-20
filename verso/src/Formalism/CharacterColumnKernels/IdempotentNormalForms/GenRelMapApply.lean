import Formalism.CharacterColumnKernels.StatementG

open Finset

noncomputable section

namespace Formalism.NG

section GenKey

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma gen_relMap_apply {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b O) (v : b → KO O) (i : a) :
    relMap O (KO O) X v i = ∑ j, X i j • v j := rfl

/- English proof (translation)
Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, gen_relMap_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`.
-/
lemma gen_relMap_mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X : Matrix a b O) (Y : Matrix b c O) :
    relMap O (KO O) (X * Y) = relMap O (KO O) X ∘ₗ relMap O (KO O) Y := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, gen_relMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[gen_relMap_apply, Matrix.one_apply, ite_smul]`.
-/
lemma gen_relMap_one {a : Type*} [Fintype a] [DecidableEq a] (v : a → KO O) :
    relMap O (KO O) (1 : Matrix a a O) v = v := by
  funext i
  simp [gen_relMap_apply, Matrix.one_apply, ite_smul]

/- English proof (translation)
Take `⟨n, snf⟩` from `(LinearMap.range (Matrix.mulVecLin A)).smithNormalForm (Pi.basisFun O M)`. Use `set U : Matrix M M O := (Pi.basisFun O M).toMatrix snf.bM with hUdef`. Use `set W : Matrix M M O := snf.bM.toMatrix (Pi.basisFun O M) with hWdef`. Establish `hWU : W * U = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`. Establish `hUW : U * W = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`.

Establish `hn : n ≤ Fintype.card G`. Establish `h1` using `Module.finrank_eq_card_basis snf.bN`. Establish `h2` using `LinearMap.finrank_range_le (Matrix.mulVecLin A)`. Rewrite `h2` using `[h1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Conclude with `h2`.

Set `e : Fin n ↪ G` to `(Fin.castLEEmb hn).trans (Fintype.equivFin G).symm.toEmbedding`. Use `⟨n, U, snf.f, e, ?_, ?_⟩` and prove the remaining obligations. Use `⟨Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0, ?_⟩` and prove the remaining obligations. Establish `hZ : (Matrix.of fun p q => ((Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0) * U) (e p) (snf.f q)) = 1`. Use extensionality with `p q`.

Simplify using `only [Matrix.of_apply, Matrix.mul_apply, e.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← Matrix.mul_apply, hWU]`. Simplify using `[Matrix.one_apply, snf.f.injective.eq_iff]`. Rewrite using `[hZ, Matrix.det_one]`. Conclude with `isUnit_one`.

Introduce `C' hC set Y : Matrix M G O := W * A with hYdef`. Establish `hAY : A = U * Y` using `by rw [hYdef, ← Matrix.mul_assoc, hUW, Matrix.one_mul]`. Establish `hY : ∀ k, k ∉ Set.range snf.f → ∀ j, Y k j = 0`. Introduce `k hk j`. Establish `hmem : (fun l => A l j) ∈ LinearMap.range (Matrix.mulVecLin A)` using `⟨Pi.single j 1, by`.

Use function extensionality and compare the values at `l`. Use the proof step `simp⟩`. Establish `h0` using `snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hk`. Rewrite `h0` using `[← Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O M)]`. Simplify `h0` using `[hYdef, Matrix.mulVec, dotProduct, Matrix.mul_apply]`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Use `set y := relMap O (KO O) Y v with hydef`. Establish `hy0 : ∀ k, k ∉ Set.range snf.f → y k = 0`.

Introduce `k hk`. Simplify using `[hydef, gen_relMap_apply, hY k hk]`. Establish `hv' : relMap O (KO O) (C' * U) y = 0`. Rewrite using `[hydef, ← LinearMap.comp_apply, ← gen_relMap_mul, Matrix.mul_assoc, ← hAY]`. Conclude with `hv`.

Use `set Z : Matrix (Fin n) (Fin n) O := Matrix.of fun p q => (C' * U) (e p) (snf.f q) with hZdef`. Establish `hz : relMap O (KO O) Z (y ∘ snf.f) = 0`. Use function extensionality and compare the values at `p`. Use `congrFun hv' (e p)` as an intermediate fact. Rewrite `this` using `[gen_relMap_apply, Pi.zero_apply]`.

Rewrite using `[gen_relMap_apply, Pi.zero_apply]`. Conclude with `(Fintype.sum_of_injective snf.f snf.f.injective _ _ (fun k hk => by simp [hy0 k hk]) (fun q => rfl)).trans this`. Establish `hyf : y ∘ snf.f = 0`. Rewrite using `[← gen_relMap_one (y ∘ snf.f), ← Matrix.nonsing_inv_mul Z hC, gen_relMap_mul, LinearMap.comp_apply, hz, map_zero]`. Establish `hy : y = 0`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k ∈ Set.range snf.f`. Take `⟨q, rfl⟩` from `hk`. Conclude with `congrFun hyf q`. Conclude with `hy0 k hk`.

Rewrite using `[hAY, gen_relMap_mul, LinearMap.comp_apply, ← hydef, hy, map_zero]`. Introduce `v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[gen_relMap_mul, LinearMap.comp_apply, hv, map_zero]`.
-/
lemma gen_key {M G : Type} [Fintype M] [DecidableEq M] [Fintype G] [DecidableEq G]
    (A : Matrix M G O) : ∃ (n : ℕ) (U : Matrix M M O) (f : Fin n ↪ M) (e : Fin n ↪ G),
      (∃ C0 : Matrix G M O, IsUnit (Matrix.of fun p q => (C0 * U) (e p) (f q)).det) ∧
      ∀ C' : Matrix G M O, IsUnit (Matrix.of fun p q => (C' * U) (e p) (f q)).det →
        LinearMap.ker (relMap O (KO O) (C' * A)) = LinearMap.ker (relMap O (KO O) A) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin A)).smithNormalForm (Pi.basisFun O M)
  set U : Matrix M M O := (Pi.basisFun O M).toMatrix snf.bM with hUdef
  set W : Matrix M M O := snf.bM.toMatrix (Pi.basisFun O M) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hn : n ≤ Fintype.card G := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    have h2 := LinearMap.finrank_range_le (Matrix.mulVecLin A)
    rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    exact h2
  let e : Fin n ↪ G := (Fin.castLEEmb hn).trans (Fintype.equivFin G).symm.toEmbedding
  refine ⟨n, U, snf.f, e, ?_, ?_⟩
  · refine ⟨Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0, ?_⟩
    have hZ : (Matrix.of fun p q =>
        ((Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0) * U) (e p) (snf.f q)) = 1 := by
      ext p q
      simp only [Matrix.of_apply, Matrix.mul_apply, e.injective.eq_iff, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← Matrix.mul_apply, hWU]
      simp [Matrix.one_apply, snf.f.injective.eq_iff]
    rw [hZ, Matrix.det_one]
    exact isUnit_one
  · intro C' hC
    set Y : Matrix M G O := W * A with hYdef
    have hAY : A = U * Y := by rw [hYdef, ← Matrix.mul_assoc, hUW, Matrix.one_mul]
    have hY : ∀ k, k ∉ Set.range snf.f → ∀ j, Y k j = 0 := by
      intro k hk j
      have hmem : (fun l => A l j) ∈ LinearMap.range (Matrix.mulVecLin A) :=
        ⟨Pi.single j 1, by
          funext l
          simp⟩
      have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hk
      rw [← Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O M)] at h0
      simpa [hYdef, Matrix.mulVec, dotProduct, Matrix.mul_apply] using h0
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      set y := relMap O (KO O) Y v with hydef
      have hy0 : ∀ k, k ∉ Set.range snf.f → y k = 0 := by
        intro k hk
        simp [hydef, gen_relMap_apply, hY k hk]
      have hv' : relMap O (KO O) (C' * U) y = 0 := by
        rw [hydef, ← LinearMap.comp_apply, ← gen_relMap_mul, Matrix.mul_assoc, ← hAY]
        exact hv
      set Z : Matrix (Fin n) (Fin n) O := Matrix.of fun p q => (C' * U) (e p) (snf.f q) with hZdef
      have hz : relMap O (KO O) Z (y ∘ snf.f) = 0 := by
        funext p
        have := congrFun hv' (e p)
        rw [gen_relMap_apply, Pi.zero_apply] at this
        rw [gen_relMap_apply, Pi.zero_apply]
        exact (Fintype.sum_of_injective snf.f snf.f.injective _ _
          (fun k hk => by simp [hy0 k hk]) (fun q => rfl)).trans this
      have hyf : y ∘ snf.f = 0 := by
        rw [← gen_relMap_one (y ∘ snf.f), ← Matrix.nonsing_inv_mul Z hC, gen_relMap_mul,
          LinearMap.comp_apply, hz, map_zero]
      have hy : y = 0 := by
        funext k
        by_cases hk : k ∈ Set.range snf.f
        · obtain ⟨q, rfl⟩ := hk
          exact congrFun hyf q
        · exact hy0 k hk
      rw [hAY, gen_relMap_mul, LinearMap.comp_apply, ← hydef, hy, map_zero]
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [gen_relMap_mul, LinearMap.comp_apply, hv, map_zero]

end GenKey

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [bigMat, bigRect, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply, Fintype.sum_prod_type]`.
-/
lemma gen_bigMat_mul {R O : Type*} [Ring R] [CommRing O] [Algebra O R] {m g d : Type*}
    [Fintype m] [Fintype d] [DecidableEq d] (ρ : R →ₐ[O] Matrix d d O) (C : Matrix g m R) (P : Matrix m g R) :
    bigMat (⇑ρ) (C * P) = bigRect (⇑ρ) C * bigRect (⇑ρ) P := by
  ext p q
  simp only [bigMat, bigRect, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

/- English proof (translation)
Introduce `R O _ _ _ _ _ _ m g s _ _ _ _ d _ _ ρ hρ P`. Establish `hk` using `fun w => gen_key (O := O) (bigRect (ρ w) P)`. Use `choose n U f e hC0 hgood using hk`. Use `choose C0 hC0 using hC0`. Set `res` to `IsLocalRing.residue O`.

Set `r : ∀ w, d w → d w → R` to `fun w a b => Function.surjInv (hρ w) (Matrix.single a b 1)`. Set `c : (Σ w : s, g × m × d w × d w) → Matrix g m R` to `fun j => Matrix.single j.2.1 j.2.2.1 (r j.1 j.2.2.2.1 j.2.2.2.2)`. Set `L : ∀ w, Matrix (g × d w) (m × d w) (MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O))` to `fun w p q => ∑ j, MvPolynomial.X j * MvPolynomial.C (res (ρ w (c j p.1 q.1) p.2 q.2))`. Set `Q : s → MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O)` to `fun w => (Matrix.of fun p q => ∑ l, L w (e w p) l * MvPolynomial.C (res (U w l (f w q)))).det`. Establish `hevalQ : ∀ w (t : (Σ w : s, g × m × d w × d w) → O), MvPolynomial.eval (fun j => res (t j)) (Q w) = res (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det`.

Introduce `w t`. Simplify using `only [Q]`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`.

Simplify using `[L, Matrix.mul_apply, bigRect, Matrix.sum_apply, map_sum]`. Establish `hsum : ∀ w (φ : g × m × d w × d w → O), bigRect (ρ w) (∑ j : (Σ w : s, g × m × d w × d w), (Pi.single (M` using `fun w => g × m × d w × d w → O) w φ j.1 j.2) • c j) = fun p q => φ (p.1, q.1, p.2, q.2) := by`. Introduce `w φ`. Use function extensionality and compare the values at `p q`. Simplify using `only [bigRect, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]`.

Rewrite using `[Fintype.sum_sigma]`. Rewrite using `[Fintype.sum_eq_single w (fun x hx => by simp [Pi.single_eq_of_ne hx])]`. Simplify using `only [Pi.single_eq_same]`. Rewrite using `[Fintype.sum_eq_single (p.1, q.1, p.2, q.2)]`. Simplify using `[c, r, Function.surjInv_eq (hρ w)]`.

Introduce and unpack `⟨i', k', a', b'⟩ hy`. Simplify using `only [c, r, Matrix.single_apply]`. Use `split_ifs with h1`. Take `⟨rfl, rfl⟩` from `h1`. Rewrite using `[Function.surjInv_eq (hρ w), Matrix.single_apply, if_neg, smul_zero]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hy rfl`. Simplify using the standard rewrite rules. Establish `hQne : ∀ w, Q w ≠ 0`. Introduce `w hQ`.

Use `set t0 : (Σ w : s, g × m × d w × d w) → O := fun j => Pi.single (M := fun w => g × m × d w × d w → O) w (fun x => C0 w (x.1, x.2.2.1) (x.2.1, x.2.2.2)) j.1 j.2 with ht0`. Establish `h1` using `hevalQ w t0`. Rewrite `h1` using `[hQ, map_zero]`. Establish `h2 : bigRect (ρ w) (∑ j, t0 j • c j) = C0 w`. Rewrite using `[ht0, hsum]`.

Rewrite `h1` using `[h2]`. Conclude with `(IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hC0 w) h1.symm`. Establish `hprod : (∏ w, Q w) ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun w _ => hQne w)`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (∏ w, Q w) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Simplify using `only [not_exists, not_not] at hcon`. Conclude with `hprod (MvPolynomial.funext fun x => by rw [hcon x, map_zero])`. Rewrite `hx` using `[map_prod]`. Establish `hxw : ∀ w, MvPolynomial.eval x (Q w) ≠ 0` using `fun w => (Finset.prod_ne_zero_iff.1 hx) w (Finset.mem_univ w)`. Set `t : (Σ w : s, g × m × d w × d w) → O` to `fun j => Function.surjInv (IsLocalRing.residue_surjective (R := O)) (x j)`.

Establish `htx : (fun j => res (t j)) = x` using `funext fun j => Function.surjInv_eq _ _`. Use `⟨∑ j, t j • c j, fun w => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, ← hevalQ w t, htx]`. Conclude with `hxw w`.

Use `show Module.length O (LinearMap.ker (relMap O (KO O) (bigMat (ρ w) (_ * P)))) = _`. Rewrite using `[gen_bigMat_mul, hgood w _ hu]`.
-/
theorem generic : StatGeneric := by
  intro R O _ _ _ _ _ _ m g s _ _ _ _ d _ _ ρ hρ P
  classical
  have hk := fun w => gen_key (O := O) (bigRect (ρ w) P)
  choose n U f e hC0 hgood using hk
  choose C0 hC0 using hC0
  let res := IsLocalRing.residue O
  let r : ∀ w, d w → d w → R := fun w a b => Function.surjInv (hρ w) (Matrix.single a b 1)
  let c : (Σ w : s, g × m × d w × d w) → Matrix g m R := fun j =>
    Matrix.single j.2.1 j.2.2.1 (r j.1 j.2.2.2.1 j.2.2.2.2)
  let L : ∀ w, Matrix (g × d w) (m × d w) (MvPolynomial (Σ w : s, g × m × d w × d w)
      (IsLocalRing.ResidueField O)) := fun w p q =>
    ∑ j, MvPolynomial.X j * MvPolynomial.C (res (ρ w (c j p.1 q.1) p.2 q.2))
  let Q : s → MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O) := fun w =>
    (Matrix.of fun p q => ∑ l, L w (e w p) l * MvPolynomial.C (res (U w l (f w q)))).det
  have hevalQ : ∀ w (t : (Σ w : s, g × m × d w × d w) → O),
      MvPolynomial.eval (fun j => res (t j)) (Q w) =
        res (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    intro w t
    simp only [Q]
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q
    simp [L, Matrix.mul_apply, bigRect, Matrix.sum_apply, map_sum]

  have hsum : ∀ w (φ : g × m × d w × d w → O),
      bigRect (ρ w) (∑ j : (Σ w : s, g × m × d w × d w),
        (Pi.single (M := fun w => g × m × d w × d w → O) w φ j.1 j.2) • c j) =
        fun p q => φ (p.1, q.1, p.2, q.2) := by
    intro w φ
    funext p q
    simp only [bigRect, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]
    rw [Fintype.sum_sigma]
    rw [Fintype.sum_eq_single w (fun x hx => by simp [Pi.single_eq_of_ne hx])]
    simp only [Pi.single_eq_same]
    rw [Fintype.sum_eq_single (p.1, q.1, p.2, q.2)]
    · simp [c, r, Function.surjInv_eq (hρ w)]
    · rintro ⟨i', k', a', b'⟩ hy
      simp only [c, r, Matrix.single_apply]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1
        rw [Function.surjInv_eq (hρ w), Matrix.single_apply, if_neg, smul_zero]
        rintro ⟨rfl, rfl⟩
        exact hy rfl
      · simp
  have hQne : ∀ w, Q w ≠ 0 := by
    intro w hQ
    set t0 : (Σ w : s, g × m × d w × d w) → O := fun j =>
      Pi.single (M := fun w => g × m × d w × d w → O) w
        (fun x => C0 w (x.1, x.2.2.1) (x.2.1, x.2.2.2)) j.1 j.2 with ht0
    have h1 := hevalQ w t0
    rw [hQ, map_zero] at h1
    have h2 : bigRect (ρ w) (∑ j, t0 j • c j) = C0 w := by
      rw [ht0, hsum]
    rw [h2] at h1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hC0 w) h1.symm
  have hprod : (∏ w, Q w) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun w _ => hQne w)
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (∏ w, Q w) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hprod (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  rw [map_prod] at hx
  have hxw : ∀ w, MvPolynomial.eval x (Q w) ≠ 0 := fun w =>
    (Finset.prod_ne_zero_iff.1 hx) w (Finset.mem_univ w)
  let t : (Σ w : s, g × m × d w × d w) → O := fun j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) (x j)
  have htx : (fun j => res (t j)) = x := funext fun j => Function.surjInv_eq _ _
  refine ⟨∑ j, t j • c j, fun w => ?_⟩
  have hu : IsUnit (Matrix.of fun p q =>
      (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hevalQ w t, htx]
    exact hxw w
  show Module.length O (LinearMap.ker (relMap O (KO O) (bigMat (ρ w) (_ * P)))) = _
  rw [gen_bigMat_mul, hgood w _ hu]

end Formalism.NG
