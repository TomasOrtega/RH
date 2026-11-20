import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeQuotientLeCocycleSpanDeterminant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupport

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.CutDetOrd

open GlobalTheory.CutDet

/- English proof (translation)
Introduce `D i r ρ π Xs S _ hS _ f hf h0`. Take `⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩` from `hS`. Take `⟨cf, hcf, -⟩` from `hb f hf`. Establish `huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i, (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) : S.X' → D.nd.O i) * b k → c = 0`. Introduce `c hc`.

Take `⟨c0, -, hc0⟩` from `hb 0 (zero_mem _)`. Rewrite using `[hc0 c hc, hc0 0 (by funext x'; simp)]`. Establish `hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0`. Introduce `k x hx hZ`. Use `cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k` and prove the remaining obligations.

Rewrite using `[← hcf]`. Conclude with `h0 x' (hp ▸ hx) (hp ▸ hZ)`. Rewrite using `[hcf, Finset.sum_apply]`. Use `Ideal.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply]`.

Use `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)` and prove the remaining obligations. Rewrite using `[hπ]`.
-/
theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

/- English proof (translation)
Introduce `D i r ρ π Xs S _ hG _ hN x' hx hZ`. Establish `hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1` using `hG.2.2.2.2.2.2.2.2.2.2.1.1 x'`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0`.

Introduce `η`. Apply `hN _ hx hZ` to reduce the goal to its premises. Introduce `g`. Establish `h` using `hcon η g`. Establish `hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x'`.

Unfold `yg`. Rewrite using `[← Matrix.smul_mul]`. Both sides reduce to the same expression. Rewrite `h` using `[hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero, ← Matrix.mulVec_mulVec]`. Conclude with `h`.

Establish `hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0` using `LinearMap.ext h0`. Unfold `Matrix.rank at hrank`. Rewrite `hrank` using `[hz, LinearMap.range_zero, finrank_bot]`. Conclude with `zero_ne_one hrank`.
-/
theorem exists_ne_zero : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  unfold Matrix.rank at hrank
  rw [hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

/- English proof (translation)
Introduce `D i r ρ π Xs S hr hS hπ _ hchi`. Establish `h52` using `value_mem_ccOff D i r ρ π Xs S hr hS hπ`. Establish `h54` using `exists_ne_zero D i r ρ π Xs S hr hS hπ hchi`. Take `⟨-, -, hcomp, hsurj, -, -, -, -, -, -, -, h51, -⟩` from `hS`. Establish `hinj : Function.Injective (algebraMap (D.nd.O i) (KK D.nd i))` using `IsFractionRing.injective _ _`.

Set `A : Subalgebra (D.nd.O i) (S.X' → MatN D.nd i)` to `spanAlg S.T' (fun x' => rO D.nd i r (S.p x'))`. Take `⟨g, γ, hγ⟩` from `exists_gens A (yg D.nd r S)`. Establish `hY : ∀ m, InY D.nd r S m → ∃ θ : Fin g → A, m = ∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)`. Introduce and unpack `_ ⟨m, a, s, ha, rfl⟩`. Conclude with `hγ m a s ha`.

Take `⟨P, Q, hPQ, hQP, hconj⟩` from `exists_conj S.e`. Establish `hbl` using `fun a (ha : a ∈ A) => hconj _ _ _ (hcomp a ha)`. Take `⟨⟨fρ, hfρ⟩, hχ⟩` from `exists_homs hinj A S.π' P Q hPQ hQP S.ψρ S.ψχ hbl`. Use `choose fχ hfχ using hχ`. Set `Rel : Submodule A (Fin g → A)` to `{ carrier := {θ | ∀ x', S.p x' ∈ Xs → (∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)) x' = 0} add_mem' := fun {a b} ha hb x' hx => by`.

Use `congrArg₂ (· + ·) (ha x' hx) (hb x' hx)` as an intermediate fact. Simplify `this` using `[add_mul, Finset.sum_add_distrib]`. Use the proof step `zero_mem' := fun x' _ => by simp`. Use the proof step `smul_mem' := fun c θ hθ x' hx => by`. Use `congrArg (fun z => (c : S.X' → MatN D.nd i) x' * z) (hθ x' hx)` as an intermediate fact.

Simplify `this }` using `[Finset.sum_apply, Finset.mul_sum, mul_assoc]`. Set `d : Option (Fin D.R.t) → ℕ` to `blockDim D.R.r`. Set `ψ` to `blockHom fρ fχ`. Establish `hψχ : ∀ c (a : A), ψ (some c) a = S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))`. Introduce `c a`.

Rewrite using `[← hfχ, ← Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound (D.nd.O i) A (Option (Fin D.R.t)) d ψ (by`. Introduce and unpack `(_ | c) B`. Take `⟨a, ha, rfl⟩` from `hsurj B`.

Conclude with `⟨⟨a, ha⟩, hfρ _⟩`. Express the relevant statement in the definitionally equal form `Matrix (Fin 1) (Fin 1) (D.nd.O i) at B`. Use `⟨algebraMap _ _ (B 0 0), ((ψ (some c)).commutes _).trans ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap _ (Matrix (Fin 1) (Fin 1) (D.nd.O i)) _ = B`. Use extensionality with `a b`.

Rewrite using `[Subsingleton.elim a 0, Subsingleton.elim b 0]`. Simplify using `[Matrix.algebraMap_matrix_apply]) g Rel (ccOff i Xs π) (by`. Introduce `n θ hθ m`. Establish `hT` using `GlobalTheory.BlockDetPoly.main S.T' D.R.nV A h51 n g (fun k p q => θ k p q) (fun k p q => (θ k p q).2) m`. Establish `h2` using `h52 _ hT (by`.

Introduce `x' hx hz`. Take `⟨η, s, hs⟩` from `h54 x' hx hz`. Rewrite using `[det_generic_eq_zero hinj (fun k p q => (θ k p q : S.X' → MatN D.nd i) x') (fun q => ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η) ?_ ?_, MvPolynomial.coeff_zero]`. Introduce `h0`. Apply `hs` to reduce the goal to its premises.

Take `⟨t, ht⟩` from `hγ 1 (fun _ => 1) (fun _ => s) (fun _ => A.one_mem)`. Rewrite `ht` using `[Fin.sum_univ_one, one_mul]`. Rewrite using `[ht, Finset.sum_apply, ← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, map_mul, ← Matrix.mulVec_mulVec, RingHom.mapMatrix_apply _ (yg D.nd r S (γ q) x'), show ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η = 0 from congrFun h0 q, Matrix.mulVec_zero]`.

Introduce `k p`. Establish `h3` using `congrArg (fun z => ((toK D.nd i).mapMatrix z).mulVec η) (hθ k p x' hx)`. Simplify using `only [Finset.sum_apply, map_sum, Matrix.sum_mulVec, Pi.mul_apply, map_mul, map_zero, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h3`. Conclude with `h3)`. Rewrite `h2` using `[det_generic_blocks hinj P Q hPQ hQP (fun k p q => (θ k p q : S.X' → MatN D.nd i) S.π') (fun k p q => S.ψρ (θ k p q)) (fun c k p q => S.ψχ c (θ k p q)) (fun k p q => hbl _ (θ k p q).2)]`.

Rewrite using `[Fintype.prod_option]`. Use `h2 using 3` and compare the differences between its conclusion and the goal. Use `congr 1 ext1 pa qb`. Simplify using `only [Matrix.of_apply, ← hfρ]`. Both sides reduce to the same expression.

Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `(Matrix.det_submatrix_equiv_self (Equiv.prodUnique (Fin g) (Fin 1)).symm _).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use `ext1 p q`. Simplify using `[hψχ])`.

Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_option]`. Use `add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_)` and prove the remaining obligations. Conclude with `length_sol_le A fρ S.ψρ hfρ (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)`. Conclude with `length_sol_le A (ψ (some c)) _ (hψχ c) (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  intro D i r ρ π Xs S hr hS hπ _ hchi
  classical
  have h52 := value_mem_ccOff D i r ρ π Xs S hr hS hπ
  have h54 := exists_ne_zero D i r ρ π Xs S hr hS hπ hchi
  obtain ⟨-, -, hcomp, hsurj, -, -, -, -, -, -, -, h51, -⟩ := hS
  have hinj : Function.Injective (algebraMap (D.nd.O i) (KK D.nd i)) := IsFractionRing.injective _ _
  let A : Subalgebra (D.nd.O i) (S.X' → MatN D.nd i) := spanAlg S.T' (fun x' => rO D.nd i r (S.p x'))
  obtain ⟨g, γ, hγ⟩ := exists_gens A (yg D.nd r S)
  have hY : ∀ m, InY D.nd r S m → ∃ θ : Fin g → A, m = ∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q) := by
    rintro _ ⟨m, a, s, ha, rfl⟩
    exact hγ m a s ha
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_conj S.e
  have hbl := fun a (ha : a ∈ A) => hconj _ _ _ (hcomp a ha)
  obtain ⟨⟨fρ, hfρ⟩, hχ⟩ := exists_homs hinj A S.π' P Q hPQ hQP S.ψρ S.ψχ hbl
  choose fχ hfχ using hχ
  let Rel : Submodule A (Fin g → A) :=
    { carrier := {θ | ∀ x', S.p x' ∈ Xs → (∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)) x' = 0}
      add_mem' := fun {a b} ha hb x' hx => by
        have := congrArg₂ (· + ·) (ha x' hx) (hb x' hx)
        simpa [add_mul, Finset.sum_add_distrib] using this
      zero_mem' := fun x' _ => by simp
      smul_mem' := fun c θ hθ x' hx => by
        have := congrArg (fun z => (c : S.X' → MatN D.nd i) x' * z) (hθ x' hx)
        simpa [Finset.sum_apply, Finset.mul_sum, mul_assoc] using this }
  let d : Option (Fin D.R.t) → ℕ := blockDim D.R.r
  let ψ := blockHom fρ fχ
  have hψχ : ∀ c (a : A), ψ (some c) a = S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    intro c a
    rw [← hfχ, ← Algebra.algebraMap_eq_smul_one]
    rfl
  have key := GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound (D.nd.O i) A (Option (Fin D.R.t)) d ψ (by
    rintro (_ | c) B
    · obtain ⟨a, ha, rfl⟩ := hsurj B
      exact ⟨⟨a, ha⟩, hfρ _⟩
    · change Matrix (Fin 1) (Fin 1) (D.nd.O i) at B
      refine ⟨algebraMap _ _ (B 0 0), ((ψ (some c)).commutes _).trans ?_⟩
      change algebraMap _ (Matrix (Fin 1) (Fin 1) (D.nd.O i)) _ = B
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.algebraMap_matrix_apply]) g Rel (ccOff i Xs π) (by
    intro n θ hθ m
    have hT := GlobalTheory.BlockDetPoly.main S.T' D.R.nV A h51 n g (fun k p q => θ k p q) (fun k p q => (θ k p q).2) m
    have h2 := h52 _ hT (by
      intro x' hx hz
      obtain ⟨η, s, hs⟩ := h54 x' hx hz
      rw [det_generic_eq_zero hinj (fun k p q => (θ k p q : S.X' → MatN D.nd i) x')
        (fun q => ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η) ?_ ?_, MvPolynomial.coeff_zero]
      · intro h0
        apply hs
        obtain ⟨t, ht⟩ := hγ 1 (fun _ => 1) (fun _ => s) (fun _ => A.one_mem)
        rw [Fin.sum_univ_one, one_mul] at ht
        rw [ht, Finset.sum_apply, ← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [Pi.mul_apply, map_mul, ← Matrix.mulVec_mulVec, RingHom.mapMatrix_apply _ (yg D.nd r S (γ q) x'),
          show ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η = 0 from congrFun h0 q, Matrix.mulVec_zero]
      · intro k p
        have h3 := congrArg (fun z => ((toK D.nd i).mapMatrix z).mulVec η) (hθ k p x' hx)
        simp only [Finset.sum_apply, map_sum, Matrix.sum_mulVec, Pi.mul_apply, map_mul, map_zero,
          Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h3
        exact h3)
    rw [det_generic_blocks hinj P Q hPQ hQP (fun k p q => (θ k p q : S.X' → MatN D.nd i) S.π')
      (fun k p q => S.ψρ (θ k p q)) (fun c k p q => S.ψχ c (θ k p q))
      (fun k p q => hbl _ (θ k p q).2)] at h2
    rw [Fintype.prod_option]
    convert h2 using 3
    · congr 1
      ext1 pa qb
      simp only [Matrix.of_apply, ← hfρ]
      rfl
    · refine Finset.prod_congr rfl fun c _ => ?_
      refine (Matrix.det_submatrix_equiv_self (Equiv.prodUnique (Fin g) (Fin 1)).symm _).symm.trans ?_
      congr 1
      ext1 p q
      simp [hψχ])
  refine key.trans ?_
  rw [Fintype.sum_option]
  refine add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_)
  · exact length_sol_le A fρ S.ψρ hfρ (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0)
      hY Rel (fun _ h => h) (fun _ _ => rfl)
  · exact length_sol_le A (ψ (some c)) _ (hψχ c) (yg D.nd r S) γ (InY D.nd r S)
      (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)

end GlobalTheory.CutDetOrd

end
