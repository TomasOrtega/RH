import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Set `c : (Fin N → R) →ₗ[R] (Fin N → F)` to `(Algebra.linearMap R F).compLeft (Fin N)`. Establish `hc : ∀ x i, c x i = (x i : F)` using `fun _ _ => rfl`. Establish `hcs : ∀ (a : R) x, c (a • x) = (a : F) • c x`. Introduce `a x`. Use extensionality with `i`.

Simplify using `[hc]`. Set `M : Submodule R (Fin N → R)` to `LinearMap.eqLocus (((Matrix.toLin' e).restrictScalars R) ∘ₗ c) c`. Establish `hM : ∀ x, x ∈ M ↔ e.mulVec (c x) = c x`. Introduce `x`. Simplify using `[M, LinearMap.mem_eqLocus]`.

Take `⟨n, snf⟩` from `Submodule.smithNormalForm (Pi.basisFun R (Fin N)) M`. Establish `ha : ∀ k, snf.a k ≠ 0`. Introduce `k h`. Use `snf.snf k` as an intermediate fact. Rewrite `this` using `[h, zero_smul]`.

Conclude with `snf.bN.ne_zero k (Subtype.ext this)`. Establish `hmem : ∀ k, e.mulVec (c (snf.bM (snf.f k))) = c (snf.bM (snf.f k))`. Introduce `k`. Establish `h1` using `(hM _).1 (snf.bN k).2`. Rewrite `h1` using `[snf.snf k, hcs, Matrix.mulVec_smul]`.

Establish `: (snf.a k : F) ≠ 0` using `fun h => ha k (Subtype.ext h)`. Conclude with `smul_right_injective _ this h1`. Set `u : Matrix (Fin N) (Fin n) F` to `fun i k => (snf.bM (snf.f k) i : F)`. Set `l : Matrix (Fin n) (Fin N) F` to `fun k j => (snf.bM.repr (Pi.single j 1) (snf.f k) : F)`. Establish `hl : ∀ (x : Fin N → R) k, l.mulVec (c x) k = (snf.bM.repr x (snf.f k) : F)`.

Introduce `x k`. Establish `hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R)`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hx]`.

Simplify using `[Matrix.mulVec, dotProduct, l, hc, mul_comm, Finset.sum_apply']`. Use `⟨n, u, l, fun i k => Subtype.property _, fun i k => Subtype.property _, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Conclude with `congrFun (hmem k) i`. Use extensionality with `k k'`.

Use `hl (snf.bM (snf.f k')) k` as an intermediate fact. Use `Eq.trans this ?_` and prove the remaining obligations. Distinguish the cases in `h : k = k'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Establish `: snf.f k' ≠ snf.f k` using `fun h' => h (snf.f.injective h').symm`. Simplify using `[h, Finsupp.single_apply, this]`. Establish `key : ∀ y : Fin N → R, y ∈ M → (u * l).mulVec (c y) = c y`. Introduce `y hy`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Establish `h1 : y = ∑ k, snf.bM.repr y (snf.f k) • snf.bM (snf.f k)` using `by conv_lhs => rw [← snf.bM.sum_repr y]`. Use `symm`. Use `Finset.sum_of_injOn snf.f (snf.f.injective.injOn) (by simp) ?_ (by simp)` and prove the remaining obligations. Introduce `j _ hj`. Establish `: j ∉ Set.range snf.f` using `by simpa using hj`.

Use `snf.repr_eq_zero_of_notMem_range ⟨y, hy⟩ this` as an intermediate fact. Simplify using `at this`. Simplify using `[this]`. Rewrite using `[show l.mulVec (c y) = _ from funext (hl y)]`. Use extensionality with `i`.

Use `conv_rhs => rw [h1]`. Simplify using `[Matrix.mulVec, dotProduct, hc, u, mul_comm, Finset.sum_apply]`. Introduce `x hx`. Use `choose d hdR hd0 hdx using hd`. Set `D : F` to `∏ j, d (x j)`.

Establish `hD : D ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hd0 _`. Establish `hDx : ∀ j, D * x j ∈ R`. Introduce `j`. Establish `: D * x j = (∏ i ∈ Finset.univ.erase j, d (x i)) * (d (x j) * x j)`. Simplify using `only [D]`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `R.mul_mem (R.prod_mem fun i _ => hdR _) (hdx _)`. Set `y : Fin N → R` to `fun j => ⟨D * x j, hDx j⟩`.

Establish `hy : c y = D • x` using `by ext j; simp [hc, y]`. Use `key y ((hM y).2 (by rw [hy, Matrix.mulVec_smul, hx]))` as an intermediate fact. Rewrite `this` using `[hy, Matrix.mulVec_smul]`. Conclude with `smul_right_injective _ hD this`.
-/
theorem exists_integral_basis_fixed_vectors (F : Type) [Field F] (R : Subring F)
    (hR : IsPrincipalIdealRing R) (hd : ∀ x : F, ∃ d ∈ R, d ≠ 0 ∧ d * x ∈ R)
    (N : ℕ) (e : Matrix (Fin N) (Fin N) F) :
    ∃ (n : ℕ) (u : Matrix (Fin N) (Fin n) F) (l : Matrix (Fin n) (Fin N) F),
      (∀ i k, u i k ∈ R) ∧ (∀ k i, l k i ∈ R) ∧ e * u = u ∧ l * u = 1 ∧
      ∀ x : Fin N → F, e.mulVec x = x → (u * l).mulVec x = x := by
  classical
  let c : (Fin N → R) →ₗ[R] (Fin N → F) := (Algebra.linearMap R F).compLeft (Fin N)
  have hc : ∀ x i, c x i = (x i : F) := fun _ _ => rfl
  have hcs : ∀ (a : R) x, c (a • x) = (a : F) • c x := by
    intro a x; ext i; simp [hc]
  let M : Submodule R (Fin N → R) :=
    LinearMap.eqLocus (((Matrix.toLin' e).restrictScalars R) ∘ₗ c) c
  have hM : ∀ x, x ∈ M ↔ e.mulVec (c x) = c x := by
    intro x; simp [M, LinearMap.mem_eqLocus]
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R (Fin N)) M
  have ha : ∀ k, snf.a k ≠ 0 := by
    intro k h
    have := snf.snf k
    rw [h, zero_smul] at this
    exact snf.bN.ne_zero k (Subtype.ext this)
  have hmem : ∀ k, e.mulVec (c (snf.bM (snf.f k))) = c (snf.bM (snf.f k)) := by
    intro k
    have h1 := (hM _).1 (snf.bN k).2
    rw [snf.snf k, hcs, Matrix.mulVec_smul] at h1
    have : (snf.a k : F) ≠ 0 := fun h => ha k (Subtype.ext h)
    exact smul_right_injective _ this h1
  let u : Matrix (Fin N) (Fin n) F := fun i k => (snf.bM (snf.f k) i : F)
  let l : Matrix (Fin n) (Fin N) F := fun k j => (snf.bM.repr (Pi.single j 1) (snf.f k) : F)
  have hl : ∀ (x : Fin N → R) k, l.mulVec (c x) k = (snf.bM.repr x (snf.f k) : F) := by
    intro x k
    have hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    simp [Matrix.mulVec, dotProduct, l, hc, mul_comm, Finset.sum_apply']
  refine ⟨n, u, l, fun i k => Subtype.property _, fun i k => Subtype.property _, ?_, ?_, ?_⟩
  · ext i k
    exact congrFun (hmem k) i
  · ext k k'
    have := hl (snf.bM (snf.f k')) k
    refine Eq.trans this ?_
    by_cases h : k = k'
    · subst h; simp
    · have : snf.f k' ≠ snf.f k := fun h' => h (snf.f.injective h').symm
      simp [h, Finsupp.single_apply, this]
  · have key : ∀ y : Fin N → R, y ∈ M → (u * l).mulVec (c y) = c y := by
      intro y hy
      rw [← Matrix.mulVec_mulVec]
      have h1 : y = ∑ k, snf.bM.repr y (snf.f k) • snf.bM (snf.f k) := by
        conv_lhs => rw [← snf.bM.sum_repr y]
        symm
        refine Finset.sum_of_injOn snf.f (snf.f.injective.injOn) (by simp) ?_ (by simp)
        intro j _ hj
        have : j ∉ Set.range snf.f := by simpa using hj
        have := snf.repr_eq_zero_of_notMem_range ⟨y, hy⟩ this
        simp at this
        simp [this]
      rw [show l.mulVec (c y) = _ from funext (hl y)]
      ext i
      conv_rhs => rw [h1]
      simp [Matrix.mulVec, dotProduct, hc, u, mul_comm, Finset.sum_apply]
    intro x hx
    choose d hdR hd0 hdx using hd
    let D : F := ∏ j, d (x j)
    have hD : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hd0 _
    have hDx : ∀ j, D * x j ∈ R := by
      intro j
      have : D * x j = (∏ i ∈ Finset.univ.erase j, d (x i)) * (d (x j) * x j) := by
        simp only [D]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]; ring
      rw [this]
      exact R.mul_mem (R.prod_mem fun i _ => hdR _) (hdx _)
    let y : Fin N → R := fun j => ⟨D * x j, hDx j⟩
    have hy : c y = D • x := by ext j; simp [hc, y]
    have := key y ((hM y).2 (by rw [hy, Matrix.mulVec_smul, hx]))
    rw [hy, Matrix.mulVec_smul] at this
    exact smul_right_injective _ hD this

/- English proof (translation)
Introduce `F _ R hR hd ι _ _ N e he hs`. Use `choose n u l hu hl heu hlu hx using fun τ => exists_integral_basis_fixed_vectors F R hR hd N (e τ)`. Establish `hule : ∀ τ, u τ * l τ * e τ = e τ`. Introduce `τ`. Use extensionality with `i j`.

Establish `h1 : (e τ).mulVec (fun i => e τ i j) = fun i => e τ i j`. Use extensionality with `i`. Use `congrFun (congrFun (he τ τ) i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Conclude with `congrFun (hx τ _ h1) i`.

Set `Q : Matrix (Fin N) (Σ τ, Fin (n τ)) F` to `fun i p => u p.1 i p.2`. Set `P : Matrix (Σ τ, Fin (n τ)) (Fin N) F` to `fun p j => (l p.1 * e p.1) p.2 j`. Establish `hPQ : P * Q = 1`. Use extensionality with `⟨σ, k⟩ ⟨τ, k'⟩`. Establish `h1 : (P * Q) ⟨σ, k⟩ ⟨τ, k'⟩ = (l σ * e σ * u τ) k k'` using `rfl`.

Rewrite using `[h1, ← heu τ, Matrix.mul_assoc, ← Matrix.mul_assoc (e σ), he]`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `[heu, hlu, Matrix.one_apply]`. Simplify using `[h, Matrix.one_apply]`.

Establish `hQP : Q * P = 1`. Rewrite using `[← hs]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← hule τ, Matrix.mul_assoc]`. Both sides reduce to the same expression. Establish `hcard : Fintype.card (Σ τ, Fin (n τ)) = N`. Use `(Matrix.toLin'OfInv hPQ hQP).finrank_eq` as an intermediate fact. Simplify using `only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this`.

Use linear arithmetic over natural numbers and integers. Set `φ` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨fun s => (φ s).1, fun i s => u (φ s).1 i (φ s).2, fun r j => l (φ r).1 (φ r).2 j, fun i j => ⟨hu _ _ _, hl _ _ _⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`. Use extensionality with `i`.

Conclude with `congrFun (congrFun (heu (φ s).1) i) (φ s).2`. Introduce `r s hrs`. Establish `hiff : r = s ↔ φ r = φ s` using `φ.injective.eq_iff.symm`. Express the relevant statement in the definitionally equal form `(l (φ r).1 * u (φ s).1) (φ r).2 (φ s).2 = _`. Simplify using `only [hiff]`.

Simplify using `only at hrs`. Use `revert hrs`. Generalize the expression as in `φ r = p`. Generalize the expression as in `φ s = q`. Take `⟨σ, k⟩` from `p`.

Take `⟨τ, k'⟩` from `q`. Introduce `h`. Simplify using `only at h`. Substitute `h` using the available equality. Simplify using `[hlu, Matrix.one_apply]`.
-/
theorem exists_integral_block_bases_of_projectors :
    ∀ (F : Type) [Field F] (R : Subring F), IsPrincipalIdealRing R → (∀ x : F, ∃ d ∈ R, d ≠ 0 ∧ d * x ∈ R) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (e : ι → Matrix (Fin N) (Fin N) F),
    (∀ σ τ, e σ * e τ = if σ = τ then e τ else 0) → ∑ τ, e τ = 1 →
    ∃ (b : Fin N → ι) (U L : Matrix (Fin N) (Fin N) F), (∀ i j, U i j ∈ R ∧ L i j ∈ R) ∧
      (∀ s, (e (b s)).mulVec (fun i => U i s) = fun i => U i s) ∧
      ∀ r s, b r = b s → (L * U) r s = if r = s then 1 else 0 := by
  intro F _ R hR hd ι _ _ N e he hs
  classical
  choose n u l hu hl heu hlu hx using fun τ => exists_integral_basis_fixed_vectors F R hR hd N (e τ)
  have hule : ∀ τ, u τ * l τ * e τ = e τ := by
    intro τ
    ext i j
    have h1 : (e τ).mulVec (fun i => e τ i j) = fun i => e τ i j := by
      ext i
      have := congrFun (congrFun (he τ τ) i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    exact congrFun (hx τ _ h1) i
  let Q : Matrix (Fin N) (Σ τ, Fin (n τ)) F := fun i p => u p.1 i p.2
  let P : Matrix (Σ τ, Fin (n τ)) (Fin N) F := fun p j => (l p.1 * e p.1) p.2 j
  have hPQ : P * Q = 1 := by
    ext ⟨σ, k⟩ ⟨τ, k'⟩
    have h1 : (P * Q) ⟨σ, k⟩ ⟨τ, k'⟩ = (l σ * e σ * u τ) k k' := rfl
    rw [h1, ← heu τ, Matrix.mul_assoc, ← Matrix.mul_assoc (e σ), he]
    by_cases h : σ = τ
    · subst h
      simp [heu, hlu, Matrix.one_apply]
    · simp [h, Matrix.one_apply]
  have hQP : Q * P = 1 := by
    rw [← hs]
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hule τ, Matrix.mul_assoc]
    rfl
  have hcard : Fintype.card (Σ τ, Fin (n τ)) = N := by
    have := (Matrix.toLin'OfInv hPQ hQP).finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  let φ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun s => (φ s).1, fun i s => u (φ s).1 i (φ s).2, fun r j => l (φ r).1 (φ r).2 j,
    fun i j => ⟨hu _ _ _, hl _ _ _⟩, ?_, ?_⟩
  · intro s
    ext i
    exact congrFun (congrFun (heu (φ s).1) i) (φ s).2
  · intro r s hrs
    have hiff : r = s ↔ φ r = φ s := φ.injective.eq_iff.symm
    change (l (φ r).1 * u (φ s).1) (φ r).2 (φ s).2 = _
    simp only [hiff]
    dsimp only at hrs
    revert hrs
    generalize φ r = p
    generalize φ s = q
    obtain ⟨σ, k⟩ := p
    obtain ⟨τ, k'⟩ := q
    intro h
    dsimp only at h
    subst h
    simp [hlu, Matrix.one_apply]

end GlobalTheory
