import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Take `⟨κ, a, ha, hspan, hli⟩` from `exists_linearIndependent' K (fun i : m => (M.map g) i)`. Establish `: Fintype κ` using `Fintype.ofInjective a ha`. Establish `h1 : Fintype.card κ ≤ Fintype.card l`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Simplify using `using this`.

Establish `h2 : Fintype.card l ≤ Fintype.card κ`. Establish `hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Apply `hM` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Establish `hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a))`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)), y ⬝ᵥ x = 0`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`. Conclude with `congrFun hx k`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]`. Consider the case `smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]`. Conclude with `key _ hi`. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact.

Simplify using `using this`. Set `e : l ≃ κ` to `Fintype.equivOfCardEq (le_antisymm h2 h1)`. Set `N : Matrix l l R` to `M.submatrix (a ∘ e) id`. Establish `hN : IsUnit (N.map g)`. Rewrite using `[← Matrix.linearIndependent_rows_iff_isUnit]`.

Conclude with `hli.comp e e.injective`. Use `⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hN` using `[Matrix.isUnit_iff_isUnit_det]`. Establish `: g N.det = (N.map g).det` using `by rw [RingHom.map_det]; rfl`. Rewrite using `[this]`.

Conclude with `hN.ne_zero`. Rewrite using `[Matrix.mul_assoc]`. Establish `: (1 : Matrix m m R).submatrix (a ∘ e) id * M = N`. Use extensionality with `i j`. Simplify using `[N, Matrix.mul_apply, Matrix.one_apply]`.

Rewrite using `[this, Matrix.adjugate_mul]`.
-/
theorem exists_mul_eq_smul_one_of_mulVec_injective {R K : Type} [CommRing R] [Field K]
    (g : R →+* K) {m l : Type} [Fintype m] [Fintype l] [DecidableEq l] (M : Matrix m l R)
    (hM : ∀ x : l → K, (M.map g).mulVec x = 0 → x = 0) :
    ∃ (r : R) (T : Matrix l m R), g r ≠ 0 ∧ T * M = r • (1 : Matrix l l R) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun i : m => (M.map g) i)
  have : Fintype κ := Fintype.ofInjective a ha
  have h1 : Fintype.card κ ≤ Fintype.card l := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have h2 : Fintype.card l ≤ Fintype.card κ := by
    have hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply hM
      funext i
      have hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)),
          y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact congrFun hx k
        | zero => simp
        | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
        | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
      exact key _ hi
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  let e : l ≃ κ := Fintype.equivOfCardEq (le_antisymm h2 h1)
  let N : Matrix l l R := M.submatrix (a ∘ e) id
  have hN : IsUnit (N.map g) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e e.injective
  refine ⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hN
    have : g N.det = (N.map g).det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hN.ne_zero
  · rw [Matrix.mul_assoc]
    have : (1 : Matrix m m R).submatrix (a ∘ e) id * M = N := by
      ext i j
      simp [N, Matrix.mul_apply, Matrix.one_apply]
    rw [this, Matrix.adjugate_mul]

/- English proof (translation)
Take `⟨κ, s, hs, hspan, hli⟩` from `exists_linearIndependent' K (fun j : a => (D₀.map g).col j)`. Establish `: Fintype κ` using `Fintype.ofInjective s hs`. Set `S : Matrix a κ R` to `(1 : Matrix a a R).submatrix id s`. Establish `hDS : D₀ * S = D₀.submatrix id s`. Use extensionality with `i j`.

Simplify using `[S, Matrix.mul_apply, Matrix.one_apply]`. Establish `hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x = ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k`. Introduce `x`. Use function extensionality and compare the values at `i`. Simplify using `[hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.

Take `⟨r₀, T₀, hr₀, hT₀⟩` from `exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by`. Introduce `x hx`. Rewrite `hx` using `[hsum]`. Use function extensionality and compare the values at `k`. Conclude with `Fintype.linearIndependent_iff.1 hli x hx k)`.

Take `⟨r₁, T₁, hr₁, hT₁⟩` from `exists_mul_eq_smul_one_of_mulVec_injective g (Matrix.fromRows T₀ D₁) (by`. Introduce `w hw`. Establish `hw1 : (T₀.map g).mulVec w = 0`. Use function extensionality and compare the values at `k`. Conclude with `congrFun hw (Sum.inl k)`.

Establish `hw2 : (D₁.map g).mulVec w = 0`. Use function extensionality and compare the values at `k`. Conclude with `congrFun hw (Sum.inr k)`. Take `⟨v, hv⟩` from `hex w hw2`. Establish `hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s))`.

Rewrite using `[hspan, ← hv]`. Establish `: (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Take `⟨u, hu⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hmem`. Rewrite `hu` using `[← hsum]`. Rewrite `hw1` using `[← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀]`. Establish `hu0 : u = 0`.

Use function extensionality and compare the values at `k`. Use `congrFun hw1 k` as an intermediate fact. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this`. Break down `this with h | h` into its components or cases. Conclude with `absurd h hr₀`.

Conclude with `h`. Rewrite using `[← hu, hu0, Matrix.mulVec_zero])`. Set `Q : Matrix a a R` to `r₀ • (1 : Matrix a a R) - S * T₀ * D₀`. Establish `hQS : Q * S = 0`. Simplify using `only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀, Matrix.mul_smul, Matrix.mul_one, sub_self]`.

Establish `hDQ : r₁ • (D₀ * Q) = 0`. Establish `h1 : T₀ * (D₀ * Q) = 0`. Establish `: T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀)`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]`.

Establish `h2 : D₁ * (D₀ * Q) = 0` using `by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]`. Establish `h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0`. Rewrite using `[Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hT₁, Matrix.smul_mul, Matrix.one_mul]`.

Use `_ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]`. Set `t` to `{j : a // j ∉ Set.range s}`. Set `e : Fin (Fintype.card t) ≃ t` to `(Fintype.equivFin t).symm`. Set `f : Fin (Fintype.card t) → a` to `fun i => (e i).1`. Establish `hf : Function.Injective f` using `Subtype.val_injective.comp e.injective`.

Establish `hfs : ∀ i k, f i ≠ s k` using `fun i k h => (e i).2 ⟨k, h.symm⟩`. Set `E : Matrix a (Fin (Fintype.card t)) R` to `(1 : Matrix a a R).submatrix id f`. Establish `hEE : E.transpose * E = 1`. Use extensionality with `i j`. Simplify using `[E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]`.

Establish `hES : E.transpose * S = 0`. Use extensionality with `i j`. Simplify using `[E, S, Matrix.mul_apply, Matrix.one_apply, hfs]`. Establish `hQE : Q * E * E.transpose = Q`. Use extensionality with `i j`.

Establish `hQE' : Q * E = Q.submatrix id f`. Use extensionality with `i j`. Simplify using `[E, Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[hQE']`. Distinguish the cases in `hj : j ∈ Set.range s`.

Take `⟨k, rfl⟩` from `hj`. Establish `: Q i (s k) = (Q * S) i k`. Simplify using `[S, Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[this, hQS]`. Simplify using `[E, Matrix.mul_apply, Matrix.one_apply, hfs]`.

Take `⟨k, hk⟩ : ∃ k, f k = j` from `⟨e.symm ⟨j, hj⟩, by simp [f]⟩`. Substitute `hk` using the available equality. Simplify using `[E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]`. Use `⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_ne_zero hr₁ hr₀`. Rewrite using `[Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]`. Establish `: E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E)`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul, sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]`.

Rewrite using `[Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]`. Simplify using `only [Q, sub_add_cancel]`.
-/
theorem exists_kernel_certificate {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by
  classical
  obtain ⟨κ, s, hs, hspan, hli⟩ := exists_linearIndependent' K (fun j : a => (D₀.map g).col j)
  have : Fintype κ := Fintype.ofInjective s hs
  let S : Matrix a κ R := (1 : Matrix a a R).submatrix id s
  have hDS : D₀ * S = D₀.submatrix id s := by
    ext i j
    simp [S, Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x =
      ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k := by
    intro x
    funext i
    simp [hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨r₀, T₀, hr₀, hT₀⟩ := exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by
    intro x hx
    rw [hsum] at hx
    funext k
    exact Fintype.linearIndependent_iff.1 hli x hx k)
  obtain ⟨r₁, T₁, hr₁, hT₁⟩ := exists_mul_eq_smul_one_of_mulVec_injective g
    (Matrix.fromRows T₀ D₁) (by
    intro w hw
    have hw1 : (T₀.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inl k)
    have hw2 : (D₁.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inr k)
    obtain ⟨v, hv⟩ := hex w hw2
    have hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s)) := by
      rw [hspan, ← hv]
      have : (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [← hsum] at hu
    rw [← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀] at hw1
    have hu0 : u = 0 := by
      funext k
      have := congrFun hw1 k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this
      rcases this with h | h
      · exact absurd h hr₀
      · exact h
    rw [← hu, hu0, Matrix.mulVec_zero])
  let Q : Matrix a a R := r₀ • (1 : Matrix a a R) - S * T₀ * D₀
  have hQS : Q * S = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hDQ : r₁ • (D₀ * Q) = 0 := by
    have h1 : T₀ * (D₀ * Q) = 0 := by
      have : T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀) := by
        simp only [Matrix.mul_assoc]
      simp only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : D₁ * (D₀ * Q) = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    have h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0 := by
      rw [Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]
    calc r₁ • (D₀ * Q) = (T₁ * Matrix.fromRows T₀ D₁) * (D₀ * Q) := by
          rw [hT₁, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  let t := {j : a // j ∉ Set.range s}
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → a := fun i => (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfs : ∀ i k, f i ≠ s k := fun i k h => (e i).2 ⟨k, h.symm⟩
  let E : Matrix a (Fin (Fintype.card t)) R := (1 : Matrix a a R).submatrix id f
  have hEE : E.transpose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hES : E.transpose * S = 0 := by
    ext i j
    simp [E, S, Matrix.mul_apply, Matrix.one_apply, hfs]
  have hQE : Q * E * E.transpose = Q := by
    ext i j
    have hQE' : Q * E = Q.submatrix id f := by
      ext i j
      simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hQE']
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k, rfl⟩ := hj
      have : Q i (s k) = (Q * S) i k := by
        simp [S, Matrix.mul_apply, Matrix.one_apply]
      rw [this, hQS]
      simp [E, Matrix.mul_apply, Matrix.one_apply, hfs]
    · obtain ⟨k, hk⟩ : ∃ k, f k = j := ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
      subst hk
      simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  refine ⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hr₁ hr₀
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]
  · have : E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E) := by
      simp only [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul,
      sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]
    simp only [Q, sub_add_cancel]

/- English proof (translation)
Introduce `R K _ _ g₀ a b c D₀ D₁ h0 hex`. Take `⟨r, n, B, C, H, hr, hB, hCB, hBC⟩` from `exists_kernel_certificate g₀ D₀ D₁ h0 hex`. Use `⟨r, n, B, hr, hB, ?_⟩` and prove the remaining obligations. Introduce `R' _ g hu v hv`. Take `⟨u, hu⟩` from `hu`.

Establish `hone : ∀ (m : ℕ) (x : Fin m → R'), ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x`. Introduce `m x`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]`. Establish `h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z`.

Introduce `z`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]`. Establish `h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v`. Rewrite using `[hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero]`. Use `⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩` and prove the remaining obligations.

Use `show (B.map g).mulVec _ = v`. Rewrite using `[Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]`. Introduce `z hz`. Rewrite using `[← hz, h1, smul_smul, Units.inv_mul, one_smul]`.
-/
theorem exists_matrix_basis_ker_of_exact_at_point :
    ∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v := by
  intro R K _ _ g₀ a b c D₀ D₁ h0 hex
  obtain ⟨r, n, B, C, H, hr, hB, hCB, hBC⟩ := exists_kernel_certificate g₀ D₀ D₁ h0 hex
  refine ⟨r, n, B, hr, hB, ?_⟩
  intro R' _ g hu v hv
  obtain ⟨u, hu⟩ := hu
  have hone : ∀ (m : ℕ) (x : Fin m → R'),
      ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x := by
    intro m x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]
  have h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]
  have h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v := by
    rw [hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      add_zero]
  refine ⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩
  · show (B.map g).mulVec _ = v
    rw [Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]
  · intro z hz
    rw [← hz, h1, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory
