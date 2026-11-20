import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OnCoord
variable {D : D7}

/- English proof (translation)
The claim follows from `D.host.conjE_apply (embT D τ) x`.
-/
theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) :=
  D.host.conjE_apply (embT D τ) x

/- English proof (translation)
Unfold `hYY`. Rewrite using `[← h.2]`. Simplify using `only [coordB, embV, tor0, map_sum, map_mul, embT_conj]`.
-/
theorem coord_emb (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (y : Matrix (Fin N') (Fin N) D.host.E) :
    coordB D (tor0 D cc δ) b k (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D y (b k) : D.host.K) : D.host.E) := by
  unfold hYY
  rw [← h.2]
  simp only [coordB, embV, tor0, map_sum, map_mul, embT_conj]

/- English proof (translation)
Simplify using `only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem coord_add (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (z w : VC D N N') :
    coordB D T b k (z + w) = coordB D T b k z + coordB D T b k w := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [coordB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem coord_smul (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (c : ℂ) (z : VC D N N') :
    coordB D T b k (c • z) = c * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

noncomputable def coordL (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b k
  map_add' := coord_add T b k
  map_smul' := coord_smul T b k

/- English proof (translation)
The claim follows from `map_sum (coordL T b k) z s`.
-/
theorem coord_sum (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) {ι : Type} (s : Finset ι) (z : ι → VC D N N') :
    coordB D T b k (∑ i ∈ s, z i) = ∑ i ∈ s, coordB D T b k (z i) :=
  map_sum (coordL T b k) z s

/- English proof (translation)
Introduce `τ τ' h`. Apply `D.eTau.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : D.host.sigmaOf (D.eTau τ : D.R.GG) = D.host.sigmaOf (D.eTau τ' : D.R.GG)`. Use extensionality with `x`.

Use `DFunLike.congr_fun h x` as an intermediate fact. Conclude with `D.host.φ₀.injective this`. Conclude with `(D.host.gal).symm.injective h1`.
-/
theorem embT_injective : Function.Injective (embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply Subtype.ext
  have h1 : D.host.sigmaOf (D.eTau τ : D.R.GG) = D.host.sigmaOf (D.eTau τ' : D.R.GG) := by
    ext x
    have := DFunLike.congr_fun h x
    exact D.host.φ₀.injective this
  exact (D.host.gal).symm.injective h1

/- English proof (translation)
Establish `h1` using `(linearIndependent_monoidHom D.host.E ℂ).comp (fun τ => (embT D τ : D.host.E →* ℂ)) (fun τ τ' h => embT_injective (RingHom.coe_monoidHom_injective h))`. Use `Fintype.linearIndependent_iff.1 h1 c ?_ τ` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify `h x` using `[Finset.sum_apply, mul_comm]`.
-/
theorem indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, embT D τ x * c τ = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp (fun τ => (embT D τ : D.host.E →* ℂ))
    (fun τ τ' h => embT_injective (RingHom.coe_monoidHom_injective h))
  refine Fintype.linearIndependent_iff.1 h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply, mul_comm] using h x

/- English proof (translation)
Establish `h1 : ∀ τ i j, f (coordV D (τ, i, j)) = 0`. Introduce `τ i j`. Use `indep (fun τ => f (coordV D (τ, i, j))) (fun x => ?_) τ` and prove the remaining obligations. Rewrite using `[← h (Matrix.single i j x)]`. Establish `: embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • coordV D (τ, i, j)`.

Use function extensionality and compare the values at `τ' i' j'`. Simplify using `only [embV, tor0, coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.single_apply]`. Distinguish the cases in `hi : i = i' ∧ j = j'`. Take `⟨rfl, rfl⟩` from `hi`. Simplify using the standard rewrite rules.

Establish `: ¬ (i' = i ∧ j' = j)` using `fun h => hi ⟨h.1.symm, h.2.symm⟩`. Simplify using `[hi, this]`. Rewrite using `[this, map_sum]`. Simplify using the standard rewrite rules. Establish `h2 : z = ∑ τ, ∑ i, ∑ j, z τ i j • coordV D (τ, i, j)`.

Use function extensionality and compare the values at `τ' i' j'`. Simplify using `[coordV, Finset.sum_apply, ite_and]`. Rewrite using `[h2]`. Simplify using `[map_sum, h1]`.
-/
theorem lin_eq_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (f : VC D N N' →ₗ[ℂ] ℂ)
    (h : ∀ y, f (embV D (tor0 D cc δ) y) = 0) (z : VC D N N') : f z = 0 := by
  have h1 : ∀ τ i j, f (coordV D (τ, i, j)) = 0 := by
    intro τ i j
    refine indep (fun τ => f (coordV D (τ, i, j))) (fun x => ?_) τ
    rw [← h (Matrix.single i j x)]
    have : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • coordV D (τ, i, j) := by
      funext τ' i' j'
      simp only [embV, tor0, coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.single_apply]
      by_cases hi : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hi
        simp
      · have : ¬ (i' = i ∧ j' = j) := fun h => hi ⟨h.1.symm, h.2.symm⟩
        simp [hi, this]
    rw [this, map_sum]
    simp
  have h2 : z = ∑ τ, ∑ i, ∑ j, z τ i j • coordV D (τ, i, j) := by
    funext τ' i' j'
    simp [coordV, Finset.sum_apply, ite_and]
  rw [h2]
  simp [map_sum, h1]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.
-/
theorem embV_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (x + y) = embV D (tor0 D cc δ) x + embV D (tor0 D cc δ) y := by
  funext τ i j
  simp [embV, tor0]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Establish `: (a • y) i j = (a : D.host.E) * y i j` using `rfl`. Simplify using `only [embV, tor0, this, map_mul, h.1 τ a, Pi.smul_apply, smul_eq_mul]`.
-/
theorem embV_smul (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (a : D.host.K)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • y) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) y := by
  funext τ i j
  have : (a • y) i j = (a : D.host.E) * y i j := rfl
  simp only [embV, tor0, this, map_mul, h.1 τ a, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Introduce `D h cc δ N N' r b hb`. Establish `h2 : ∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0`. Introduce `j k`. Rewrite using `[coord_emb h, hb.1 k j]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hc : ∀ (c : Fin r → ℂ) j, coordB D (tor0 D cc δ) b j (∑ k, c k • embV D (tor0 D cc δ) (b k)) = c j`. Introduce `c j`. Simplify using `[coord_sum, coord_smul, h2]`. Set `P : VC D N N' →ₗ[ℂ] VC D N N'` to `∑ k, (coordL (tor0 D cc δ) b k).smulRight (embV D (tor0 D cc δ) (b k))`. Establish `hP : ∀ z, P z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)`.

Introduce `z`. Simplify using `only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]`. Both sides reduce to the same expression. Establish `hE : ∀ y, P (embV D (tor0 D cc δ) y) = embV D (tor0 D cc δ) y`. Introduce `y`.

Establish `hy : y ∈ Submodule.span D.host.K (Set.range b)` using `hb.2 ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Rewrite using `[hP]`.

Simplify using `[h2]`. Consider the case `zero`. Establish `: embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0`. Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.

Rewrite using `[this, map_zero]`. Consider the case `add x y _ _ hx hy => rw [embV_add, map_add, hx, hy]`. Consider the case `smul a x _ hx => rw [embV_smul h, map_smul, hx]`. Establish `h1 : ∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)`. Introduce `z`.

Rewrite using `[← hP]`. Use function extensionality and compare the values at `τ i j`. Set `e : VC D N N' →ₗ[ℂ] ℂ` to `{ toFun := fun z => z τ i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Use `lin_eq_zero cc δ (e ∘ₗ (LinearMap.id - P)) (fun y => by` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, hE, LinearMap.id_apply, sub_self, map_zero]) z`.

Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at this`. Conclude with `sub_eq_zero.1 this`. Use `⟨h1, h2, fun z w => ?_, fun x => ⟨fun hx k => ?_, fun hx => ?_⟩, fun z w hzw => ?_, fun c => ?_⟩` and prove the remaining obligations. Establish `hw : ∀ τ i j, w τ i j = ∑ k, coordB D (tor0 D cc δ) b k w * (tor0 D cc δ).emb τ (b k i j)`. Introduce `τ i j`.

Use `congrFun (congrFun (congrFun (h1 w) τ) i) j` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, embV]`. Take `⟨c, hcw⟩ : ∃ c : Fin r → ℂ, ∀ k, coordB D (tor0 D cc δ) b k w = c k` from `⟨_, fun _ => rfl⟩`. Simplify using `only [hcw] at hw ⊢`. Simplify using `only [hw, map_sum, map_mul, Finset.mul_sum, coordB, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations. Proceed by induction on `hx using AddSubgroup.closure_induction generalizing k with`. Consider the case `mem x hx`. Take `⟨w, hw, j, rfl⟩` from `hx`. Rewrite using `[coord_smul, h2]`.

Use `split_ifs`. Rewrite using `[mul_one]`. Conclude with `hw`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.

Consider the case `zero`. Establish `: coordB D (tor0 D cc δ) b k 0 = 0` using `map_zero (coordL (tor0 D cc δ) b k)`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [coord_add]`.

Conclude with `add_mem (hx k) (hy k)`. Consider the case `neg x _ hx`. Establish `: coordB D (tor0 D cc δ) b k (-x) = - coordB D (tor0 D cc δ) b k x` using `map_neg (coordL (tor0 D cc δ) b k) x`. Rewrite using `[this]`. Conclude with `neg_mem (hx k)`.

Rewrite using `[h1 x]`. Conclude with `sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, hx k, k, rfl⟩`. Rewrite using `[h1 z, h1 w]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [show coordB D (tor0 D cc δ) b k z = coordB D (tor0 D cc δ) b k w from congrFun hzw k]`. Conclude with `⟨_, funext (hc c)⟩`.
-/
theorem coords_of_orthonormal_basis : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)) ∧ (∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0) ∧ (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D (tor0 D cc δ) b k z * (starRingEnd ℂ) (coordB D (tor0 D cc δ) b k w)) ∧ (∀ x : VC D N N', x ∈ LaB D (tor0 D cc δ) b ↔ ∀ k, coordB D (tor0 D cc δ) b k x ∈ (lamOf D cc δ)) ∧ Function.Bijective (fun (z : VC D N N') (k : Fin r) => coordB D (tor0 D cc δ) b k z) := by
  intro D h cc δ N N' r b hb
  have h2 : ∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0 := by
    intro j k
    rw [coord_emb h, hb.1 k j]
    split_ifs <;> simp
  have hc : ∀ (c : Fin r → ℂ) j,
      coordB D (tor0 D cc δ) b j (∑ k, c k • embV D (tor0 D cc δ) (b k)) = c j := by
    intro c j
    simp [coord_sum, coord_smul, h2]
  let P : VC D N N' →ₗ[ℂ] VC D N N' :=
    ∑ k, (coordL (tor0 D cc δ) b k).smulRight (embV D (tor0 D cc δ) (b k))
  have hP : ∀ z, P z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  have hE : ∀ y, P (embV D (tor0 D cc δ) y) = embV D (tor0 D cc δ) y := by
    intro y
    have hy : y ∈ Submodule.span D.host.K (Set.range b) := hb.2 ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [hP]
      simp [h2]
    | zero =>
      have : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
        funext τ i j
        simp [embV, tor0]
      rw [this, map_zero]
    | add x y _ _ hx hy => rw [embV_add, map_add, hx, hy]
    | smul a x _ hx => rw [embV_smul h, map_smul, hx]
  have h1 : ∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    rw [← hP]
    funext τ i j
    let e : VC D N N' →ₗ[ℂ] ℂ :=
      { toFun := fun z => z τ i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have := lin_eq_zero cc δ (e ∘ₗ (LinearMap.id - P)) (fun y => by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, hE, LinearMap.id_apply, sub_self, map_zero]) z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at this
    exact sub_eq_zero.1 this
  refine ⟨h1, h2, fun z w => ?_, fun x => ⟨fun hx k => ?_, fun hx => ?_⟩, fun z w hzw => ?_, fun c => ?_⟩
  · have hw : ∀ τ i j, w τ i j = ∑ k, coordB D (tor0 D cc δ) b k w * (tor0 D cc δ).emb τ (b k i j) := by
      intro τ i j
      have := congrFun (congrFun (congrFun (h1 w) τ) i) j
      simpa [Finset.sum_apply, embV] using this
    obtain ⟨c, hcw⟩ : ∃ c : Fin r → ℂ, ∀ k, coordB D (tor0 D cc δ) b k w = c k := ⟨_, fun _ => rfl⟩
    simp only [hcw] at hw ⊢
    simp only [hw, map_sum, map_mul, Finset.mul_sum, coordB, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · induction hx using AddSubgroup.closure_induction generalizing k with
    | mem x hx =>
      obtain ⟨w, hw, j, rfl⟩ := hx
      rw [coord_smul, h2]
      split_ifs
      · rw [mul_one]; exact hw
      · rw [mul_zero]; exact zero_mem _
    | zero =>
      have : coordB D (tor0 D cc δ) b k 0 = 0 := map_zero (coordL (tor0 D cc δ) b k)
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy => rw [coord_add]; exact add_mem (hx k) (hy k)
    | neg x _ hx =>
      have : coordB D (tor0 D cc δ) b k (-x) = - coordB D (tor0 D cc δ) b k x :=
        map_neg (coordL (tor0 D cc δ) b k) x
      rw [this]; exact neg_mem (hx k)
  · rw [h1 x]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, hx k, k, rfl⟩
  · rw [h1 z, h1 w]
    exact Finset.sum_congr rfl fun k _ => by rw [show coordB D (tor0 D cc δ) b k z = coordB D (tor0 D cc δ) b k w from congrFun hzw k]
  · exact ⟨_, funext (hc c)⟩

end GlobalTheory.OnCoord
