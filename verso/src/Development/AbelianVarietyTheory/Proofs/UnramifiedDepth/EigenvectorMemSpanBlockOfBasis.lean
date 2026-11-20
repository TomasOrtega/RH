import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `K C _ _ ι O A _ n d M em u hem hM hb a z hz`. Set `U : Matrix (Σ a : A, Fin (n a)) (Fin d) K` to `Matrix.of u`. Set `W : Matrix (Fin d) (Σ a : A, Fin (n a)) K` to `Matrix.of fun t => (hb (Pi.single t 1)).exists.choose`. Establish `hWU : W * U = 1`. Use extensionality with `t s`.

Use `(hb (Pi.single t 1)).exists.choose_spec s` as an intermediate fact. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [W, U, Matrix.of_apply]`. Rewrite using `[this, Pi.single_apply]`. Simplify using `[eq_comm]`.

Establish `hUW : U * W = 1`. Establish `h1 : U * W * U = U` using `by rw [Matrix.mul_assoc, hWU, Matrix.mul_one]`. Establish `h2 : (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) * U = U` using `Matrix.one_mul _`. Use extensionality with `q q'`. Use `(hb (u q)).unique (y₁ := (U * W) q) (y₂ := (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) q) (fun s => by` as an intermediate fact.

Use `congrFun (congrFun h1 q) s` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Conclude with `this)`. Use the proof step `(fun s => by`. Use `congrFun (congrFun h2 q) s` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply]`. Conclude with `this)`. Conclude with `congrFun this q'`. Establish `hWU' : W.map ι * U.map ι = 1`. Rewrite using `[← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero ι) (map_one ι)]`.

Establish `hUW' : U.map ι * W.map ι = 1`. Rewrite using `[← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero ι) (map_one ι)]`. Establish `hvm : ∀ c : (Σ a : A, Fin (n a)) → C, Matrix.vecMul c (U.map ι) = ∑ q, c q • fun s => ι (u q s)`. Introduce `c`. Use function extensionality and compare the values at `s`.

Simplify using `[Matrix.vecMul, dotProduct, U, Finset.sum_apply]`. Establish `hind : ∀ c : (Σ a : A, Fin (n a)) → C, (∑ q, c q • fun s => ι (u q s)) = 0 → c = 0`. Introduce `c hc`. Rewrite `hc` using `[← hvm]`. Establish `: Matrix.vecMul (Matrix.vecMul c (U.map ι)) (W.map ι) = c`.

Rewrite using `[Matrix.vecMul_vecMul, hUW', Matrix.vecMul_one]`. Rewrite using `[← this, hc, Matrix.zero_vecMul]`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : (Σ a : A, Fin (n a)) → C, z = ∑ q, c q • fun s => ι (u q s) := by`. Use `⟨Matrix.vecMul z (W.map ι), ?_⟩` and prove the remaining obligations. Rewrite using `[← hvm, Matrix.vecMul_vecMul, hWU', Matrix.vecMul_one]`.

Establish `hzero : ∀ q : (Σ a : A, Fin (n a)), q.1 ≠ a → c q = 0`. Introduce `q hq`. Assume the negation of the conclusion as `hcq`. Apply `hq` to reduce the goal to its premises. Apply `hem` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Establish `h` using `hz x`. Establish `h3 : (∑ q : (Σ a : A, Fin (n a)), ((em q.1 x - em a x) * c q) • fun s => ι (u q s)) = 0`. Establish `e1 : (M x).mulVec z = ∑ q : (Σ a : A, Fin (n a)), (em q.1 x * c q) • fun s => ι (u q s)`. Rewrite using `[hc, Matrix.mulVec_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, hM, smul_smul, mul_comm]`. Establish `e2 : em a x • z = ∑ q : (Σ a : A, Fin (n a)), (em a x * c q) • fun s => ι (u q s)`. Rewrite using `[hc, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Simplify using `only [sub_mul, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← e1, ← e2, h, sub_self]`. Establish `h4` using `congrFun (hind _ h3) q`. Simplify using `only [Pi.zero_apply, mul_eq_zero] at h4`.

Conclude with `sub_eq_zero.mp (h4.resolve_right hcq)`. Use `⟨fun i => c ⟨a, i⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Fintype.sum_sigma, Finset.sum_eq_single a]`. Introduce `a' _ ha'`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hzero ⟨a', i⟩ ha', zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem eigenvector_mem_span_block_of_basis : ∀ (K C : Type) [Field K] [Field C] (ι : K →+* C) (O A : Type) [Fintype A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → K), Function.Injective em → (∀ x q, (M x).mulVec (fun s => ι (u q s)) = em q.1 x • fun s => ι (u q s)) → (∀ z : Fin d → K, ∃! b : (Σ a : A, Fin (n a)) → K, ∀ s, ∑ q, b q * u q s = z s) → ∀ (a : A) (z : Fin d → C), (∀ x, (M x).mulVec z = em a x • z) → ∃ b : Fin (n a) → C, z = ∑ i, b i • fun s => ι (u ⟨a, i⟩ s) := by
  intro K C _ _ ι O A _ n d M em u hem hM hb a z hz
  classical
  let U : Matrix (Σ a : A, Fin (n a)) (Fin d) K := Matrix.of u
  let W : Matrix (Fin d) (Σ a : A, Fin (n a)) K :=
    Matrix.of fun t => (hb (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hb (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := by
    have h1 : U * W * U = U := by rw [Matrix.mul_assoc, hWU, Matrix.mul_one]
    have h2 : (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) * U = U := Matrix.one_mul _
    ext q q'
    have := (hb (u q)).unique (y₁ := (U * W) q)
      (y₂ := (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) q)
      (fun s => by
        have := congrFun (congrFun h1 q) s
        rw [Matrix.mul_apply] at this
        exact this)
      (fun s => by
        have := congrFun (congrFun h2 q) s
        rw [Matrix.mul_apply] at this
        exact this)
    exact congrFun this q'
  have hWU' : W.map ι * U.map ι = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hUW' : U.map ι * W.map ι = 1 := by
    rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hvm : ∀ c : (Σ a : A, Fin (n a)) → C,
      Matrix.vecMul c (U.map ι) = ∑ q, c q • fun s => ι (u q s) := by
    intro c
    funext s
    simp [Matrix.vecMul, dotProduct, U, Finset.sum_apply]
  have hind : ∀ c : (Σ a : A, Fin (n a)) → C,
      (∑ q, c q • fun s => ι (u q s)) = 0 → c = 0 := by
    intro c hc
    rw [← hvm] at hc
    have : Matrix.vecMul (Matrix.vecMul c (U.map ι)) (W.map ι) = c := by
      rw [Matrix.vecMul_vecMul, hUW', Matrix.vecMul_one]
    rw [← this, hc, Matrix.zero_vecMul]
  obtain ⟨c, hc⟩ : ∃ c : (Σ a : A, Fin (n a)) → C, z = ∑ q, c q • fun s => ι (u q s) := by
    refine ⟨Matrix.vecMul z (W.map ι), ?_⟩
    rw [← hvm, Matrix.vecMul_vecMul, hWU', Matrix.vecMul_one]
  have hzero : ∀ q : (Σ a : A, Fin (n a)), q.1 ≠ a → c q = 0 := by
    intro q hq
    by_contra hcq
    apply hq
    apply hem
    funext x
    have h := hz x
    have h3 : (∑ q : (Σ a : A, Fin (n a)), ((em q.1 x - em a x) * c q) • fun s => ι (u q s)) = 0 := by
      have e1 : (M x).mulVec z
          = ∑ q : (Σ a : A, Fin (n a)), (em q.1 x * c q) • fun s => ι (u q s) := by
        rw [hc, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Matrix.mulVec_smul, hM, smul_smul, mul_comm]
      have e2 : em a x • z
          = ∑ q : (Σ a : A, Fin (n a)), (em a x * c q) • fun s => ι (u q s) := by
        rw [hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul]
      simp only [sub_mul, sub_smul, Finset.sum_sub_distrib]
      rw [← e1, ← e2, h, sub_self]
    have h4 := congrFun (hind _ h3) q
    simp only [Pi.zero_apply, mul_eq_zero] at h4
    exact sub_eq_zero.mp (h4.resolve_right hcq)
  refine ⟨fun i => c ⟨a, i⟩, ?_⟩
  rw [hc, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hzero ⟨a', i⟩ ha', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory
