import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Introduce `A R _ _ _ J u v b c hreg hbc hu hv l`. Establish `hl : ∀ x ∈ J.map (algebraMap A R), ∀ r : R, l (r * x) ∈ J`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, hj, rfl⟩` from `hx`. Introduce `r`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Conclude with `J.mul_mem_right _ hj`. Consider the case `zero => intro r`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro r`. Rewrite using `[mul_add, map_add]`. Conclude with `J.add_mem (hx r) (hy r)`. Consider the case `smul s x _ hx => intro r`.

Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx _`. Establish `key : ∀ (y y' : A) (β γ β' γ' : R), β ∈ b → γ ∈ c → β' ∈ b → γ' ∈ c → algebraMap A R y = β + γ → algebraMap A R y' = β' + γ' → y' * l β - y * l β' ∈ J`. Introduce `y y' β γ β' γ' hβ hγ hβ' hγ' hy hy'`. Establish `h1 : algebraMap A R y' * β - algebraMap A R y * β' ∈ J.map (algebraMap A R)`.

Apply `hbc` to reduce the goal to its premises. Establish `e : algebraMap A R y' * β - algebraMap A R y * β' = β * γ' - β' * γ`. Rewrite using `[hy, hy']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_mul hβ hγ') (Ideal.mul_mem_mul hβ' hγ)`. Establish `h2` using `hl _ h1 1`. Rewrite `h2` using `[one_mul, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Then use the resulting hypothesis. Take `⟨βu, hβu, γu, hγu, hu'⟩` from `Submodule.mem_sup.mp hu`. Take `⟨βv, hβv, γv, hγv, hv'⟩` from `Submodule.mem_sup.mp hv`.

Establish `k` using `key u v βu γu βv γv hβu hγu hβv hγv hu'.symm hv'.symm`. Establish `hm : v * l βu ∈ J ⊔ Ideal.span {u}`. Establish `e : v * l βu = (v * l βu - u * l βv) + u * l βv` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left k) (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨l βv, mul_comm _ _⟩))`.

Take `⟨j, hj, s, hs, hjs⟩` from `Submodule.mem_sup.mp (hreg.2 _ hm)`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hs`. Use `⟨a, fun y β γ hβ hγ hy => hreg.1 _ ?_⟩` and prove the remaining obligations. Establish `k2` using `key y u β γ βu γu hβ hγ hβu hγu hy hu'.symm`. Establish `e : u * (l β - y * a) = (u * l β - y * l βu) + y * j`.

Rewrite using `[← hjs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.add_mem k2 (J.mul_mem_left _ hj)`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.level :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (J : Ideal A) (u v : A) (b c : Ideal R), Reg2 J u v → b * c ≤ J.map (algebraMap A R) →
      algebraMap A R u ∈ b ⊔ c → algebraMap A R v ∈ b ⊔ c → ∀ l : Module.Dual A R,
        ∃ a : A, ∀ (y : A) (β γ : R), β ∈ b → γ ∈ c → algebraMap A R y = β + γ → l β - y * a ∈ J := by
  intro A R _ _ _ J u v b c hreg hbc hu hv l
  have hl : ∀ x ∈ J.map (algebraMap A R), ∀ r : R, l (r * x) ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact J.mul_mem_right _ hj
    | zero => intro r; simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add]; exact J.add_mem (hx r) (hy r)
    | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have key : ∀ (y y' : A) (β γ β' γ' : R), β ∈ b → γ ∈ c → β' ∈ b → γ' ∈ c →
      algebraMap A R y = β + γ → algebraMap A R y' = β' + γ' → y' * l β - y * l β' ∈ J := by
    intro y y' β γ β' γ' hβ hγ hβ' hγ' hy hy'
    have h1 : algebraMap A R y' * β - algebraMap A R y * β' ∈ J.map (algebraMap A R) := by
      apply hbc
      have e : algebraMap A R y' * β - algebraMap A R y * β' = β * γ' - β' * γ := by
        rw [hy, hy']; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_mul hβ hγ') (Ideal.mul_mem_mul hβ' hγ)
    have h2 := hl _ h1 1
    rwa [one_mul, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h2
  obtain ⟨βu, hβu, γu, hγu, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨βv, hβv, γv, hγv, hv'⟩ := Submodule.mem_sup.mp hv
  have k := key u v βu γu βv γv hβu hγu hβv hγv hu'.symm hv'.symm
  have hm : v * l βu ∈ J ⊔ Ideal.span {u} := by
    have e : v * l βu = (v * l βu - u * l βv) + u * l βv := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left k)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨l βv, mul_comm _ _⟩))
  obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp (hreg.2 _ hm)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨a, fun y β γ hβ hγ hy => hreg.1 _ ?_⟩
  have k2 := key y u β γ βu γu hβ hγ hβu hγu hy hu'.symm
  have e : u * (l β - y * a) = (u * l β - y * l βu) + y * j := by
    rw [← hjs]; ring
  rw [e]
  exact J.add_mem k2 (J.mul_mem_left _ hj)
