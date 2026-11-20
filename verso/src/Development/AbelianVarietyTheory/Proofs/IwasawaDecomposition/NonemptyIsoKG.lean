import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory.FourCopiesIso

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hs j hj`. Use `congrArg (h (v j)) hs` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero, Finset.sum_eq_single j]`. Rewrite `this` using `[map_smul, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 this).resolve_right (h0 j)`. Introduce `i _ hij`. Rewrite using `[map_smul, ho i j hij, smul_zero]`. Introduce `e`. Conclude with `absurd hj e`.
-/
theorem linearIndependent_of_orthogonal {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
    (h : V → V →ₗ[K] K) (v : J → V) (h0 : ∀ i, h (v i) (v i) ≠ 0) (ho : ∀ i j, i ≠ j → h (v j) (v i) = 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hs j hj
  have := congrArg (h (v j)) hs
  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h0 j)
  · intro i _ hij
    rw [map_smul, ho i j hij, smul_zero]
  · intro e; exact absurd hj e

/- English proof (translation)
Introduce `K E _ _ _ _ _ cj σ ι _ hcard hσ hcc htr hpos`. Set `h : E → E →ₗ[K] K` to `fun y => (Algebra.trace K E) ∘ₗ LinearMap.mulRight K (cj y)`. Establish `hh : ∀ x y, h y x = Algebra.trace K E (x * cj y)` using `fun _ _ => rfl`. Establish `hne : ∀ x, x ≠ 0 → h x x ≠ 0`. Introduce `x hx e`.

Take `⟨a, ha, h1⟩` from `hpos x hx`. Rewrite `e` using `[hh, h1]`. Conclude with `ha.ne' (by exact_mod_cast e)`. Take `⟨s, hs⟩ : (⊤ : Submodule K E).FG` from `Module.Finite.fg_top`. Take `⟨n, v, h0, ho, hsp⟩` from `GlobalTheory.FourCopies.exists_orthogonal_family h (fun x y e => by`.

Rewrite `e`, the goal using `[hh]`. Use `htr (x * cj y)` as an intermediate fact. Rewrite `this` using `[e, map_zero, map_mul, hcc, mul_comm]`. Conclude with `this)`. Use the proof step `(fun x e => by`.

Assume the negation of the conclusion as `hx`. Conclude with `hne x hx e) s`. Establish `htop : ⊤ ≤ Submodule.span K (Set.range v)`. Rewrite using `[← hs]`. Conclude with `Submodule.span_le.2 (fun y hy => hsp y hy)`.

Establish `hli` using `linearIndependent_of_orthogonal h v (fun i => hne _ (h0 i)) ho`. Establish `hn : Module.finrank K E = n`. Simplify using `using Module.finrank_eq_card_basis (Module.Basis.mk hli htop)`. Set `e : ι ≃ Fin n` to `Fintype.equivFinOfCardEq (hcard.trans hn)`. Use `choose a ha hav using fun i => hpos (v i) (h0 i)`.

Use `choose A hA hA' using fun i => GlobalTheory.FourCopies.exists_similitude (a i) (ha i)`. Set `H : (Fin 4 → E) → (Fin 4 → E) →ₗ[K] K` to `fun y => ∑ k, h (y k) ∘ₗ LinearMap.proj k`. Establish `hH : ∀ x y, H y x = ∑ k, Algebra.trace K E (x k * cj (y k))`. Introduce `x y`. Simplify using `only [H, LinearMap.sum_apply]`.

Both sides reduce to the same expression. Set `b : Fin 4 × ι → (Fin 4 → E)` to `fun w k => (A (e w.2) w.1 k : E) * v (e w.2)`. Establish `hb : ∀ w w', H (b w') (b w) = if w = w' then 1 else 0`. Introduce `w w'`. Establish `h1 : H (b w') (b w) = ((∑ k, A (e w.2) w.1 k * A (e w'.2) w'.1 k : ℚ) : K) * h (v (e w'.2)) (v (e w.2))`.

Rewrite using `[hH, hh]`. Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_mul (_ * _ : K), ← map_smul, Algebra.smul_def]`.

Use `congr 1`. Simplify using `only [b, map_mul, map_ratCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Distinguish the cases in `hi : w.2 = w'.2`.

Rewrite using `[← hi, hh, hav, ← Rat.cast_mul, mul_comm, hA]`. Establish `: w.1 = w'.1 ↔ w = w'` using `⟨fun t => Prod.ext t hi, fun t => by rw [t]⟩`. Simplify using `only [this]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `: w ≠ w'` using `fun t => hi (by rw [t])`.

Rewrite using `[if_neg this, ho _ _ (fun t => hi (e.injective t)), mul_zero]`. Establish `hbl : LinearIndependent K b` using `linearIndependent_of_orthogonal H b (fun i => by rw [hb]; simp) (fun i j hij => by rw [hb, if_neg hij])`. Establish `: Nonempty ι`. Rewrite using `[← Fintype.card_pos_iff, hcard]`. Conclude with `Module.finrank_pos`.

Establish `hc : Fintype.card (Fin 4 × ι) = Module.finrank K (Fin 4 → E)`. Rewrite using `[Module.finrank_pi_fintype, Fintype.card_prod, hcard]`. Simplify using the standard rewrite rules. Set `B` to `basisOfLinearIndependentOfCardEqFinrank hbl hc`. Establish `hB : ∀ w, B w = b w` using `fun w => by simp [B]`.

Establish `hco : ∀ x w, H (b w) x = B.equivFun x w`. Introduce `x w`. Use `conv_lhs => rw [← B.sum_equivFun x]`. Simplify using `only [map_sum, map_smul, hB, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Simplify using the standard rewrite rules.

Use `⟨⟨B.equivFun, fun x y => ?_⟩⟩` and prove the remaining obligations. Establish `hy : ∀ k, cj (y k) = ∑ w, algebraMap K E (σ (B.equivFun y w)) * cj (b w k)`. Introduce `k`. Use `conv_lhs => rw [← B.sum_equivFun y]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, map_sum, hB]`.

Simplify using `only [Algebra.smul_def, map_mul, hσ]`. Simplify using `only [hσ, ← map_mul, ← map_sum]`. Use `congr 1`. Simplify using `only [hy, Finset.mul_sum, map_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← hco x w, hH, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul (σ _), ← map_smul, Algebra.smul_def]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nonempty_isoKG : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  intro K E _ _ _ _ _ cj σ ι _ hcard hσ hcc htr hpos
  classical
  let h : E → E →ₗ[K] K := fun y => (Algebra.trace K E) ∘ₗ LinearMap.mulRight K (cj y)
  have hh : ∀ x y, h y x = Algebra.trace K E (x * cj y) := fun _ _ => rfl
  have hne : ∀ x, x ≠ 0 → h x x ≠ 0 := by
    intro x hx e
    obtain ⟨a, ha, h1⟩ := hpos x hx
    rw [hh, h1] at e
    exact ha.ne' (by exact_mod_cast e)
  obtain ⟨s, hs⟩ : (⊤ : Submodule K E).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := GlobalTheory.FourCopies.exists_orthogonal_family h
    (fun x y e => by
      rw [hh] at e ⊢
      have := htr (x * cj y)
      rw [e, map_zero, map_mul, hcc, mul_comm] at this
      exact this)
    (fun x e => by
      by_contra hx
      exact hne x hx e) s
  have htop : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hs]; exact Submodule.span_le.2 (fun y hy => hsp y hy)
  have hli := linearIndependent_of_orthogonal h v (fun i => hne _ (h0 i)) ho
  have hn : Module.finrank K E = n := by
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq (hcard.trans hn)
  choose a ha hav using fun i => hpos (v i) (h0 i)
  choose A hA hA' using fun i => GlobalTheory.FourCopies.exists_similitude (a i) (ha i)
  let H : (Fin 4 → E) → (Fin 4 → E) →ₗ[K] K := fun y => ∑ k, h (y k) ∘ₗ LinearMap.proj k
  have hH : ∀ x y, H y x = ∑ k, Algebra.trace K E (x k * cj (y k)) := by
    intro x y
    simp only [H, LinearMap.sum_apply]
    rfl
  let b : Fin 4 × ι → (Fin 4 → E) := fun w k => (A (e w.2) w.1 k : E) * v (e w.2)
  have hb : ∀ w w', H (b w') (b w) = if w = w' then 1 else 0 := by
    intro w w'
    have h1 : H (b w') (b w) =
        ((∑ k, A (e w.2) w.1 k * A (e w'.2) w'.1 k : ℚ) : K) * h (v (e w'.2)) (v (e w.2)) := by
      rw [hH, hh]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← smul_eq_mul (_ * _ : K), ← map_smul, Algebra.smul_def]
      congr 1
      simp only [b, map_mul, map_ratCast]
      ring
    rw [h1]
    by_cases hi : w.2 = w'.2
    · rw [← hi, hh, hav, ← Rat.cast_mul, mul_comm, hA]
      have : w.1 = w'.1 ↔ w = w' := ⟨fun t => Prod.ext t hi, fun t => by rw [t]⟩
      simp only [this]
      split_ifs <;> simp
    · have : w ≠ w' := fun t => hi (by rw [t])
      rw [if_neg this, ho _ _ (fun t => hi (e.injective t)), mul_zero]
  have hbl : LinearIndependent K b :=
    linearIndependent_of_orthogonal H b (fun i => by rw [hb]; simp) (fun i j hij => by rw [hb, if_neg hij])
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  have hc : Fintype.card (Fin 4 × ι) = Module.finrank K (Fin 4 → E) := by
    rw [Module.finrank_pi_fintype, Fintype.card_prod, hcard]; simp
  let B := basisOfLinearIndependentOfCardEqFinrank hbl hc
  have hB : ∀ w, B w = b w := fun w => by simp [B]
  have hco : ∀ x w, H (b w) x = B.equivFun x w := by
    intro x w
    conv_lhs => rw [← B.sum_equivFun x]
    simp only [map_sum, map_smul, hB, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  refine ⟨⟨B.equivFun, fun x y => ?_⟩⟩
  have hy : ∀ k, cj (y k) = ∑ w, algebraMap K E (σ (B.equivFun y w)) * cj (b w k) := by
    intro k
    conv_lhs => rw [← B.sum_equivFun y]
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hB]
    simp only [Algebra.smul_def, map_mul, hσ]
  simp only [hσ, ← map_mul, ← map_sum]
  congr 1
  simp only [hy, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← hco x w, hH, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← smul_eq_mul (σ _), ← map_smul, Algebra.smul_def]
  congr 1
  ring

end GlobalTheory.FourCopiesIso
