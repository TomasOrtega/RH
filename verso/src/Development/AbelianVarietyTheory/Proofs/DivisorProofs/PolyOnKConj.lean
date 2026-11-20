import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv

noncomputable section

open MvPolynomial
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

def conjPoly (n : ℕ) : Poly n →+* Poly n :=
  (rename (Sum.swap : (Fin n × Fin n) ⊕ (Fin n × Fin n) → _)).toRingHom.comp (map (starRingEnd ℂ))

/- English proof (translation)
Establish `h : (ev g).comp (conjPoly n) = (starRingEnd ℂ).comp (ev g)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[conjPoly, ev]`. Introduce `i`.

Break down `i with x | x` into its components or cases. Simplify using `[conjPoly, ev]`. Simplify using `[conjPoly, ev]`. Conclude with `congrArg (fun φ : Poly n →+* ℂ => φ P) h`.
-/
theorem ev_conjPoly {n : ℕ} (g : Mat n) (P : Poly n) : ev g (conjPoly n P) = conj (ev g P) := by
  have h : (ev g).comp (conjPoly n) = (starRingEnd ℂ).comp (ev g) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjPoly, ev]
    · intro i
      rcases i with x | x
      · simp [conjPoly, ev]
      · simp [conjPoly, ev]
  exact congrArg (fun φ : Poly n →+* ℂ => φ P) h

/- English proof (translation)
Take `⟨P, hP⟩` from `hf`. Conclude with `⟨conjPoly n P, fun k hk => by dsimp only; rw [ev_conjPoly, hP k hk]⟩`.
-/
theorem polyOnK_conj {n : ℕ} {ε : Fin n → Bool} {f : Mat n → ℂ} (hf : PolyOnK ε f) :
    PolyOnK ε fun k => conj (f k) := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨conjPoly n P, fun k hk => by dsimp only; rw [ev_conjPoly, hP k hk]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, fun k _ => by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨P, hP⟩` from `hf a (Finset.mem_insert_self a s)`. Take `⟨Q, hQ⟩` from `ih fun i hi => hf i (Finset.mem_insert_of_mem hi)`.

Conclude with `⟨P + Q, fun k hk => by dsimp only at hQ ⊢; rw [Finset.sum_insert ha, map_add, hP k hk, hQ k hk]⟩`.
-/
theorem polyOnK_sum {n : ℕ} {ε : Fin n → Bool} {ι : Type} (s : Finset ι) (f : ι → Mat n → ℂ)
    (hf : ∀ i ∈ s, PolyOnK ε (f i)) : PolyOnK ε fun k => ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun k _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨P, hP⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨Q, hQ⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact ⟨P + Q, fun k hk => by dsimp only at hQ ⊢; rw [Finset.sum_insert ha, map_add, hP k hk, hQ k hk]⟩

/- English proof (translation)
Introduce `n ε W _ _ _ T hT`. Apply `polyOnK_conj` to reduce the goal to its premises. Establish `e : trK T = fun k => ∑ i, ⟪(stdOrthonormalBasis ℂ W) i, T k ((stdOrthonormalBasis ℂ W) i)⟫_ℂ`. Use function extensionality and compare the values at `k`. Simplify using `only [trK, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ W)]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `polyOnK_sum _ _ fun i _ => hT _ _`.
-/
theorem trPoly : TrPoly := by
  intro n ε W _ _ _ T hT
  apply polyOnK_conj
  have e : trK T = fun k => ∑ i, ⟪(stdOrthonormalBasis ℂ W) i, T k ((stdOrthonormalBasis ℂ W) i)⟫_ℂ := by
    funext k
    simp only [trK, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ W)]
    rfl
  rw [e]
  exact polyOnK_sum _ _ fun i _ => hT _ _

end GlobalTheory.PsCo.PcEF
