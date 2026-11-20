import Mathlib

namespace GlobalTheory.CompanionTheory.WedgeSpan

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hv : LinearIndependent Ω (Fin.cons (b i) e : Fin (n + 1) → V)` using `linearIndependent_finCons.2 ⟨he, hx⟩`. Establish `hbe' : ExteriorAlgebra.ιMulti Ω n b = t • ExteriorAlgebra.ιMulti Ω n e`. Use `congrArg Subtype.val hbe` as an intermediate fact. Simplify using `using this`.

Establish `htb : Matrix.vecTail (Fin.cons (b i) b : Fin (n + 1) → V) = b` using `by funext k; simp [Matrix.vecTail]`. Establish `hte : Matrix.vecTail (Fin.cons (b i) e : Fin (n + 1) → V) = e` using `by funext k; simp [Matrix.vecTail]`. Establish `h0 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) b : Fin (n + 1) → V) = 0` using `(ExteriorAlgebra.ιMulti Ω (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ) (by simp) (Fin.succ_ne_zero i).symm`. Rewrite `h0` using `[ExteriorAlgebra.ιMulti_succ_apply, htb, hbe', mul_smul_comm, smul_eq_zero]`. Establish `h1 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) e : Fin (n + 1) → V) = 0`.

Rewrite using `[ExteriorAlgebra.ιMulti_succ_apply, hte]`. Break down `h0 with h | h` into its components or cases. Conclude with `absurd h ht`. Simplify using `using h`. Establish `hfam` using `exteriorPower.ιMulti_family_linearIndependent_field (n := n + 1) hv`.

Apply `hfam.ne_zero (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl _))` to reduce the goal to its premises. Rewrite using `[exteriorPower.ιMulti_family, Equiv.symm_apply_apply]`. Conclude with `Subtype.ext h1`.
-/
theorem span_of_wedge_proportional (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (b e : Fin n → V) (t : Ω) (he : LinearIndependent Ω e) (ht : t ≠ 0)
    (hbe : exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e) (i : Fin n) :
    b i ∈ Submodule.span Ω (Set.range e) := by
  classical
  by_contra hx
  have hv : LinearIndependent Ω (Fin.cons (b i) e : Fin (n + 1) → V) :=
    linearIndependent_finCons.2 ⟨he, hx⟩
  have hbe' : ExteriorAlgebra.ιMulti Ω n b = t • ExteriorAlgebra.ιMulti Ω n e := by
    have := congrArg Subtype.val hbe
    simpa using this
  have htb : Matrix.vecTail (Fin.cons (b i) b : Fin (n + 1) → V) = b :=
    by funext k; simp [Matrix.vecTail]
  have hte : Matrix.vecTail (Fin.cons (b i) e : Fin (n + 1) → V) = e :=
    by funext k; simp [Matrix.vecTail]
  have h0 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) b : Fin (n + 1) → V) = 0 :=
    (ExteriorAlgebra.ιMulti Ω (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
      (by simp) (Fin.succ_ne_zero i).symm
  rw [ExteriorAlgebra.ιMulti_succ_apply, htb, hbe', mul_smul_comm, smul_eq_zero] at h0
  have h1 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) e : Fin (n + 1) → V) = 0 := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, hte]
    rcases h0 with h | h
    · exact absurd h ht
    · simpa using h
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n + 1) hv
  apply hfam.ne_zero (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl _))
  rw [exteriorPower.ιMulti_family, Equiv.symm_apply_apply]
  exact Subtype.ext h1

end GlobalTheory.CompanionTheory.WedgeSpan
