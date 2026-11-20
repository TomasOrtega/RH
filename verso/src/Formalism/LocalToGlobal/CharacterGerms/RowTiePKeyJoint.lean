import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJointDef

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

section Eig

variable {C : Type} [Field C] [CharZero C] {n : ℕ}

/- English proof (translation)
Use `set x := Matrix.mulVec t u - μ • u with hxdef`. Establish `htu : Matrix.mulVec t u = μ • u + x` using `by rw [hxdef]; abel`. Establish `hx : ∀ k : ℕ, Matrix.mulVec (t ^ k) x = μ ^ k • x`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ' t k, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h2, smul_smul, ← pow_succ]`. Establish `hu : ∀ k : ℕ, Matrix.mulVec (t ^ (k + 1)) u = μ ^ (k + 1) • u + (((k : C) + 1) * μ ^ k) • x`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp [htu]`. Consider the case `succ k ih`. Rewrite using `[pow_succ' t (k + 1), ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, htu, h2]`. Use `push_cast`.

Use `module`. Take `⟨r, rfl⟩ : ∃ r, q = r + 2` from `⟨q - 2, by omega⟩`. Establish `hA` using `hu (r + 1)`. Rewrite `hA` using `[show r + 1 + 1 = r + 2 from rfl, ht, htu]`. Establish `hB` using `hx (r + 2)`.

Rewrite `hB` using `[ht, h2]`. It suffices to establish `hx0 : x = 0 by rw [htu, hx0, add_zero]`. Distinguish the cases in `hμ : μ = 0`. Substitute `hμ` using the available equality. Simplify using `at hA`.

Conclude with `hA`. Establish `hB' : (μ ^ (r + 2) - μ) • x = 0` using `by rw [sub_smul, ← hB, sub_self]`. Break down `smul_eq_zero.mp hB' with h | h` into its components or cases. Establish `h1 : μ ^ (r + 1) = 1`. Establish `e1 : μ ^ (r + 1) * μ = 1 * μ`.

Rewrite using `[← pow_succ, one_mul]`. Conclude with `sub_eq_zero.mp h`. Conclude with `mul_right_cancel₀ hμ e1`. Rewrite `hA` using `[sub_eq_zero.mp h, h1, mul_one]`. Establish `hA2` using `add_left_cancel hA`.

Establish `e : (((r + 1 : ℕ) : C) + 1) • x = ((r : C) + 1) • x + x`. Use `push_cast`. Rewrite using `[add_smul, one_smul]`. Rewrite `hA2` using `[e]`. Establish `h3 : ((r : C) + 1) • x = 0` using `add_eq_right.mp hA2.symm`.

Conclude with `(smul_eq_zero.mp h3).resolve_left (Nat.cast_add_one_ne_zero r)`. Conclude with `h`.
-/
theorem sq_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (u : Fin n → C)
    (h2 : Matrix.mulVec t (Matrix.mulVec t u - μ • u) = μ • (Matrix.mulVec t u - μ • u)) :
    Matrix.mulVec t u = μ • u := by
  set x := Matrix.mulVec t u - μ • u with hxdef
  have htu : Matrix.mulVec t u = μ • u + x := by rw [hxdef]; abel
  have hx : ∀ k : ℕ, Matrix.mulVec (t ^ k) x = μ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' t k, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h2, smul_smul, ← pow_succ]
  have hu : ∀ k : ℕ, Matrix.mulVec (t ^ (k + 1)) u = μ ^ (k + 1) • u + (((k : C) + 1) * μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp [htu]
    | succ k ih =>
      rw [pow_succ' t (k + 1), ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, htu, h2]
      push_cast
      module
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hA := hu (r + 1)
  rw [show r + 1 + 1 = r + 2 from rfl, ht, htu] at hA
  have hB := hx (r + 2)
  rw [ht, h2] at hB
  suffices hx0 : x = 0 by rw [htu, hx0, add_zero]
  by_cases hμ : μ = 0
  · subst hμ
    simp at hA
    exact hA
  · have hB' : (μ ^ (r + 2) - μ) • x = 0 := by rw [sub_smul, ← hB, sub_self]
    rcases smul_eq_zero.mp hB' with h | h
    · have h1 : μ ^ (r + 1) = 1 := by
        have e1 : μ ^ (r + 1) * μ = 1 * μ := by
          rw [← pow_succ, one_mul]
          exact sub_eq_zero.mp h
        exact mul_right_cancel₀ hμ e1
      rw [sub_eq_zero.mp h, h1, mul_one] at hA
      have hA2 := add_left_cancel hA
      have e : (((r + 1 : ℕ) : C) + 1) • x = ((r : C) + 1) • x + x := by
        push_cast
        rw [add_smul, one_smul]
      rw [e] at hA2
      have h3 : ((r : C) + 1) • x = 0 := add_eq_right.mp hA2.symm
      exact (smul_eq_zero.mp h3).resolve_left (Nat.cast_add_one_ne_zero r)
    · exact h

/- English proof (translation)
Rewrite `hw` using `[Module.End.mem_maxGenEigenspace]`. Take `⟨k, hk⟩` from `hw`. Proceed by induction on `k generalizing w with`. Consider the case `zero`. Simplify using `only [pow_zero, Module.End.one_apply] at hk`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Rewrite `hk` using `[pow_succ, Module.End.mul_apply]`. Establish `hy` using `ih _ hk`.

Establish `e : (Matrix.toLin' t - μ • (1 : Module.End C (Fin n → C))) w = Matrix.mulVec t w - μ • w`. Simplify using `[Matrix.toLin'_apply]`. Rewrite `hy` using `[e]`. Conclude with `sq_to_eig hq t ht μ w hy`.
-/
theorem gen_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (w : Fin n → C)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' t : Module.End C (Fin n → C)) μ) : Matrix.mulVec t w = μ • w := by
  rw [Module.End.mem_maxGenEigenspace] at hw
  obtain ⟨k, hk⟩ := hw
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hk
    subst hk
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hk
    have hy := ih _ hk
    have e : (Matrix.toLin' t - μ • (1 : Module.End C (Fin n → C))) w = Matrix.mulVec t w - μ • w := by
      simp [Matrix.toLin'_apply]
    rw [e] at hy
    exact sq_to_eig hq t ht μ w hy

end Eig

/- English proof (translation)
Introduce `C _ _ hC n q hq T hT hcomm v`. Set `f : T → Module.End C (Fin n → C)` to `fun t => Matrix.toLin' t.1`. Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f (fun i j _ => by show (Matrix.toLin' i.1).comp (Matrix.toLin' j.1) = (Matrix.toLin' j.1).comp (Matrix.toLin' i.1)`. Rewrite using `[← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm i.1 i.2 j.1 j.2])`. Use the proof step `(fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))`.

Establish `hv : v ∈ ⨆ χ : T → C, ⨅ i, (f i).maxGenEigenspace (χ i)`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Use `Submodule.iSup_induction _ (motive := fun v => ∃ (m : ℕ) (w : Fin m → Fin n → C), v = ∑ j, w j ∧ ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j) hv ?_ ?_ ?_` and prove the remaining obligations. Introduce `χ x hx`.

Use `⟨1, fun _ => x, by simp, fun _ t ht => ⟨χ ⟨t, ht⟩, gen_to_eig hq t (hT t ht) _ x ?_⟩⟩` and prove the remaining obligations. Conclude with `(Submodule.mem_iInf _).mp hx ⟨t, ht⟩`. Conclude with `⟨0, Fin.elim0, by simp, fun j => Fin.elim0 j⟩`. Introduce and unpack `x y ⟨m₁, w₁, rfl, h₁⟩ ⟨m₂, w₂, rfl, h₂⟩`. Use `⟨m₁ + m₂, Fin.append w₁ w₂, by rw [Fin.sum_univ_add]; simp, fun j => ?_⟩` and prove the remaining obligations.

Use `Fin.addCases (fun j => ?_) (fun j => ?_) j` and prove the remaining obligations. Simplify using `using h₁ j`. Simplify using `using h₂ j`.
-/
theorem jointEig_holds : JointEigSt := by
  intro C _ _ hC n q hq T hT hcomm v
  let f : T → Module.End C (Fin n → C) := fun t => Matrix.toLin' t.1
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => by
      show (Matrix.toLin' i.1).comp (Matrix.toLin' j.1) = (Matrix.toLin' j.1).comp (Matrix.toLin' i.1)
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm i.1 i.2 j.1 j.2])
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hv : v ∈ ⨆ χ : T → C, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun v => ∃ (m : ℕ) (w : Fin m → Fin n → C),
    v = ∑ j, w j ∧ ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j) hv ?_ ?_ ?_
  · intro χ x hx
    refine ⟨1, fun _ => x, by simp, fun _ t ht => ⟨χ ⟨t, ht⟩, gen_to_eig hq t (hT t ht) _ x ?_⟩⟩
    exact (Submodule.mem_iInf _).mp hx ⟨t, ht⟩
  · exact ⟨0, Fin.elim0, by simp, fun j => Fin.elim0 j⟩
  · rintro x y ⟨m₁, w₁, rfl, h₁⟩ ⟨m₂, w₂, rfl, h₂⟩
    refine ⟨m₁ + m₂, Fin.append w₁ w₂, by rw [Fin.sum_univ_add]; simp, fun j => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using h₁ j
    · simpa using h₂ j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
