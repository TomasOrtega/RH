import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU hn g`. Use `set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef`. Use `set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hBdef`. Establish `hAB : A * B = 1` using `(g : GL (Fin n) L).mul_inv`. Establish `hBA : B * A = 1` using `(g : GL (Fin n) L).inv_mul`.

Establish `hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n` using `g.2`. Establish `key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1`. Introduce `i j`. Take `rfl | rfl : n = 0 ∨ n = 1` from `by omega`. Conclude with `i.elim0`.

Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Establish `h1 : σ (A 0 0) * A 0 0 = 1`. Simplify `congrFun (congrFun hherm 0) 0` using `[Matrix.mul_apply, antiJ]`. Establish `h2 : B 0 0 * A 0 0 = 1`.

Simplify `congrFun (congrFun hBA 0) 0` using `[Matrix.mul_apply]`. Establish `hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1`. Use `congrArg Valued.v h1` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hU.2.1]`. Then use the resulting hypothesis. Establish `hle : Valued.v (A 0 0) ≤ 1`.

Assume the negation of the conclusion as `hlt`. Establish `hgt : 1 < Valued.v (A 0 0)` using `not_le.1 hlt`. Establish `: Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0)` using `by gcongr`. Rewrite `this` using `[mul_one, hsq]`. Conclude with `hlt this`.

Establish `hA1 : Valued.v (A 0 0) = 1`. Use `le_antisymm hle ?_` and prove the remaining obligations. Establish `: Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1` using `by gcongr`. Rewrite `this` using `[mul_one, hsq]`. Then use the resulting hypothesis. Use `⟨hA1, ?_⟩` and prove the remaining obligations.

Use `congrArg Valued.v h2` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hA1, mul_one]`. Then use the resulting hypothesis. Establish `hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L` using `fun x hx => by`. Unfold `intL`. Conclude with `(Valuation.mem_integer_iff _ _).2 hx.le`.

Set `A' : Matrix (Fin n) (Fin n) (intL L)` to `fun i j => ⟨A i j, hint _ (key i j).1⟩`. Set `B' : Matrix (Fin n) (Fin n) (intL L)` to `fun i j => ⟨B i j, hint _ (key i j).2⟩`. Establish `hinj : Function.Injective ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L)` using `fun X Y h => by`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`.

Establish `eA : (intL L).subtype.mapMatrix A' = A` using `rfl`. Establish `eB : (intL L).subtype.mapMatrix B' = B` using `rfl`. Unfold `KU`. Rewrite using `[Subgroup.mem_subgroupOf]`. Unfold `intPts`.

Rewrite using `[Subgroup.mem_inf, MonoidHom.mem_range]`. Use `⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, eA, eB, map_one, hAB]`. Rewrite using `[map_mul, eA, eB, map_one, hBA]`. Unfold `bc`.

Conclude with `Units.ext eA`.
-/
theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
