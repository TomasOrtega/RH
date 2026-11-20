import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open PositivityTheory.PfSWUS.Loc

/- English proof (translation)
Use `choose s hs using ha`. Set `e : A → R ⧸ lev ϖ 1` to `fun y => Ideal.Quotient.mk (lev ϖ 1) (φ (s y))`. Establish `hinj : Function.Injective e`. Introduce `y y' h`. Establish `h'` using `Ideal.Quotient.eq.mp h`.

Rewrite using `[← hs y, ← hs y']`. Conclude with `(hker _ _).mpr h'`. Establish `himg : e '' {y | PA y} = Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x}`. Use extensionality with `c`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨φ (s y), ?_, rfl⟩` and prove the remaining obligations. Establish `hy' : PA (a (s y))`. Rewrite using `[hs y]`. Conclude with `hy`.

Conclude with `(hP _).mp hy'`. Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨w, rfl⟩` from `hφ x`. Use `⟨a w, (hP w).mpr hx, ?_⟩` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq.mpr ((hker _ _).mp (hs (a w)))`.

Rewrite using `[← himg, Nat.card_image_of_injective hinj]`. Both sides reduce to the same expression.
-/
theorem card_bridge {W A R : Type} [CommRing R] (ϖ : R) (a : W → A) (ha : Function.Surjective a) (φ : W → R)
    (hφ : Function.Surjective φ) (hker : ∀ w w', a w = a w' ↔ φ w - φ w' ∈ lev ϖ 1) (PA : A → Prop) (PR : R → Prop)
    (hP : ∀ w, PA (a w) ↔ PR (φ w)) :
    Nat.card {y // PA y} = Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x}) := by
  classical
  choose s hs using ha
  let e : A → R ⧸ lev ϖ 1 := fun y => Ideal.Quotient.mk (lev ϖ 1) (φ (s y))
  have hinj : Function.Injective e := by
    intro y y' h
    have h' := Ideal.Quotient.eq.mp h
    rw [← hs y, ← hs y']
    exact (hker _ _).mpr h'
  have himg : e '' {y | PA y} = Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x} := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ (s y), ?_, rfl⟩
      have hy' : PA (a (s y)) := by
        rw [hs y]
        exact hy
      exact (hP _).mp hy'
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := hφ x
      refine ⟨a w, (hP w).mpr hx, ?_⟩
      exact Ideal.Quotient.eq.mpr ((hker _ _).mp (hs (a w)))
  rw [← himg, Nat.card_image_of_injective hinj]
  rfl

/- English proof (translation)
Unfold `solCount`. Establish `hinj : Function.Injective (fun y : Matrix (Fin 1) (Fin 1) (R ⧸ lev ϖ 1) => y 0 0)`. Introduce `y y' h`. Use extensionality with `a b`. Take `rfl : a = 0` from `Subsingleton.elim _ _`.

Take `rfl : b = 0` from `Subsingleton.elim _ _`. Conclude with `h`. Rewrite using `[← Nat.card_image_of_injective hinj, Set.image_image]`. Use `congrArg (fun s : Set (R ⧸ lev ϖ 1) => Nat.card s) ?_` and prove the remaining obligations. Use extensionality with `c`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, hX, rfl⟩`. Use `⟨X 0 0, ?_, rfl⟩` and prove the remaining obligations. Establish `h00` using `congrFun (congrFun hX 0) 0`. Simplify `h00` using `[red, cT, Matrix.mul_apply]`.

Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨Matrix.of fun _ _ => x, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq]`. Use extensionality with `a b`. Take `rfl : a = 0` from `Subsingleton.elim _ _`.

Take `rfl : b = 0` from `Subsingleton.elim _ _`. Simplify `hx` using `[red, cT, Matrix.mul_apply]`.
-/
theorem solCount_one_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (j t : R) :
    solCount σ ϖ (Matrix.of fun _ _ => j : Matrix (Fin 1) (Fin 1) R) (Matrix.of fun _ _ => t : Matrix (Fin 1) (Fin 1) R) 1 =
      Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x : R | Ideal.Quotient.mk (lev ϖ 1) (σ x * j * x) =
        Ideal.Quotient.mk (lev ϖ 1) t}) := by
  classical
  unfold solCount
  have hinj : Function.Injective (fun y : Matrix (Fin 1) (Fin 1) (R ⧸ lev ϖ 1) => y 0 0) := by
    intro y y' h
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    exact h
  rw [← Nat.card_image_of_injective hinj, Set.image_image]
  refine congrArg (fun s : Set (R ⧸ lev ϖ 1) => Nat.card s) ?_
  ext c
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨X 0 0, ?_, rfl⟩
    have h00 := congrFun (congrFun hX 0) 0
    simpa [red, cT, Matrix.mul_apply] using h00
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Matrix.of fun _ _ => x, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    simpa [red, cT, Matrix.mul_apply] using hx

end PositivityTheory.SiegelWeilFormula.MOne

end
