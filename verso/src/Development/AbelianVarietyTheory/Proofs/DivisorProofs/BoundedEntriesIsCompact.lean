import Mathlib

namespace GlobalTheory.BoundedUnitsCompact

/- English proof (translation)
Establish `h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} = Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M))`. Use extensionality with `A`. Prove the components needed by the constructor for the conclusion. Introduce `hA i _ j _`. Simplify using `using hA i j`.

Introduce `hA i j`. Simplify using `using hA i trivial j trivial`. Rewrite using `[h]`. Conclude with `isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))`.
-/
theorem boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))

/- English proof (translation)
Establish `hK1` using `boundedEntries_isCompact (F := F) (n := n) M`. Establish `hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M}))` using `hK1.prod (hK1.image MulOpposite.continuous_op)`. Establish `hce` using `Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)`. Use `hce.isCompact_preimage hK using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`.

Simplify using `[Units.embedProduct, -MulOpposite.op_inv]`.
-/
theorem isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]

end GlobalTheory.BoundedUnitsCompact
