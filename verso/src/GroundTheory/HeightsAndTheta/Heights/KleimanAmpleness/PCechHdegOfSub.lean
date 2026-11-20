import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHdegOfSubSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem Cdeg_top (i : ℕ) : Cdeg G (fun I => (⊤ : Submodule R (G I))) i = ⊤ := by
  ext s
  simp [Cdeg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem cocyDeg_top (i : ℕ) :
    cocyDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = LinearMap.ker (d G ρ i) := by
  rw [cocyDeg, Cdeg_top, inf_top_eq]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem bdryDeg_top (i : ℕ) :
    bdryDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i =>
    change (Cdeg G _ i).map (d G ρ i) = LinearMap.range (d G ρ i)
    rw [Cdeg_top, Submodule.map_top]

def hEquivHdegTop (i : ℕ) : H G ρ i ≃ₗ[R] Hdeg G (fun I => (⊤ : Submodule R (G I))) ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i).symm) (by
    ext z
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    change (z : Cochain G i) ∈ bdry G ρ i ↔ (z : Cochain G i) ∈ bdryDeg G _ ρ i
    rw [bdryDeg_top])

end Cech

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem CechHdegOfSub.proof : CechHdegOfSub.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ T n
  let φ : ∀ I : Chart x, T.sub I →ₗ[S] E := fun I =>
    { toFun := fun y => (y : E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (m : T.sub I),
      φ J (T.res I J h m) = Cech.idRes S E (support x) I J h (φ I m) := fun _ _ _ _ => rfl
  have hdeg : ∀ (I : Chart x) (m : T.sub I), m ∈ (⊤ : Submodule S (T.sub I)) →
      φ I m ∈ (T.sub I).restrictScalars S := fun _ m _ => m.2
  have hinj : ∀ I, Function.Injective (φ I) := fun _ => Subtype.val_injective
  have hmap : ∀ I, (⊤ : Submodule S (T.sub I)).map (φ I) = (T.sub I).restrictScalars S := by
    intro I
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro h
      exact ⟨⟨y, h⟩, trivial, rfl⟩
  exact ⟨(Cech.hEquivHdegTop (fun I => T.sub I) T.res n).trans
    (LinearEquiv.ofBijective (Cech.mapHdeg _ _ φ hφ hdeg n)
      (Cech.Transport.proof.{u, v, v} (N + 1) (support x) S (fun I => T.sub I) (fun _ => E) T.res
        (Cech.idRes S E (support x)) _ _ φ hφ hdeg hinj hmap n))⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
