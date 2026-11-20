import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.KStability
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.DedekindSR
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

open CategoryTheory NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

/- English proof (translation)
Establish `key : ∀ x : M, x ∈ AddCommGroup.torsion M ↔ e x ∈ AddCommGroup.torsion N`. Introduce `x`. Rewrite using `[AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]`. Conclude with `(Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm`. Conclude with `Nat.card_congr (e.toEquiv.subtypeEquiv key)`.
-/
private theorem UpperTheory.V.ZK.Up.card_tors_eq {M N : Type} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    Nat.card (AddCommGroup.torsion M) = Nat.card (AddCommGroup.torsion N) := by
  have key : ∀ x : M, x ∈ AddCommGroup.torsion M ↔ e x ∈ AddCommGroup.torsion N := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  exact Nat.card_congr (e.toEquiv.subtypeEquiv key)

/- English proof (translation)
Introduce `L _ _ hL m n n' hn hnn'`. Use `haveI := hL`. Establish `hiso : ∀ k, 2 * m + 4 ≤ k → IsIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m)` using `fun k hk => PositivityTheory.v8.KStability.kStability (𝓞 L) 2 (dedekindSR (𝓞 L)) m k (by omega)`. Establish `he : Nonempty ((grpH (GL (Fin n) (𝓞 L)) m : Type) ≃+ (grpH (GL (Fin n') (𝓞 L)) m : Type))`. Proceed by induction on `n', hnn' using Nat.le_induction with`.

Consider the case `base => exact ⟨AddEquiv.refl _⟩`. Consider the case `succ k hk ih`. Take `⟨e⟩` from `ih`. Use `haveI := hiso k (by omega)`. Conclude with `⟨e.trans (asIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m)).toLinearEquiv.toAddEquiv⟩`.

Take `⟨e⟩` from `he`. Establish `key : ∀ x, x ∈ AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type) ↔ e x ∈ AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m : Type)`. Introduce `x`. Rewrite using `[AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]`. Conclude with `(Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm`.

Establish `hfin : Finite (AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type))` using `(UpperTheory.V.KT.tors_le L n m).1`. Use `⟨Finite.of_equiv _ (e.toEquiv.subtypeEquiv key), ?_⟩` and prove the remaining obligations. Rewrite using `[← UpperTheory.V.ZK.Up.card_tors_eq e]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.ZK.Up.torsStab :
    UpperTheory.V.ZK.Up.TorsStab := by
  intro L _ _ hL m n n' hn hnn'
  haveI := hL
  have hiso : ∀ k, 2 * m + 4 ≤ k → IsIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m) :=
    fun k hk => PositivityTheory.v8.KStability.kStability (𝓞 L) 2 (dedekindSR (𝓞 L)) m k (by omega)
  have he : Nonempty ((grpH (GL (Fin n) (𝓞 L)) m : Type) ≃+ (grpH (GL (Fin n') (𝓞 L)) m : Type)) := by
    induction n', hnn' using Nat.le_induction with
    | base => exact ⟨AddEquiv.refl _⟩
    | succ k hk ih =>
      obtain ⟨e⟩ := ih
      haveI := hiso k (by omega)
      exact ⟨e.trans (asIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m)).toLinearEquiv.toAddEquiv⟩
  obtain ⟨e⟩ := he
  have key : ∀ x, x ∈ AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type) ↔
      e x ∈ AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m : Type) := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  have hfin : Finite (AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type)) :=
    (UpperTheory.V.KT.tors_le L n m).1
  refine ⟨Finite.of_equiv _ (e.toEquiv.subtypeEquiv key), ?_⟩
  rw [← UpperTheory.V.ZK.Up.card_tors_eq e]
  rfl
