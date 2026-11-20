import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CharpolyRevMap
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IdemNormalForm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsolutelyIrreducibleSpan

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Introduce `k _ n _ _ _ G _ ρ hρ`. Take `⟨hirr, hcom⟩` from `hρ`. Set `A` to `MonoidAlgebra k G`. Set `V` to `n → k`. Set `L : A →ₐ[k] Matrix n n k` to `MonoidAlgebra.lift k (Matrix n n k) G ρ`.

Set `φ : A →ₐ[k] Module.End k V` to `(Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] _).toAlgHom.comp L`. Use `letI : Module A V := Module.compHom V φ.toRingHom`. Establish `hact : ∀ (a : A) (v : V), a • v = (L a).mulVec v` using `fun a v => rfl`. Use `haveI : IsScalarTower k A V := ⟨fun c a v => by`. Rewrite using `[hact, hact, map_smul, Matrix.smul_mulVec]⟩`.

Establish `hof : ∀ g, L (MonoidAlgebra.of k G g) = ρ g` using `fun g => MonoidAlgebra.lift_of ρ g`. Establish `hS : IsSimpleModule A V` using `by haveI : Nontrivial (Submodule A V) := by`. Use `⟨⊥, ⊤, fun h => ?_⟩` and prove the remaining obligations. Establish `: (⊤ : Submodule A V) = ⊥` using `h.symm`. Establish `h2 : (fun _ : n => (1 : k)) ∈ (⊤ : Submodule A V)` using `Submodule.mem_top`.

Rewrite `h2` using `[this, Submodule.mem_bot]`. Conclude with `one_ne_zero (congrFun h2 (Classical.arbitrary n))`. It suffices to establish `hso : IsSimpleOrder (Submodule A V) from @IsSimpleModule.mk _ _ _ _ _ hso`. Use `⟨fun W => ?_⟩` and prove the remaining obligations. Break down `hirr (W.restrictScalars k) (fun g v hv => by` into its components or cases.

Use `W.smul_mem (MonoidAlgebra.of k G g) hv` as an intermediate fact. Rewrite `this` using `[hact, hof]`. Conclude with `this) with h | h`. Use `left`. Conclude with `(Submodule.restrictScalars_eq_bot_iff k A V).mp h`.

Use `right`. Conclude with `(Submodule.restrictScalars_eq_top_iff k A V).mp h`. Establish `hsc : ∀ ψ : V →ₗ[A] V, ∃ c : k, ∀ v, ψ v = c • v`. Introduce `ψ`. Set `M : Matrix n n k` to `LinearMap.toMatrix' (ψ.restrictScalars k)`.

Establish `hM : ∀ v, M.mulVec v = ψ v` using `fun v => by`. Use `LinearMap.toMatrix'_mulVec (ψ.restrictScalars k) v` as an intermediate fact. Simplify `this` using `[M]`. Take `⟨c, hc⟩` from `hcom M (fun g => by`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]`. Rewrite using `[hM, hM, ← hof, ← hact, ← hact, map_smul])`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← hM, hc, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Establish `hsurj` using `burnside k A V hS hsc`. Use `eq_top_iff.mpr fun B _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hsurj (Matrix.toLin' B)`. Establish `hB : B = L a`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun ha v` as an intermediate fact. Simplify using `only [Matrix.toLin'_apply]`. Rewrite using `[← hact]`. Conclude with `this.symm`.

Rewrite using `[hB]`. Conclude with `MonoidAlgebra.induction_on (motive := fun a => L a ∈ Submodule.span k (Set.range ρ)) a (fun g => by rw [hof]; exact Submodule.subset_span ⟨g, rfl⟩) (fun f g hf hg => by rw [map_add]; exact Submodule.add_mem _ hf hg) (fun c f hf => by rw [map_smul]; exact Submodule.smul_mem _ _ hf …`.
-/
theorem burnsideMat : StatBurnsideMat := by
  intro k _ n _ _ _ G _ ρ hρ
  obtain ⟨hirr, hcom⟩ := hρ
  let A := MonoidAlgebra k G
  let V := n → k
  let L : A →ₐ[k] Matrix n n k := MonoidAlgebra.lift k (Matrix n n k) G ρ
  let φ : A →ₐ[k] Module.End k V := (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] _).toAlgHom.comp L
  letI : Module A V := Module.compHom V φ.toRingHom
  have hact : ∀ (a : A) (v : V), a • v = (L a).mulVec v := fun a v => rfl
  haveI : IsScalarTower k A V := ⟨fun c a v => by
    rw [hact, hact, map_smul, Matrix.smul_mulVec]⟩
  have hof : ∀ g, L (MonoidAlgebra.of k G g) = ρ g := fun g => MonoidAlgebra.lift_of ρ g
  have hS : IsSimpleModule A V := by
    haveI : Nontrivial (Submodule A V) := by
      refine ⟨⊥, ⊤, fun h => ?_⟩
      have : (⊤ : Submodule A V) = ⊥ := h.symm
      have h2 : (fun _ : n => (1 : k)) ∈ (⊤ : Submodule A V) := Submodule.mem_top
      rw [this, Submodule.mem_bot] at h2
      exact one_ne_zero (congrFun h2 (Classical.arbitrary n))
    suffices hso : IsSimpleOrder (Submodule A V) from @IsSimpleModule.mk _ _ _ _ _ hso
    refine ⟨fun W => ?_⟩
    rcases hirr (W.restrictScalars k) (fun g v hv => by
      have := W.smul_mem (MonoidAlgebra.of k G g) hv
      rw [hact, hof] at this
      exact this) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff k A V).mp h
    · right; exact (Submodule.restrictScalars_eq_top_iff k A V).mp h
  have hsc : ∀ ψ : V →ₗ[A] V, ∃ c : k, ∀ v, ψ v = c • v := by
    intro ψ
    let M : Matrix n n k := LinearMap.toMatrix' (ψ.restrictScalars k)
    have hM : ∀ v, M.mulVec v = ψ v := fun v => by
      have := LinearMap.toMatrix'_mulVec (ψ.restrictScalars k) v
      simpa [M] using this
    obtain ⟨c, hc⟩ := hcom M (fun g => by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [hM, hM, ← hof, ← hact, ← hact, map_smul])
    refine ⟨c, fun v => ?_⟩
    rw [← hM, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsurj := burnside k A V hS hsc
  refine eq_top_iff.mpr fun B _ => ?_
  obtain ⟨a, ha⟩ := hsurj (Matrix.toLin' B)
  have hB : B = L a := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun ha v
    simp only [Matrix.toLin'_apply]
    rw [← hact]
    exact this.symm
  rw [hB]
  exact MonoidAlgebra.induction_on (motive := fun a => L a ∈ Submodule.span k (Set.range ρ)) a
    (fun g => by rw [hof]; exact Submodule.subset_span ⟨g, rfl⟩)
    (fun f g hf hg => by rw [map_add]; exact Submodule.add_mem _ hf hg)
    (fun c f hf => by rw [map_smul]; exact Submodule.smul_mem _ _ hf)

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan .. | (apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheo …`.
-/
theorem ontoSpan : StatOntoSpan := by
  first | exact UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan .. | (apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> first | assumption | infer_instance)

/- English proof (translation)
Introduce `O _ _ _ X' _ d _ _ R' hint`. Set `L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O))` to `{ toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j) map_add' := fun F F' => by funext x'; ext i j; simp map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }`. Establish `hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L`. Introduce `a ha`. Use `choose F hF using hint a ha`.

Conclude with `⟨F, by funext x'; ext i j; exact hF x' i j⟩`. Use `haveI : IsNoetherian O (LinearMap.range L) := inferInstance`. Use `haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle`. Use `haveI h2 : IsNoetherian O R' := h1`. Conclude with `isNoetherian_of_tower O h2`.
-/
theorem noeth : StatNoeth := by
  intro O _ _ _ X' _ d _ _ R' hint
  let L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O)) :=
    { toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j)
      map_add' := fun F F' => by funext x'; ext i j; simp
      map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }
  have hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L := by
    intro a ha
    choose F hF using hint a ha
    exact ⟨F, by funext x'; ext i j; exact hF x' i j⟩
  haveI : IsNoetherian O (LinearMap.range L) := inferInstance
  haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle
  haveI h2 : IsNoetherian O R' := h1
  exact isNoetherian_of_tower O h2

end Formalism.RepresentationBoundsCohomology.ringDataObjects
