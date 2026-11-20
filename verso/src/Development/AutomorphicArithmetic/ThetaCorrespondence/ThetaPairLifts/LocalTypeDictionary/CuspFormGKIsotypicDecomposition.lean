import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpan
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteSumOfGKModuleMaps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StructureOfKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpanStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
namespace GlobalTheory.CuspGKId
/- English proof (citation)
Apply `GlobalTheory.T.gKModule_map_finite_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FLocalTypeDictionary%2FFiniteSumOfGKModuleMaps.lean&line=96#L96)
-/
theorem cuspForm_local_sum_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := _root_.GlobalTheory.T.gKModule_map_finite_sum
/- English proof (citation)
Apply `GlobalTheory.T.structure_of_kFinite_vectors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FLocalTypeDictionary%2FStructureOfKFiniteVectors.lean&line=42#L42)
-/
theorem cuspForm_kFinite_structure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := _root_.GlobalTheory.T.structure_of_kFinite_vectors
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
/- English proof (translation)
Introduce `hPr D θ V S M hθ τ φ hφ hty hW`. Take `⟨m, T, p, hT, hsum⟩` from `_root_.GlobalTheory.CuspGKId.cuspForm_local_sum_model hPr θ V S M hθ τ φ hφ hty hW`. Take `⟨-, hKst, hder, hsimp⟩` from `_root_.GlobalTheory.CuspGKId.cuspForm_kFinite_structure hPr V S M τ`. Set `P` to `GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)`. Set `kOp : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} → Module.End ℂ P` to `fun g => LinearMap.codRestrict P ((M.rep τ g.1 : M.H τ →ₗ[ℂ] M.H τ).comp P.subtype) fun v => hKst g.1 g.2.1 g.2.2 v`.

Establish `hdu : ∀ X ∈ lieAt V τ, ∀ v w w' : P, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w' : M.H τ) 0 → w = w'` using `fun X _ v w w' h h' => Subtype.ext (h.unique h')`. Set `dOp : {X // X ∈ lieAt V τ} → Module.End ℂ P` to `fun X => { toFun := fun v => Classical.choose (hder X.1 X.2 v) map_add' := fun a b => by`. Use `(hdu X.1 X.2 (a + b) _ _ (Classical.choose_spec (hder X.1 X.2 (a + b))) ?_)` and prove the remaining obligations. Establish `h` using `(Classical.choose_spec (hder X.1 X.2 a)).add (Classical.choose_spec (hder X.1 X.2 b))`. Establish `e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((a + b : P) : M.H τ)) = fun t => M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) + M.rep τ (NormedSpace.exp (t • X.1)) (b : M.H τ)`.

Use function extensionality and compare the values at `fun t => by rw [Submodule.coe_add, map_add]`. Rewrite using `[e, Submodule.coe_add]`. Conclude with `h`. Use the proof step `map_smul' := fun c a => by`. Use `(hdu X.1 X.2 (c • a) _ _ (Classical.choose_spec (hder X.1 X.2 (c • a))) ?_)` and prove the remaining obligations.

Establish `h` using `(Classical.choose_spec (hder X.1 X.2 a)).const_smul c`. Establish `e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((c • a : P) : M.H τ)) = fun t => c • M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ)`. Use function extensionality and compare the values at `fun t => by rw [Submodule.coe_smul, map_smul]`. Rewrite using `[e, Submodule.coe_smul]`. Conclude with `h }`.

Establish `hdOp : ∀ X : {X // X ∈ lieAt V τ}, ∀ v : P, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) (v : M.H τ)) (dOp X v : M.H τ) 0` using `fun X v => Classical.choose_spec (hder X.1 X.2 v)`. Set `a : ({g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} ⊕ {X // X ∈ lieAt V τ}) → Module.End ℂ P` to `fun i => Sum.elim kOp dOp i`. Establish `hsimple : ∀ B : Submodule ℂ P, (∀ i, ∀ v ∈ B, a i v ∈ B) → B ≠ ⊥ → B = ⊤` using `fun B hB h0 => hsimp B h0 fun X hX v w hv hd => by`. Rewrite using `[hdu X hX v w _ hd (hdOp ⟨X, hX⟩ v)]`. Conclude with `hB (Sum.inr ⟨X, hX⟩) v hv`.

Set `Ttot : (Fin m → P) →ₗ[ℂ] (GA D V → ℂ)` to `∑ j, (T j).comp (LinearMap.proj j)`. Establish `hTtot : ∀ y, Ttot y = ∑ j, T j (y j)` using `fun y => by`. Simplify using `[Ttot, LinearMap.sum_apply]`. Establish `hTK : ∀ (g : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)}) (y : Fin m → P), Ttot (fun j => kOp g (y j)) = rTr V (atTau θ V τ g.1) (Ttot y)` using `fun g y => by`. Rewrite using `[hTtot, hTtot, show rTr V (atTau θ V τ g.1) (∑ j, T j (y j)) = ∑ j, rTr V (atTau θ V τ g.1) (T j (y j)) from map_sum (rTrL V (atTau θ V τ g.1)) (fun j => T j (y j)) Finset.univ]`.

Conclude with `Finset.sum_congr rfl fun j _ => (hT j).mapK g.1 g.2.1 g.2.2 (y j) _ rfl`. Establish `hTL : ∀ (X : {X // X ∈ lieAt V τ}) (y : Fin m → P), Ttot (fun j => dOp X (y j)) = Rder θ V τ X.1 (Ttot y)` using `fun X y => by`. Rewrite using `[hTtot, hTtot, Rder_sum X.2 _ fun j => (hT j).aut _]`. Conclude with `Finset.sum_congr rfl fun j _ => (hT j).mapLie X.1 X.2 (y j) _ (hdOp X (y j))`. Establish `hloc` using `isLocSub_locGen θ M τ φ`.

Set `N : Submodule ℂ (Fin m → P)` to `(locGen θ M τ φ).comap Ttot`. Establish `hN : ∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N`. Introduce and unpack `(g | X) y hy`. Use `show Ttot (fun j => kOp g (y j)) ∈ locGen θ M τ φ`. Rewrite using `[hTK]`.

Conclude with `hloc.k g.1 g.2 _ hy`. Use `show Ttot (fun j => dOp X (y j)) ∈ locGen θ M τ φ`. Rewrite using `[hTL]`. Conclude with `hloc.lie X.1 X.2 _ hy`. Establish `hpN : p ∈ N` using `by show Ttot p ∈ locGen θ M τ φ`.

Rewrite using `[hTtot, ← hsum]`. Conclude with `mem_locGen θ M τ φ`. Take `⟨n, Sm, q, hSa, hSN, hpq⟩` from `sub_pow_sum a hsimple m N hN p hpN`. Use `⟨n, fun l => Ttot.comp (Sm l), q, fun l => ⟨fun v => ?_, fun g hg hk v w hw => ?_, fun X hX v w hw => ?_⟩, fun l v => hSN l v, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hTtot]`.

Conclude with `isAutFunSm_sum _ fun j => (hT j).aut _`. Establish `e : w = kOp ⟨g, hg, hk⟩ v` using `Subtype.ext hw`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, e]`. Use `hSa l (Sum.inl ⟨g, hg, hk⟩) v` as an intermediate fact. Simplify using `only [a, Sum.elim_inl] at this`.

Rewrite using `[this, hTK]`. Establish `e : w = dOp ⟨X, hX⟩ v` using `hdu X hX v w _ hw (hdOp ⟨X, hX⟩ v)`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, e]`. Use `hSa l (Sum.inr ⟨X, hX⟩) v` as an intermediate fact. Simplify using `only [a, Sum.elim_inr] at this`.

Rewrite using `[this, hTL]`. Rewrite using `[hsum, ← hTtot p, hpq, map_sum]`. Both sides reduce to the same expression.
-/
theorem cuspForm_local_sum_generates : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (n : ℕ) (T : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T l)) ∧
      (∀ l v, T l v ∈ GlobalTheory.CuspGKId.locGen θ M τ φ) ∧ φ = ∑ l, T l (p l) := by
  intro hPr D θ V S M hθ τ φ hφ hty hW
  obtain ⟨m, T, p, hT, hsum⟩ := _root_.GlobalTheory.CuspGKId.cuspForm_local_sum_model hPr θ V S M hθ τ φ hφ hty hW
  obtain ⟨-, hKst, hder, hsimp⟩ := _root_.GlobalTheory.CuspGKId.cuspForm_kFinite_structure hPr V S M τ
  let P := GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)
  let kOp : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} → Module.End ℂ P :=
    fun g => LinearMap.codRestrict P ((M.rep τ g.1 : M.H τ →ₗ[ℂ] M.H τ).comp P.subtype) fun v => hKst g.1 g.2.1 g.2.2 v
  have hdu : ∀ X ∈ lieAt V τ, ∀ v w w' : P,
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w' : M.H τ) 0 → w = w' :=
    fun X _ v w w' h h' => Subtype.ext (h.unique h')
  let dOp : {X // X ∈ lieAt V τ} → Module.End ℂ P := fun X =>
    { toFun := fun v => Classical.choose (hder X.1 X.2 v)
      map_add' := fun a b => by
        refine (hdu X.1 X.2 (a + b) _ _ (Classical.choose_spec (hder X.1 X.2 (a + b))) ?_)
        have h := (Classical.choose_spec (hder X.1 X.2 a)).add (Classical.choose_spec (hder X.1 X.2 b))
        have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((a + b : P) : M.H τ)) =
            fun t => M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) + M.rep τ (NormedSpace.exp (t • X.1)) (b : M.H τ) :=
          funext fun t => by rw [Submodule.coe_add, map_add]
        rw [e, Submodule.coe_add]
        exact h
      map_smul' := fun c a => by
        refine (hdu X.1 X.2 (c • a) _ _ (Classical.choose_spec (hder X.1 X.2 (c • a))) ?_)
        have h := (Classical.choose_spec (hder X.1 X.2 a)).const_smul c
        have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((c • a : P) : M.H τ)) =
            fun t => c • M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) :=
          funext fun t => by rw [Submodule.coe_smul, map_smul]
        rw [e, Submodule.coe_smul]
        exact h }
  have hdOp : ∀ X : {X // X ∈ lieAt V τ}, ∀ v : P,
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) (v : M.H τ)) (dOp X v : M.H τ) 0 :=
    fun X v => Classical.choose_spec (hder X.1 X.2 v)
  let a : ({g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} ⊕
      {X // X ∈ lieAt V τ}) → Module.End ℂ P := fun i => Sum.elim kOp dOp i
  have hsimple : ∀ B : Submodule ℂ P, (∀ i, ∀ v ∈ B, a i v ∈ B) → B ≠ ⊥ → B = ⊤ := fun B hB h0 =>
    hsimp B h0 fun X hX v w hv hd => by
      rw [hdu X hX v w _ hd (hdOp ⟨X, hX⟩ v)]
      exact hB (Sum.inr ⟨X, hX⟩) v hv
  let Ttot : (Fin m → P) →ₗ[ℂ] (GA D V → ℂ) := ∑ j, (T j).comp (LinearMap.proj j)
  have hTtot : ∀ y, Ttot y = ∑ j, T j (y j) := fun y => by
    simp [Ttot, LinearMap.sum_apply]
  have hTK : ∀ (g : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)})
      (y : Fin m → P), Ttot (fun j => kOp g (y j)) = rTr V (atTau θ V τ g.1) (Ttot y) := fun g y => by
    rw [hTtot, hTtot, show rTr V (atTau θ V τ g.1) (∑ j, T j (y j)) = ∑ j, rTr V (atTau θ V τ g.1) (T j (y j))
      from map_sum (rTrL V (atTau θ V τ g.1)) (fun j => T j (y j)) Finset.univ]
    exact Finset.sum_congr rfl fun j _ => (hT j).mapK g.1 g.2.1 g.2.2 (y j) _ rfl
  have hTL : ∀ (X : {X // X ∈ lieAt V τ}) (y : Fin m → P), Ttot (fun j => dOp X (y j)) = Rder θ V τ X.1 (Ttot y) :=
    fun X y => by
      rw [hTtot, hTtot, Rder_sum X.2 _ fun j => (hT j).aut _]
      exact Finset.sum_congr rfl fun j _ => (hT j).mapLie X.1 X.2 (y j) _ (hdOp X (y j))
  have hloc := isLocSub_locGen θ M τ φ
  let N : Submodule ℂ (Fin m → P) := (locGen θ M τ φ).comap Ttot
  have hN : ∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N := by
    rintro (g | X) y hy
    · show Ttot (fun j => kOp g (y j)) ∈ locGen θ M τ φ
      rw [hTK]
      exact hloc.k g.1 g.2 _ hy
    · show Ttot (fun j => dOp X (y j)) ∈ locGen θ M τ φ
      rw [hTL]
      exact hloc.lie X.1 X.2 _ hy
  have hpN : p ∈ N := by
    show Ttot p ∈ locGen θ M τ φ
    rw [hTtot, ← hsum]
    exact mem_locGen θ M τ φ
  obtain ⟨n, Sm, q, hSa, hSN, hpq⟩ := sub_pow_sum a hsimple m N hN p hpN
  refine ⟨n, fun l => Ttot.comp (Sm l), q, fun l => ⟨fun v => ?_, fun g hg hk v w hw => ?_,
    fun X hX v w hw => ?_⟩, fun l v => hSN l v, ?_⟩
  · rw [LinearMap.comp_apply, hTtot]
    exact isAutFunSm_sum _ fun j => (hT j).aut _
  · have e : w = kOp ⟨g, hg, hk⟩ v := Subtype.ext hw
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    have := hSa l (Sum.inl ⟨g, hg, hk⟩) v
    simp only [a, Sum.elim_inl] at this
    rw [this, hTK]
  · have e : w = dOp ⟨X, hX⟩ v := hdu X hX v w _ hw (hdOp ⟨X, hX⟩ v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    have := hSa l (Sum.inr ⟨X, hX⟩) v
    simp only [a, Sum.elim_inr] at this
    rw [this, hTL]
  · rw [hsum, ← hTtot p, hpq, map_sum]
    rfl
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
/- English proof (translation)
Establish `hsm : ∀ f ∈ A, IsAutFunSm θ V f` using `fun f hf => (hAf f hf).1`. Use `set Hs := partSub θ M A hsm s p0 lam with hHs`. Establish `hinj : ∀ F₁ ∈ Hs, ∀ F₂ ∈ Hs, F₁ p0 = F₂ p0 → F₁ = F₂`. Introduce `F₁ h₁ F₂ h₂ e`. Establish `h3 : F₁ - F₂ ∈ Hs` using `Hs.sub_mem h₁ h₂`.

Use `IsPartMult.eq_zero h3 hp0 hsimple (by rw [MultilinearMap.sub_apply, e, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Use `set E := Hs.map (evAt p0) with hE`. Establish `hEloc : IsLocSub θ M τ E`. Use `⟨fun g hg y hy => ?_, fun X hX y hy => ?_⟩` and prove the remaining obligations.

Take `⟨F', hF', rfl⟩` from `hy`. Conclude with `⟨_, IsPartMult.rTr_comp hθ hA hF' hτ hg, rfl⟩`. Take `⟨F', hF', rfl⟩` from `hy`. Conclude with `⟨_, IsPartMult.postRder_comp hθ hA hsm hF' hτ hX, rfl⟩`. Establish `hx : F p0 ∈ A` using `hF.mem p0`.

Take `⟨hxa, -, hxt, W, hW1, hW2, hW3⟩` from `hAf _ hx`. Take `⟨n, T, p, hT, hTl, hsum⟩` from `_root_.GlobalTheory.CuspGKId.cuspForm_local_sum_generates hPr θ V S M hθ τ (F p0) hxa (hxt τ) ⟨W, hW1, hW2, hW3 τ⟩`. Establish `hgen : locGen θ M τ (F p0) ≤ E` using `locGen_le θ M ⟨F, hF, rfl⟩ hEloc`. Set `f` to `(evAt p0).domRestrict Hs`. Establish `hfi : Function.Injective f` using `fun a b e => Subtype.ext (hinj a a.2 b b.2 e)`.

Set `e` to `LinearEquiv.ofInjective f hfi`. Establish `hrange : ∀ l v, T l v ∈ LinearMap.range f` using `fun l v => by`. Rewrite using `[LinearMap.range_domRestrict]`. Conclude with `hgen (hTl l v)`. Set `T' : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M)` to `fun l => Hs.subtype.comp (e.symm.toLinearMap.comp ((T l).codRestrict (LinearMap.range f) (hrange l)))`.

Establish `hT'mem : ∀ l v, T' l v ∈ Hs` using `fun l v => (e.symm _).2`. Establish `hT'ev : ∀ l v, T' l v p0 = T l v` using `fun l v => by`. Use `LinearEquiv.ofInjective_apply (h := hfi) f (e.symm ⟨T l v, hrange l v⟩)` as an intermediate fact. Establish `h2 : e (e.symm ⟨T l v, hrange l v⟩) = ⟨T l v, hrange l v⟩` using `e.apply_symm_apply _`. Conclude with `(this.symm.trans (congrArg Subtype.val h2))`.

Use `⟨n, T', p, fun m v => hT'mem m v, fun m g hg hk v w hw u => ?_, fun m X hX v w hw u => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : T' m w = (rTrL V (atTau θ V τ g)).compMultilinearMap (T' m v)` using `hinj _ (hT'mem m w) _ (IsPartMult.rTr_comp hθ hA (hT'mem m v) hτ ⟨hg, hk⟩) (by`. Rewrite using `[hT'ev, LinearMap.compMultilinearMap_apply, hT'ev]`. Conclude with `(hT m).mapK g hg hk v w hw)`. Rewrite using `[h1]`.

Both sides reduce to the same expression. Establish `h1 : T' m w = GlobalTheory.CuspGKId.postRder (θ` using `θ) τ X hX (T' m v) (fun u => hsm _ ((hT'mem m v).mem u)) := hinj _ (hT'mem m w) _ (IsPartMult.postRder_comp hθ hA hsm (hT'mem m v) hτ hX) (by`. Rewrite using `[hT'ev]`. Use `show T m w = Rder θ V τ X (T' m v p0)`. Rewrite using `[hT'ev]`.

Conclude with `(hT m).mapLie X hX v w hw)`. Rewrite using `[h1]`. Both sides reduce to the same expression. Use `hinj _ hF _ (Hs.sum_mem fun m _ => hT'mem m (p m)) ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.sum_apply]`.

Simplify using `only [hT'ev]`. Conclude with `hsum`.
-/
theorem IsPartMult.partialMultiplicity_decomposition (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hAf : ∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) {s : Finset D.what₂.Tau}
    {p0 : Tup M} {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} (hp0 : ∀ τ, p0 τ ≠ 0)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    {F : MMK M} (hF : IsPartMult θ M A s p0 lam F) {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    ∃ (n : ℕ) (T : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M))
      (q : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ m p, IsPartMult θ M A s p0 lam (T m p)) ∧
      (∀ m, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), (w : M.H τ) = M.rep τ g v →
          ∀ u, T m w u = rTr V (atTau θ V τ g) (T m v u)) ∧
      (∀ m, ∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
          ∀ u, T m w u = Rder θ V τ X (T m v u)) ∧
      F = ∑ m, T m (q m) := by
  have hsm : ∀ f ∈ A, IsAutFunSm θ V f := fun f hf => (hAf f hf).1
  set Hs := partSub θ M A hsm s p0 lam with hHs
  have hinj : ∀ F₁ ∈ Hs, ∀ F₂ ∈ Hs, F₁ p0 = F₂ p0 → F₁ = F₂ := by
    intro F₁ h₁ F₂ h₂ e
    have h3 : F₁ - F₂ ∈ Hs := Hs.sub_mem h₁ h₂
    have := IsPartMult.eq_zero h3 hp0 hsimple (by rw [MultilinearMap.sub_apply, e, sub_self])
    exact sub_eq_zero.1 this
  set E := Hs.map (evAt p0) with hE
  have hEloc : IsLocSub θ M τ E := by
    refine ⟨fun g hg y hy => ?_, fun X hX y hy => ?_⟩
    · obtain ⟨F', hF', rfl⟩ := hy
      exact ⟨_, IsPartMult.rTr_comp hθ hA hF' hτ hg, rfl⟩
    · obtain ⟨F', hF', rfl⟩ := hy
      exact ⟨_, IsPartMult.postRder_comp hθ hA hsm hF' hτ hX, rfl⟩
  have hx : F p0 ∈ A := hF.mem p0
  obtain ⟨hxa, -, hxt, W, hW1, hW2, hW3⟩ := hAf _ hx
  obtain ⟨n, T, p, hT, hTl, hsum⟩ :=
    _root_.GlobalTheory.CuspGKId.cuspForm_local_sum_generates hPr θ V S M hθ τ (F p0) hxa (hxt τ) ⟨W, hW1, hW2, hW3 τ⟩
  have hgen : locGen θ M τ (F p0) ≤ E := locGen_le θ M ⟨F, hF, rfl⟩ hEloc
  let f := (evAt p0).domRestrict Hs
  have hfi : Function.Injective f := fun a b e => Subtype.ext (hinj a a.2 b b.2 e)
  let e := LinearEquiv.ofInjective f hfi
  have hrange : ∀ l v, T l v ∈ LinearMap.range f := fun l v => by
    rw [LinearMap.range_domRestrict]
    exact hgen (hTl l v)
  let T' : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M) := fun l =>
    Hs.subtype.comp (e.symm.toLinearMap.comp ((T l).codRestrict (LinearMap.range f) (hrange l)))
  have hT'mem : ∀ l v, T' l v ∈ Hs := fun l v => (e.symm _).2
  have hT'ev : ∀ l v, T' l v p0 = T l v := fun l v => by
    have := LinearEquiv.ofInjective_apply (h := hfi) f (e.symm ⟨T l v, hrange l v⟩)
    have h2 : e (e.symm ⟨T l v, hrange l v⟩) = ⟨T l v, hrange l v⟩ := e.apply_symm_apply _
    exact (this.symm.trans (congrArg Subtype.val h2))
  refine ⟨n, T', p, fun m v => hT'mem m v, fun m g hg hk v w hw u => ?_, fun m X hX v w hw u => ?_, ?_⟩
  · have h1 : T' m w = (rTrL V (atTau θ V τ g)).compMultilinearMap (T' m v) :=
      hinj _ (hT'mem m w) _ (IsPartMult.rTr_comp hθ hA (hT'mem m v) hτ ⟨hg, hk⟩) (by
        rw [hT'ev, LinearMap.compMultilinearMap_apply, hT'ev]
        exact (hT m).mapK g hg hk v w hw)
    rw [h1]
    rfl
  · have h1 : T' m w = GlobalTheory.CuspGKId.postRder (θ := θ) τ X hX (T' m v) (fun u => hsm _ ((hT'mem m v).mem u)) :=
      hinj _ (hT'mem m w) _ (IsPartMult.postRder_comp hθ hA hsm (hT'mem m v) hτ hX) (by
        rw [hT'ev]
        show T m w = Rder θ V τ X (T' m v p0)
        rw [hT'ev]
        exact (hT m).mapLie X hX v w hw)
    rw [h1]
    rfl
  · refine hinj _ hF _ (Hs.sum_mem fun m _ => hT'mem m (p m)) ?_
    rw [MultilinearMap.sum_apply]
    simp only [hT'ev]
    exact hsum
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`. Set `F : MMK M` to `(MultilinearMap.mkPiRing ℂ D.what₂.Tau f).compLinearMap lam`. Establish `hFu : ∀ u : Tup M, F u = (∏ τ, lam τ (u τ)) • f` using `fun u => by`.

Simplify using `[F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]`. Use `Submodule.subset_span ⟨F, p0, ⟨fun u => by rw [hFu]; exact A.smul_mem _ hf, fun τ h => absurd h (Finset.notMem_empty τ), fun τ h => absurd h (Finset.notMem_empty τ), fun τ _ u w => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hFu, hFu, smul_smul]`. Use `congr 1`. Establish `h1 : ∀ w' : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), (∏ τ', lam τ' (Function.update u τ w' τ')) = lam τ w' * ∏ τ' ∈ Finset.univ.erase τ, lam τ' (u τ')`.

Introduce `w'`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ' h' => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase h')]`.

Rewrite using `[h1, h1, hlam, one_mul]`. Rewrite using `[hFu, Finset.prod_congr rfl (fun τ _ => hlam τ), Finset.prod_const_one, one_smul]`. Consider the case `insert τ s hτ ih`. Use `ih.trans (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `y ⟨F, u, hF, rfl⟩`.

Take `⟨n, T, q, hT, hK, hL, hsum⟩` from `_root_.GlobalTheory.CuspGKId.IsPartMult.partialMultiplicity_decomposition hPr hθ hA hAf hp0 hsimple hF hτ`. Rewrite using `[hsum, MultilinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Establish `h1 : T m (q m) u = lam τ (u τ) • glue τ (T m) (p0 τ) (Function.update u τ (q m))`. Rewrite using `[glue_apply, Function.update_self, Function.update_idem, ← (hT m (q m)).other τ hτ u (u τ), Function.update_eq_self]`.

Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, isPartMult_glue hτ (hT m) (hK m) (hL m), rfl⟩)`.
-/
theorem mem_span_partialMultiplicity (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hAf : ∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f)
    {p0 : Tup M} {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} (hp0 : ∀ τ, p0 τ ≠ 0)
    (hlam : ∀ τ, lam τ (p0 τ) = 1)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    (s : Finset D.what₂.Tau) :
    A ≤ Submodule.span ℂ {y | ∃ (F : MMK M) (u : Tup M), IsPartMult θ M A s p0 lam F ∧ y = F u} := by
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    let F : MMK M := (MultilinearMap.mkPiRing ℂ D.what₂.Tau f).compLinearMap lam
    have hFu : ∀ u : Tup M, F u = (∏ τ, lam τ (u τ)) • f := fun u => by
      simp [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]
    refine Submodule.subset_span ⟨F, p0, ⟨fun u => by rw [hFu]; exact A.smul_mem _ hf,
      fun τ h => absurd h (Finset.notMem_empty τ), fun τ h => absurd h (Finset.notMem_empty τ),
      fun τ _ u w => ?_⟩, ?_⟩
    · rw [hFu, hFu, smul_smul]
      congr 1
      have h1 : ∀ w' : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
          (∏ τ', lam τ' (Function.update u τ w' τ')) = lam τ w' * ∏ τ' ∈ Finset.univ.erase τ, lam τ' (u τ') := by
        intro w'
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun τ' h' => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase h')]
      rw [h1, h1, hlam, one_mul]
    · rw [hFu, Finset.prod_congr rfl (fun τ _ => hlam τ), Finset.prod_const_one, one_smul]
  | insert τ s hτ ih =>
    refine ih.trans (Submodule.span_le.2 ?_)
    rintro y ⟨F, u, hF, rfl⟩
    obtain ⟨n, T, q, hT, hK, hL, hsum⟩ := _root_.GlobalTheory.CuspGKId.IsPartMult.partialMultiplicity_decomposition hPr hθ hA hAf hp0 hsimple hF hτ
    rw [hsum, MultilinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    have h1 : T m (q m) u = lam τ (u τ) • glue τ (T m) (p0 τ) (Function.update u τ (q m)) := by
      rw [glue_apply, Function.update_self, Function.update_idem, ← (hT m (q m)).other τ hτ u (u τ),
        Function.update_eq_self]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, isPartMult_glue hτ (hT m) (hK m) (hL m), rfl⟩)
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
/- English proof (translation)
Introduce `hPr D θ V S M hθ A hA hAf`. Establish `hA1` using `hA.1`. Establish `hst` using `fun τ => _root_.GlobalTheory.CuspGKId.cuspForm_kFinite_structure hPr V S M τ`. Use `choose p0 hp0 using fun τ => (hst τ).1`. Establish `hl : ∀ τ, ∃ l : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ, l (p0 τ) = 1`.

Introduce `τ`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), φ (p0 τ) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hp0 τ ((Module.forall_dual_apply_eq_zero_iff ℂ (p0 τ)).1 h)`.

Conclude with `⟨(φ (p0 τ))⁻¹ • φ, by simp [hφ]⟩`. Use `choose lam hlam using hl`. Establish `hsimple` using `fun τ => (hst τ).2.2.2`. Use `(_root_.GlobalTheory.CuspGKId.mem_span_partialMultiplicity hPr hθ hA1 hAf (p0 := p0) (lam := lam) hp0 hlam hsimple Finset.univ).trans ?_` and prove the remaining obligations. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨F, u, hF, rfl⟩`. Use `⟨F, u, ⟨fun v => (hAf _ (hF.mem v)).1, fun v => (hAf _ (hF.mem v)).2.1, fun τ => hF.equivK τ (Finset.mem_univ τ), fun τ => hF.equivLie τ (Finset.mem_univ τ)⟩, rfl⟩` and prove the remaining obligations.
-/
theorem le_multiplicitySpan_cuspForm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ A : Submodule ℂ (GA D V → ℂ), GlobalTheory.CuspGK.IsIrrGKSub θ M A → (∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) →
    A ≤ GlobalTheory.CuspGK.multSpan θ M := by
  intro hPr D θ V S M hθ A hA hAf
  have hA1 := hA.1
  have hst := fun τ => _root_.GlobalTheory.CuspGKId.cuspForm_kFinite_structure hPr V S M τ
  choose p0 hp0 using fun τ => (hst τ).1
  have hl : ∀ τ, ∃ l : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ, l (p0 τ) = 1 := by
    intro τ
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), φ (p0 τ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0 τ ((Module.forall_dual_apply_eq_zero_iff ℂ (p0 τ)).1 h)
    exact ⟨(φ (p0 τ))⁻¹ • φ, by simp [hφ]⟩
  choose lam hlam using hl
  have hsimple := fun τ => (hst τ).2.2.2
  refine (_root_.GlobalTheory.CuspGKId.mem_span_partialMultiplicity hPr hθ hA1 hAf (p0 := p0) (lam := lam) hp0 hlam hsimple Finset.univ).trans ?_
  refine Submodule.span_mono ?_
  rintro y ⟨F, u, hF, rfl⟩
  refine ⟨F, u, ⟨fun v => (hAf _ (hF.mem v)).1, fun v => (hAf _ (hF.mem v)).2.1,
    fun τ => hF.equivK τ (Finset.mem_univ τ), fun τ => hF.equivLie τ (Finset.mem_univ τ)⟩, rfl⟩
end GlobalTheory.CuspGKId
end
end
end
end
end
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm | exact _root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm | (intros; apply _root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cuspForm_gK_isotypic_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ A : Submodule ℂ (GA D V → ℂ), GlobalTheory.CuspGK.IsIrrGKSub θ M A → (∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) →
    A ≤ GlobalTheory.CuspGK.multSpan θ M := by
  first | exact @_root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm | exact _root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm | (intros; apply _root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm <;> assumption)
end
