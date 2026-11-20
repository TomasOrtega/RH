import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaximalIsotropicDoubled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Graphs

variable {D : D7}

def graphSub (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearMap.range (LinearMap.prod LinearMap.id (Matrix.mulVecLin c))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem mem_graphSub {W : HSp D} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    {y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)} : y ∈ graphSub W c ↔ y.2 = c *ᵥ y.1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨y.1, Prod.ext rfl (by simp [h])⟩

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression.
-/
theorem cT_eq (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) c = cᴴ := by
  funext i j
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem star_dot (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

def graphLag (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : Lag W :=
  ⟨graphSub W g, by
    rw [graphSub, LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
        W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    rw [cT_eq] at h
    show star x ⬝ᵥ W.gram *ᵥ y = star ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x) ⬝ᵥ
      W.gram *ᵥ ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ y)
    rw [star_dot, h]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem graphLag_bot (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    (graphLag W g hg).1.comap (LinearMap.inl D.host.E _ _) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h : (0 : Fin W.rank → D.host.E) = (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x :=
    mem_graphSub.1 (Submodule.mem_comap.1 hx)
  have h2 := congrArg (((g⁻¹ : GL (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ ·) h
  simpa [Matrix.mulVec_mulVec] using h2.symm

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem herm' (W : HSp D) : W.gramᵀ.map (starRingAut : D.host.E ≃+* D.host.E) = W.gram := by
  have h := GlobalTheory.AutFunCounterexample.gram_herm W
  funext i j
  exact congrFun (congrFun h i) j

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ g : GL (Fin W.rank) D.host.E,
    g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧ Formalism.UG.bc (incA D) g = matHom W (γ : GA D W) := by
  have h : matHom W (γ : GA D W) ∈ HFin (AF D.host.F) D.sp.cm.sig W.gram := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 h
  exact ⟨g, hg, e⟩

def ratG (W : HSp D) (γ : GQ W) : GL (Fin W.rank) D.host.E := (exists_rat W γ).choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ratG_mem (W : HSp D) (γ : GQ W) :
    ratG W γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := (exists_rat W γ).choose_spec.1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mt_ratG (W : HSp D) (γ : GQ W) :
    Formalism.L2.Theta.mt W (γ : GA D W) = (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) := by
  rw [Formalism.L2.Theta.mt, ← (exists_rat W γ).choose_spec.2]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bc_injective (W : HSp D) {g g' : GL (Fin W.rank) D.host.E}
    (h : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) =
      (g' : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) : g = g' := by
  exact Units.ext (Matrix.ext fun i j => incA_injective D (congrFun (congrFun h i) j))

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem graphSub_injective (W : HSp D) {c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : graphSub W c = graphSub W c') : c = c' := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hx : (x, c *ᵥ x) ∈ graphSub W c' := h ▸ mem_graphSub.2 rfl
  exact mem_graphSub.1 hx

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem isLagFrame_graph (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    IsLagFrame W (graphLag W g hg) (1, (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)) := by
  have h := congrArg (Submodule.map (LinearMap.prod (LinearMap.id : (Fin W.rank → D.host.E) →ₗ[D.host.E] _)
    (Matrix.mulVecLin (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E))))
    (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  refine Eq.trans ?_ h
  congr 2
  funext j
  ext a <;> simp [Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hr_mem (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
  show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
      ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      W.gram.map (inclR (F := D.host.F) (AF D.host.F)) *
      (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) =
      W.gram.map (inclR (F := D.host.F) (AF D.host.F))
  rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, h]

def ofRat (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : GQ W :=
  ⟨(⟨Formalism.UG.bc (incA D) g, hr_mem W g hg⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram),
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

end GlobalTheory.RawLift.Graphs

namespace GlobalTheory.RawLift.Graphs

open GlobalTheory.RawLift.Graphs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem graphs : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  intro D W
  let f : GQ W → {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} :=
    fun γ => ⟨graphLag W (ratG W γ) (ratG_mem W γ), graphLag_bot W _ _⟩
  have hinj : Function.Injective f := by
    intro γ γ' h
    have h1 : graphSub W (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = graphSub W (ratG W γ') :=
      congrArg (fun Y => Y.1.1) h
    have h2 := graphSub_injective W h1
    have h3 : Formalism.L2.Theta.mt W (γ : GA D W) = Formalism.L2.Theta.mt W (γ' : GA D W) := by
      rw [mt_ratG, mt_ratG, h2]
    exact Subtype.ext (GlobalTheory.AutFunCounterexample.GA_ext W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨g, hgU, hgY⟩ := ((GlobalTheory.Doubling.maximal_isotropic_doubled D.host.E starRingAut W.rank W.gram
      (fun x => star_star x) (GlobalTheory.AutFunCounterexample.gram_det_ne W) (herm' W) Y.1 Y.2.1 Y.2.2).2.2).1 hY
    have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := hgU
    refine ⟨ofRat W g hg, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : ratG W (ofRat W g hg) = g := bc_injective W ((mt_ratG W _).symm.trans rfl)
    show graphSub W (ratG W (ofRat W g hg)) = Y.1
    rw [e1]
    ext y
    rw [mem_graphSub]
    exact (hgY y).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ⟨_, mt_ratG W γ, isLagFrame_graph W _ (ratG_mem W γ)⟩⟩

end GlobalTheory.RawLift.Graphs
