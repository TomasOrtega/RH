import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPoint

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ValGroup

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem exists_log {K : Type} [Field K] (w : AbsoluteValue K ℝ) (x : K) :
    ∃ a : K, a ≠ 0 ∧ Real.log (w x) = Real.log (w a) := by
  by_cases h : x = 0
  · exact ⟨1, one_ne_zero, by simp [h]⟩
  · exact ⟨x, h, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_log_sub {K : Type} [Field K] (w : AbsoluteValue K ℝ) (x x' : K) :
    ∃ a : K, a ≠ 0 ∧ Real.log (w x') - Real.log (w x) = Real.log (w a) := by
  obtain ⟨a, ha, h⟩ := exists_log w x
  obtain ⟨b, hb, h'⟩ := exists_log w x'
  refine ⟨b / a, div_ne_zero hb ha, ?_⟩
  rw [h, h', map_div₀, Real.log_div (w.ne_zero hb) (w.ne_zero ha)]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem nonempty_algPt {F : Type} [Field F] [NumberField F] (Y : Var F) : Nonempty (AlgPt Y) := by
  have hP : IsProper Y.str := by
    have := isProper_str F Y.N
    change IsProper (Y.I.subschemeι ≫ PSpace.str F Y.N)
    infer_instance
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.str
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (X := Y.X) Set.univ_nonempty
  obtain ⟨⟨y, -⟩⟩ := ((ExtConj.main F).2.1 Y x hx).1
  exact ⟨y⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L L' : HermLB M.p) (k : ℕ+) (cf cf' : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M L' k cf' → ∀ v : HeightOneSpectrum (𝓞 F), ∃ (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 ∧ ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v) = Real.log (e.w α) := by
  intro F _ _ C Y A M L L' k cf cf' ⟨_, r, _, _, h⟩ ⟨_, r', _, _, h'⟩ v
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  obtain ⟨y⟩ := nonempty_algPt Y
  obtain ⟨yt, hyt, hU⟩ := exists_valuationRing_point F Y M v e y
  have chart (B : HermLB M.p) : ∃ i, yt (IsLocalRing.closedPoint e.O) ∈ B.B.U i :=
    Opens.mem_iSup.1 (B.isLB.cover.ge (Set.mem_univ _))
  obtain ⟨i, hi⟩ := chart L
  obtain ⟨i', hi'⟩ := chart L'
  have h₁ := h v e y yt (fun _ => i) hyt (hU _ hi).1
  have h₂ := h' v e y yt (fun _ => i') hyt (hU _ hi').1
  obtain ⟨a, ha, h₃⟩ := exists_log_sub e.w
    (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r (fun _ => i) : Y.Fnˣ) : Y.Fn))
    (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r' (fun _ => i') : Y.Fnˣ) : Y.Fn))
  refine ⟨e, a, ha, ?_⟩
  rw [← h₃]
  linarith

end GlobalTheory.TrueGeo.ValGroup
