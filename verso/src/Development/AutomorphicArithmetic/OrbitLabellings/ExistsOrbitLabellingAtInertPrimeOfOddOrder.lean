import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
import Development.AutomorphicArithmetic.OrbitLabellings.RowLab

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth UpperTheory.G2 NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Split into cases according to the possible forms of the given data. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_orbit_labelling_at_inert_prime_of_odd_order :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv)
    (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl →
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    V.l = resCharOf la → V.l ≠ 2 → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) →
    N.cls V.l = PrimeClass.inertClass → Odd (N.ordP V.l) → ∀ (j : ℕ) (Z : Finset (RPl N.R)), RF.IsReps (parOf N j V.l) Z → ∀ n j₁ j₂ : ℕ,
    ∃ lab : Formalism.L2.FormalSeriesBounds.LabS E C {z // z ∈ Z} (2 * N.ordP V.l), LabSArith V io ι lab ∧
      lab.hd = (N.ordP V.l : ZMod (2 * N.ordP V.l)) ∧ lab.n = n ∧ lab.j = j₁ ∧ lab.j' = j₂ ∧
      (∀ o g s, lab.big o g s ↔ (Even s.val ↔ g = 0)) ∧
      (∀ o s, lab.tau o s = if Even s.val then pl (N.pos V.l o.1 s.val) else ComplexEmbedding.conjugate (pl (N.pos V.l o.1 s.val))) ∧
      Function.Surjective (fun x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l) => lab.tau x.1 x.2) ∧ ¬ (V.l : ℤ) ∣ NumberField.discr E := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ _ V ι hι hc hl h2 hla hC ho j Z hZ n j₁ j₂
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E := by
    have h := hC
    unfold NumDatum.cls primeClass at h
    refine hP.unr _ V.l_prime (fun h2 => ?_) (fun hq => ?_) (fun hd => ?_)
    · rw [if_pos h2] at h
      cases h
    · rw [if_pos hq] at h
      split_ifs at h
    · rw [if_pos hd] at h
      split_ifs at h
  have hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
      emA3 io ι (pl w) x ^ V.l) := by
    intro w x
    obtain ⟨y, hy, e⟩ := hP.frob la (Or.inl (hl ▸ hC)) w x
    have := hla y hy
    rw [e, ← hl, map_sub, map_sub, map_pow, map_pow] at this
    exact this
  obtain ⟨lab, h1, h3, h4, h5, h6, h7, h8, h9⟩ :=
    UpperTheory.G2.RowLab.exists_lab c N pl hP.inj hP.psi T io C V ι hι hc h2 hunr hf ho Z hZ n j₁ j₂
  exact ⟨lab, h1, h3, h4, h5, h6, h7, h8, h9, hunr⟩
