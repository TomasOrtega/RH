import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def wSum {Z : Scheme.{0}} {ι : Type} (w : ι → Wt Z) (m : ι → ℤ) (s : Finset ι) : Wt Z :=
  fun Ω _ _ z => ∑ a ∈ s, m a * w a Ω z

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trRel_of :
    TrLin → WtLin → WtVanish → TrRel := by
  intro hT hW hV q _ n i Z S p _ ι _ w m hw hq D hD hz x
  classical
  obtain ⟨hTa, hTs, -⟩ := hT q n i
  obtain ⟨hWa, hWs, -⟩ := hW
  have h0 : wSum w m ∅ = Wt.const Z 0 := by
    funext Ω _ _ z
    simp [wSum, Wt.const]
  have hc : ∀ y : Ht q (sch.obj Z) n i, tr p (Wt.const Z 0) q n i y = 0 := by
    intro y
    have hs : Wt.smul 0 (Wt.const Z 0) = Wt.const Z 0 := by
      funext Ω _ _ z
      simp [Wt.smul, Wt.const]
    rw [← hs, hTs p 0 _ (isWt_zero p) hq y, zero_smul]
  have hins : ∀ (a : ι) (s : Finset ι), a ∉ s →
      wSum w m (insert a s) = (Wt.smul (m a) (w a)).add (wSum w m s) := by
    intro a s ha
    funext Ω _ _ z
    simp [wSum, Wt.add, Wt.smul, Finset.sum_insert ha]
  have key : ∀ s : Finset ι, IsWt p (wSum w m s) ∧
      ∀ y, tr p (wSum w m s) q n i y = ∑ a ∈ s, m a • tr p (w a) q n i y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [h0]
      exact ⟨isWt_zero p, fun y => by rw [hc y, Finset.sum_empty]⟩
    | insert a s ha ih =>
      rw [hins a s ha]
      have h1 := hWs p (m a) (w a) (hw a)
      refine ⟨hWa p _ _ h1 ih.1, fun y => ?_⟩
      rw [hTa p _ _ h1 ih.1 hq y, hTs p _ _ (hw a) hq y, ih.2 y, Finset.sum_insert ha]
  have hzero : wSum w m Finset.univ = Wt.const Z 0 :=
    hV p _ (key Finset.univ).1 D hD fun Ω _ _ z hz' => hz Ω z hz'
  rw [← (key Finset.univ).2 x, hzero, hc x]
