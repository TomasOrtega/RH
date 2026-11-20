import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def wSum {Z : Scheme.{0}} {ι : Type} (w : ι → Wt Z) (m : ι → ℤ) (s : Finset ι) : Wt Z :=
  fun Ω _ _ z => ∑ a ∈ s, m a * w a Ω z

/- English proof (translation)
Introduce `hT hW hV q _ n i Z S p _ ι _ w m hw hq D hD hz x`. Take `⟨hTa, hTs, -⟩` from `hT q n i`. Take `⟨hWa, hWs, -⟩` from `hW`. Establish `h0 : wSum w m ∅ = Wt.const Z 0`. Use function extensionality and compare the values at `Ω _ _ z`.

Simplify using `[wSum, Wt.const]`. Establish `hc : ∀ y : Ht q (sch.obj Z) n i, tr p (Wt.const Z 0) q n i y = 0`. Introduce `y`. Establish `hs : Wt.smul 0 (Wt.const Z 0) = Wt.const Z 0`. Use function extensionality and compare the values at `Ω _ _ z`.

Simplify using `[Wt.smul, Wt.const]`. Rewrite using `[← hs, hTs p 0 _ (isWt_zero p) hq y, zero_smul]`. Establish `hins : ∀ (a : ι) (s : Finset ι), a ∉ s → wSum w m (insert a s) = (Wt.smul (m a) (w a)).add (wSum w m s)`. Introduce `a s ha`. Use function extensionality and compare the values at `Ω _ _ z`.

Simplify using `[wSum, Wt.add, Wt.smul, Finset.sum_insert ha]`. Establish `key : ∀ s : Finset ι, IsWt p (wSum w m s) ∧ ∀ y, tr p (wSum w m s) q n i y = ∑ a ∈ s, m a • tr p (w a) q n i y`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Rewrite using `[h0]`. Conclude with `⟨isWt_zero p, fun y => by rw [hc y, Finset.sum_empty]⟩`. Consider the case `insert a s ha ih`. Rewrite using `[hins a s ha]`. Establish `h1` using `hWs p (m a) (w a) (hw a)`.

Use `⟨hWa p _ _ h1 ih.1, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hTa p _ _ h1 ih.1 hq y, hTs p _ _ (hw a) hq y, ih.2 y, Finset.sum_insert ha]`. Establish `hzero : wSum w m Finset.univ = Wt.const Z 0` using `hV p _ (key Finset.univ).1 D hD fun Ω _ _ z hz' => hz Ω z hz'`. Rewrite using `[← (key Finset.univ).2 x, hzero, hc x]`.
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
