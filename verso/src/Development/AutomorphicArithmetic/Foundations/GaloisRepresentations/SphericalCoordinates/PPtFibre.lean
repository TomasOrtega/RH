import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Set `Y : Over X` to `Over.mk (a ≫ (GlobalTheory.KS.pow A k).hom)`. Set `fa : Y ⟶ GlobalTheory.KS.pow A k` to `Over.homMk a rfl`. Set `fb : Y ⟶ GlobalTheory.KS.pow A k` to `Over.homMk b h0.symm`. Establish `hab : fa = fb`. Unfold `GlobalTheory.KS.pow at fa fb ⊢`.

Apply `Limits.Pi.hom_ext` to reduce the goal to its premises. Introduce `j`. Use `ext`. Simplify using `only [Over.comp_left, Over.homMk_left, fa, fb]`. Conclude with `h j`.

Conclude with `congrArg (fun f => f.left) hab`.
-/
private theorem pow_map_ext {X : Scheme.{0}} {A : Over X} {k : ℕ} {T : Scheme.{0}}
    (a b : T ⟶ (GlobalTheory.KS.pow A k).left) (h0 : a ≫ (GlobalTheory.KS.pow A k).hom = b ≫ (GlobalTheory.KS.pow A k).hom)
    (h : ∀ j, a ≫ (GlobalTheory.KS.pr A j).left = b ≫ (GlobalTheory.KS.pr A j).left) : a = b := by
  let Y : Over X := Over.mk (a ≫ (GlobalTheory.KS.pow A k).hom)
  let fa : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk a rfl
  let fb : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk b h0.symm
  have hab : fa = fb := by
    unfold GlobalTheory.KS.pow at fa fb ⊢
    apply Limits.Pi.hom_ext
    intro j
    ext
    simp only [Over.comp_left, Over.homMk_left, fa, fb]
    exact h j
  exact congrArg (fun f => f.left) hab

section
variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D : PLat O bar}
  {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {A : Over X} [GrpObj A] (S : Sheet s A D ρ) (k : ℕ)

/- English proof (translation)
The claim follows from `Over.w (Pi.lift (fun j => S.ex P (z j)) : Over.mk (S.u P) ⟶ GlobalTheory.KS.pow A k)`.
-/
private theorem pt_hom (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) :
    S.pt k P z ≫ (GlobalTheory.KS.pow A k).hom = S.u P :=
  Over.w (Pi.lift (fun j => S.ex P (z j)) : Over.mk (S.u P) ⟶ GlobalTheory.KS.pow A k)

/- English proof (translation)
Unfold `Sheet.pt GlobalTheory.KS.pr`. Rewrite using `[← Over.comp_left, Limits.Pi.lift_π]`.
-/
private theorem pt_pr (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) (j : Fin k) :
    S.pt k P z ≫ (GlobalTheory.KS.pr A j).left = (S.ex P (z j)).left := by
  unfold Sheet.pt GlobalTheory.KS.pr
  rw [← Over.comp_left, Limits.Pi.lift_π]

/- English proof (translation)
Establish `h` using `S.exp P hP`. Unfold `IsExp at h`. Establish `e` using `h.1 (a - b) b`. Rewrite `e` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
private theorem ex_sub (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ρ P) (a b : Fin g → ℂ) :
    S.ex P a = S.ex P (a - b) * S.ex P b := by
  have h := S.exp P hP
  unfold IsExp at h
  have e := h.1 (a - b) b
  rwa [sub_add_cancel] at e

end

/- English proof (translation)
Introduce `O _ bar g ρ D X s A _ S k P hP`. Establish `hE` using `S.exp P hP`. Unfold `IsExp at hE`. Establish `hu : ∀ (P' : D.La →+ (Fin g → ℂ)) (w : Fin g → ℂ), (S.ex P' w).left ≫ A.hom = S.u P'` using `fun P' w => Over.w (S.ex P' w)`. Use `⟨fun z => pt_hom S k P z, fun z j => pt_pr S k P z j, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Establish `hc : ∀ j : Fin k, ∃ w, S.ex P w = Over.homMk (U` using `Over.mk (S.u P)) (V := A) (y ≫ (GlobalTheory.KS.pr A j).left) (by show _ = S.u P`. Rewrite using `[Category.assoc, Over.w]`. Conclude with `hy) := fun j => hE.2.1 _`. Use `choose z hz using hc`.

Use `⟨z, pow_map_ext _ _ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hy, pt_hom]`. Introduce `j`. Rewrite using `[pt_pr, hz j]`. Both sides reduce to the same expression.

Introduce `z z'`. Prove the components needed by the constructor for the conclusion. Introduce `heq j`. Establish `e1 : (S.ex P (z j)).left = (S.ex P (z' j)).left`. Rewrite using `[← pt_pr S k P z j, ← pt_pr S k P z' j, heq]`.

Establish `e2 : S.ex P (z j) = S.ex P (z' j)` using `Over.OverMorphism.ext e1`. Establish `e3 : S.ex P (z j - z' j) = 1`. Establish `e4` using `ex_sub S P hP (z j) (z' j)`. Rewrite `e4` using `[e2]`. Conclude with `mul_eq_right.mp e4.symm`.

Conclude with `(S.ker P hP _).mp e3`. Introduce `hr`. Apply `pow_map_ext` to reduce the goal to its premises. Rewrite using `[pt_hom, pt_hom]`. Introduce `j`.

Rewrite using `[pt_pr, pt_pr, ex_sub S P hP (z j) (z' j), (S.ker P hP _).mpr (hr j), _root_.one_mul]`. Introduce `P' h hP' hx z`. Establish `hu' : S.u P' = S.u P`. Combine the equalities or inequalities in the displayed calculation. Apply `pow_map_ext` to reduce the goal to its premises.

Rewrite using `[pt_hom, pt_hom, hu']`. Introduce `j`. Rewrite using `[pt_pr, pt_pr]`. Conclude with `S.lin P P' h hP hP' hx (z j)`.
-/
theorem UpperTheory.Gal.W2.ptFibre_of :
    UpperTheory.Gal.W2.PtFibre := by
  intro O _ bar g ρ D X s A _ S k P hP
  have hE := S.exp P hP
  unfold IsExp at hE
  have hu : ∀ (P' : D.La →+ (Fin g → ℂ)) (w : Fin g → ℂ), (S.ex P' w).left ≫ A.hom = S.u P' :=
    fun P' w => Over.w (S.ex P' w)
  refine ⟨fun z => pt_hom S k P z, fun z j => pt_pr S k P z j, ?_, ?_, ?_⟩
  · intro y hy
    have hc : ∀ j : Fin k, ∃ w, S.ex P w =
        Over.homMk (U := Over.mk (S.u P)) (V := A) (y ≫ (GlobalTheory.KS.pr A j).left) (by
          show _ = S.u P
          rw [Category.assoc, Over.w]
          exact hy) := fun j => hE.2.1 _
    choose z hz using hc
    refine ⟨z, pow_map_ext _ _ ?_ ?_⟩
    · rw [hy, pt_hom]
    · intro j
      rw [pt_pr, hz j]
      rfl
  · intro z z'
    constructor
    · intro heq j
      have e1 : (S.ex P (z j)).left = (S.ex P (z' j)).left := by
        rw [← pt_pr S k P z j, ← pt_pr S k P z' j, heq]
      have e2 : S.ex P (z j) = S.ex P (z' j) := Over.OverMorphism.ext e1
      have e3 : S.ex P (z j - z' j) = 1 := by
        have e4 := ex_sub S P hP (z j) (z' j)
        rw [e2] at e4
        exact mul_eq_right.mp e4.symm
      exact (S.ker P hP _).mp e3
    · intro hr
      apply pow_map_ext
      · rw [pt_hom, pt_hom]
      · intro j
        rw [pt_pr, pt_pr, ex_sub S P hP (z j) (z' j), (S.ker P hP _).mpr (hr j), _root_.one_mul]
  · intro P' h hP' hx z
    have hu' : S.u P' = S.u P := by
      calc S.u P' = (S.ex P' (h 0)).left ≫ A.hom := (hu P' (h 0)).symm
        _ = (S.ex P 0).left ≫ A.hom := by rw [S.lin P P' h hP hP' hx 0]
        _ = S.u P := hu P 0
    apply pow_map_ext
    · rw [pt_hom, pt_hom, hu']
    · intro j
      rw [pt_pr, pt_pr]
      exact S.lin P P' h hP hP' hx (z j)
