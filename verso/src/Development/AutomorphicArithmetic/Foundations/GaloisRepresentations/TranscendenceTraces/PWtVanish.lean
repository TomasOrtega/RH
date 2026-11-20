import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hIso hPt hEx hLift hFin Z S p _ w hw D hD hzero`. Use function extensionality and compare the values at `Ω _ _ z`. Use `show w Ω z = 0`. Take `⟨A, W, v, hEt, hW, hvW, hvz, huniq⟩` from `hIso p (pt z)`. Use `haveI : IsFinite A.r := A.finite`.

Set `φ : A.V → ℤ` to `fun y => if y ∈ W then 1 else 0`. Establish `hφ : IsLocallyConstant φ`. Use `IsLocallyConstant.iff_isOpen_fiber.2 ?_` and prove the remaining obligations. Introduce `n`. Distinguish the cases in `h1 : n = 1`.

Substitute `h1` using the available equality. Use `hW.isOpen using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y ∈ W <;> simp [φ, hy]`. Distinguish the cases in `h0 : n = 0`.

Substitute `h0` using the available equality. Use `hW.compl.isOpen using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y ∈ W <;> simp [φ, hy]`. Use `isOpen_empty using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y ∈ W <;> simp [φ, hy] <;> omega`. Take `⟨ψ, hψ, hψeq⟩` from `hw A φ hφ`. Establish `hsum : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v → ψ (A.r v) = w Ω z * ∑ᶠ z' ∈ fib A.r x1, φ (pt z')`. Introduce `Ω1 _ _ x1 hx1`.

Rewrite using `[← hx1, hψeq Ω1 x1, mul_finsum_mem]`. Apply `finsum_mem_congr rfl` to reduce the goal to its premises. Introduce `z' hz'`. Establish `hz'' : z' ≫ A.r = x1` using `hz'`. Distinguish the cases in `hW' : pt z' ∈ W`.

Establish `hr : A.r (pt z') = A.r v`. Rewrite using `[← pt_comp, hz'']`. Conclude with `hx1`. Establish `hv : pt z' = v` using `huniq _ hW' hr`. Establish `hwz : w Ω1 (z' ≫ A.v) = w Ω z` using `hPt p w hw Ω1 Ω (z' ≫ A.v) z (by rw [pt_comp, hv, hvz])`.

Simplify using `[φ, hW', hwz]`. Simplify using `[φ, hW']`. Establish `hpos : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v → 0 < ∑ᶠ z' ∈ fib A.r x1, φ (pt z')`. Introduce `Ω1 _ _ x1 hx1`. Take `⟨z1, hz1, hpz1⟩` from `hLift A.r Ω1 x1 v hx1.symm`.

Establish `hf` using `hFin A.r Ω1 x1`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hf]`. Establish `hmem : z1 ∈ hf.toFinset`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `hz1`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨Ω0, _, _, x0, hx0⟩` from `hEx A.U (A.r v)`. Establish `hO : IsOpen (ψ ⁻¹' {ψ (A.r v)})` using `hψ.isOpen_fiber _`. Establish `hopen` using `A.u.isOpenMap _ hO`. Take `⟨y, ⟨u1, hu1, rfl⟩, hyD⟩` from `hD.inter_open_nonempty _ hopen ⟨A.u (A.r v), A.r v, rfl, rfl⟩`.

Take `⟨Ω2, _, _, x2, hx2⟩` from `hEx A.U u1`. Establish `hψ1 : ψ u1 = 0`. Rewrite using `[← hx2, hψeq Ω2 x2]`. Apply `finsum_mem_of_eqOn_zero` to reduce the goal to its premises. Introduce `z' hz'`.

Establish `hz'' : z' ≫ A.r = x2` using `hz'`. Establish `hw0 : w Ω2 (z' ≫ A.v) = 0`. Apply `hzero Ω2` to reduce the goal to its premises. Establish `hc : (z' ≫ A.v) ≫ p = x2 ≫ A.u`. Rewrite using `[Category.assoc, A.pb.w, ← Category.assoc, hz'']`.

Rewrite using `[hc, pt_comp, hx2]`. Conclude with `hyD`. Simplify using `[hw0]`. Establish `hu1' : ψ u1 = ψ (A.r v)` using `hu1`. Establish `h1` using `hsum Ω0 x0 hx0`.

Establish `h2` using `hpos Ω0 x0 hx0`. Rewrite `h1` using `[← hu1', hψ1]`. Break down `mul_eq_zero.mp h1.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h h2.ne'`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtVanish_of :
    Isolate → WtPt → PtEx → PtLift → FibFin → WtVanish := by
  intro hIso hPt hEx hLift hFin Z S p _ w hw D hD hzero
  funext Ω _ _ z
  show w Ω z = 0
  obtain ⟨A, W, v, hEt, hW, hvW, hvz, huniq⟩ := hIso p (pt z)
  haveI : IsFinite A.r := A.finite
  classical
  let φ : A.V → ℤ := fun y => if y ∈ W then 1 else 0
  have hφ : IsLocallyConstant φ := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 ?_
    intro n
    by_cases h1 : n = 1
    · subst h1
      convert hW.isOpen using 1
      ext y
      by_cases hy : y ∈ W <;> simp [φ, hy]
    · by_cases h0 : n = 0
      · subst h0
        convert hW.compl.isOpen using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy]
      · convert isOpen_empty using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy] <;> omega
  obtain ⟨ψ, hψ, hψeq⟩ := hw A φ hφ
  have hsum : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      ψ (A.r v) = w Ω z * ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    rw [← hx1, hψeq Ω1 x1, mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro z' hz'
    have hz'' : z' ≫ A.r = x1 := hz'
    by_cases hW' : pt z' ∈ W
    · have hr : A.r (pt z') = A.r v := by
        rw [← pt_comp, hz'']
        exact hx1
      have hv : pt z' = v := huniq _ hW' hr
      have hwz : w Ω1 (z' ≫ A.v) = w Ω z :=
        hPt p w hw Ω1 Ω (z' ≫ A.v) z (by rw [pt_comp, hv, hvz])
      simp [φ, hW', hwz]
    · simp [φ, hW']
  have hpos : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      0 < ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    obtain ⟨z1, hz1, hpz1⟩ := hLift A.r Ω1 x1 v hx1.symm
    have hf := hFin A.r Ω1 x1
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have hmem : z1 ∈ hf.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hz1
    calc (0:ℤ) < φ (pt z1) := by simp [φ, hpz1, hvW]
      _ ≤ _ := Finset.single_le_sum (f := fun z' => φ (pt z'))
          (fun i _ => by by_cases hi : pt i ∈ W <;> simp [φ, hi]) hmem
  obtain ⟨Ω0, _, _, x0, hx0⟩ := hEx A.U (A.r v)
  have hO : IsOpen (ψ ⁻¹' {ψ (A.r v)}) := hψ.isOpen_fiber _
  have hopen := A.u.isOpenMap _ hO
  obtain ⟨y, ⟨u1, hu1, rfl⟩, hyD⟩ :=
    hD.inter_open_nonempty _ hopen ⟨A.u (A.r v), A.r v, rfl, rfl⟩
  obtain ⟨Ω2, _, _, x2, hx2⟩ := hEx A.U u1
  have hψ1 : ψ u1 = 0 := by
    rw [← hx2, hψeq Ω2 x2]
    apply finsum_mem_of_eqOn_zero
    intro z' hz'
    have hz'' : z' ≫ A.r = x2 := hz'
    have hw0 : w Ω2 (z' ≫ A.v) = 0 := by
      apply hzero Ω2
      have hc : (z' ≫ A.v) ≫ p = x2 ≫ A.u := by
        rw [Category.assoc, A.pb.w, ← Category.assoc, hz'']
      rw [hc, pt_comp, hx2]
      exact hyD
    simp [hw0]
  have hu1' : ψ u1 = ψ (A.r v) := hu1
  have h1 := hsum Ω0 x0 hx0
  have h2 := hpos Ω0 x0 hx0
  rw [← hu1', hψ1] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h h2.ne'
