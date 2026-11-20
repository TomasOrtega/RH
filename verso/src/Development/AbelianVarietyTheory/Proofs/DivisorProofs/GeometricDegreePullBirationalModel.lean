import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

/- English proof (translation)
The claim follows from `HermLB.isometric_of_eqOn fun σ a y _ => by exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm`.
-/
theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

/- English proof (translation)
Introduce `hC k _ X Y _ _ p q D hX hY π hπ φ hM L`. Establish `hdeg : π.residueDegree (genericPoint Y) ≠ 0` using `by rw [hM.deg]; exact one_ne_zero`. Establish `hP` using `((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)`. Establish `hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a` using `fun M a h => by`. Use `hP M a h` as an intermediate fact.

Rewrite `this` using `[hM.deg, Nat.cast_one, one_mul]`. Then use the resulting hypothesis. Establish `hS` using `hC.arShift`. Establish `hg : gdeg (L.pull π hπ) D = gdeg L D`. Take `⟨h, hh⟩` from `((hC.arExists k X p D hX).1 L)`. Establish `ha : L.IsSelfInter (h (genericPoint X))` using `⟨h, hh, rfl⟩`.

Use `set a := h (genericPoint X)`. Establish `h1` using `hP1 _ _ (hS k X p D hX L a 1 ha)`. Establish `h1'` using `(isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1`. Establish `h2` using `hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)`. Establish `e` using `HermLB.IsSelfInter.unique hY h1' h2`.

Establish `hD : ((D : ℝ) + 1) ≠ 0` using `by positivity`. Establish `: ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D` using `by linarith`. Conclude with `(mul_left_cancel₀ hD this).symm`. Use `⟨hg, fun a t ha => ?_⟩` and prove the remaining obligations. Use `hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)` as an intermediate fact.

Rewrite `this` using `[hg]`. Then use the resulting hypothesis.
-/
theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
