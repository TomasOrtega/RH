import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct Pointwise

namespace GlobalTheory.ModuPiLocal

/- English proof (translation)
Use `letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)`. Use `haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩`. Set `μ : ∀ i, Measure (A i)` to `fun i => Measure.addHaar`. Set `S : ∀ i, TopologicalSpace.PositiveCompacts (A i)` to `fun i => Classical.choice inferInstance`. Establish `h0 : ∀ i, μ i (S i : Set (A i)) ≠ 0` using `fun i => (Measure.measure_pos_of_nonempty_interior (μ i) (S i).interior_nonempty).ne'`.

Establish `h1 : ∀ i, μ i (S i : Set (A i)) ≠ ⊤` using `fun i => (S i).isCompact.measure_lt_top.ne`. Establish `hp : ∀ T : ∀ i, Set (A i), (Measure.pi μ) (Set.univ.pi T) = ∏ i, μ i (T i)` using `fun T => Measure.pi_pi _ _`. Use `distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ) (s := Set.univ.pi fun i => (S i : Set (A i))) (by rw [hp]; exact Finset.prod_ne_zero_iff.2 fun i _ => h0 i) (by rw [hp]; exact ENNReal.prod_ne_top fun i _ => h1 i) ?_` and prove the remaining obligations. Establish `e : u • (Set.univ.pi fun i => (S i : Set (A i))) = Set.univ.pi fun i => Units.map (Pi.evalRingHom A i).toMonoidHom u • (S i : Set (A i))`. Use extensionality with `x`.

Simplify using `only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, forall_true_left]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Rewrite using `[e, hp, hp, ENNReal.coe_finset_prod, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[distribHaarChar_mul]`.
-/
theorem distribHaarChar_pi {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, T2Space (A i)] [∀ i, SecondCountableTopology (A i)] (u : (∀ i, A i)ˣ) :
    distribHaarChar (∀ i, A i) u = ∏ i, distribHaarChar (A i) (Units.map (Pi.evalRingHom A i).toMonoidHom u) := by
  classical
  letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)
  haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩
  let μ : ∀ i, Measure (A i) := fun i => Measure.addHaar
  let S : ∀ i, TopologicalSpace.PositiveCompacts (A i) := fun i => Classical.choice inferInstance
  have h0 : ∀ i, μ i (S i : Set (A i)) ≠ 0 := fun i =>
    (Measure.measure_pos_of_nonempty_interior (μ i) (S i).interior_nonempty).ne'
  have h1 : ∀ i, μ i (S i : Set (A i)) ≠ ⊤ := fun i => (S i).isCompact.measure_lt_top.ne
  have hp : ∀ T : ∀ i, Set (A i), (Measure.pi μ) (Set.univ.pi T) = ∏ i, μ i (T i) := fun T =>
    Measure.pi_pi _ _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := Set.univ.pi fun i => (S i : Set (A i)))
    (by rw [hp]; exact Finset.prod_ne_zero_iff.2 fun i _ => h0 i)
    (by rw [hp]; exact ENNReal.prod_ne_top fun i _ => h1 i) ?_
  have e : u • (Set.univ.pi fun i => (S i : Set (A i))) =
      Set.univ.pi fun i => Units.map (Pi.evalRingHom A i).toMonoidHom u • (S i : Set (A i)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [← map_inv]
    rfl
  rw [e, hp, hp, ENNReal.coe_finset_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [distribHaarChar_mul]

end GlobalTheory.ModuPiLocal

namespace GlobalTheory.ModuPiLocal

/- English proof (translation)
Introduce `F _ _ S x hx`. Rewrite using `[modu, dif_pos hx, distribHaarChar_pi (fun v : S => Fv F v.1), NNReal.coe_prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `hv : IsUnit (x v)` using `(Pi.isUnit_iff.1 hx) v`. Establish `h` using `GlobalTheory.GaugeProdFormula.modu_finite F v.1 (x v) hv.ne_zero`.

Rewrite `h` using `[modu, dif_pos hv]`. Rewrite using `[← h]`. Use `congr 2`. Use `ext`. Both sides reduce to the same expression.
-/
theorem modu_sPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  intro F _ _ S x hx
  rw [modu, dif_pos hx, distribHaarChar_pi (fun v : S => Fv F v.1), NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : IsUnit (x v) := (Pi.isUnit_iff.1 hx) v
  have h := GlobalTheory.GaugeProdFormula.modu_finite F v.1 (x v) hv.ne_zero
  rw [modu, dif_pos hv] at h
  rw [← h]
  congr 2
  ext
  rfl

end GlobalTheory.ModuPiLocal
