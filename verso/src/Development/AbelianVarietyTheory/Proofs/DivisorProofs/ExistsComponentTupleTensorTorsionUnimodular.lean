import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `h0` using `GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hf 0`. Establish `he0 : ∀ j, e 0 j = 0` using `fun j => by`. Use `hf.2.2.1 0 0 j` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Simplify using `using this`. Establish `e1 : (1 : Fin r → N.Gt) = fun j => N.io (e 0 j)` using `funext fun j => by rw [he0, N.io_zero]; rfl`. Rewrite using `[pow_zero, pow_zero, e1, ← N'.io_zero]`. Conclude with `h0`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ]`. Conclude with `GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hf _ _ _ _ ih h`.
-/
theorem gtRelV_npow_of_tensFacts {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hf : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hf 0
    have he0 : ∀ j, e 0 j = 0 := fun j => by
      have := hf.2.2.1 0 0 j
      rw [add_zero] at this
      simpa using this
    have e1 : (1 : Fin r → N.Gt) = fun j => N.io (e 0 j) := funext fun j => by rw [he0, N.io_zero]; rfl
    rw [pow_zero, pow_zero, e1, ← N'.io_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hf _ _ _ _ ih h

/- English proof (translation)
Introduce `R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p'`. Establish `hGt` using `GlobalTheory.Ex.GtValues.points_correspond`. Establish `hf` using `GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'`. Take `⟨q', hq', -⟩` from `((hGt R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).1 p'`. Take `⟨vs, hvs⟩` from `GlobalTheory.T.exists_torus_components_of_unimodular_tensor F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW q'.1.2`.

Establish `hk` using `gtRelV_npow_of_tensFacts hf hvs k`. Rewrite `hk` using `[N'.mem_QT.1 q'.2]`. Establish `hio` using `GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf q'.1.1.toAdd`. Establish `hv` using `GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW _ _ _ hk hio`. Set `qs : Fin r → N.QT k` to `fun j => ⟨(Multiplicative.ofAdd (chi T ν ν' q'.1.1.toAdd j), vs j), N.mem_QT.2 (congrFun hv j)⟩`.

Use `choose ps hps using fun j => ((hGt R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.1 (qs j)`. Conclude with `⟨ps, q', qs, hq', hps, fun _ => rfl, hvs⟩`.
-/
theorem exists_components_of_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hf := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  obtain ⟨q', hq', -⟩ := ((hGt R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).1 p'
  obtain ⟨vs, hvs⟩ := GlobalTheory.T.exists_torus_components_of_unimodular_tensor F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW q'.1.2
  have hk := gtRelV_npow_of_tensFacts hf hvs k
  rw [N'.mem_QT.1 q'.2] at hk
  have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf q'.1.1.toAdd
  have hv := GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW _ _ _ hk hio
  let qs : Fin r → N.QT k := fun j =>
    ⟨(Multiplicative.ofAdd (chi T ν ν' q'.1.1.toAdd j), vs j), N.mem_QT.2 (congrFun hv j)⟩
  choose ps hps using fun j => ((hGt R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.1 (qs j)
  exact ⟨ps, q', qs, hq', hps, fun _ => rfl, hvs⟩

end GlobalTheory.Mum.TensTor
