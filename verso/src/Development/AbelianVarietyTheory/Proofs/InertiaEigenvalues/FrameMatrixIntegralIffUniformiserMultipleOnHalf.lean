import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumIntegralDivUniformisersIffReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfUniInt

/- English proof (translation)
Introduce `D S T βS βT Q e he ϖ hϖ hQ x hx`. Take `⟨⟨es, hes, rfl⟩, hc⟩` from `he`. Use `set M := frMapO S T βS βT x with hM`. Use `set a : EAf D := toEAf D (incA D (ϖ : D.host.E)) with ha_def`. Establish `hxm : (x.map fun w => incA D (ϖ : D.host.E) * w) = incA D (ϖ : D.host.E) • x`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `hsm : frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w) = a • M`. Rewrite using `[hxm, GlobalTheory.RedHalfDrop.frMapO_smul_eq]`. Rewrite using `[hsm]`.

Establish `hxx : (∑ PP ∈ Q, es PP) • x = x`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `hx i j`. Establish `hMe : ∀ i j, toEAf D (∑ PP ∈ Q, es PP) * M i j = M i j`.

Introduce `i j`. Establish `h1` using `GlobalTheory.RedHalfDrop.frMapO_smul_eq βS βT (∑ PP ∈ Q, es PP) x`. Rewrite `h1` using `[hxx]`. Establish `h2` using `congrFun (congrFun h1 i) j`. Rewrite `h2` using `[Matrix.smul_apply, smul_eq_mul]`.

Conclude with `h2.symm`. Establish `ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `Subring.subset_closure (Or.inl ⟨⟨(ϖ : D.host.E), ⟨ϖ, rfl⟩⟩, rfl⟩)`. Establish `hϖ' : (ϖ : D.host.E) ≠ 0`. Introduce `h`. Conclude with `hϖ (Subtype.ext h)`.

Establish `hsum : (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) = (∑ PP ∈ Q, es PP) * incA D ((ϖ : D.host.E)⁻¹)` using `(Finset.sum_mul _ _ _).symm`. Establish `hinv : ∀ i j, toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) * (a * M i j) = M i j`. Introduce `i j`. Establish `hu : toEAf D (incA D ((ϖ : D.host.E)⁻¹)) * a = 1`. Rewrite using `[ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ hϖ', map_one, map_one]`.

Rewrite using `[hsum, map_mul, mul_assoc, ← mul_assoc (toEAf D (incA D _)), hu, one_mul, hMe]`. Establish `hNe : ∀ i j, toEAf D (∑ PP ∈ Q, es PP) * (a * M i j) = a * M i j`. Introduce `i j`. Rewrite using `[mul_left_comm, hMe]`. Establish `hQ' : ∀ PP ∈ Q, (fun _ => ϖ) PP ∈ PP.asIdeal ∧ (fun _ => ϖ) PP ∉ PP.asIdeal ^ 2` using `hQ`.

Prove the components needed by the constructor for the conclusion. Introduce `hI`. Establish `hN : IsIntM (a • M)` using `fun i j => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `mul_mem ha (hI i j)`.

Use `⟨hN, fun PP hPP => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `hN' : a * M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Use `hN i j` as an intermediate fact. Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis.

Establish `key` using `(GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es (fun _ => ϖ) hes hc hQ' (a * M i j) hN' (hNe i j)).1 (by rw [hinv]; exact hI i j) PP hPP`. Unfold `redM`. Rewrite using `[dif_pos (hN i j), Matrix.zero_apply]`. Use `key using 3` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Introduce and unpack `⟨hN, hR⟩ i j`. Establish `hN' : a * M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Use `hN i j` as an intermediate fact. Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis. Establish `key` using `(GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es (fun _ => ϖ) hes hc hQ' (a * M i j) hN' (hNe i j)).2 (fun PP hPP => by`.

Establish `h3` using `congrFun (congrFun (hR PP hPP) i) j`. Unfold `redM at h3`. Rewrite `h3` using `[dif_pos (hN i j), Matrix.zero_apply]`. Use `h3 using 3` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.smul_apply, smul_eq_mul])`.

Establish `e1` using `hinv i j`. Rewrite `key` using `[e1]`. Conclude with `key`.
-/
theorem half_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ IsIntM (frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w)) = 0) := by
  intro D S T βS βT Q e he ϖ hϖ hQ x hx
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  set M := frMapO S T βS βT x with hM
  set a : EAf D := toEAf D (incA D (ϖ : D.host.E)) with ha_def
  have hxm : (x.map fun w => incA D (ϖ : D.host.E) * w) = incA D (ϖ : D.host.E) • x := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hsm : frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w) = a • M := by
    rw [hxm, GlobalTheory.RedHalfDrop.frMapO_smul_eq]
  rw [hsm]
  have hxx : (∑ PP ∈ Q, es PP) • x = x := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hx i j
  have hMe : ∀ i j, toEAf D (∑ PP ∈ Q, es PP) * M i j = M i j := by
    intro i j
    have h1 := GlobalTheory.RedHalfDrop.frMapO_smul_eq βS βT (∑ PP ∈ Q, es PP) x
    rw [hxx] at h1
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  have ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    Subring.subset_closure (Or.inl ⟨⟨(ϖ : D.host.E), ⟨ϖ, rfl⟩⟩, rfl⟩)
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by
    intro h; exact hϖ (Subtype.ext h)
  have hsum : (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) = (∑ PP ∈ Q, es PP) * incA D ((ϖ : D.host.E)⁻¹) :=
    (Finset.sum_mul _ _ _).symm
  have hinv : ∀ i j, toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) * (a * M i j) = M i j := by
    intro i j
    have hu : toEAf D (incA D ((ϖ : D.host.E)⁻¹)) * a = 1 := by
      rw [ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ hϖ', map_one, map_one]
    rw [hsum, map_mul, mul_assoc, ← mul_assoc (toEAf D (incA D _)), hu, one_mul, hMe]
  have hNe : ∀ i j, toEAf D (∑ PP ∈ Q, es PP) * (a * M i j) = a * M i j := by
    intro i j
    rw [mul_left_comm, hMe]
  have hQ' : ∀ PP ∈ Q, (fun _ => ϖ) PP ∈ PP.asIdeal ∧ (fun _ => ϖ) PP ∉ PP.asIdeal ^ 2 := hQ
  constructor
  · intro hI
    have hN : IsIntM (a • M) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem ha (hI i j)
    refine ⟨hN, fun PP hPP => ?_⟩
    ext i j
    have hN' : a * M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := hN i j; rwa [Matrix.smul_apply, smul_eq_mul] at this
    have key := (GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es (fun _ => ϖ) hes hc hQ' (a * M i j) hN' (hNe i j)).1
      (by rw [hinv]; exact hI i j) PP hPP
    unfold redM
    rw [dif_pos (hN i j), Matrix.zero_apply]
    convert key using 3
    rw [Matrix.smul_apply, smul_eq_mul]
  · rintro ⟨hN, hR⟩ i j
    have hN' : a * M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := hN i j; rwa [Matrix.smul_apply, smul_eq_mul] at this
    have key := (GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es (fun _ => ϖ) hes hc hQ' (a * M i j) hN' (hNe i j)).2
      (fun PP hPP => by
        have h3 := congrFun (congrFun (hR PP hPP) i) j
        unfold redM at h3
        rw [dif_pos (hN i j), Matrix.zero_apply] at h3
        convert h3 using 3
        rw [Matrix.smul_apply, smul_eq_mul])
    have e1 := hinv i j
    rw [e1] at key
    exact key

end GlobalTheory.HalfUniInt
