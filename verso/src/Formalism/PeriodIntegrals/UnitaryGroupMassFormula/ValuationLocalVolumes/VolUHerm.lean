import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTyp

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUHm

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclR (x : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) = inclR (F := F) (Fv F v) (σ x) := by
  simp [sigR, inclR]

/- English proof (translation)
Simplify using `[sigR, sc, Algebra.TensorProduct.map_tmul]`.
-/
theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Rewrite using `[← VolTU.sc_mul_eq_smul, ← VolTU.sc_mul_eq_smul, map_mul, sigR_sc]`.
-/
theorem sigR_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [← VolTU.sc_mul_eq_smul, ← VolTU.sc_mul_eq_smul, map_mul, sigR_sc]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨a, -, rfl⟩` from `ha`. Rewrite using `[sigR_inclR]`. Conclude with `VolUTr.TrW.inclR_mem' (E := E) v ⟨σ a, (a.2).map σ.toRingHom.toIntAlgHom⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [map_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h`.

Establish `e : c • x = (c : Fv F v) • x` using `rfl`. Rewrite using `[e, sigR_smul]`. Conclude with `Submodule.smul_mem _ c h`.
-/
theorem sigR_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    rw [sigR_inclR]
    exact VolUTr.TrW.inclR_mem' (E := E) v ⟨σ a, (a.2).map σ.toRingHom.toIntAlgHom⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, sigR_smul]
    exact Submodule.smul_mem _ c h

def sigL : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := sigR_smul σ v

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _`. Conclude with `IsModuleTopology.continuous_of_linearMap (sigL σ v)`.
-/
theorem sigR_cont : Continuous (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMap (sigL σ v)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hinv]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigR_sigR (hinv : ∀ y, σ (σ y) = y) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hinv]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

section Phi

variable (r : ℕ)

def phiF (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E :=
  fun p => if p.1 < p.2 then Y p + sigR (Fv F v) σ (Y (p.2, p.1)) else Y p

def phiB (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E :=
  fun p => if p.1 < p.2 then Y p - sigR (Fv F v) σ (Y (p.2, p.1)) else Y p

/- English proof (translation)
Simplify using `[phiF, h]`.
-/
theorem phiF_low (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) {i j : Fin (r + 1)} (h : ¬ i < j) :
    phiF σ v r Y (i, j) = Y (i, j) := by
  simp [phiF, h]

/- English proof (translation)
Simplify using `[phiF, h]`.
-/
theorem phiF_up (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) {i j : Fin (r + 1)} (h : i < j) :
    phiF σ v r Y (i, j) = Y (i, j) + sigR (Fv F v) σ (Y (j, i)) := by
  simp [phiF, h]

def phiE : (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) ≃ₜ+ (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) where
  toFun := phiF σ v r
  invFun := phiB σ v r
  left_inv Y := by
    funext p
    by_cases h : p.1 < p.2
    · have h' : ¬ p.2 < p.1 := fun h2 => lt_asymm h h2
      simp [phiF, phiB, h, h']
    · simp [phiF, phiB, h]
  right_inv Y := by
    funext p
    by_cases h : p.1 < p.2
    · have h' : ¬ p.2 < p.1 := fun h2 => lt_asymm h h2
      simp [phiF, phiB, h, h']
    · simp [phiF, phiB, h]
  map_add' Y Z := by
    funext p
    by_cases h : p.1 < p.2
    · simp only [phiF, h, if_true, Pi.add_apply, map_add]
      abel
    · simp [phiF, h]
  continuous_toFun := by
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    refine continuous_pi fun p => ?_
    by_cases h : p.1 < p.2
    · simp only [phiF, h, if_true]
      exact (continuous_apply p).add ((sigR_cont σ v).comp (continuous_apply (p.2, p.1)))
    · simp only [phiF, h, if_false]
      exact continuous_apply p
  continuous_invFun := by
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
      IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
    refine continuous_pi fun p => ?_
    by_cases h : p.1 < p.2
    · simp only [phiB, h, if_true]
      exact (continuous_apply p).sub ((sigR_cont σ v).comp (continuous_apply (p.2, p.1)))
    · simp only [phiB, h, if_false]
      exact continuous_apply p

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Distinguish the cases in `hij : i < j`. Establish `h1` using `h i j`. Establish `h2` using `h j i`.

Rewrite `h1` using `[phiF_up σ v r Y hij]`. Rewrite `h2` using `[phiF_low σ v r Y (fun h3 => lt_asymm hij h3)]`. Establish `e : Y (i, j) = (Y (i, j) + sigR (Fv F v) σ (Y (j, i))) - sigR (Fv F v) σ (Y (j, i))` using `by ring`. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ h1 (sigR_mem σ v h2)`.

Establish `h1` using `h i j`. Rewrite `h1` using `[phiF_low σ v r Y hij]`. Then use the resulting hypothesis. Introduce `h i j`. Distinguish the cases in `hij : i < j`. Rewrite using `[phiF_up σ v r Y hij]`.

Conclude with `Submodule.add_mem _ (h i j) (sigR_mem σ v (h j i))`. Rewrite using `[phiF_low σ v r Y hij]`. Conclude with `h i j`.
-/
theorem phiF_mem_iff (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :
    (∀ i j, phiF σ v r Y (i, j) ∈ OEv (E := E) v) ↔ ∀ i j, Y (i, j) ∈ OEv (E := E) v := by
  constructor
  · intro h i j
    by_cases hij : i < j
    · have h1 := h i j
      have h2 := h j i
      rw [phiF_up σ v r Y hij] at h1
      rw [phiF_low σ v r Y (fun h3 => lt_asymm hij h3)] at h2
      have e : Y (i, j) = (Y (i, j) + sigR (Fv F v) σ (Y (j, i))) - sigR (Fv F v) σ (Y (j, i)) := by ring
      rw [e]
      exact Submodule.sub_mem _ h1 (sigR_mem σ v h2)
    · have h1 := h i j
      rwa [phiF_low σ v r Y hij] at h1
  · intro h i j
    by_cases hij : i < j
    · rw [phiF_up σ v r Y hij]
      exact Submodule.add_mem _ (h i j) (sigR_mem σ v (h j i))
    · rw [phiF_low σ v r Y hij]
      exact h i j

def hermBox (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {Y | ∀ i j, Y (i, j) ∈ OEv (E := E) v ∧
    (i < j → (Y (i, j) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) ∧
    (i = j → (Y (i, j) + sigR (Fv F v) σ (Y (i, j)) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v)}

/- English proof (translation)
Use extensionality with `Y`. Simplify using `only [VolTW, hermBox, Set.mem_setOf_eq, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `⟨(phiF_mem_iff σ v r Y).2 (fun i j => (h i j).1) i j, fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations.

Rewrite using `[phiF_up σ v r Y hij]`. Conclude with `(h i j).2`. Substitute `hij` using the available equality. Rewrite using `[phiF_low σ v r Y (lt_irrefl _)]`. Conclude with `(h i i).2`.

Introduce `h`. Establish `hO` using `(phiF_mem_iff σ v r Y).1 (fun i j => (h i j).1)`. Introduce `i j`. Use `⟨hO i j, ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases.

Use `(h i j).2.1 hij` as an intermediate fact. Rewrite `this` using `[phiF_up σ v r Y hij]`. Then use the resulting hypothesis. Substitute `hij` using the available equality. Use `(h i i).2.2 rfl` as an intermediate fact. Rewrite `this` using `[phiF_low σ v r Y (lt_irrefl _)]`. Then use the resulting hypothesis.

Establish `h1` using `sigR_mem σ v ((h j i).2.1 hij)`. Rewrite `h1` using `[phiF_up σ v r Y hij, map_mul, sigR_sc, map_sub, map_add, sigR_sigR σ v hinv, ← hc.1 j i]`. Rewrite using `[show Y (i, j) + sigR (Fv F v) σ (Y (j, i)) - c i j = sigR (Fv F v) σ (Y (j, i)) + Y (i, j) - c i j by ring]`. Conclude with `h1`.
-/
theorem volTW_eq (hinv : ∀ y, σ (σ y) = y) (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (hc : VolTHermInt σ v r c) : VolTW σ v g r c = phiF σ v r ⁻¹' hermBox σ v g r c := by
  ext Y
  simp only [VolTW, hermBox, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro h i j
    refine ⟨(phiF_mem_iff σ v r Y).2 (fun i j => (h i j).1) i j, fun hij => ?_, fun hij => ?_⟩
    · rw [phiF_up σ v r Y hij]
      exact (h i j).2
    · subst hij
      rw [phiF_low σ v r Y (lt_irrefl _)]
      exact (h i i).2
  · intro h
    have hO := (phiF_mem_iff σ v r Y).1 (fun i j => (h i j).1)
    intro i j
    refine ⟨hO i j, ?_⟩
    rcases lt_trichotomy i j with hij | hij | hij
    · have := (h i j).2.1 hij
      rwa [phiF_up σ v r Y hij] at this
    · subst hij
      have := (h i i).2.2 rfl
      rwa [phiF_low σ v r Y (lt_irrefl _)] at this
    · have h1 := sigR_mem σ v ((h j i).2.1 hij)
      rw [phiF_up σ v r Y hij, map_mul, sigR_sc, map_sub, map_add, sigR_sigR σ v hinv, ← hc.1 j i] at h1
      rw [show Y (i, j) + sigR (Fv F v) σ (Y (j, i)) - c i j =
        sigR (Fv F v) σ (Y (j, i)) + Y (i, j) - c i j by ring]
      exact h1

/- English proof (translation)
Take `⟨h1, h2, h3, h4, -⟩` from `VolUH.top_facts (E := E) v (Fin (r + 1) × Fin (r + 1))`. Establish `h` using `VolUH.haar_pre μ (phiE σ v r) (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) hK (hermBox σ v g r c)`. Establish `hK' : (phiE σ v r) ⁻¹' VolTO (E` using `E) v (Fin (r + 1) × Fin (r + 1)) = VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) := by`. Use extensionality with `Y`. Simplify using `only [VolTO, Set.mem_preimage, Set.mem_setOf_eq, Prod.forall]`.

Conclude with `phiF_mem_iff σ v r Y`. Rewrite `h` using `[hK', hK, one_mul]`. Rewrite using `[volTW_eq σ v hinv g r c hc]`. Conclude with `h`.
-/
theorem volTW_meas (hinv : ∀ y, σ (σ y) = y) (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1) (g : ℕ)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    μ (VolTW σ v g r c) = μ (hermBox σ v g r c) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := VolUH.top_facts (E := E) v (Fin (r + 1) × Fin (r + 1))
  have h := VolUH.haar_pre μ (phiE σ v r) (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) hK (hermBox σ v g r c)
  have hK' : (phiE σ v r) ⁻¹' VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) =
      VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) := by
    ext Y
    simp only [VolTO, Set.mem_preimage, Set.mem_setOf_eq, Prod.forall]
    exact phiF_mem_iff σ v r Y
  rw [hK', hK, one_mul] at h
  rw [volTW_eq σ v hinv g r c hc]
  exact h

variable (ψ : AddChar (AF F) ℂ)

def VolTHermBox (g : ℕ) : Prop :=
  ∀ c, VolTHermInt σ v r c →
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (hermBox σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹

/- English proof (translation)
Take `⟨hH, -, hO⟩` from `VolUL.sd_facts ψ v hψ hfin hann hd (Fin (r + 1) × Fin (r + 1))`. Introduce `c hc`. Rewrite using `[volTW_meas σ v r hinv _ hO g c hc]`. Conclude with `hB c hc`.
-/
theorem volTHermCnt_of_box (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : VolUL.AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (hinv : ∀ y, σ (σ y) = y) (g : ℕ) (hB : VolTHermBox σ v r ψ g) :
    VolTHermCnt σ ψ v g r := by
  obtain ⟨hH, -, hO⟩ := VolUL.sd_facts ψ v hψ hfin hann hd (Fin (r + 1) × Fin (r + 1))
  intro c hc
  rw [volTW_meas σ v r hinv _ hO g c hc]
  exact hB c hc

end Phi

end Formalism.L2.SG.Pf.NcVal.VolUHm
