import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXKfOrb

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcX.KfOrbPf
open scoped TensorProduct

section OEvRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oev_inclR (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := oev_inclR (F := F) (E := E) v 1
  simpa using h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      show _ * ((c : Fv F v) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show ((c : Fv F v) • x) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem sigR_smul' (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add, h1, h2, map_add, smul_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem oev_sigR (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    refine Submodule.subset_span
      ⟨⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)⟩, trivial, ?_⟩
    simp [sigR, inclR]
    rfl
  | zero => simp
  | add x y _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _
    rw [sigR_smul']
    exact Submodule.smul_mem _ c h

def oevRing : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oev_mul v
  one_mem' := oev_one v
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  neg_mem' := fun hx => Submodule.neg_mem _ hx

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_std_of_oev {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) (hy : ∀ i, y i ∈ OEv (E := E) v) :
    y ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  have hsingle : ∀ (i : Fin n) (z : Fv F v ⊗[F] E), z ∈ OEv (E := E) v → Pi.single i z ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
    intro i z hz
    change z ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨o, -, rfl⟩ := hw
      refine Submodule.subset_span ⟨Pi.single i (o : E), ?_, ?_⟩
      · rw [SetLike.mem_coe, MassDataMassesW.KCptW.stdSub, Submodule.mem_pi]
        intro k _
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · funext k
        by_cases hk : k = i
        · subst hk; simp [ratV]
        · simp [ratV, hk]
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add w w' _ _ h1 h2 => rw [Pi.single_add]; exact Submodule.add_mem _ h1 h2
    | smul c w _ h =>
      have : (Pi.single i (c • w) : Fin n → Fv F v ⊗[F] E) = c • (Pi.single i w : Fin n → Fv F v ⊗[F] E) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      rw [this]
      exact Submodule.smul_mem _ c h
  rw [← Finset.univ_sum_single y]
  exact Submodule.sum_mem _ fun i _ => hsingle i (y i) (hy i)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ev_oev (x : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, inclR (F := F) (Fv F v) x ∈ OEv (E := E) v := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral x).isAlgebraic
  obtain ⟨N, hN0, hNx⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨N • x, hNx⟩
  filter_upwards [ev_int (F := F) ((N : F)⁻¹)] with v hv
  have e : inclR (F := F) (Fv F v) x =
      (⟨algebraMap F (Fv F v) ((N : F)⁻¹), hv⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) := by
    show _ = algebraMap F (Fv F v) ((N : F)⁻¹) • inclR (F := F) (Fv F v) (N • x)
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, map_zsmul, zsmul_eq_mul, ← mul_assoc, ← map_intCast (algebraMap F (Fv F v ⊗[F] E)), ← map_mul,
      inv_mul_cancel₀ (Int.cast_ne_zero.2 hN0), map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (oev_inclR v o)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oev_smul' {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : z ∈ OEv (E := E) v) : r • z ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨r, hr⟩ : v.adicCompletionIntegers F) hz

end OEvRing

end Formalism.L2.SG.Pf.NcX.IntWittPf
