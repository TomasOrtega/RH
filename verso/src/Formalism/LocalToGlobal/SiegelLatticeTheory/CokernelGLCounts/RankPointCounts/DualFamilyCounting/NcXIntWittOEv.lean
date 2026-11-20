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
The claim follows from `Submodule.subset_span ⟨o, trivial, rfl⟩`.
-/
theorem oev_inclR (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

/- English proof (translation)
Establish `h` using `oev_inclR (F := F) (E := E) v 1`. Simplify using `using h`.
-/
theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := oev_inclR (F := F) (E := E) v 1
  simpa using h

/- English proof (translation)
Unfold `OEv at hx hy ⊢`. Rewrite `hx`, `hy`, the goal using `[SetLike.mem_coe]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨a, -, rfl⟩` from `ha`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨b, -, rfl⟩` from `hb`. Conclude with `Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ h1 h2 => rw [mul_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c y _ h => show _ * ((c : Fv F v) • y) ∈ _`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c h`.

Consider the case `zero => simp`. Consider the case `add x z _ _ h1 h2 => rw [add_mul]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h => show ((c : Fv F v) • x) * y ∈ _`. Rewrite using `[smul_mul_assoc]`.

Conclude with `Submodule.smul_mem _ c h`.
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
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, TensorProduct.smul_tmul']`. Consider the case `add x y h1 h2 => rw [smul_add, map_add, h1, h2, map_add, smul_add]`.
-/
theorem sigR_smul' (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add, h1, h2, map_add, smul_add]

/- English proof (translation)
Unfold `OEv at hx ⊢`. Rewrite `hx`, the goal using `[SetLike.mem_coe]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨a, -, rfl⟩` from `ha`.

Use `Submodule.subset_span ⟨⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)⟩, trivial, ?_⟩` and prove the remaining obligations. Simplify using `[sigR, inclR]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x y _ _ h1 h2 => rw [map_add]`.

Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h => show sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _`. Rewrite using `[sigR_smul']`. Conclude with `Submodule.smul_mem _ c h`.
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
Establish `hsingle : ∀ (i : Fin n) (z : Fv F v ⊗[F] E), z ∈ OEv (E` using `E) v → Pi.single i z ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by`. Introduce `i z hz`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨o, -, rfl⟩` from `hw`. Use `Submodule.subset_span ⟨Pi.single i (o : E), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, MassDataMassesW.KCptW.stdSub, Submodule.mem_pi]`. Introduce `k _`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[ratV]`. Simplify using `[ratV, hk]`. Consider the case `zero => rw [Pi.single_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add w w' _ _ h1 h2 => rw [Pi.single_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c w _ h`. Establish `: (Pi.single i (c • w) : Fin n → Fv F v ⊗[F] E) = c • (Pi.single i w : Fin n → Fv F v ⊗[F] E)`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ c h`. Rewrite using `[← Finset.univ_sum_single y]`. Conclude with `Submodule.sum_mem _ fun i _ => hsingle i (y i) (hy i)`.
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
Establish `halg : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral x).isAlgebraic`. Take `⟨N, hN0, hNx⟩` from `halg.exists_integral_multiple`. Set `o : 𝓞 E` to `⟨N • x, hNx⟩`. Use `filter_upwards [ev_int (F := F) ((N : F)⁻¹)] with v hv`. Establish `e : inclR (F` using `F) (Fv F v) x = (⟨algebraMap F (Fv F v) ((N : F)⁻¹), hv⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) := by show _ = algebraMap F (Fv F v) ((N : F)⁻¹) • inclR (F := F) (Fv F v) (N • x)`.

Rewrite using `[Algebra.smul_def, ← IsScalarTower.algebraMap_apply, map_zsmul, zsmul_eq_mul, ← mul_assoc, ← map_intCast (algebraMap F (Fv F v ⊗[F] E)), ← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hN0), map_one, one_mul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (oev_inclR v o)`.
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
The claim follows from `Submodule.smul_mem _ (⟨r, hr⟩ : v.adicCompletionIntegers F) hz`.
-/
theorem oev_smul' {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : z ∈ OEv (E := E) v) : r • z ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨r, hr⟩ : v.adicCompletionIntegers F) hz

end OEvRing

end Formalism.L2.SG.Pf.NcX.IntWittPf
