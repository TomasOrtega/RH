import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace MassDataLevelSSteps.LatTop

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation

section Key

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨N1, h1, m1⟩` from `hy`. Take `⟨N2, h2, m2⟩` from `hz`. Use `⟨N1 * N2, mul_ne_zero h1 h2, ?_⟩` and prove the remaining obligations. Establish `e1 : (N1 * N2) • y = N2 • (N1 • y)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (N1 * N2) • z = N1 • (N2 • z)` using `by rw [mul_smul]`.

Rewrite using `[smul_add, e1, e2]`. Conclude with `L.add_mem (zsmul_mem m1 N2) (zsmul_mem m2 N1)`. Consider the case `smul e y _ hy`. Take `⟨N, hN, m⟩` from `hy`. Take `⟨c, hc, hint⟩` from `exists_integral_multiples ℤ ℚ (L := E) {e}`.

Establish `hi : IsIntegral ℤ (c • e)` using `hint e (Finset.mem_singleton_self e)`. Use `⟨c * N, mul_ne_zero hc hN, ?_⟩` and prove the remaining obligations. Establish `e3 : (c * N) • (e • y) = (c • e) • (N • y)`. Rewrite using `[mul_smul, smul_comm N e y, smul_assoc]`. Rewrite using `[e3]`.

Establish `e4 : (c • e) • (N • y) = (IsIntegralClosure.mk' (𝓞 E) (c • e) hi) • (N • y)`. Rewrite using `[← algebraMap_smul E (IsIntegralClosure.mk' (𝓞 E) (c • e) hi) (N • y), IsIntegralClosure.algebraMap_mk']`. Rewrite using `[e4]`. Conclude with `L.smul_mem _ m`.
-/
theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1, m1⟩ := hy
    obtain ⟨N2, h2, m2⟩ := hz
    refine ⟨N1 * N2, mul_ne_zero h1 h2, ?_⟩
    have e1 : (N1 * N2) • y = N2 • (N1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (N1 * N2) • z = N1 • (N2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem m1 N2) (zsmul_mem m2 N1)
  | smul e y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hi : IsIntegral ℤ (c • e) := hint e (Finset.mem_singleton_self e)
    refine ⟨c * N, mul_ne_zero hc hN, ?_⟩
    have e3 : (c * N) • (e • y) = (c • e) • (N • y) := by
      rw [mul_smul, smul_comm N e y, smul_assoc]
    rw [e3]
    have e4 : (c • e) • (N • y) = (IsIntegralClosure.mk' (𝓞 E) (c • e) hi) • (N • y) := by
      rw [← algebraMap_smul E (IsIntegralClosure.mk' (𝓞 E) (c • e) hi) (N • y),
        IsIntegralClosure.algebraMap_mk']
    rw [e4]
    exact L.smul_mem _ m

end Key

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def ratAdd : (Fin n → E) →+ (Fin n → Fv F v ⊗[F] E) :=
  AddMonoidHom.compLeft (inclR (F := F) (Fv F v) : E →+* Fv F v ⊗[F] E).toAddMonoidHom (Fin n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratAdd_apply (x : Fin n → E) : ratAdd v x = ratV (F := F) (Fv F v) x := rfl

/- English proof (translation)
The claim follows from `(latLoc (E := E) v Λ).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hy`.
-/
theorem smul_mem_latLoc (Λ : Set (Fin n → E)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc (E := E) v Λ) : c • y ∈ latLoc (E := E) v Λ :=
  (latLoc (E := E) v Λ).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hy

/- English proof (translation)
Establish `: CompactSpace (v.adicCompletionIntegers F)` using `isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v)`. Establish `: Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.mpr hfg`. Establish `: Module.Finite ℤ L` using `Module.Finite.trans (𝓞 E) L`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := L)`. Set `g : s → (Fin n → Fv F v ⊗[F] E)` to `fun i => ratV (F := F) (Fv F v) ((i.1 : L) : Fin n → E)`.

Set `f : (s → v.adicCompletionIntegers F) → (Fin n → Fv F v ⊗[F] E)` to `fun c => ∑ i, ((c i : v.adicCompletionIntegers F) : Fv F v) • g i`. Establish `hf : Continuous f`. Use `continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Establish `hi : Continuous fun c : (s → v.adicCompletionIntegers F) => ((c i : v.adicCompletionIntegers F) : Fv F v)` using `(continuous_apply i).subtype_val`. Conclude with `hi.smul (continuous_const : Continuous fun _ : (s → v.adicCompletionIntegers F) => g i)`.

Establish `hle : latLoc (E` using `E) v (L : Set (Fin n → E)) ≤ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Establish `key : ∀ x : L, x ∈ Submodule.span ℤ (s : Set L) → ratAdd v (x : Fin n → E) ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g)`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩`. Consider the case `zero => show ratAdd v ((0 : L) : Fin n → E) ∈ _`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => show ratAdd v ((x + y : L) : Fin n → E) ∈ _`.

Rewrite using `[Submodule.coe_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul k x _ hx => show ratAdd v ((k • x : L) : Fin n → E) ∈ _`. Rewrite using `[Submodule.coe_smul_of_tower, map_zsmul]`. Conclude with `zsmul_mem hx k`.

Conclude with `key ⟨l, hl⟩ (hs ▸ Submodule.mem_top)`. Establish `e : (latLoc (E` using `E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = Set.range f := by`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).mp (hle hy)`. Conclude with `⟨c, hc⟩`. Introduce and unpack `⟨c, rfl⟩`. Use `Submodule.sum_mem _ fun i _ => smul_mem_latLoc v _ (c i).2 ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨_, (i.1 : L).2, rfl⟩`.

Rewrite using `[e]`. Conclude with `isCompact_range hf`.
-/
theorem isCompact_latLoc (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : CompactSpace (v.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v)
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := L)
  let g : s → (Fin n → Fv F v ⊗[F] E) := fun i => ratV (F := F) (Fv F v) ((i.1 : L) : Fin n → E)
  let f : (s → v.adicCompletionIntegers F) → (Fin n → Fv F v ⊗[F] E) :=
    fun c => ∑ i, ((c i : v.adicCompletionIntegers F) : Fv F v) • g i
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun i _ => ?_
    have hi : Continuous fun c : (s → v.adicCompletionIntegers F) =>
        ((c i : v.adicCompletionIntegers F) : Fv F v) := (continuous_apply i).subtype_val
    exact hi.smul (continuous_const : Continuous fun _ : (s → v.adicCompletionIntegers F) => g i)
  have hle : latLoc (E := E) v (L : Set (Fin n → E)) ≤
      Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have key : ∀ x : L, x ∈ Submodule.span ℤ (s : Set L) →
        ratAdd v (x : Fin n → E) ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      | zero =>
        show ratAdd v ((0 : L) : Fin n → E) ∈ _
        simp
      | add x y _ _ hx hy =>
        show ratAdd v ((x + y : L) : Fin n → E) ∈ _
        rw [Submodule.coe_add, map_add]
        exact Submodule.add_mem _ hx hy
      | smul k x _ hx =>
        show ratAdd v ((k • x : L) : Fin n → E) ∈ _
        rw [Submodule.coe_smul_of_tower, map_zsmul]
        exact zsmul_mem hx k
    exact key ⟨l, hl⟩ (hs ▸ Submodule.mem_top)
  have e : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = Set.range f := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hle hy)
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      refine Submodule.sum_mem _ fun i _ => smul_mem_latLoc v _ (c i).2 ?_
      exact Submodule.subset_span ⟨_, (i.1 : L).2, rfl⟩
  rw [e]
  exact isCompact_range hf

/- English proof (translation)
Proceed by induction on `N using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Move the coercions through the operations in `at ih ⊢`. Rewrite using `[add_mul, one_mul, TensorProduct.tmul_add, ih, TensorProduct.add_tmul]`.

Consider the case `pred k ih`. Move the coercions through the operations in `at ih ⊢`. Rewrite using `[sub_mul, one_mul, TensorProduct.tmul_sub, ih, TensorProduct.sub_tmul]`.
-/
theorem one_tmul_intCast_mul (N : ℤ) (e : E) :
    (1 : Fv F v) ⊗ₜ[F] ((N : E) * e) = (N : Fv F v) ⊗ₜ[F] e := by
  induction N using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [add_mul, one_mul, TensorProduct.tmul_add, ih, TensorProduct.add_tmul]
  | pred k ih =>
    push_cast at ih ⊢
    rw [sub_mul, one_mul, TensorProduct.tmul_sub, ih, TensorProduct.sub_tmul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[ratV, inclR, TensorProduct.smul_tmul']`. Conclude with `one_tmul_intCast_mul v N e`.

Simplify using `[ratV, inclR, h]`.
-/
theorem ratV_zsmul_single (N : ℤ) (j : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (N • (Pi.single j e : Fin n → E)) =
      (N : Fv F v) • (Pi.single j ((1 : Fv F v) ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [ratV, inclR, TensorProduct.smul_tmul']
    exact one_tmul_intCast_mul v N e
  · simp [ratV, inclR, h]

end Lat

end MassDataLevelSSteps.LatTop
