import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LineBC

variable (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

/- English proof (translation)
Use `haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation`. Take `⟨n, g, hg⟩` from `Module.Finite.exists_fin' (𝓞 K) (𝓞 K')`. Take `⟨h, hh⟩` from `Module.projective_lifting_property g LinearMap.id hg`. Set `ι : 𝓞 K' →ₗ[𝓞 K] K'` to `(IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap`.

Use `haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) ι := by`. Rewrite using `[isLocalizedModule_iff_isLocalization]`. Conclude with `IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')`. Establish `hunitK : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x)` using `(isLocalizedModule_id (nonZeroDivisors (𝓞 K)) K K).map_units`. Set `t : Fin n → 𝓞 K' →ₗ[𝓞 K] 𝓞 K` to `fun j => LinearMap.proj j ∘ₗ h`.

Set `τ1 : Fin n → K' →ₗ[𝓞 K] K` to `fun j => IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) ι (Algebra.linearMap (𝓞 K) K ∘ₗ t j) hunitK`. Establish `hτ1 : ∀ j c, τ1 j (ι c) = algebraMap (𝓞 K) K (t j c)` using `fun j c => IsLocalizedModule.lift_apply _ ι _ hunitK c`. Set `τ : Fin n → K' →ₗ[K] K` to `fun j => (τ1 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K`. Set `b : Fin n → 𝓞 K'` to `fun j => g (Pi.single j 1)`. Establish `hsum : ∀ a : 𝓞 K', a = ∑ j, t j a • b j`.

Introduce `a`. Establish `h1 : g (h a) = a` using `LinearMap.congr_fun hh a`. Use `conv_lhs => rw [← h1, ← Finset.univ_sum_single (h a), map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show (Pi.single j (h a j) : Fin n → 𝓞 K) = h a j • (Pi.single j 1 : Fin n → 𝓞 K) by`.

Apply the tactic sequence `ext k; by_cases hk : k = j <;> simp [Pi.single_apply, hk], map_smul]`. Both sides reduce to the same expression. Use `⟨n, τ, b, fun j c => ⟨t j c, hτ1 j c⟩, fun z => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, d⟩, hd⟩` from `IsLocalizedModule.surj (nonZeroDivisors (𝓞 K)) ι z`. Establish `hd' : (d : 𝓞 K) • z = ι a` using `hd`.

Establish `hne : (algebraMap (𝓞 K) K' (d : 𝓞 K)) ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) K K']`. Simplify using `using nonZeroDivisors.coe_ne_zero d`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[← Algebra.smul_def, hd', Finset.mul_sum]`.

Use `conv_lhs => rw [hsum a, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e1 : τ j z * algebraMap (𝓞 K) K (d : 𝓞 K) = algebraMap (𝓞 K) K (t j a)`. Rewrite using `[← hτ1, ← hd', map_smul, Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression.

Establish `e2 : algebraMap (𝓞 K) K' (d : 𝓞 K) * algebraMap K K' (τ j z) = algebraMap (𝓞 K) K' (t j a)`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) K K', ← map_mul, mul_comm, e1, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[← mul_assoc, e2, map_smul, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem exists_coords : ∃ (n : ℕ) (τ : Fin n → K' →ₗ[K] K) (b : Fin n → 𝓞 K'),
    (∀ j (c : 𝓞 K'), ∃ r : 𝓞 K, τ j (c : K') = algebraMap (𝓞 K) K r) ∧
    ∀ z : K', z = ∑ j, algebraMap K K' (τ j z) * (b j : K') := by
  classical
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 K')
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g LinearMap.id hg
  let ι : 𝓞 K' →ₗ[𝓞 K] K' := (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) ι := by
    rw [isLocalizedModule_iff_isLocalization]
    exact IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hunitK : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) K K).map_units
  let t : Fin n → 𝓞 K' →ₗ[𝓞 K] 𝓞 K := fun j => LinearMap.proj j ∘ₗ h
  let τ1 : Fin n → K' →ₗ[𝓞 K] K := fun j =>
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) ι (Algebra.linearMap (𝓞 K) K ∘ₗ t j) hunitK
  have hτ1 : ∀ j c, τ1 j (ι c) = algebraMap (𝓞 K) K (t j c) := fun j c =>
    IsLocalizedModule.lift_apply _ ι _ hunitK c
  let τ : Fin n → K' →ₗ[K] K := fun j => (τ1 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  let b : Fin n → 𝓞 K' := fun j => g (Pi.single j 1)
  have hsum : ∀ a : 𝓞 K', a = ∑ j, t j a • b j := by
    intro a
    have h1 : g (h a) = a := LinearMap.congr_fun hh a
    conv_lhs => rw [← h1, ← Finset.univ_sum_single (h a), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (h a j) : Fin n → 𝓞 K) = h a j • (Pi.single j 1 : Fin n → 𝓞 K) by
      ext k; by_cases hk : k = j <;> simp [Pi.single_apply, hk], map_smul]
    rfl
  refine ⟨n, τ, b, fun j c => ⟨t j c, hτ1 j c⟩, fun z => ?_⟩
  obtain ⟨⟨a, d⟩, hd⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 K)) ι z
  have hd' : (d : 𝓞 K) • z = ι a := hd
  have hne : (algebraMap (𝓞 K) K' (d : 𝓞 K)) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K K']
    simpa using nonZeroDivisors.coe_ne_zero d
  apply mul_left_cancel₀ hne
  rw [← Algebra.smul_def, hd', Finset.mul_sum]
  conv_lhs => rw [hsum a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : τ j z * algebraMap (𝓞 K) K (d : 𝓞 K) = algebraMap (𝓞 K) K (t j a) := by
    rw [← hτ1, ← hd', map_smul, Algebra.smul_def, mul_comm]
    rfl
  have e2 : algebraMap (𝓞 K) K' (d : 𝓞 K) * algebraMap K K' (τ j z) = algebraMap (𝓞 K) K' (t j a) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K K', ← map_mul, mul_comm, e1, ← IsScalarTower.algebraMap_apply]
  rw [← mul_assoc, e2, map_smul, Algebra.smul_def]
  rfl

/- English proof (translation)
Use `set f : (Fin m → K) → (Fin m → K') := fun v i => algebraMap K K' (v i) with hf`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, ⟨hvL, hvx⟩, rfl⟩`. Use `⟨Submodule.subset_span ⟨v, hvL, rfl⟩, ?_⟩` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hvx`. Use `show f (a • x) ∈ (Submodule.span K' {fun i => algebraMap K K' (x i)}).restrictScalars (𝓞 K')`. Rewrite using `[Submodule.restrictScalars_mem, Submodule.mem_span_singleton]`. Conclude with `⟨algebraMap K K' a, funext fun i => by simp [f]⟩`. Introduce and unpack `y ⟨hyL, hyx⟩`.

Take `⟨n, τ, b, hτ, hz⟩` from `exists_coords K K'`. Set `T : Fin n → (Fin m → K') → (Fin m → K)` to `fun j w i => τ j (w i)`. Set `N : Submodule (𝓞 K') (Fin m → K')` to `{ carrier := {w | ∀ (c : 𝓞 K') j, T j (c • w) ∈ L} add_mem' := fun {u w} hu hw c j => by`. Establish `: T j (c • (u + w)) = T j (c • u) + T j (c • w)` using `funext fun i => by`. Simplify using `[T, smul_add, map_add]`.

Rewrite using `[this]`. Conclude with `L.add_mem (hu c j) (hw c j)`. Use the proof step `zero_mem' := fun c j => by`. Establish `: T j (c • (0 : Fin m → K')) = 0` using `funext fun i => by simp [T]`. Rewrite using `[this]`.

Conclude with `L.zero_mem`. Use the proof step `smul_mem' := fun c' w hw c j => by`. Rewrite using `[smul_smul]`. Conclude with `hw _ j }`. Establish `hgen : ∀ v ∈ L, f v ∈ N`.

Introduce `v hv c j`. Take `⟨r, hr⟩` from `hτ j c`. Establish `: T j (c • f v) = r • v` using `funext fun i => by`. Simplify using `only [T, f, Pi.smul_apply]`. Rewrite using `[show c • algebraMap K K' (v i) = v i • (c : K') by`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, mul_comm]`. Apply the tactic sequence `try rfl, map_smul, hr, smul_eq_mul, Algebra.smul_def, mul_comm]`. Rewrite using `[this]`. Conclude with `L.smul_mem r hv`. Establish `hN : latBC K' L ≤ N` using `Submodule.span_le.2 (by rintro _ ⟨v, hv, rfl⟩; exact hgen v hv)`.

Establish `hTL : ∀ j, T j y ∈ L` using `fun j => by simpa using hN hyL 1 j`. Establish `hyx' : y ∈ Submodule.span K' {fun i => algebraMap K K' (x i)}` using `hyx`. Rewrite `hyx'` using `[Submodule.mem_span_singleton]`. Take `⟨β, rfl⟩` from `hyx'`. Establish `hTx : ∀ j, T j (β • fun i => algebraMap K K' (x i)) ∈ Submodule.span K {x}` using `fun j => by`.

Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨τ j β, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [T, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_comm β, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Establish `hrec : (β • fun i => algebraMap K K' (x i)) = ∑ j, b j • f (T j (β • fun i => algebraMap K K' (x i)))`.

Use function extensionality and compare the values at `fun i => by`. Rewrite using `[Finset.sum_apply]`. Use `(hz _).trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [f, Pi.smul_apply]`. Rewrite using `[Algebra.smul_def, mul_comm]`.

Both sides reduce to the same expression. Rewrite using `[hrec]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hTL j, hTx j⟩, rfl⟩)` and prove the remaining obligations.
-/
theorem latBC_lineLat (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (_hL : L.FG) (x : Fin m → K) :
    latBC K' (lineLat L x) = lineLat (latBC K' L) (fun i => algebraMap K K' (x i)) := by
  classical
  set f : (Fin m → K) → (Fin m → K') := fun v i => algebraMap K K' (v i) with hf
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, ⟨hvL, hvx⟩, rfl⟩
    refine ⟨Submodule.subset_span ⟨v, hvL, rfl⟩, ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hvx
    show f (a • x) ∈ (Submodule.span K' {fun i => algebraMap K K' (x i)}).restrictScalars (𝓞 K')
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    exact ⟨algebraMap K K' a, funext fun i => by simp [f]⟩
  · rintro y ⟨hyL, hyx⟩
    obtain ⟨n, τ, b, hτ, hz⟩ := exists_coords K K'
    let T : Fin n → (Fin m → K') → (Fin m → K) := fun j w i => τ j (w i)

    let N : Submodule (𝓞 K') (Fin m → K') :=
      { carrier := {w | ∀ (c : 𝓞 K') j, T j (c • w) ∈ L}
        add_mem' := fun {u w} hu hw c j => by
          have : T j (c • (u + w)) = T j (c • u) + T j (c • w) := funext fun i => by
            simp [T, smul_add, map_add]
          rw [this]; exact L.add_mem (hu c j) (hw c j)
        zero_mem' := fun c j => by
          have : T j (c • (0 : Fin m → K')) = 0 := funext fun i => by simp [T]
          rw [this]; exact L.zero_mem
        smul_mem' := fun c' w hw c j => by
          rw [smul_smul]; exact hw _ j }
    have hgen : ∀ v ∈ L, f v ∈ N := by
      intro v hv c j
      obtain ⟨r, hr⟩ := hτ j c
      have : T j (c • f v) = r • v := funext fun i => by
        simp only [T, f, Pi.smul_apply]
        rw [show c • algebraMap K K' (v i) = v i • (c : K') by
          rw [Algebra.smul_def, Algebra.smul_def, mul_comm]; try rfl, map_smul, hr, smul_eq_mul, Algebra.smul_def, mul_comm]
      rw [this]; exact L.smul_mem r hv
    have hN : latBC K' L ≤ N := Submodule.span_le.2 (by rintro _ ⟨v, hv, rfl⟩; exact hgen v hv)
    have hTL : ∀ j, T j y ∈ L := fun j => by simpa using hN hyL 1 j
    have hyx' : y ∈ Submodule.span K' {fun i => algebraMap K K' (x i)} := hyx
    rw [Submodule.mem_span_singleton] at hyx'
    obtain ⟨β, rfl⟩ := hyx'
    have hTx : ∀ j, T j (β • fun i => algebraMap K K' (x i)) ∈ Submodule.span K {x} := fun j => by
      rw [Submodule.mem_span_singleton]
      refine ⟨τ j β, funext fun i => ?_⟩
      simp only [T, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm β, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    have hrec : (β • fun i => algebraMap K K' (x i)) = ∑ j, b j • f (T j (β • fun i => algebraMap K K' (x i))) :=
      funext fun i => by
        rw [Finset.sum_apply]
        refine (hz _).trans (Finset.sum_congr rfl fun j _ => ?_)
        simp only [f, Pi.smul_apply]
        rw [Algebra.smul_def, mul_comm]; rfl
    rw [hrec]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hTL j, hTx j⟩, rfl⟩)

end GlobalTheory.LineBC
