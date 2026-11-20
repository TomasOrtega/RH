import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDxSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hR_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J (t • x) y = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hR_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J x (t • y) = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)`. Rewrite using `[v.valuedAdicCompletion_eq_valuation' π, hπ]`. Establish `h1 : Valued.v (π : v.adicCompletion F) < 1`. Rewrite using `[hv]`.

Evaluate the decidable proposition. Use `⟨π, fun h => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hlt : ‖(π : v.adicCompletion F)‖ < 1` using `Valued.toNormedField.norm_lt_one_iff.2 h1`.

Conclude with `tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `h1.le`.
-/
theorem exists_unif_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
    rw [hv]
    decide
  refine ⟨π, fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

/- English proof (translation)
Introduce `F E _ _ _ _ σ hσ M J hJ hdet a ha1 ha2 v d b x hx`. Establish `: FiniteDimensional F E` using `Module.Finite.of_basis b`. Establish `: CharZero E` using `charZero_of_injective_algebraMap (algebraMap F E).injective`. Establish `hNE : NumberField E` using `{ to_charZero := inferInstance to_finiteDimensional := Module.Finite.trans F E }`. Use `locallyCompact_Fv F v` as an intermediate fact.

Establish `: IsModuleTopology (Fv F v) (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalAddGroup (Fv F v ⊗[F] E)` using `IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)`. Establish `: T2Space (Fv F v ⊗[F] E)`. Take `⟨ι, _, ⟨h⟩⟩` from `PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)`. Conclude with `h.isEmbedding.t2Space`.

Establish `: ContinuousSMul (Fv F v) (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (ContinuousSMul (Fv F v) (Fin a → Fin a → Fv F v ⊗[F] E))`. Establish `: T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))`. Establish `: ContinuousSMul (Fv F v) (HermR (Fv F v) σ a)`. Use `⟨continuous_induced_rng.2 ?_⟩` and prove the remaining obligations. Use `show Continuous fun p : Fv F v × HermR (Fv F v) σ a => p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))`.

Conclude with `continuous_fst.smul (continuous_subtype_val.comp continuous_snd)`. Take `⟨π, hπ0, hπ, hπO⟩` from `exists_unif_Fv v`. Use `set L := latSub b v a M with hLdef`. Establish `hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))` using `(PositiveNearLattice.isClopen_latV b v a M).isOpen`. Establish `hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))` using `PositiveNearLattice.isCompact_latV b v a M`.

Establish `hπL : ∀ w ∈ L, π • w ∈ L`. Introduce `w hw i j k`. Establish `h` using `hw i j k`. Use `show (Algebra.TensorProduct.basis (Fv F v) b).repr (π • w i j) k ∈ v.adicCompletionIntegers F`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `mul_mem hπO h`. Set `β : (Fin a → Fin M → Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a` to `fun u w => ⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ u w⟩`. Establish `hβc : Continuous fun q : (Fin a → Fin M → Fv F v ⊗[F] E) × (Fin a → Fin M → Fv F v ⊗[F] E) => β q.1 q.2` using `(continuous_gramB (Fv F v) σ J).subtype_mk _`. Establish `hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w`. Introduce `u u' w`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Use `show gramB (Fv F v) σ J (u + u') w i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u' w i j`. Simplify using `only [gramB, Pi.add_apply, hR_add_left, hR_add_right]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hβ2 : ∀ u w w', β u (w + w') = β u w + β u w'`. Introduce `u w w'`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Use `show gramB (Fv F v) σ J u (w + w') i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u w' i j`.

Simplify using `only [gramB, Pi.add_apply, hR_add_left, hR_add_right]`. Expand and normalize the polynomial expressions, which then agree. Establish `hβs : ∀ (t : Fv F v) u w, β u (t • w) = t • β u w`. Introduce `t u w`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i j`. Use `show gramB (Fv F v) σ J u (t • w) i j = t • gramB (Fv F v) σ J u w i j`. Simplify using `only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]`. Use `set G := gramH (Fv F v) σ hσ J hJ (n := a) with hGdef`. Establish `hG : ∀ u W, G (u + W) = G u + β u W + G W`.

Introduce `u W`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Use `show gramR (Fv F v) σ J (u + W) i j = gramR (Fv F v) σ J u i j + gramB (Fv F v) σ J u W i j + gramR (Fv F v) σ J W i j`. Simplify using `only [gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hGs : ∀ (t : Fv F v) w, G (t • w) = t • t • G w`. Introduce `t w`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`.

Use `show gramR (Fv F v) σ J (t • w) i j = t • t • gramR (Fv F v) σ J w i j`. Simplify using `only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right]`. Establish `hGc : Continuous G` using `continuous_gramH (Fv F v) σ hσ J hJ`. Establish `hxo : IsOpen (β x '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))`. Establish `h` using `hDx F E σ hσ M J hJ hdet a ha1 ha2 v d b x hx`.

Establish `e : (fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W) = β x`. Use function extensionality and compare the values at `W`. Rewrite using `[← hGdef, hG]`. Normalize the expressions using the abelian group laws. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Establish `hd : 0 < d`. Break down `Nat.eq_zero_or_pos d with h0 | h0` into its components or cases. Substitute `h0` using the available equality. It suffices to derive a contradiction. Establish `: (1 : E) = 0`.

Rewrite using `[← b.sum_repr (1 : E)]`. Simplify using the standard rewrite rules. Conclude with `one_ne_zero this`. Conclude with `h0`. Establish `hM : 0 < M` using `by omega`.

Set `i0 : Fin a` to `⟨0, ha1⟩`. Set `j0 : Fin M` to `⟨0, hM⟩`. Set `k0 : Fin d` to `⟨0, hd⟩`. Set `φ : (Fin a → Fin M → Fv F v ⊗[F] E) → Fv F v` to `fun Y => PositiveNearLattice.crd b (Fv F v) (Y i0 j0) k0`. Establish `hφc : Continuous φ` using `(PositiveNearLattice.continuous_crd b (Fv F v) k0).comp ((continuous_apply j0).comp (continuous_apply i0))`.

Establish `hφs : ∀ (t : Fv F v) Y, φ (t • Y) = t * φ Y`. Introduce `t Y`. Use `show (Algebra.TensorProduct.basis (Fv F v) b).repr (t • Y i0 j0) k0 = t * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y i0 j0) k0`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Set `e0 : Fin a → Fin M → Fv F v ⊗[F] E` to `fun i j => if i = i0 ∧ j = j0 then inclR (Fv F v) (b k0) else 0`.

Establish `he0L : e0 ∈ L`. Introduce `i j k`. Use `show PositiveNearLattice.crd b (Fv F v) (e0 i j) k ∈ v.adicCompletionIntegers F`. Distinguish the cases in `hij : i = i0 ∧ j = j0`. Simplify using `only [e0, if_pos hij, PositiveNearLattice.crd_incl, b.repr_self, Finsupp.single_apply] split_ifs`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [e0, if_neg hij, PositiveNearLattice.crd, map_zero, Finsupp.zero_apply]`. Conclude with `zero_mem _`. Establish `hφe : φ e0 = 1` using `by show PositiveNearLattice.crd b (Fv F v) (e0 i0 j0) k0 = 1`.

Simplify using `[e0, PositiveNearLattice.crd_incl, b.repr_self]`. Establish `hsmall : ∀ U ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ N2 ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E), ∀ c : Fv F v, (∀ w ∈ L, c • w ∈ N2) → ∀ w ∈ L, c • G w ∈ U`. Introduce `U hU`. Establish `hT : ∀ᶠ t in 𝓝 (0 : Fv F v), ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U`. Establish `hP : ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), ∀ᶠ q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) in 𝓝 ((0 : Fv F v), w), q.1 • G q.2 ∈ U`.

Introduce `w _`. Establish `h : Tendsto (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2) (𝓝 ((0 : Fv F v), w)) (𝓝 (0 : HermR (Fv F v) σ a))`. Establish `hc : Continuous (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2)` using `continuous_fst.smul (hGc.comp continuous_snd)`. Use `hc.tendsto ((0 : Fv F v), w)` as an intermediate fact. Simplify using `using this`.

Conclude with `h hU`. Conclude with `hLc.eventually_forall_of_forall_eventually (P := fun (t : Fv F v) (w : Fin a → Fin M → Fv F v ⊗[F] E) => t • G w ∈ U) hP`. Use `⟨φ ⁻¹' {t | ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U}, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : φ 0 = 0`. Use `hφs 0 0` as an intermediate fact.

Simplify using `using this`. Conclude with `hφc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hT)`. Introduce `c hc w hw`. Establish `h` using `hc e0 he0L`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, hφs, hφe, mul_one] at h`.

Conclude with `h w hw`. Conclude with `filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall`.
-/
theorem gramFilt_of (hDx : DxOpen) : GramFilt := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 ha2 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hNE : NumberField E :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F E }
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : ContinuousSMul (Fv F v) (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (Fv F v) (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
    refine ⟨continuous_induced_rng.2 ?_⟩
    show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
      p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  obtain ⟨π, hπ0, hπ, hπO⟩ := exists_unif_Fv v
  set L := latSub b v a M with hLdef
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := by
    intro w hw i j k
    have h := hw i j k
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (π • w i j) k ∈ v.adicCompletionIntegers F
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hπO h
  let β : (Fin a → Fin M → Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) →
      HermR (Fv F v) σ a := fun u w => ⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ u w⟩
  have hβc : Continuous fun q : (Fin a → Fin M → Fv F v ⊗[F] E) × (Fin a → Fin M → Fv F v ⊗[F] E) =>
      β q.1 q.2 := (continuous_gramB (Fv F v) σ J).subtype_mk _
  have hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w := by
    intro u u' w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J (u + u') w i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u' w i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβ2 : ∀ u w w', β u (w + w') = β u w + β u w' := by
    intro u w w'
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (w + w') i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u w' i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβs : ∀ (t : Fv F v) u w, β u (t • w) = t • β u w := by
    intro t u w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (t • w) i j = t • gramB (Fv F v) σ J u w i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]
  set G := gramH (Fv F v) σ hσ J hJ (n := a) with hGdef
  have hG : ∀ u W, G (u + W) = G u + β u W + G W := by
    intro u W
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (u + W) i j =
      gramR (Fv F v) σ J u i j + gramB (Fv F v) σ J u W i j + gramR (Fv F v) σ J W i j
    simp only [gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hGs : ∀ (t : Fv F v) w, G (t • w) = t • t • G w := by
    intro t w
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (t • w) i j = t • t • gramR (Fv F v) σ J w i j
    simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right]
  have hGc : Continuous G := continuous_gramH (Fv F v) σ hσ J hJ
  have hxo : IsOpen (β x '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))) := by
    have h := hDx F E σ hσ M J hJ hdet a ha1 ha2 v d b x hx
    have e : (fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) = β x := by
      funext W
      rw [← hGdef, hG]
      abel
    rwa [e] at h

  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      exfalso
      have : (1 : E) = 0 := by
        rw [← b.sum_repr (1 : E)]
        simp
      exact one_ne_zero this
    · exact h0
  have hM : 0 < M := by omega
  let i0 : Fin a := ⟨0, ha1⟩
  let j0 : Fin M := ⟨0, hM⟩
  let k0 : Fin d := ⟨0, hd⟩
  let φ : (Fin a → Fin M → Fv F v ⊗[F] E) → Fv F v := fun Y => PositiveNearLattice.crd b (Fv F v) (Y i0 j0) k0
  have hφc : Continuous φ :=
    (PositiveNearLattice.continuous_crd b (Fv F v) k0).comp ((continuous_apply j0).comp (continuous_apply i0))
  have hφs : ∀ (t : Fv F v) Y, φ (t • Y) = t * φ Y := by
    intro t Y
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (t • Y i0 j0) k0 =
      t * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y i0 j0) k0
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e0 : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    if i = i0 ∧ j = j0 then inclR (Fv F v) (b k0) else 0
  have he0L : e0 ∈ L := by
    intro i j k
    show PositiveNearLattice.crd b (Fv F v) (e0 i j) k ∈ v.adicCompletionIntegers F
    by_cases hij : i = i0 ∧ j = j0
    · simp only [e0, if_pos hij, PositiveNearLattice.crd_incl, b.repr_self, Finsupp.single_apply]
      split_ifs
      · simp
      · simp
    · simp only [e0, if_neg hij, PositiveNearLattice.crd, map_zero, Finsupp.zero_apply]
      exact zero_mem _
  have hφe : φ e0 = 1 := by
    show PositiveNearLattice.crd b (Fv F v) (e0 i0 j0) k0 = 1
    simp [e0, PositiveNearLattice.crd_incl, b.repr_self]
  have hsmall : ∀ U ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ N2 ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E),
      ∀ c : Fv F v, (∀ w ∈ L, c • w ∈ N2) → ∀ w ∈ L, c • G w ∈ U := by
    intro U hU
    have hT : ∀ᶠ t in 𝓝 (0 : Fv F v), ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
        t • G w ∈ U := by
      have hP : ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
          ∀ᶠ q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) in 𝓝 ((0 : Fv F v), w), q.1 • G q.2 ∈ U := by
        intro w _
        have h : Tendsto (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2)
            (𝓝 ((0 : Fv F v), w)) (𝓝 (0 : HermR (Fv F v) σ a)) := by
          have hc : Continuous (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2) :=
            continuous_fst.smul (hGc.comp continuous_snd)
          have := hc.tendsto ((0 : Fv F v), w)
          simpa using this
        exact h hU
      exact hLc.eventually_forall_of_forall_eventually
        (P := fun (t : Fv F v) (w : Fin a → Fin M → Fv F v ⊗[F] E) => t • G w ∈ U) hP
    refine ⟨φ ⁻¹' {t | ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U}, ?_, ?_⟩
    · have h0 : φ 0 = 0 := by
        have := hφs 0 0
        simpa using this
      exact hφc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hT)
    · intro c hc w hw
      have h := hc e0 he0L
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hφs, hφe, mul_one] at h
      exact h w hw
  exact filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall

end PI.VolStabS
