import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExistsUnifFv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasureEqOfCos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts

noncomputable section

namespace GlobalTheory.GramPreimageLB

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabS Topology Filter
open scoped TensorProduct ENNReal

def DiffOpenOnLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ)
      (b : Module.Basis (Fin d) F E) (x : Fin a → Fin M → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) x →
      IsOpen ((fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) '' (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E)))

def GramFiltration : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (b : Module.Basis (Fin d) F E)
      (x : Fin a → Fin M → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) x →
      ∃ N ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E), ∀ y, y - x ∈ N →
        ∀ Λ0, scaledB (Fv F v) (latSub b v a M) Λ0 →
          (Λ0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ⊆ N →
        ∃ (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
          (H : ℕ → AddSubgroup (HermR (Fv F v) σ a))
          (D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a),
          Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
          (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
          (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
          (∀ n, (Λ n).map D = H n) ∧
          ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ hσ J hJ (y + Z + W) - gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈
              H (n + 1)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hdet a _h1 v d b x hx`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `: IsArtinianRing (Fv F v ⊗[F] E)` using `IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)`. Establish `: IsReduced (Fv F v ⊗[F] E)` using `isReduced_tens_field F E (Fv F v)`. Establish `hss : IsSemisimpleRing (Fv F v ⊗[F] E)` using `IsArtinianRing.isSemisimpleRing_of_isReduced _`.

Establish `: IsTopologicalAddGroup (Fv F v ⊗[F] E)` using `IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)`. Take `⟨q, hq⟩` from `h F E σ hσ M J hJ hdet (Fv F v) hss a x hx`. Use `set T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) := fun S j k => ∑ i', (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * S i' j) * q k i' with hT`. Establish `hTc : Continuous T`. Use `continuous_pi fun j => continuous_pi fun k => continuous_finsetSum _ fun i' _ => ?_` and prove the remaining obligations.

Conclude with `(continuous_const.mul (continuous_id.matrix_elem i' j)).mul continuous_const`. Establish `hT0 : T 0 = 0`. Use function extensionality and compare the values at `j k`. Simplify using `[hT]`. Use `set L := latSub b v a M with hL`.

Establish `hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))` using `(PositiveNearLattice.isClopen_latV b v a M).isOpen`. Use `set Dx : (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a := fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W with hDx`. Establish `hDB : ∀ W, (Dx W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J x W`. Introduce `W`. Rewrite using `[← gramR_add_sub]`.

Both sides reduce to the same expression. Establish `hDadd : ∀ W W', Dx (W + W') = Dx W + Dx W'`. Introduce `W W'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubgroup.coe_add, hDB, hDB, hDB, gramB_add_right]`.

Establish `hDT : ∀ S : HermR (Fv F v) σ a, Dx (T S) = S`. Introduce `S`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hDB]`. Conclude with `hq S.1 S.2`.

Use `show IsOpen (Dx '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Establish `hU : IsOpen {S : HermR (Fv F v) σ a | T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L}` using `hLo.preimage (hTc.comp (continuous_subtype_val.comp (continuous_id.sub continuous_const)))`. Use `Filter.mem_of_superset (hU.mem_nhds ?_) ?_` and prove the remaining obligations.

Use `show T ((Dx l - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L`. Rewrite using `[sub_self, AddSubgroup.coe_zero, hT0]`. Conclude with `L.zero_mem`. Introduce `S hS`. Use `⟨l + T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), L.add_mem hl hS, ?_⟩` and prove the remaining obligations.

Rewrite using `[hDadd, hDT]`. Normalize the expressions using the abelian group laws.
-/
theorem diffOpenOnLattice_of (h : SecGram) : DiffOpenOnLattice := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet a _h1 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := isReduced_tens_field F E (Fv F v)
  have hss : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  obtain ⟨q, hq⟩ := h F E σ hσ M J hJ hdet (Fv F v) hss a x hx
  set T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun S j k => ∑ i', (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * S i' j) * q k i' with hT
  have hTc : Continuous T := by
    refine continuous_pi fun j => continuous_pi fun k => continuous_finsetSum _ fun i' _ => ?_
    exact (continuous_const.mul (continuous_id.matrix_elem i' j)).mul continuous_const
  have hT0 : T 0 = 0 := by
    funext j k
    simp [hT]
  set L := latSub b v a M with hL
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  set Dx : (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a := fun W =>
    gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W
    with hDx
  have hDB : ∀ W, (Dx W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J x W := by
    intro W
    rw [← gramR_add_sub]
    rfl
  have hDadd : ∀ W W', Dx (W + W') = Dx W + Dx W' := by
    intro W W'
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hDB, hDB, hDB, gramB_add_right]
  have hDT : ∀ S : HermR (Fv F v) σ a, Dx (T S) = S := by
    intro S
    apply Subtype.ext
    rw [hDB]
    exact hq S.1 S.2
  show IsOpen (Dx '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨l, hl, rfl⟩
  have hU : IsOpen {S : HermR (Fv F v) σ a | T ((S - Dx l : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L} :=
    hLo.preimage (hTc.comp (continuous_subtype_val.comp (continuous_id.sub continuous_const)))
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show T ((Dx l - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L
    rw [sub_self, AddSubgroup.coe_zero, hT0]
    exact L.zero_mem
  · intro S hS
    refine ⟨l + T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)),
      L.add_mem hl hS, ?_⟩
    rw [hDadd, hDT]
    abel

/- English proof (translation)
Introduce `F E _ _ _ _ σ hσ M J hJ hdet a ha1 v d b x hx`. Establish `: FiniteDimensional F E` using `Module.Finite.of_basis b`. Establish `: CharZero E` using `charZero_of_injective_algebraMap (algebraMap F E).injective`. Establish `hNE : NumberField E` using `{ to_charZero := inferInstance to_finiteDimensional := Module.Finite.trans F E }`. Use `locallyCompact_Fv F v` as an intermediate fact.

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

Use `show gramR (Fv F v) σ J (t • w) i j = t • t • gramR (Fv F v) σ J w i j`. Simplify using `only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right]`. Establish `hGc : Continuous G` using `continuous_gramH (Fv F v) σ hσ J hJ`. Establish `hxo : IsOpen (β x '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))`. Establish `h` using `hDx F E σ hσ M J hJ hdet a ha1 v d b x hx`.

Establish `e : (fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W) = β x`. Use function extensionality and compare the values at `W`. Rewrite using `[← hGdef, hG]`. Normalize the expressions using the abelian group laws. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Establish `hd : 0 < d`. Break down `Nat.eq_zero_or_pos d with h0 | h0` into its components or cases. Substitute `h0` using the available equality. It suffices to derive a contradiction. Establish `: (1 : E) = 0`.

Rewrite using `[← b.sum_repr (1 : E)]`. Simplify using the standard rewrite rules. Conclude with `one_ne_zero this`. Conclude with `h0`. Establish `hM : 0 < M`.

Break down `Nat.eq_zero_or_pos M with h0 | h0` into its components or cases. It suffices to derive a contradiction. Substitute `h0` using the available equality. Establish `: Nontrivial (Fv F v ⊗[F] E)` using `nontrivial_of_ne _ _ ((Algebra.TensorProduct.basis (Fv F v) b).ne_zero ⟨0, hd⟩)`. Conclude with `hx.ne_zero ⟨0, ha1⟩ (funext fun j => j.elim0)`.

Conclude with `h0`. Set `i0 : Fin a` to `⟨0, ha1⟩`. Set `j0 : Fin M` to `⟨0, hM⟩`. Set `k0 : Fin d` to `⟨0, hd⟩`. Set `φ : (Fin a → Fin M → Fv F v ⊗[F] E) → Fv F v` to `fun Y => PositiveNearLattice.crd b (Fv F v) (Y i0 j0) k0`.

Establish `hφc : Continuous φ` using `(PositiveNearLattice.continuous_crd b (Fv F v) k0).comp ((continuous_apply j0).comp (continuous_apply i0))`. Establish `hφs : ∀ (t : Fv F v) Y, φ (t • Y) = t * φ Y`. Introduce `t Y`. Use `show (Algebra.TensorProduct.basis (Fv F v) b).repr (t • Y i0 j0) k0 = t * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y i0 j0) k0`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Set `e0 : Fin a → Fin M → Fv F v ⊗[F] E` to `fun i j => if i = i0 ∧ j = j0 then inclR (Fv F v) (b k0) else 0`. Establish `he0L : e0 ∈ L`. Introduce `i j k`. Use `show PositiveNearLattice.crd b (Fv F v) (e0 i j) k ∈ v.adicCompletionIntegers F`. Distinguish the cases in `hij : i = i0 ∧ j = j0`.

Simplify using `only [e0, if_pos hij, PositiveNearLattice.crd_incl, b.repr_self, Finsupp.single_apply] split_ifs`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [e0, if_neg hij, PositiveNearLattice.crd, map_zero, Finsupp.zero_apply]`. Conclude with `zero_mem _`.

Establish `hφe : φ e0 = 1` using `by show PositiveNearLattice.crd b (Fv F v) (e0 i0 j0) k0 = 1`. Simplify using `[e0, PositiveNearLattice.crd_incl, b.repr_self]`. Establish `hsmall : ∀ U ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ N2 ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E), ∀ c : Fv F v, (∀ w ∈ L, c • w ∈ N2) → ∀ w ∈ L, c • G w ∈ U`. Introduce `U hU`. Establish `hT : ∀ᶠ t in 𝓝 (0 : Fv F v), ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U`.

Establish `hP : ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), ∀ᶠ q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) in 𝓝 ((0 : Fv F v), w), q.1 • G q.2 ∈ U`. Introduce `w _`. Establish `h : Tendsto (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2) (𝓝 ((0 : Fv F v), w)) (𝓝 (0 : HermR (Fv F v) σ a))`. Establish `hc : Continuous (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2)` using `continuous_fst.smul (hGc.comp continuous_snd)`. Use `hc.tendsto ((0 : Fv F v), w)` as an intermediate fact.

Simplify using `using this`. Conclude with `h hU`. Conclude with `hLc.eventually_forall_of_forall_eventually (P := fun (t : Fv F v) (w : Fin a → Fin M → Fv F v ⊗[F] E) => t • G w ∈ U) hP`. Use `⟨φ ⁻¹' {t | ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U}, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : φ 0 = 0`.

Use `hφs 0 0` as an intermediate fact. Simplify using `using this`. Conclude with `hφc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hT)`. Introduce `c hc w hw`. Establish `h` using `hc e0 he0L`.

Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, hφs, hφe, mul_one] at h`. Conclude with `h w hw`. Conclude with `filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall`.
-/
theorem gramFiltration_of (hDx : DiffOpenOnLattice) : GramFiltration := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 v d b x hx
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
    have h := hDx F E σ hσ M J hJ hdet a ha1 v d b x hx
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
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso
      subst h0
      have : Nontrivial (Fv F v ⊗[F] E) :=
        nontrivial_of_ne _ _ ((Algebra.TensorProduct.basis (Fv F v) b).ne_zero ⟨0, hd⟩)
      exact hx.ne_zero ⟨0, ha1⟩ (funext fun j => j.elim0)
    · exact h0
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

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν x S0 hx hxS0 W hW hxW`. Take `⟨t1, t2, t3, t4, -⟩` from `GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v`. Use `haveI := t1`. Use `haveI := t2`. Use `haveI := t3`.

Use `haveI := t4`. Use `haveI := locallyCompact_Fv F v`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩`. Use `haveI : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))`.

Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `hσ : ∀ y, σ (σ y) = y` using `sigma_invol σ hCM.2.2.2`. Establish `hpre : ∀ S : Set (HermR (Fv F v) σ a), (gramR (Fv F v) σ J) ⁻¹' (Subtype.val '' S) = (gramH (Fv F v) σ hσ J hJ.1) ⁻¹' S`. Introduce `S`. Use extensionality with `y`.

Simplify using `only [Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsy⟩`. Establish `: gramH (Fv F v) σ hσ J hJ.1 y = s` using `Subtype.ext hsy.symm`. Rewrite using `[this]`.

Conclude with `hs`. Introduce `hy`. Conclude with `⟨_, hy, rfl⟩`. Break down `Nat.eq_zero_or_pos a with rfl | ha1` into its components or cases. Use `haveI : Subsingleton (HermR (Fv F v) σ 0) := ⟨fun s t => Subtype.ext (Matrix.ext fun i => i.elim0)⟩`.

Establish `hWu : W = Set.univ` using `Set.eq_univ_of_forall fun y => (Subsingleton.elim x y) ▸ hxW`. Establish `hμpos : μ Set.univ ≠ 0` using `(isOpen_univ.measure_pos μ ⟨x, trivial⟩).ne'`. Establish `hμfin : μ Set.univ ≠ ⊤` using `isCompact_univ.measure_lt_top.ne`. Establish `hνpos : ν Set.univ ≠ 0` using `(isOpen_univ.measure_pos ν ⟨S0, trivial⟩).ne'`. Establish `hνfin : ν Set.univ ≠ ⊤` using `isCompact_univ.measure_lt_top.ne`.

Use `⟨μ Set.univ / ν Set.univ, ENNReal.div_pos hμpos hνfin, ENNReal.div_ne_top hμfin hνpos, Set.univ, Filter.univ_mem, ?_⟩` and prove the remaining obligations. Introduce `S _ _`. Break down `S.eq_empty_or_nonempty with rfl | ⟨s, hs⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `hS : S = Set.univ` using `Set.eq_univ_of_forall fun t => Subsingleton.elim s t ▸ hs`.

Rewrite using `[hS, hpre, Set.preimage_univ, hWu, Set.univ_inter, ENNReal.div_mul_cancel hνpos hνfin]`. Set `b` to `Module.finBasis F E set G := gramH (n := a) (Fv F v) σ hσ J hJ.1 with hGdef`. Establish `hGx : G x = S0` using `Subtype.ext hxS0`. Take `⟨N, hN, hd⟩` from `gramFiltration_of (diffOpenOnLattice_of secGram_holds) F E σ hσ n J hJ.1 hJ.2 a ha1 v _ b x hx`. Establish `hWx : (fun w => x + w) ⁻¹' W ∈ 𝓝 (0 : Fin a → Fin n → Fv F v ⊗[F] E)` using `(continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hxW)`.

Take `⟨Λ0, hB, -, -, hsub⟩` from `isCOBasis_latSub b v a n _ (inter_mem hN hWx)`. Take `⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩` from `hd x (by rw [sub_self]; exact mem_of_mem_nhds hN) Λ0 hB (fun z hz => (hsub hz).1)`. Establish `hΛW : ∀ z, z - x ∈ Λ 0 → z ∈ W`. Introduce `z hz`. Rewrite `hz` using `[h0]`.

Establish `h` using `(hsub hz).2`. Simplify using `only [Set.mem_preimage, add_sub_cancel] at h`. Conclude with `h`. Establish `hHa : Antitone H`. Introduce `i j hij`.

Rewrite using `[← hD, ← hD]`. Conclude with `AddSubgroup.map_mono (hΛa hij)`. Establish `hDW : ∀ k Z, Z ∈ Λ k → D Z ∈ H k` using `fun k Z hZ => hD k ▸ AddSubgroup.mem_map_of_mem D hZ`. Use `set Q : Set (Fin a → Fin n → Fv F v ⊗[F] E) := {z | z - x ∈ Λ 0} with hQ`. Use `set C : Set (HermR (Fv F v) σ a) := {z | z - S0 ∈ H 0} with hC`.

Establish `hQc : IsCompact Q` using `isCompact_cos (Λ 0) (hΛc 0) x`. Establish `hCc : IsCompact C` using `isCompact_cos (H 0) (hHc 0) S0`. Establish `hCo : IsOpen C` using `(hHo 0).preimage (continuous_id.sub continuous_const)`. Establish `hQC : ∀ z ∈ Q, G z ∈ C`. Introduce `z hz`.

Establish `h1` using `hyp 0 0 (Λ 0).zero_mem (z - x) hz`. Establish `e1 : x + 0 + (z - x) = z` using `by abel`. Rewrite `h1` using `[e1, add_zero]`. Use `show G z - S0 ∈ H 0`. Establish `e : G z - S0 = (G z - G x - D (z - x)) + D (z - x)` using `by rw [hGx]; abel`.

Rewrite using `[e]`. Conclude with `(H 0).add_mem (hHa (Nat.zero_le 1) h1) (hDW 0 _ hz)`. Establish `hGm : Measurable G` using `(continuous_gramH (Fv F v) σ hσ J hJ.1).measurable`. Use `haveI : LocallyCompactSpace (HermR (Fv F v) σ a) := (hHc 0).locallyCompactSpace_of_mem_nhds_of_addGroup ((hHo 0).mem_nhds (H 0).zero_mem)`. Establish `hΛ0pos : μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) ≠ 0` using `((hΛo 0).measure_pos μ ⟨0, zero_mem _⟩).ne'`.

Establish `hΛ0fin : μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) ≠ ⊤` using `((hΛc 0).measure_lt_top).ne`. Establish `hH0pos : ν (H 0 : Set (HermR (Fv F v) σ a)) ≠ 0` using `((hHo 0).measure_pos ν ⟨0, zero_mem _⟩).ne'`. Establish `hH0fin : ν (H 0 : Set (HermR (Fv F v) σ a)) ≠ ⊤` using `((hHc 0).measure_lt_top).ne`. Use `set κ := μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) / ν (H 0 : Set (HermR (Fv F v) σ a)) with hκ`. Set `m : Measure (HermR (Fv F v) σ a)` to `(μ.restrict Q).map G`.

Establish `hm : ∀ s, MeasurableSet s → m s = μ (G ⁻¹' s ∩ Q)` using `fun s hs => by`. Rewrite using `[Measure.map_apply hGm hs, Measure.restrict_apply (hGm hs)]`. Use `haveI : IsFiniteMeasure m := by`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[hm _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]`.

Conclude with `hQc.measure_lt_top`. Establish `hmC : m Cᶜ = 0`. Rewrite using `[hm _ hCo.measurableSet.compl]`. Establish `: G ⁻¹' Cᶜ ∩ Q = ∅` using `Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.1 (hQC z hz.2)`. Rewrite using `[this, measure_empty]`.

Establish `hcos : ∀ k h, h - S0 ∈ H 0 → m {z | z - h ∈ H k} = κ * ν {z | z - h ∈ H k}`. Introduce `k h hh`. Establish `hmeas : MeasurableSet {z : HermR (Fv F v) σ a | z - h ∈ H k}` using `((hHo k).preimage (continuous_id.sub continuous_const)).measurableSet`. Establish `hνt : ν {z | z - h ∈ H k} = ν (H k)`. Establish `: {z : HermR (Fv F v) σ a | z - h ∈ H k} = (fun w => w + -h) ⁻¹' (H k : Set _)`.

Use extensionality with `z`. Simplify using `[sub_eq_add_neg]`. Rewrite using `[this, measure_preimage_add_right]`. Establish `hyT : G x - h ∈ H 0`. Rewrite using `[hGx]`.

Use `(H 0).neg_mem hh` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Establish `e` using `cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G x hyp h hyT k`. Rewrite using `[hm _ hmeas, hνt, Set.inter_comm]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcmp` using `cosDens_holds (HermR (Fv F v) σ a) ν m inferInstance H hHo hHc hHa hHb S0 κ hmC hcos`. Establish `hκpos : 0 < κ` using `ENNReal.div_pos_iff.2 ⟨hΛ0pos, hH0fin⟩`. Establish `hκfin : κ ≠ ⊤` using `ENNReal.div_ne_top hΛ0fin hH0pos`. Use `⟨κ, hκpos, hκfin, C, hCo.mem_nhds (by simp [hC, (H 0).zero_mem]), ?_⟩` and prove the remaining obligations. Introduce `S hSC hSm`.

Rewrite using `[hpre]`. Establish `hνS : ν S ≠ ⊤` using `ne_top_of_le_ne_top hCc.measure_lt_top.ne (measure_mono hSC)`. Use `haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))`. Use `haveI : SecondCountableTopology (HermR (Fv F v) σ a) := Topology.IsInducing.subtypeVal.secondCountableTopology`. Use `haveI : ν.Regular := Measure.regular_of_isAddLeftInvariant (hHc 0) ⟨0, mem_interior_iff_mem_nhds.2 ((hHo 0).mem_nhds (H 0).zero_mem)⟩ hH0fin`.

Rewrite using `[hSm.measure_eq_iSup_isCompact_of_ne_top hνS, ENNReal.mul_iSup]`. Use `iSup_le fun K => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.mul_iSup]`. Use `iSup_le fun hKS => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.mul_iSup]`.

Use `iSup_le fun hKc => ?_` and prove the remaining obligations. Establish `e` using `hcmp K hKc`. Rewrite `e` using `[Set.inter_eq_left.2 (hKS.trans hSC)]`. Rewrite using `[← e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lb_gram_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ)
    (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E)
    (S0 : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x →
    gramR (Fv F v) σ J x = (S0 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) →
    ∀ W : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsOpen W → x ∈ W →
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S0, ∀ S ⊆ N, MeasurableSet S →
      c * ν S ≤ μ ((gramR (Fv F v) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν x S0 hx hxS0 W hW hxW
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := locallyCompact_Fv F v
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  haveI : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ y, σ (σ y) = y := sigma_invol σ hCM.2.2.2
  have hpre : ∀ S : Set (HermR (Fv F v) σ a), (gramR (Fv F v) σ J) ⁻¹' (Subtype.val '' S) =
      (gramH (Fv F v) σ hσ J hJ.1) ⁻¹' S := by
    intro S
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hsy⟩
      have : gramH (Fv F v) σ hσ J hJ.1 y = s := Subtype.ext hsy.symm
      rw [this]
      exact hs
    · intro hy
      exact ⟨_, hy, rfl⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · haveI : Subsingleton (HermR (Fv F v) σ 0) :=
      ⟨fun s t => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    have hWu : W = Set.univ := Set.eq_univ_of_forall fun y => (Subsingleton.elim x y) ▸ hxW
    have hμpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ ⟨x, trivial⟩).ne'
    have hμfin : μ Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
    have hνpos : ν Set.univ ≠ 0 := (isOpen_univ.measure_pos ν ⟨S0, trivial⟩).ne'
    have hνfin : ν Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
    refine ⟨μ Set.univ / ν Set.univ, ENNReal.div_pos hμpos hνfin, ENNReal.div_ne_top hμfin hνpos,
      Set.univ, Filter.univ_mem, ?_⟩
    intro S _ _
    rcases S.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
    · simp
    · have hS : S = Set.univ := Set.eq_univ_of_forall fun t => Subsingleton.elim s t ▸ hs
      rw [hS, hpre, Set.preimage_univ, hWu, Set.univ_inter, ENNReal.div_mul_cancel hνpos hνfin]
  · let b := Module.finBasis F E
    set G := gramH (n := a) (Fv F v) σ hσ J hJ.1 with hGdef
    have hGx : G x = S0 := Subtype.ext hxS0
    obtain ⟨N, hN, hd⟩ :=
      gramFiltration_of (diffOpenOnLattice_of secGram_holds) F E σ hσ n J hJ.1 hJ.2 a ha1 v _ b x hx
    have hWx : (fun w => x + w) ⁻¹' W ∈ 𝓝 (0 : Fin a → Fin n → Fv F v ⊗[F] E) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
        (by simpa using hW.mem_nhds hxW)
    obtain ⟨Λ0, hB, -, -, hsub⟩ := isCOBasis_latSub b v a n _ (inter_mem hN hWx)
    obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ :=
      hd x (by rw [sub_self]; exact mem_of_mem_nhds hN) Λ0 hB (fun z hz => (hsub hz).1)
    have hΛW : ∀ z, z - x ∈ Λ 0 → z ∈ W := by
      intro z hz
      rw [h0] at hz
      have h := (hsub hz).2
      simp only [Set.mem_preimage, add_sub_cancel] at h
      exact h
    have hHa : Antitone H := by
      intro i j hij
      rw [← hD, ← hD]
      exact AddSubgroup.map_mono (hΛa hij)
    have hDW : ∀ k Z, Z ∈ Λ k → D Z ∈ H k := fun k Z hZ => hD k ▸ AddSubgroup.mem_map_of_mem D hZ
    set Q : Set (Fin a → Fin n → Fv F v ⊗[F] E) := {z | z - x ∈ Λ 0} with hQ
    set C : Set (HermR (Fv F v) σ a) := {z | z - S0 ∈ H 0} with hC
    have hQc : IsCompact Q := isCompact_cos (Λ 0) (hΛc 0) x
    have hCc : IsCompact C := isCompact_cos (H 0) (hHc 0) S0
    have hCo : IsOpen C := (hHo 0).preimage (continuous_id.sub continuous_const)
    have hQC : ∀ z ∈ Q, G z ∈ C := by
      intro z hz
      have h1 := hyp 0 0 (Λ 0).zero_mem (z - x) hz
      have e1 : x + 0 + (z - x) = z := by abel
      rw [e1, add_zero] at h1
      show G z - S0 ∈ H 0
      have e : G z - S0 = (G z - G x - D (z - x)) + D (z - x) := by rw [hGx]; abel
      rw [e]
      exact (H 0).add_mem (hHa (Nat.zero_le 1) h1) (hDW 0 _ hz)
    have hGm : Measurable G := (continuous_gramH (Fv F v) σ hσ J hJ.1).measurable
    haveI : LocallyCompactSpace (HermR (Fv F v) σ a) :=
      (hHc 0).locallyCompactSpace_of_mem_nhds_of_addGroup ((hHo 0).mem_nhds (H 0).zero_mem)
    have hΛ0pos : μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) ≠ 0 :=
      ((hΛo 0).measure_pos μ ⟨0, zero_mem _⟩).ne'
    have hΛ0fin : μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) ≠ ⊤ :=
      ((hΛc 0).measure_lt_top).ne
    have hH0pos : ν (H 0 : Set (HermR (Fv F v) σ a)) ≠ 0 :=
      ((hHo 0).measure_pos ν ⟨0, zero_mem _⟩).ne'
    have hH0fin : ν (H 0 : Set (HermR (Fv F v) σ a)) ≠ ⊤ := ((hHc 0).measure_lt_top).ne
    set κ := μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) / ν (H 0 : Set (HermR (Fv F v) σ a))
      with hκ
    let m : Measure (HermR (Fv F v) σ a) := (μ.restrict Q).map G
    have hm : ∀ s, MeasurableSet s → m s = μ (G ⁻¹' s ∩ Q) := fun s hs => by
      rw [Measure.map_apply hGm hs, Measure.restrict_apply (hGm hs)]
    haveI : IsFiniteMeasure m := by
      refine ⟨?_⟩
      rw [hm _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
      exact hQc.measure_lt_top
    have hmC : m Cᶜ = 0 := by
      rw [hm _ hCo.measurableSet.compl]
      have : G ⁻¹' Cᶜ ∩ Q = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.1 (hQC z hz.2)
      rw [this, measure_empty]
    have hcos : ∀ k h, h - S0 ∈ H 0 → m {z | z - h ∈ H k} = κ * ν {z | z - h ∈ H k} := by
      intro k h hh
      have hmeas : MeasurableSet {z : HermR (Fv F v) σ a | z - h ∈ H k} :=
        ((hHo k).preimage (continuous_id.sub continuous_const)).measurableSet
      have hνt : ν {z | z - h ∈ H k} = ν (H k) := by
        have : {z : HermR (Fv F v) σ a | z - h ∈ H k} = (fun w => w + -h) ⁻¹' (H k : Set _) := by
          ext z
          simp [sub_eq_add_neg]
        rw [this, measure_preimage_add_right]
      have hyT : G x - h ∈ H 0 := by
        rw [hGx]
        have := (H 0).neg_mem hh
        rwa [neg_sub] at this
      have e := cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G x hyp h hyT k
      rw [hm _ hmeas, hνt, Set.inter_comm]
      calc μ (Q ∩ G ⁻¹' {z | z - h ∈ H k})
          = μ (Q ∩ G ⁻¹' {z | z - h ∈ H k}) * ν (H 0 : Set (HermR (Fv F v) σ a)) /
              ν (H 0 : Set (HermR (Fv F v) σ a)) :=
            (ENNReal.mul_div_cancel_right hH0pos hH0fin).symm
        _ = μ (Λ 0 : Set (Fin a → Fin n → Fv F v ⊗[F] E)) * ν (H k : Set (HermR (Fv F v) σ a)) /
              ν (H 0 : Set (HermR (Fv F v) σ a)) := by rw [e]
        _ = κ * ν (H k : Set (HermR (Fv F v) σ a)) := ENNReal.mul_div_right_comm
    have hcmp := cosDens_holds (HermR (Fv F v) σ a) ν m inferInstance H hHo hHc hHa hHb S0 κ hmC hcos
    have hκpos : 0 < κ := ENNReal.div_pos_iff.2 ⟨hΛ0pos, hH0fin⟩
    have hκfin : κ ≠ ⊤ := ENNReal.div_ne_top hΛ0fin hH0pos
    refine ⟨κ, hκpos, hκfin, C, hCo.mem_nhds (by simp [hC, (H 0).zero_mem]), ?_⟩
    intro S hSC hSm
    rw [hpre]
    have hνS : ν S ≠ ⊤ := ne_top_of_le_ne_top hCc.measure_lt_top.ne (measure_mono hSC)
    haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    haveI : SecondCountableTopology (HermR (Fv F v) σ a) :=
      Topology.IsInducing.subtypeVal.secondCountableTopology
    haveI : ν.Regular := Measure.regular_of_isAddLeftInvariant (hHc 0)
      ⟨0, mem_interior_iff_mem_nhds.2 ((hHo 0).mem_nhds (H 0).zero_mem)⟩ hH0fin
    rw [hSm.measure_eq_iSup_isCompact_of_ne_top hνS, ENNReal.mul_iSup]
    refine iSup_le fun K => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hKS => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hKc => ?_
    have e := hcmp K hKc
    rw [Set.inter_eq_left.2 (hKS.trans hSC)] at e
    rw [← e]
    calc m K ≤ m S := measure_mono hKS
      _ = μ (G ⁻¹' S ∩ Q) := hm S hSm
      _ ≤ μ (G ⁻¹' S ∩ W) := measure_mono (Set.inter_subset_inter_right _ fun z hz => hΛW z hz)

end GlobalTheory.GramPreimageLB
