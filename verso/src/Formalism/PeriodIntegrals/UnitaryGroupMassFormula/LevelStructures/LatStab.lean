import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatTop

noncomputable section

namespace MassDataLevelSSteps.LatTop

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets Matrix MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation

section Open

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap F (Fv F v)) N]`. Conclude with `(map_ne_zero (algebraMap F (Fv F v))).mpr (Int.cast_ne_zero.mpr hN)`.
-/
theorem intCast_ne_zero_Fv {N : ℤ} (hN : N ≠ 0) : (N : Fv F v) ≠ 0 := by
  rw [← map_intCast (algebraMap F (Fv F v)) N]
  exact (map_ne_zero (algebraMap F (Fv F v))).mpr (Int.cast_ne_zero.mpr hN)

/- English proof (translation)
Establish `hN : ∀ q, ∃ N : ℤ, N ≠ 0 ∧ N • x q ∈ L` using `fun q => exists_int_smul_mem L hL _`. Use `choose Nf hNf hNm using hN`. Use `⟨∏ q, Nf q, Finset.prod_ne_zero_iff.2 fun q _ => hNf q, fun q => ?_⟩` and prove the remaining obligations. Establish `hq : ∏ q, Nf q = (∏ q' ∈ Finset.univ.erase q, Nf q') * Nf q` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ q)).symm`. Rewrite using `[hq, mul_smul]`.

Conclude with `zsmul_mem (hNm q) _`.
-/
theorem exists_common_mult {ι : Type} [Fintype ι] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : ι → Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ q, N • x q ∈ L := by
  classical
  have hN : ∀ q, ∃ N : ℤ, N ≠ 0 ∧ N • x q ∈ L := fun q => exists_int_smul_mem L hL _
  choose Nf hNf hNm using hN
  refine ⟨∏ q, Nf q, Finset.prod_ne_zero_iff.2 fun q _ => hNf q, fun q => ?_⟩
  have hq : ∏ q, Nf q = (∏ q' ∈ Finset.univ.erase q, Nf q') * Nf q :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ q)).symm
  rw [hq, mul_smul]
  exact zsmul_mem (hNm q) _

/- English proof (translation)
Use `set M := latLoc (E := E) v (L : Set (Fin n → E))`. Set `b` to `Module.finBasis F E`. Set `Bt` to `Algebra.TensorProduct.basis (Fv F v) b`. Take `⟨N, hN0, hNmem⟩` from `exists_common_mult L hL (fun q : Fin n × Fin (Module.finrank F E) => (Pi.single q.1 (b q.2) : Fin n → E))`. Establish `hNv : (N : Fv F v) ≠ 0` using `intCast_ne_zero_Fv v hN0`.

Establish `hsingle : ∀ j k, (N : Fv F v) • (Pi.single j (Bt k) : Fin n → Fv F v ⊗[F] E) ∈ M`. Introduce `j k`. Rewrite using `[Algebra.TensorProduct.basis_apply, ← ratV_zsmul_single v N j (b k)]`. Conclude with `Submodule.subset_span ⟨_, hNmem (j, k), rfl⟩`. Establish `hcoord : ∀ j (z : Fv F v ⊗[F] E), (∀ k, Bt.repr z k ∈ v.adicCompletionIntegers F) → (N : Fv F v) • (Pi.single j z : Fin n → Fv F v ⊗[F] E) ∈ M`.

Introduce `j z hz`. Establish `hrep : (N : Fv F v) • (Pi.single j z : Fin n → Fv F v ⊗[F] E) = ∑ k, Bt.repr z k • ((N : Fv F v) • (Pi.single j (Bt k) : Fin n → Fv F v ⊗[F] E))`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `only [Pi.smul_apply, Finset.sum_apply, Pi.single_eq_same]`. Use `conv_lhs => rw [← Bt.sum_repr z]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Simplify using `[Pi.single_eq_of_ne h]`. Rewrite using `[hrep]`. Conclude with `Submodule.sum_mem _ fun k _ => smul_mem_latLoc v _ (hz k) (hsingle j k)`. Set `U : Set (Fin n → Fv F v ⊗[F] E)` to `{y | ∀ j k, Bt.repr (y j) k ∈ v.adicCompletionIntegers F}`. Establish `hUo : IsOpen U`.

Establish `e : U = ⋂ j, ⋂ k, (fun y : Fin n → Fv F v ⊗[F] E => Bt.coord k (y j)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `y`. Simplify using `[U, Module.Basis.coord_apply]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => (Valued.isOpen_valuationSubring _).preimage ((IsModuleTopology.continuous_of_linearMap (Bt.coord k)).comp (continuous_apply j))`.

Establish `hUM : ∀ y ∈ U, (N : Fv F v) • y ∈ M`. Introduce `y hy`. Rewrite using `[← Finset.univ_sum_single y, Finset.smul_sum]`. Conclude with `Submodule.sum_mem _ fun j _ => hcoord j (y j) (hy j)`. Set `W : Set (Fin n → Fv F v ⊗[F] E)` to `{y | (N : Fv F v)⁻¹ • y ∈ U}`.

Establish `hWo : IsOpen W` using `hUo.preimage (continuous_const_smul _)`. Establish `hW0 : (0 : Fin n → Fv F v ⊗[F] E) ∈ W` using `by show (N : Fv F v)⁻¹ • (0 : Fin n → Fv F v ⊗[F] E) ∈ U`. Rewrite using `[smul_zero]`. Introduce `j k`. Simplify using the standard rewrite rules.

Establish `hWM : W ⊆ M`. Introduce `y hy`. Establish `h` using `hUM _ hy`. Rewrite `h` using `[smul_smul, mul_inv_cancel₀ hNv, one_smul]`. Then use the resulting hypothesis. Conclude with `M.toAddSubgroup.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWM)`.
-/
theorem isOpen_latLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    IsOpen (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E))
  let b := Module.finBasis F E
  let Bt := Algebra.TensorProduct.basis (Fv F v) b
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL
    (fun q : Fin n × Fin (Module.finrank F E) => (Pi.single q.1 (b q.2) : Fin n → E))
  have hNv : (N : Fv F v) ≠ 0 := intCast_ne_zero_Fv v hN0
  have hsingle : ∀ j k, (N : Fv F v) • (Pi.single j (Bt k) : Fin n → Fv F v ⊗[F] E) ∈ M := by
    intro j k
    rw [Algebra.TensorProduct.basis_apply, ← ratV_zsmul_single v N j (b k)]
    exact Submodule.subset_span ⟨_, hNmem (j, k), rfl⟩
  have hcoord : ∀ j (z : Fv F v ⊗[F] E), (∀ k, Bt.repr z k ∈ v.adicCompletionIntegers F) →
      (N : Fv F v) • (Pi.single j z : Fin n → Fv F v ⊗[F] E) ∈ M := by
    intro j z hz
    have hrep : (N : Fv F v) • (Pi.single j z : Fin n → Fv F v ⊗[F] E) =
        ∑ k, Bt.repr z k • ((N : Fv F v) • (Pi.single j (Bt k) : Fin n → Fv F v ⊗[F] E)) := by
      funext i
      by_cases h : i = j
      · subst h
        simp only [Pi.smul_apply, Finset.sum_apply, Pi.single_eq_same]
        conv_lhs => rw [← Bt.sum_repr z]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_comm]
      · simp [Pi.single_eq_of_ne h]
    rw [hrep]
    exact Submodule.sum_mem _ fun k _ => smul_mem_latLoc v _ (hz k) (hsingle j k)
  let U : Set (Fin n → Fv F v ⊗[F] E) := {y | ∀ j k, Bt.repr (y j) k ∈ v.adicCompletionIntegers F}
  have hUo : IsOpen U := by
    have e : U = ⋂ j, ⋂ k, (fun y : Fin n → Fv F v ⊗[F] E => Bt.coord k (y j)) ⁻¹'
        (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext y
      simp [U, Module.Basis.coord_apply]
    rw [e]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k =>
      (Valued.isOpen_valuationSubring _).preimage
        ((IsModuleTopology.continuous_of_linearMap (Bt.coord k)).comp (continuous_apply j))
  have hUM : ∀ y ∈ U, (N : Fv F v) • y ∈ M := by
    intro y hy
    rw [← Finset.univ_sum_single y, Finset.smul_sum]
    exact Submodule.sum_mem _ fun j _ => hcoord j (y j) (hy j)
  let W : Set (Fin n → Fv F v ⊗[F] E) := {y | (N : Fv F v)⁻¹ • y ∈ U}
  have hWo : IsOpen W := hUo.preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Fv F v ⊗[F] E) ∈ W := by
    show (N : Fv F v)⁻¹ • (0 : Fin n → Fv F v ⊗[F] E) ∈ U
    rw [smul_zero]
    intro j k
    simp
  have hWM : W ⊆ M := by
    intro y hy
    have h := hUM _ hy
    rwa [smul_smul, mul_inv_cancel₀ hNv, one_smul] at h
  exact M.toAddSubgroup.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWM)

end Open

section Mat

variable {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}

def matStab (M : Set (Fin n → A)) : Set (Matrix (Fin n) (Fin n) A) := {m | ∀ x ∈ M, m *ᵥ x ∈ M}

/- English proof (translation)
Rewrite using `[isOpen_iff_eventually]`. Introduce `m0 hm0`. Establish `hcont : Continuous fun z : Matrix (Fin n) (Fin n) A × (Fin n → A) => z.1 *ᵥ z.2` using `continuous_fst.matrix_mulVec continuous_snd`. Conclude with `hc.eventually_forall_of_forall_eventually (P := fun m x => m *ᵥ x ∈ M) fun x hx => (hcont.tendsto (m0, x)).eventually (ho.mem_nhds (hm0 x hx))`.
-/
theorem isOpen_matStab {M : Set (Fin n → A)} (hc : IsCompact M) (ho : IsOpen M) :
    IsOpen (matStab M) := by
  rw [isOpen_iff_eventually]
  intro m0 hm0
  have hcont : Continuous fun z : Matrix (Fin n) (Fin n) A × (Fin n → A) => z.1 *ᵥ z.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  exact hc.eventually_forall_of_forall_eventually (P := fun m x => m *ᵥ x ∈ M)
    fun x hx => (hcont.tendsto (m0, x)).eventually (ho.mem_nhds (hm0 x hx))

/- English proof (translation)
Establish `e : matStab M = ⋂ x ∈ M, (fun m : Matrix (Fin n) (Fin n) A => m *ᵥ x) ⁻¹' M`. Use extensionality with `m`. Simplify using `[matStab]`. Rewrite using `[e]`. Conclude with `isClosed_biInter fun x _ => hcl.preimage (continuous_id.matrix_mulVec continuous_const)`.
-/
theorem isClosed_matStab {M : Set (Fin n → A)} (hcl : IsClosed M) : IsClosed (matStab M) := by
  have e : matStab M = ⋂ x ∈ M, (fun m : Matrix (Fin n) (Fin n) A => m *ᵥ x) ⁻¹' M := by
    ext m
    simp [matStab]
  rw [e]
  exact isClosed_biInter fun x _ => hcl.preimage (continuous_id.matrix_mulVec continuous_const)

/- English proof (translation)
Set `Q : Set (Fin n → A)` to `(fun y => c⁻¹ • y) '' M`. Establish `hQ : IsCompact Q` using `hc.image (continuous_const_smul _)`. Establish `hT : IsCompact ((fun m : Matrix (Fin n) (Fin n) A => mᵀ) '' (Set.univ.pi fun _ => Q : Set (Matrix (Fin n) (Fin n) A)))` using `(isCompact_univ_pi fun _ => hQ).image continuous_id.matrix_transpose`. Use `hT.of_isClosed_subset (isClosed_matStab hcl) ?_` and prove the remaining obligations. Introduce `m hm`.

Use `⟨mᵀ, fun j _ => ?_, Matrix.transpose_transpose m⟩` and prove the remaining obligations. Use `⟨c • mᵀ j, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hm _ (hcol j)`. Rewrite `h` using `[Matrix.mulVec_smul, Matrix.mulVec_single_one]`. Conclude with `h`.

Simplify using `only [smul_smul, inv_mul_cancel₀ hc0, one_smul]`.
-/
theorem isCompact_matStab {K : Type} [Field K] [Module K A] [SMulCommClass K A A]
    [ContinuousConstSMul K A] {M : Set (Fin n → A)} (hc : IsCompact M) (hcl : IsClosed M) (c : K)
    (hc0 : c ≠ 0) (hcol : ∀ j, c • (Pi.single j 1 : Fin n → A) ∈ M) : IsCompact (matStab M) := by
  classical
  let Q : Set (Fin n → A) := (fun y => c⁻¹ • y) '' M
  have hQ : IsCompact Q := hc.image (continuous_const_smul _)
  have hT : IsCompact ((fun m : Matrix (Fin n) (Fin n) A => mᵀ) ''
      (Set.univ.pi fun _ => Q : Set (Matrix (Fin n) (Fin n) A))) :=
    (isCompact_univ_pi fun _ => hQ).image continuous_id.matrix_transpose
  refine hT.of_isClosed_subset (isClosed_matStab hcl) ?_
  intro m hm
  refine ⟨mᵀ, fun j _ => ?_, Matrix.transpose_transpose m⟩
  refine ⟨c • mᵀ j, ?_, ?_⟩
  · have h := hm _ (hcol j)
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at h
    exact h
  · simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Mat

section Grp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg' : g⁻¹ ∈ Kloc (E` using `E) v L := (Kloc (E := E) v L).inv_mem hg`. Conclude with `⟨fun x hx => (hg x).1 hx, fun x hx => (hg' x).1 hx⟩`.

Introduce and unpack `⟨h1, h2⟩ show ∀ x, _`. Introduce `x`. Use `⟨h1 x, fun hx => ?_⟩` and prove the remaining obligations. Establish `h` using `h2 _ hx`. Rewrite `h` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem kloc_eq (L : Set (Fin n → E)) :
    (Kloc (E := E) v L : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      {g : GL (Fin n) (Fv F v ⊗[F] E) | ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (latLoc (E := E) v L : Set (Fin n → Fv F v ⊗[F] E)) ∧
        (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (latLoc (E := E) v L : Set (Fin n → Fv F v ⊗[F] E))} := by
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Kloc (E := E) v L := (Kloc (E := E) v L).inv_mem hg
    exact ⟨fun x hx => (hg x).1 hx, fun x hx => (hg' x).1 hx⟩
  · rintro ⟨h1, h2⟩
    show ∀ x, _
    intro x
    refine ⟨h1 x, fun hx => ?_⟩
    have h := h2 _ hx
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h

variable (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
  (hfg : L.FG)
include hL hfg

/- English proof (translation)
Rewrite using `[kloc_eq]`. Establish `hS` using `isOpen_matStab (isCompact_latLoc v L hfg) (isOpen_latLoc v L hL)`. Conclude with `(hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)`.
-/
theorem isOpen_kloc : IsOpen (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  rw [kloc_eq]
  have hS := isOpen_matStab (isCompact_latLoc v L hfg) (isOpen_latLoc v L hL)
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

/- English proof (translation)
Use `set M := latLoc (E := E) v (L : Set (Fin n → E))`. Establish `hMc` using `isCompact_latLoc v L hfg`. Establish `hMo` using `isOpen_latLoc v L hL`. Establish `hMcl : IsClosed (M : Set (Fin n → Fv F v ⊗[F] E))` using `M.toAddSubgroup.isClosed_of_isOpen hMo`. Take `⟨N, hN0, hNmem⟩` from `exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))`.

Establish `hcol : ∀ j, (N : Fv F v) • (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ M`. Introduce `j`. Rewrite using `[Algebra.TensorProduct.one_def, ← ratV_zsmul_single v N j (1 : E)]`. Conclude with `Submodule.subset_span ⟨_, hNmem j, rfl⟩`. Establish `hSc` using `isCompact_matStab hMc hMcl (N : Fv F v) (intCast_ne_zero_Fv v hN0) hcol`.

Rewrite using `[kloc_eq]`. Establish `e : {g : GL (Fin n) (Fv F v ⊗[F] E) | ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈ matStab (M : Set (Fin n → Fv F v ⊗[F] E)) ∧ (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈ matStab (M : Set (Fin n → Fv F v ⊗[F] E))} = Units.embedProduct _ ⁻ …`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, ⟨_, h2, rfl⟩⟩`. Introduce and unpack `⟨h1, y, hy, hyg⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hy' : y = (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))` using `MulOpposite.op_injective hyg`. Rewrite `hy` using `[hy']`. Then use the resulting hypothesis.

Rewrite using `[e]`. Conclude with `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hSc.prod (hSc.image MulOpposite.continuous_op))`.
-/
theorem isCompact_kloc :
    IsCompact (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E))
  have hMc := isCompact_latLoc v L hfg
  have hMo := isOpen_latLoc v L hL
  have hMcl : IsClosed (M : Set (Fin n → Fv F v ⊗[F] E)) := M.toAddSubgroup.isClosed_of_isOpen hMo
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  have hcol : ∀ j, (N : Fv F v) • (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ M := by
    intro j
    rw [Algebra.TensorProduct.one_def, ← ratV_zsmul_single v N j (1 : E)]
    exact Submodule.subset_span ⟨_, hNmem j, rfl⟩
  have hSc := isCompact_matStab hMc hMcl (N : Fv F v) (intCast_ne_zero_Fv v hN0) hcol
  rw [kloc_eq]
  have e : {g : GL (Fin n) (Fv F v ⊗[F] E) | ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (M : Set (Fin n → Fv F v ⊗[F] E)) ∧
        (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (M : Set (Fin n → Fv F v ⊗[F] E))} =
      Units.embedProduct _ ⁻¹' (matStab (M : Set (Fin n → Fv F v ⊗[F] E)) ×ˢ
        (MulOpposite.op '' matStab (M : Set (Fin n → Fv F v ⊗[F] E)))) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyg⟩
      refine ⟨h1, ?_⟩
      have hy' : y = (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
        MulOpposite.op_injective hyg
      rwa [hy'] at hy
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod (hSc.image MulOpposite.continuous_op))

/- English proof (translation)
The claim follows from `have : LocallyCompactSpace (Fv F v) := (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _)) (isClosed_HR (Fv F v) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_kloc v L hL h …`.
-/
theorem isCompact_Kv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsCompact (Kv σ J (L : Set (Fin n → E)) v) :=
  have : LocallyCompactSpace (Fv F v) :=
    (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))
  (isClosed_HR (Fv F v) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_kloc v L hL hfg)

/- English proof (translation)
The claim follows from `(isOpen_kloc v L hL hfg).preimage continuous_subtype_val`.
-/
theorem isOpen_Kv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsOpen (Kv σ J (L : Set (Fin n → E)) v) :=
  (isOpen_kloc v L hL hfg).preimage continuous_subtype_val

end Grp

section Flag

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/- English proof (translation)
Set `W'` to `W.restrictScalars (Fv F v)`. Set `Bq` to `Module.Free.chooseBasis (Fv F v) ((Fin n → Fv F v ⊗[F] E) ⧸ W')`. Set `f : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Module.Free.ChooseBasisIndex (Fv F v) ((Fin n → Fv F v ⊗[F] E) ⧸ W') → Fv F v)` to `Bq.equivFun.toLinearMap ∘ₗ W'.mkQ`. Establish `hf : Continuous f` using `IsModuleTopology.continuous_of_linearMap f`. Establish `e : (W : Set (Fin n → Fv F v ⊗[F] E)) = f ⁻¹' {0}`.

Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, W', Submodule.restrictScalars_mem, SetLike.mem_coe]`. Rewrite using `[e]`. Conclude with `isClosed_singleton.preimage hf`.
-/
theorem isClosed_submodule (W : Submodule (Fv F v ⊗[F] E) (Fin n → Fv F v ⊗[F] E)) :
    IsClosed (W : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  let W' := W.restrictScalars (Fv F v)
  let Bq := Module.Free.chooseBasis (Fv F v) ((Fin n → Fv F v ⊗[F] E) ⧸ W')
  let f : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v]
      (Module.Free.ChooseBasisIndex (Fv F v) ((Fin n → Fv F v ⊗[F] E) ⧸ W') → Fv F v) :=
    Bq.equivFun.toLinearMap ∘ₗ W'.mkQ
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have e : (W : Set (Fin n → Fv F v ⊗[F] E)) = f ⁻¹' {0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, f, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, W', Submodule.restrictScalars_mem, SetLike.mem_coe]
  rw [e]
  exact isClosed_singleton.preimage hf

/- English proof (translation)
Establish `e : (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) = ⋂ b, (fun g : HA (Fv F v) σ J => lin (Fv F v) σ J g (ratV (F` using `F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b)) ⁻¹' (spanR (F := F) (Fv F v) (F0 P) {a | a < b} : Set (Fin n → Fv F v ⊗[F] E)) := by`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `Iff.rfl`. Rewrite using `[e]`.

Use `isClosed_iInter fun b => (isClosed_submodule v _).preimage ?_` and prove the remaining obligations. Establish `hm : Continuous fun g : HA (Fv F v) σ J => ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))` using `Units.continuous_val.comp continuous_subtype_val`. Conclude with `(hm.matrix_mulVec continuous_const).sub continuous_const`.
-/
theorem isClosed_Ssub (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) :
    IsClosed (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) := by
  have e : (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) = ⋂ b, (fun g : HA (Fv F v) σ J =>
      lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b)) ⁻¹'
      (spanR (F := F) (Fv F v) (F0 P) {a | a < b} : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [e]
  refine isClosed_iInter fun b => (isClosed_submodule v _).preimage ?_
  have hm : Continuous fun g : HA (Fv F v) σ J =>
      ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (hm.matrix_mulVec continuous_const).sub continuous_const

end Flag

end MassDataLevelSSteps.LatTop
