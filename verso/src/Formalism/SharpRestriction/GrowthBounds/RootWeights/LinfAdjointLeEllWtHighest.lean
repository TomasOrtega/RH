import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringSpanHighestComponentIntegral
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Use `csSup_le' ?_` and prove the remaining obligations. Introduce and unpack `k ⟨ka, hk, -, a, rfl⟩`. Take `⟨f, hf, hf0⟩` from `(Submodule.ne_bot_iff _).1 hk`. Establish `hfw` using `hf.1`. Choose the witnesses or unpack the hypotheses as in `⟨nu, x, hx, hfx⟩ : ∃ nu x, x ∈ weightSp E nu ∧ f x ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hf0` to reduce the goal to its premises. Establish `hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f`. Rewrite using `[← hI.1.2.2]`.

Conclude with `iSup_le fun nu x hx => hcon nu x hx`. Conclude with `LinearMap.ext fun x => hk Submodule.mem_top`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hfx`. Establish `hfxw : f x ∈ weightSp E (nu + ka)`. Rewrite using `[mem_weightSpace_iff_diag_scalar]`.

Introduce `c`. Establish `h1` using `congrArg (fun T : Module.End (KK O) V => T x) (mem_weightSpace_iff_diag_scalar.1 hfw c)`. Simplify using `only [adjointEndAction_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h1`. Rewrite `h1` using `[mem_weightSpace_iff_diag_scalar.1 hx c, map_smul]`. Rewrite using `[sub_eq_iff_eq_add.1 h1, ← add_smul]`.

Use `congr 1`. Simplify using `only [Pi.add_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `weight_entries_between_extreme_highest hI hfxw hfx a`.

Establish `h2` using `weight_entries_between_extreme_highest hI hx hx0 a`. Simplify using `only [Pi.add_apply] at h1`. Unfold `ellWt`. Use linear arithmetic over natural numbers and integers.
-/
theorem linf_adjoint_le_ellWt_highest [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) : linf (adjointEndAction E) ⊤ ≤ ellWt lam := by
  refine csSup_le' ?_
  rintro k ⟨ka, hk, -, a, rfl⟩
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hk
  have hfw := hf.1
  obtain ⟨nu, x, hx, hfx⟩ : ∃ nu x, x ∈ weightSp E nu ∧ f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← hI.1.2.2]
      exact iSup_le fun nu x hx => hcon nu x hx
    exact LinearMap.ext fun x => hk Submodule.mem_top
  have hx0 : x ≠ 0 := by rintro rfl; simp at hfx
  have hfxw : f x ∈ weightSp E (nu + ka) := by
    rw [mem_weightSpace_iff_diag_scalar]
    intro c
    have h1 := congrArg (fun T : Module.End (KK O) V => T x) (mem_weightSpace_iff_diag_scalar.1 hfw c)
    simp only [adjointEndAction_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h1
    rw [mem_weightSpace_iff_diag_scalar.1 hx c, map_smul] at h1
    rw [sub_eq_iff_eq_add.1 h1, ← add_smul]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  have h1 := weight_entries_between_extreme_highest hI hfxw hfx a
  have h2 := weight_entries_between_extreme_highest hI hx hx0 a
  simp only [Pi.add_apply] at h1
  unfold ellWt
  omega

end hw

/- English proof (translation)
Introduce `p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI x hx`. Use `dvr_fraction_field_char_zero_prime S hR.prime` as an intermediate fact. Use `irreducible_highest_weight_findim hI` as an intermediate fact. Establish `hCR` using `h2 (KK O) V n E hI.1`. Take `⟨xi, x1, x2, x3⟩` from `exists_highest_coordinate_functional hI`.

Establish `hKv` using `hK p n' O S hR n lam V E v hI`. Establish `hlat : UZLattice (O` using `O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) := ⟨nabla_to_delta_maps_stable hI.1 lam v, nabla_to_delta_maps_fg hI hCR x1 x2 x3 hKv⟩`. Establish `hMQ` using `nabla_to_delta_maps_span_top (O := O) hI (nabla_finitely_generated hI hCR x1 x2 x3)`. Establish `key` using `h p n' O S hR n (Module.End (KK O) V) (adjointEndAction E) (adjoint_end_isGLRep hI.1) _ hlat hMQ (traceInvariantProjection O V) (trace_projection_isInvProj hI) (xi.smulRight v) (coordinate_rank_one_mem_maps x1 x2 x3)`. Rewrite `key` using `[hMQ]`.

Establish `hd : (Module.finrank (KK O) V : KK O) ≠ 0`. Establish `: Nontrivial V` using `⟨⟨v, 0, hI.2.2.1.1⟩⟩`. Conclude with `(Module.finrank_pos (R := KK O) (M := V)).ne'` after adjusting the coercions. Establish `hInv : traceInvariantProjection O V (xi.smulRight v) = ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)`. Rewrite using `[traceInvariantProjection, LinearMap.smulRight_apply, LinearMap.trace_smulRight, x1, one_smul]`.

Rewrite `key` using `[hInv]`. Use `set D' := N0 n * deF p n (linf (adjointEndAction E) ⊤) with hD'`. Use `set D0 := N0 n * deF p n (ellWt lam) with hD0`. Establish `hle : D' ≤ D0`. Use `Nat.mul_le_mul_left _ ?_` and prove the remaining obligations.

Unfold `deF`. Conclude with `Nat.log_mono_right (by have := linf_adjoint_le_ellWt_highest hI; omega)`. Establish `h3 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) • ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) ∈ nablaToDeltaMaps (O` using `O) E lam v := Submodule.smul_mem _ _ (Submodule.smul_mem _ _ key)`. Establish `h4 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) • ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) = (p : O) ^ D0 • (1 : Module.End (KK O) V)`. Rewrite using `[smul_smul ((p : O) ^ (D0 - D')), ← pow_add, Nat.sub_add_cancel hle, smul_comm, ← algebraMap_smul (KK O) ((Module.finrank (KK O) V : ℕ) : O), smul_smul, map_natCast, mul_inv_cancel₀ hd, one_smul]`.

Rewrite `h3` using `[h4]`. Use `h3 x hx` as an intermediate fact. Simplify using `using this`.
-/
theorem restA_of_linf_integrality (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) (hK : HighestWeightVectorIntegrality) : LatticeNablaDeltaBound := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI x hx
  have := dvr_fraction_field_char_zero_prime S hR.prime
  have := irreducible_highest_weight_findim hI
  have hCR := h2 (KK O) V n E hI.1
  obtain ⟨xi, x1, x2, x3⟩ := exists_highest_coordinate_functional hI
  have hKv := hK p n' O S hR n lam V E v hI
  have hlat : UZLattice (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) :=
    ⟨nabla_to_delta_maps_stable hI.1 lam v, nabla_to_delta_maps_fg hI hCR x1 x2 x3 hKv⟩
  have hMQ := nabla_to_delta_maps_span_top (O := O) hI (nabla_finitely_generated hI hCR x1 x2 x3)
  have key := h p n' O S hR n (Module.End (KK O) V) (adjointEndAction E) (adjoint_end_isGLRep hI.1) _ hlat hMQ
    (traceInvariantProjection O V) (trace_projection_isInvProj hI) (xi.smulRight v) (coordinate_rank_one_mem_maps x1 x2 x3)
  rw [hMQ] at key
  have hd : (Module.finrank (KK O) V : KK O) ≠ 0 := by
    have : Nontrivial V := ⟨⟨v, 0, hI.2.2.1.1⟩⟩
    exact_mod_cast (Module.finrank_pos (R := KK O) (M := V)).ne'
  have hInv : traceInvariantProjection O V (xi.smulRight v) = ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V) := by
    rw [traceInvariantProjection, LinearMap.smulRight_apply, LinearMap.trace_smulRight, x1, one_smul]
  rw [hInv] at key
  set D' := N0 n * deF p n (linf (adjointEndAction E) ⊤) with hD'
  set D0 := N0 n * deF p n (ellWt lam) with hD0
  have hle : D' ≤ D0 := by
    refine Nat.mul_le_mul_left _ ?_
    unfold deF
    exact Nat.log_mono_right (by have := linf_adjoint_le_ellWt_highest hI; omega)
  have h3 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) •
      ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) ∈ nablaToDeltaMaps (O := O) E lam v :=
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ key)
  have h4 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) •
      ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) =
      (p : O) ^ D0 • (1 : Module.End (KK O) V) := by
    rw [smul_smul ((p : O) ^ (D0 - D')), ← pow_add, Nat.sub_add_cancel hle, smul_comm,
      ← algebraMap_smul (KK O) ((Module.finrank (KK O) V : ℕ) : O), smul_smul, map_natCast, mul_inv_cancel₀ hd,
      one_smul]
  rw [h4] at h3
  have := h3 x hx
  simpa using this

/- English proof (translation)
The claim follows from `highest_weight_lattice_of_first_part D (restA_of_linf_integrality D h2 h highest_vector_integrality)`.
-/
theorem integral_form_of_linf_lemma (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) : NablaDeltaComparisonField D :=
  highest_weight_lattice_of_first_part D (restA_of_linf_integrality D h2 h highest_vector_integrality)

end Formalism.MainNotions.G.GLWeightTheory
