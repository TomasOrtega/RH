import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DiscreteSeriesSU.GapInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Establish `hx : rreg ε g x ∈ Hlam ε Ψ T.w` using `hS n ε lam T Ψ hP g hg x x.2`. Use `show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _`. Conclude with `congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))`.
-/
theorem sigLam_coe' (hS : HlamStable) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hP : IsPsiFor ε lam T Ψ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x : Hlam ε Ψ T.w) :
    ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x := by
  have hx : rreg ε g x ∈ Hlam ε Ψ T.w := hS n ε lam T Ψ hP g hg x x.2
  show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))

/- English proof (translation)
Take `⟨σ, hσk, -, hKT⟩` from `HW.KType.exists_rep T`. Establish `hint' : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (σ g x) = sigLam ε Ψ T.w g (φ x)`. Introduce `g hg x`. Establish `e : g = toMK (pdA_kg g hg)` using `(pdA_toMK_kg g hg).symm`. Rewrite using `[e, hσk, hint]`.

Conclude with `(isKTypeOf_map_iff φ hφ hint' (Formalism.QuantumDeterminants.lowK ε lam) ⊤).1 hKT`.
-/
theorem isKTypeOf_range {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (φ : T.V →ₗ[ℂ] Hlam ε Ψ T.w) (hφ : Function.Injective φ)
    (hint : ∀ (k : KG ε) (v : T.V), φ (T.op k v) = sigLam ε Ψ T.w (toMK k) (φ v)) :
    Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) (Formalism.QuantumDeterminants.lowK ε lam) ((⊤ : Submodule ℂ T.V).map φ) := by
  obtain ⟨σ, hσk, -, hKT⟩ := HW.KType.exists_rep T
  have hint' : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (σ g x) = sigLam ε Ψ T.w g (φ x) := by
    intro g hg x
    have e : g = toMK (pdA_kg g hg) := (pdA_toMK_kg g hg).symm
    rw [e, hσk, hint]
  exact (isKTypeOf_map_iff φ hφ hint' (Formalism.QuantumDeterminants.lowK ε lam) ⊤).1 hKT

/- English proof (translation)
Introduce `n ε lam T Ψ hl hP hDS B hB hr horth`. Establish `hw : T.w ≠ 0` using `fun h => by`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.

Break down `T.irred (LinearMap.ker B) (fun k v hv => by` into its components or cases. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Use `show B (T.op k v) = 0`. Rewrite using `[hB, hv, map_zero]) with h0 | h0`. Use `swap`.

Conclude with `LinearMap.ker_eq_top.1 h0`. Establish `hBinj : Function.Injective B` using `LinearMap.ker_eq_bot.1 h0`. Set `j' : T.V →ₗ[ℂ] Hlam ε Ψ T.w` to `{ toFun := fun v => ⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩ map_add' := fun v v' => Subtype.ext (datumEmbedding_add hP T.w v v') map_smul' := fun c v => Subtype.ext (datumEmbedding_smul hP T.w c v) }`. Set `B' : T.V →ₗ[ℂ] Hlam ε Ψ T.w` to `B.codRestrict (Hlam ε Ψ T.w) hr`. Establish `hj'inj : Function.Injective j'` using `fun a b h => uniformisationL2_injective hP hw (congrArg Subtype.val h)`.

Establish `hB'inj : Function.Injective B'` using `fun a b h => hBinj (congrArg Subtype.val h)`. Establish `hjint : ∀ (k : KG ε) (v : T.V), j' (T.op k v) = sigLam ε Ψ T.w (toMK k) (j' v)`. Introduce `k v`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[sigLam_coe' hS hP (show toMK k ∈ UJset ε from k.1.2)]`.

Conclude with `(rightRegular_datumEmbedding hP T.w v k).symm`. Establish `hBint : ∀ (k : KG ε) (v : T.V), B' (T.op k v) = sigLam ε Ψ T.w (toMK k) (B' v)`. Introduce `k v`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[sigLam_coe' hS hP (show toMK k ∈ UJset ε from k.1.2)]`.

Conclude with `hB k v`. Establish `hEq` using `PositivityTheory.DiscreteSeriesGap.GapInv.lowKMultOne_dec n ε lam (Hlam ε Ψ T.w) (sigLam ε Ψ T.w) ((mir_isHCParam_iff lam).2 hl) hDS _ _ (isKTypeOf_range B' hB'inj hBint) (isKTypeOf_range j' hj'inj hjint)`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hmem : B' v ∈ (⊤ : Submodule ℂ T.V).map j'`. Rewrite using `[← hEq]`.

Conclude with `Submodule.mem_map_of_mem Submodule.mem_top`. Take `⟨u, -, hu⟩` from `hmem`. Establish `hu' : uniformisationL2 ε Ψ T.w u = B v` using `congrArg Subtype.val hu`. Establish `h2` using `horth u v`. Rewrite `h2` using `[hu']`.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `inner_self_eq_zero.1 h2`.
-/
theorem kmapZero_of (hS : HlamStable) : KmapZero := by
  intro n ε lam T Ψ hl hP hDS B hB hr horth
  have hw : T.w ≠ 0 := fun h => by
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  rcases T.irred (LinearMap.ker B) (fun k v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      show B (T.op k v) = 0
      rw [hB, hv, map_zero]) with h0 | h0
  swap
  · exact LinearMap.ker_eq_top.1 h0
  have hBinj : Function.Injective B := LinearMap.ker_eq_bot.1 h0
  let j' : T.V →ₗ[ℂ] Hlam ε Ψ T.w :=
    { toFun := fun v => ⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩
      map_add' := fun v v' => Subtype.ext (datumEmbedding_add hP T.w v v')
      map_smul' := fun c v => Subtype.ext (datumEmbedding_smul hP T.w c v) }
  let B' : T.V →ₗ[ℂ] Hlam ε Ψ T.w := B.codRestrict (Hlam ε Ψ T.w) hr
  have hj'inj : Function.Injective j' := fun a b h =>
    uniformisationL2_injective hP hw (congrArg Subtype.val h)
  have hB'inj : Function.Injective B' := fun a b h => hBinj (congrArg Subtype.val h)
  have hjint : ∀ (k : KG ε) (v : T.V), j' (T.op k v) = sigLam ε Ψ T.w (toMK k) (j' v) := by
    intro k v
    refine Subtype.ext ?_
    rw [sigLam_coe' hS hP (show toMK k ∈ UJset ε from k.1.2)]
    exact (rightRegular_datumEmbedding hP T.w v k).symm
  have hBint : ∀ (k : KG ε) (v : T.V), B' (T.op k v) = sigLam ε Ψ T.w (toMK k) (B' v) := by
    intro k v
    refine Subtype.ext ?_
    rw [sigLam_coe' hS hP (show toMK k ∈ UJset ε from k.1.2)]
    exact hB k v
  have hEq := PositivityTheory.DiscreteSeriesGap.GapInv.lowKMultOne_dec n ε lam (Hlam ε Ψ T.w) (sigLam ε Ψ T.w)
    ((mir_isHCParam_iff lam).2 hl) hDS _ _ (isKTypeOf_range B' hB'inj hBint) (isKTypeOf_range j' hj'inj hjint)
  refine LinearMap.ext fun v => ?_
  have hmem : B' v ∈ (⊤ : Submodule ℂ T.V).map j' := by
    rw [← hEq]
    exact Submodule.mem_map_of_mem Submodule.mem_top
  obtain ⟨u, -, hu⟩ := hmem
  have hu' : uniformisationL2 ε Ψ T.w u = B v := congrArg Subtype.val hu
  have h2 := horth u v
  rw [hu'] at h2
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.1 h2

end PositivityTheory.RgFd
