import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccATensWordMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccBLowKShiftF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ImageLeClosGen
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Proj

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

/- English proof (translation)
Introduce `g hg v`. Establish `h` using `Lap.QuotA.proj_comm (rreg_isURepOn ε) (Hlam ε Ψ v₀) (rreg_mem_Hlam hgap hP hv₀) g hg v`. Rewrite `h` using `[Submodule.starProjection_orthogonal']`. Simplify using `only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub] at h`. Conclude with `sub_right_injective h`.
-/
theorem projection_commutes_right_regular (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, ∀ v : L2 ε,
      (Hlam ε Ψ v₀).starProjection (rreg ε g v) = rreg ε g ((Hlam ε Ψ v₀).starProjection v) := by
  intro g hg v
  have h := Lap.QuotA.proj_comm (rreg_isURepOn ε) (Hlam ε Ψ v₀) (rreg_mem_Hlam hgap hP hv₀) g hg v
  rw [Submodule.starProjection_orthogonal'] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub] at h
  exact sub_right_injective h

/- English proof (translation)
The claim follows from `Lap.QuotA.smooth_of_comm _ (fun g hg v => projection_commutes_right_regular hgap hP hv₀ g hg v) hx`.
-/
theorem projection_preserves_smooth (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : L2 ε)
    (hx : x ∈ smD ε (rreg ε)) : (Hlam ε Ψ v₀).starProjection x ∈ smD ε (rreg ε) :=
  Lap.QuotA.smooth_of_comm _ (fun g hg v => projection_commutes_right_regular hgap hP hv₀ g hg v) hx

/- English proof (translation)
The claim follows from `Lap.QuotA.smE_comm (rreg_isURepOn ε) _ (fun g hg v => projection_commutes_right_regular hgap hP hv₀ g hg v) x hx a b`.
-/
theorem projection_commutes_derived_action (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : smD ε (rreg ε))
    (hx : (Hlam ε Ψ v₀).starProjection (x : L2 ε) ∈ smD ε (rreg ε)) (a b : Fin n) :
    ((smE ε (rreg ε) a b ⟨(Hlam ε Ψ v₀).starProjection (x : L2 ε), hx⟩ : smD ε (rreg ε)) : L2 ε) =
      (Hlam ε Ψ v₀).starProjection ((smE ε (rreg ε) a b x : smD ε (rreg ε)) : L2 ε) :=
  Lap.QuotA.smE_comm (rreg_isURepOn ε) _ (fun g hg v => projection_commutes_right_regular hgap hP hv₀ g hg v) x hx a b

end Proj

section Layer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact hVK`. Consider the case `succ j ih`. Introduce `k hk`.

Set `Tk : Submodule ℂ D` to `{ carrier := {x | ∃ y ∈ layer ε E V (j + 1), (y : H) = σ k x} add_mem' := by`. Introduce and unpack `x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩`. Conclude with `⟨y + y', Submodule.add_mem _ hy hy', by simp [e, e']⟩`. Use the proof step `zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c x ⟨y, hy, e⟩`. Conclude with `⟨c • y, Submodule.smul_mem _ c hy, by simp [e]⟩ }`. It suffices to establish `hle : layer ε E V (j + 1) ≤ Tk from fun x hx => hle hx`. Use `show layer ε E V j ⊔ _ ≤ Tk`. Use `sup_le (fun x hx => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)` and prove the remaining obligations.

Take `⟨y, hy, e⟩` from `ih k hk x hx`. Conclude with `⟨y, layer_le_succ j hy, e⟩`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `x hx`. Take `⟨y, hy, e⟩` from `ih k hk x hx`.

Establish `h` using `derived_adK hσ hD hk (Matrix.single a b (1 : ℂ)) x`. Rewrite `h` using `[tset_actM_single]`. Establish `hyx : (⟨σ k (x : H), hD.kStable k hk x x.2⟩ : D) = y` using `Subtype.ext e.symm`. Rewrite `h` using `[hyx]`. Use `⟨(actM E (k * Matrix.single a b 1 * kᴴ)) y, ?_, h.symm⟩` and prove the remaining obligations.

Simplify using `only [actM, LinearMap.sum_apply, LinearMap.smul_apply]`. Conclude with `Submodule.sum_mem _ fun a' _ => Submodule.sum_mem _ fun b' _ => Submodule.smul_mem _ _ (apply_mem_layer_succ hD.glRep hVs a' b' hy)`.
-/
theorem layer_k_stable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVs : IsKStableSub ε E V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    ∀ j, ∀ k ∈ Kset ε, ∀ x ∈ layer ε E V j, ∃ y ∈ layer ε E V j, (y : H) = σ k x := by
  intro j
  induction j with
  | zero => exact hVK
  | succ j ih =>
    intro k hk
    let Tk : Submodule ℂ D :=
      { carrier := {x | ∃ y ∈ layer ε E V (j + 1), (y : H) = σ k x}
        add_mem' := by
          rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
          exact ⟨y + y', Submodule.add_mem _ hy hy', by simp [e, e']⟩
        zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
        smul_mem' := by
          rintro c x ⟨y, hy, e⟩
          exact ⟨c • y, Submodule.smul_mem _ c hy, by simp [e]⟩ }
    suffices hle : layer ε E V (j + 1) ≤ Tk from fun x hx => hle hx
    show layer ε E V j ⊔ _ ≤ Tk
    refine sup_le (fun x hx => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
    · obtain ⟨y, hy, e⟩ := ih k hk x hx
      exact ⟨y, layer_le_succ j hy, e⟩
    · rw [Submodule.map_le_iff_le_comap]
      intro x hx
      obtain ⟨y, hy, e⟩ := ih k hk x hx
      have h := derived_adK hσ hD hk (Matrix.single a b (1 : ℂ)) x
      rw [tset_actM_single] at h
      have hyx : (⟨σ k (x : H), hD.kStable k hk x x.2⟩ : D) = y := Subtype.ext e.symm
      rw [hyx] at h
      refine ⟨(actM E (k * Matrix.single a b 1 * kᴴ)) y, ?_, h.symm⟩
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun a' _ => Submodule.sum_mem _ fun b' _ =>
        Submodule.smul_mem _ _ (apply_mem_layer_succ hD.glRep hVs a' b' hy)

/- English proof (translation)
Rewrite `hf` using `[tset_mem]`. Establish `hdir : Directed (· ≤ ·) (fun k => layer ε E V k)` using `fun i j => ⟨max i j, layer_mono (le_max_left i j), layer_mono (le_max_right i j)⟩`. Establish `hc : ∀ c, ∃ j, f c ∈ layer ε E V j` using `fun c => by`. Use `hf c` as an intermediate fact. Rewrite `this` using `[genSub_eq_iSup_layer hE hVs]`.

Conclude with `(Submodule.mem_iSup_of_directed _ hdir).mp this`. Use `choose j hj using hc`. Conclude with `⟨Finset.univ.sup j, fun c => layer_mono (Finset.le_sup (Finset.mem_univ c)) (hj c)⟩`.
-/
theorem tensor_generated_mem_layer (hE : IsGlRep E) {V : Submodule ℂ D} (hVs : IsKStableSub ε E V)
    {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) : ∃ j, ∀ c, f c ∈ layer ε E V j := by
  rw [tset_mem] at hf
  have hdir : Directed (· ≤ ·) (fun k => layer ε E V k) :=
    fun i j => ⟨max i j, layer_mono (le_max_left i j), layer_mono (le_max_right i j)⟩
  have hc : ∀ c, ∃ j, f c ∈ layer ε E V j := fun c => by
    have := hf c
    rw [genSub_eq_iSup_layer hE hVs] at this
    exact (Submodule.mem_iSup_of_directed _ hdir).mp this
  choose j hj using hc
  exact ⟨Finset.univ.sup j, fun c => layer_mono (Finset.le_sup (Finset.mem_univ c)) (hj c)⟩

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [occCoef, tensGrp, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, inner_add_right]`.
-/
theorem occurrence_coef_add (dual : Bool) (η f f' : Fin n → H) :
    occCoef dual σ η (f + f') = occCoef dual σ η f + occCoef dual σ η f' := by
  funext g
  simp only [occCoef, tensGrp, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, inner_add_right]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [occCoef, tensGrp, Pi.smul_apply, map_smul, smul_comm _ c, ← Finset.smul_sum, inner_smul_right, Finset.mul_sum, smul_eq_mul]`.
-/
theorem occurrence_coef_smul (dual : Bool) (η f : Fin n → H) (c : ℂ) :
    occCoef dual σ η (c • f) = c • occCoef dual σ η f := by
  funext g
  simp only [occCoef, tensGrp, Pi.smul_apply, map_smul, smul_comm _ c, ← Finset.smul_sum, inner_smul_right,
    Finset.mul_sum, smul_eq_mul]

end Layer

end ReciprocityTheory.ChartRestriction.DS.G2
