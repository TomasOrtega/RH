import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct

universe u v w

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

/- English proof (translation)
Establish `h` using `HermitianBundle.quot_norm_eq_iInf M F hF σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e)`. Use `(le_of_eq h).trans ?_` and prove the remaining obligations. Conclude with `ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] e, by simp⟩ : {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e})`.
-/
theorem normAt_mkQ_le (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    (hF : M.Saturated F) (σ : K →+* ℂ) (e : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ e) ≤ M.normAt σ e := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e)
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] e, by simp⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e})

/- English proof (translation)
Set `v : ι → M.carrier ⧸ F` to `fun i ↦ F.mkQ (x i)`. Take `⟨s, hs, hmax⟩` from `exists_maximal_linearIndepOn (𝓞 K) v`. Use `set N := span (𝓞 K) (v '' s)`. Establish `hS : Module.IsTorsion (𝓞 K) (M.carrier ⧸ span (𝓞 K) (Set.range x))`. Rewrite using `[← Module.finrank_eq_zero_iff_isTorsion]`.

Use `Submodule.finrank_quotient_add_finrank (span (𝓞 K) (Set.range x))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hv : span (𝓞 K) (Set.range x) ≤ (torsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N)).comap (N.mkQ ∘ₗ F.mkQ)`. Rewrite using `[span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Distinguish the cases in `hi : i ∈ s`. Establish `: N.mkQ (v i) = 0`. Rewrite using `[mkQ_apply, Quotient.mk_eq_zero]`. Conclude with `subset_span ⟨i, hi, rfl⟩`. Simplify using `only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]`.

Conclude with `this ▸ zero_mem _`. Take `⟨a, ha, hav⟩` from `hmax i hi`. Simplify using `only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]`. Rewrite using `[mem_torsion_iff]`. Use `⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero]`. Conclude with `hav`. Establish `hT : Module.IsTorsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N)`. Introduce `q`. Take `⟨q, rfl⟩` from `N.mkQ_surjective q`.

Take `⟨m, rfl⟩` from `F.mkQ_surjective q`. Take `⟨a, ha⟩` from `hS (x := (span (𝓞 K) (Set.range x)).mkQ m)`. Rewrite `ha` using `[Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero]`. Take `⟨b, hb⟩` from `(mem_torsion_iff _).mp (hv ha)`. Use `⟨b * a, ?_⟩` and prove the remaining obligations.

Rewrite `hb`, the goal using `[Submonoid.smul_def]`. Simplify `hb` using `[mul_smul, map_smul]`. Establish `hrank : Module.rank (𝓞 K) (M.carrier ⧸ F) ≤ #(v '' s)`. Establish `h` using `rank_quotient_add_rank_of_isDomain N`. Rewrite `h` using `[Module.rank_eq_zero_iff_isTorsion.mpr hT, zero_add]`.

Conclude with `h ▸ rank_span_le _`. Establish `hle : lift.{w} #(Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F))) ≤ lift.{0} #s`. Establish `h1` using `(lift_le.{w}).mpr hrank`. Establish `h2` using `mk_image_le_lift (f := v) (s := s)`. Rewrite `h1` using `[← Module.finrank_eq_rank, lift_natCast]`.

Rewrite using `[mk_fin, lift_natCast, lift_uzero]`. Conclude with `(lift_le.{v}).mp (by simpa using h1.trans h2)`. Take `⟨e⟩` from `lift_mk_le'.mp hle`. Conclude with `⟨fun j ↦ (e j : ι), hs.comp e e.injective⟩`.
-/
theorem exists_linearIndependent_mkQ (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    {ι : Type w} (x : ι → M.carrier)
    (hx : Module.finrank (𝓞 K) (span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier) :
    ∃ s : Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F)) → ι,
      LinearIndependent (𝓞 K) (fun j ↦ F.mkQ (x (s j))) := by
  classical
  let v : ι → M.carrier ⧸ F := fun i ↦ F.mkQ (x i)
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn (𝓞 K) v
  set N := span (𝓞 K) (v '' s)
  have hS : Module.IsTorsion (𝓞 K) (M.carrier ⧸ span (𝓞 K) (Set.range x)) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have := Submodule.finrank_quotient_add_finrank (span (𝓞 K) (Set.range x))
    omega
  have hv : span (𝓞 K) (Set.range x) ≤
      (torsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N)).comap (N.mkQ ∘ₗ F.mkQ) := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · have : N.mkQ (v i) = 0 := by
        rw [mkQ_apply, Quotient.mk_eq_zero]
        exact subset_span ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      exact this ▸ zero_mem _
    · obtain ⟨a, ha, hav⟩ := hmax i hi
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      rw [mem_torsion_iff]
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero]
      exact hav
  have hT : Module.IsTorsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N) := by
    intro q
    obtain ⟨q, rfl⟩ := N.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha⟩ := hS (x := (span (𝓞 K) (Set.range x)).mkQ m)
    rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero] at ha
    obtain ⟨b, hb⟩ := (mem_torsion_iff _).mp (hv ha)
    refine ⟨b * a, ?_⟩
    rw [Submonoid.smul_def] at hb ⊢
    simpa [mul_smul, map_smul] using hb
  have hrank : Module.rank (𝓞 K) (M.carrier ⧸ F) ≤ #(v '' s) := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [Module.rank_eq_zero_iff_isTorsion.mpr hT, zero_add] at h
    exact h ▸ rank_span_le _
  have hle : lift.{w} #(Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F))) ≤ lift.{0} #s := by
    have h1 := (lift_le.{w}).mpr hrank
    have h2 := mk_image_le_lift (f := v) (s := s)
    rw [← Module.finrank_eq_rank, lift_natCast] at h1
    rw [mk_fin, lift_natCast, lift_uzero]
    exact (lift_le.{v}).mp (by simpa using h1.trans h2)
  obtain ⟨e⟩ := lift_mk_le'.mp hle
  exact ⟨fun j ↦ (e j : ι), hs.comp e e.injective⟩

/- English proof (translation)
Introduce `K _ _ M F hF ι x hx`. Take `⟨s, hs⟩` from `exists_linearIndependent_mkQ M F x hx`. Use `⟨s, hs, le_trans ?_ (h1 K (M.quot F hF) (fun j ↦ F.mkQ (x (s j))) hs (by rw [Fintype.card_fin]; rfl))⟩` and prove the remaining obligations. Use `gcongr with j _ σ _`. Establish `hne : HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) ≠ 0`.

Use `(linearIndependent_fibreVec (M.quot F hF).metric σ hs).ne_zero j` as an intermediate fact. Conclude with `norm_ne_zero_iff.mpr this`. Establish `hpos : 0 < HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j)))` using `(norm_nonneg _).lt_of_ne' hne`. Apply the tactic sequence `all_goals first`. Consider the case `exact hpos`.

Consider the case `exact normAt_mkQ_le M F hF σ _`.
-/
theorem HadamardMeanQuotient.proof (h1 : HadamardMean.Statement.{u, v, 0}) :
    HadamardMeanQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x hx
  obtain ⟨s, hs⟩ := exists_linearIndependent_mkQ M F x hx
  refine ⟨s, hs, le_trans ?_ (h1 K (M.quot F hF) (fun j ↦ F.mkQ (x (s j))) hs
    (by rw [Fintype.card_fin]; rfl))⟩
  gcongr with j _ σ _
  have hne : HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) ≠ 0 := by
    have := (linearIndependent_fibreVec (M.quot F hF).metric σ hs).ne_zero j
    exact norm_ne_zero_iff.mpr this
  have hpos : 0 < HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) :=
    (norm_nonneg _).lt_of_ne' hne
  all_goals first
    | exact hpos
    | exact normAt_mkQ_le M F hF σ _

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
