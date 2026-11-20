import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsExtendEndomorphismFractions

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

def kmuIncl : Kmu l →+* MaximalUnramifiedExtension l := Subfield.inclusion (Subfield.le_topologicalClosure (Kmu l))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kmuIncl_norm (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := rfl

/- English proof (translation)
The claim follows from `AddMonoidHomClass.isometry_of_norm (kmuIncl l) (fun x => kmuIncl_norm l x)`.
-/
theorem kmuIncl_isometry : Isometry (kmuIncl l) :=
  AddMonoidHomClass.isometry_of_norm (kmuIncl l) (fun x => kmuIncl_norm l x)

/- English proof (translation)
Introduce `x`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `e he`. Take `⟨y, hy, hxy⟩` from `kur_approx l x.2 e he`. Conclude with `⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩`.
-/
theorem kmuIncl_denseRange : DenseRange (kmuIncl l) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨y, hy, hxy⟩ := kur_approx l x.2 e he
  exact ⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩

/- English proof (translation)
Take `⟨s, hs1, hs2⟩` from `kmu_sigma l`. Establish `: CompleteSpace (MaximalUnramifiedExtension l)` using `kur_complete l`. Apply the tactic sequence `have hiso : Isometry ((kmuIncl l).comp s) := AddMonoidHomClass.isometry_of_norm _ (fun x => by`. Rewrite using `[RingHom.comp_apply, kmuIncl_norm, hs1])`. Apply the tactic sequence `let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l := IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s) (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous`.

Apply the tactic sequence `have hdi : IsDenseInducing (kmuIncl l) := (kmuIncl_isometry l).isUniformInducing.isDenseInducing (kmuIncl_denseRange l)`. Apply the tactic sequence `have hσc : Continuous σ := (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous).continuous`. Establish `hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x)` using `fun x => hdi.extend_eq hiso.continuous x`. Establish `hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖` using `rfl`. Use `⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hl, norm_l_Cl]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`. Introduce `x`. Use `(kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x (isClosed_eq hσc.norm continuous_norm) (fun y => ?_)` and prove the remaining obligations. Rewrite using `[hσi, kmuIncl_norm, kmuIncl_norm, hs1]`.

Introduce `x hx`. Establish `hopen : IsOpen (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1)` using `IsUltrametricDist.isOpen_closedBall _ one_ne_zero`. Establish `hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l))` using `(kmuIncl_denseRange l).open_subset_closure_inter hopen (by simpa using hx)`. Establish `hcl : IsClosed {x : MaximalUnramifiedExtension l | ‖σ x - x ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖}` using `isClosed_le (hσc.sub (continuous_pow l)).norm continuous_const`. Use `closure_minimal ?_ hcl hmem` and prove the remaining obligations.

Introduce and unpack `_ ⟨hy1, y, rfl⟩`. Establish `hy : ‖y‖ ≤ 1`. Rewrite `hy1` using `[mem_closedBall_zero_iff, kmuIncl_norm]`. Conclude with `hy1`. Use `hs2 y hy` as an intermediate fact.

Use `show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖`. Rewrite using `[hσi, ← map_pow, ← map_sub, kmuIncl_norm]`. Conclude with `this`. Introduce `x hx`. Conclude with `kur_discrete l x.2 hx`.
-/
theorem kurFrob : ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ := by
  obtain ⟨s, hs1, hs2⟩ := kmu_sigma l
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  have hiso : Isometry ((kmuIncl l).comp s) :=
    AddMonoidHomClass.isometry_of_norm _ (fun x => by
      rw [RingHom.comp_apply, kmuIncl_norm, hs1])
  let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l :=
    IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s)
      (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous
  have hdi : IsDenseInducing (kmuIncl l) :=
    (kmuIncl_isometry l).isUniformInducing.isDenseInducing (kmuIncl_denseRange l)
  have hσc : Continuous σ :=
    (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing
      (kmuIncl_denseRange l) hiso.uniformContinuous).continuous
  have hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x) := fun x =>
    hdi.extend_eq hiso.continuous x
  have hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖ := rfl
  refine ⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩
  · rw [hl, norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  · intro x
    refine (kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x
      (isClosed_eq hσc.norm continuous_norm) (fun y => ?_)
    rw [hσi, kmuIncl_norm, kmuIncl_norm, hs1]
  · intro x hx
    have hopen : IsOpen (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l)) :=
      (kmuIncl_denseRange l).open_subset_closure_inter hopen (by simpa using hx)
    have hcl : IsClosed {x : MaximalUnramifiedExtension l | ‖σ x - x ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖} :=
      isClosed_le (hσc.sub (continuous_pow l)).norm continuous_const
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hy1, y, rfl⟩
    have hy : ‖y‖ ≤ 1 := by
      rw [mem_closedBall_zero_iff, kmuIncl_norm] at hy1
      exact hy1
    have := hs2 y hy
    show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖
    rw [hσi, ← map_pow, ← map_sub, kmuIncl_norm]
    exact this
  · intro x hx
    exact kur_discrete l x.2 hx

end ReciprocityTheory.ChartRestriction.L1
