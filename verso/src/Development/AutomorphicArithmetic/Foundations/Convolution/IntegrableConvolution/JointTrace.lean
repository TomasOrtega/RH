import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CutIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AlgTrace

noncomputable section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section Hilbert
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `h : M.topologicalClosure = M` using `hM.submodule_topologicalClosure_eq`. Establish `h2 : prj M x ∈ M.topologicalClosure` using `Submodule.starProjection_apply_mem M.topologicalClosure x`. Rewrite `h2` using `[h]`. Then use the resulting hypothesis.
-/
private lemma prj_mem {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) : prj M x ∈ M := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  have h2 : prj M x ∈ M.topologicalClosure := Submodule.starProjection_apply_mem M.topologicalClosure x
  rwa [h] at h2

/- English proof (translation)
Conclude with `(Submodule.mem_orthogonal' _ _).1 (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) w (M.le_topologicalClosure hw)`.
-/
private lemma prj_orth {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) {w : H} (hw : w ∈ M) :
    ⟪x - prj M x, w⟫_ℂ = 0 := by
  exact (Submodule.mem_orthogonal' _ _).1
    (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) w
    (M.le_topologicalClosure hw)

/- English proof (translation)
Establish `h : M.topologicalClosure = M` using `hM.submodule_topologicalClosure_eq`. Conclude with `Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure) (M.le_topologicalClosure hv) fun w hw => ho w (by rwa [h] at hw)`.
-/
private lemma prj_eq {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {u v : H} (hv : v ∈ M)
    (ho : ∀ w ∈ M, ⟪u - v, w⟫_ℂ = 0) : prj M u = v := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure)
    (M.le_topologicalClosure hv) fun w hw => ho w (by rwa [h] at hw)

/- English proof (translation)
The claim follows from `prj_eq hM hv fun w _ => by simp`.
-/
private lemma prj_of_mem {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {v : H} (hv : v ∈ M) :
    prj M v = v :=
  prj_eq hM hv fun w _ => by simp

/- English proof (translation)
Use `prj_orth hM x hw` as an intermediate fact. Rewrite `this` using `[inner_sub_left, sub_eq_zero]`. Conclude with `this.symm`.
-/
private lemma inner_prj_left {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) {w : H}
    (hw : w ∈ M) : ⟪prj M x, w⟫_ℂ = ⟪x, w⟫_ℂ := by
  have := prj_orth hM x hw
  rw [inner_sub_left, sub_eq_zero] at this
  exact this.symm

/- English proof (translation)
Use `prj_eq hM (prj_mem hM b) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[inner_sub_left, h w hw, ← inner_sub_left]`. Conclude with `prj_orth hM b hw`.
-/
private lemma prj_congr {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {a b : H}
    (h : ∀ w ∈ M, ⟪a, w⟫_ℂ = ⟪b, w⟫_ℂ) : prj M a = prj M b := by
  refine prj_eq hM (prj_mem hM b) fun w hw => ?_
  rw [inner_sub_left, h w hw, ← inner_sub_left]
  exact prj_orth hM b hw

/- English proof (translation)
Establish `h1 : ⟪prj M x, y⟫_ℂ = ⟪prj M x, prj M y⟫_ℂ`. Rewrite using `[← inner_conj_symm, ← inner_prj_left hM y (prj_mem hM x), inner_conj_symm]`. Rewrite using `[h1, inner_prj_left hM x (prj_mem hM y)]`.
-/
private lemma inner_prj_symm {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x y : H) :
    ⟪prj M x, y⟫_ℂ = ⟪x, prj M y⟫_ℂ := by
  have h1 : ⟪prj M x, y⟫_ℂ = ⟪prj M x, prj M y⟫_ℂ := by
    rw [← inner_conj_symm, ← inner_prj_left hM y (prj_mem hM x), inner_conj_symm]
  rw [h1, inner_prj_left hM x (prj_mem hM y)]

/- English proof (translation)
Use `prj_eq hM (h1 _ (prj_mem hM x)) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[← map_sub, hadj]`. Conclude with `prj_orth hM x (h2 w hw)`.
-/
private lemma comm_prj {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (B B' : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B' y⟫_ℂ) (h1 : ∀ v ∈ M, B v ∈ M) (h2 : ∀ v ∈ M, B' v ∈ M)
    (x : H) : prj M (B x) = B (prj M x) := by
  refine prj_eq hM (h1 _ (prj_mem hM x)) fun w hw => ?_
  rw [← map_sub, hadj]
  exact prj_orth hM x (h2 w hw)

private def cmp (W : Submodule ℂ H) [FiniteDimensional ℂ W] (B : H →L[ℂ] H) : Module.End ℂ W :=
  LinearMap.codRestrict W (((prj W ∘L B : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ W.subtype)
    fun w => prj_mem (Submodule.closed_of_finiteDimensional W) _

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma coe_cmp (W : Submodule ℂ H) [FiniteDimensional ℂ W] (B : H →L[ℂ] H) (w : W) :
    ((cmp W B w : W) : H) = prj W (B w) := rfl

/- English proof (translation)
Establish `hcl` using `Submodule.closed_of_finiteDimensional W`. Set `e` to `stdOrthonormalBasis ℂ W`. Rewrite using `[LinearMap.trace_eq_sum_inner _ e]`. Apply the tactic sequence `have he : Orthonormal ℂ (fun k => ((e k : W) : H)) := e.orthonormal.comp_linearIsometry W.subtypeₗᵢ`. Take `⟨s, b, hvs, hb⟩` from `(he.toSubtypeRange).exists_hilbertBasis_extension`.

Establish `hbi : ∀ i, b i = (i : H)` using `fun i => congrFun hb i`. Set `f : Fin _ → s` to `fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩`. Establish `hf : Function.Injective f` using `fun k l h => by`. Establish `: ((e k : W) : H) = (e l : W)` using `congrArg (fun z : s => (z : H)) h`. Conclude with `he.linearIndependent.injective this`.

Establish `hbf : ∀ k, b (f k) = (e k : H)` using `fun k => hbi _`. Establish `hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0` using `fun i hi => by`. Use `prj_eq hcl W.zero_mem fun w hw => ?_` and prove the remaining obligations. Establish `hw' : (w : H) = ∑ k, ⟪(e k : H), w⟫_ℂ • (e k : H)`. Use `e.sum_repr' (⟨w, hw⟩ : W)` as an intermediate fact.

Establish `h2` using `congrArg (Subtype.val) this`. Simplify `h2.symm` using `[Submodule.coe_sum]`. Rewrite using `[sub_zero, hw', inner_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, ← hbf k]`.

Establish `: ⟪b i, b (f k)⟫_ℂ = 0` using `b.orthonormal.2 fun h => hi ⟨k, h.symm⟩`. Rewrite using `[this, mul_zero]`. Establish `hHS : IsHilbertSchmidt (prj W)`. Rewrite using `[isHilbertSchmidt_iff b]`. Establish `hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f` using `fun i hi => by`.

Assume the negation of the conclusion as `h`. Conclude with `hi (by simp [hout i h])`. Rewrite using `[← hf.tsum_eq hs, tsum_fintype]`. Conclude with `ENNReal.sum_lt_top.2 fun k _ => by`. Conclude with `ENNReal.pow_lt_top enorm_lt_top`.

Establish `hT : IsTraceClass (prj W ∘L B ∘L prj W)` using `isTraceClass_comp hHS (hHS.comp_left B)`. Establish `h1` using `hT.hasSum_trace b`. Establish `h2 : HasSum ((fun i => ⟪b i, (prj W ∘L B ∘L prj W) (b i)⟫_ℂ) ∘ f) (trace (prj W ∘L B ∘L prj W))` using `(hf.hasSum_iff fun i hi => by simp [hout i hi]).2 h1`. Unfold `trOn`. Rewrite using `[h2.unique (hasSum_fintype _)]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, hbf, ContinuousLinearMap.comp_apply]`. Rewrite using `[prj_of_mem hcl (e k).2, Submodule.coe_inner, coe_cmp]`.
-/
private lemma trOn_eq (W : Submodule ℂ H) [FiniteDimensional ℂ W] (B : H →L[ℂ] H) :
    trOn W B = LinearMap.trace ℂ W (cmp W B) := by
  classical
  have hcl := Submodule.closed_of_finiteDimensional W
  let e := stdOrthonormalBasis ℂ W
  rw [LinearMap.trace_eq_sum_inner _ e]
  have he : Orthonormal ℂ (fun k => ((e k : W) : H)) :=
    e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  obtain ⟨s, b, hvs, hb⟩ := (he.toSubtypeRange).exists_hilbertBasis_extension
  have hbi : ∀ i, b i = (i : H) := fun i => congrFun hb i
  let f : Fin _ → s := fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩
  have hf : Function.Injective f := fun k l h => by
    have : ((e k : W) : H) = (e l : W) := congrArg (fun z : s => (z : H)) h
    exact he.linearIndependent.injective this
  have hbf : ∀ k, b (f k) = (e k : H) := fun k => hbi _

  have hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0 := fun i hi => by
    refine prj_eq hcl W.zero_mem fun w hw => ?_
    have hw' : (w : H) = ∑ k, ⟪(e k : H), w⟫_ℂ • (e k : H) := by
      have := e.sum_repr' (⟨w, hw⟩ : W)
      have h2 := congrArg (Subtype.val) this
      simpa [Submodule.coe_sum] using h2.symm
    rw [sub_zero, hw', inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, ← hbf k]
    have : ⟪b i, b (f k)⟫_ℂ = 0 := b.orthonormal.2 fun h => hi ⟨k, h.symm⟩
    rw [this, mul_zero]
  have hHS : IsHilbertSchmidt (prj W) := by
    rw [isHilbertSchmidt_iff b]
    have hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f := fun i hi => by
      by_contra h
      exact hi (by simp [hout i h])
    rw [← hf.tsum_eq hs, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun k _ => by
      exact ENNReal.pow_lt_top enorm_lt_top
  have hT : IsTraceClass (prj W ∘L B ∘L prj W) := isTraceClass_comp hHS (hHS.comp_left B)
  have h1 := hT.hasSum_trace b
  have h2 : HasSum ((fun i => ⟪b i, (prj W ∘L B ∘L prj W) (b i)⟫_ℂ) ∘ f) (trace (prj W ∘L B ∘L prj W)) :=
    (hf.hasSum_iff fun i hi => by simp [hout i hi]).2 h1
  unfold trOn
  rw [h2.unique (hasSum_fintype _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp, hbf, ContinuousLinearMap.comp_apply]
  rw [prj_of_mem hcl (e k).2, Submodule.coe_inner, coe_cmp]

end Hilbert

section Slots
variable {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {π : UnitaryRep Γ H} {V : Submodule ℂ H} {m : ℕ}
  {ι : Fin (m + 1) → G →* Γ} {E : H →L[ℂ] H} {A : Fin (m + 1) → H →L[ℂ] H} {U : H ≃ₗᵢ[ℂ] H}

private def eF (B : H →L[ℂ] H) (y : ℝ) : Submodule ℂ H :=
  Module.End.eigenspace (B : H →ₗ[ℂ] H) (y : ℂ)

/- English proof (translation)
The claim follows from `Module.End.mem_eigenspace_iff`.
-/
private lemma mem_eF {B : H →L[ℂ] H} {y : ℝ} {x : H} : x ∈ eF B y ↔ B x = (y : ℂ) • x :=
  Module.End.mem_eigenspace_iff

/- English proof (translation)
Establish `: (eF B y : Set H) = (fun x => B x - (y : ℂ) • x) ⁻¹' {0}`. Use extensionality with `x`. Simplify using `[mem_eF, sub_eq_zero]`. Rewrite using `[this]`. Conclude with `isClosed_singleton.preimage (by fun_prop)`.
-/
private lemma eF_closed (B : H →L[ℂ] H) (y : ℝ) : IsClosed (eF B y : Set H) := by
  have : (eF B y : Set H) = (fun x => B x - (y : ℂ) • x) ⁻¹' {0} := by
    ext x
    simp [mem_eF, sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage (by fun_prop)

/- English proof (translation)
Unfold `eigIn`. Rewrite using `[Submodule.mem_inf, Module.End.mem_eigenspace_iff]`. Simplify using the standard rewrite rules.
-/
private lemma mem_R {x : H} : x ∈ eigIn V E 1 ↔ x ∈ V ∧ E x = x := by
  unfold eigIn
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  simp

/- English proof (translation)
Establish `hh : ∀ i, x ∈ eigIn (eigIn V E 1) (A i) y ↔ x ∈ eigIn V E 1 ∧ x ∈ eF (A i) y` using `fun i => Submodule.mem_inf`. Simplify using `only [jointEig, Submodule.mem_iInf, hh]`. Conclude with `⟨fun h => ⟨(h 0).1, fun i => (h i).2⟩, fun h i => ⟨h.1, h.2 i⟩⟩`.
-/
private lemma mem_W {y : ℝ} {x : H} :
    x ∈ jointEig V E A y ↔ x ∈ eigIn V E 1 ∧ ∀ i, x ∈ eF (A i) y := by
  have hh : ∀ i, x ∈ eigIn (eigIn V E 1) (A i) y ↔ x ∈ eigIn V E 1 ∧ x ∈ eF (A i) y :=
    fun i => Submodule.mem_inf
  simp only [jointEig, Submodule.mem_iInf, hh]
  exact ⟨fun h => ⟨(h 0).1, fun i => (h i).2⟩, fun h i => ⟨h.1, h.2 i⟩⟩

/- English proof (translation)
The claim follows from `(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (isSelfAdjoint_of_nonneg (h.A_pos i))) x z`.
-/
private lemma A_sym (h : Slots π V m ι E A U) (i : Fin (m + 1)) (x z : H) :
    ⟪A i x, z⟫_ℂ = ⟪x, A i z⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (isSelfAdjoint_of_nonneg (h.A_pos i))) x z

/- English proof (translation)
The claim follows from `(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h.E_sa) x z`.
-/
private lemma E_sym (h : Slots π V m ι E A U) (x z : H) : ⟪E x, z⟫_ℂ = ⟪x, E z⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h.E_sa) x z

private def Near (V : Submodule ℂ H) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H) (y : ℝ)
    (j : Fin (m + 1)) (x : H) : Prop :=
  x ∈ eigIn V E 1 ∧ ∀ k, k ≠ j → x ∈ eF (A k) y

/- English proof (translation)
Establish `hF` using `eF_closed (A j) y`. Establish `hV : IsClosed (V : Set H)` using `h.summand.closed`. Take `⟨hxR, hxk⟩` from `hx`. Take `⟨hxV, hxE⟩` from `mem_R.1 hxR`. Establish `hAF : ∀ k, ∀ v ∈ eF (A j) y, A k v ∈ eF (A j) y` using `fun k v hv => by`.

Rewrite `hv`, the goal using `[mem_eF]`. Rewrite using `[h.A_A j k, hv, map_smul]`. Establish `hEF : ∀ v ∈ eF (A j) y, E v ∈ eF (A j) y` using `fun v hv => by`. Rewrite `hv`, the goal using `[mem_eF]`. Rewrite using `[h.A_E, hv, map_smul]`.

Establish `hPV : ∀ v, prj V (A j v) = A j (prj V v)` using `comm_prj hV (A j) (A j) (A_sym h j) (h.A_mem j) (h.A_mem j)`. Establish `hPVF : ∀ v ∈ eF (A j) y, prj V v ∈ eF (A j) y` using `fun v hv => by`. Rewrite `hv`, the goal using `[mem_eF]`. Rewrite using `[← hPV, hv, map_smul]`. Establish `hQV` using `comm_prj hF (prj V) (prj V) (inner_prj_symm hV) hPVF hPVF x`.

Use `mem_W.2 ⟨mem_R.2 ⟨?_, ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite `hQV` using `[prj_of_mem hV hxV]`. Rewrite using `[hQV]`. Conclude with `prj_mem hV _`. Rewrite using `[← comm_prj hF E E (E_sym h) hEF hEF x, hxE]`.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Conclude with `prj_mem hF x`. Rewrite using `[mem_eF, ← comm_prj hF (A k) (A k) (A_sym h k) (hAF k) (hAF k) x, mem_eF.1 (hxk k hk), map_smul]`.
-/
private lemma Q_mem (h : Slots π V m ι E A U) {y : ℝ} {j : Fin (m + 1)} {x : H}
    (hx : Near V E A y j x) : prj (eF (A j) y) x ∈ jointEig V E A y := by
  have hF := eF_closed (A j) y
  have hV : IsClosed (V : Set H) := h.summand.closed
  obtain ⟨hxR, hxk⟩ := hx
  obtain ⟨hxV, hxE⟩ := mem_R.1 hxR
  have hAF : ∀ k, ∀ v ∈ eF (A j) y, A k v ∈ eF (A j) y := fun k v hv => by
    rw [mem_eF] at hv ⊢
    rw [h.A_A j k, hv, map_smul]
  have hEF : ∀ v ∈ eF (A j) y, E v ∈ eF (A j) y := fun v hv => by
    rw [mem_eF] at hv ⊢
    rw [h.A_E, hv, map_smul]
  have hPV : ∀ v, prj V (A j v) = A j (prj V v) :=
    comm_prj hV (A j) (A j) (A_sym h j) (h.A_mem j) (h.A_mem j)
  have hPVF : ∀ v ∈ eF (A j) y, prj V v ∈ eF (A j) y := fun v hv => by
    rw [mem_eF] at hv ⊢
    rw [← hPV, hv, map_smul]
  have hQV := comm_prj hF (prj V) (prj V) (inner_prj_symm hV) hPVF hPVF x
  refine mem_W.2 ⟨mem_R.2 ⟨?_, ?_⟩, fun k => ?_⟩
  · rw [prj_of_mem hV hxV] at hQV
    rw [hQV]
    exact prj_mem hV _
  · rw [← comm_prj hF E E (E_sym h) hEF hEF x, hxE]
  · by_cases hk : k = j
    · subst hk
      exact prj_mem hF x
    · rw [mem_eF, ← comm_prj hF (A k) (A k) (A_sym h k) (hAF k) (hAF k) x,
        mem_eF.1 (hxk k hk), map_smul]

/- English proof (translation)
Establish `hP : prj (jointEig V E A y) x = prj (eF (A j) y) x` using `prj_eq hW (Q_mem h hx) fun w hw => prj_orth (eF_closed _ _) x ((mem_W.1 hw).2 j)`. Rewrite using `[hP]`. Conclude with `inner_prj_left (eF_closed _ _) x hf`.
-/
private lemma inner_P (h : Slots π V m ι E A U) {y : ℝ}
    (hW : IsClosed (jointEig V E A y : Set H)) {j : Fin (m + 1)} {x f : H}
    (hx : Near V E A y j x) (hf : f ∈ eF (A j) y) :
    ⟪prj (jointEig V E A y) x, f⟫_ℂ = ⟪x, f⟫_ℂ := by
  have hP : prj (jointEig V E A y) x = prj (eF (A j) y) x :=
    prj_eq hW (Q_mem h hx) fun w hw => prj_orth (eF_closed _ _) x ((mem_W.1 hw).2 j)
  rw [hP]
  exact inner_prj_left (eF_closed _ _) x hf

/- English proof (translation)
Assemble the required witnesses or components as `⟨(mem_W.1 hw).1, fun k _ => (mem_W.1 hw).2 k⟩`.
-/
private lemma near_of_mem {y : ℝ} {w : H} (hw : w ∈ jointEig V E A y) (j : Fin (m + 1)) :
    Near V E A y j w :=
  ⟨(mem_W.1 hw).1, fun k _ => (mem_W.1 hw).2 k⟩

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_eF]`. Rewrite using `[h.A_ι k j hk, hx, map_smul]`.
-/
private lemma pi_eF (h : Slots π V m ι E A U) {y : ℝ} {k j : Fin (m + 1)} (hk : k ≠ j) (g : G)
    {x : H} (hx : x ∈ eF (A k) y) : π (ι j g) x ∈ eF (A k) y := by
  rw [mem_eF] at hx ⊢
  rw [h.A_ι k j hk, hx, map_smul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(cutIrr Γ G H π V m ι E A U h).2.1 j g x hx.1, fun k hk => pi_eF h hk g (hx.2 k hk)⟩`.
-/
private lemma pi_near (h : Slots π V m ι E A U) {y : ℝ} {j : Fin (m + 1)} (g : G) {x : H}
    (hx : Near V E A y j x) : Near V E A y j (π (ι j g) x) :=
  ⟨(cutIrr Γ G H π V m ι E A U h).2.1 j g x hx.1, fun k hk => pi_eF h hk g (hx.2 k hk)⟩

/- English proof (translation)
Use `prj_congr hW fun w hw => ?_` and prove the remaining obligations. Rewrite using `[UnitaryRep.inner_map_left, UnitaryRep.inner_map_left, ← map_inv (ι i)]`. Establish `hx : Near V E A y i (π (ι i g⁻¹) w)` using `pi_near h _ (near_of_mem hw i)`. Rewrite using `[inner_prj_symm hW, ← inner_conj_symm, inner_P h hW hx hu, inner_conj_symm]`.
-/
private lemma key (h : Slots π V m ι E A U) {y : ℝ}
    (hW : IsClosed (jointEig V E A y : Set H)) {i : Fin (m + 1)} (g : G) {u : H}
    (hu : u ∈ eF (A i) y) :
    prj (jointEig V E A y) (π (ι i g) (prj (jointEig V E A y) u)) =
      prj (jointEig V E A y) (π (ι i g) u) := by
  refine prj_congr hW fun w hw => ?_
  rw [UnitaryRep.inner_map_left, UnitaryRep.inner_map_left, ← map_inv (ι i)]
  have hx : Near V E A y i (π (ι i g⁻¹) w) := pi_near h _ (near_of_mem hw i)
  rw [inner_prj_symm hW, ← inner_conj_symm, inner_P h hW hx hu, inner_conj_symm]

/- English proof (translation)
Use `prj_congr hW fun w hw => ?_` and prove the remaining obligations. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right S, ← ContinuousLinearMap.adjoint_inner_right S]`. Use `inner_P h hW hx ?_` and prove the remaining obligations. Rewrite using `[mem_eF]`. Use `ext_inner_left ℂ fun z => ?_` and prove the remaining obligations.

Rewrite using `[← A_sym h j, ContinuousLinearMap.adjoint_inner_right, hS, A_sym h j, mem_eF.1 ((mem_W.1 hw).2 j), inner_smul_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]`.
-/
private lemma key2 (h : Slots π V m ι E A U) {y : ℝ}
    (hW : IsClosed (jointEig V E A y : Set H)) {j : Fin (m + 1)} {x : H}
    (hx : Near V E A y j x) (S : H →L[ℂ] H) (hS : ∀ v, S (A j v) = A j (S v)) :
    prj (jointEig V E A y) (S (prj (jointEig V E A y) x)) = prj (jointEig V E A y) (S x) := by
  refine prj_congr hW fun w hw => ?_
  rw [← ContinuousLinearMap.adjoint_inner_right S, ← ContinuousLinearMap.adjoint_inner_right S]
  refine inner_P h hW hx ?_
  rw [mem_eF]
  refine ext_inner_left ℂ fun z => ?_
  rw [← A_sym h j, ContinuousLinearMap.adjoint_inner_right, hS, A_sym h j,
    mem_eF.1 ((mem_W.1 hw).2 j), inner_smul_right, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]

/- English proof (translation)
Establish `hW : IsClosed (jointEig V E A y : Set H)` using `Submodule.closed_of_finiteDimensional _`. Take `⟨hRc, hRinv, hirr⟩` from `cutIrr Γ G H π V m ι E A U h`. Set `p' : Submodule ℂ H` to `p.map (jointEig V E A y).subtype`. Establish `hp'W : ∀ w ∈ p', w ∈ jointEig V E A y`. Introduce and unpack `_ ⟨w, -, rfl⟩`.

Conclude with `w.2`. Establish `hp'c : IsClosed (p' : Set H)` using `Submodule.closed_of_finiteDimensional p'`. Establish `hp' : ∀ i g, ∀ w ∈ p', prj (jointEig V E A y) (π (ι i g) w) ∈ p'`. Introduce and unpack `i g _ ⟨w, hw, rfl⟩`. Conclude with `⟨_, hp i g w hw, rfl⟩`.

Set `Φ : (Fin (m + 1) → G) →* Γ` to `MonoidHom.noncommPiCoprod ι (fun i j hij x z => h.ι_comm i j hij x z)`. Establish `hΦ : ∀ i g, Φ (Pi.mulSingle i g) = ι i g` using `fun i g => MonoidHom.noncommPiCoprod_mulSingle ι i g`. Establish `step : ∀ (g : Fin (m + 1) → G) (s : Finset (Fin (m + 1))), ∀ w ∈ p', π (Φ (s.piecewise g 1)) w ∈ eigIn V E 1 ∧ (∀ k, k ∉ s → π (Φ (s.piecewise g 1)) w ∈ eF (A k) y) ∧ prj (jointEig V E A y) (π (Φ (s.piecewise g 1)) w) ∈ p'`. Introduce `g s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Introduce `w hw`. Establish `hw'` using `hp'W w hw`. Simplify using `only [Finset.piecewise_empty, map_one, UnitaryRep.map_one_apply]`. Conclude with `⟨(mem_W.1 hw').1, fun k _ => (mem_W.1 hw').2 k, by rwa [prj_of_mem hW hw']⟩`.

Consider the case `insert a s ha ih`. Introduce `w hw`. Establish `e1 : (insert a s).piecewise g 1 = Pi.mulSingle a (g a) * s.piecewise g 1`. Use extensionality with `k`. Distinguish the cases in `hk : k = a`.

Substitute `hk` using the available equality. Simplify using `[ha]`. Simplify using `[hk, Finset.piecewise, Pi.mulSingle_eq_of_ne hk]`. Take `⟨h1, h2, h3⟩` from `ih w hw`. Rewrite using `[e1, map_mul, hΦ, UnitaryRep.map_mul_apply]`.

Use `⟨hRinv a _ _ h1, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_insert, not_or]`. Conclude with `pi_eF h hk.1 _ (h2 k hk.2)`. Rewrite using `[← key h hW (g a) (h2 a ha)]`. Conclude with `hp' a (g a) _ h3`.

Establish `hall : ∀ g, ∀ w ∈ p', π (Φ g) w ∈ eigIn V E 1 ∧ prj (jointEig V E A y) (π (Φ g) w) ∈ p'` using `fun g w hw => by`. Use `step g Finset.univ w hw` as an intermediate fact. Rewrite `this` using `[Finset.piecewise_univ]`. Conclude with `⟨this.1, this.2.2⟩`. Set `M : Submodule ℂ H` to `Submodule.span ℂ {x | ∃ g, ∃ w ∈ p', x = π (Φ g) w}`.

Establish `hMR : M ≤ eigIn V E 1` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨g, w, hw, rfl⟩`. Conclude with `(hall g w hw).1)`. Establish `hCR : M.topologicalClosure ≤ eigIn V E 1` using `Submodule.topologicalClosure_minimal _ hMR hRc`. Establish `hCinv : ∀ i g, ∀ v ∈ M.topologicalClosure, π (ι i g) v ∈ M.topologicalClosure`.

Introduce `i g`. Establish `h1 : M ≤ M.topologicalClosure.comap ((π (ι i g) : H →L[ℂ] H) : H →ₗ[ℂ] H)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨g', w, hw, rfl⟩`. Use `M.le_topologicalClosure (Submodule.subset_span ⟨Pi.mulSingle i g * g', w, hw, ?_⟩)` and prove the remaining obligations. Rewrite using `[map_mul, hΦ, UnitaryRep.map_mul_apply]`.

Use the proof step `rfl)`. Establish `hcl : IsClosed ((M.topologicalClosure.comap ((π (ι i g) : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)` using `M.isClosed_topologicalClosure.preimage (π (ι i g)).continuous`. Conclude with `fun v hv => Submodule.topologicalClosure_minimal _ h1 hcl hv`. Establish `hCp : ∀ v ∈ M.topologicalClosure, prj (jointEig V E A y) v ∈ p'`. Establish `h1 : M ≤ p'.comap ((prj (jointEig V E A y) : H →L[ℂ] H) : H →ₗ[ℂ] H)` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨g, w, hw, rfl⟩`. Conclude with `(hall g w hw).2)`. Establish `hcl : IsClosed ((p'.comap ((prj (jointEig V E A y) : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)` using `hp'c.preimage (prj (jointEig V E A y)).continuous`. Conclude with `fun v hv => Submodule.topologicalClosure_minimal _ h1 hcl hv`. Break down `hirr _ hCR M.isClosed_topologicalClosure hCinv with h0 | h1` into its components or cases.

Use `left`. Use `(Submodule.eq_bot_iff p).2 fun w hw => ?_` and prove the remaining obligations. Establish `hwM : (w : H) ∈ M.topologicalClosure` using `M.le_topologicalClosure (Submodule.subset_span ⟨1, w, ⟨w, hw, rfl⟩, by simp⟩)`. Rewrite `hwM` using `[h0]`. Conclude with `Subtype.ext ((Submodule.mem_bot ℂ).1 hwM)`.

Use `right`. Use `(Submodule.eq_top_iff').2 fun w => ?_` and prove the remaining obligations. Establish `hwC : (w : H) ∈ M.topologicalClosure`. Rewrite using `[h1]`. Conclude with `(mem_W.1 w.2).1`.

Use `hCp _ hwC` as an intermediate fact. Rewrite `this` using `[prj_of_mem hW w.2]`. Take `⟨z, hz, hzw⟩` from `this`. Establish `: z = w` using `Subtype.ext hzw`. Rewrite using `[← this]` and apply the resulting hypothesis.
-/
private lemma irr (h : Slots π V m ι E A U) (y : ℝ) [FiniteDimensional ℂ (jointEig V E A y)]
    (p : Submodule ℂ (jointEig V E A y))
    (hp : ∀ i g, ∀ w ∈ p, cmp (jointEig V E A y) (π (ι i g)) w ∈ p) : p = ⊥ ∨ p = ⊤ := by
  have hW : IsClosed (jointEig V E A y : Set H) := Submodule.closed_of_finiteDimensional _
  obtain ⟨hRc, hRinv, hirr⟩ := cutIrr Γ G H π V m ι E A U h
  let p' : Submodule ℂ H := p.map (jointEig V E A y).subtype
  have hp'W : ∀ w ∈ p', w ∈ jointEig V E A y := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hp'c : IsClosed (p' : Set H) := Submodule.closed_of_finiteDimensional p'
  have hp' : ∀ i g, ∀ w ∈ p', prj (jointEig V E A y) (π (ι i g) w) ∈ p' := by
    rintro i g _ ⟨w, hw, rfl⟩
    exact ⟨_, hp i g w hw, rfl⟩
  let Φ : (Fin (m + 1) → G) →* Γ :=
    MonoidHom.noncommPiCoprod ι (fun i j hij x z => h.ι_comm i j hij x z)
  have hΦ : ∀ i g, Φ (Pi.mulSingle i g) = ι i g := fun i g =>
    MonoidHom.noncommPiCoprod_mulSingle ι i g
  have step : ∀ (g : Fin (m + 1) → G) (s : Finset (Fin (m + 1))), ∀ w ∈ p',
      π (Φ (s.piecewise g 1)) w ∈ eigIn V E 1 ∧
        (∀ k, k ∉ s → π (Φ (s.piecewise g 1)) w ∈ eF (A k) y) ∧
        prj (jointEig V E A y) (π (Φ (s.piecewise g 1)) w) ∈ p' := by
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      intro w hw
      have hw' := hp'W w hw
      simp only [Finset.piecewise_empty, map_one, UnitaryRep.map_one_apply]
      exact ⟨(mem_W.1 hw').1, fun k _ => (mem_W.1 hw').2 k, by rwa [prj_of_mem hW hw']⟩
    | insert a s ha ih =>
      intro w hw
      have e1 : (insert a s).piecewise g 1 = Pi.mulSingle a (g a) * s.piecewise g 1 := by
        ext k
        by_cases hk : k = a
        · subst hk
          simp [ha]
        · simp [hk, Finset.piecewise, Pi.mulSingle_eq_of_ne hk]
      obtain ⟨h1, h2, h3⟩ := ih w hw
      rw [e1, map_mul, hΦ, UnitaryRep.map_mul_apply]
      refine ⟨hRinv a _ _ h1, fun k hk => ?_, ?_⟩
      · rw [Finset.mem_insert, not_or] at hk
        exact pi_eF h hk.1 _ (h2 k hk.2)
      · rw [← key h hW (g a) (h2 a ha)]
        exact hp' a (g a) _ h3
  have hall : ∀ g, ∀ w ∈ p', π (Φ g) w ∈ eigIn V E 1 ∧
      prj (jointEig V E A y) (π (Φ g) w) ∈ p' := fun g w hw => by
    have := step g Finset.univ w hw
    rw [Finset.piecewise_univ] at this
    exact ⟨this.1, this.2.2⟩
  let M : Submodule ℂ H := Submodule.span ℂ {x | ∃ g, ∃ w ∈ p', x = π (Φ g) w}
  have hMR : M ≤ eigIn V E 1 := Submodule.span_le.2 (by
    rintro _ ⟨g, w, hw, rfl⟩
    exact (hall g w hw).1)
  have hCR : M.topologicalClosure ≤ eigIn V E 1 :=
    Submodule.topologicalClosure_minimal _ hMR hRc
  have hCinv : ∀ i g, ∀ v ∈ M.topologicalClosure, π (ι i g) v ∈ M.topologicalClosure := by
    intro i g
    have h1 : M ≤ M.topologicalClosure.comap ((π (ι i g) : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
      Submodule.span_le.2 (by
        rintro _ ⟨g', w, hw, rfl⟩
        refine M.le_topologicalClosure (Submodule.subset_span ⟨Pi.mulSingle i g * g', w, hw, ?_⟩)
        rw [map_mul, hΦ, UnitaryRep.map_mul_apply]
        rfl)
    have hcl : IsClosed
        ((M.topologicalClosure.comap ((π (ι i g) : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) :
          Set H) :=
      M.isClosed_topologicalClosure.preimage (π (ι i g)).continuous
    exact fun v hv => Submodule.topologicalClosure_minimal _ h1 hcl hv
  have hCp : ∀ v ∈ M.topologicalClosure, prj (jointEig V E A y) v ∈ p' := by
    have h1 : M ≤ p'.comap ((prj (jointEig V E A y) : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
      Submodule.span_le.2 (by
        rintro _ ⟨g, w, hw, rfl⟩
        exact (hall g w hw).2)
    have hcl : IsClosed
        ((p'.comap ((prj (jointEig V E A y) : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      hp'c.preimage (prj (jointEig V E A y)).continuous
    exact fun v hv => Submodule.topologicalClosure_minimal _ h1 hcl hv
  rcases hirr _ hCR M.isClosed_topologicalClosure hCinv with h0 | h1
  · left
    refine (Submodule.eq_bot_iff p).2 fun w hw => ?_
    have hwM : (w : H) ∈ M.topologicalClosure := M.le_topologicalClosure
      (Submodule.subset_span ⟨1, w, ⟨w, hw, rfl⟩, by simp⟩)
    rw [h0] at hwM
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hwM)
  · right
    refine (Submodule.eq_top_iff').2 fun w => ?_
    have hwC : (w : H) ∈ M.topologicalClosure := by
      rw [h1]
      exact (mem_W.1 w.2).1
    have := hCp _ hwC
    rw [prj_of_mem hW w.2] at this
    obtain ⟨z, hz, hzw⟩ := this
    have : z = w := Subtype.ext hzw
    rwa [← this]

/- English proof (translation)
Establish `hW : IsClosed (jointEig V E A y : Set H)` using `Submodule.closed_of_finiteDimensional _`. Set `T : Fin (m + 1) → G → Module.End ℂ (jointEig V E A y)` to `fun i g => cmp (jointEig V E A y) (π (ι i g))`. Establish `hTc : ∀ i j, i ≠ j → ∀ x z, Commute (T i x) (T j z)`. Introduce `i j hij x z`. Use `LinearMap.ext fun w => Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `prj _ (π (ι i x) (prj _ (π (ι j z) w))) = prj _ (π (ι j z) (prj _ (π (ι i x) w)))`. Establish `hwi` using `(mem_W.1 w.2).2 i`. Establish `hwj` using `(mem_W.1 w.2).2 j`. Rewrite using `[key h hW x (pi_eF h hij z hwi), key h hW z (pi_eF h hij.symm x hwj), ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, (h.ι_comm i j hij x z).eq]`. Establish `hUW : ∀ w ∈ jointEig V E A y, U w ∈ jointEig V E A y` using `fun w hw => by`.

Take `⟨hR, hA⟩` from `mem_W.1 hw`. Take `⟨hV, hE⟩` from `mem_R.1 hR`. Use `mem_W.2 ⟨mem_R.2 ⟨?_, ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← h.U_mem]`. Conclude with `⟨w, hV, rfl⟩`.

Rewrite using `[← h.U_E, hE]`. Rewrite using `[mem_eF, ← h.U_A, mem_eF.1 (hA (i + 1)), map_smul]`. Set `U0 : Module.End ℂ (jointEig V E A y)` to `LinearMap.restrict ((U.toLinearEquiv : H ≃ₗ[ℂ] H) : H →ₗ[ℂ] H) hUW`. Establish `hU0 : Function.Injective U0` using `fun a b hab => Subtype.ext (U.injective (congrArg Subtype.val hab))`. Set `UW : (jointEig V E A y) ≃ₗ[ℂ] (jointEig V E A y)` to `LinearEquiv.ofInjectiveEndo U0 hU0`.

Establish `hUWc : ∀ w, ((UW w : jointEig V E A y) : H) = U w` using `fun w => rfl`. Establish `hUs : ∀ w ∈ jointEig V E A y, U.symm w ∈ jointEig V E A y` using `fun w hw => by`. Establish `h1` using `hUWc (UW.symm ⟨w, hw⟩)`. Rewrite `h1` using `[UW.apply_symm_apply]`. Establish `h2 : w = U (UW.symm ⟨w, hw⟩ : jointEig V E A y)` using `h1`.

Rewrite using `[h2, U.symm_apply_apply]`. Conclude with `Subtype.coe_prop _`. Establish `hUP : ∀ x, prj (jointEig V E A y) (U x) = U (prj (jointEig V E A y) x)` using `comm_prj hW (U : H →L[ℂ] H) ((U.symm : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H) (fun x z => U.inner_map_eq_flip x z) hUW hUs`. Establish `hint : ∀ i x w, UW (T (i + 1) x w) = T i x (UW w)`. Introduce `i x w`.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `U (prj _ (π (ι (i + 1) x) w)) = prj _ (π (ι i x) (U w))`. Rewrite using `[← hUP, h.U_ι]`. Take `⟨c, hc, hcS⟩` from `algTrace (jointEig V E A y) G m T hTc (fun p hp => irr h y p hp) UW hint`. Use `⟨c, hc, fun i₀ S hSA hSπ => ?_⟩` and prove the remaining obligations.

Establish `hcomm : ∀ j, j ≠ i₀ → ∀ x, Commute (cmp (jointEig V E A y) S) (T j x)`. Introduce `j hj x`. Use `LinearMap.ext fun w => Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `prj _ (S (prj _ (π (ι j x) w))) = prj _ (π (ι j x) (prj _ (S w)))`. Establish `hSw : S w ∈ eF (A j) y`.

Rewrite using `[mem_eF, ← hSA j hj, mem_eF.1 ((mem_W.1 w.2).2 j), map_smul]`. Rewrite using `[key2 h hW (pi_near h x (near_of_mem w.2 j)) S (hSA j hj), key h hW x hSw, hSπ j hj]`. Rewrite using `[trOn_eq, trOn_eq, ← hcS i₀ _ hcomm]`. Both sides reduce to the same expression.
-/
private lemma aux (h : Slots π V m ι E A U) (y : ℝ) [FiniteDimensional ℂ (jointEig V E A y)] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H),
      (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
      (∀ j, j ≠ i₀ → ∀ g v, S (π (ι j g) v) = π (ι j g) (S v)) →
      trOn (jointEig V E A y) (S ∘L (U : H →L[ℂ] H)) = c * trOn (jointEig V E A y) S := by
  have hW : IsClosed (jointEig V E A y : Set H) := Submodule.closed_of_finiteDimensional _
  let T : Fin (m + 1) → G → Module.End ℂ (jointEig V E A y) :=
    fun i g => cmp (jointEig V E A y) (π (ι i g))
  have hTc : ∀ i j, i ≠ j → ∀ x z, Commute (T i x) (T j z) := by
    intro i j hij x z
    refine LinearMap.ext fun w => Subtype.ext ?_
    change prj _ (π (ι i x) (prj _ (π (ι j z) w))) = prj _ (π (ι j z) (prj _ (π (ι i x) w)))
    have hwi := (mem_W.1 w.2).2 i
    have hwj := (mem_W.1 w.2).2 j
    rw [key h hW x (pi_eF h hij z hwi), key h hW z (pi_eF h hij.symm x hwj),
      ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, (h.ι_comm i j hij x z).eq]
  have hUW : ∀ w ∈ jointEig V E A y, U w ∈ jointEig V E A y := fun w hw => by
    obtain ⟨hR, hA⟩ := mem_W.1 hw
    obtain ⟨hV, hE⟩ := mem_R.1 hR
    refine mem_W.2 ⟨mem_R.2 ⟨?_, ?_⟩, fun i => ?_⟩
    · rw [← h.U_mem]
      exact ⟨w, hV, rfl⟩
    · rw [← h.U_E, hE]
    · rw [mem_eF, ← h.U_A, mem_eF.1 (hA (i + 1)), map_smul]
  let U0 : Module.End ℂ (jointEig V E A y) :=
    LinearMap.restrict ((U.toLinearEquiv : H ≃ₗ[ℂ] H) : H →ₗ[ℂ] H) hUW
  have hU0 : Function.Injective U0 := fun a b hab =>
    Subtype.ext (U.injective (congrArg Subtype.val hab))
  let UW : (jointEig V E A y) ≃ₗ[ℂ] (jointEig V E A y) := LinearEquiv.ofInjectiveEndo U0 hU0
  have hUWc : ∀ w, ((UW w : jointEig V E A y) : H) = U w := fun w => rfl
  have hUs : ∀ w ∈ jointEig V E A y, U.symm w ∈ jointEig V E A y := fun w hw => by
    have h1 := hUWc (UW.symm ⟨w, hw⟩)
    rw [UW.apply_symm_apply] at h1
    have h2 : w = U (UW.symm ⟨w, hw⟩ : jointEig V E A y) := h1
    rw [h2, U.symm_apply_apply]
    exact Subtype.coe_prop _
  have hUP : ∀ x, prj (jointEig V E A y) (U x) = U (prj (jointEig V E A y) x) :=
    comm_prj hW (U : H →L[ℂ] H) ((U.symm : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H)
      (fun x z => U.inner_map_eq_flip x z) hUW hUs
  have hint : ∀ i x w, UW (T (i + 1) x w) = T i x (UW w) := by
    intro i x w
    refine Subtype.ext ?_
    change U (prj _ (π (ι (i + 1) x) w)) = prj _ (π (ι i x) (U w))
    rw [← hUP, h.U_ι]
  obtain ⟨c, hc, hcS⟩ := algTrace (jointEig V E A y) G m T hTc (fun p hp => irr h y p hp) UW hint
  refine ⟨c, hc, fun i₀ S hSA hSπ => ?_⟩
  have hcomm : ∀ j, j ≠ i₀ → ∀ x, Commute (cmp (jointEig V E A y) S) (T j x) := by
    intro j hj x
    refine LinearMap.ext fun w => Subtype.ext ?_
    change prj _ (S (prj _ (π (ι j x) w))) = prj _ (π (ι j x) (prj _ (S w)))
    have hSw : S w ∈ eF (A j) y := by
      rw [mem_eF, ← hSA j hj, mem_eF.1 ((mem_W.1 w.2).2 j), map_smul]
    rw [key2 h hW (pi_near h x (near_of_mem w.2 j)) S (hSA j hj), key h hW x hSw, hSπ j hj]
  rw [trOn_eq, trOn_eq, ← hcS i₀ _ hcomm]
  rfl

end Slots

end UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Introduce `Γ G H _ _ _ _ _ _ π V m ι E A U h y hfd`. Conclude with `aux h y`.
-/
theorem UpperTheory.ConvolutionTheory.L1.jointTrace :
    UpperTheory.ConvolutionTheory.L1.JointTrace := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h y hfd
  exact aux h y
