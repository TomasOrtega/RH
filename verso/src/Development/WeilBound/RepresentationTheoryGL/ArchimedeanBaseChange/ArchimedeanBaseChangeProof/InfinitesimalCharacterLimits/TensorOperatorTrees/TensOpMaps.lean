import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TrStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

open PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap PositivityTheory.Rg.Rs.InducedTensorMap.Main PositivityTheory.Rg.Rs.ParabolicProjection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.span ℂ {φ | MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ ∧ φ ∈ finVec (cptRep E (r + s))} = _`. Rewrite using `[show {φ : Sm E (r + s) | MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ ∧ φ ∈ finVec (cptRep E (r + s))} = ((indSub (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) ⊓ finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) : Set (Sm E (r + s))) from S …`. Conclude with `Submodule.span_eq _`.
-/
theorem node_space (t₁ : Tr E r) (t₂ : Tr E s) :
    (Tr.node t₁ t₂).space =
      indSub (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) ⊓ finVec (cptRep E (r + s)) := by
  change Submodule.span ℂ {φ | MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ ∧
    φ ∈ finVec (cptRep E (r + s))} = _
  rw [show {φ : Sm E (r + s) | MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ ∧
      φ ∈ finVec (cptRep E (r + s))} = ((indSub (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) ⊓
      finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) : Set (Sm E (r + s))) from Set.ext fun _ => Iff.rfl]
  exact Submodule.span_eq _

/- English proof (translation)
Take `⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩` from `InducedTensorMap.tensor_pair_finite_sum hF`. Rewrite using `[tensOp_sum]`. Conclude with `InducedTensorMap.A.sum_mem (fun i => hm₁ _ (u₁ i)) fun i => hm₂ _ (u₂ i)`.
-/
theorem tensOp_maps {U₁ U₁' : Submodule ℂ (Sm E r)} {U₂ U₂' : Submodule ℂ (Sm E s)} {g₁ : Sm E r →ₗ[ℂ] Sm E r}
    {g₂ : Sm E s →ₗ[ℂ] Sm E s} (hm₁ : ∀ ψ ∈ U₁, g₁ ψ ∈ U₁') (hm₂ : ∀ ψ ∈ U₂, g₂ ψ ∈ U₂')
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) : tensOp g₁ g₂ F ∈ tens2 U₁' U₂' := by
  obtain ⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩ := InducedTensorMap.tensor_pair_finite_sum hF
  rw [tensOp_sum]
  exact InducedTensorMap.A.sum_mem (fun i => hm₁ _ (u₁ i)) fun i => hm₂ _ (u₂ i)

/- English proof (translation)
Take `⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩` from `InducedTensorMap.tensor_pair_finite_sum hF`. Rewrite `h0` using `[tensOp_sum]`. Establish `s1 : ∀ a, ∑ i, (g₁ (ψ₁ i)).1 a • ψ₂ i = 0`. Introduce `a`. Use `hn₂ _ (Submodule.sum_mem _ fun i _ => U₂.smul_mem _ (u₂ i)) (Subtype.ext (funext fun b => ?_))` and prove the remaining obligations.

Use `congrFun h0 (a, b)` as an intermediate fact. Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ZeroMemClass.coe_zero] at this ⊢`. Conclude with `this`. Establish `s2 : ∀ b, ∑ i, (ψ₂ i).1 b • ψ₁ i = 0`. Introduce `b`.

Use `hn₁ _ (Submodule.sum_mem _ fun i _ => U₁.smul_mem _ (u₁ i)) (Subtype.ext (funext fun a => ?_))` and prove the remaining obligations. Use `congrArg (fun w : Sm E s => w.1 b) (s1 a)` as an intermediate fact. Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ZeroMemClass.coe_zero] at this ⊢`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Use function extensionality and compare the values at `m`. Use `congrArg (fun w : Sm E r => w.1 m.1) (s2 m.2)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ZeroMemClass.coe_zero] at this ⊢`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem tensOp_inj {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {g₁ : Sm E r →ₗ[ℂ] Sm E r}
    {g₂ : Sm E s →ₗ[ℂ] Sm E s} (hn₁ : ∀ ψ ∈ U₁, g₁ ψ = 0 → ψ = 0) (hn₂ : ∀ ψ ∈ U₂, g₂ ψ = 0 → ψ = 0)
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (h0 : tensOp g₁ g₂ F = 0) : F = 0 := by
  obtain ⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩ := InducedTensorMap.tensor_pair_finite_sum hF
  rw [tensOp_sum] at h0
  have s1 : ∀ a, ∑ i, (g₁ (ψ₁ i)).1 a • ψ₂ i = 0 := by
    intro a
    refine hn₂ _ (Submodule.sum_mem _ fun i _ => U₂.smul_mem _ (u₂ i)) (Subtype.ext (funext fun b => ?_))
    have := congrFun h0 (a, b)
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    exact this
  have s2 : ∀ b, ∑ i, (ψ₂ i).1 b • ψ₁ i = 0 := by
    intro b
    refine hn₁ _ (Submodule.sum_mem _ fun i _ => U₁.smul_mem _ (u₁ i)) (Subtype.ext (funext fun a => ?_))
    have := congrArg (fun w : Sm E s => w.1 b) (s1 a)
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  funext m
  have := congrArg (fun w : Sm E r => w.1 m.1) (s2 m.2)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ZeroMemClass.coe_zero] at this ⊢
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Establish `H : Good U₁ U₂ g₁ g₂` using `⟨hU₁, hU₂, he₁, he₂⟩`. Establish `hV : IsStable (indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)))`. Establish `h` using `isStable_indFin hU₁ hU₂`. Rewrite `h` using `[show {φ : Sm E (r + s) | MemInd2 U₁ U₂ φ ∧ φ ∈ finVec (cptRep E (r + s))} = ((indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) : Set (Sm E (r + s))) from Set.ext fun _ => Iff.rfl, Submodule.span_eq]`. Then use the resulting hypothesis. Set `L : (indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) →ₗ[ℂ] Sm E (r + s)` to `{ toFun := fun φ => ⟨ind g₁ g₂ φ.1.1, ind_mem_Sm H (Submodule.mem_inf.1 φ.2).1 (Submodule.mem_inf.1 φ.2).2⟩ map_add' := fun φ ψ => Subtype.ext (map_add (ind g₁ g₂) φ.1.1 ψ.1.1) map_smul' := fun c φ => Subtype.ext (map_smul (ind g₁ g₂) c φ.1.1) }`.

Take `⟨T', hT'⟩` from `LinearMap.exists_extend L`. Establish `e : ∀ φ (hφ : φ ∈ indSub U₁ U₂ ⊓ finVec (cptRep E (r + s))), (T' φ).1 = ind g₁ g₂ φ.1` using `fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hT' ⟨φ, hφ⟩)`. Establish `heq : ∀ o, ∀ φ ∈ indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)), T' (act o φ) = act o (T' φ)`. Introduce `o φ hφ`. Establish `ho` using `hV o φ hφ`.

Take `⟨hI, hK⟩` from `Submodule.mem_inf.1 hφ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[e _ ho]`. Consider the cases of `o with`. Consider the case `fin g`.

Rewrite using `[act_fin_val, act_fin_val, e _ hφ]`. Use function extensionality and compare the values at `x`. Conclude with `ind_rt H hI 1 g x`. Consider the case `cpt k`. Rewrite using `[act_cpt_val, act_cpt_val, e _ hφ]`.

Use function extensionality and compare the values at `x`. Conclude with `ind_rt H hI k 1 x`. Consider the case `lie X`. Express the relevant statement in the definitionally equal form `ind g₁ g₂ (lie E (r + s) X φ).1 = lieD X (T' φ).1`. Rewrite using `[e _ hφ]`.

Conclude with `ind_lie H hI hK X (lie_mem_indSub hU₁ hU₂ hI hK X)`. Use `⟨T', fun φ hφ => ?_, fun φ hφ h0 => ?_, heq⟩` and prove the remaining obligations. Take `⟨hI, hK⟩` from `Submodule.mem_inf.1 hφ`. Use `Submodule.mem_inf.2 ⟨⟨fun u x => ?_, fun k g => ?_⟩, finVec_of_equiv heq hφ hK⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(T' φ).1 (unip u * x) = (T' φ).1 x`.

Rewrite using `[e φ hφ]`. Conclude with `ind_left H hI u x`. Express the relevant statement in the definitionally equal form `res (cf (r + s) k g) (T' φ).1 ∈ tens2 U₁' U₂'`. Rewrite using `[e φ hφ, ind_levi H hI k g]`. Conclude with `tensOp_maps hm₁ hm₂ (hI.2 k g)`.

Take `⟨hI, hK⟩` from `Submodule.mem_inf.1 hφ`. Establish `hz : ind g₁ g₂ φ.1 = 0`. Rewrite using `[← e φ hφ, h0]`. Both sides reduce to the same expression. Apply `Subtype.ext` to reduce the goal to its premises.

Use `ext_res hI.1 (fun _ _ => rfl) fun k g => ?_` and prove the remaining obligations. Establish `h2` using `ind_levi H hI k g`. Rewrite `h2` using `[hz]`. Establish `h1` using `tensOp_inj hn₁ hn₂ (hI.2 k g) (h2.symm.trans (map_zero _))`. Rewrite using `[h1]`.

Conclude with `(map_zero _).symm`.
-/
theorem emb_ind {U₁ U₁' : Submodule ℂ (Sm E r)} {U₂ U₂' : Submodule ℂ (Sm E s)} {g₁ : Sm E r →ₗ[ℂ] Sm E r}
    {g₂ : Sm E s →ₗ[ℂ] Sm E s} (hU₁ : IsStable U₁) (hU₂ : IsStable U₂) (hm₁ : ∀ ψ ∈ U₁, g₁ ψ ∈ U₁')
    (hm₂ : ∀ ψ ∈ U₂, g₂ ψ ∈ U₂') (hn₁ : ∀ ψ ∈ U₁, g₁ ψ = 0 → ψ = 0) (hn₂ : ∀ ψ ∈ U₂, g₂ ψ = 0 → ψ = 0)
    (he₁ : ∀ o, ∀ ψ ∈ U₁, g₁ (act o ψ) = act o (g₁ ψ)) (he₂ : ∀ o, ∀ ψ ∈ U₂, g₂ (act o ψ) = act o (g₂ ψ)) :
    Emb (indSub U₁ U₂ ⊓ finVec (cptRep E (r + s))) (· ∈ indSub U₁' U₂' ⊓ finVec (cptRep E (r + s))) := by
  have H : Good U₁ U₂ g₁ g₂ := ⟨hU₁, hU₂, he₁, he₂⟩
  have hV : IsStable (indSub U₁ U₂ ⊓ finVec (cptRep E (r + s))) := by
    have h := isStable_indFin hU₁ hU₂
    rwa [show {φ : Sm E (r + s) | MemInd2 U₁ U₂ φ ∧ φ ∈ finVec (cptRep E (r + s))} =
      ((indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) : Set (Sm E (r + s))) from
      Set.ext fun _ => Iff.rfl, Submodule.span_eq] at h
  let L : (indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) →ₗ[ℂ] Sm E (r + s) :=
    { toFun := fun φ => ⟨ind g₁ g₂ φ.1.1, ind_mem_Sm H (Submodule.mem_inf.1 φ.2).1 (Submodule.mem_inf.1 φ.2).2⟩
      map_add' := fun φ ψ => Subtype.ext (map_add (ind g₁ g₂) φ.1.1 ψ.1.1)
      map_smul' := fun c φ => Subtype.ext (map_smul (ind g₁ g₂) c φ.1.1) }
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend L
  have e : ∀ φ (hφ : φ ∈ indSub U₁ U₂ ⊓ finVec (cptRep E (r + s))), (T' φ).1 = ind g₁ g₂ φ.1 := fun φ hφ =>
    congrArg Subtype.val (LinearMap.congr_fun hT' ⟨φ, hφ⟩)
  have heq : ∀ o, ∀ φ ∈ indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)), T' (act o φ) = act o (T' φ) := by
    intro o φ hφ
    have ho := hV o φ hφ
    obtain ⟨hI, hK⟩ := Submodule.mem_inf.1 hφ
    apply Subtype.ext
    rw [e _ ho]
    cases o with
    | fin g =>
      rw [act_fin_val, act_fin_val, e _ hφ]
      funext x
      exact ind_rt H hI 1 g x
    | cpt k =>
      rw [act_cpt_val, act_cpt_val, e _ hφ]
      funext x
      exact ind_rt H hI k 1 x
    | lie X =>
      change ind g₁ g₂ (lie E (r + s) X φ).1 = lieD X (T' φ).1
      rw [e _ hφ]
      exact ind_lie H hI hK X (lie_mem_indSub hU₁ hU₂ hI hK X)
  refine ⟨T', fun φ hφ => ?_, fun φ hφ h0 => ?_, heq⟩
  · obtain ⟨hI, hK⟩ := Submodule.mem_inf.1 hφ
    refine Submodule.mem_inf.2 ⟨⟨fun u x => ?_, fun k g => ?_⟩, finVec_of_equiv heq hφ hK⟩
    · change (T' φ).1 (unip u * x) = (T' φ).1 x
      rw [e φ hφ]
      exact ind_left H hI u x
    · change res (cf (r + s) k g) (T' φ).1 ∈ tens2 U₁' U₂'
      rw [e φ hφ, ind_levi H hI k g]
      exact tensOp_maps hm₁ hm₂ (hI.2 k g)
  · obtain ⟨hI, hK⟩ := Submodule.mem_inf.1 hφ
    have hz : ind g₁ g₂ φ.1 = 0 := by
      rw [← e φ hφ, h0]
      rfl
    apply Subtype.ext
    refine ext_res hI.1 (fun _ _ => rfl) fun k g => ?_
    have h2 := ind_levi H hI k g
    rw [hz] at h2
    have h1 := tensOp_inj hn₁ hn₂ (hI.2 k g) (h2.symm.trans (map_zero _))
    rw [h1]
    exact (map_zero _).symm

/- English proof (translation)
Introduce `E _ _ _ r s t₁ t₁' t₂ t₂' hs₁ _ hs₂ _ h₁ h₂`. Take `⟨f₁, hf₁, hi₁, he₁⟩` from `h₁`. Take `⟨f₂, hf₂, hi₂, he₂⟩` from `h₂`. Rewrite using `[node_space, node_space]`. Conclude with `emb_ind (isStable_tw hs₁ _) (isStable_tw hs₂ _) (twMap_mem hf₁) (twMap_mem hf₂) (twMap_ne hi₁) (twMap_ne hi₂) (twMap_equiv hs₁ he₁) (twMap_equiv hs₂ he₂)`.
-/
theorem graft : Graft := by
  intro E _ _ _ r s t₁ t₁' t₂ t₂' hs₁ _ hs₂ _ h₁ h₂
  obtain ⟨f₁, hf₁, hi₁, he₁⟩ := h₁
  obtain ⟨f₂, hf₂, hi₂, he₂⟩ := h₂
  rw [node_space, node_space]
  exact emb_ind (isStable_tw hs₁ _) (isStable_tw hs₂ _) (twMap_mem hf₁) (twMap_mem hf₂) (twMap_ne hi₁)
    (twMap_ne hi₂) (twMap_equiv hs₁ he₁) (twMap_equiv hs₂ he₂)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

end
