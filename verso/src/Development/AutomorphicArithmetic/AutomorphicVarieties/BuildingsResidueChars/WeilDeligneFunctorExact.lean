import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

open TensorProduct Module GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
/- English proof (translation)
Introduce `LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj`. Establish `hS' : Function.Surjective (S.baseChange F)` using `LinearMap.lTensor_surjective F hsurj`. Establish `hex' : Function.Exact (T.baseChange F) (S.baseChange F)` using `lTensor_exact F hex hsurj`. Establish `eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y)` using `fun _ => rfl`. Establish `eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y)` using `fun _ => rfl`.

Establish `hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F)` using `iSup_le fun c => by`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨y, rfl⟩` from `hS' y`. Use `⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y` as an intermediate fact.

Rewrite `this` using `[LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply]`. Simplify using `[this]`. Use `⟨fun y => ?_, fun y => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `letterQ_surjective m F τ y`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `h` using `[eS, ← LinearMap.mem_ker, ker_letterQ]`. Take `⟨z, hz, hzy⟩` from `hker h`. Take `⟨w, hw⟩` from `(hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])`. Use `⟨letterQ m' F τ w, ?_⟩` and prove the remaining obligations.

Establish `hz0 : letterQ m F τ z = 0`. Rewrite using `[← LinearMap.mem_ker, ker_letterQ]`. Conclude with `hz`. Rewrite using `[eT, hw, map_sub, hz0, sub_zero]`. Introduce and unpack `⟨w, hw⟩`.

Take `⟨w, rfl⟩` from `letterQ_surjective m' F τ w`. Rewrite using `[← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]`. Take `⟨y, rfl⟩` from `letterQ_surjective m'' F τ y`. Take `⟨y, rfl⟩` from `hS' y`. Conclude with `⟨letterQ m F τ y, eS y⟩`.
-/
theorem UpperTheory.weilDeligne_functor_exact :
    UpperTheory.V.Af.Wd.LetterExact := by
  intro LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj
  have hS' : Function.Surjective (S.baseChange F) := LinearMap.lTensor_surjective F hsurj
  have hex' : Function.Exact (T.baseChange F) (S.baseChange F) := lTensor_exact F hex hsurj
  have eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y) := fun _ => rfl
  have eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y) := fun _ => rfl
  have hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hS' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := letterQ_surjective m F τ y
    constructor
    · intro h
      rw [eS, ← LinearMap.mem_ker, ker_letterQ] at h
      obtain ⟨z, hz, hzy⟩ := hker h
      obtain ⟨w, hw⟩ := (hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])
      refine ⟨letterQ m' F τ w, ?_⟩
      have hz0 : letterQ m F τ z = 0 := by
        rw [← LinearMap.mem_ker, ker_letterQ]; exact hz
      rw [eT, hw, map_sub, hz0, sub_zero]
    · rintro ⟨w, hw⟩
      obtain ⟨w, rfl⟩ := letterQ_surjective m' F τ w
      rw [← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]
  · obtain ⟨y, rfl⟩ := letterQ_surjective m'' F τ y
    obtain ⟨y, rfl⟩ := hS' y
    exact ⟨letterQ m F τ y, eS y⟩
