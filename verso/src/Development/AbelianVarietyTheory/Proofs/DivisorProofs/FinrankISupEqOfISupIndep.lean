import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `stab : ∀ (s : Finset (I → ℂ)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y`. Introduce `s i`. Establish `: (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i)`. Use `iSup₂_le fun y hy v hv => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hV y v hv i]`.

Conclude with `Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)`. Conclude with `fun u hu => this hu`. Establish `key : ∀ (x : I → ℂ) (s : Finset (I → ℂ)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0`. Introduce `x s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => intro _ v _ hv`. Simplify using `using hv`. Consider the case `insert y s hy ih`. Introduce `hx v hvx hv`. Rewrite `hx` using `[Finset.mem_insert, not_or]`.

Rewrite `hv` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨w, hw, u, hu, hsum⟩` from `hv`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hx.1`. Establish `e : (x i - y i) • v = h i u - y i • u`. Rewrite using `[sub_smul, ← hV x v hvx i, ← hsum, map_add, hV y w hw i, smul_add]`.

Normalize the expressions using the abelian group laws. Establish `h0` using `ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx) (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))`. Conclude with `(smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)`. Introduce `x`. Rewrite using `[Submodule.disjoint_def]`.

Introduce `v hvx hv`. Use `replace hv : v ∈ ⨆ y : {y : I → ℂ // y ≠ x}, V y.1 := by rwa [iSup_subtype]`. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.mp hv`. Use `key x (s.image Subtype.val) ?_ v hvx ?_` and prove the remaining obligations. Introduce `hx`.

Take `⟨⟨y, hy⟩, -, e⟩` from `Finset.mem_image.mp hx`. Conclude with `hy e`. Use `(iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs` and prove the remaining obligations. Conclude with `le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1 (Finset.mem_image_of_mem _ hy) le_rfl`.
-/
theorem iSupIndep_of_joint_eigen {E I : Type} [AddCommGroup E] [Module ℂ E]
    (h : I → Module.End ℂ E) (V : (I → ℂ) → Submodule ℂ E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → ℂ)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → ℂ) (s : Finset (I → ℂ)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add, hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → ℂ // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

/- English proof (translation)
Rewrite using `[Submodule.iSup_eq_range_dfinsupp_lsum, Submodule.iSup_eq_range_dfinsupp_lsum]`. Establish `e : ∀ x, V x ≃ₗ[ℂ] V' x` using `fun x => LinearEquiv.ofFinrankEq _ _ (hd x)`. Conclude with `(((LinearEquiv.ofInjective _ hV.dfinsupp_lsum_injective).symm.trans (DFinsupp.mapRange.linearEquiv e)).trans (LinearEquiv.ofInjective _ hV'.dfinsupp_lsum_injective)).finrank_eq`.
-/
theorem finrank_iSup_eq_of_iSupIndep {E W X : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (V : X → Submodule ℂ E) (V' : X → Submodule ℂ W) (hV : iSupIndep V) (hV' : iSupIndep V')
    (hd : ∀ x, Module.finrank ℂ (V x) = Module.finrank ℂ (V' x)) :
    Module.finrank ℂ (⨆ x, V x : Submodule ℂ E) = Module.finrank ℂ (⨆ x, V' x : Submodule ℂ W) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, Submodule.iSup_eq_range_dfinsupp_lsum]
  have e : ∀ x, V x ≃ₗ[ℂ] V' x := fun x => LinearEquiv.ofFinrankEq _ _ (hd x)
  exact (((LinearEquiv.ofInjective _ hV.dfinsupp_lsum_injective).symm.trans
    (DFinsupp.mapRange.linearEquiv e)).trans
      (LinearEquiv.ofInjective _ hV'.dfinsupp_lsum_injective)).finrank_eq

/- English proof (translation)
Introduce `E W I C _ _ _ _ _ _ h h' U U' lab hU hU' hlab hd S`. Establish `re : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F), (⨆ (c : C) (_ : S c), A c) = ⨆ (x : I → ℂ), ⨆ (c : C) (_ : S c ∧ lab c = x), A c`. Introduce `F _ _ A`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup₂_le fun c hc => le_iSup_of_le (lab c) ?_` and prove the remaining obligations.

Conclude with `le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl`. Conclude with `iSup_le fun x => iSup₂_le fun c hc => le_iSup₂_of_le (f := fun c' (_ : S c') => A c') c hc.1 le_rfl`. Establish `one : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F), (∀ c c', lab c = lab c' → A c = A c') → ∀ c, S c → (⨆ (c' : C) (_ : S c' ∧ lab c' = lab c), A c') = A c`. Introduce `F _ _ A hA c hc`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `iSup₂_le fun c' hc' => (hA c' c hc'.2).le`. Conclude with `le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl`. Establish `none : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F) (x : I → ℂ), (¬ ∃ c, S c ∧ lab c = x) → (⨆ (c' : C) (_ : S c' ∧ lab c' = x), A c') = ⊥`. Introduce `F _ _ A x hx`. Conclude with `le_bot_iff.mp (iSup₂_le fun c hc => (hx ⟨c, hc⟩).elim)`.

Establish `ind : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (g : I → Module.End ℂ F) (A : C → Submodule ℂ F), (∀ c c', lab c = lab c' → A c = A c') → (∀ c, ∀ x ∈ A c, ∀ i, g i x = lab c i • x) → iSupIndep fun x : I → ℂ => ⨆ (c : C) (_ : S c ∧ lab c = x), A c`. Introduce `F _ _ g A hA hg`. Use `iSupIndep_of_joint_eigen g _ fun x v hv i => ?_` and prove the remaining obligations. Distinguish the cases in `hx : ∃ c, S c ∧ lab c = x`. Take `⟨c, hc, rfl⟩` from `hx`.

Rewrite `hv` using `[one A hA c hc]`. Conclude with `hg c v hv i`. Rewrite `hv` using `[none A x hx, Submodule.mem_bot]`. Simplify using `[hv]`. Rewrite using `[re U, re U']`.

Use `finrank_iSup_eq_of_iSupIndep _ _ (ind h U (fun c c' e => (hlab c c' e).1) hU) (ind h' U' (fun c c' e => (hlab c c' e).2) hU') fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : ∃ c, S c ∧ lab c = x`. Take `⟨c, hc, rfl⟩` from `hx`. Rewrite using `[one U (fun c c' e => (hlab c c' e).1) c hc, one U' (fun c c' e => (hlab c c' e).2) c hc]`. Conclude with `hd c`.

Rewrite using `[none U x hx, none U' x hx]`. Simplify using the standard rewrite rules.
-/
theorem finrank_iSup_joint_eigen_eq : ∀ {E W I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (h : I → Module.End ℂ E) (h' : I → Module.End ℂ W) (U : C → Submodule ℂ E) (U' : C → Submodule ℂ W) (lab : C → I → ℂ), (∀ c, ∀ x ∈ U c, ∀ i, h i x = lab c i • x) → (∀ c, ∀ x ∈ U' c, ∀ i, h' i x = lab c i • x) → (∀ c c', lab c = lab c' → U c = U c' ∧ U' c = U' c') → (∀ c, Module.finrank ℂ (U c) = Module.finrank ℂ (U' c)) → ∀ S : C → Prop, Module.finrank ℂ (⨆ (c : C) (_ : S c), U c : Submodule ℂ E) = Module.finrank ℂ (⨆ (c : C) (_ : S c), U' c : Submodule ℂ W) := by
  intro E W I C _ _ _ _ _ _ h h' U U' lab hU hU' hlab hd S
  have re : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (⨆ (c : C) (_ : S c), A c) = ⨆ (x : I → ℂ), ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ A
    apply le_antisymm
    · refine iSup₂_le fun c hc => le_iSup_of_le (lab c) ?_
      exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
    · exact iSup_le fun x => iSup₂_le fun c hc =>
        le_iSup₂_of_le (f := fun c' (_ : S c') => A c') c hc.1 le_rfl
  have one : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (∀ c c', lab c = lab c' → A c = A c') → ∀ c, S c →
      (⨆ (c' : C) (_ : S c' ∧ lab c' = lab c), A c') = A c := by
    intro F _ _ A hA c hc
    apply le_antisymm
    · exact iSup₂_le fun c' hc' => (hA c' c hc'.2).le
    · exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
  have none : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F) (x : I → ℂ),
      (¬ ∃ c, S c ∧ lab c = x) → (⨆ (c' : C) (_ : S c' ∧ lab c' = x), A c') = ⊥ := by
    intro F _ _ A x hx
    exact le_bot_iff.mp (iSup₂_le fun c hc => (hx ⟨c, hc⟩).elim)
  have ind : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (g : I → Module.End ℂ F)
      (A : C → Submodule ℂ F), (∀ c c', lab c = lab c' → A c = A c') →
      (∀ c, ∀ x ∈ A c, ∀ i, g i x = lab c i • x) →
      iSupIndep fun x : I → ℂ => ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ g A hA hg
    refine iSupIndep_of_joint_eigen g _ fun x v hv i => ?_
    by_cases hx : ∃ c, S c ∧ lab c = x
    · obtain ⟨c, hc, rfl⟩ := hx
      rw [one A hA c hc] at hv
      exact hg c v hv i
    · rw [none A x hx, Submodule.mem_bot] at hv
      simp [hv]
  rw [re U, re U']
  refine finrank_iSup_eq_of_iSupIndep _ _ (ind h U (fun c c' e => (hlab c c' e).1) hU)
    (ind h' U' (fun c c' e => (hlab c c' e).2) hU') fun x => ?_
  by_cases hx : ∃ c, S c ∧ lab c = x
  · obtain ⟨c, hc, rfl⟩ := hx
    rw [one U (fun c c' e => (hlab c c' e).1) c hc, one U' (fun c c' e => (hlab c c' e).2) c hc]
    exact hd c
  · rw [none U x hx, none U' x hx]
    simp

end GlobalTheory
