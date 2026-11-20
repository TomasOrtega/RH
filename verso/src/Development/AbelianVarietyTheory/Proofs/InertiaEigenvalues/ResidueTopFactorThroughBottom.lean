import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ r t U a ha g hg`. Set `res : (Fin r ⊕ Fin t → O) → (Fin r ⊕ Fin t → IsLocalRing.ResidueField O)` to `fun u j => IsLocalRing.residue O (u j)`. Set `Wsp : Submodule (IsLocalRing.ResidueField O) (Fin r ⊕ Fin t → IsLocalRing.ResidueField O)` to `{ carrier := {w | ∃ u ∈ U, res u = w} add_mem' := by`. Introduce and unpack `_ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩`. Conclude with `⟨u + v, U.add_mem hu hv, by ext j; simp [res]⟩`.

Use the proof step `zero_mem' := ⟨0, U.zero_mem, by ext j; simp [res]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨u, hu, rfl⟩`. Take `⟨o, rfl⟩` from `IsLocalRing.residue_surjective c`. Conclude with `⟨o • u, U.smul_mem o hu, by ext j; simp [res]⟩ }`.

Set `top : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O)` to `LinearMap.funLeft _ _ Sum.inl`. Set `bot : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O)` to `LinearMap.funLeft _ _ Sum.inr`. Set `π : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O)` to `bot.comp Wsp.subtype`. Set `f : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O)` to `(LinearMap.id - Matrix.toLin' g).comp (top.comp Wsp.subtype)`. Establish `hker : LinearMap.ker π ≤ LinearMap.ker f`.

Introduce and unpack `⟨w, u, hu, rfl⟩ hw`. Rewrite `hw`, the goal using `[LinearMap.mem_ker]`. Establish `h2 : ∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0` using `fun i => congrFun hw i`. Establish `h3` using `hg _ (ha u hu h2)`. Simplify using `only [f, top, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.id_apply, Matrix.toLin'_apply]`.

Rewrite using `[sub_eq_zero]`. Conclude with `h3.symm`. Set `b₀ : LinearMap.range π →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O)` to `((LinearMap.ker π).liftQ f hker).comp (π.quotKerEquivRange.symm.toLinearMap)`. Take `⟨B, hB⟩` from `LinearMap.exists_extend b₀`. Use `⟨LinearMap.toMatrix' B, ?_⟩` and prove the remaining obligations.

Introduce `u hu`. Establish `hw : res u ∈ Wsp` using `⟨u, hu, rfl⟩`. Establish `key : B (π ⟨res u, hw⟩) = f ⟨res u, hw⟩`. Establish `h1` using `LinearMap.congr_fun hB ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at h1`.

Rewrite using `[h1]`. Use `show (LinearMap.ker π).liftQ f hker (π.quotKerEquivRange.symm ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩) = _`. Rewrite using `[LinearMap.quotKerEquivRange_symm_apply_image]`. Both sides reduce to the same expression. Establish `e : π ⟨res u, hw⟩ = fun i => IsLocalRing.residue O (u (Sum.inr i))` using `rfl`.

Establish `e2 : f ⟨res u, hw⟩ = (fun i => IsLocalRing.residue O (u (Sum.inl i))) - g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i)))` using `rfl`. Rewrite `key` using `[e, e2]`. Rewrite using `[LinearMap.toMatrix'_mulVec, key]`. Normalize the expressions using the abelian group laws.
-/
theorem residue_top_factor_through_bottom : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (U : Submodule O (Fin r ⊕ Fin t → O)) (a : Fin r → IsLocalRing.ResidueField O), (∀ u ∈ U, (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0) → ∀ g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → g.mulVec v = v) → ∃ b : Matrix (Fin r) (Fin t) (IsLocalRing.ResidueField O), ∀ u ∈ U, g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) + b.mulVec (fun i => IsLocalRing.residue O (u (Sum.inr i))) = (fun i => IsLocalRing.residue O (u (Sum.inl i))) := by
  intro O _ _ r t U a ha g hg
  let res : (Fin r ⊕ Fin t → O) → (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    fun u j => IsLocalRing.residue O (u j)
  let Wsp : Submodule (IsLocalRing.ResidueField O) (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    { carrier := {w | ∃ u ∈ U, res u = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, U.add_mem hu hv, by ext j; simp [res]⟩
      zero_mem' := ⟨0, U.zero_mem, by ext j; simp [res]⟩
      smul_mem' := by
        rintro c _ ⟨u, hu, rfl⟩
        obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨o • u, U.smul_mem o hu, by ext j; simp [res]⟩ }
  let top : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inl
  let bot : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inr
  let π : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) := bot.comp Wsp.subtype
  let f : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    (LinearMap.id - Matrix.toLin' g).comp (top.comp Wsp.subtype)
  have hker : LinearMap.ker π ≤ LinearMap.ker f := by
    rintro ⟨w, u, hu, rfl⟩ hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h2 : ∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0 := fun i => congrFun hw i
    have h3 := hg _ (ha u hu h2)
    simp only [f, top, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Matrix.toLin'_apply]
    rw [sub_eq_zero]
    exact h3.symm
  let b₀ : LinearMap.range π →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    ((LinearMap.ker π).liftQ f hker).comp (π.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨B, hB⟩ := LinearMap.exists_extend b₀
  refine ⟨LinearMap.toMatrix' B, ?_⟩
  intro u hu
  have hw : res u ∈ Wsp := ⟨u, hu, rfl⟩
  have key : B (π ⟨res u, hw⟩) = f ⟨res u, hw⟩ := by
    have h1 := LinearMap.congr_fun hB ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    show (LinearMap.ker π).liftQ f hker
      (π.quotKerEquivRange.symm ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have e : π ⟨res u, hw⟩ = fun i => IsLocalRing.residue O (u (Sum.inr i)) := rfl
  have e2 : f ⟨res u, hw⟩ = (fun i => IsLocalRing.residue O (u (Sum.inl i))) -
      g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) := rfl
  rw [e, e2] at key
  rw [LinearMap.toMatrix'_mulVec, key]
  abel

end GlobalTheory
