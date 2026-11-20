import Mathlib
open scoped BigOperators

/- English proof (translation)
Establish `hb` using `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := S) ℂ`. Set `f : Module.End (Module.End A S) S` to `{ toFun := t map_add' := t.map_add map_smul' := by`. Introduce `d m`. Take `⟨c, rfl⟩` from `hb.2 d`. Simplify using `[Module.algebraMap_end_apply] }`.

Set `b` to `Module.finBasis ℂ S`. Take `⟨a, ha⟩` from `jacobson_density f (Finset.univ.image b)`. Use `⟨a, fun m => ?_⟩` and prove the remaining obligations. Set `u : Module.End ℂ S` to `Module.toModuleEnd ℂ (S := A) S a`. Establish `: t = u`.

Use `b.ext fun i => ?_` and prove the remaining obligations. Conclude with `ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
private theorem burnside_endomorphism {S A : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    [Ring A] [Algebra ℂ A] [Module A S] [IsScalarTower ℂ A S] [IsSimpleModule A S]
    (t : Module.End ℂ S) : ∃ a : A, ∀ m : S, t m = a • m := by
  classical
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := S) ℂ
  let f : Module.End (Module.End A S) S :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := by
        intro d m
        obtain ⟨c, rfl⟩ := hb.2 d
        simp [Module.algebraMap_end_apply] }
  let b := Module.finBasis ℂ S
  obtain ⟨a, ha⟩ := jacobson_density f (Finset.univ.image b)
  refine ⟨a, fun m => ?_⟩
  let u : Module.End ℂ S := Module.toModuleEnd ℂ (S := A) S a
  have : t = u := by
    refine b.ext fun i => ?_
    exact ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; rfl

/- English proof (translation)
Establish `hs : IsSimpleModule R S`. Rewrite using `[isSimpleModule_iff]`. Use `{ eq_bot_or_eq_top := fun N => ?_ }` and prove the remaining obligations. Distinguish the cases in `hN : N = ⊥`. Conclude with `Or.inl hN`.

Use `right`. Take `⟨x, hxN, hx⟩` from `N.exists_mem_ne_zero_of_ne_bot hN`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `hy : y ∈ Submodule.span ℂ {y | ∃ r ∈ R, y = r x}` using `by rw [h x hx]; trivial`.

Establish `hle : Submodule.span ℂ {y | ∃ r ∈ R, y = r x} ≤ N.restrictScalars ℂ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, rfl⟩`. Conclude with `N.smul_mem (⟨r, hr⟩ : R) hxN`. Conclude with `hle hy`.

Rewrite using `[eq_top_iff]`. Introduce `t _`. Take `⟨a, ha⟩` from `burnside_endomorphism (A := R) t`. Establish `: t = (a : Module.End ℂ S)` using `LinearMap.ext ha`. Rewrite using `[this]`.

Conclude with `a.2`.
-/
private theorem burn_sub {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    [Nontrivial S] (R : Subalgebra ℂ (Module.End ℂ S))
    (h : ∀ x : S, x ≠ 0 → Submodule.span ℂ {y | ∃ r ∈ R, y = r x} = ⊤) : R = ⊤ := by
  have hs : IsSimpleModule R S := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    by_cases hN : N = ⊥
    · exact Or.inl hN
    right
    obtain ⟨x, hxN, hx⟩ := N.exists_mem_ne_zero_of_ne_bot hN
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span ℂ {y | ∃ r ∈ R, y = r x} := by rw [h x hx]; trivial
    have hle : Submodule.span ℂ {y | ∃ r ∈ R, y = r x} ≤ N.restrictScalars ℂ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨r, hr, rfl⟩
      exact N.smul_mem (⟨r, hr⟩ : R) hxN
    exact hle hy
  rw [eq_top_iff]
  intro t _
  obtain ⟨a, ha⟩ := burnside_endomorphism (A := R) t
  have : t = (a : Module.End ℂ S) := LinearMap.ext ha
  rw [this]; exact a.2

/- English proof (translation)
Introduce `S X _ _ _ _ _ _ _ M P hM hP hirr`. Set `Q : Subalgebra ℂ (Module.End ℂ S × Module.End ℂ X)` to `Algebra.adjoin ℂ P`. Set `π₁ : (Module.End ℂ S × Module.End ℂ X) →ₐ[ℂ] Module.End ℂ S` to `AlgHom.fst ℂ _ _`. Set `π₂ : (Module.End ℂ S × Module.End ℂ X) →ₐ[ℂ] Module.End ℂ X` to `AlgHom.snd ℂ _ _`. Establish `hcomm : ∀ q ∈ Q, ∀ f ∈ M, q.2 ∘ₗ f = f ∘ₗ q.1`.

Introduce `q hq f hf`. Proceed by induction on `hq using Algebra.adjoin_induction with`. Consider the case `mem p hp => exact hP p hp f hf`. Consider the case `algebraMap r`. Use extensionality with `x`.

Simplify using `[Module.algebraMap_end_apply]`. Consider the case `add a b _ _ ha hb`. Use extensionality with `x`. Establish `h1` using `LinearMap.congr_fun ha x`. Establish `h2` using `LinearMap.congr_fun hb x`.

Simplify using `only [LinearMap.comp_apply] at h1 h2`. Simplify using `[h1, h2]`. Consider the case `mul a b _ _ ha hb`. Use extensionality with `x`. Establish `h2` using `LinearMap.congr_fun hb x`.

Establish `h1` using `LinearMap.congr_fun ha (b.1 x)`. Simplify using `only [LinearMap.comp_apply] at h1 h2`. Simplify using `[Module.End.mul_apply, h1, h2]`. Set `φ : Q →ₐ[ℂ] Module.End ℂ S` to `π₁.comp Q.val`. Set `ψ : Q →ₐ[ℂ] Module.End ℂ X` to `π₂.comp Q.val`.

Establish `hinj : Function.Injective φ`. Use `(injective_iff_map_eq_zero φ).2 fun q hq => ?_` and prove the remaining obligations. Establish `h1 : (q : Module.End ℂ S × Module.End ℂ X).1 = 0` using `hq`. Establish `h2 : (q : Module.End ℂ S × Module.End ℂ X).2 = 0`. Rewrite using `[← LinearMap.ker_eq_top, eq_top_iff, ← hM]`.

Use `iSup₂_le fun f hf => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Use `LinearMap.congr_fun (hcomm q q.2 f hf) x` as an intermediate fact. Simplify `this` using `[h1]`. Conclude with `Subtype.ext (Prod.ext h1 h2)`.

Establish `hmap₁ : Q.map π₁ = Algebra.adjoin ℂ (Prod.fst '' P)` using `AlgHom.map_adjoin π₁ P`. Establish `hmap₂ : Q.map π₂ = Algebra.adjoin ℂ (Prod.snd '' P)` using `AlgHom.map_adjoin π₂ P`. Establish `htop : Q.map π₁ = ⊤`. Use `burn_sub _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hirr x hx]`.

Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `⟨p.1, hmap₁ ▸ Algebra.subset_adjoin ⟨p, hp, rfl⟩, rfl⟩`. Establish `hsurj : Function.Surjective φ`. Introduce `t`.

Establish `ht : t ∈ Q.map π₁` using `by rw [htop]; trivial`. Take `⟨q, hq, rfl⟩` from `ht`. Conclude with `⟨⟨q, hq⟩, rfl⟩`. Set `e : Q ≃ₐ[ℂ] Module.End ℂ S` to `AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩`. Establish `he : ∀ t, ((e.symm t : Q) : Module.End ℂ S × Module.End ℂ X).1 = t` using `fun t => e.apply_symm_apply t`.

Use `⟨ψ.comp (e.symm : Module.End ℂ S →ₐ[ℂ] Q), fun t f hf => ?_, fun t => ?_⟩` and prove the remaining obligations. Use `hcomm _ (e.symm t).2 f hf` as an intermediate fact. Rewrite `this` using `[he t]`. Conclude with `this`. Rewrite using `[← hmap₂]`.

Conclude with `⟨_, (e.symm t).2, rfl⟩`.
-/
theorem UpperTheory.exists_algHom_end_intertwining_mem_adjoin :
    ∀ (S X : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ S] [FiniteDimensional ℂ X] [Nontrivial S] (M : Set (S →ₗ[ℂ] X)) (P : Set (Module.End ℂ S × Module.End ℂ X)), (⨆ f ∈ M, LinearMap.range f) = ⊤ → (∀ p ∈ P, ∀ f ∈ M, p.2 ∘ₗ f = f ∘ₗ p.1) → (∀ x : S, x ≠ 0 → Submodule.span ℂ {y | ∃ p ∈ P, y = p.1 x} = ⊤) → ∃ c : Module.End ℂ S →ₐ[ℂ] Module.End ℂ X, (∀ t, ∀ f ∈ M, c t ∘ₗ f = f ∘ₗ t) ∧ ∀ t, c t ∈ Algebra.adjoin ℂ (Prod.snd '' P) := by
  intro S X _ _ _ _ _ _ _ M P hM hP hirr
  let Q : Subalgebra ℂ (Module.End ℂ S × Module.End ℂ X) := Algebra.adjoin ℂ P
  let π₁ : (Module.End ℂ S × Module.End ℂ X) →ₐ[ℂ] Module.End ℂ S := AlgHom.fst ℂ _ _
  let π₂ : (Module.End ℂ S × Module.End ℂ X) →ₐ[ℂ] Module.End ℂ X := AlgHom.snd ℂ _ _
  have hcomm : ∀ q ∈ Q, ∀ f ∈ M, q.2 ∘ₗ f = f ∘ₗ q.1 := by
    intro q hq f hf
    induction hq using Algebra.adjoin_induction with
    | mem p hp => exact hP p hp f hf
    | algebraMap r =>
      ext x
      simp [Module.algebraMap_end_apply]
    | add a b _ _ ha hb =>
      ext x
      have h1 := LinearMap.congr_fun ha x
      have h2 := LinearMap.congr_fun hb x
      simp only [LinearMap.comp_apply] at h1 h2
      simp [h1, h2]
    | mul a b _ _ ha hb =>
      ext x
      have h2 := LinearMap.congr_fun hb x
      have h1 := LinearMap.congr_fun ha (b.1 x)
      simp only [LinearMap.comp_apply] at h1 h2
      simp [Module.End.mul_apply, h1, h2]
  let φ : Q →ₐ[ℂ] Module.End ℂ S := π₁.comp Q.val
  let ψ : Q →ₐ[ℂ] Module.End ℂ X := π₂.comp Q.val
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun q hq => ?_
    have h1 : (q : Module.End ℂ S × Module.End ℂ X).1 = 0 := hq
    have h2 : (q : Module.End ℂ S × Module.End ℂ X).2 = 0 := by
      rw [← LinearMap.ker_eq_top, eq_top_iff, ← hM]
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨x, rfl⟩
      have := LinearMap.congr_fun (hcomm q q.2 f hf) x
      simpa [h1] using this
    exact Subtype.ext (Prod.ext h1 h2)
  have hmap₁ : Q.map π₁ = Algebra.adjoin ℂ (Prod.fst '' P) := AlgHom.map_adjoin π₁ P
  have hmap₂ : Q.map π₂ = Algebra.adjoin ℂ (Prod.snd '' P) := AlgHom.map_adjoin π₂ P
  have htop : Q.map π₁ = ⊤ := by
    refine burn_sub _ fun x hx => ?_
    rw [eq_top_iff, ← hirr x hx]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.1, hmap₁ ▸ Algebra.subset_adjoin ⟨p, hp, rfl⟩, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro t
    have ht : t ∈ Q.map π₁ := by rw [htop]; trivial
    obtain ⟨q, hq, rfl⟩ := ht
    exact ⟨⟨q, hq⟩, rfl⟩
  let e : Q ≃ₐ[ℂ] Module.End ℂ S := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ t, ((e.symm t : Q) : Module.End ℂ S × Module.End ℂ X).1 = t := fun t => e.apply_symm_apply t
  refine ⟨ψ.comp (e.symm : Module.End ℂ S →ₐ[ℂ] Q), fun t f hf => ?_, fun t => ?_⟩
  · have := hcomm _ (e.symm t).2 f hf
    rw [he t] at this
    exact this
  · rw [← hmap₂]
    exact ⟨_, (e.symm t).2, rfl⟩
