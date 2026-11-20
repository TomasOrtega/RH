import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open scoped TensorProduct
open GlobalTheory.EigenSplit

namespace GlobalTheory.EigenLine

variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]

/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem action_one_tmul (ρ : O →+* Module.End K L) (a : O) :
    tensorAction ρ ((1 : K) ⊗ₜ[ℤ] a) = ρ a := by
  ext x
  simp

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `tmul r a => intro x hx`. Rewrite using `[tensorAction_tmul]`.

Conclude with `P.smul_mem _ (hP a x hx)`. Consider the case `add s t hs ht`. Introduce `x hx`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `P.add_mem (hs x hx) (ht x hx)`.
-/
theorem action_mem (ρ : O →+* Module.End K L) (P : Submodule K L)
    (hP : ∀ a, ∀ x ∈ P, ρ a x ∈ P) (t : K ⊗[ℤ] O) : ∀ x ∈ P, tensorAction ρ t x ∈ P := by
  induction t using TensorProduct.induction_on with
  | zero => intro x _; simp
  | tmul r a => intro x hx; rw [tensorAction_tmul]; exact P.smul_mem _ (hP a x hx)
  | add s t hs ht =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact P.add_mem (hs x hx) (ht x hx)

/- English proof (translation)
Establish `h` using `congrArg (fun t => tensorAction ρ t x) (hε a)`. Simplify `h` using `only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul, LinearMap.smul_apply]`.
-/
theorem action_eigen_right (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    tensorAction ρ ε (ρ a x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) (hε a)
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h

/- English proof (translation)
Establish `h` using `congrArg (fun t => tensorAction ρ t x) ((mul_comm _ _).trans (hε a))`. Simplify `h` using `only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul, LinearMap.smul_apply]`.
-/
theorem action_eigen_left (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    ρ a (tensorAction ρ ε x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) ((mul_comm _ _).trans (hε a))
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h

noncomputable def twist (c : O →+* O) : K ⊗[ℤ] O →ₐ[ℤ] K ⊗[ℤ] O :=
  Algebra.TensorProduct.map (AlgHom.id ℤ K) c.toIntAlgHom

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r a => simp [twist, hcc]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`.
-/
theorem twist_twist (c : O →+* O) (hcc : ∀ a, c (c a) = a) (t : K ⊗[ℤ] O) :
    twist c (twist c t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hcc]
  | add s t hs ht => simp only [map_add, hs, ht]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r a => simp [twist, hadj]`. Consider the case `add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]`.
-/
theorem form_action (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y) (t : K ⊗[ℤ] O) (x y : L) :
    B x (tensorAction ρ t y) = B (tensorAction ρ (twist c t) x) y := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hadj]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, f y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hf (LinearMap.ext h)`. Establish `htop : LinearMap.range f = ⊤`.

Use `LinearMap.range_eq_top.2 fun k => ⟨(k / f y) • y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]`. Establish `h` using `LinearMap.finrank_range_add_finrank_ker f`. Rewrite `h` using `[htop, finrank_top, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_ker_add_one {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) :
    Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  have htop : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.2 fun k => ⟨(k / f y) • y, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, finrank_top, Module.finrank_self] at h
  omega

/- English proof (translation)
Use `set T := tensorAction ρ ε with hT`. Use `set E := LinearMap.range T with hE`. Establish `hn₀ : n₀ ∈ M`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span ⟨1, by simp⟩`.

Establish `hTn : T n₀ ≠ 0` using `fun h => hε0 (hinj ε h)`. Establish `hTM : ∀ m ∈ M, T m ∈ K ∙ T n₀`. Introduce `m hm`. Rewrite `hm` using `[hspan]`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Establish `: T (ρ a n₀) = χ a • T n₀` using `action_eigen_right ρ χ ε hε a n₀`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.

Establish `hline : M ⊓ E = K ∙ T n₀`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hxM, z, rfl⟩`. Establish `hz : z ∈ M ⊔ M'` using `by rw [hMM.sup_eq_top]; trivial`. Take `⟨m, hm, m', hm', rfl⟩` from `Submodule.mem_sup.1 hz`.

Establish `h1 : T m' ∈ M'` using `action_mem ρ M' hM' ε m' hm'`. Establish `h2 : T m ∈ M` using `action_mem ρ M hM ε m hm`. Establish `h3 : T m' ∈ M`. Establish `: T m' = T (m + m') - T m` using `by rw [map_add]; abel`. Rewrite using `[this]`.

Conclude with `M.sub_mem hxM h2`. Establish `h4 : T m' = 0`. Establish `: T m' ∈ M ⊓ M'` using `⟨h3, h1⟩`. Rewrite `this` using `[hMM.inf_eq_bot, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[map_add, h4, add_zero]`.

Conclude with `hTM m hm`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `⟨action_mem ρ M hM ε n₀ hn₀, n₀, rfl⟩`. Use `⟨by rw [hline]; exact finrank_span_singleton hTn, ?_⟩` and prove the remaining obligations. Set `f : E →ₗ[K] K` to `(B n₀).comp E.subtype`.

Establish `hf : f ≠ 0`. Establish `h1 : twist c ε ≠ 0`. Introduce `h`. Apply `hε0` to reduce the goal to its premises. Rewrite using `[← twist_twist c hcc ε, h, map_zero]`.

Establish `h2 : tensorAction ρ (twist c ε) n₀ ≠ 0` using `fun h => h1 (hinj _ h)`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, B (tensorAction ρ (twist c ε) n₀) z ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `h2 (hnd _ h)`.

Introduce `h0`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← form_action ρ c B hadj]`. Conclude with `LinearMap.congr_fun h0 ⟨T z, z, rfl⟩`. Establish `hmap : (LinearMap.ker f).map E.subtype = B.orthogonal M ⊓ E`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, hy⟩, hyk, rfl⟩`. Use `⟨?_, hy⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y ∈ B.orthogonal M`.

Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff]`. Introduce `n hn`. Establish `hy0 : B n₀ y = 0` using `hyk`. Rewrite `hn` using `[hspan]`. Proceed by induction on `hn using Submodule.span_induction with`.

Consider the case `mem n hn`. Take `⟨a, rfl⟩` from `hn`. Take `⟨z, rfl⟩` from `hy`. Establish `h1` using `hadj (c a) n₀ (T z)`. Rewrite `h1` using `[hcc]`.

Use `show B (ρ a n₀) (T z) = 0`. Rewrite using `[← h1, action_eigen_left ρ χ ε hε, map_smul, hy0, smul_zero]`. Consider the case `zero => simp [LinearMap.BilinForm.IsOrtho]`. Consider the case `add u v _ _ hu hv`. Simplify using `only [LinearMap.BilinForm.IsOrtho, map_add, LinearMap.add_apply] at *`.

Rewrite using `[hu, hv, add_zero]`. Consider the case `smul r u _ hu`. Simplify using `only [LinearMap.BilinForm.IsOrtho, map_smul, LinearMap.smul_apply] at *`. Rewrite using `[hu, smul_zero]`. Introduce and unpack `⟨hx, hxE⟩`.

Use `⟨⟨x, hxE⟩, ?_, rfl⟩` and prove the remaining obligations. Establish `hx' : x ∈ B.orthogonal M` using `hx`. Rewrite `hx'` using `[LinearMap.BilinForm.mem_orthogonal_iff]`. Conclude with `hx' n₀ hn₀`. Rewrite using `[← hmap, Submodule.finrank_map_subtype_eq]`.

Conclude with `finrank_ker_add_one f hf`.
-/
theorem line_hyperplane_cut (K : Type) [Field K] (O : Type) [CommRing O] (L : Type)
    [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (χ : O →+* K) (ε : K ⊗[ℤ] O) (M M' : Submodule K L) (n₀ : L)
    (hcc : ∀ a, c (c a) = a) (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (hε0 : ε ≠ 0) (hMM : IsCompl M M')
    (hM : ∀ a, ∀ x ∈ M, ρ a x ∈ M) (hM' : ∀ a, ∀ x ∈ M', ρ a x ∈ M')
    (hspan : M = Submodule.span K (Set.range fun a => ρ a n₀))
    (hinj : ∀ t : K ⊗[ℤ] O, tensorAction ρ t n₀ = 0 → t = 0) :
    Module.finrank K ↥(M ⊓ LinearMap.range (tensorAction ρ ε)) = 1 ∧
    Module.finrank K ↥(B.orthogonal M ⊓ LinearMap.range (tensorAction ρ ε)) + 1 =
      Module.finrank K ↥(LinearMap.range (tensorAction ρ ε)) := by
  set T := tensorAction ρ ε with hT
  set E := LinearMap.range T with hE
  have hn₀ : n₀ ∈ M := by
    rw [hspan]
    exact Submodule.subset_span ⟨1, by simp⟩
  have hTn : T n₀ ≠ 0 := fun h => hε0 (hinj ε h)

  have hTM : ∀ m ∈ M, T m ∈ K ∙ T n₀ := by
    intro m hm
    rw [hspan] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have : T (ρ a n₀) = χ a • T n₀ := action_eigen_right ρ χ ε hε a n₀
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hline : M ⊓ E = K ∙ T n₀ := by
    apply le_antisymm
    · rintro x ⟨hxM, z, rfl⟩
      have hz : z ∈ M ⊔ M' := by rw [hMM.sup_eq_top]; trivial
      obtain ⟨m, hm, m', hm', rfl⟩ := Submodule.mem_sup.1 hz
      have h1 : T m' ∈ M' := action_mem ρ M' hM' ε m' hm'
      have h2 : T m ∈ M := action_mem ρ M hM ε m hm
      have h3 : T m' ∈ M := by
        have : T m' = T (m + m') - T m := by rw [map_add]; abel
        rw [this]
        exact M.sub_mem hxM h2
      have h4 : T m' = 0 := by
        have : T m' ∈ M ⊓ M' := ⟨h3, h1⟩
        rwa [hMM.inf_eq_bot, Submodule.mem_bot] at this
      rw [map_add, h4, add_zero]
      exact hTM m hm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨action_mem ρ M hM ε n₀ hn₀, n₀, rfl⟩
  refine ⟨by rw [hline]; exact finrank_span_singleton hTn, ?_⟩

  let f : E →ₗ[K] K := (B n₀).comp E.subtype
  have hf : f ≠ 0 := by
    have h1 : twist c ε ≠ 0 := by
      intro h
      apply hε0
      rw [← twist_twist c hcc ε, h, map_zero]
    have h2 : tensorAction ρ (twist c ε) n₀ ≠ 0 := fun h => h1 (hinj _ h)
    obtain ⟨z, hz⟩ : ∃ z, B (tensorAction ρ (twist c ε) n₀) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact h2 (hnd _ h)
    intro h0
    apply hz
    rw [← form_action ρ c B hadj]
    exact LinearMap.congr_fun h0 ⟨T z, z, rfl⟩
  have hmap : (LinearMap.ker f).map E.subtype = B.orthogonal M ⊓ E := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
      refine ⟨?_, hy⟩
      change y ∈ B.orthogonal M
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hy0 : B n₀ y = 0 := hyk
      rw [hspan] at hn
      induction hn using Submodule.span_induction with
      | mem n hn =>
        obtain ⟨a, rfl⟩ := hn
        obtain ⟨z, rfl⟩ := hy
        have h1 := hadj (c a) n₀ (T z)
        rw [hcc] at h1
        show B (ρ a n₀) (T z) = 0
        rw [← h1, action_eigen_left ρ χ ε hε, map_smul, hy0, smul_zero]
      | zero => simp [LinearMap.BilinForm.IsOrtho]
      | add u v _ _ hu hv =>
        simp only [LinearMap.BilinForm.IsOrtho, map_add, LinearMap.add_apply] at *
        rw [hu, hv, add_zero]
      | smul r u _ hu =>
        simp only [LinearMap.BilinForm.IsOrtho, map_smul, LinearMap.smul_apply] at *
        rw [hu, smul_zero]
    · rintro ⟨hx, hxE⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      have hx' : x ∈ B.orthogonal M := hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
      exact hx' n₀ hn₀
  rw [← hmap, Submodule.finrank_map_subtype_eq]
  exact finrank_ker_add_one f hf

end GlobalTheory.EigenLine
