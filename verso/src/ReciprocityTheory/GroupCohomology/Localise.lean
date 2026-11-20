import ReciprocityTheory.GroupCohomology.LocaliseA

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

/- English proof (translation)
Introduce `R _ G _ _ _ _ t L V j hφ hu he hcov n`. Take `⟨e, he⟩` from `he`. Use `isLocalized_of_cx j.hom t ?_ ?_ ?_ n` and prove the remaining obligations. Introduce `k x y hxy`. Break down `j with ⟨φ, u, hφc, huc, heq⟩` into its components or cases.

Simplify using `only at hφ hu`. Substitute `hφ` using the available equality. Use `Subtype.ext (funext fun g => hu.injective ?_)` and prove the remaining obligations. Conclude with `congrFun (congrArg Subtype.val hxy) g`. Introduce `k`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Use `Subtype.ext (funext fun g => e.injective ?_)` and prove the remaining obligations. Rewrite using `[he, he]`. Conclude with `congrFun (congrArg Subtype.val hxy) g`.

Introduce `y`. Use `⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩` and prove the remaining obligations. Use `show t • e.symm (y.1 g) = y.1 g`. Rewrite using `[← he, e.apply_symm_apply]`. Introduce `k x`.

Break down `j with ⟨φ, u, hφc, huc, heq⟩` into its components or cases. Simplify using `only at hφ hu hcov`. Substitute `hφ` using the available equality. Establish `hx : Continuous x.1` using `x.2`. Set `O : ℕ → Set (Fin k → G)` to `fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)`.

Establish `hO : ∀ m, IsOpen (O m)` using `fun m => ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx`. Establish `hmono : Monotone O`. Use `monotone_nat_of_le_succ fun m g hg => ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `hg`. Use `⟨t • l, ?_⟩` and prove the remaining obligations.

Simplify using `only at hl ⊢`. Rewrite using `[map_smul, hl, pow_succ', mul_smul]`. Establish `hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m`. Introduce `g _`. Take `⟨m, l, hl⟩` from `hcov (x.1 g)`.

Conclude with `Set.mem_iUnion.2 ⟨m, l, hl⟩`. Take `⟨m, hm⟩` from `isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le`. Establish `hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g` using `fun g => invFun_eq (hm (Set.mem_univ g))`. Establish `hyc : Continuous fun g => invFun u (t ^ m • x.1 g)`. Rewrite using `[hu.isEmbedding.continuous_iff]`.

Establish `: (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g` using `funext hy`. Rewrite using `[this]`. Conclude with `hx.const_smul _`. Use `⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩` and prove the remaining obligations. Conclude with `hy g`.
-/
theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  refine isLocalized_of_cx j.hom t ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

/- English proof (translation)
Introduce `R _ A L`. Use `⟨truncCx A L, truncHom A L, ⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Proceed by induction on `c using H_ind with`.

Consider the case `h x hx`. Rewrite `hc` using `[Hom.H_cls, cls_eq_zero_iff, mem_B_zero]`. Rewrite using `[cls_eq_zero_iff, mem_B_zero]`. Conclude with `Subtype.ext hc`. Introduce `c`.

Proceed by induction on `c using H_ind with`. Consider the case `h x hx`. Conclude with `⟨(truncCx A L).cls 0 ⟨x, Submodule.mem_top⟩ (Subtype.ext hx), rfl⟩`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`.

Proceed by induction on `c using H_ind with`. Consider the case `h x hx`. Rewrite `hc` using `[Hom.H_cls, cls_eq_zero_iff, mem_B_succ]`. Take `⟨y, hy⟩` from `hc`. Rewrite using `[cls_eq_zero_iff, mem_B_succ]`.

Conclude with `⟨⟨y, Submodule.mem_top⟩, Subtype.ext hy⟩`. Use extensionality with `c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c', rfl⟩`. Proceed by induction on `c' using H_ind with`.

Consider the case `h x hx`. Rewrite using `[Hom.H_cls]`. Take `⟨_, h⟩` from `(mem_truncW_one A L).1 x.2`. Conclude with `h`. Introduce `hc`.

Take `⟨x, hx, rfl⟩` from `exists_cls c`. Establish `hm : x ∈ truncW A L 1` using `(mem_truncW_one A L).2 ⟨hx, hc⟩`. Conclude with `⟨(truncCx A L).cls 1 ⟨x, hm⟩ (Subtype.ext hx), rfl⟩`. Introduce `n hn`. Take `⟨k, rfl⟩ : ∃ k, n = k + 2` from `⟨n - 2, by omega⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `a b`. Proceed by induction on `a using H_ind with`. Consider the case `h x hx`. Proceed by induction on `b using H_ind with`.

Consider the case `h y hy`. Establish `h1 : x = 0` using `Subtype.ext ((Submodule.mem_bot R).1 x.2)`. Establish `h2 : y = 0` using `Subtype.ext ((Submodule.mem_bot R).1 y.2)`. Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
theorem trunc_holds : TruncStatement.{u} := by
  intro R _ A L
  refine ⟨truncCx A L, truncHom A L, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_zero] at hc
      rw [cls_eq_zero_iff, mem_B_zero]
      exact Subtype.ext hc
  · intro c
    induction c using H_ind with
    | h x hx =>
      exact ⟨(truncCx A L).cls 0 ⟨x, Submodule.mem_top⟩ (Subtype.ext hx), rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_succ] at hc
      obtain ⟨y, hy⟩ := hc
      rw [cls_eq_zero_iff, mem_B_succ]
      exact ⟨⟨y, Submodule.mem_top⟩, Subtype.ext hy⟩
  · ext c
    constructor
    · rintro ⟨c', rfl⟩
      induction c' using H_ind with
      | h x hx =>
        rw [Hom.H_cls]
        obtain ⟨_, h⟩ := (mem_truncW_one A L).1 x.2
        exact h
    · intro hc
      obtain ⟨x, hx, rfl⟩ := exists_cls c
      have hm : x ∈ truncW A L 1 := (mem_truncW_one A L).2 ⟨hx, hc⟩
      exact ⟨(truncCx A L).cls 1 ⟨x, hm⟩ (Subtype.ext hx), rfl⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    constructor
    intro a b
    induction a using H_ind with
    | h x hx =>
    induction b using H_ind with
    | h y hy =>
      have h1 : x = 0 := Subtype.ext ((Submodule.mem_bot R).1 x.2)
      have h2 : y = 0 := Subtype.ext ((Submodule.mem_bot R).1 y.2)
      subst h1 h2; rfl

end ReciprocityTheory.Coh
