import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Use `show f ∈ ⨆ i, 𝒜 i`. Conclude with `Submodule.mem_iSup_of_mem j hf`.
-/
private theorem mem_gradedSub {O S X : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup X]
    (𝒜 : X → Submodule O S) [SetLike.GradedMonoid 𝒜] {j : X} {f : S} (hf : f ∈ 𝒜 j) : f ∈ gradedSub 𝒜 := by
  show f ∈ ⨆ i, 𝒜 i
  exact Submodule.mem_iSup_of_mem j hf

/- English proof (translation)
Set `B` to `gradedSub 𝒜`. Set `Z : Set X` to `{j | p j = 0}`. Set `P0 : Submodule O B` to `Submodule.comap B.val.toLinearMap (⨆ j ∈ Z, 𝒜 j)`. Set `P1 : Submodule O B` to `Submodule.comap B.val.toLinearMap (⨆ j ∈ Zᶜ, 𝒜 j)`. Establish `hdisj` using `hI.disjoint_biSup_biSup (s := Z) (t := Zᶜ) disjoint_compl_right`.

Establish `hc : IsCompl P0 P1`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x h0 h1`. Conclude with `Subtype.ext (Submodule.disjoint_def.mp hdisj _ h0 h1)`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`. Establish `hle : (⨆ j, 𝒜 j) ≤ (⨆ j ∈ Z, 𝒜 j) ⊔ (⨆ j ∈ Zᶜ, 𝒜 j)`. Use `iSup_le fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j ∈ Z`.

Conclude with `le_sup_of_le_left (le_biSup 𝒜 hj)`. Conclude with `le_sup_of_le_right (le_biSup 𝒜 hj)`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp (hle hx)`. Establish `hsub : ∀ s : Set X, (⨆ j ∈ s, 𝒜 j) ≤ ⨆ j, 𝒜 j` using `fun s => iSup₂_le fun j _ => le_iSup 𝒜 j`. Establish `haB : a ∈ B` using `hsub Z ha`.

Establish `hbB : b ∈ B` using `hsub Zᶜ hb`. Conclude with `Submodule.mem_sup.mpr ⟨⟨a, haB⟩, ha, ⟨b, hbB⟩, hb, Subtype.ext hab⟩`. Set `L : B →ₗ[O] K` to `ξ.toLinearMap ∘ₗ Submodule.projection P0 P1 hc`. Establish `hform : ∀ j f (hf : f ∈ 𝒜 j), L ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0`. Introduce `j f hf`.

Use `split_ifs with hj`. Establish `hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P0` using `(le_biSup 𝒜 (show j ∈ Z from hj)) hf show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _`. Rewrite using `[Submodule.projection_apply_of_mem_left hc hm]`. Establish `hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P1` using `(le_biSup 𝒜 (show j ∈ Zᶜ from hj)) hf show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _`. Establish `h0` using `Submodule.projection_apply_right hc ⟨_, hm⟩`.

Rewrite using `[h0, map_zero]`. Establish `hmul_h : ∀ j k f g (hf : f ∈ 𝒜 j) (hg : g ∈ 𝒜 k), L (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩) = L ⟨f, mem_gradedSub 𝒜 hf⟩ * L ⟨g, mem_gradedSub 𝒜 hg⟩`. Introduce `j k f g hf hg`. Establish `hfg : f * g ∈ 𝒜 (j + k)` using `SetLike.GradedMul.mul_mem hf hg`. Establish `e : (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩ : B) = ⟨f * g, mem_gradedSub 𝒜 hfg⟩` using `rfl`.

Establish `hm : ξ ⟨f * g, mem_gradedSub 𝒜 hfg⟩ = ξ ⟨f, mem_gradedSub 𝒜 hf⟩ * ξ ⟨g, mem_gradedSub 𝒜 hg⟩`. Rewrite using `[← map_mul]`. Both sides reduce to the same expression. Establish `h1` using `h j f hf`. Establish `h2` using `h k g hg`.

Rewrite using `[e, hform _ _ hfg, hform _ _ hf, hform _ _ hg, map_add p]`. Apply the tactic sequence `by_cases hj : p j = 0 <;> by_cases hk : p k = 0`. Simplify using `[hj, hk, hm]`. Establish `: p j + p k ≠ 0` using `by omega`. Simplify using `[hj, hk, this]`.

Establish `: p j + p k ≠ 0` using `by omega`. Simplify using `[hj, hk, this]`. Distinguish the cases in `hs : p j + p k = 0`. Simplify using `only [hs, hj, hk, if_true, if_false, mul_zero, hm]`. Break down `lt_or_gt_of_ne hj with hj' | hj'` into its components or cases.

Rewrite using `[h1 hj', zero_mul]`. Rewrite using `[h2 (by omega), mul_zero]`. Simplify using `[hs, hj, hk]`. Establish `hmul : ∀ (x : S) (hx : x ∈ ⨆ j, 𝒜 j) (y : S) (hy : y ∈ ⨆ j, 𝒜 j), L ((⟨x, hx⟩ : B) * ⟨y, hy⟩) = L ⟨x, hx⟩ * L ⟨y, hy⟩`. Introduce `x hx y hy`.

Proceed by induction on `hx using Submodule.iSup_induction' with`. Consider the case `mem j f hf`. Proceed by induction on `hy using Submodule.iSup_induction' with`. Consider the case `mem k g hg => exact hmul_h j k f g hf hg`. Consider the case `zero`.

Express the relevant statement in the definitionally equal form `L ((⟨f, _⟩ : B) * 0) = L ⟨f, _⟩ * L 0`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb iha ihb`. Express the relevant statement in the definitionally equal form `L ((⟨f, _⟩ : B) * (⟨a, ha⟩ + ⟨b, hb⟩)) = L ⟨f, _⟩ * L (⟨a, ha⟩ + ⟨b, hb⟩)`. Rewrite using `[mul_add, map_add, map_add, mul_add, iha, ihb]`.

Consider the case `zero`. Express the relevant statement in the definitionally equal form `L ((0 : B) * ⟨y, hy⟩) = L 0 * L ⟨y, hy⟩`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb iha ihb`. Express the relevant statement in the definitionally equal form `L (((⟨a, ha⟩ : B) + ⟨b, hb⟩) * ⟨y, hy⟩) = L (⟨a, ha⟩ + ⟨b, hb⟩) * L ⟨y, hy⟩`.

Rewrite using `[add_mul, map_add, map_add, add_mul, iha, ihb]`. Establish `hone : L 1 = 1`. Establish `h1 : (1 : S) ∈ 𝒜 0` using `SetLike.GradedOne.one_mem`. Establish `e : (1 : B) = ⟨1, mem_gradedSub 𝒜 h1⟩` using `rfl`. Rewrite using `[e, hform _ _ h1, if_pos (map_zero p)]`.

Rewrite using `[← e, map_one]`. Use `⟨AlgHom.ofLinearMap L hone (fun x y => hmul x.1 x.2 y.1 y.2), ?_⟩` and prove the remaining obligations. Introduce `j f hf`. Conclude with `hform j f hf`.
-/
private theorem limit_graded {O S X K : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup X]
    [CommRing K] [Algebra O K] (𝒜 : X → Submodule O S) [SetLike.GradedMonoid 𝒜] (hI : iSupIndep 𝒜)
    (ξ : gradedSub 𝒜 →ₐ[O] K) (p : X →+ ℤ)
    (h : ∀ j f (hf : f ∈ 𝒜 j), p j < 0 → ξ ⟨f, mem_gradedSub 𝒜 hf⟩ = 0) :
    ∃ ξ₀ : gradedSub 𝒜 →ₐ[O] K, ∀ j f (hf : f ∈ 𝒜 j),
      ξ₀ ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0 := by
  classical
  let B := gradedSub 𝒜
  let Z : Set X := {j | p j = 0}
  let P0 : Submodule O B := Submodule.comap B.val.toLinearMap (⨆ j ∈ Z, 𝒜 j)
  let P1 : Submodule O B := Submodule.comap B.val.toLinearMap (⨆ j ∈ Zᶜ, 𝒜 j)
  have hdisj := hI.disjoint_biSup_biSup (s := Z) (t := Zᶜ) disjoint_compl_right
  have hc : IsCompl P0 P1 := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x h0 h1
      exact Subtype.ext (Submodule.disjoint_def.mp hdisj _ h0 h1)
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      have hle : (⨆ j, 𝒜 j) ≤ (⨆ j ∈ Z, 𝒜 j) ⊔ (⨆ j ∈ Zᶜ, 𝒜 j) := by
        refine iSup_le fun j => ?_
        by_cases hj : j ∈ Z
        · exact le_sup_of_le_left (le_biSup 𝒜 hj)
        · exact le_sup_of_le_right (le_biSup 𝒜 hj)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hle hx)
      have hsub : ∀ s : Set X, (⨆ j ∈ s, 𝒜 j) ≤ ⨆ j, 𝒜 j := fun s => iSup₂_le fun j _ => le_iSup 𝒜 j
      have haB : a ∈ B := hsub Z ha
      have hbB : b ∈ B := hsub Zᶜ hb
      exact Submodule.mem_sup.mpr ⟨⟨a, haB⟩, ha, ⟨b, hbB⟩, hb, Subtype.ext hab⟩
  let L : B →ₗ[O] K := ξ.toLinearMap ∘ₗ Submodule.projection P0 P1 hc
  have hform : ∀ j f (hf : f ∈ 𝒜 j),
      L ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0 := by
    intro j f hf
    split_ifs with hj
    · have hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P0 := (le_biSup 𝒜 (show j ∈ Z from hj)) hf
      show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _
      rw [Submodule.projection_apply_of_mem_left hc hm]
    · have hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P1 := (le_biSup 𝒜 (show j ∈ Zᶜ from hj)) hf
      show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _
      have h0 := Submodule.projection_apply_right hc ⟨_, hm⟩
      rw [h0, map_zero]
  have hmul_h : ∀ j k f g (hf : f ∈ 𝒜 j) (hg : g ∈ 𝒜 k),
      L (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩) =
        L ⟨f, mem_gradedSub 𝒜 hf⟩ * L ⟨g, mem_gradedSub 𝒜 hg⟩ := by
    intro j k f g hf hg
    have hfg : f * g ∈ 𝒜 (j + k) := SetLike.GradedMul.mul_mem hf hg
    have e : (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩ : B) = ⟨f * g, mem_gradedSub 𝒜 hfg⟩ := rfl
    have hm : ξ ⟨f * g, mem_gradedSub 𝒜 hfg⟩ = ξ ⟨f, mem_gradedSub 𝒜 hf⟩ * ξ ⟨g, mem_gradedSub 𝒜 hg⟩ := by
      rw [← map_mul]
      rfl
    have h1 := h j f hf
    have h2 := h k g hg
    rw [e, hform _ _ hfg, hform _ _ hf, hform _ _ hg, map_add p]
    by_cases hj : p j = 0 <;> by_cases hk : p k = 0
    · simp [hj, hk, hm]
    · have : p j + p k ≠ 0 := by omega
      simp [hj, hk, this]
    · have : p j + p k ≠ 0 := by omega
      simp [hj, hk, this]
    · by_cases hs : p j + p k = 0
      · simp only [hs, hj, hk, if_true, if_false, mul_zero, hm]
        rcases lt_or_gt_of_ne hj with hj' | hj'
        · rw [h1 hj', zero_mul]
        · rw [h2 (by omega), mul_zero]
      · simp [hs, hj, hk]
  have hmul : ∀ (x : S) (hx : x ∈ ⨆ j, 𝒜 j) (y : S) (hy : y ∈ ⨆ j, 𝒜 j),
      L ((⟨x, hx⟩ : B) * ⟨y, hy⟩) = L ⟨x, hx⟩ * L ⟨y, hy⟩ := by
    intro x hx y hy
    induction hx using Submodule.iSup_induction' with
    | mem j f hf =>
      induction hy using Submodule.iSup_induction' with
      | mem k g hg => exact hmul_h j k f g hf hg
      | zero =>
        change L ((⟨f, _⟩ : B) * 0) = L ⟨f, _⟩ * L 0
        simp
      | add a b ha hb iha ihb =>
        change L ((⟨f, _⟩ : B) * (⟨a, ha⟩ + ⟨b, hb⟩)) = L ⟨f, _⟩ * L (⟨a, ha⟩ + ⟨b, hb⟩)
        rw [mul_add, map_add, map_add, mul_add, iha, ihb]
    | zero =>
      change L ((0 : B) * ⟨y, hy⟩) = L 0 * L ⟨y, hy⟩
      simp
    | add a b ha hb iha ihb =>
      change L (((⟨a, ha⟩ : B) + ⟨b, hb⟩) * ⟨y, hy⟩) = L (⟨a, ha⟩ + ⟨b, hb⟩) * L ⟨y, hy⟩
      rw [add_mul, map_add, map_add, add_mul, iha, ihb]
  have hone : L 1 = 1 := by
    have h1 : (1 : S) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
    have e : (1 : B) = ⟨1, mem_gradedSub 𝒜 h1⟩ := rfl
    rw [e, hform _ _ h1, if_pos (map_zero p)]
    rw [← e, map_one]
  refine ⟨AlgHom.ofLinearMap L hone (fun x y => hmul x.1 x.2 y.1 y.2), ?_⟩
  intro j f hf
  exact hform j f hf

/- English proof (translation)
Establish `hmemA : ∀ L : List (H × Fin 4 × Fin 4), (L.map (fun a => r a.1 a.2.1 a.2.2)).prod ∈ A`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => simpa using A.one_mem`. Consider the case `cons a L ih => simpa using A.mul_mem (hr a.1 a.2.1 a.2.2) ih`.

Establish `hξL : ∀ L : List (H × Fin 4 × Fin 4), ξ ⟨_, hmemA L⟩ = (L.map (fun a => ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩)).prod`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Establish `e : (⟨_, hmemA []⟩ : A) = 1` using `Subtype.ext (by simp)`.

Rewrite using `[e, map_one]`. Simplify using the standard rewrite rules. Consider the case `cons a L ih`. Establish `e : ξ ⟨_, hmemA (a :: L)⟩ = ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩ * ξ ⟨_, hmemA L⟩`. Rewrite using `[← map_mul]`.

Apply `congrArg ξ` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[e, ih]`. Simplify using the standard rewrite rules.

Establish `hspan : Submodule.span O (mono r w) ≤ Subalgebra.toSubmodule A`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨L, -, rfl⟩`. Conclude with `hmemA L`. Use `revert hA`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `hA`. Take `⟨L, hL, rfl⟩` from `hx`. Use `(hξL L).trans ?_` and prove the remaining obligations.

Apply `List.prod_eq_zero` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`. Establish `hall : ∀ a ∈ L, 0 ≤ p (wt a.2.1 a.2.2)`. Introduce `a ha`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Conclude with `hne (List.mem_map.mpr ⟨a, ha, h a.1 a.2.1 a.2.2 hlt⟩)`. Establish `hnn : 0 ≤ p w`. Rewrite using `[← hL, map_list_sum, List.map_map]`. Apply `List.sum_nonneg` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `List.mem_map.mp hx`. Conclude with `hall a ha`. Use linear arithmetic over natural numbers and integers. Consider the case `zero`.

Introduce `hA`. Establish `e : (⟨0, hA⟩ : A) = 0` using `rfl`. Rewrite using `[e, map_zero]`. Consider the case `add x y hx hy ihx ihy`. Introduce `hA`.

Establish `e : (⟨x + y, hA⟩ : A) = ⟨x, hspan hx⟩ + ⟨y, hspan hy⟩` using `rfl`. Rewrite using `[e, map_add, ihx, ihy, add_zero]`. Consider the case `smul a x hx ih`. Introduce `hA`. Establish `e : (⟨a • x, hA⟩ : A) = a • (⟨x, hspan hx⟩ : A)` using `rfl`.

Rewrite using `[e, map_smul, ih, smul_zero]`.
-/
private theorem vanish_mono {O S K H : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    [Group H] (A : Subalgebra O S) (r : H →* M4 S) (hr : ∀ g i j, r g i j ∈ A) (ξ : A →ₐ[O] K)
    (p : ℤ × ℤ →+ ℤ) (h : ∀ g i j, p (wt i j) < 0 → ξ ⟨r g i j, hr g i j⟩ = 0) (w : ℤ × ℤ) (hw : p w < 0)
    (f : S) (hf : f ∈ Submodule.span O (mono r w)) (hA : f ∈ A) : ξ ⟨f, hA⟩ = 0 := by
  have hmemA : ∀ L : List (H × Fin 4 × Fin 4), (L.map (fun a => r a.1 a.2.1 a.2.2)).prod ∈ A := by
    intro L
    induction L with
    | nil => simpa using A.one_mem
    | cons a L ih => simpa using A.mul_mem (hr a.1 a.2.1 a.2.2) ih
  have hξL : ∀ L : List (H × Fin 4 × Fin 4), ξ ⟨_, hmemA L⟩ =
      (L.map (fun a => ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩)).prod := by
    intro L
    induction L with
    | nil =>
      have e : (⟨_, hmemA []⟩ : A) = 1 := Subtype.ext (by simp)
      rw [e, map_one]
      simp
    | cons a L ih =>
      have e : ξ ⟨_, hmemA (a :: L)⟩ = ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩ * ξ ⟨_, hmemA L⟩ := by
        rw [← map_mul]
        apply congrArg ξ
        apply Subtype.ext
        simp
      rw [e, ih]
      simp
  have hspan : Submodule.span O (mono r w) ≤ Subalgebra.toSubmodule A := by
    rw [Submodule.span_le]
    rintro x ⟨L, -, rfl⟩
    exact hmemA L
  revert hA
  induction hf using Submodule.span_induction with
  | mem x hx =>
    intro hA
    obtain ⟨L, hL, rfl⟩ := hx
    refine (hξL L).trans ?_
    apply List.prod_eq_zero
    by_contra hne
    have hall : ∀ a ∈ L, 0 ≤ p (wt a.2.1 a.2.2) := by
      intro a ha
      by_contra hlt
      push_neg at hlt
      exact hne (List.mem_map.mpr ⟨a, ha, h a.1 a.2.1 a.2.2 hlt⟩)
    have hnn : 0 ≤ p w := by
      rw [← hL, map_list_sum, List.map_map]
      apply List.sum_nonneg
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hall a ha
    omega
  | zero =>
    intro hA
    have e : (⟨0, hA⟩ : A) = 0 := rfl
    rw [e, map_zero]
  | add x y hx hy ihx ihy =>
    intro hA
    have e : (⟨x + y, hA⟩ : A) = ⟨x, hspan hx⟩ + ⟨y, hspan hy⟩ := rfl
    rw [e, map_add, ihx, ihy, add_zero]
  | smul a x hx ih =>
    intro hA
    have e : (⟨a • x, hA⟩ : A) = a • (⟨x, hspan hx⟩ : A) := rfl
    rw [e, map_smul, ih, smul_zero]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD M hF ξ hcase`. Establish `hrep : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j, M.rep ζ g i j = ζ ⟨M.ru.hom g i j, M.sPart_le (M.entry_mem g i j)⟩`. Introduce `ζ g i j`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hp0⟩ : ∃ p : ℤ × ℤ →+ ℤ, (∀ g i j, p (wt i j) < 0 → M.rep ξ g i j = 0) ∧ ∀ i j, (p (wt i j) = 0 ↔ lamW i = lamW j) := by`.

Break down `hcase with hc | hc` into its components or cases. Use `⟨AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩` and prove the remaining obligations. Introduce `g i j hlt`. Establish `h1 : lamW i < lamW j`. Simplify using `only [wt, AddMonoidHom.coe_fst] at hlt`.

Use linear arithmetic over natural numbers and integers. Use `hc i j h1` as an intermediate fact. Simplify using `only [Ge, not_exists, not_not] at this`. Conclude with `this g`. Introduce `i j`.

Simplify using `only [wt, AddMonoidHom.coe_fst]`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Use `⟨-AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩` and prove the remaining obligations. Introduce `g i j hlt`. Establish `h1 : lamW j < lamW i`.

Simplify using `only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst] at hlt`. Use linear arithmetic over natural numbers and integers. Use `hc i j h1` as an intermediate fact. Simplify using `only [Ge, not_exists, not_not] at this`. Conclude with `this g`.

Introduce `i j`. Simplify using `only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst]`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Take `⟨hI, -, -⟩` from `sInternal D hD M`. Establish `hvan : ∀ j f (hf : f ∈ M.sPart j), p j < 0 → ξ ⟨f, mem_gradedSub M.sPart hf⟩ = 0`.

Introduce `j f hf hj`. Establish `hf' : f ∈ Submodule.span c.O (mono M.ru.hom j)`. Rewrite using `[← spanMono D hD M hF j]`. Conclude with `hf`. Conclude with `vanish_mono M.SS M.ru.hom (fun g i j => M.sPart_le (M.entry_mem g i j)) ξ p (fun g i j hlt => (hrep ξ g i j).symm.trans (hp g i j hlt)) j hj f hf' _`.

Take `⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ j f (hf : f ∈ M.sPart j), ξ₀ ⟨f, M.sPart_le hf⟩ = if p j = 0 then ξ ⟨f, M.sPart_le hf⟩ else 0` from `limit_graded M.sPart hI ξ p hvan`. Use `⟨ξ₀, fun g i j => ?_⟩` and prove the remaining obligations. Rewrite using `[hrep, hrep, hξ₀ (wt i j) _ (M.entry_mem g i j)]`. Distinguish the cases in `hij : lamW i = lamW j`. Rewrite using `[if_pos ((hp0 i j).mpr hij), if_pos hij]`.

Rewrite using `[if_neg (fun h => hij ((hp0 i j).mp h)), if_neg hij]`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.ptLimit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, lamW i < lamW j → ¬ Ge (M.rep ξ) i j) ∨ ∀ i j, lamW j < lamW i → ¬ Ge (M.rep ξ) i j) → ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ g i j, M.rep ξ₀ g i j = if lamW i = lamW j then M.rep ξ g i j else 0 := by
  intro Ω _ _ _ l _ c D hD M hF ξ hcase
  have hrep : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j,
      M.rep ζ g i j = ζ ⟨M.ru.hom g i j, M.sPart_le (M.entry_mem g i j)⟩ := by
    intro ζ g i j
    rfl
  obtain ⟨p, hp, hp0⟩ : ∃ p : ℤ × ℤ →+ ℤ, (∀ g i j, p (wt i j) < 0 → M.rep ξ g i j = 0) ∧
      ∀ i j, (p (wt i j) = 0 ↔ lamW i = lamW j) := by
    rcases hcase with hc | hc
    · refine ⟨AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩
      · intro g i j hlt
        have h1 : lamW i < lamW j := by
          simp only [wt, AddMonoidHom.coe_fst] at hlt
          omega
        have := hc i j h1
        simp only [Ge, not_exists, not_not] at this
        exact this g
      · intro i j
        simp only [wt, AddMonoidHom.coe_fst]
        constructor <;> intro h <;> omega
    · refine ⟨-AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩
      · intro g i j hlt
        have h1 : lamW j < lamW i := by
          simp only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst] at hlt
          omega
        have := hc i j h1
        simp only [Ge, not_exists, not_not] at this
        exact this g
      · intro i j
        simp only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst]
        constructor <;> intro h <;> omega
  obtain ⟨hI, -, -⟩ := sInternal D hD M
  have hvan : ∀ j f (hf : f ∈ M.sPart j), p j < 0 → ξ ⟨f, mem_gradedSub M.sPart hf⟩ = 0 := by
    intro j f hf hj
    have hf' : f ∈ Submodule.span c.O (mono M.ru.hom j) := by
      rw [← spanMono D hD M hF j]
      exact hf
    exact vanish_mono M.SS M.ru.hom (fun g i j => M.sPart_le (M.entry_mem g i j)) ξ p
      (fun g i j hlt => (hrep ξ g i j).symm.trans (hp g i j hlt)) j hj f hf' _
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ j f (hf : f ∈ M.sPart j),
      ξ₀ ⟨f, M.sPart_le hf⟩ = if p j = 0 then ξ ⟨f, M.sPart_le hf⟩ else 0 :=
    limit_graded M.sPart hI ξ p hvan
  refine ⟨ξ₀, fun g i j => ?_⟩
  rw [hrep, hrep, hξ₀ (wt i j) _ (M.entry_mem g i j)]
  by_cases hij : lamW i = lamW j
  · rw [if_pos ((hp0 i j).mpr hij), if_pos hij]
  · rw [if_neg (fun h => hij ((hp0 i j).mp h)), if_neg hij]
