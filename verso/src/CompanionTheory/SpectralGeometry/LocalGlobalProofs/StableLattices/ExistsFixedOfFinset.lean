import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

noncomputable section

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RestT

section Local

variable {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)} {A : X → X → (H →L[ℂ] H)}

def IsOpFam (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)) (A : X → X → (H →L[ℂ] H)) : Prop :=
  ∀ y ξ, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A y ξ (T x) = ⟪ξ, x⟫_ℂ • T y

/- English proof (translation)
Establish `hle : isoPart δ ρ ⊤ ≤ LinearMap.ker ((C - D : H →L[ℂ] H) : H →ₗ[ℂ] H)` using `isoPart_le (ContinuousLinearMap.isClosed_ker (C - D)) fun T hT x => by`. Simplify using `[h T hT x]`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hv : v ∈ LinearMap.ker ((C - D : H →L[ℂ] H) : H →ₗ[ℂ] H)` using `hle (by rw [show isoPart δ ρ ⊤ = ⊤ from hi]; exact Submodule.mem_top)`. Simplify `hv` using `[sub_eq_zero]`.
-/
theorem ext_of_hom (hi : IsIsotypic δ ρ) {C D : H →L[ℂ] H}
    (h : ∀ T ∈ homIn δ ρ ⊤, ∀ x, C (T x) = D (T x)) : C = D := by
  have hle : isoPart δ ρ ⊤ ≤ LinearMap.ker ((C - D : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    isoPart_le (ContinuousLinearMap.isClosed_ker (C - D)) fun T hT x => by
      simp [h T hT x]
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker ((C - D : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    hle (by rw [show isoPart δ ρ ⊤ = ⊤ from hi]; exact Submodule.mem_top)
  simpa [sub_eq_zero] using hv

/- English proof (translation)
Establish `hle : isoPart δ ρ ⊤ ≤ (ℂ ∙ v)ᗮ` using `isoPart_le (Submodule.isClosed_orthogonal _) fun T hT x => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h T hT x)`. Establish `hv : v ∈ (ℂ ∙ v)ᗮ` using `hle (by rw [show isoPart δ ρ ⊤ = ⊤ from hi]; exact Submodule.mem_top)`. Conclude with `inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv)`.
-/
theorem eq_zero_of_hom [CompleteSpace H] (hi : IsIsotypic δ ρ) {v : H}
    (h : ∀ T ∈ homIn δ ρ ⊤, ∀ x, ⟪T x, v⟫_ℂ = 0) : v = 0 := by
  have hle : isoPart δ ρ ⊤ ≤ (ℂ ∙ v)ᗮ :=
    isoPart_le (Submodule.isClosed_orthogonal _) fun T hT x =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h T hT x)
  have hv : v ∈ (ℂ ∙ v)ᗮ := hle (by rw [show isoPart δ ρ ⊤ = ⊤ from hi]; exact Submodule.mem_top)
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv)

/- English proof (translation)
Use `ext_of_hom hi fun T hT x => ?_` and prove the remaining obligations. Establish `hCT : C ∘L T ∈ homIn δ ρ ⊤` using `mem_homIn_top.2 fun g x => by`. Use `DFunLike.congr_fun (hC g) (T x)` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`. Simplify using `[(mem_homIn_top.1 hT) g x, this]`.

Establish `h1` using `hA y ξ _ hCT x`. Simplify using `only [ContinuousLinearMap.comp_apply] at h1`. Simplify using `[h1, hA y ξ T hT x]`.
-/
theorem IsOpFam.commute (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) {C : H →L[ℂ] H}
    (hC : ∀ g, Commute C (ρ g)) (y ξ : X) : Commute (A y ξ) C := by
  refine ext_of_hom hi fun T hT x => ?_
  have hCT : C ∘L T ∈ homIn δ ρ ⊤ := mem_homIn_top.2 fun g x => by
    have := DFunLike.congr_fun (hC g) (T x)
    simp only [ContinuousLinearMap.mul_apply] at this
    simp [(mem_homIn_top.1 hT) g x, this]
  have h1 := hA y ξ _ hCT x
  simp only [ContinuousLinearMap.comp_apply] at h1
  simp [h1, hA y ξ T hT x]

/- English proof (translation)
Use `ext_of_hom hi fun T hT x => ?_` and prove the remaining obligations. Simplify using `[hA y ξ T hT x, hA (δ g y) ξ T hT x, (mem_homIn_top.1 hT) g y]`.
-/
theorem IsOpFam.rep_mul (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (g : G) (y ξ : X) :
    ρ g * A y ξ = A (δ g y) ξ := by
  refine ext_of_hom hi fun T hT x => ?_
  simp [hA y ξ T hT x, hA (δ g y) ξ T hT x, (mem_homIn_top.1 hT) g y]

/- English proof (translation)
Use `ext_of_hom hi fun T hT x => ?_` and prove the remaining obligations. Simplify using `[hA y' ξ' T hT x, hA y ξ T hT y', hA y ξ' T hT x, smul_smul, mul_comm]`.
-/
theorem IsOpFam.mul (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (y ξ y' ξ' : X) :
    A y ξ * A y' ξ' = ⟪ξ, y'⟫_ℂ • A y ξ' := by
  refine ext_of_hom hi fun T hT x => ?_
  simp [hA y' ξ' T hT x, hA y ξ T hT y', hA y ξ' T hT x, smul_smul, mul_comm]

/- English proof (translation)
Use `ext_of_hom hi fun T hT x => ?_` and prove the remaining obligations. Use `sub_eq_zero.1 (eq_zero_of_hom hi fun T' hT' x' => ?_)` and prove the remaining obligations. Rewrite using `[inner_sub_right, ContinuousLinearMap.adjoint_inner_right, hA y ξ T' hT' x', hA ξ y T hT x, inner_smul_left, inner_smul_right, inner_eq_be hδ hρ hT hT' x y, inner_eq_be hδ hρ hT hT' ξ x', inner_conj_symm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsOpFam.adjoint_eq [CompleteSpace H] (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ)
    (hρ : IsUnitaryRep ρ) (y ξ : X) : ContinuousLinearMap.adjoint (A y ξ) = A ξ y := by
  refine ext_of_hom hi fun T hT x => ?_
  refine sub_eq_zero.1 (eq_zero_of_hom hi fun T' hT' x' => ?_)
  rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right, hA y ξ T' hT' x', hA ξ y T hT x,
    inner_smul_left, inner_smul_right, inner_eq_be hδ hρ hT hT' x y, inner_eq_be hδ hρ hT hT' ξ x',
    inner_conj_symm]
  ring

/- English proof (translation)
Use `hδ.complete` as an intermediate fact. Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, ← inv_inv g, ← hδ.unitary.inner_apply_left, ContinuousLinearMap.adjoint_inner_right, ← hρ.inner_apply_left, (mem_homIn_top.1 hT) g⁻¹ u]`.
-/
theorem adjoint_intertwine [CompleteSpace H] (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {T : X →L[ℂ] H}
    (hT : T ∈ homIn δ ρ ⊤) (g : G) (v : H) :
    have := hδ.complete
    ContinuousLinearMap.adjoint T (ρ g v) = δ g (ContinuousLinearMap.adjoint T v) := by
  have := hδ.complete
  refine ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inv_inv g, ← hδ.unitary.inner_apply_left,
    ContinuousLinearMap.adjoint_inner_right, ← hρ.inner_apply_left, (mem_homIn_top.1 hT) g⁻¹ u]

/- English proof (translation)
Use `hδ.complete` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨T, hT, x, hx⟩ : ∃ T ∈ homIn δ ρ ⊤, ∃ x, ⟪T x, w⟫_ℂ ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `hw (eq_zero_of_hom hi hn)`.

Use `set z := ContinuousLinearMap.adjoint T w with hz`. Establish `hz0 : z ≠ 0` using `fun e => hx (by rw [← ContinuousLinearMap.adjoint_inner_right, ← hz, e, inner_zero_right])`. Establish `hn : (‖z‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz0`. Use `⟨(‖z‖ : ℂ)⁻¹ • z, ?_, fun e => ?_⟩` and prove the remaining obligations. Simplify using `[norm_smul, hz0]`.

Use `set ξ := (‖z‖ : ℂ)⁻¹ • z with hξ`. Establish `h1 : ‖ξ‖ = 1` using `by simp [hξ, norm_smul, hz0]`. Establish `h2 : ⟪A ξ ξ (T ξ), w⟫_ℂ = 0`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, hA.adjoint_eq hi hδ hρ, e, inner_zero_right]`. Rewrite `h2` using `[hA ξ ξ T hT ξ, inner_self_eq_norm_sq_to_K, h1]`.

Establish `h3 : ⟪ξ, z⟫_ℂ = 0`. Rewrite using `[hz, ContinuousLinearMap.adjoint_inner_right]`. Simplify using `using h2`. Rewrite `h3` using `[hξ, inner_smul_left, inner_self_eq_norm_sq_to_K]`. Simplify using `[hz0] at h3`.
-/
theorem IsOpFam.exists_ne_zero [CompleteSpace H] (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ)
    (hρ : IsUnitaryRep ρ) {w : H} (hw : w ≠ 0) : ∃ ξ : X, ‖ξ‖ = 1 ∧ A ξ ξ w ≠ 0 := by
  have := hδ.complete
  obtain ⟨T, hT, x, hx⟩ : ∃ T ∈ homIn δ ρ ⊤, ∃ x, ⟪T x, w⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hw (eq_zero_of_hom hi hn)
  set z := ContinuousLinearMap.adjoint T w with hz
  have hz0 : z ≠ 0 := fun e => hx (by rw [← ContinuousLinearMap.adjoint_inner_right, ← hz, e, inner_zero_right])
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  refine ⟨(‖z‖ : ℂ)⁻¹ • z, ?_, fun e => ?_⟩
  · simp [norm_smul, hz0]
  set ξ := (‖z‖ : ℂ)⁻¹ • z with hξ
  have h1 : ‖ξ‖ = 1 := by simp [hξ, norm_smul, hz0]
  have h2 : ⟪A ξ ξ (T ξ), w⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hA.adjoint_eq hi hδ hρ, e, inner_zero_right]
  rw [hA ξ ξ T hT ξ, inner_self_eq_norm_sq_to_K, h1] at h2
  have h3 : ⟪ξ, z⟫_ℂ = 0 := by
    rw [hz, ContinuousLinearMap.adjoint_inner_right]
    simpa using h2
  rw [hξ, inner_smul_left, inner_self_eq_norm_sq_to_K] at h3
  simp [hz0] at h3

/- English proof (translation)
Use `hδ.complete` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨T, hT, x, hx⟩ : ∃ T ∈ homIn δ ρ ⊤, ∃ x, ⟪T x, h⟫_ℂ ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `h0 (eq_zero_of_hom hi hn)`.

Use `⟨ContinuousLinearMap.adjoint T h, fun e => hx ?_, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, e, inner_zero_right]`. Rewrite using `[← adjoint_intertwine hδ hρ hT k h, hK k hk]`.
-/
theorem exists_fixed_ne_zero [CompleteSpace H] (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ)
    (K : Subgroup G) {h : H} (h0 : h ≠ 0) (hK : ∀ k ∈ K, ρ k h = h) : ∃ x : X, x ≠ 0 ∧ ∀ k ∈ K, δ k x = x := by
  have := hδ.complete
  obtain ⟨T, hT, x, hx⟩ : ∃ T ∈ homIn δ ρ ⊤, ∃ x, ⟪T x, h⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (eq_zero_of_hom hi hn)
  refine ⟨ContinuousLinearMap.adjoint T h, fun e => hx ?_, fun k hk => ?_⟩
  · rw [← ContinuousLinearMap.adjoint_inner_right, e, inner_zero_right]
  · rw [← adjoint_intertwine hδ hρ hT k h, hK k hk]

/- English proof (translation)
Use `hδ.complete` as an intermediate fact. Use `sub_eq_zero.1 (eq_zero_of_hom hi fun T hT x => ?_)` and prove the remaining obligations. Take `⟨c, hc⟩` from `hl (ContinuousLinearMap.adjoint T h) fun k hk => by`. Rewrite using `[← adjoint_intertwine hδ hρ hT k h, hK k hk]`. Establish `h1 : ∀ u, ⟪T u, h⟫_ℂ = c * ⟪u, ξ⟫_ℂ` using `fun u => by`.

Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, hc, inner_smul_right]`. Rewrite using `[inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left (A ξ ξ), hA.adjoint_eq hi hδ hρ, hA ξ ξ T hT x, inner_smul_left, h1, h1, inner_conj_symm, inner_self_eq_norm_sq_to_K, hξ]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsOpFam.apply_fixed [CompleteSpace H] (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ)
    (hρ : IsUnitaryRep ρ) (K : Subgroup G) {ξ : X} (hξ : ‖ξ‖ = 1)
    (hl : ∀ x : X, (∀ k ∈ K, δ k x = x) → ∃ c : ℂ, x = c • ξ) {h : H} (hK : ∀ k ∈ K, ρ k h = h) : A ξ ξ h = h := by
  have := hδ.complete
  refine sub_eq_zero.1 (eq_zero_of_hom hi fun T hT x => ?_)
  obtain ⟨c, hc⟩ := hl (ContinuousLinearMap.adjoint T h) fun k hk => by
    rw [← adjoint_intertwine hδ hρ hT k h, hK k hk]
  have h1 : ∀ u, ⟪T u, h⟫_ℂ = c * ⟪u, ξ⟫_ℂ := fun u => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hc, inner_smul_right]
  rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left (A ξ ξ), hA.adjoint_eq hi hδ hρ, hA ξ ξ T hT x,
    inner_smul_left, h1, h1, inner_conj_symm, inner_self_eq_norm_sq_to_K, hξ]
  simp
  ring

end Local

section Tensor

variable {ι G H : Type} {Γ Hs : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
  {a : ∀ i, Hs i → (H →L[ℂ] H)} {ξ : ∀ i, Hs i} {w : H}

def pr (hc : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y')) (s : Finset ι) (y : ∀ i, Hs i) : H →L[ℂ] H :=
  s.noncommProd (fun i => a i (y i)) fun i _ j _ h => hc i j h _ _

variable (hc : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y'))

/- English proof (translation)
The claim follows from `Finset.noncommProd_empty _ _`.
-/
@[simp] theorem pr_empty (y : ∀ i, Hs i) : pr hc ∅ y = 1 := Finset.noncommProd_empty _ _

/- English proof (translation)
The claim follows from `Finset.noncommProd_insert_of_notMem _ _ _ _ hi`.
-/
theorem pr_insert [DecidableEq ι] {s : Finset ι} {i : ι} (hi : i ∉ s) (y : ∀ i, Hs i) :
    pr hc (insert i s) y = a i (y i) * pr hc s y :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hi

/- English proof (translation)
The claim follows from `Finset.noncommProd_commute _ _ _ _ h`.
-/
theorem commute_pr {C : H →L[ℂ] H} {s : Finset ι} {y : ∀ i, Hs i} (h : ∀ i ∈ s, Commute C (a i (y i))) :
    Commute C (pr hc s y) :=
  Finset.noncommProd_commute _ _ _ _ h

/- English proof (translation)
The claim follows from `Finset.noncommProd_congr rfl (fun i hi => by rw [h i hi]) _`.
-/
theorem pr_congr {s : Finset ι} {y y' : ∀ i, Hs i} (h : ∀ i ∈ s, y i = y' i) : pr hc s y = pr hc s y' :=
  Finset.noncommProd_congr rfl (fun i hi => by rw [h i hi]) _

/- English proof (translation)
Establish `h` using `commute_pr hc (C := a i (y i)) (s := s) (y := y) fun j hj => hc i j (fun e => hi (e ▸ hj)) _ _`. Rewrite using `[pr_insert hc hi, h.eq, ContinuousLinearMap.mul_apply, hy, hw]`.
-/
theorem pr_insert_apply [DecidableEq ι] {s : Finset ι} {i : ι} (hi : i ∉ s) {y : ∀ i, Hs i} (hy : y i = ξ i)
    (hw : a i (ξ i) w = w) : pr hc (insert i s) y w = pr hc s y w := by
  have h := commute_pr hc (C := a i (y i)) (s := s) (y := y) fun j hj =>
    hc i j (fun e => hi (e ▸ hj)) _ _
  rw [pr_insert hc hi, h.eq, ContinuousLinearMap.mul_apply, hy, hw]

/- English proof (translation)
Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j u hj ih`. Establish `ih'` using `ih fun i hi => hy i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.union_insert]`.

Distinguish the cases in `h : j ∈ t ∪ u`. Rewrite using `[Finset.insert_eq_of_mem h]` and apply the resulting hypothesis. Rewrite using `[pr_insert_apply hc h (hy j (Finset.mem_insert_self _ _) fun e => h (Finset.mem_union_left _ e)) (hw j), ih']`.
-/
theorem pr_union_apply [DecidableEq ι] (hw : ∀ i, a i (ξ i) w = w) (t u : Finset ι) {y : ∀ i, Hs i}
    (hy : ∀ i ∈ u, i ∉ t → y i = ξ i) : pr hc (t ∪ u) y w = pr hc t y w := by
  induction u using Finset.induction_on with
  | empty => simp
  | insert j u hj ih =>
    have ih' := ih fun i hi => hy i (Finset.mem_insert_of_mem hi)
    rw [Finset.union_insert]
    by_cases h : j ∈ t ∪ u
    · rwa [Finset.insert_eq_of_mem h]
    · rw [pr_insert_apply hc h (hy j (Finset.mem_insert_self _ _) fun e => h (Finset.mem_union_left _ e)) (hw j), ih']

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Establish `h` using `commute_pr hc (C := a j (ξ j)) (s := s) (y := y) fun i hi => hc j i (fun e => hj (e ▸ hi)) _ _`. Establish `h2 : a j (ξ j) (pr hc s y w) = pr hc s y w`.

Use `DFunLike.congr_fun h.eq w` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply, hw j] at this`. Conclude with `this`. Rewrite using `[pr_insert hc hj, pr_insert hc hj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply (ContinuousLinearMap.adjoint _), hadj, ContinuousLinearMap.smul_apply, h2, inner_smul_right, ih, Finset.prod …`.
-/
theorem inner_pr [CompleteSpace H] [DecidableEq ι] (hw : ∀ i, a i (ξ i) w = w)
    (hadj : ∀ i y y', ContinuousLinearMap.adjoint (a i y') * a i y = ⟪y', y⟫_ℂ • a i (ξ i))
    (s : Finset ι) (y y' : ∀ i, Hs i) :
    ⟪pr hc s y' w, pr hc s y w⟫_ℂ = (∏ i ∈ s, ⟪y' i, y i⟫_ℂ) * ⟪w, w⟫_ℂ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have h := commute_pr hc (C := a j (ξ j)) (s := s) (y := y) fun i hi =>
      hc j i (fun e => hj (e ▸ hi)) _ _
    have h2 : a j (ξ j) (pr hc s y w) = pr hc s y w := by
      have := DFunLike.congr_fun h.eq w
      simp only [ContinuousLinearMap.mul_apply, hw j] at this
      exact this
    rw [pr_insert hc hj, pr_insert hc hj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply (ContinuousLinearMap.adjoint _), hadj,
      ContinuousLinearMap.smul_apply, h2, inner_smul_right, ih, Finset.prod_insert hj, mul_assoc]

open Classical in

def pureVec (ξ : ∀ i, Hs i) (w : H) (y : ∀ i, Hs i) : H :=
  if h : {i | y i ≠ ξ i}.Finite then pr hc h.toFinset y w else 0

/- English proof (translation)
Establish `hy' : {i | y i ≠ ξ i}.Finite` using `hy`. Rewrite using `[pureVec, dif_pos hy']`. Establish `hsub : hy'.toFinset ⊆ s` using `fun i hi => by`. Assume the negation of the conclusion as `hn`. Conclude with `(hy'.mem_toFinset.1 hi) (hs i hn)`.

Rewrite using `[← Finset.union_eq_right.2 hsub]`. Use `(pr_union_apply hc hw hy'.toFinset s (y := y) fun i _ hi => ?_).symm using 3` and compare the differences between its conclusion and the goal. Assume the negation of the conclusion as `hn`. Conclude with `hi (hy'.mem_toFinset.2 hn)`.
-/
theorem pureVec_eq [DecidableEq ι] (hw : ∀ i, a i (ξ i) w = w) {y : ∀ i, Hs i} (hy : Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y) {s : Finset ι}
    (hs : ∀ i ∉ s, y i = ξ i) : pureVec hc ξ w y = pr hc s y w := by
  have hy' : {i | y i ≠ ξ i}.Finite := hy
  rw [pureVec, dif_pos hy']
  have hsub : hy'.toFinset ⊆ s := fun i hi => by
    by_contra hn
    exact (hy'.mem_toFinset.1 hi) (hs i hn)
  rw [← Finset.union_eq_right.2 hsub]
  convert (pr_union_apply hc hw hy'.toFinset s (y := y) fun i _ hi => ?_).symm using 3
  by_contra hn
  exact hi (hy'.mem_toFinset.2 hn)

variable {p : ∀ i, G →* Γ i} {e : ∀ i, Γ i →* G} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {π : G →* (H →L[ℂ] H)}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on generalizing g with`. Consider the case `empty => exact ⟨g, by simp, by simp, by simp⟩`. Consider the case `insert v s hv ih => set g' := (e v (p v g))⁻¹ * g with hg'`. Establish `h1 : p v g' = 1` using `by simp [hg', hpe]`. Establish `h2 : ∀ u, u ≠ v → p u g' = p u g` using `fun u hu => by simp [hg', hpe' v u hu.symm]`.

Take `⟨k, hk1, hk2, hk3⟩` from `ih g'`. Use `⟨k, fun i hi => ?_, fun i hi => ?_, fun y => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Rewrite using `[hk2 i hv, h1]`. Conclude with `hk1 i hi`.

Rewrite using `[hk2 i fun h => hi (Finset.mem_insert_of_mem h), h2 i fun h => hi (h ▸ Finset.mem_insert_self _ _)]`. Establish `e1 : π g = π (e v (p v g)) * π g'` using `by rw [← map_mul, hg', mul_inv_cancel_left]`. Establish `e2 : pr hc s (fun i => δ i (p i g') (y i)) = pr hc s (fun i => δ i (p i g) (y i))` using `pr_congr hc fun i hi => by rw [h2 i fun h => hv (h ▸ hi)]`. Rewrite using `[pr_insert hc hv, pr_insert hc hv, e1, mul_assoc, ← mul_assoc (π g'), (hcomm v g' h1 (y v)).eq, mul_assoc, hk3 y, e2, ← mul_assoc, hrep, mul_assoc]`.
-/
theorem exists_off [DecidableEq ι] (hpe : ∀ i x, p i (e i x) = x) (hpe' : ∀ i j, i ≠ j → ∀ x, p j (e i x) = 1)
    (hcomm : ∀ v g, p v g = 1 → ∀ y, Commute (π g) (a v y))
    (hrep : ∀ i x y, π (e i x) * a i y = a i (δ i x y)) (s : Finset ι) (g : G) :
    ∃ k, (∀ i ∈ s, p i k = 1) ∧ (∀ i ∉ s, p i k = p i g) ∧
      ∀ y, π g * pr hc s y = pr hc s (fun i => δ i (p i g) (y i)) * π k := by
  induction s using Finset.induction_on generalizing g with
  | empty => exact ⟨g, by simp, by simp, by simp⟩
  | insert v s hv ih =>
    set g' := (e v (p v g))⁻¹ * g with hg'
    have h1 : p v g' = 1 := by simp [hg', hpe]
    have h2 : ∀ u, u ≠ v → p u g' = p u g := fun u hu => by simp [hg', hpe' v u hu.symm]
    obtain ⟨k, hk1, hk2, hk3⟩ := ih g'
    refine ⟨k, fun i hi => ?_, fun i hi => ?_, fun y => ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hk2 i hv, h1]
      · exact hk1 i hi
    · rw [hk2 i fun h => hi (Finset.mem_insert_of_mem h), h2 i fun h => hi (h ▸ Finset.mem_insert_self _ _)]
    · have e1 : π g = π (e v (p v g)) * π g' := by rw [← map_mul, hg', mul_inv_cancel_left]
      have e2 : pr hc s (fun i => δ i (p i g') (y i)) = pr hc s (fun i => δ i (p i g) (y i)) :=
        pr_congr hc fun i hi => by rw [h2 i fun h => hv (h ▸ hi)]
      rw [pr_insert hc hv, pr_insert hc hv, e1, mul_assoc, ← mul_assoc (π g'), (hcomm v g' h1 (y v)).eq, mul_assoc,
        hk3 y, e2, ← mul_assoc, hrep, mul_assoc]

include hc in

/- English proof (translation)
Establish `hfix : ∀ g, ∀ᶠ i in Filter.cofinite, δ i (p i g) (ξ i) = ξ i` using `fun g => by`. Take `⟨s₀, h, -⟩` from `hk g`. Conclude with `Filter.eventually_cofinite.2 (s₀.finite_toSet.subset fun i hi => by`. Assume the negation of the conclusion as `hn`. Conclude with `hi (h i hn))`.

Establish `happly : ∀ g y, Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y → π g (pureVec hc ξ w y) = pureVec hc ξ w fun i => δ i (p i g) (y i)` using `fun g y hy => by`. Take `⟨s₀, h0, h1⟩` from `hk g`. Establish `hy' : {i | y i ≠ ξ i}.Finite` using `hy`. Use `set s := s₀ ∪ hy'.toFinset with hs`. Establish `hoff : ∀ i ∉ s, y i = ξ i` using `fun i hi => by`.

Assume the negation of the conclusion as `hn`. Conclude with `hi (Finset.mem_union_right _ (hy'.mem_toFinset.2 hn))`. Take `⟨k, hk1, hk2, hk3⟩` from `exists_off hc hpe hpe' hcomm hrep s g`. Establish `hr` using `restr_map (f := fun i => δ i (p i g)) (hfix g) hy`. Rewrite using `[pureVec_eq hc hw hy hoff, pureVec_eq hc hw hr (s := s) fun i hi => by`.

Rewrite using `[hoff i hi]`. Conclude with `h0 i fun h => hi (Finset.mem_union_left _ h)]`. Use `DFunLike.congr_fun (hk3 y) w` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`. Rewrite using `[this, h1 s Finset.subset_union_left k hk1 hk2]`.

Establish `hself : pureVec hc ξ w ξ = w`. Rewrite using `[pureVec_eq hc hw (restr_self ξ) (s := ∅) fun _ _ => rfl]`. Simplify using the standard rewrite rules. Use `⟨pureVec hc ξ w, .of_forall hξ, hfix, fun y y' hy hy' => ?_, ?_, happly⟩` and prove the remaining obligations. Establish `hy1 : {i | y i ≠ ξ i}.Finite` using `hy`.

Establish `hy2 : {i | y' i ≠ ξ i}.Finite` using `hy'`. Use `set s := hy1.toFinset ∪ hy2.toFinset with hs`. Establish `h1 : ∀ i ∉ s, y i = ξ i` using `fun i hi => by`. Assume the negation of the conclusion as `hn`. Conclude with `hi (Finset.mem_union_left _ (hy1.mem_toFinset.2 hn))`.

Establish `h2 : ∀ i ∉ s, y' i = ξ i` using `fun i hi => by`. Assume the negation of the conclusion as `hn`. Conclude with `hi (Finset.mem_union_right _ (hy2.mem_toFinset.2 hn))`. Rewrite using `[pureVec_eq hc hw hy h1, pureVec_eq hc hw hy' h2, inner_pr hc hw hadj, inner_self_eq_norm_sq_to_K, hw1, finprod_eq_prod_of_mulSupport_subset (s := s)]`. Simplify using the standard rewrite rules.

Introduce `i hi`. Assume the negation of the conclusion as `hn`. Apply `hi` to reduce the goal to its premises. Establish `hn' : i ∉ s` using `hn`. Simplify using `only [h1 i hn', h2 i hn', inner_self_eq_norm_sq_to_K, hξ i]`.

Simplify using the standard rewrite rules. Use `set D := Submodule.span ℂ {v | ∃ y, Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y ∧ v = pureVec hc ξ w y} with hD`. Establish `hinv : ∀ g, ∀ v ∈ D, π g v ∈ D` using `fun g v hv => by`. Establish `hle : D ≤ D.comap (π g : H →ₗ[ℂ] H)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `Submodule.subset_span ⟨_, restr_map (f := fun i => δ i (p i g)) (hfix g) hy, happly g y hy⟩)`. Conclude with `hle hv`. Break down `hπ.2 _ (isSubrep_topologicalClosure hinv) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hm : w ∈ D.topologicalClosure` using `Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ξ, restr_self ξ, hself.symm⟩)`.

Rewrite `hm` using `[h, Submodule.mem_bot]`. Simplify using `[hm] at hw1`. Conclude with `h`.
-/
theorem exists_isRestrTensor [CompleteSpace H] (hπ : IsTopIrreducible π) (hξ : ∀ i, ‖ξ i‖ = 1) (hw1 : ‖w‖ = 1)
    (hw : ∀ i, a i (ξ i) w = w)
    (hadj : ∀ i y y', ContinuousLinearMap.adjoint (a i y') * a i y = ⟪y', y⟫_ℂ • a i (ξ i))
    (hpe : ∀ i x, p i (e i x) = x) (hpe' : ∀ i j, i ≠ j → ∀ x, p j (e i x) = 1)
    (hcomm : ∀ v g, p v g = 1 → ∀ y, Commute (π g) (a v y))
    (hrep : ∀ i x y, π (e i x) * a i y = a i (δ i x y))
    (hk : ∀ g, ∃ s₀ : Finset ι, (∀ i ∉ s₀, δ i (p i g) (ξ i) = ξ i) ∧ ∀ s, s₀ ⊆ s → ∀ k, (∀ i ∈ s, p i k = 1) →
      (∀ i ∉ s, p i k = p i g) → π k w = w) :
    ∃ B, IsRestrTensor p δ ξ π B := by
  classical
  have hfix : ∀ g, ∀ᶠ i in Filter.cofinite, δ i (p i g) (ξ i) = ξ i := fun g => by
    obtain ⟨s₀, h, -⟩ := hk g
    exact Filter.eventually_cofinite.2 (s₀.finite_toSet.subset fun i hi => by
      by_contra hn
      exact hi (h i hn))
  have happly : ∀ g y, Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y →
      π g (pureVec hc ξ w y) = pureVec hc ξ w fun i => δ i (p i g) (y i) := fun g y hy => by
    obtain ⟨s₀, h0, h1⟩ := hk g
    have hy' : {i | y i ≠ ξ i}.Finite := hy
    set s := s₀ ∪ hy'.toFinset with hs
    have hoff : ∀ i ∉ s, y i = ξ i := fun i hi => by
      by_contra hn
      exact hi (Finset.mem_union_right _ (hy'.mem_toFinset.2 hn))
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_off hc hpe hpe' hcomm hrep s g
    have hr := restr_map (f := fun i => δ i (p i g)) (hfix g) hy
    rw [pureVec_eq hc hw hy hoff, pureVec_eq hc hw hr (s := s) fun i hi => by
      rw [hoff i hi]; exact h0 i fun h => hi (Finset.mem_union_left _ h)]
    have := DFunLike.congr_fun (hk3 y) w
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, h1 s Finset.subset_union_left k hk1 hk2]
  have hself : pureVec hc ξ w ξ = w := by
    rw [pureVec_eq hc hw (restr_self ξ) (s := ∅) fun _ _ => rfl]
    simp
  refine ⟨pureVec hc ξ w, .of_forall hξ, hfix, fun y y' hy hy' => ?_, ?_, happly⟩
  · have hy1 : {i | y i ≠ ξ i}.Finite := hy
    have hy2 : {i | y' i ≠ ξ i}.Finite := hy'
    set s := hy1.toFinset ∪ hy2.toFinset with hs
    have h1 : ∀ i ∉ s, y i = ξ i := fun i hi => by
      by_contra hn
      exact hi (Finset.mem_union_left _ (hy1.mem_toFinset.2 hn))
    have h2 : ∀ i ∉ s, y' i = ξ i := fun i hi => by
      by_contra hn
      exact hi (Finset.mem_union_right _ (hy2.mem_toFinset.2 hn))
    rw [pureVec_eq hc hw hy h1, pureVec_eq hc hw hy' h2, inner_pr hc hw hadj,
      inner_self_eq_norm_sq_to_K, hw1, finprod_eq_prod_of_mulSupport_subset (s := s)]
    · simp
    · intro i hi
      by_contra hn
      apply hi
      have hn' : i ∉ s := hn
      simp only [h1 i hn', h2 i hn', inner_self_eq_norm_sq_to_K, hξ i]
      simp
  · set D := Submodule.span ℂ {v | ∃ y, Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y ∧ v = pureVec hc ξ w y} with hD
    have hinv : ∀ g, ∀ v ∈ D, π g v ∈ D := fun g v hv => by
      have hle : D ≤ D.comap (π g : H →ₗ[ℂ] H) := Submodule.span_le.2 (by
        rintro _ ⟨y, hy, rfl⟩
        exact Submodule.subset_span ⟨_, restr_map (f := fun i => δ i (p i g)) (hfix g) hy, happly g y hy⟩)
      exact hle hv
    rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with h | h
    · exfalso
      have hm : w ∈ D.topologicalClosure :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ξ, restr_self ξ, hself.symm⟩)
      rw [h, Submodule.mem_bot] at hm
      simp [hm] at hw1
    · exact h

end Tensor

section Select

variable {ι H : Type} {X : ι → Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [∀ i, NormedAddCommGroup (X i)] [∀ i, InnerProductSpace ℂ (X i)]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, w₀, hw₀, h₀, by simp⟩`. Consider the case `insert j s hj ih`. Take `⟨ξ, w, hw, hI, hξ⟩` from `ih fun i hi => hstep i (Finset.mem_insert_of_mem hi)`. Take `⟨x, hx1, hx⟩` from `hsel j w hw`.

Use `⟨Function.update ξ j x, A j x x w, hx, hstep j (Finset.mem_insert_self _ _) x w hI, fun i hi => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Use `⟨by simpa using hx1, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.update_self]`.

Rewrite using `[← ContinuousLinearMap.mul_apply, hproj i x hx1]`. Establish `hi' : i ∈ s` using `(Finset.mem_insert.1 hi).resolve_left e`. Simplify using `only [Function.update_of_ne e]`. Use `⟨(hξ i hi').1, ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun (hc i j e (ξ i) (ξ i) x x).eq w` as an intermediate fact.

Simplify using `only [ContinuousLinearMap.mul_apply, (hξ i hi').2] at this`. Conclude with `this`.
-/
theorem exists_fixed_of_finset [DecidableEq ι] {A : ∀ i, X i → X i → (H →L[ℂ] H)}
    (hc : ∀ i j, i ≠ j → ∀ y ξ y' ξ', Commute (A i y ξ) (A j y' ξ'))
    (hsel : ∀ i (w : H), w ≠ 0 → ∃ ξ, ‖ξ‖ = 1 ∧ A i ξ ξ w ≠ 0)
    (hproj : ∀ i ξ, ‖ξ‖ = 1 → A i ξ ξ * A i ξ ξ = A i ξ ξ)
    (Inv : H → Prop) (s : Finset ι) (hstep : ∀ i ∈ s, ∀ ξ w, Inv w → Inv (A i ξ ξ w)) {w₀ : H} (h₀ : Inv w₀)
    (hw₀ : w₀ ≠ 0) :
    ∃ (ξ : ∀ i, X i) (w : H), w ≠ 0 ∧ Inv w ∧ ∀ i ∈ s, ‖ξ i‖ = 1 ∧ A i (ξ i) (ξ i) w = w := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, w₀, hw₀, h₀, by simp⟩
  | insert j s hj ih =>
    obtain ⟨ξ, w, hw, hI, hξ⟩ := ih fun i hi => hstep i (Finset.mem_insert_of_mem hi)
    obtain ⟨x, hx1, hx⟩ := hsel j w hw
    refine ⟨Function.update ξ j x, A j x x w, hx, hstep j (Finset.mem_insert_self _ _) x w hI, fun i hi => ?_⟩
    by_cases e : i = j
    · subst e
      refine ⟨by simpa using hx1, ?_⟩
      simp only [Function.update_self]
      rw [← ContinuousLinearMap.mul_apply, hproj i x hx1]
    · have hi' : i ∈ s := (Finset.mem_insert.1 hi).resolve_left e
      simp only [Function.update_of_ne e]
      refine ⟨(hξ i hi').1, ?_⟩
      have := DFunLike.congr_fun (hc i j e (ξ i) (ξ i) x x).eq w
      simp only [ContinuousLinearMap.mul_apply, (hξ i hi').2] at this
      exact this

end Select

end GlobalTheory.CompanionTheory.RestT

end
