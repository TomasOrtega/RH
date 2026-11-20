import Mathlib

open Module

namespace GlobalTheory.DualFrameSpan

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[LinearMap.sum_apply]`.
-/
lemma sum_comp' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x; simp [LinearMap.sum_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[LinearMap.sum_apply]`.
-/
lemma comp_sum' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x; simp [LinearMap.sum_apply]

/- English proof (translation)
Use `set b := stdOrthonormalBasis ℂ H`. Rewrite `h` using `[LinearMap.trace_eq_sum_inner _ b]`. Establish `h' : ∀ i, (inner ℂ (b i) ((LinearMap.adjoint B ∘ₗ B) (b i)) : ℂ) = ((‖B (b i)‖ ^ 2 : ℝ) : ℂ)`. Introduce `i`. Rewrite using `[LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Apply the tactic sequence `first | rfl | simp | norm_cast`. Rewrite `h` using `[h']`. Establish `h2 : (∑ i, ‖B (b i)‖ ^ 2 : ℝ) = 0` using `by exact_mod_cast h`. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h2`.

Apply `b.toBasis.ext` to reduce the goal to its premises. Introduce `i`. Use `h3 i (Finset.mem_univ _)` as an intermediate fact. Simplify using `using this`.
-/
lemma eq_zero_of_trace_adjoint_comp_self (B : H →ₗ[ℂ] H)
    (h : LinearMap.trace ℂ H (LinearMap.adjoint B ∘ₗ B) = 0) : B = 0 := by
  set b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, (inner ℂ (b i) ((LinearMap.adjoint B ∘ₗ B) (b i)) : ℂ)
      = ((‖B (b i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast; first | rfl | simp | norm_cast
  simp_rw [h'] at h
  have h2 : (∑ i, ‖B (b i)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h2
  apply b.toBasis.ext
  intro i
  have := h3 i (Finset.mem_univ _)
  simpa using this

noncomputable def pairing (W : Submodule ℂ (H →ₗ[ℂ] H)) : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ (fun X Y : W => LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)))
    (fun x y z => by simp [LinearMap.add_comp]) (fun c x y => by simp [LinearMap.smul_comp])
    (fun x y z => by simp [LinearMap.comp_add]) (fun c x y => by simp [LinearMap.comp_smul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pairing_apply (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := rfl

/- English proof (translation)
Establish `key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0`. Introduce `y hy`. Use `hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩` as an intermediate fact. Rewrite `this` using `[pairing_apply]`. Conclude with `Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)`.

Use `⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩` and prove the remaining obligations. Rewrite using `[pairing_apply, LinearMap.trace_comp_comm']`. Conclude with `hx y`.
-/
lemma pairing_nondegenerate (W : Submodule ℂ (H →ₗ[ℂ] H))
    (hW : ∀ X ∈ W, LinearMap.adjoint X ∈ W) : (pairing W).Nondegenerate := by
  have key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0 := by
    intro y hy
    have := hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩
    rw [pairing_apply] at this
    exact Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)
  refine ⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact hx y

section span

variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))

/- English proof (translation)
Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Take `⟨g', hg', he⟩` from `hadj g hg`. Rewrite using `[he]`.

Conclude with `Submodule.subset_span ⟨g', hg', rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
lemma adjoint_mem_span (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', he⟩ := hadj g hg
    rw [he]; exact Submodule.subset_span ⟨g', hg', rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Rewrite using `[← hρ g hg h hh]`. Conclude with `Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [LinearMap.add_comp]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.smul_comp]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
lemma comp_mem_span (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hρ g hg h hh]; exact Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ hx

end span

/- English proof (translation)
Introduce `G H _ _ _ _ K ρ hmul hρ hadj`. Take `⟨t, hts, hsp, hli⟩` from `exists_linearIndependent ℂ (ρ '' K)`. Use `set W := Submodule.span ℂ (ρ '' K) with hWdef`. Establish `hWt : Submodule.span ℂ (Set.range ((↑) : t → (H →ₗ[ℂ] H))) = W`. Rewrite using `[Subtype.range_coe]`.

Conclude with `hsp`. Use `haveI : Finite t := hli.finite`. Use `letI : Fintype t := Fintype.ofFinite t`. Set `b0 : Basis t ℂ W` to `(Basis.span hli).map (LinearEquiv.ofEq _ _ hWt)`. Set `e` to `Fintype.equivFin t`.

Set `b : Basis (Fin (Fintype.card t)) ℂ W` to `b0.reindex e`. Establish `hb : ∀ j, ((b j : W) : H →ₗ[ℂ] H) = ((e.symm j : t) : H →ₗ[ℂ] H)`. Introduce `j`. Simplify using `[b, b0, Basis.span_apply]`. Establish `hbK : ∀ j, ∃ g ∈ K, ρ g = (b j : H →ₗ[ℂ] H)` using `fun j => by`.

Rewrite using `[hb]`. Conclude with `hts (e.symm j).2`. Use `choose k hkK hk using hbK`. Establish `hnd` using `pairing_nondegenerate W (fun X hX => adjoint_mem_span K ρ hadj hX)`. Set `D` to `(pairing W).dualBasis hnd b`.

Establish `expand : ∀ X ∈ W, X = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ X) • (D j : H →ₗ[ℂ] H)`. Introduce `X hX`. Establish `h1` using `congrArg Subtype.val (D.sum_repr ⟨X, hX⟩)`. Rewrite `h1` using `[Submodule.coe_sum]`. Express the relevant statement in the definitionally equal form `_ = X at h1`.

Use `conv_lhs => rw [← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply, pairing_apply, hk, LinearMap.trace_comp_comm' (b j : H →ₗ[ℂ] H) X]`. Establish `hdual : ∀ i j, LinearMap.trace ℂ H (ρ (k i) ∘ₗ (D j : H →ₗ[ℂ] H)) = if i = j then 1 else 0`. Introduce `i j`.

Rewrite using `[hk, LinearMap.trace_comp_comm']`. Conclude with `LinearMap.BilinForm.apply_dualBasis_left hnd b j i`. Use `⟨Fintype.card t, k, fun j => (D j : H →ₗ[ℂ] H), hkK, ?_, ?_⟩` and prove the remaining obligations. Introduce `A g hg set A' := ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) • (D j : H →ₗ[ℂ] H) with hA'`. Establish `hbi : ∀ i, LinearMap.trace ℂ H (ρ (k i) ∘ₗ A') = LinearMap.trace ℂ H (ρ (k i) ∘ₗ A)`.

Introduce `i`. Simplify using `only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `hvan : ∀ C ∈ W, LinearMap.trace ℂ H (C ∘ₗ A') = LinearMap.trace ℂ H (C ∘ₗ A)`. Introduce `C hC`. Establish `h1` using `congrArg Subtype.val (b.sum_repr ⟨C, hC⟩)`.

Rewrite `h1` using `[Submodule.coe_sum]`. Express the relevant statement in the definitionally equal form `_ = C at h1`. Rewrite using `[← h1]`. Simplify using `only [Submodule.coe_smul, sum_comp', LinearMap.smul_comp, map_sum, map_smul, ← hk, hbi]`. Rewrite using `[← hvan (ρ g) (Submodule.subset_span ⟨g, hg, rfl⟩)]`.

Simplify using `only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul]`. Introduce `i h hh`. Conclude with `expand _ (comp_mem_span K ρ hmul hρ hh (D i).2)`.
-/
theorem dual_frame : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  intro G H _ _ _ _ K ρ hmul hρ hadj
  classical
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent ℂ (ρ '' K)
  set W := Submodule.span ℂ (ρ '' K) with hWdef
  have hWt : Submodule.span ℂ (Set.range ((↑) : t → (H →ₗ[ℂ] H))) = W := by
    rw [Subtype.range_coe]; exact hsp
  haveI : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b0 : Basis t ℂ W := (Basis.span hli).map (LinearEquiv.ofEq _ _ hWt)
  let e := Fintype.equivFin t
  let b : Basis (Fin (Fintype.card t)) ℂ W := b0.reindex e
  have hb : ∀ j, ((b j : W) : H →ₗ[ℂ] H) = ((e.symm j : t) : H →ₗ[ℂ] H) := by
    intro j; simp [b, b0, Basis.span_apply]
  have hbK : ∀ j, ∃ g ∈ K, ρ g = (b j : H →ₗ[ℂ] H) := fun j => by
    rw [hb]; exact hts (e.symm j).2
  choose k hkK hk using hbK
  have hnd := pairing_nondegenerate W (fun X hX => adjoint_mem_span K ρ hadj hX)
  let D := (pairing W).dualBasis hnd b
  have expand : ∀ X ∈ W, X = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ X) • (D j : H →ₗ[ℂ] H) := by
    intro X hX
    have h1 := congrArg Subtype.val (D.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    change _ = X at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply, pairing_apply, hk,
      LinearMap.trace_comp_comm' (b j : H →ₗ[ℂ] H) X]
  have hdual : ∀ i j, LinearMap.trace ℂ H (ρ (k i) ∘ₗ (D j : H →ₗ[ℂ] H)) = if i = j then 1 else 0 := by
    intro i j
    rw [hk, LinearMap.trace_comp_comm']
    exact LinearMap.BilinForm.apply_dualBasis_left hnd b j i
  refine ⟨Fintype.card t, k, fun j => (D j : H →ₗ[ℂ] H), hkK, ?_, ?_⟩
  · intro A g hg
    set A' := ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) • (D j : H →ₗ[ℂ] H) with hA'
    have hbi : ∀ i, LinearMap.trace ℂ H (ρ (k i) ∘ₗ A') = LinearMap.trace ℂ H (ρ (k i) ∘ₗ A) := by
      intro i
      simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, hdual, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hvan : ∀ C ∈ W, LinearMap.trace ℂ H (C ∘ₗ A') = LinearMap.trace ℂ H (C ∘ₗ A) := by
      intro C hC
      have h1 := congrArg Subtype.val (b.sum_repr ⟨C, hC⟩)
      rw [Submodule.coe_sum] at h1
      change _ = C at h1
      rw [← h1]
      simp only [Submodule.coe_smul, sum_comp', LinearMap.smul_comp, map_sum, map_smul, ← hk, hbi]
    rw [← hvan (ρ g) (Submodule.subset_span ⟨g, hg, rfl⟩)]
    simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul]
  · intro i h hh
    exact expand _ (comp_mem_span K ρ hmul hρ hh (D i).2)

end GlobalTheory.DualFrameSpan
