import Mathlib
open NumberField
namespace GlobalTheory.TraceDualHom

/- English proof (translation)
Establish `h : ∀ i : Fin a, ∃ t : E, ∀ c : E, Algebra.trace ℚ E (t * c) = φ (Pi.single i c)`. Introduce `i`. Use `⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i), fun c => ?_⟩` and prove the remaining obligations. Use `LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate ℚ E) (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i) c` as an intermediate fact. Conclude with `this`.

Use `choose t ht using h`. Use `⟨∑ i, t i • LinearMap.proj i, fun x => ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← Finset.univ_sum_single x]`. Simplify using `[ht, map_sum]`.
-/
theorem exists_linear_trace_eq (E : Type) [Field E] [NumberField E] (a : ℕ)
    (φ : (Fin a → E) →ₗ[ℚ] ℚ) :
    ∃ l : (Fin a → E) →ₗ[E] E, ∀ x, Algebra.trace ℚ E (l x) = φ x := by
  classical
  have h : ∀ i : Fin a, ∃ t : E, ∀ c : E, Algebra.trace ℚ E (t * c) = φ (Pi.single i c) := by
    intro i
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i), fun c => ?_⟩
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate ℚ E)
      (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i) c
    exact this
  choose t ht using h
  refine ⟨∑ i, t i • LinearMap.proj i, fun x => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single x]
  simp [ht, map_sum]

/- English proof (translation)
Establish `h1 : (δ : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E))` using `(IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩`. Rewrite `h1` using `[coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem]`. Establish `h2 : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite using `[Submodule.mem_traceDual]`. Introduce `c hc`.

Take `⟨o, rfl⟩` from `Submodule.mem_one.1 hc`. Take `⟨m, hm⟩` from `hx o`. Conclude with `⟨m, by simpa using hm.symm⟩`. Conclude with `Submodule.mem_one.1 (h1 x h2)`.
-/
theorem different_mul_mem (E : Type) [Field E] [NumberField E] (x : E)
    (hx : ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * c) = m)
    (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) : ∃ o : 𝓞 E, (o : E) = δ * x := by
  have h1 : (δ : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem] at h1
  have h2 : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro c hc
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hc
    obtain ⟨m, hm⟩ := hx o
    exact ⟨m, by simpa using hm.symm⟩
  exact Submodule.mem_one.1 (h1 x h2)

/- English proof (translation)
Establish `key : ∀ (e : E), ∀ x ∈ Submodule.span ℚ (A : Set (Fin a → E)), e • x ∈ Submodule.span ℚ (A : Set (Fin a → E))`. Introduce `e x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[← (integralBasis E).sum_repr e, Finset.sum_smul]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[integralBasis_apply, algebraMap_smul]`. Conclude with `A.smul_mem _ hx`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul q x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x ∈ Submodule.span E (A : Set (Fin a → E))` using `hA ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)`. Consider the case `smul e x _ hx => exact key e x (hx trivial)`.
-/
theorem rat_span_eq_top (E : Type) [Field E] [NumberField E] (a : ℕ)
    (A : Submodule (𝓞 E) (Fin a → E)) (hA : Submodule.span E (A : Set (Fin a → E)) = ⊤) :
    Submodule.span ℚ (A : Set (Fin a → E)) = ⊤ := by
  have key : ∀ (e : E), ∀ x ∈ Submodule.span ℚ (A : Set (Fin a → E)),
      e • x ∈ Submodule.span ℚ (A : Set (Fin a → E)) := by
    intro e x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [← (integralBasis E).sum_repr e, Finset.sum_smul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [integralBasis_apply, algebraMap_smul]
      exact A.smul_mem _ hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span E (A : Set (Fin a → E)) := hA ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => simp
  | add x y _ _ hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | smul e x _ hx => exact key e x (hx trivial)

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hfg`. Use `haveI : Module.Finite ℤ A := Module.Finite.trans (𝓞 E) A`. Use `haveI : Module.Free ℤ A := inferInstance`. Set `b` to `Module.Free.chooseBasis ℤ A`. Set `f : A →ₗ[ℤ] (Fin a → E)` to `A.subtype.restrictScalars ℤ`.

Establish `hli : LinearIndependent ℤ (f ∘ b)` using `b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 Subtype.val_injective)`. Establish `hliQ : LinearIndependent ℚ (f ∘ b)` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hli`. Establish `hsp : ∀ x, x ∈ Submodule.span ℤ (Set.range (f ∘ b)) ↔ x ∈ A`. Introduce `x`. Rewrite using `[Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`. Introduce `hx`. Conclude with `⟨⟨x, hx⟩, rfl⟩`.

Establish `htop : ⊤ ≤ Submodule.span ℚ (Set.range (f ∘ b))`. Rewrite using `[← rat_span_eq_top E a A hA, Submodule.span_le]`. Introduce `x hx`. Conclude with `Submodule.span_le_restrictScalars ℤ ℚ _ ((hsp x).2 hx)`. Set `B` to `Module.Basis.mk hliQ htop`.

Establish `hB : Set.range B = Set.range (f ∘ b)` using `by simp [B]`. Rewrite using `[← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem]`. Introduce `i`. Take `⟨m, hm⟩` from `hz (B.coord i) (fun x hx => by`. Rewrite `hx` using `[← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem]`.

Take `⟨m, hm⟩` from `hx i`. Conclude with `⟨m, by simpa using hm.symm⟩)`. Conclude with `⟨m, by simpa using hm.symm⟩`.
-/
theorem mem_of_forall_rat_functional (E : Type) [Field E] [NumberField E] (a : ℕ)
    (A : Submodule (𝓞 E) (Fin a → E)) (hfg : A.FG)
    (hA : Submodule.span E (A : Set (Fin a → E)) = ⊤) (z : Fin a → E)
    (hz : ∀ φ : (Fin a → E) →ₗ[ℚ] ℚ, (∀ x ∈ A, ∃ m : ℤ, φ x = m) → ∃ m : ℤ, φ z = m) :
    z ∈ A := by
  haveI : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ A := Module.Finite.trans (𝓞 E) A
  haveI : Module.Free ℤ A := inferInstance
  let b := Module.Free.chooseBasis ℤ A
  let f : A →ₗ[ℤ] (Fin a → E) := A.subtype.restrictScalars ℤ
  have hli : LinearIndependent ℤ (f ∘ b) :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hsp : ∀ x, x ∈ Submodule.span ℤ (Set.range (f ∘ b)) ↔ x ∈ A := by
    intro x
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range (f ∘ b)) := by
    rw [← rat_span_eq_top E a A hA, Submodule.span_le]
    intro x hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ ((hsp x).2 hx)
  let B := Module.Basis.mk hliQ htop
  have hB : Set.range B = Set.range (f ∘ b) := by simp [B]
  rw [← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem]
  intro i
  obtain ⟨m, hm⟩ := hz (B.coord i) (fun x hx => by
    rw [← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem] at hx
    obtain ⟨m, hm⟩ := hx i
    exact ⟨m, by simpa using hm.symm⟩)
  exact ⟨m, by simpa using hm.symm⟩

/- English proof (translation)
Introduce `E _ _ a b A Bm hA _ hAs _ ψ hψ δ hδ y hy`. Use `mem_of_forall_rat_functional E a A hA hAs _ fun φ hφ => ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `exists_linear_trace_eq E a φ`. Take `⟨m, hm⟩` from `hψ (((δ : E) • l).smulRight y) (fun x hx => by`. Take `⟨o, ho⟩` from `different_mul_mem E (l x) (fun c => by`.

Take `⟨m, hm⟩` from `hφ (c • x) (A.smul_mem c hx)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, ← hl, ← algebraMap_smul E c x, map_smul, smul_eq_mul, mul_comm]) δ hδ`. Rewrite using `[LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, ← ho]`. Conclude with `Bm.smul_mem o hy)`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `e : (((δ : E) • l).smulRight y) ∘ₗ ψ = ((((δ : E) • l) ∘ₗ ψ).smulRight y)` using `rfl`. Rewrite `hm` using `[e, LinearMap.trace_smulRight]`. Rewrite using `[← hm, ← hl, ← algebraMap_smul E δ (ψ y), map_smul]`. Both sides reduce to the same expression.
-/
theorem different_smul_mem_of_trace_integral : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (A : Submodule (𝓞 E) (Fin a → E)) (Bm : Submodule (𝓞 E) (Fin b → E)), A.FG → Bm.FG → Submodule.span E (A : Set (Fin a → E)) = ⊤ → Submodule.span E (Bm : Set (Fin b → E)) = ⊤ → ∀ ψ : (Fin b → E) →ₗ[E] (Fin a → E), (∀ T : (Fin a → E) →ₗ[E] (Fin b → E), (∀ x ∈ A, T x ∈ Bm) → ∃ m : ℤ, Algebra.trace ℚ E (LinearMap.trace E _ (T ∘ₗ ψ)) = m) → ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ y ∈ Bm, δ • ψ y ∈ A := by
  intro E _ _ a b A Bm hA _ hAs _ ψ hψ δ hδ y hy
  refine mem_of_forall_rat_functional E a A hA hAs _ fun φ hφ => ?_
  obtain ⟨l, hl⟩ := exists_linear_trace_eq E a φ
  obtain ⟨m, hm⟩ := hψ (((δ : E) • l).smulRight y) (fun x hx => by
    obtain ⟨o, ho⟩ := different_mul_mem E (l x) (fun c => by
      obtain ⟨m, hm⟩ := hφ (c • x) (A.smul_mem c hx)
      refine ⟨m, ?_⟩
      rw [← hm, ← hl, ← algebraMap_smul E c x, map_smul, smul_eq_mul, mul_comm]) δ hδ
    rw [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, ← ho]
    exact Bm.smul_mem o hy)
  refine ⟨m, ?_⟩
  have e : (((δ : E) • l).smulRight y) ∘ₗ ψ = ((((δ : E) • l) ∘ₗ ψ).smulRight y) := rfl
  rw [e, LinearMap.trace_smulRight] at hm
  rw [← hm, ← hl, ← algebraMap_smul E δ (ψ y), map_smul]
  rfl

end GlobalTheory.TraceDualHom
