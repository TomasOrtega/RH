import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `K L _ _ _ _ _ n M W`. Take `⟨m, ω, η, hη, hsum⟩` from `exists_trace_dual_system K L`. Set `F : Fin m → (Fin n → L) → (Fin n → K)` to `fun i y j => Algebra.trace K L (η i * y j)`. Establish `Fadd : ∀ i y z, F i (y + z) = F i y + F i z`. Introduce `i y z`.

Use function extensionality and compare the values at `j`. Simplify using `[F, mul_add, map_add]`. Establish `Fzero : ∀ i, F i 0 = 0` using `by intro i; funext j; simp [F]`. Establish `hint : ∀ i (a : 𝓞 L), ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Algebra.trace K L (η i * a)`. Introduce `i a`.

Establish `h` using `(Submodule.mem_traceDual.mp (hη i)) (a : L) (Submodule.mem_one.mpr ⟨a, rfl⟩)`. Take `⟨c, hc⟩` from `h`. Conclude with `⟨c, by rw [hc, Algebra.traceForm_apply]⟩`. Establish `Ftr : ∀ i (c : L) (x : Fin n → K), F i (c • (fun j => algebraMap K L (x j))) = Algebra.trace K L (η i * c) • x`. Introduce `i c x`.

Use function extensionality and compare the values at `j`. Simplify using `only [F, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm _ (algebraMap K L (x j)), ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]`. Establish `hsm : ∀ (a : 𝓞 L) (v : Fin n → L), a • v = (a : L) • v`. Introduce `a v`.

Use function extensionality and compare the values at `j`. Both sides reduce to the same expression. Establish `hM : ∀ y ∈ Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))), ∀ i (a : 𝓞 L), F i (a • y) ∈ M`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨x, hx, rfl⟩` from `hx`. Introduce `i a`. Take `⟨c, hc⟩` from `hint i a`. Rewrite using `[hsm, Ftr, ← hc, algebraMap_smul]`.

Conclude with `M.smul_mem c hx`. Consider the case `zero => intro i a`. Rewrite using `[smul_zero, Fzero]`. Conclude with `M.zero_mem`. Consider the case `add x y _ _ hx hy => intro i a`.

Rewrite using `[smul_add, Fadd]`. Conclude with `M.add_mem (hx i a) (hy i a)`. Consider the case `smul b x _ hx => intro i a`. Rewrite using `[smul_smul]`. Conclude with `hx i (a * b)`.

Establish `hW : ∀ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))), ∀ i (a : L), F i (a • y) ∈ W`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨x, hx, rfl⟩` from `hx`.

Introduce `i a`. Rewrite using `[Ftr]`. Conclude with `W.smul_mem _ hx`. Consider the case `zero => intro i a`. Rewrite using `[smul_zero, Fzero]`.

Conclude with `W.zero_mem`. Consider the case `add x y _ _ hx hy => intro i a`. Rewrite using `[smul_add, Fadd]`. Conclude with `W.add_mem (hx i a) (hy i a)`. Consider the case `smul b x _ hx => intro i a`.

Rewrite using `[smul_smul]`. Conclude with `hx i (a * b)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `y ⟨hy1, hy2⟩`. Establish `hy2' : y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))` using `hy2`.

Establish `hdec : y = ∑ i, ω i • (fun j => algebraMap K L (F i y j))`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, hsum (y j)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (ω i : L) * _`.

Rewrite using `[mul_comm]`. Rewrite using `[hdec]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i y, ?_, rfl⟩)` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `using hM y hy1 i 1`.

Simplify using `using hW y hy2' i 1`. Use `le_inf (Submodule.span_mono (Set.image_mono fun x hx => hx.1)) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `Submodule.subset_span ⟨x, hx.2, rfl⟩`.
-/
theorem span_inf_span_eq_span_inf_of_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)),
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓
        (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) =
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) ''
        ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  intro K L _ _ _ _ _ n M W
  obtain ⟨m, ω, η, hη, hsum⟩ := exists_trace_dual_system K L
  let F : Fin m → (Fin n → L) → (Fin n → K) := fun i y j => Algebra.trace K L (η i * y j)
  have Fadd : ∀ i y z, F i (y + z) = F i y + F i z := by
    intro i y z; funext j; simp [F, mul_add, map_add]
  have Fzero : ∀ i, F i 0 = 0 := by intro i; funext j; simp [F]
  have hint : ∀ i (a : 𝓞 L), ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Algebra.trace K L (η i * a) := by
    intro i a
    have h := (Submodule.mem_traceDual.mp (hη i)) (a : L) (Submodule.mem_one.mpr ⟨a, rfl⟩)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc, Algebra.traceForm_apply]⟩
  have Ftr : ∀ i (c : L) (x : Fin n → K),
      F i (c • (fun j => algebraMap K L (x j))) = Algebra.trace K L (η i * c) • x := by
    intro i c x; funext j
    simp only [F, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm _ (algebraMap K L (x j)), ← Algebra.smul_def, LinearMap.map_smul,
      smul_eq_mul, mul_comm]
  have hsm : ∀ (a : 𝓞 L) (v : Fin n → L), a • v = (a : L) • v := by
    intro a v; funext j; rfl
  have hM : ∀ y ∈ Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))),
      ∀ i (a : 𝓞 L), F i (a • y) ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      obtain ⟨c, hc⟩ := hint i a
      rw [hsm, Ftr, ← hc, algebraMap_smul]
      exact M.smul_mem c hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact M.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact M.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  have hW : ∀ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))),
      ∀ i (a : L), F i (a • y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      rw [Ftr]
      exact W.smul_mem _ hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact W.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact W.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  apply le_antisymm
  · rintro y ⟨hy1, hy2⟩
    have hy2' : y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))) :=
      hy2
    have hdec : y = ∑ i, ω i • (fun j => algebraMap K L (F i y j)) := by
      funext j
      rw [Finset.sum_apply, hsum (y j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = (ω i : L) * _
      rw [mul_comm]
    rw [hdec]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i y, ?_, rfl⟩)
    refine ⟨?_, ?_⟩
    · simpa using hM y hy1 i 1
    · simpa using hW y hy2' i 1
  · refine le_inf (Submodule.span_mono (Set.image_mono fun x hx => hx.1)) ?_
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx.2, rfl⟩

end GlobalTheory
