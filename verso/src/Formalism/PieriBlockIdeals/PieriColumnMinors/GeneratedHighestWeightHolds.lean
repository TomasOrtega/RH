import Formalism.PieriBlockIdeals.StatementLP

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

section

variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}

inductive LowW (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : N → Prop
  | base (v : N) : IsHW T κ v → LowW T κ v
  | step (a b : Fin q) (x : N) : b < a → LowW T κ x → LowW T κ (T a b x)

def lowSpan (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : Submodule K N :=
  Submodule.span K {x | LowW T κ x}

/- English proof (translation)
Introduce `y hy`. Establish `: (lowSpan T κ).map (T c d) ≤ lowSpan T κ`. Unfold `lowSpan`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `Submodule.subset_span (LowW.step c d x h hx)`. Conclude with `this (Submodule.mem_map_of_mem hy)`.
-/
theorem lowSpan_low (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) (c d : Fin q) (h : d < c) :
    ∀ y ∈ lowSpan T κ, T c d y ∈ lowSpan T κ := by
  intro y hy
  have : (lowSpan T κ).map (T c d) ≤ lowSpan T κ := by
    unfold lowSpan
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span (LowW.step c d x h hx)
  exact this (Submodule.mem_map_of_mem hy)

/- English proof (translation)
Proceed by induction on `hx with`. Consider the case `base v hv`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Rewrite using `[hv.1 a b h]`.

Conclude with `Submodule.zero_mem _`. Substitute `h` using the available equality. Rewrite using `[hv.2 a]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (LowW.base v hv))`. Conclude with `Submodule.subset_span (LowW.step a b v h (LowW.base v hv))`.

Consider the case `step c d x hdc _ ih`. Introduce `a b`. Establish `h` using `LinearMap.congr_fun (hT a b c d) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Establish `e : T a b (T c d x) = T c d (T a b x) + (((if b = c then T a d else 0 : Module.End K N) x) - ((if d = a then T c b else 0 : Module.End K N) x))`.

Rewrite using `[← h]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `Submodule.add_mem _ (lowSpan_low T κ c d hdc _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `ih a d`. Simplify using the standard rewrite rules. Use `split_ifs`. Conclude with `ih c b`. Simplify using the standard rewrite rules.
-/
theorem lowW_all (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) (x : N) (hx : LowW T κ x) :
    ∀ a b, T a b x ∈ lowSpan T κ := by
  induction hx with
  | base v hv =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.1 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.2 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (LowW.base v hv))
    · exact Submodule.subset_span (LowW.step a b v h (LowW.base v hv))
  | step c d x hdc _ ih =>
    intro a b
    have h := LinearMap.congr_fun (hT a b c d) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have e : T a b (T c d x) = T c d (T a b x) +
        (((if b = c then T a d else 0 : Module.End K N) x) - ((if d = a then T c b else 0 : Module.End K N) x)) := by
      rw [← h]; abel
    rw [e]
    refine Submodule.add_mem _ (lowSpan_low T κ c d hdc _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih a d
      · simp
    · split_ifs
      · exact ih c b
      · simp

/- English proof (translation)
Introduce `a b y hy`. Establish `: (lowSpan T κ).map (T a b) ≤ lowSpan T κ`. Rewrite using `[lowSpan, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `lowW_all T hT κ x hx a b`.

Conclude with `this (Submodule.mem_map_of_mem hy)`.
-/
theorem lowSpan_stab (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) : Stab T (lowSpan T κ) := by
  intro a b y hy
  have : (lowSpan T κ).map (T a b) ≤ lowSpan T κ := by
    rw [lowSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact lowW_all T hT κ x hx a b
  exact this (Submodule.mem_map_of_mem hy)

end

/- English proof (translation)
Introduce `K N q _ _ _ _ _ T B hF κ hgen v μ hv hhw`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, μ a ≠ κ a := by`. Assume the negation of the conclusion as `hcon`. Conclude with `hne (funext fun a => by_contra fun h => hcon ⟨a, h⟩)`.

Establish `htop : lowSpan T κ = ⊤` using `hgen _ (lowSpan_stab T hF.gl κ) (fun w hw => Submodule.subset_span (LowW.base w hw))`. Establish `horth : ∀ x, LowW T κ x → B v x = 0`. Introduce `x hx`. Consider the cases of `hx with`. Consider the case `base _ hw`.

Establish `h` using `hF.adj a a v x`. Rewrite `h` using `[hhw.2 a, hw.2 a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `h2 : (μ a - κ a) * B v x = 0` using `by rw [sub_mul, h, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)`. Consider the case `step c d y hdc _`.

Rewrite using `[← hF.adj d c v y, hhw.1 d c hdc, map_zero, LinearMap.zero_apply]`. Establish `hall : ∀ y ∈ lowSpan T κ, B v y = 0`. Introduce `y hy`. Establish `: lowSpan T κ ≤ LinearMap.ker (B v)`. Rewrite using `[lowSpan, Submodule.span_le]`.

Introduce `x hx`. Conclude with `LinearMap.mem_ker.2 (horth x hx)`. Conclude with `LinearMap.mem_ker.1 (this hy)`. Establish `h0 : B v v = 0` using `hall v (by rw [htop]; exact Submodule.mem_top)`. Conclude with `absurd (hF.pos v hv) (by rw [h0]; exact lt_irrefl _)`.
-/
theorem generatedHighestWeight_holds : GeneratedHW := by
  intro K N q _ _ _ _ _ T B hF κ hgen v μ hv hhw
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ κ a := by
    by_contra hcon
    exact hne (funext fun a => by_contra fun h => hcon ⟨a, h⟩)
  have htop : lowSpan T κ = ⊤ :=
    hgen _ (lowSpan_stab T hF.gl κ) (fun w hw => Submodule.subset_span (LowW.base w hw))
  have horth : ∀ x, LowW T κ x → B v x = 0 := by
    intro x hx
    cases hx with
    | base _ hw =>
      have h := hF.adj a a v x
      rw [hhw.2 a, hw.2 a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
      have h2 : (μ a - κ a) * B v x = 0 := by rw [sub_mul, h, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
    | step c d y hdc _ =>
      rw [← hF.adj d c v y, hhw.1 d c hdc, map_zero, LinearMap.zero_apply]
  have hall : ∀ y ∈ lowSpan T κ, B v y = 0 := by
    intro y hy
    have : lowSpan T κ ≤ LinearMap.ker (B v) := by
      rw [lowSpan, Submodule.span_le]
      intro x hx
      exact LinearMap.mem_ker.2 (horth x hx)
    exact LinearMap.mem_ker.1 (this hy)
  have h0 : B v v = 0 := hall v (by rw [htop]; exact Submodule.mem_top)
  exact absurd (hF.pos v hv) (by rw [h0]; exact lt_irrefl _)

end Formalism.CohomologicalDescent.LP
