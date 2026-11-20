import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Take `⟨i, g, rfl⟩` from `hl a (by simp)`. Take `⟨h1, h2⟩` from `ih (fun x hx => hl x (by simp [hx]))`.

Use `⟨fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[List.prod_cons, UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, hE, h1]`. Rewrite using `[List.prod_cons, UnitaryRep.map_mul_apply]`. Conclude with `hP _ _ _ (h2 v hv)`.
-/
private lemma UpperTheory.ConvolutionTheory.L1.cutIrr_prod {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (E : H →L[ℂ] H) {m : ℕ} (ι : Fin (m + 1) → G →* Γ)
    (hE : ∀ i g v, E (π (ι i g) v) = π (ι i g) (E v)) (P : Submodule ℂ H)
    (hP : ∀ i g, ∀ v ∈ P, π (ι i g) v ∈ P) (l : List Γ) (hl : ∀ x ∈ l, ∃ i g, x = ι i g) :
    (∀ v, E (π l.prod v) = π l.prod (E v)) ∧ ∀ v ∈ P, π l.prod v ∈ P := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i, g, rfl⟩ := hl a (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hl x (by simp [hx]))
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [List.prod_cons, UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, hE, h1]
    · rw [List.prod_cons, UnitaryRep.map_mul_apply]
      exact hP _ _ _ (h2 v hv)

/- English proof (translation)
Introduce `Γ G H _ _ _ _ _ _ π V m ι E A U h`. Establish `hfix : ∀ v, v ∈ eigIn V E 1 ↔ v ∈ V ∧ E v = v`. Introduce `v`. Simplify using `[eigIn, Module.End.mem_eigenspace_iff]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hset : (eigIn V E 1 : Set H) = (V : Set H) ∩ {v | E v = v}`. Use extensionality with `v`. Conclude with `hfix v`. Rewrite using `[hset]`. Conclude with `h.summand.closed.inter (isClosed_eq E.continuous continuous_id)`.

Introduce `i g v hv`. Take `⟨hV, hE⟩` from `(hfix v).1 hv`. Conclude with `(hfix _).2 ⟨h.summand.inv _ _ hV, by rw [h.E_ι, hE]⟩`. Introduce `P hPle hPc hPinv`. Distinguish the cases in `hbot : P = ⊥`.

Conclude with `Or.inl hbot`. Use `right`. Take `⟨w, hwP, hw0⟩` from `P.ne_bot_iff.1 hbot`. Take `⟨hwV, hEw⟩` from `(hfix w).1 (hPle hwP)`. Set `S : Submodule ℂ H` to `Submodule.span ℂ (Set.range fun γ => π γ w)`.

Establish `hSinv : π.IsInvariant S`. Introduce `g v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨γ, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `S.add_mem hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[map_smul]`. Conclude with `S.smul_mem a hx`. Establish `hSV : S ≤ V` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨γ, rfl⟩`.

Conclude with `h.summand.inv _ _ hwV)`. Establish `hQle : S.topologicalClosure ≤ V` using `Submodule.topologicalClosure_minimal _ hSV h.summand.closed`. Establish `hQ : S.topologicalClosure = V`. Break down `h.summand.irred _ hQle S.isClosed_topologicalClosure hSinv.topologicalClosure with h0 | h1` into its components or cases. It suffices to derive a contradiction.

Establish `hmem : w ∈ S.topologicalClosure` using `S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)`. Rewrite `hmem` using `[h0]`. Conclude with `hw0 (by simpa using hmem)`. Conclude with `h1`. Establish `hES : ∀ v ∈ S, E v ∈ P`.

Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨γ, rfl⟩` from `hx`. Take `⟨g, γ', c, hγ, hc⟩` from `h.rest γ`.

Establish `hl : ∀ x ∈ List.ofFn (fun i => ι i (g i)), ∃ i g, x = ι i g`. Introduce `x hx`. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hx`. Conclude with `⟨i, g i, rfl⟩`. Take `⟨h1, h2⟩` from `UpperTheory.ConvolutionTheory.L1.cutIrr_prod π E ι h.E_ι P hPinv _ hl`.

Establish `hc'` using `hc w hwV`. Rewrite `hc'` using `[hEw]`. Use `show E (π γ w) ∈ P`. Rewrite using `[hγ, UnitaryRep.map_mul_apply, h1, hc']`. Conclude with `h2 _ (P.smul_mem c hwP)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `P.add_mem hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[map_smul]`. Conclude with `P.smul_mem a hx`. Establish `hEQ : ∀ v ∈ V, E v ∈ P`. Introduce `v hv`. Rewrite `hv` using `[← hQ]`.

Establish `hcl : v ∈ closure (S : Set H)` using `hv`. Establish `hm` using `map_mem_closure E.continuous hcl (t := (P : Set H)) (fun x hx => hES x hx)`. Rewrite `hm` using `[hPc.closure_eq]`. Then use the resulting hypothesis. Use `le_antisymm hPle fun v hv => ?_` and prove the remaining obligations. Take `⟨hV, hE⟩` from `(hfix v).1 hv`.

Rewrite using `[← hE]`. Conclude with `hEQ v hV`.
-/
theorem UpperTheory.ConvolutionTheory.L1.cutIrr :
    UpperTheory.ConvolutionTheory.L1.CutIrr := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h
  have hfix : ∀ v, v ∈ eigIn V E 1 ↔ v ∈ V ∧ E v = v := by
    intro v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hset : (eigIn V E 1 : Set H) = (V : Set H) ∩ {v | E v = v} := by
      ext v
      exact hfix v
    rw [hset]
    exact h.summand.closed.inter (isClosed_eq E.continuous continuous_id)
  · intro i g v hv
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    exact (hfix _).2 ⟨h.summand.inv _ _ hV, by rw [h.E_ι, hE]⟩
  · intro P hPle hPc hPinv
    by_cases hbot : P = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨w, hwP, hw0⟩ := P.ne_bot_iff.1 hbot
    obtain ⟨hwV, hEw⟩ := (hfix w).1 (hPle hwP)
    let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun γ => π γ w)
    have hSinv : π.IsInvariant S := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact S.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact S.smul_mem a hx
    have hSV : S ≤ V := Submodule.span_le.2 (by
      rintro _ ⟨γ, rfl⟩
      exact h.summand.inv _ _ hwV)
    have hQle : S.topologicalClosure ≤ V :=
      Submodule.topologicalClosure_minimal _ hSV h.summand.closed
    have hQ : S.topologicalClosure = V := by
      rcases h.summand.irred _ hQle S.isClosed_topologicalClosure hSinv.topologicalClosure with h0 | h1
      · exfalso
        have hmem : w ∈ S.topologicalClosure :=
          S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
        rw [h0] at hmem
        exact hw0 (by simpa using hmem)
      · exact h1
    have hES : ∀ v ∈ S, E v ∈ P := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        obtain ⟨g, γ', c, hγ, hc⟩ := h.rest γ
        have hl : ∀ x ∈ List.ofFn (fun i => ι i (g i)), ∃ i g, x = ι i g := by
          intro x hx
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
          exact ⟨i, g i, rfl⟩
        obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr_prod π E ι h.E_ι P hPinv _ hl
        have hc' := hc w hwV
        rw [hEw] at hc'
        show E (π γ w) ∈ P
        rw [hγ, UnitaryRep.map_mul_apply, h1, hc']
        exact h2 _ (P.smul_mem c hwP)
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact P.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact P.smul_mem a hx
    have hEQ : ∀ v ∈ V, E v ∈ P := by
      intro v hv
      rw [← hQ] at hv
      have hcl : v ∈ closure (S : Set H) := hv
      have hm := map_mem_closure E.continuous hcl (t := (P : Set H)) (fun x hx => hES x hx)
      rwa [hPc.closure_eq] at hm
    refine le_antisymm hPle fun v hv => ?_
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    rw [← hE]
    exact hEQ v hV
