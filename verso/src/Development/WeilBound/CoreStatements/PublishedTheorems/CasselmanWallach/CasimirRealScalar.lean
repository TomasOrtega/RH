import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirEigenvector

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Unfold `casimirK`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_assoc, hT b a, ← mul_assoc, hT a b, mul_assoc]`.
-/
lemma comm_casimirK (T : Module.End ℂ V) (hT : ∀ a b, E a b * T = T * E a b) :
    casimirK ε E * T = T * casimirK ε E := by
  unfold casimirK
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, hT b a, ← mul_assoc, hT a b, mul_assoc]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hb : Submodule.span ℂ {v | ∃ μ : ℝ, Eig ε E μ v} = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `v ⟨μ, hv⟩`.

Assume the negation of the conclusion as `hne`. Conclude with `hc μ v hne hv`. Rewrite `hb` using `[h.span]`. Conclude with `top_ne_bot hb`.
-/
lemma exists_eig_ne (h : Mod ε E) [Nontrivial V] : ∃ μ : ℝ, ∃ v : V, v ≠ 0 ∧ Eig ε E μ v := by
  by_contra hc
  push_neg at hc
  have hb : Submodule.span ℂ {v | ∃ μ : ℝ, Eig ε E μ v} = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro v ⟨μ, hv⟩
    by_contra hne
    exact hc μ v hne hv
  rw [h.span] at hb
  exact top_ne_bot hb

end CasimirEigenvector

/- English proof (translation)
Introduce `n ε V _ _ E h T hT`. Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Conclude with `⟨0, fun v => Subsingleton.elim _ _⟩`. Take `⟨μ, v, hv0, hv⟩` from `CasimirEigenvector.exists_eig_ne h`. Use `set W := Module.End.eigenspace (casimirK ε E) (μ : ℂ) with hWdef`.

Establish `hWle : W ≤ Submodule.span ℂ {v | ∃ ν : ℝ, ν ≤ μ ∧ Eig ε E ν v}`. Introduce `x hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨μ, le_rfl, Module.End.mem_eigenspace_iff.mp hx⟩`. Use `h.fin μ` as an intermediate fact.

Establish `: FiniteDimensional ℂ W` using `Submodule.finiteDimensional_of_le hWle`. Establish `hvW : v ∈ W` using `Module.End.mem_eigenspace_iff.mpr hv`. Establish `: Nontrivial W` using `⟨⟨⟨v, hvW⟩, 0, fun he => hv0 (congrArg Subtype.val he)⟩⟩`. Establish `hTW : ∀ x ∈ W, T x ∈ W`. Introduce `x hx`.

Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Establish `hc` using `congrArg (fun f : Module.End ℂ V => f x) (CasimirEigenvector.comm_casimirK (ε := ε) T hT)`. Simplify using `only [Module.End.mul_apply] at hc`. Rewrite using `[hc, hx, map_smul]`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (T.restrict hTW)`.

Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hN : LinearMap.ker (T - c • 1) = ⊥ ∨ LinearMap.ker (T - c • 1) = ⊤`. Apply `h.irr` to reduce the goal to its premises. Introduce `a b x hx`.

Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Establish `he` using `congrArg (fun f : Module.End ℂ V => f x) (hT a b)`. Simplify using `only [Module.End.mul_apply] at he`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢`. Rewrite using `[← he, ← LinearMap.map_smul, ← map_sub, hx, map_zero]`.

Establish `hw1 : T (w : V) = c • (w : V)`. Use `Module.End.mem_eigenspace_iff.mp hw.1` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Establish `hw0 : (w : V) ≠ 0` using `fun h0 => hw.2 (Subtype.ext h0)`. Break down `hN with hN | hN` into its components or cases.

It suffices to derive a contradiction. Apply `hw0` to reduce the goal to its premises. Establish `: (w : V) ∈ LinearMap.ker (T - c • 1)`. Rewrite using `[LinearMap.mem_ker]`. Simplify using `[hw1]`.

Rewrite `this` using `[hN]`. Conclude with `(Submodule.mem_bot ℂ).mp this`. Introduce `x`. Establish `: x ∈ LinearMap.ker (T - c • 1)` using `by rw [hN]; trivial`. Rewrite `this` using `[LinearMap.mem_ker]`.

Simplify `this` using `[sub_eq_zero]`.
-/
theorem casimir_eigen_exists : A3 := by
  intro n ε V _ _ E h T hT
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  obtain ⟨μ, v, hv0, hv⟩ := CasimirEigenvector.exists_eig_ne h
  set W := Module.End.eigenspace (casimirK ε E) (μ : ℂ) with hWdef
  have hWle : W ≤ Submodule.span ℂ {v | ∃ ν : ℝ, ν ≤ μ ∧ Eig ε E ν v} := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨μ, le_rfl, Module.End.mem_eigenspace_iff.mp hx⟩
  have := h.fin μ
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
  have hvW : v ∈ W := Module.End.mem_eigenspace_iff.mpr hv
  have : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun he => hv0 (congrArg Subtype.val he)⟩⟩
  have hTW : ∀ x ∈ W, T x ∈ W := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have hc := congrArg (fun f : Module.End ℂ V => f x) (CasimirEigenvector.comm_casimirK (ε := ε) T hT)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hx, map_smul]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hTW)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hN : LinearMap.ker (T - c • 1) = ⊥ ∨ LinearMap.ker (T - c • 1) = ⊤ := by
    apply h.irr
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have he := congrArg (fun f : Module.End ℂ V => f x) (hT a b)
    simp only [Module.End.mul_apply] at he
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢
    rw [← he, ← LinearMap.map_smul, ← map_sub, hx, map_zero]
  have hw1 : T (w : V) = c • (w : V) := by
    have := Module.End.mem_eigenspace_iff.mp hw.1
    exact congrArg Subtype.val this
  have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  rcases hN with hN | hN
  · exfalso
    apply hw0
    have : (w : V) ∈ LinearMap.ker (T - c • 1) := by
      rw [LinearMap.mem_ker]
      simp [hw1]
    rw [hN] at this
    exact (Submodule.mem_bot ℂ).mp this
  · intro x
    have : x ∈ LinearMap.ker (T - c • 1) := by rw [hN]; trivial
    rw [LinearMap.mem_ker] at this
    simpa [sub_eq_zero] using this

end PositivityTheory.CW

end
