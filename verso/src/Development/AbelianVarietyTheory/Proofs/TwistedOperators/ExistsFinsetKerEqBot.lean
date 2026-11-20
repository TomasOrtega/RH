import Mathlib

namespace GlobalTheory.FinsetKernelTrivial

open scoped BigOperators

noncomputable def restr {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X) :
    W →ₗ[ℂ] (P → ℂ) :=
  LinearMap.pi (fun x : P => (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.1).comp (V.subtype.comp W.subtype))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma restr_apply {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := rfl

/- English proof (translation)
Establish `hex : ∃ n, ∃ P : Finset X, Module.finrank ℂ (LinearMap.ker (restr V W P)) = n` using `⟨_, ∅, rfl⟩`. Take `⟨P, hP⟩` from `Nat.find_spec hex`. Use `⟨P, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨w, hwK, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`.

Establish `hf : ((w : V) : X → ℂ) ≠ 0`. Introduce `h`. Apply `hw0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using h`. Take `⟨x, hx⟩` from `Function.ne_iff.mp hf`. Establish `hle : LinearMap.ker (restr V W (insert x P)) < LinearMap.ker (restr V W P)`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Introduce `v hv`.

Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `y`. Use `congrFun hv ⟨y.1, Finset.mem_insert_of_mem y.2⟩` as an intermediate fact. Simplify `this` using `[restr_apply]`. Introduce `heq`.

Establish `: w ∈ LinearMap.ker (restr V W (insert x P))` using `heq ▸ hwK`. Rewrite `this` using `[LinearMap.mem_ker]`. Use `congrFun this ⟨x, Finset.mem_insert_self x P⟩` as an intermediate fact. Conclude with `hx (by simpa [restr_apply] using this)`. Establish `hlt` using `Submodule.finrank_lt_finrank_of_lt hle`.

Establish `hmin` using `Nat.find_min hex (hP ▸ hlt)`. Conclude with `hmin ⟨insert x P, rfl⟩`.
-/
lemma exists_finset_ker_eq_bot {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] : ∃ P : Finset X, LinearMap.ker (restr V W P) = ⊥ := by
  classical
  have hex : ∃ n, ∃ P : Finset X, Module.finrank ℂ (LinearMap.ker (restr V W P)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  by_contra hne
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hf : ((w : V) : X → ℂ) ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hle : LinearMap.ker (restr V W (insert x P)) < LinearMap.ker (restr V W P) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext y
      have := congrFun hv ⟨y.1, Finset.mem_insert_of_mem y.2⟩
      simpa [restr_apply] using this
    · intro heq
      have : w ∈ LinearMap.ker (restr V W (insert x P)) := heq ▸ hwK
      rw [LinearMap.mem_ker] at this
      have := congrFun this ⟨x, Finset.mem_insert_self x P⟩
      exact hx (by simpa [restr_apply] using this)
  have hlt := Submodule.finrank_lt_finrank_of_lt hle
  have hmin := Nat.find_min hex (hP ▸ hlt)
  exact hmin ⟨insert x P, rfl⟩

/- English proof (translation)
Introduce `X V W _`. Take `⟨P, hP⟩` from `exists_finset_ker_eq_bot V W`. Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective (restr V W P) hP`. Use `⟨P, fun x => if h : x ∈ P then ((L (Pi.single ⟨x, h⟩ 1) : W) : V) else 0, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Establish `h1 : (⟨w, hw⟩ : W) = L (restr V W P ⟨w, hw⟩)`. Use `congrArg (fun g => g ⟨w, hw⟩) hL` as an intermediate fact. Simplify using `using this.symm`. Establish `h2 : restr V W P ⟨w, hw⟩ = ∑ x : P, ((w : X → ℂ) x.1) • (Pi.single x (1 : ℂ))`. Use function extensionality and compare the values at `y`.

Simplify using `[restr_apply, Finset.sum_apply, Pi.single_apply]`. Establish `h3 : w = ∑ x : P, ((w : X → ℂ) x.1) • ((L (Pi.single x 1) : W) : V)`. Use `congrArg (fun u : W => (u : V)) h1` as an intermediate fact. Simplify using `only at this`. Use `conv_lhs => rw [this, h2, map_sum]`.

Simplify using `[map_smul]`. Use `conv_lhs => rw [h3]`. Rewrite using `[← Finset.sum_attach P]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `x _`.

Simplify using `[x.2]`.
-/
theorem main : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ ↥V) [FiniteDimensional ℂ ↥W],
    ∃ (P : Finset X) (e : X → ↥V), ∀ w ∈ W, w = ∑ x ∈ P, (↑w : X → ℂ) x • e x := by
  intro X V W _
  classical
  obtain ⟨P, hP⟩ := exists_finset_ker_eq_bot V W
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (restr V W P) hP
  refine ⟨P, fun x => if h : x ∈ P then ((L (Pi.single ⟨x, h⟩ 1) : W) : V) else 0, ?_⟩
  intro w hw
  have h1 : (⟨w, hw⟩ : W) = L (restr V W P ⟨w, hw⟩) := by
    have := congrArg (fun g => g ⟨w, hw⟩) hL
    simpa using this.symm
  have h2 : restr V W P ⟨w, hw⟩ = ∑ x : P, ((w : X → ℂ) x.1) • (Pi.single x (1 : ℂ)) := by
    funext y
    simp [restr_apply, Finset.sum_apply, Pi.single_apply]
  have h3 : w = ∑ x : P, ((w : X → ℂ) x.1) • ((L (Pi.single x 1) : W) : V) := by
    have := congrArg (fun u : W => (u : V)) h1
    simp only at this
    conv_lhs => rw [this, h2, map_sum]
    simp [map_smul]
  conv_lhs => rw [h3]
  rw [← Finset.sum_attach P]
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [x.2]

end GlobalTheory.FinsetKernelTrivial
