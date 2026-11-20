import Mathlib

namespace CommutingFamilyCommonEigenvector

/- English proof (translation)
Use `haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW`. Set `f : Module.End ℂ W` to `(T i).restrict (fun x hx => hinv i x hx)`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue f`. Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Use `⟨μ, ?_⟩` and prove the remaining obligations.

Set `W' : Submodule ℂ E` to `W ⊓ (T i).eigenspace μ`. Establish `hW'le : W' ≤ W` using `inf_le_left`. Establish `hvW' : (v : E) ∈ W'`. Use `Submodule.mem_inf.mpr ⟨v.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`.

Use `hv.apply_eq_smul` as an intermediate fact. Establish `h2` using `congrArg Subtype.val this`. Simplify `h2` using `[f]`. Establish `hvne : (v : E) ≠ 0`. Introduce `h`.

Apply `hv.2` to reduce the goal to its premises. Conclude with `Subtype.ext h`. Establish `hW'ne : W' ≠ ⊥`. Introduce `h`. Rewrite `hvW'` using `[h]`.

Conclude with `hvne ((Submodule.mem_bot ℂ).mp hvW')`. Establish `hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W'`. Introduce `j x hx`. Establish `hx'` using `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨hinv j x hx'.1, ?_⟩` and prove the remaining obligations.

Establish `hx2 : T i x = μ • x` using `Module.End.mem_eigenspace_iff.mp hx'.2`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Establish `hcom : T i (T j x) = T j (T i x)`. Use `hc i j` as an intermediate fact. Conclude with `congrArg (fun g : Module.End ℂ E => g x) this.eq`.

Rewrite using `[hcom, hx2, map_smul]`. Establish `heq : W' = W` using `Submodule.eq_of_le_of_finrank_le hW'le (hmin W' hW'ne hW'inv)`. Establish `: w ∈ W'` using `heq ▸ hw`. Conclude with `Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp this).2`.
-/
private lemma key {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
    (T : I → Module.End ℂ E) (hc : ∀ (a b : I), Commute (T a) (T b))
    (W : Submodule ℂ E) (hW : W ≠ ⊥) (hinv : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W')
    (i : I) (w : E) (hw : w ∈ W) : ∃ μ : ℂ, T i w = μ • w := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let f : Module.End ℂ W := (T i).restrict (fun x hx => hinv i x hx)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  let W' : Submodule ℂ E := W ⊓ (T i).eigenspace μ
  have hW'le : W' ≤ W := inf_le_left
  have hvW' : (v : E) ∈ W' := by
    refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
    rw [Module.End.mem_eigenspace_iff]
    have := hv.apply_eq_smul
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  have hvne : (v : E) ≠ 0 := by
    intro h; apply hv.2; exact Subtype.ext h
  have hW'ne : W' ≠ ⊥ := by
    intro h; rw [h] at hvW'; exact hvne ((Submodule.mem_bot ℂ).mp hvW')
  have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
    intro j x hx
    have hx' := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hinv j x hx'.1, ?_⟩
    have hx2 : T i x = μ • x := Module.End.mem_eigenspace_iff.mp hx'.2
    rw [Module.End.mem_eigenspace_iff]
    have hcom : T i (T j x) = T j (T i x) := by
      have := hc i j
      exact congrArg (fun g : Module.End ℂ E => g x) this.eq
    rw [hcom, hx2, map_smul]
  have heq : W' = W :=
    Submodule.eq_of_le_of_finrank_le hW'le (hmin W' hW'ne hW'inv)
  have : w ∈ W' := heq ▸ hw
  exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp this).2

end CommutingFamilyCommonEigenvector

/- English proof (translation)
Introduce `d E _ _ _ I T hc hd hpos`. Set `P : ℕ → Prop` to `fun n => ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ (∀ i, ∀ x ∈ W, T i x ∈ W) ∧ Module.finrank ℂ W = n`. Establish `hex : ∃ n, P n`. Use `⟨Module.finrank ℂ (⊤ : Submodule ℂ E), ⊤, ?_, fun i x _ => Submodule.mem_top, rfl⟩` and prove the remaining obligations. Introduce `h`.

Establish `: Module.finrank ℂ (⊤ : Submodule ℂ E) = 0` using `by rw [h]; simp`. Rewrite `this` using `[finrank_top]`. Use linear arithmetic over natural numbers and integers. Take `⟨W, hW, hinv, hWr⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') → Module.finrank ℂ W ≤ Module.finrank ℂ W'`.

Introduce `W' h1 h2`. Rewrite using `[hWr]`. Conclude with `Nat.find_min' hex ⟨W', h1, h2, rfl⟩`. Take `⟨w, hwW, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Use `⟨w, hw0, fun i => Classical.choose (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW), ?_⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `Classical.choose_spec (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW)`.
-/
theorem UpperTheory.Reformulated.B.Ygb8.main :
    ∀ (d : ℕ) (E : Type) [inst : AddCommGroup E] [inst_1 : _root_.Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
      (T : I → Module.End ℂ E),
      (∀ (a b : I), Commute (T a) (T b)) →
        Module.finrank ℂ E = d → (0 : ℕ) < d → ∃ (w : E), w ≠ (0 : E) ∧ ∃ (c : I → ℂ), ∀ (i : I), (T i : E → E) w = c i • w := by
  intro d E _ _ _ I T hc hd hpos
  classical
  let P : ℕ → Prop := fun n => ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ (∀ i, ∀ x ∈ W, T i x ∈ W) ∧
    Module.finrank ℂ W = n
  have hex : ∃ n, P n := by
    refine ⟨Module.finrank ℂ (⊤ : Submodule ℂ E), ⊤, ?_, fun i x _ => Submodule.mem_top, rfl⟩
    intro h
    have : Module.finrank ℂ (⊤ : Submodule ℂ E) = 0 := by rw [h]; simp
    rw [finrank_top] at this
    omega
  obtain ⟨W, hW, hinv, hWr⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWr]
    exact Nat.find_min' hex ⟨W', h1, h2, rfl⟩
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨w, hw0, fun i => Classical.choose (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW), ?_⟩
  intro i
  exact Classical.choose_spec (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW)
