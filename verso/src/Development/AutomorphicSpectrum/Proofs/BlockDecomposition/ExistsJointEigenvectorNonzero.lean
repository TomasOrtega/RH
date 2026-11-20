import Mathlib

namespace GlobalTheory.CompanionTheory.LinAlg

open Module

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `U hU hne _`. Conclude with `absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hne`.

Consider the case `succ n ih`. Introduce `U hU hne hinv`. Distinguish the cases in `hs : ∀ i, ∃ a : ℂ, ∀ x ∈ U, H i x = a • x`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne choose χ hχ using hs`. Conclude with `⟨v, hv, hv0, χ, fun i => hχ i v hv⟩`.

Use `push_neg at hs`. Take `⟨i, hi⟩` from `hs`. Use `haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne`. Set `R : End ℂ U` to `(H i).restrict (hinv i)`. Take `⟨a, ha⟩` from `Module.End.exists_eigenvalue R`.

Take `⟨⟨w, hwU⟩, hw⟩` from `ha.exists_hasEigenvector`. Establish `hw' : H i w = a • w`. Establish `h1` using `congrArg Subtype.val hw.apply_eq_smul`. Simplify `h1` using `[R]`. Establish `hw0 : w ≠ 0`.

Introduce `h`. Conclude with `hw.2 (Subtype.ext h)`. Establish `hmem : ∀ {x : W}, x ∈ End.eigenspace (H i) a ↔ H i x = a • x`. Introduce `x`. Conclude with `End.mem_eigenspace_iff`.

Establish `hU'ne : U ⊓ End.eigenspace (H i) a ≠ ⊥`. Introduce `h`. Establish `: w ∈ U ⊓ End.eigenspace (H i) a` using `⟨hwU, hmem.mpr hw'⟩`. Rewrite `this` using `[h]`. Conclude with `hw0 ((Submodule.mem_bot ℂ).mp this)`.

Establish `hlt : U ⊓ End.eigenspace (H i) a < U`. Use `lt_of_le_of_ne inf_le_left ?_` and prove the remaining obligations. Introduce `h`. Take `⟨x, hx, hne'⟩` from `hi a`. Establish `: x ∈ U ⊓ End.eigenspace (H i) a` using `by rw [h]; exact hx`.

Conclude with `hne' (hmem.mp this.2)`. Establish `hfr` using `Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨v, hv, hv0, χ, hχ⟩` from `ih (U ⊓ End.eigenspace (H i) a) (by omega) hU'ne (by`. Introduce `k x hx`. Use `⟨hinv k x hx.1, hmem.mpr ?_⟩` and prove the remaining obligations.

Establish `h2 : H i x = a • x` using `hmem.mp hx.2`. Establish `h3 : H i (H k x) = H k (H i x)`. Use `congrArg (fun f : End ℂ W => f x) (hc i k).eq` as an intermediate fact. Simplify using `using this`. Rewrite using `[h3, h2, map_smul])`.

Conclude with `⟨v, hv.1, hv0, χ, hχ⟩`.
-/
theorem exists_common_eigenvector_in_submodule {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {ι : Type} (H : ι → End ℂ W)
    (hc : ∀ i i', Commute (H i) (H i')) :
    ∀ (n : ℕ) (U : Submodule ℂ W), finrank ℂ U ≤ n → U ≠ ⊥ →
      (∀ i, ∀ x ∈ U, H i x ∈ U) →
      ∃ v ∈ U, v ≠ 0 ∧ ∃ χ : ι → ℂ, ∀ i, H i v = χ i • v := by
  intro n
  induction n with
  | zero =>
    intro U hU hne _
    exact absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hne
  | succ n ih =>
    intro U hU hne hinv
    by_cases hs : ∀ i, ∃ a : ℂ, ∀ x ∈ U, H i x = a • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      choose χ hχ using hs
      exact ⟨v, hv, hv0, χ, fun i => hχ i v hv⟩
    · push_neg at hs
      obtain ⟨i, hi⟩ := hs
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
      let R : End ℂ U := (H i).restrict (hinv i)
      obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue R
      obtain ⟨⟨w, hwU⟩, hw⟩ := ha.exists_hasEigenvector
      have hw' : H i w = a • w := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [R] using h1
      have hw0 : w ≠ 0 := by
        intro h
        exact hw.2 (Subtype.ext h)
      have hmem : ∀ {x : W}, x ∈ End.eigenspace (H i) a ↔ H i x = a • x := by
        intro x
        exact End.mem_eigenspace_iff
      have hU'ne : U ⊓ End.eigenspace (H i) a ≠ ⊥ := by
        intro h
        have : w ∈ U ⊓ End.eigenspace (H i) a := ⟨hwU, hmem.mpr hw'⟩
        rw [h] at this
        exact hw0 ((Submodule.mem_bot ℂ).mp this)
      have hlt : U ⊓ End.eigenspace (H i) a < U := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hx, hne'⟩ := hi a
        have : x ∈ U ⊓ End.eigenspace (H i) a := by rw [h]; exact hx
        exact hne' (hmem.mp this.2)
      have hfr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨v, hv, hv0, χ, hχ⟩ := ih (U ⊓ End.eigenspace (H i) a) (by omega) hU'ne (by
        intro k x hx
        refine ⟨hinv k x hx.1, hmem.mpr ?_⟩
        have h2 : H i x = a • x := hmem.mp hx.2
        have h3 : H i (H k x) = H k (H i x) := by
          have := congrArg (fun f : End ℂ W => f x) (hc i k).eq
          simpa using this
        rw [h3, h2, map_smul])
      exact ⟨v, hv.1, hv0, χ, hχ⟩

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hbot : ∀ μ : ℂ, μ ≠ 0 → T.maxGenEigenspace μ = ⊥`. Introduce `μ hμ`. Assume the negation of the conclusion as `hne`.

Rewrite `hne` using `[End.maxGenEigenspace_eq_genEigenspace_finrank]`. Conclude with `hno μ hμ (End.hasEigenvalue_of_hasGenEigenvalue (k := finrank ℂ W) hne)`. Establish `htop : T.maxGenEigenspace 0 = ⊤`. Rewrite using `[eq_top_iff, ← End.iSup_maxGenEigenspace_eq_top T]`. Use `iSup_le fun μ => ?_` and prove the remaining obligations.

Distinguish the cases in `hμ : μ = 0`. Rewrite using `[hμ]`. Rewrite using `[hbot μ hμ]`. Conclude with `bot_le`. Establish `hvm : v ∈ T.maxGenEigenspace 0` using `htop ▸ Submodule.mem_top`.

Rewrite `hvm` using `[End.maxGenEigenspace_eq_genEigenspace_finrank, End.mem_genEigenspace_nat]`. Simplify using `only [zero_smul, sub_zero, LinearMap.mem_ker] at hvm`. Apply `hv` to reduce the goal to its premises. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Rewrite using `[add_comm, pow_add, Module.End.mul_apply, hvm, map_zero]`.
-/
theorem exists_hasEigenvalue_ne_zero {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : End ℂ W) (v : W) (m : ℕ) (hm : finrank ℂ W ≤ m)
    (hv : (T ^ m) v ≠ 0) : ∃ μ : ℂ, μ ≠ 0 ∧ T.HasEigenvalue μ := by
  by_contra hno
  push_neg at hno
  have hbot : ∀ μ : ℂ, μ ≠ 0 → T.maxGenEigenspace μ = ⊥ := by
    intro μ hμ
    by_contra hne
    rw [End.maxGenEigenspace_eq_genEigenspace_finrank] at hne
    exact hno μ hμ (End.hasEigenvalue_of_hasGenEigenvalue (k := finrank ℂ W) hne)
  have htop : T.maxGenEigenspace 0 = ⊤ := by
    rw [eq_top_iff, ← End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · rw [hμ]
    · rw [hbot μ hμ]
      exact bot_le
  have hvm : v ∈ T.maxGenEigenspace 0 := htop ▸ Submodule.mem_top
  rw [End.maxGenEigenspace_eq_genEigenspace_finrank, End.mem_genEigenspace_nat] at hvm
  simp only [zero_smul, sub_zero, LinearMap.mem_ker] at hvm
  apply hv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, Module.End.mul_apply, hvm, map_zero]

/- English proof (translation)
Introduce `W _ _ _ ι J _ H hc c s v m hm hv`. Take `⟨μ, hμ, hT⟩` from `exists_hasEigenvalue_ne_zero _ v m hm hv`. Establish `hcomm : ∀ i, Commute (∑ j, c j • H (s j)) (H i)`. Introduce `i`. Conclude with `Commute.sum_left _ _ _ fun j _ => (hc (s j) i).smul_left (c j)`.

Take `⟨v₀, hv₀U, hv₀, χ, hχ⟩` from `exists_common_eigenvector_in_submodule H hc _ (End.eigenspace (∑ j, c j • H (s j)) μ) le_rfl hT (by`. Introduce `i x hx`. Rewrite `hx`, the goal using `[End.mem_eigenspace_iff]`. Establish `h3 : (∑ j, c j • H (s j)) (H i x) = H i ((∑ j, c j • H (s j)) x)`. Use `congrArg (fun f : End ℂ W => f x) (hcomm i).eq` as an intermediate fact.

Simplify using `using this`. Rewrite using `[h3, hx, map_smul])`. Use `⟨v₀, hv₀, χ, hχ, ?_⟩` and prove the remaining obligations. Introduce `hsum`. Establish `h1 : (∑ j, c j • H (s j)) v₀ = (∑ j, c j * χ (s j)) • v₀`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, hχ, Finset.sum_smul, mul_smul]`. Rewrite `hv₀U` using `[End.mem_eigenspace_iff, h1, hsum, zero_smul]`. Conclude with `hv₀ ((smul_eq_zero.mp hv₀U.symm).resolve_left hμ)`.
-/
theorem exists_joint_eigenvector_combination_ne_zero :
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J]
      (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) →
      ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m →
        ((∑ j, c j • H (s j)) ^ m) v ≠ 0 →
        ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  intro W _ _ _ ι J _ H hc c s v m hm hv
  obtain ⟨μ, hμ, hT⟩ := exists_hasEigenvalue_ne_zero _ v m hm hv
  have hcomm : ∀ i, Commute (∑ j, c j • H (s j)) (H i) := by
    intro i
    exact Commute.sum_left _ _ _ fun j _ => (hc (s j) i).smul_left (c j)
  obtain ⟨v₀, hv₀U, hv₀, χ, hχ⟩ := exists_common_eigenvector_in_submodule H hc _
    (End.eigenspace (∑ j, c j • H (s j)) μ) le_rfl hT (by
      intro i x hx
      rw [End.mem_eigenspace_iff] at hx ⊢
      have h3 : (∑ j, c j • H (s j)) (H i x) = H i ((∑ j, c j • H (s j)) x) := by
        have := congrArg (fun f : End ℂ W => f x) (hcomm i).eq
        simpa using this
      rw [h3, hx, map_smul])
  refine ⟨v₀, hv₀, χ, hχ, ?_⟩
  intro hsum
  have h1 : (∑ j, c j • H (s j)) v₀ = (∑ j, c j * χ (s j)) • v₀ := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hχ, Finset.sum_smul, mul_smul]
  rw [End.mem_eigenspace_iff, h1, hsum, zero_smul] at hv₀U
  exact hv₀ ((smul_eq_zero.mp hv₀U.symm).resolve_left hμ)

end GlobalTheory.CompanionTheory.LinAlg
