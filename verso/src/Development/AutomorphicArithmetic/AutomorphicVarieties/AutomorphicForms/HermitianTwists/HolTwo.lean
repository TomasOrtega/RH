import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolVec

open private eps eps_Eop from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolVec

open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br Complex in
/- English proof (translation)
Introduce `hL π hπ H hH`. Set `v : InfinitePlace ℚ` to `default`. Establish `hv : ∀ w : InfinitePlace ℚ, w = v` using `fun w => Subsingleton.elim _ _`. Set `E : Fin 2 → Fin 2 → Module.End ℂ π.V` to `fun i j => (TR.Eop v i j).restrict fun φ h => π.stable (.lie _) φ h`. Establish `hE : ∀ i j x, (E i j x).1 = TR.Eop v i j x.1` using `fun _ _ _ => rfl`.

Establish `hcap` using `capTwo ℚ π v _ _ (hπ v)`. Establish `hD : ∀ φ ∈ π.V, TR.Eop v 1 1 φ = -TR.Eop v 0 0 φ` using `fun φ hφ => by`. Use `(hcap φ hφ).1` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, zero_smul]`. Conclude with `eq_neg_of_add_eq_zero_right this`.

Establish `hrel : ∀ i j k l φ, _` using `fun i j k l (φ : TR.Sm ℚ 2) => LinearMap.congr_fun (TR.glRel_Eop (a := 2) v i j k l) φ`. Establish `hadj : ∀ i j x y, H (E i j x) y = -H x (E i j y)` using `fun i j x y => eq_neg_of_add_eq_zero_left (hH.lie _ x y)`. Establish `hJ : ∀ i j x, π.op (.cpt eps) (E i j x) = (if i = j then 1 else -1 : ℂ) • E i j (π.op (.cpt eps) x)` using `fun i j x => Subtype.ext (eps_Eop v i j x.1)`. Establish `hBC : ∀ x, E 0 1 (E 1 0 x) = E 1 0 (E 0 1 x) + (2 : ℂ) • E 0 0 x` using `fun x => by`. Use `Subtype.ext ?_` and prove the remaining obligations.

Establish `h` using `hrel 0 1 1 0 x.1`. Simplify using `only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hD _ x.2] at h`. Simplify using `only [Submodule.coe_add, Submodule.coe_smul, hE]`. Take the linear combination `(norm := module) h`. Establish `key` using `hL π.V (E 0 0) (E 0 1) (E 1 0) (π.op (.cpt eps)) H ?_ ?_ hBC ?_ hH.definite (hadj 0 0) (hadj 0 1) (hadj 1 0) ?_ ?_ ?_ ?_ ?_`.

Take `⟨x, hx, h1, h2⟩` from `key`. Use `⟨x.1, x.2, fun h => hx (Subtype.ext h), ?_⟩` and prove the remaining obligations. Break down `h1 with h1 | h1` into its components or cases. Use `Or.inl ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hv w, Nat.cast_ofNat]`.

Conclude with `congrArg Subtype.val h1`. Rewrite using `[hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]`. Conclude with `congrArg Subtype.val h2`. Rewrite using `[hv w, hD _ x.2, add_neg_cancel]`. Use `Or.inr ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[hv w, Nat.cast_zero, mul_zero, zero_smul]`. Conclude with `congrArg Subtype.val h1`. Rewrite using `[hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]`. Conclude with `congrArg Subtype.val h2`. Rewrite using `[hv w, hD _ x.2, add_neg_cancel]`.

Introduce `x`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `h` using `hrel 0 0 0 1 x.1`. Simplify using `at h`. Simplify using `only [Submodule.coe_add, hE]`.

Take the linear combination `(norm := module) h`. Introduce `x`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `h` using `hrel 0 0 1 0 x.1`. Simplify using `at h`.

Simplify using `only [Submodule.coe_sub, hE]`. Take the linear combination `(norm := module) h`. Introduce `x`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `h` using `(hcap x.1 x.2).2`.

Establish `h'` using `congrArg Subtype.val (hBC x)`. Rewrite `h` using `[hD _ x.2, map_neg, hD (TR.Eop v 0 0 x.1) (E 0 0 x).2, neg_neg]`. Simplify using `only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg, hE] at h h' ⊢`. Take the linear combination `(norm := module) (1 / 2 : ℂ) • h - (1 / 2 : ℂ) • h'`. Introduce `x h`.

Use `hH.definite x ?_` and prove the remaining obligations. Rewrite using `[← hH.cpt eps x x, h]`. Simplify using the standard rewrite rules. Introduce `x`. Simplify using `[hJ]`.

Introduce `x`. Simplify using `[hJ]`. Introduce `x`. Simplify using `[hJ]`. Take `⟨φ, hφ, h0, n, h⟩` from `wtVec π`.

Conclude with `⟨⟨φ, hφ⟩, fun e => h0 (congrArg Subtype.val e), n, Subtype.ext (h v)⟩`.
-/
theorem UpperTheory.V.Af.Rn.holTwo :
    UpperTheory.V.Af.Rn.LowTwo → UpperTheory.V.Af.Rn.HolTwo := by
  classical
  intro hL π hπ H hH
  let v : InfinitePlace ℚ := default
  have hv : ∀ w : InfinitePlace ℚ, w = v := fun w => Subsingleton.elim _ _
  let E : Fin 2 → Fin 2 → Module.End ℂ π.V := fun i j => (TR.Eop v i j).restrict fun φ h => π.stable (.lie _) φ h
  have hE : ∀ i j x, (E i j x).1 = TR.Eop v i j x.1 := fun _ _ _ => rfl
  have hcap := capTwo ℚ π v _ _ (hπ v)
  have hD : ∀ φ ∈ π.V, TR.Eop v 1 1 φ = -TR.Eop v 0 0 φ := fun φ hφ => by
    have := (hcap φ hφ).1
    rw [add_neg_cancel, zero_smul] at this
    exact eq_neg_of_add_eq_zero_right this
  have hrel : ∀ i j k l φ, _ := fun i j k l (φ : TR.Sm ℚ 2) => LinearMap.congr_fun (TR.glRel_Eop (a := 2) v i j k l) φ
  have hadj : ∀ i j x y, H (E i j x) y = -H x (E i j y) := fun i j x y => eq_neg_of_add_eq_zero_left (hH.lie _ x y)
  have hJ : ∀ i j x, π.op (.cpt eps) (E i j x) = (if i = j then 1 else -1 : ℂ) • E i j (π.op (.cpt eps) x) := fun i j x =>
    Subtype.ext (eps_Eop v i j x.1)
  have hBC : ∀ x, E 0 1 (E 1 0 x) = E 1 0 (E 0 1 x) + (2 : ℂ) • E 0 0 x := fun x => by
    refine Subtype.ext ?_
    have h := hrel 0 1 1 0 x.1
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hD _ x.2] at h
    simp only [Submodule.coe_add, Submodule.coe_smul, hE]
    linear_combination (norm := module) h
  have key := hL π.V (E 0 0) (E 0 1) (E 1 0) (π.op (.cpt eps)) H ?_ ?_ hBC ?_ hH.definite (hadj 0 0) (hadj 0 1)
    (hadj 1 0) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, h1, h2⟩ := key
    refine ⟨x.1, x.2, fun h => hx (Subtype.ext h), ?_⟩
    rcases h1 with h1 | h1
    · refine Or.inl ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩
      · rw [hv w, Nat.cast_ofNat]
        exact congrArg Subtype.val h1
      · rw [hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]
        exact congrArg Subtype.val h2
      · rw [hv w, hD _ x.2, add_neg_cancel]
    · refine Or.inr ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩
      · rw [hv w, Nat.cast_zero, mul_zero, zero_smul]
        exact congrArg Subtype.val h1
      · rw [hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]
        exact congrArg Subtype.val h2
      · rw [hv w, hD _ x.2, add_neg_cancel]
  · intro x
    refine Subtype.ext ?_
    have h := hrel 0 0 0 1 x.1
    simp at h
    simp only [Submodule.coe_add, hE]
    linear_combination (norm := module) h
  · intro x
    refine Subtype.ext ?_
    have h := hrel 0 0 1 0 x.1
    simp at h
    simp only [Submodule.coe_sub, hE]
    linear_combination (norm := module) h
  · intro x
    refine Subtype.ext ?_
    have h := (hcap x.1 x.2).2
    have h' := congrArg Subtype.val (hBC x)
    rw [hD _ x.2, map_neg, hD (TR.Eop v 0 0 x.1) (E 0 0 x).2, neg_neg] at h
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg, hE] at h h' ⊢
    linear_combination (norm := module) (1 / 2 : ℂ) • h - (1 / 2 : ℂ) • h'
  · intro x h
    refine hH.definite x ?_
    rw [← hH.cpt eps x x, h]
    simp
  · intro x
    simp [hJ]
  · intro x
    simp [hJ]
  · intro x
    simp [hJ]
  · obtain ⟨φ, hφ, h0, n, h⟩ := wtVec π
    exact ⟨⟨φ, hφ⟩, fun e => h0 (congrArg Subtype.val e), n, Subtype.ext (h v)⟩
