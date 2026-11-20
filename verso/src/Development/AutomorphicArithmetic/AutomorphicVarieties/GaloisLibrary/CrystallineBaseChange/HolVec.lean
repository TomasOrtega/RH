import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CapTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LieX0EqRaisingLowering
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Sl2Low
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

noncomputable section

open NumberField UpperTheory.V UpperTheory.V.Af Complex

namespace UpperTheory.V.Br

/- English proof (translation)
Establish `hI : I * I = -1` using `I_mul_I`. Establish `key` using `sl2Low V ((-I) • (B - C)) (A + (I / 2) • (B + C)) (A - (I / 2) • (B + C)) H k hk ?_ ?_ ?_ ?_ hH ?_ ?_ ?_ ?_`. Take `⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩` from `key`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2`. Use `⟨x, hx, ?_, ?_⟩` and prove the remaining obligations.

Establish `: B x - C x = I • ((-I) • (B x - C x))`. Rewrite using `[smul_smul, mul_neg, hI, neg_neg, one_smul]`. Rewrite using `[this, h1, smul_smul]`. Take the linear combination `(norm := module) (2 : ℂ) • h2`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2`.

Use `⟨J x, fun h => hx (hJ x h), ?_, ?_⟩` and prove the remaining obligations. Establish `: B x - C x = I • ((-I) • (B x - C x))`. Rewrite using `[smul_smul, mul_neg, hI, neg_neg, one_smul]`. Rewrite `this` using `[h1]`. Establish `h3` using `congrArg J this`.

Simplify using `only [map_sub, map_smul] at h3`. Rewrite using `[hJB, hJC]`. Take the linear combination `(norm := module) -h3`. Establish `h3` using `congrArg J h2`. Simplify using `only [map_add, map_smul, map_zero] at h3`.

Rewrite using `[hJA, hJB, hJC]`. Take the linear combination `(norm := module) (2 : ℂ) • h3`. Use extensionality with `x`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul, hAB, hAC, hBC]`. Apply the tactic sequence `match_scalars <;> grind`.

Use extensionality with `x`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul, hAB, hAC, hBC]`. Apply the tactic sequence `match_scalars <;> grind`. Use extensionality with `x`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul, Module.End.one_apply, hAB, hAC, hBC, hCas]`.

Apply the tactic sequence `match_scalars <;> grind`. Use extensionality with `x`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul, Module.End.one_apply, hAB, hAC, hBC, hCas]`. Apply the tactic sequence `match_scalars <;> grind`. Introduce `x y`.

Simplify using `[hB, hC]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y`. Simplify using `[hA, hB, hC, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x y`. Simplify using `[hA, hB, hC, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨x, hx, n, h⟩` from `hw`. Use `⟨x, hx, n, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, h, smul_smul]`. Use `congr 1`. Use `grind`.
-/
private theorem low_of {V : Type} [AddCommGroup V] [Module ℂ V] (A B C J : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ)
    (hk : 3 ≤ k) (hAB : ∀ x, A (B x) = B (A x) + B x) (hAC : ∀ x, A (C x) = C (A x) - C x)
    (hBC : ∀ x, B (C x) = C (B x) + (2 : ℂ) • A x)
    (hCas : ∀ x, C (B x) = ((k : ℂ) * (k - 2) / 4) • x - A (A x) - A x)
    (hH : ∀ x, H x x = 0 → x = 0) (hA : ∀ x y, H (A x) y = -H x (A y)) (hB : ∀ x y, H (B x) y = -H x (B y))
    (hC : ∀ x y, H (C x) y = -H x (C y))
    (hJ : ∀ x, J x = 0 → x = 0) (hJA : ∀ x, A (J x) = J (A x)) (hJB : ∀ x, B (J x) = -J (B x)) (hJC : ∀ x, C (J x) = -J (C x))
    (hw : ∃ x, x ≠ 0 ∧ ∃ n : ℤ, B x - C x = (I * n) • x) :
    ∃ x, x ≠ 0 ∧ B x - C x = (I * k) • x ∧ (2 : ℂ) • A x = I • (B x + C x) := by
  have hI : I * I = -1 := I_mul_I
  have key := sl2Low V ((-I) • (B - C)) (A + (I / 2) • (B + C)) (A - (I / 2) • (B + C)) H k hk ?_ ?_ ?_ ?_ hH ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := key
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨x, hx, ?_, ?_⟩
      · have : B x - C x = I • ((-I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [this, h1, smul_smul]
      · linear_combination (norm := module) (2 : ℂ) • h2
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨J x, fun h => hx (hJ x h), ?_, ?_⟩
      · have : B x - C x = I • ((-I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [h1] at this
        have h3 := congrArg J this
        simp only [map_sub, map_smul] at h3
        rw [hJB, hJC]
        linear_combination (norm := module) -h3
      · have h3 := congrArg J h2
        simp only [map_add, map_smul, map_zero] at h3
        rw [hJA, hJB, hJC]
        linear_combination (norm := module) (2 : ℂ) • h3
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul,
      hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul,
      hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul,
      Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul,
      Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · intro x y
    simp [hB, hC]
    ring
  · intro x y
    simp [hA, hB, hC, map_ofNat]
    ring
  · intro x y
    simp [hA, hB, hC, map_ofNat]
    ring
  · obtain ⟨x, hx, n, h⟩ := hw
    refine ⟨x, hx, n, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, h, smul_smul]
    congr 1
    grind

private def eps : TR.Kinf ℚ 2 :=
  ⟨Matrix.diagonal ![-1, 1], by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

/- English proof (translation)
Establish `h` using `LinearMap.congr_fun (TR.Cen.rt_Eop (Unitary.toUnits eps) v i j) φ`. Establish `e1 : (Unitary.toUnits eps).val = Matrix.diagonal ![-1, 1]` using `rfl`. Establish `e2 : ((Unitary.toUnits eps)⁻¹).val = Matrix.diagonal ![-1, 1]`. Express the relevant statement in the definitionally equal form `star (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) = _`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`.

Use `congr 1`. Rewrite `h` using `[e1, e2]`. Use `h.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = _ • TR.Eop v i j (TR.rt ℚ 2 (TR.infGL ℚ 2 (Unitary.toUnits eps)) φ)`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]`.
-/
private theorem eps_Eop (v : InfinitePlace ℚ) (i j : Fin 2) (φ : TR.Sm ℚ 2) :
    TR.cptRep ℚ 2 eps (TR.Eop v i j φ) = (if i = j then 1 else -1 : ℂ) • TR.Eop v i j (TR.cptRep ℚ 2 eps φ) := by
  have h := LinearMap.congr_fun (TR.Cen.rt_Eop (Unitary.toUnits eps) v i j) φ
  have e1 : (Unitary.toUnits eps).val = Matrix.diagonal ![-1, 1] := rfl
  have e2 : ((Unitary.toUnits eps)⁻¹).val = Matrix.diagonal ![-1, 1] := by
    change star (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
  rw [e1, e2] at h
  refine h.trans ?_
  change _ = _ • TR.Eop v i j (TR.rt ℚ 2 (TR.infGL ℚ 2 (Unitary.toUnits eps)) φ)
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

end UpperTheory.V.Br

open UpperTheory.V.Br in
/- English proof (translation)
Introduce `k hk π hπ H hH`. Set `v : InfinitePlace ℚ` to `default`. Establish `hv : ∀ w : InfinitePlace ℚ, w = v` using `fun w => Subsingleton.elim _ _`. Set `E : Fin 2 → Fin 2 → Module.End ℂ π.V` to `fun i j => (TR.Eop v i j).restrict fun φ h => π.stable (.lie _) φ h`. Establish `hE : ∀ i j x, (E i j x).1 = TR.Eop v i j x.1` using `fun _ _ _ => rfl`.

Establish `hcap` using `capTwo ℚ π v _ _ (hπ v)`. Establish `hD : ∀ φ ∈ π.V, TR.Eop v 1 1 φ = -TR.Eop v 0 0 φ` using `fun φ hφ => by`. Use `(hcap φ hφ).1` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, zero_smul]`. Conclude with `eq_neg_of_add_eq_zero_right this`.

Establish `hrel : ∀ i j k l φ, _` using `fun i j k l (φ : TR.Sm ℚ 2) => LinearMap.congr_fun (TR.glRel_Eop (a := 2) v i j k l) φ`. Establish `hadj : ∀ i j x y, H (E i j x) y = -H x (E i j y)` using `fun i j x y => eq_neg_of_add_eq_zero_left (hH.lie _ x y)`. Establish `hJ : ∀ i j x, π.op (.cpt eps) (E i j x) = (if i = j then 1 else -1 : ℂ) • E i j (π.op (.cpt eps) x)` using `fun i j x => Subtype.ext (eps_Eop v i j x.1)`. Establish `hBC : ∀ x, E 0 1 (E 1 0 x) = E 1 0 (E 0 1 x) + (2 : ℂ) • E 0 0 x` using `fun x => by`. Use `Subtype.ext ?_` and prove the remaining obligations.

Establish `h` using `hrel 0 1 1 0 x.1`. Simplify using `only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hD _ x.2] at h`. Simplify using `only [Submodule.coe_add, Submodule.coe_smul, hE]`. Take the linear combination `(norm := module) h`. Establish `key` using `low_of (E 0 0) (E 0 1) (E 1 0) (π.op (.cpt eps)) H k hk ?_ ?_ hBC ?_ hH.definite (hadj 0 0) (hadj 0 1) (hadj 1 0) ?_ ?_ ?_ ?_ ?_`.

Take `⟨x, hx, h1, h2⟩` from `key`. Use `⟨x.1, x.2, fun h => hx (Subtype.ext h), fun w => ?_, fun w => ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hv w]`. Conclude with `congrArg Subtype.val h1`. Rewrite using `[hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]`.

Conclude with `congrArg Subtype.val h2`. Rewrite using `[hv w, hD _ x.2, add_neg_cancel]`. Introduce `x`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `h` using `hrel 0 0 0 1 x.1`.

Simplify using `at h`. Simplify using `only [Submodule.coe_add, hE]`. Take the linear combination `(norm := module) h`. Introduce `x`. Use `Subtype.ext ?_` and prove the remaining obligations.

Establish `h` using `hrel 0 0 1 0 x.1`. Simplify using `at h`. Simplify using `only [Submodule.coe_sub, hE]`. Take the linear combination `(norm := module) h`. Introduce `x`.

Use `Subtype.ext ?_` and prove the remaining obligations. Establish `h` using `(hcap x.1 x.2).2`. Establish `h'` using `congrArg Subtype.val (hBC x)`. Rewrite `h` using `[hD _ x.2, map_neg, hD (TR.Eop v 0 0 x.1) (E 0 0 x).2, neg_neg]`. Simplify using `only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, hE] at h h' ⊢`.

Take the linear combination `(norm := module) (1 / 2 : ℂ) • h - (1 / 2 : ℂ) • h'`. Introduce `x h`. Use `hH.definite x ?_` and prove the remaining obligations. Rewrite using `[← hH.cpt eps x x, h]`. Simplify using the standard rewrite rules.

Introduce `x`. Simplify using `[hJ]`. Introduce `x`. Simplify using `[hJ]`. Introduce `x`.

Simplify using `[hJ]`. Take `⟨φ, hφ, h0, n, h⟩` from `wtVec π`. Conclude with `⟨⟨φ, hφ⟩, fun e => h0 (congrArg Subtype.val e), n, Subtype.ext (h v)⟩`.
-/
theorem UpperTheory.V.Br.holVec :
    UpperTheory.V.Br.HolVec := by
  classical
  intro k hk π hπ H hH
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
  have key := low_of (E 0 0) (E 0 1) (E 1 0) (π.op (.cpt eps)) H k hk ?_ ?_ hBC ?_ hH.definite (hadj 0 0) (hadj 0 1)
    (hadj 1 0) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, h1, h2⟩ := key
    refine ⟨x.1, x.2, fun h => hx (Subtype.ext h), fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hv w]
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
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, hE] at h h' ⊢
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
