import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def fockEmb (σ : Type) [DecidableEq σ] :
    MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2 :=
  (basisMonomials σ ℂ).constr ℂ fun α =>
    lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)

/- English proof (translation)
Introduce `α β`. Establish `h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) = lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)`. Introduce `γ`. Use `(basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ => (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) : lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ` as an intermediate fact. Simplify `this` using `[fockEmb]`.

Rewrite using `[h, h, lp.inner_single_left]`. Use `split_ifs with e`. Substitute `e` using the available equality. Establish `h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ)` using `Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _`. Rewrite using `[lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h0]`.

Simplify using `[Finsupp.prod]`. Rewrite using `[lp.single_apply_ne _ _ _ e, inner_zero_right]`.
-/
theorem isFockIsometry_fockEmb (σ : Type) [DecidableEq σ] : IsFockIP (fockEmb σ) := by
  intro α β
  have h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) =
      lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro γ
    have := (basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ =>
      (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) :
        lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ
    simpa [fockEmb] using this
  rw [h, h, lp.inner_single_left]
  split_ifs with e
  · subst e
    have h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0]
    simp [Finsupp.prod]
  · rw [lp.single_apply_ne _ _ _ e, inner_zero_right]

/- English proof (translation)
Introduce `h`. Simplify using `using h 0 0`.
-/
theorem not_isFockIP_zero (σ : Type) [DecidableEq σ] :
    ¬ IsFockIP (0 : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) := by
  intro h
  simpa using h 0 0

/- English proof (translation)
Unfold `minusPart`. Establish `: ∀ d : ℕ, homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0`. Introduce `d`. Rewrite using `[homogeneousComponent_eq_zero (d + 2) P (by omega)]; simp`. Simplify using `[this]`.
-/
theorem minusPart_of_deg {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ)
    (h : P.totalDegree ≤ 1) : minusPart A P = 0 := by
  unfold minusPart
  have : ∀ d : ℕ, homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0 := by
    intro d
    rw [homogeneousComponent_eq_zero (d + 2) P (by omega)]; simp
  simp [this]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => minusPart_of_deg _ _ h, fun _ _ => minusPart_of_deg _ _ h⟩`.
-/
theorem mem_jointHarm_of_deg {p q r s : ℕ} (P : Pol p q r s) (h : P.totalDegree ≤ 1) :
    P ∈ jointHarm p q r s :=
  ⟨fun _ _ => minusPart_of_deg _ _ h, fun _ _ => minusPart_of_deg _ _ h⟩

/- English proof (translation)
Use `Set.eq_univ_of_forall fun P Z hZ => ?_` and prove the remaining obligations. Establish `: Z = 0`. Use extensionality with `a b`. Break down `a with a | a` into its components or cases. Break down `b with b | b` into its components or cases.

Conclude with `hZ _ _ trivial`. Conclude with `b.elim0`. Conclude with `a.elim0`. Simplify using `[this, minusPart]`.
-/
theorem harmonic_all_of_compact (p q r : ℕ) : harm1 p q r 0 = Set.univ := by
  refine Set.eq_univ_of_forall fun P Z hZ => ?_
  have : Z = 0 := by
    ext a b
    rcases a with a | a
    · rcases b with b | b
      · exact hZ _ _ trivial
      · exact b.elim0
    · exact a.elim0
  simp [this, minusPart]

/- English proof (translation)
Introduce `h`. Establish `h1` using `h (Eab (.inr 0) (.inl 0)) (by`. Introduce `a b hab`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [Eab, sameBlock, Matrix.single_apply])`. Establish `hom : (X (.inl 0, .inl 0) * X (.inr 0, .inl 0) : Pol 1 1 1 0).IsHomogeneous 2` using `(isHomogeneous_X _ _).mul (isHomogeneous_X _ _)`.

Unfold `minusPart at h1`. Rewrite `h1` using `[finsum_eq_single _ 0]`. Rewrite `h1` using `[homogeneousComponent_of_mem hom, fockAct1_Eab]`. Simplify using `[omE, raiB, lowB, linePos, pderiv_X, Pi.single_apply] at h1`. Introduce `d hd`.

Rewrite using `[homogeneousComponent_of_mem hom, if_neg (by omega)]; simp`.
-/
theorem not_mem_harm2 :
    (X (.inl 0, .inl 0) * X (.inr 0, .inl 0) : Pol 1 1 1 0) ∉ harm2 1 1 1 0 := by
  intro h
  have h1 := h (Eab (.inr 0) (.inl 0)) (by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp_all [Eab, sameBlock, Matrix.single_apply])
  have hom : (X (.inl 0, .inl 0) * X (.inr 0, .inl 0) : Pol 1 1 1 0).IsHomogeneous 2 :=
    (isHomogeneous_X _ _).mul (isHomogeneous_X _ _)
  unfold minusPart at h1
  rw [finsum_eq_single _ 0] at h1
  · rw [homogeneousComponent_of_mem hom, fockAct1_Eab] at h1
    simp [omE, raiB, lowB, linePos, pderiv_X, Pi.single_apply] at h1
  · intro d hd
    rw [homogeneousComponent_of_mem hom, if_neg (by omega)]; simp

/- English proof (translation)
Introduce `_ hx` and use `Submodule.mem_sInf.2 fun _ hN => hN.1 hx`.
-/
theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S :=
  fun _ hx => Submodule.mem_sInf.2 fun _ hN => hN.1 hx

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun N hN => hN.2 Z y (Submodule.mem_sInf.1 hy N hN)`.
-/
theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act S) :
    act Z y ∈ genSub act S :=
  Submodule.mem_sInf.2 fun N hN => hN.2 Z y (Submodule.mem_sInf.1 hy N hN)

def charAct (p q : ℕ) (c : ℚ) : Mat p q →ₗ[ℂ] Module.End ℂ ℂ :=
  ((c : ℂ) • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight 1

/- English proof (translation)
Simplify using `[charAct]`.
-/
theorem charAct_apply (p q : ℕ) (c : ℚ) (Z : Mat p q) (v : ℂ) :
    charAct p q c Z v = (c : ℂ) * Z.trace * v := by
  simp [charAct]

/- English proof (translation)
Simplify using `[wtSub, charAct_apply, Eab, sub_eq_zero]`.
-/
theorem mem_wt (p q : ℕ) (c : ℚ) (μ : Ix p q → ℚ) (v : ℂ) :
    v ∈ wtSub (charAct p q c) μ ↔ ∀ a, (c : ℂ) * v = μ a * v := by
  simp [wtSub, charAct_apply, Eab, sub_eq_zero]

@[reducible] def charMod (p q : ℕ) (c : ℚ) : GKMod p q where
  V := ℂ
  act := charAct p q c
  lie := by
    intro X Y
    ext
    simp [charAct_apply, Matrix.trace_mul_comm X Y]; ring
  kfin := fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩
  wts := fun v => Submodule.mem_iSup_of_mem (fun _ => c) ((mem_wt _ _ _ _ _).2 fun _ => rfl)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨m, -, hm⟩` from `h (fun _ => c) (1 : ℂ) ⟨one_ne_zero, (mem_wt _ _ _ _ _).2 fun _ => rfl, by`. Use `(Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun b => (Submodule.mem_iInf _).2 fun hab => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`.

Conclude with `absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)`. Apply the tactic sequence `all_goals first | exact b.elim0 | exact a.elim0⟩`. Simplify `congrFun hm (.inl 0)` using `[blattner, rhoNC]`. Introduce and unpack `rfl μ v ⟨hv, hw, -⟩`. Use `⟨0, by simp, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Use `(mem_wt _ _ _ _ _).1 hw a` as an intermediate fact. Establish `h2 : (c : ℂ) = μ a` using `mul_right_cancel₀ hv this`. Simplify using `[blattner, rhoNC]`. Conclude with `h2.symm` after adjusting the coercions.
-/
theorem coneTypes_rank_one (c d : ℚ) : ConeTypes (charMod 1 0 c) (fun _ => d) ↔ c = d := by
  constructor
  · intro h
    obtain ⟨m, -, hm⟩ := h (fun _ => c) (1 : ℂ) ⟨one_ne_zero, (mem_wt _ _ _ _ _).2 fun _ => rfl, by
      refine (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun b =>
        (Submodule.mem_iInf _).2 fun hab => ?_
      rcases a with a | a <;> rcases b with b | b
      · exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
      all_goals first | exact b.elim0 | exact a.elim0⟩
    simpa [blattner, rhoNC] using congrFun hm (.inl 0)
  · rintro rfl μ v ⟨hv, hw, -⟩
    refine ⟨0, by simp, ?_⟩
    funext a
    have := (mem_wt _ _ _ _ _).1 hw a
    have h2 : (c : ℂ) = μ a := mul_right_cancel₀ hv this
    simp [blattner, rhoNC]
    exact_mod_cast h2.symm

def lamHalf : Ix 1 1 → ℚ := Sum.elim (fun _ => 1 / 2) (fun _ => -1 / 2)

/- English proof (translation)
Simplify using `only [blattner, rhoNC, Finset.card_filter, Fintype.sum_sum_type]`. Evaluate the numerical expressions using `[lamHalf, sameBlock]`.
-/
theorem blattner_lamHalf : blattner lamHalf (.inl 0) = 1 := by
  simp only [blattner, rhoNC, Finset.card_filter, Fintype.sum_sum_type]
  norm_num [lamHalf, sameBlock]

/- English proof (translation)
Introduce `h`. Take `⟨m, hm0, hm⟩` from `h (fun _ => 0) (1 : ℂ) ⟨one_ne_zero, (mem_wt _ _ _ _ _).2 fun _ => rfl, by`. Use `(Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun b => (Submodule.mem_iInf _).2 fun hab => ?_` and prove the remaining obligations. Use `show charAct 1 1 0 _ 1 = 0`. Simplify using `[charAct_apply]⟩`.

Establish `h1` using `congrFun hm (.inl 0)`. Establish `h2 : m (.inr 0) (.inl 0) = 0`. Assume the negation of the conclusion as `hh`. Use `hm0 _ _ hh` as an intermediate fact. Evaluate the numerical expressions using `[lamHalf] at this`.

Simplify using `[blattner_lamHalf, Fintype.sum_sum_type, h2] at h1`. Establish `: (0 : ℚ) ≤ m (.inl 0) (.inr 0)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_coneTypes_trivial : ¬ ConeTypes (charMod 1 1 0) lamHalf := by
  intro h
  obtain ⟨m, hm0, hm⟩ := h (fun _ => 0) (1 : ℂ) ⟨one_ne_zero, (mem_wt _ _ _ _ _).2 fun _ => rfl, by
    refine (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun b =>
        (Submodule.mem_iInf _).2 fun hab => ?_
    show charAct 1 1 0 _ 1 = 0
    simp [charAct_apply]⟩
  have h1 := congrFun hm (.inl 0)
  have h2 : m (.inr 0) (.inl 0) = 0 := by
    by_contra hh
    have := hm0 _ _ hh
    norm_num [lamHalf] at this
  simp [blattner_lamHalf, Fintype.sum_sum_type, h2] at h1
  have : (0 : ℚ) ≤ m (.inl 0) (.inr 0) := Nat.cast_nonneg _
  linarith

def vac : Pol 1 0 1 0 →ₗ[ℂ] TensorProduct ℂ (charMod 1 0 (1 / 2)).V (charMod 1 0 (1 / 2)).V :=
  (lcoeff ℂ 0).smulRight ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ)

/- English proof (translation)
Use extensionality with `a b`. Break down `a with a | a` into its components or cases. Break down `b with b | b` into its components or cases. Rewrite using `[Subsingleton.elim a 0, Subsingleton.elim b 0]`. Simplify using `[Eab]`.

Conclude with `b.elim0`. Conclude with `a.elim0`.
-/
theorem mat_eq (Z : Mat 1 0) : Z = Z (.inl 0) (.inl 0) • Eab (.inl 0) (.inl 0) := by
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [Eab]
    · exact b.elim0
  · exact a.elim0

/- English proof (translation)
Use `show coeff 0 (monomial α (1 : ℂ)) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ) = _`. Rewrite using `[coeff_monomial]`.
-/
theorem vac_monomial (α : Ln 1 0 1 0 →₀ ℕ) :
    vac (monomial α 1) = (if α = 0 then (1 : ℂ) else 0) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ) := by
  show coeff 0 (monomial α (1 : ℂ)) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ) = _
  rw [coeff_monomial]

/- English proof (translation)
Use `⟨⟨fun Z => ?_, fun Z => ?_⟩, fun h => ?_⟩` and prove the remaining obligations. Use `(basisMonomials _ ℂ).ext fun α => ?_` and prove the remaining obligations. Rewrite using `[mat_eq Z]`. Simplify using `only [coe_basisMonomials, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, cartan1, vac_monomial]`. Use `erw [vac_monomial]`.

Use `split_ifs with e`. Substitute `e` using the available equality. Apply `(TensorProduct.lid ℂ ℂ).injective` to reduce the goal to its premises. Simplify using `[lineSign, charAct_apply, Eab]`. Simplify using the standard rewrite rules.

Use `(basisMonomials _ ℂ).ext fun α => ?_` and prove the remaining obligations. Rewrite using `[mat_eq Z]`. Simplify using `only [coe_basisMonomials, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, cartan2, vac_monomial]`. Use `erw [vac_monomial]`. Use `split_ifs with e`.

Substitute `e show _ = (1 : ℂ) • TensorProduct.map LinearMap.id (_ • charAct 1 0 (1 / 2) _) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ)` using the available equality. Apply `(TensorProduct.lid ℂ ℂ).injective` to reduce the goal to its premises. Simplify using `[lineSign, charAct_apply, Eab]`. Simplify using the standard rewrite rules. Establish `h1` using `vac_monomial 0`.

Rewrite `h1` using `[h]`. Establish `h2` using `congrArg (TensorProduct.lid ℂ ℂ) h1`. Simplify using `at h2`.
-/
theorem intw_vac : Intw (charMod 1 0 (1 / 2)) (charMod 1 0 (1 / 2)) vac ∧ vac ≠ 0 := by
  refine ⟨⟨fun Z => ?_, fun Z => ?_⟩, fun h => ?_⟩
  · refine (basisMonomials _ ℂ).ext fun α => ?_
    rw [mat_eq Z]
    simp only [coe_basisMonomials, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, cartan1,
      vac_monomial]
    erw [vac_monomial]
    split_ifs with e
    · subst e
      apply (TensorProduct.lid ℂ ℂ).injective
      simp [lineSign, charAct_apply, Eab]
    · simp
  · refine (basisMonomials _ ℂ).ext fun α => ?_
    rw [mat_eq Z]
    simp only [coe_basisMonomials, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, cartan2,
      vac_monomial]
    erw [vac_monomial]
    split_ifs with e
    · subst e
      show _ = (1 : ℂ) • TensorProduct.map LinearMap.id (_ • charAct 1 0 (1 / 2) _)
        ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ)
      apply (TensorProduct.lid ℂ ℂ).injective
      simp [lineSign, charAct_apply, Eab]
    · simp
  · have h1 := vac_monomial 0
    rw [h] at h1
    have h2 := congrArg (TensorProduct.lid ℂ ℂ) h1
    simp at h2

end GlobalTheory.FockAlg.Model
