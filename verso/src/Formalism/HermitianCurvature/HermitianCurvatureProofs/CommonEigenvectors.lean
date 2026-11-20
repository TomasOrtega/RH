import Formalism.HermitianCurvature.CapelliDeterminantAndBranching

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CommonEigenvectors

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `haveI : Nontrivial G := Submodule.nontrivial_iff_ne_bot.2 hG`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue (T.restrict hT)`. Take `⟨x, hx⟩` from `hμ.exists_hasEigenvector`. Use `⟨μ, x, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩` and prove the remaining obligations. Establish `h1` using `Module.End.mem_eigenspace_iff.1 hx.1`.

Establish `h2` using `congrArg Subtype.val h1`. Simplify using `using h2`.
-/
theorem eig_in [FiniteDimensional ℂ V] (T : Module.End ℂ V) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hT : ∀ x ∈ G, T x ∈ G) : ∃ (μ : ℂ) (x : V), x ∈ G ∧ x ≠ 0 ∧ T x = μ • x := by
  haveI : Nontrivial G := Submodule.nontrivial_iff_ne_bot.2 hG
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hT)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, x, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩
  have h1 := Module.End.mem_eigenspace_iff.1 hx.1
  have h2 := congrArg Subtype.val h1
  simpa using h2

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨G, 0, le_rfl, hG, hst, by simp⟩`. Consider the case `@insert a s ha ih`. Take `⟨G₁, ν, h1, h2, h3, h4⟩` from `ih`. Take `⟨μ, x, hx1, hx2, hx3⟩` from `eig_in (D a) G₁ h2 (h3 a)`.

Use `⟨G₁ ⊓ LinearMap.ker (D a - μ • 1), Function.update ν a μ, le_trans inf_le_left h1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hbot`. Apply `hx2` to reduce the goal to its premises. Establish `hm : x ∈ G₁ ⊓ LinearMap.ker (D a - μ • 1)` using `Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (by simp [hx3])⟩`. Rewrite `hm` using `[hbot]`.

Simplify using `using hm`. Introduce `c y hy`. Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.1 hy`. Establish `hy2' : D a y = μ • y` using `by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2`. Establish `hcomm : D a (D c y) = D c (D a y)`.

Use `congrArg (fun T => T y) (hc a c)` as an intermediate fact. Simplify using `using this`. Conclude with `Submodule.mem_inf.2 ⟨h3 c y hy1, LinearMap.mem_ker.2 (by simp [hcomm, hy2'])⟩`. Introduce `b hb y hy`. Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.1 hy`.

Establish `hy2' : D a y = μ • y` using `by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2`. Break down `Finset.mem_insert.1 hb with rfl | hb` into its components or cases. Simplify using `[hy2']`. Establish `hba : b ≠ a` using `fun h => ha (h ▸ hb)`. Simplify using `[Function.update_apply, hba, h4 b hb y hy1]`.
-/
theorem common [FiniteDimensional ℂ V] {ι : Type} [DecidableEq ι] (D : ι → Module.End ℂ V)
    (hc : ∀ a b, D a * D b = D b * D a) (s : Finset ι) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hst : ∀ a, ∀ x ∈ G, D a x ∈ G) :
    ∃ (G' : Submodule ℂ V) (ν : ι → ℂ), G' ≤ G ∧ G' ≠ ⊥ ∧ (∀ a, ∀ x ∈ G', D a x ∈ G') ∧
      ∀ a ∈ s, ∀ x ∈ G', D a x = ν a • x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨G, 0, le_rfl, hG, hst, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨G₁, ν, h1, h2, h3, h4⟩ := ih
    obtain ⟨μ, x, hx1, hx2, hx3⟩ := eig_in (D a) G₁ h2 (h3 a)
    refine ⟨G₁ ⊓ LinearMap.ker (D a - μ • 1), Function.update ν a μ, le_trans inf_le_left h1, ?_, ?_, ?_⟩
    · intro hbot
      apply hx2
      have hm : x ∈ G₁ ⊓ LinearMap.ker (D a - μ • 1) :=
        Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (by simp [hx3])⟩
      rw [hbot] at hm
      simpa using hm
    · intro c y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      have hcomm : D a (D c y) = D c (D a y) := by
        have := congrArg (fun T => T y) (hc a c)
        simpa using this
      exact Submodule.mem_inf.2 ⟨h3 c y hy1, LinearMap.mem_ker.2 (by simp [hcomm, hy2'])⟩
    · intro b hb y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      rcases Finset.mem_insert.1 hb with rfl | hb
      · simp [hy2']
      · have hba : b ≠ a := fun h => ha (h ▸ hb)
        simp [Function.update_apply, hba, h4 b hb y hy1]

def hop {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • E c c

/- English proof (translation)
Establish `h : E c c (E a b x) - E a b (E c c x) = ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x` using `congrArg (fun T => T x) (hE c c a b)`. Rewrite `h` using `[sub_eq_iff_eq_add']`. Rewrite using `[h, LinearMap.sub_apply]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> subst_vars <;> simp`.
-/
theorem diag_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c a b : Fin n) (x : V) :
    E c c (E a b x) = E a b (E c c x) + ((if c = a then E a b x else 0) - (if b = c then E a b x else 0)) := by
  have h : E c c (E a b x) - E a b (E c c x) = ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    congrArg (fun T => T x) (hE c c a b)
  rw [sub_eq_iff_eq_add'] at h
  rw [h, LinearMap.sub_apply]
  congr 1
  split_ifs <;> subst_vars <;> simp

/- English proof (translation)
Unfold `hop`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, diag_move hE, smul_add, smul_sub, smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← sub_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hop_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) (x : V) :
    hop E (E a b x) = E a b (hop E x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • E a b x := by
  unfold hop
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, diag_move hE, smul_add, smul_sub,
    smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← sub_smul]
  congr 2
  ring

/- English proof (translation)
Unfold `hop`. Rewrite using `[LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, hx, smul_smul]`.
-/
theorem hop_weight {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {θ : Fin n → ℂ} {x : V}
    (hx : ∀ a, E a a x = θ a • x) :
    hop E x = (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c) • x := by
  unfold hop
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.smul_apply, hx, smul_smul]

/- English proof (translation)
Unfold `hval`. Rewrite using `[Complex.re_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by simp [Complex.mul_re]`.
-/
theorem hval_re {n : ℕ} (θ : Fin n → ℂ) :
    (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c).re = hval θ := by
  unfold hval
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [Complex.mul_re]

end Formalism.FourierDecayAlt.P.CommonEigenvectors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors

/- English proof (translation)
Introduce `V _ _ _ n E hE S hS hS0`. Establish `hcomm : ∀ a b : Fin n, E a a * E b b = E b b * E a a`. Introduce `a b`. Establish `h` using `hE a a b b`. Rewrite `h` using `[sub_eq_iff_eq_add]`.

Rewrite using `[h]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hab, Ne.symm hab]`.

Establish `hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S`. Introduce `a b x hx`. Conclude with `hS a b x hx`. Take `⟨G', ν0, hG'S, hG'0, -, hG'ν⟩` from `common (fun a => E a a) hcomm Finset.univ S hS0 (fun a => hstab a a)`. Take `⟨x0, hx0G, hx00⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hG'0`.

Set `W : Set (Fin n → ℂ)` to `{θ | ∃ x ∈ S, x ≠ 0 ∧ ∀ a, E a a x = θ a • x}`. Establish `hWne : W.Nonempty` using `⟨ν0, x0, hG'S hx0G, hx00, fun a => hG'ν a (Finset.mem_univ a) x0 hx0G⟩`. Establish `hWfin : W.Finite`. Use `(Set.Finite.pi (t := fun a => {μ | (E a a).HasEigenvalue μ}) fun a => Module.End.finite_hasEigenvalue (E a a)).subset ?_` and prove the remaining obligations. Introduce and unpack `θ ⟨x, -, hx0, hx⟩`.

Conclude with `Set.mem_univ_pi.2 fun a => Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hx a), hx0⟩`. Take `⟨ν, ⟨v, hvS, hv0, hv⟩, hmax⟩` from `Set.exists_max_image W hval hWfin hWne`. Use `⟨ν, v, hvS, hv0, ⟨hv, fun a b hab => ?_⟩, fun θ x hxS hx0 hx => hmax θ ⟨x, hxS, hx0, hx⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hy`. Use `set y := E a b v with hydef`.

Establish `hyS : y ∈ S` using `hstab a b v hvS`. Set `θ' : Fin n → ℂ` to `fun c => ν c + ((if c = a then 1 else 0) - (if b = c then 1 else 0))`. Establish `hy' : ∀ c, E c c y = θ' c • y`. Introduce `c`. Rewrite using `[hydef, diag_move hE, hv c, map_smul]`.

Simplify using `only [θ', add_smul, sub_smul, ite_smul, one_smul, zero_smul]`. Establish `hle` using `hmax θ' ⟨y, hyS, hy, hy'⟩`. Establish `k1` using `hop_weight hy'`. Establish `k2` using `hop_move hE a b v`. Rewrite `k2` using `[hop_weight hv, map_smul, ← hydef, ← add_smul, k1]`.

Establish `k3` using `smul_left_injective ℂ hy k2`. Establish `hv' : hval θ' = hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))`. Rewrite using `[← hval_re, ← hval_re, k3]`. Simplify using the standard rewrite rules. Establish `hba : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)`.

Use `Fin.lt_iff_val_lt_val.1 hab` as an intermediate fact. Conclude with `this` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_singular_maximal_vector : Qr.ExistsSingMax := by
  intro V _ _ _ n E hE S hS hS0
  have hcomm : ∀ a b : Fin n, E a a * E b b = E b b * E a a := by
    intro a b
    have h := hE a a b b
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    exact hS a b x hx
  obtain ⟨G', ν0, hG'S, hG'0, -, hG'ν⟩ :=
    common (fun a => E a a) hcomm Finset.univ S hS0 (fun a => hstab a a)
  obtain ⟨x0, hx0G, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG'0
  let W : Set (Fin n → ℂ) := {θ | ∃ x ∈ S, x ≠ 0 ∧ ∀ a, E a a x = θ a • x}
  have hWne : W.Nonempty := ⟨ν0, x0, hG'S hx0G, hx00, fun a => hG'ν a (Finset.mem_univ a) x0 hx0G⟩
  have hWfin : W.Finite := by
    refine (Set.Finite.pi (t := fun a => {μ | (E a a).HasEigenvalue μ})
      fun a => Module.End.finite_hasEigenvalue (E a a)).subset ?_
    rintro θ ⟨x, -, hx0, hx⟩
    exact Set.mem_univ_pi.2 fun a =>
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hx a), hx0⟩
  obtain ⟨ν, ⟨v, hvS, hv0, hv⟩, hmax⟩ := Set.exists_max_image W hval hWfin hWne
  refine ⟨ν, v, hvS, hv0, ⟨hv, fun a b hab => ?_⟩, fun θ x hxS hx0 hx => hmax θ ⟨x, hxS, hx0, hx⟩⟩
  by_contra hy
  set y := E a b v with hydef
  have hyS : y ∈ S := hstab a b v hvS
  let θ' : Fin n → ℂ := fun c => ν c + ((if c = a then 1 else 0) - (if b = c then 1 else 0))
  have hy' : ∀ c, E c c y = θ' c • y := by
    intro c
    rw [hydef, diag_move hE, hv c, map_smul]
    simp only [θ', add_smul, sub_smul, ite_smul, one_smul, zero_smul]
  have hle := hmax θ' ⟨y, hyS, hy, hy'⟩
  have k1 := hop_weight hy'
  have k2 := hop_move hE a b v
  rw [hop_weight hv, map_smul, ← hydef, ← add_smul, k1] at k2
  have k3 := smul_left_injective ℂ hy k2
  have hv' : hval θ' = hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← hval_re, ← hval_re, k3]
    simp
  have hba : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.1 hab
    exact_mod_cast this
  linarith

attribute [local instance 100] LieRing.ofAssociativeRing in
/- English proof (translation)
Introduce `V _ _ _ n E ν v hE hv hv0 a b hab`. Take `⟨hd, hr⟩` from `hv`. Establish `hab' : a ≠ b` using `ne_of_lt hab`. Distinguish the cases in `h0 : E a a - E b b = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `h1 : (E a a - E b b) v = 0` using `by rw [h0]; rfl`. Rewrite `h1` using `[LinearMap.sub_apply, hd, hd, ← sub_smul]`. Simplify `h1` using `[hv0]`. Establish `e0` using `hE a b b a`. Establish `e1` using `hE a a a b`.

Establish `e2` using `hE b b a b`. Establish `e3` using `hE a a b a`. Establish `e4` using `hE b b b a`. Simplify using `[hab', hab'.symm] at e0 e1 e2 e3 e4`. Establish `t : IsSl2Triple (E a a - E b b) (E a b) (E b a)` using `{ h_ne_zero := h0 lie_e_f := by rw [Ring.lie_def, e0] lie_h_e_nsmul := by`.

Rewrite using `[Ring.lie_def]`. Combine the equalities or inequalities in the displayed calculation. Use `lie_h_f_nsmul := by`. Rewrite using `[Ring.lie_def]`. Combine the equalities or inequalities in the displayed calculation.

Establish `pv : t.HasPrimitiveVectorWith v (ν a - ν b)` using `{ ne_zero := hv0 lie_h := by show (E a a - E b b) v = (ν a - ν b) • v`. Rewrite using `[LinearMap.sub_apply, hd, hd, sub_smul]`. Use `lie_e := by show E a b v = 0`. Conclude with `hr a b hab }`. Conclude with `pv.exists_nat`.
-/
theorem singular_dominant : Qr.SingDom := by
  intro V _ _ _ n E ν v hE hv hv0 a b hab
  obtain ⟨hd, hr⟩ := hv
  have hab' : a ≠ b := ne_of_lt hab
  by_cases h0 : E a a - E b b = 0
  · refine ⟨0, ?_⟩
    have h1 : (E a a - E b b) v = 0 := by rw [h0]; rfl
    rw [LinearMap.sub_apply, hd, hd, ← sub_smul] at h1
    simpa [hv0] using h1
  · have e0 := hE a b b a
    have e1 := hE a a a b
    have e2 := hE b b a b
    have e3 := hE a a b a
    have e4 := hE b b b a
    simp [hab', hab'.symm] at e0 e1 e2 e3 e4
    have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
      { h_ne_zero := h0
        lie_e_f := by rw [Ring.lie_def, e0]
        lie_h_e_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E a b - E a b * (E a a - E b b)
              = (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
            _ = 2 • E a b := by rw [e1, e2]; abel
        lie_h_f_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E b a - E b a * (E a a - E b b)
              = (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
            _ = -(2 • E b a) := by rw [e3, e4]; abel }
    have pv : t.HasPrimitiveVectorWith v (ν a - ν b) :=
      { ne_zero := hv0
        lie_h := by
          show (E a a - E b b) v = (ν a - ν b) • v
          rw [LinearMap.sub_apply, hd, hd, sub_smul]
        lie_e := by
          show E a b v = 0
          exact hr a b hab }
    exact pv.exists_nat

end Formalism.FourierDecayAlt.P
