import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowKAllPos

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

/- English proof (translation)
Take `⟨c, hc, heq⟩` from `h`. Establish `hsing : ∀ p : Fin k, ∑ j : Fin k, ((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j = ((p : ℕ) : ℝ)`. Introduce `p`. Simplify using `only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `e1 : ∑ j : Fin k, ((j : ℕ) : ℝ) * (Λ - fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) j = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)`.

Establish `hj : ∀ j : Fin k, (Λ - fun c => Λ c + (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) j = (Pi.single b (1 : ℝ) : Fin k → ℝ) j - (Pi.single a (1 : ℝ) : Fin k → ℝ) j`. Introduce `j`. Simplify using `only [Pi.sub_apply, Pi.single_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hj, mul_sub, Finset.sum_sub_distrib, hsing]`.

Establish `e2 : ∑ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j ≤ 0`. Establish `hj : ∀ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j = ∑ p, ∑ q, (c p q : ℝ) * (((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j - ((j : ℕ) : ℝ) * (Pi.single q (1 : ℝ) : Fin k → ℝ) j)`. Introduce `j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PI.UpqRep.root, Pi.sub_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]`. Apply `Finset.sum_nonpos` to reduce the goal to its premises. Introduce `p _`. Rewrite using `[Finset.sum_comm]`.

Apply `Finset.sum_nonpos` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[← Finset.mul_sum, Finset.sum_sub_distrib, hsing, hsing]`. Distinguish the cases in `h0 : c p q = 0`. Simplify using `[h0]`.

Establish `hpq : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ)` using `by exact_mod_cast (hc p q h0).1`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)`. Establish `hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Rewrite `e1` using `[heq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_cdom_raise_of_lt {k : ℕ} {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b)
    (h : PI.UpqRep.CDom (PI.UpqRep.allPos k)
      (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) Λ) : False := by
  obtain ⟨c, hc, heq⟩ := h
  have hsing : ∀ p : Fin k, ∑ j : Fin k, ((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j = ((p : ℕ) : ℝ) := by
    intro p
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have e1 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (Λ - fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) j =
      ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have hj : ∀ j : Fin k,
        (Λ - fun c => Λ c + (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) j =
          (Pi.single b (1 : ℝ) : Fin k → ℝ) j - (Pi.single a (1 : ℝ) : Fin k → ℝ) j := by
      intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      ring
    simp only [hj, mul_sub, Finset.sum_sub_distrib, hsing]
  have e2 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j ≤ 0 := by
    have hj : ∀ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j =
        ∑ p, ∑ q, (c p q : ℝ) * (((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j -
          ((j : ℕ) : ℝ) * (Pi.single q (1 : ℝ) : Fin k → ℝ) j) := by
      intro j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PI.UpqRep.root, Pi.sub_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    apply Finset.sum_nonpos
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_nonpos
    intro q _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsing, hsing]
    by_cases h0 : c p q = 0
    · simp [h0]
    · have hpq : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast (hc p q h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [heq] at e1
  linarith

/- English proof (translation)
Use `set Bs := fr k r g with hBs`. Establish `hB : IsFrameOf k r [z] Bs` using `fr_frame hgU hgfix s hgz`. Use `set Λ := PI.UpqRep.lowK (PI.UpqRep.allPos k) u with hΛ`. Use `set E := EB π Bs with hE`. Establish `hgl : GlRel E` using `(frame_general_linear W k r k z π Bs hR hB).1`.

Use `set Ec : Fin k → (W →L[ℂ] W) := fun c => ecOp π (unitB (Hpk k r) Bs c c) with hEc`. Establish `hEE : ∀ c x, E c c x = Ec c x` using `fun c x => rfl`. Establish `hσ : ∀ θ : Fin k → ℝ, π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) = NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • Ec c)`. Introduce `θ`. Rewrite using `[← torus hgU θ]`.

Conclude with `op_torus hR hB θ`. Take `⟨-, -, hirr, ⟨v₀, -, hv0, hwt⟩, hdom⟩` from `hK`. Establish `hdiag : ∀ c, E c c v₀ = (Λ c : ℂ) • v₀`. Introduce `c`. Use `set A := hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef`.

Establish `hA : InLieW k r z A` using `(QrD.frame_lie hB c c).2`. Establish `hAe : A = (-Complex.I) • unitB (Hpk k r) Bs c c` using `hpart2_self Bs c`. Establish `hf : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • A)) v₀) = fun t : ℝ => Complex.exp (((-t * Λ c : ℝ) : ℂ) * Complex.I) • v₀`. Use function extensionality and compare the values at `t`. Use `set θ : Fin k → ℝ := fun c' => if c' = c then -t else 0 with hθ`.

Establish `h1 : (t : ℂ) • A = ∑ c', ((θ c' : ℂ) * Complex.I) • unitB (Hpk k r) Bs c' c'`. Rewrite using `[Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]`. Rewrite using `[hAe, smul_smul]`. Use `congr 1`. Simplify using `only [hθ, if_pos rfl]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsθ : ∑ a, Λ a * θ a = -t * Λ c`. Rewrite using `[Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]`. Simplify using `only [hθ, if_pos rfl]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, torus hgU θ]`. Use `(hwt θ (Dg_mem θ)).trans ?_` and prove the remaining obligations. Rewrite using `[hsθ]`. Establish `hd : dOp π A v₀ = (-(Λ c : ℂ) * Complex.I) • v₀`.

Rewrite using `[← QrD.dRep_eq hR.1 hR.2 hA v₀]`. Unfold `dRep`. Rewrite using `[hf]`. Conclude with `(deriv_cexp (Λ c) v₀).deriv`. Rewrite using `[hEE]`.

Use `show ecOp π (unitB (Hpk k r) Bs c c) v₀ = _`. Unfold `ecOp`. Rewrite using `[hpart1_self, SkewHermitianParts.dOp_zero, zero_add, _root_.smul_apply, hd, smul_smul]`. Use `congr 1`. Take the linear combination `(-(Λ c : ℂ)) * Complex.I_sq`.

Establish `hup : ∀ a b, a < b → E a b v₀ = 0`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Use `set x := E a b v₀ with hx`. Establish `hxw : ∀ c, Ec c x = (((fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) c : ℝ) : ℂ) • x`.

Introduce `c`. Rewrite using `[← hEE, hx, CommonEigenvectors.diag_move hgl c a b v₀, hdiag c, map_smul]`. Apply the tactic sequence `by_cases hca : c = a <;> by_cases hcb : c = b`. Conclude with `absurd (hca.symm.trans hcb) hab.ne`. Rewrite using `[if_pos hca, if_neg (fun h => hcb h.symm)]`.

Simplify using `only [if_pos hca, if_neg hcb]`. Use `push_cast`. Use `module`. Rewrite using `[if_neg hca, if_pos hcb.symm]`. Simplify using `only [if_neg hca, if_pos hcb]`.

Use `push_cast`. Use `module`. Rewrite using `[if_neg hca, if_neg (fun h => hcb h.symm)]`. Simplify using `only [if_neg hca, if_neg hcb]`. Use `push_cast`.

Use `module`. Establish `hwx : PI.UpqRep.IsWtOn (PI.UpqRep.Kset (PI.UpqRep.allPos k)) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹)) (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) x`. Introduce `θ _`. Use `show π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) x = _`. Rewrite using `[hσ θ]`.

Conclude with `exp_sum_eig Ec θ _ x hxw`. Conclude with `not_cdom_raise_of_lt hab (hdom _ x Submodule.mem_top hne hwx)`. Establish `hHW : IsHW E (fun j => (Λ j : ℂ)) v₀` using `⟨hdiag, hup⟩`. Use `set m : Fin k → ℂ := fun j => (Λ j : ℂ) - ((j : ℕ) : ℂ) with hm`. Establish `hq0 : ∀ w', qdet E w' v₀ = cpol m w' • v₀`.

Introduce `w'`. Rewrite using `[quantumDetHighestWeight_holds W k E _ v₀ hgl hHW w']`. Use `congr 1`. Unfold `cpol`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Simplify using `only [hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : v₀ ∈ CapSp E m` using `mem_CapSp.2 hq0`. Establish `hstab : Stab E (CapSp E m)` using `(capelli_stabilizer W k E m hgl).1`.

Establish `hirrE : ∀ S : Submodule ℂ W, Stab E S → S = ⊥ ∨ S = ⊤`. Introduce `S hS`. Establish `hU` using `lie_stabilizer W k r z π Bs hz hT hR hB S hS`. Use `hirr S le_top ?_` and prove the remaining obligations. Introduce `h hh y hy`.

Establish `hu : hᴴ * h = 1`. Use `Matrix.mem_unitaryGroup_iff'.1 hh.1` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Conclude with `hU _ (emb_uw hgU hgfix s hgz hu) y hy`. Establish `htop : CapSp E m = ⊤`.

Break down `hirrE _ hstab with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hmem` using `[h]`. Conclude with `hv0 ((Submodule.mem_bot ℂ).1 hmem)`. Conclude with `h`.

Establish `hv : v ∈ CapSp E m`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Conclude with `mem_CapSp.1 hv w`.
-/
theorem core {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} {g : Mx k r} {u : Fin k → ℝ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : IsRepW k r z π) (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z)
    (hK : PI.UpqRep.IsKTypeOf (PI.UpqRep.allPos k) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) u) ⊤) (w : ℂ) (v : W) :
    qdet (EB π (fr k r g)) w v =
      cpol (fun j : Fin k => ((PI.UpqRep.lowK (PI.UpqRep.allPos k) u j : ℝ) : ℂ) - ((j : ℕ) : ℂ)) w • v := by
  set Bs := fr k r g with hBs
  have hB : IsFrameOf k r [z] Bs := fr_frame hgU hgfix s hgz
  set Λ := PI.UpqRep.lowK (PI.UpqRep.allPos k) u with hΛ
  set E := EB π Bs with hE
  have hgl : GlRel E := (frame_general_linear W k r k z π Bs hR hB).1
  set Ec : Fin k → (W →L[ℂ] W) := fun c => ecOp π (unitB (Hpk k r) Bs c c) with hEc
  have hEE : ∀ c x, E c c x = Ec c x := fun c x => rfl
  have hσ : ∀ θ : Fin k → ℝ, π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • Ec c) := by
    intro θ
    rw [← torus hgU θ]
    exact op_torus hR hB θ
  obtain ⟨-, -, hirr, ⟨v₀, -, hv0, hwt⟩, hdom⟩ := hK

  have hdiag : ∀ c, E c c v₀ = (Λ c : ℂ) • v₀ := by
    intro c
    set A := hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
    have hA : InLieW k r z A := (QrD.frame_lie hB c c).2
    have hAe : A = (-Complex.I) • unitB (Hpk k r) Bs c c := hpart2_self Bs c
    have hf : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • A)) v₀) =
        fun t : ℝ => Complex.exp (((-t * Λ c : ℝ) : ℂ) * Complex.I) • v₀ := by
      funext t
      set θ : Fin k → ℝ := fun c' => if c' = c then -t else 0 with hθ
      have h1 : (t : ℂ) • A = ∑ c', ((θ c' : ℂ) * Complex.I) • unitB (Hpk k r) Bs c' c' := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        rw [hAe, smul_smul]
        congr 1
        simp only [hθ, if_pos rfl]
        push_cast
        ring
      have hsθ : ∑ a, Λ a * θ a = -t * Λ c := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        simp only [hθ, if_pos rfl]
        ring
      rw [h1, torus hgU θ]
      refine (hwt θ (Dg_mem θ)).trans ?_
      rw [hsθ]
    have hd : dOp π A v₀ = (-(Λ c : ℂ) * Complex.I) • v₀ := by
      rw [← QrD.dRep_eq hR.1 hR.2 hA v₀]
      unfold dRep
      rw [hf]
      exact (deriv_cexp (Λ c) v₀).deriv
    rw [hEE]
    show ecOp π (unitB (Hpk k r) Bs c c) v₀ = _
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add, _root_.smul_apply, hd, smul_smul]
    congr 1
    linear_combination (-(Λ c : ℂ)) * Complex.I_sq

  have hup : ∀ a b, a < b → E a b v₀ = 0 := by
    intro a b hab
    by_contra hne
    set x := E a b v₀ with hx
    have hxw : ∀ c, Ec c x = (((fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) c : ℝ) : ℂ) • x := by
      intro c
      rw [← hEE, hx, CommonEigenvectors.diag_move hgl c a b v₀, hdiag c, map_smul]
      by_cases hca : c = a <;> by_cases hcb : c = b
      · exact absurd (hca.symm.trans hcb) hab.ne
      · rw [if_pos hca, if_neg (fun h => hcb h.symm)]
        simp only [if_pos hca, if_neg hcb]
        push_cast
        module
      · rw [if_neg hca, if_pos hcb.symm]
        simp only [if_neg hca, if_pos hcb]
        push_cast
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm)]
        simp only [if_neg hca, if_neg hcb]
        push_cast
        module
    have hwx : PI.UpqRep.IsWtOn (PI.UpqRep.Kset (PI.UpqRep.allPos k)) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
        (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) x := by
      intro θ _
      show π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) x = _
      rw [hσ θ]
      exact exp_sum_eig Ec θ _ x hxw
    exact not_cdom_raise_of_lt hab (hdom _ x Submodule.mem_top hne hwx)

  have hHW : IsHW E (fun j => (Λ j : ℂ)) v₀ := ⟨hdiag, hup⟩
  set m : Fin k → ℂ := fun j => (Λ j : ℂ) - ((j : ℕ) : ℂ) with hm
  have hq0 : ∀ w', qdet E w' v₀ = cpol m w' • v₀ := by
    intro w'
    rw [quantumDetHighestWeight_holds W k E _ v₀ hgl hHW w']
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have hmem : v₀ ∈ CapSp E m := mem_CapSp.2 hq0
  have hstab : Stab E (CapSp E m) := (capelli_stabilizer W k E m hgl).1
  have hirrE : ∀ S : Submodule ℂ W, Stab E S → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hU := lie_stabilizer W k r z π Bs hz hT hR hB S hS
    refine hirr S le_top ?_
    intro h hh y hy
    have hu : hᴴ * h = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hU _ (emb_uw hgU hgfix s hgz hu) y hy
  have htop : CapSp E m = ⊤ := by
    rcases hirrE _ hstab with h | h
    · exfalso
      rw [h] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).1 hmem)
    · exact h
  have hv : v ∈ CapSp E m := by
    rw [htop]
    exact Submodule.mem_top
  exact mem_CapSp.1 hv w

end QrCap

end Formalism.FourierDecayAlt.P
