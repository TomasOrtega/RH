import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHWOfFd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameBlockIffIsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryOfISupIntertwinerRangeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SubQuot

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `[wtSub, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_wtSub' {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Simplify using `[hwSub, mem_wtSub', Submodule.mem_iInf]`.
-/
theorem mem_hwSub' {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, mem_wtSub', Submodule.mem_iInf]

variable (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N N' : Submodule ℂ V)

def resA (h' : Stab act N') : Mat p q →ₗ[ℂ] Module.End ℂ N' where
  toFun Z := (act Z).restrict (h' Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resA_coe (h' : Stab act N') (Z : Mat p q) (x : N') :
    ((resA act N' h' Z x : N') : V) = act Z x := rfl

abbrev below : Submodule ℂ N' := N.comap N'.subtype

/- English proof (translation)
Introduce `x hx` and use `h Z x hx`.
-/
theorem le_comap_resA (h : Stab act N) (h' : Stab act N') (Z : Mat p q) :
    below N N' ≤ (below N N').comap (resA act N' h' Z) := fun x hx => h Z x hx

def quoA (h : Stab act N) (h' : Stab act N') : Mat p q →ₗ[ℂ] Module.End ℂ (N' ⧸ below N N') where
  toFun Z := (below N N').mapQ (below N N') (resA act N' h' Z) (le_comap_resA act N N' h h' Z)
  map_add' X Y := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_smul' c X := by
    apply Submodule.linearMap_qext
    ext x
    simp

def Rel (T : Module.End ℂ V) (T' : Module.End ℂ (N' ⧸ below N N')) : Prop :=
  ∀ x : N', ∃ y : N', (y : V) = T x ∧ T' ((below N N').mkQ x) = (below N N').mkQ y

variable {N N'}

/- English proof (translation)
Introduce `x`. Take `⟨y₂, hy₂, e₂⟩` from `h₂ x`. Take `⟨y₁, hy₁, e₁⟩` from `h₁ y₂`. Use `⟨y₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hy₁, hy₂]`.

Both sides reduce to the same expression. Rewrite using `[Module.End.mul_apply, e₂, e₁]`.
-/
theorem Rel.mul {T₁ T₂ : Module.End ℂ V} {T₁' T₂' : Module.End ℂ (N' ⧸ below N N')} (h₁ : Rel N N' T₁ T₁')
    (h₂ : Rel N N' T₂ T₂') : Rel N N' (T₁ * T₂) (T₁' * T₂') := by
  intro x
  obtain ⟨y₂, hy₂, e₂⟩ := h₂ x
  obtain ⟨y₁, hy₁, e₁⟩ := h₁ y₂
  refine ⟨y₁, ?_, ?_⟩
  · rw [hy₁, hy₂]; rfl
  · rw [Module.End.mul_apply, e₂, e₁]

/- English proof (translation)
Introduce `x`. Take `⟨y₂, hy₂, e₂⟩` from `h₂ x`. Take `⟨y₁, hy₁, e₁⟩` from `h₁ x`. Use `⟨y₁ + y₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_add, hy₁, hy₂]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.add_apply, e₁, e₂, map_add]`.
-/
theorem Rel.add {T₁ T₂ : Module.End ℂ V} {T₁' T₂' : Module.End ℂ (N' ⧸ below N N')} (h₁ : Rel N N' T₁ T₁')
    (h₂ : Rel N N' T₂ T₂') : Rel N N' (T₁ + T₂) (T₁' + T₂') := by
  intro x
  obtain ⟨y₂, hy₂, e₂⟩ := h₂ x
  obtain ⟨y₁, hy₁, e₁⟩ := h₁ x
  refine ⟨y₁ + y₂, ?_, ?_⟩
  · rw [Submodule.coe_add, hy₁, hy₂]; rfl
  · rw [LinearMap.add_apply, e₁, e₂, map_add]

/- English proof (translation)
Introduce `x`. Take `⟨y₂, hy₂, e₂⟩` from `h₂ x`. Take `⟨y₁, hy₁, e₁⟩` from `h₁ x`. Use `⟨y₁ - y₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_sub, hy₁, hy₂]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.sub_apply, e₁, e₂, map_sub]`.
-/
theorem Rel.sub {T₁ T₂ : Module.End ℂ V} {T₁' T₂' : Module.End ℂ (N' ⧸ below N N')} (h₁ : Rel N N' T₁ T₁')
    (h₂ : Rel N N' T₂ T₂') : Rel N N' (T₁ - T₂) (T₁' - T₂') := by
  intro x
  obtain ⟨y₂, hy₂, e₂⟩ := h₂ x
  obtain ⟨y₁, hy₁, e₁⟩ := h₁ x
  refine ⟨y₁ - y₂, ?_, ?_⟩
  · rw [Submodule.coe_sub, hy₁, hy₂]; rfl
  · rw [LinearMap.sub_apply, e₁, e₂, map_sub]

/- English proof (translation)
Introduce `x`. Take `⟨y, hy, e⟩` from `h x`. Use `⟨c • y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, hy]`. Both sides reduce to the same expression.

Rewrite using `[LinearMap.smul_apply, e, map_smul]`.
-/
theorem Rel.smul {T : Module.End ℂ V} {T' : Module.End ℂ (N' ⧸ below N N')} (h : Rel N N' T T') (c : ℂ) :
    Rel N N' (c • T) (c • T') := by
  intro x
  obtain ⟨y, hy, e⟩ := h x
  refine ⟨c • y, ?_, ?_⟩
  · rw [Submodule.coe_smul, hy]; rfl
  · rw [LinearMap.smul_apply, e, map_smul]

/- English proof (translation)
Introduce `x`. Take `⟨y, hy, e⟩` from `h x`. Use `⟨-y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_neg, hy]`. Both sides reduce to the same expression.

Rewrite using `[LinearMap.neg_apply, e, map_neg]`.
-/
theorem Rel.neg {T : Module.End ℂ V} {T' : Module.End ℂ (N' ⧸ below N N')} (h : Rel N N' T T') :
    Rel N N' (-T) (-T') := by
  intro x
  obtain ⟨y, hy, e⟩ := h x
  refine ⟨-y, ?_, ?_⟩
  · rw [Submodule.coe_neg, hy]; rfl
  · rw [LinearMap.neg_apply, e, map_neg]

/- English proof (translation)
Introduce `x` and use `⟨x, rfl, rfl⟩`.
-/
theorem Rel.one : Rel N N' (1 : Module.End ℂ V) 1 := fun x => ⟨x, rfl, rfl⟩

/- English proof (translation)
Introduce `_` and use `⟨0, rfl, by simp⟩`.
-/
theorem Rel.zero : Rel N N' (0 : Module.End ℂ V) 0 := fun _ => ⟨0, rfl, by simp⟩

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `using (Rel.zero : Rel N N' 0 0)`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(h a).add ih`.
-/
theorem Rel.sum {κ : Type} (s : Finset κ) {T : κ → Module.End ℂ V} {T' : κ → Module.End ℂ (N' ⧸ below N N')}
    (h : ∀ i, Rel N N' (T i) (T' i)) : Rel N N' (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (Rel.zero : Rel N N' 0 0)
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

/- English proof (translation)
Unfold `qop`. Use `((Rel.sum _ fun c => (h a c).mul (h c b)).sub ((h a b).smul α)).sub ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Rel.one.smul β`. Conclude with `Rel.zero`.
-/
theorem rel_qop {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → ι → Module.End ℂ V}
    {G' : ι → ι → Module.End ℂ (N' ⧸ below N N')} (h : ∀ a b, Rel N N' (G a b) (G' a b)) (α β : ℂ) (a b : ι) :
    Rel N N' (qop G α β a b) (qop G' α β a b) := by
  unfold qop
  refine ((Rel.sum _ fun c => (h a c).mul (h c b)).sub ((h a b).smul α)).sub ?_
  split_ifs
  · exact Rel.one.smul β
  · exact Rel.zero

/- English proof (translation)
The claim follows from `Rel.neg (h b a)`.
-/
theorem rel_negT {ι : Type} {G : ι → ι → Module.End ℂ V}
    {G' : ι → ι → Module.End ℂ (N' ⧸ below N N')} (h : ∀ a b, Rel N N' (G a b) (G' a b)) (a b : ι) :
    Rel N N' (negT G a b) (negT G' a b) := Rel.neg (h b a)

end GlobalTheory.HoweR.SubQuot

namespace GlobalTheory.HoweR

open SubQuot in

/- English proof (translation)
Introduce `p q α β α' β'`. Take `⟨R, hR⟩` from `GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic (Ix p q) (fun a => a.isLeft) α β α' β'`. Take `⟨B, hB⟩` from `exists_rat_gt R`. Use `⟨B, ?_⟩` and prove the remaining obligations. Introduce `V _ _ act hG N N' hlt hN hN' hQ`.

Set `K` to `below N N'`. Set `A` to `quoA act N N' hN hN'`. Establish `hmk : ∀ Z (x : N'), A Z (K.mkQ x) = K.mkQ (resA act N' hN' Z x)` using `fun _ _ => rfl`. Establish `hlie : IsLieAct A`. Introduce `X Y`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `K.mkQ_surjective v`. Establish `e : resA act N' hN' (X * Y - Y * X) x = resA act N' hN' X (resA act N' hN' Y x) - resA act N' hN' Y (resA act N' hN' X x)`. Use `ext`. Simplify using `only [resA_coe, Submodule.coe_sub, hG.1 X Y, LinearMap.sub_apply, Module.End.mul_apply]`.

Rewrite using `[hmk, e, map_sub]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hmk]`. Establish `hwts : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub A μ`. Introduce `v`. Take `⟨x, rfl⟩` from `K.mkQ_surjective v`.

Establish `h1` using `GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q V act N' (fun a => hN' _) x x.2 (hG.2.1 x)`. Establish `h2 : (⨆ μ : Ix p q → ℚ, N' ⊓ wtSub act μ) ≤ ((⨆ μ : Ix p q → ℚ, wtSub A μ).comap K.mkQ).map N'.subtype`. Use `iSup_le fun μ y hy => ⟨⟨y, (Submodule.mem_inf.1 hy).1⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show K.mkQ ⟨y, (Submodule.mem_inf.1 hy).1⟩ ∈ ⨆ μ : Ix p q → ℚ, wtSub A μ`. Use `Submodule.mem_iSup_of_mem μ ?_` and prove the remaining obligations.

Establish `hy2` using `mem_wtSub'.1 (Submodule.mem_inf.1 hy).2`. Use `mem_wtSub'.2 fun a => ?_` and prove the remaining obligations. Rewrite using `[hmk, ← map_smul]`. Use `congr 1`. Use `ext`.

Conclude with `hy2 a`. Take `⟨y, hy, hyx⟩` from `h2 h1`. Establish `: y = x` using `Subtype.ext hyx`. Conclude with `this ▸ hy`. Establish `hres : LocU (fun a : Ix p q => a.isLeft) (units (resA act N' hN'))` using `(GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner (Ix p q) N' (fun a => a.isLeft) (units (resA act N' hN')) V (units act) N'.subtype Subtype.val_injective (fun a b _ x => rfl)).2 hG.2.2`.

Establish `hloc : LocU (fun a : Ix p q => a.isLeft) (units A)` using `GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range (Ix p q) N' (fun a => a.isLeft) (units (resA act N' hN')) (N' ⧸ K) (units A) {K.mkQ} (by`. Introduce `f hf a b _ x`. Rewrite `hf` using `[Set.mem_singleton_iff]`. Substitute `hf` using the available equality. Use the proof step `rfl)`.

Use the proof step `(by simp) hres`. Establish `hrel : ∀ a b, Rel N N' (units act a b) (units A a b)` using `fun a b x => ⟨resA act N' hN' (Eab a b) x, rfl, rfl⟩`. Establish `hq1 : ∀ a b, qop (units A) α β a b = 0`. Introduce `a b`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `K.mkQ_surjective v`. Take `⟨y, hy, e⟩` from `rel_qop hrel α β a b x`. Rewrite using `[LinearMap.zero_apply, e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `show (y : V) ∈ N`. Rewrite using `[hy]`.

Conclude with `(hQ a b x x.2).1`. Establish `hq2 : ∀ a b, qop (negT (units A)) α' β' a b = 0`. Introduce `a b`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `K.mkQ_surjective v`.

Take `⟨y, hy, e⟩` from `rel_qop (rel_negT hrel) α' β' a b x`. Rewrite using `[LinearMap.zero_apply, e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `show (y : V) ∈ N`. Rewrite using `[hy]`. Conclude with `(hQ a b x x.2).2`.

Take `⟨x₀, hx₀', hx₀⟩` from `SetLike.exists_of_lt hlt`. Establish `hx0 : K.mkQ ⟨x₀, hx₀'⟩ ≠ 0`. Rewrite using `[Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]`. Conclude with `hx₀`. Establish `hnt : Nontrivial (N' ⧸ K)` using `⟨⟨_, 0, hx0⟩⟩`.

Establish `hgl : IsGl (units A)` using `(GlobalTheory.HoweR.lie_units_stab p q (N' ⧸ K) A).1 hlie`. Take `⟨U, hU0, hUu, hUb⟩` from `hR (N' ⧸ K) (units A) hnt hgl hq1 hq2 hloc`. Establish `hKS : KStable A U` using `((GlobalTheory.HoweR.lie_units_stab p q (N' ⧸ K) A).2.1 U).1 hUu.2.1`. Use `haveI : FiniteDimensional ℂ U := hUu.1`. Take `⟨μ, v, hvU, hv0, hvhw⟩` from `GlobalTheory.HoweR.exists_isHW_of_fd p q (N' ⧸ K) A hlie hwts U hU0 hUu.1 hKS`.

Establish `hbd : ∀ a, |μ a| ≤ B`. Introduce `a`. Establish `h` using `hUb a v hvU hv0 ((μ a : ℚ) : ℂ) ((mem_hwSub'.1 hvhw).1 a)`. Rewrite `h` using `[Complex.ratCast_re]`. Conclude with `h.trans hB.le` after adjusting the coercions.

Take `⟨x, rfl⟩` from `K.mkQ_surjective v`. Establish `hc : ∀ c, act (Eab c c) (x : V) - ((μ c : ℚ) : ℂ) • (x : V) ∈ N`. Introduce `c`. Establish `e : K.mkQ (resA act N' hN' (Eab c c) x) = K.mkQ (((μ c : ℚ) : ℂ) • x)`. Rewrite using `[← hmk, map_smul]`.

Conclude with `(mem_hwSub'.1 hvhw).1 c`. Conclude with `(Submodule.Quotient.eq K).1 e`. Establish `hd : ∀ c d, posC c d → act (Eab c d) (x : V) ∈ N`. Introduce `c d hcd`. Establish `e : K.mkQ (resA act N' hN' (Eab c d) x) = 0`.

Rewrite using `[← hmk]`. Conclude with `(mem_hwSub'.1 hvhw).2 c d hcd`. Rewrite `e` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `e`. Establish `kst : ∀ W : Submodule ℂ V, Stab act W → KStable act W` using `fun W hW X _ w hw => hW X w hw`.

Take `⟨v', hv'N', hv'hw, hxv'⟩` from `GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG N N' (kst N hN) (kst N' hN') μ (x : V) x.2 hc hd`. Use `⟨μ, hbd, v', hv'N', hv'hw, fun hv'N => hv0 ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `show (x : V) ∈ N`. Simplify using `using N.add_mem hxv' hv'N`.
-/
theorem exists_hwSub_of_quadMod : ∀ (p q : ℕ) (α β α' β' : ℂ), ∃ B : ℚ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, N < N' → Stab act N →
    Stab act N' → QuadMod act α β α' β' N N' →
    ∃ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) ∧ ∃ v ∈ N', v ∈ hwSub act μ ∧ v ∉ N := by
  intro p q α β α' β'
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic (Ix p q) (fun a => a.isLeft) α β α' β'
  obtain ⟨B, hB⟩ := exists_rat_gt R
  refine ⟨B, ?_⟩
  intro V _ _ act hG N N' hlt hN hN' hQ
  let K := below N N'
  let A := quoA act N N' hN hN'
  have hmk : ∀ Z (x : N'), A Z (K.mkQ x) = K.mkQ (resA act N' hN' Z x) := fun _ _ => rfl

  have hlie : IsLieAct A := by
    intro X Y
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    have e : resA act N' hN' (X * Y - Y * X) x =
        resA act N' hN' X (resA act N' hN' Y x) - resA act N' hN' Y (resA act N' hN' X x) := by
      ext
      simp only [resA_coe, Submodule.coe_sub, hG.1 X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rw [hmk, e, map_sub]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hmk]

  have hwts : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub A μ := by
    intro v
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    have h1 := GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q V act N' (fun a => hN' _) x x.2 (hG.2.1 x)
    have h2 : (⨆ μ : Ix p q → ℚ, N' ⊓ wtSub act μ) ≤
        ((⨆ μ : Ix p q → ℚ, wtSub A μ).comap K.mkQ).map N'.subtype := by
      refine iSup_le fun μ y hy => ⟨⟨y, (Submodule.mem_inf.1 hy).1⟩, ?_, rfl⟩
      show K.mkQ ⟨y, (Submodule.mem_inf.1 hy).1⟩ ∈ ⨆ μ : Ix p q → ℚ, wtSub A μ
      refine Submodule.mem_iSup_of_mem μ ?_
      have hy2 := mem_wtSub'.1 (Submodule.mem_inf.1 hy).2
      refine mem_wtSub'.2 fun a => ?_
      rw [hmk, ← map_smul]
      congr 1
      ext
      exact hy2 a
    obtain ⟨y, hy, hyx⟩ := h2 h1
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

  have hres : LocU (fun a : Ix p q => a.isLeft) (units (resA act N' hN')) :=
    (GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner (Ix p q) N' (fun a => a.isLeft) (units (resA act N' hN')) V (units act) N'.subtype
      Subtype.val_injective (fun a b _ x => rfl)).2 hG.2.2
  have hloc : LocU (fun a : Ix p q => a.isLeft) (units A) :=
    GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range (Ix p q) N' (fun a => a.isLeft) (units (resA act N' hN')) (N' ⧸ K) (units A) {K.mkQ}
      (by
        intro f hf a b _ x
        rw [Set.mem_singleton_iff] at hf
        subst hf
        rfl)
      (by simp) hres

  have hrel : ∀ a b, Rel N N' (units act a b) (units A a b) :=
    fun a b x => ⟨resA act N' hN' (Eab a b) x, rfl, rfl⟩
  have hq1 : ∀ a b, qop (units A) α β a b = 0 := by
    intro a b
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    obtain ⟨y, hy, e⟩ := rel_qop hrel α β a b x
    rw [LinearMap.zero_apply, e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (y : V) ∈ N
    rw [hy]
    exact (hQ a b x x.2).1
  have hq2 : ∀ a b, qop (negT (units A)) α' β' a b = 0 := by
    intro a b
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    obtain ⟨y, hy, e⟩ := rel_qop (rel_negT hrel) α' β' a b x
    rw [LinearMap.zero_apply, e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (y : V) ∈ N
    rw [hy]
    exact (hQ a b x x.2).2

  obtain ⟨x₀, hx₀', hx₀⟩ := SetLike.exists_of_lt hlt
  have hx0 : K.mkQ ⟨x₀, hx₀'⟩ ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hx₀
  have hnt : Nontrivial (N' ⧸ K) := ⟨⟨_, 0, hx0⟩⟩
  have hgl : IsGl (units A) := (GlobalTheory.HoweR.lie_units_stab p q (N' ⧸ K) A).1 hlie
  obtain ⟨U, hU0, hUu, hUb⟩ := hR (N' ⧸ K) (units A) hnt hgl hq1 hq2 hloc
  have hKS : KStable A U := ((GlobalTheory.HoweR.lie_units_stab p q (N' ⧸ K) A).2.1 U).1 hUu.2.1
  haveI : FiniteDimensional ℂ U := hUu.1
  obtain ⟨μ, v, hvU, hv0, hvhw⟩ := GlobalTheory.HoweR.exists_isHW_of_fd p q (N' ⧸ K) A hlie hwts U hU0 hUu.1 hKS
  have hbd : ∀ a, |μ a| ≤ B := by
    intro a
    have h := hUb a v hvU hv0 ((μ a : ℚ) : ℂ) ((mem_hwSub'.1 hvhw).1 a)
    rw [Complex.ratCast_re] at h
    exact_mod_cast h.trans hB.le
  obtain ⟨x, rfl⟩ := K.mkQ_surjective v
  have hc : ∀ c, act (Eab c c) (x : V) - ((μ c : ℚ) : ℂ) • (x : V) ∈ N := by
    intro c
    have e : K.mkQ (resA act N' hN' (Eab c c) x) = K.mkQ (((μ c : ℚ) : ℂ) • x) := by
      rw [← hmk, map_smul]
      exact (mem_hwSub'.1 hvhw).1 c
    exact (Submodule.Quotient.eq K).1 e
  have hd : ∀ c d, posC c d → act (Eab c d) (x : V) ∈ N := by
    intro c d hcd
    have e : K.mkQ (resA act N' hN' (Eab c d) x) = 0 := by
      rw [← hmk]
      exact (mem_hwSub'.1 hvhw).2 c d hcd
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at e
    exact e
  have kst : ∀ W : Submodule ℂ V, Stab act W → KStable act W := fun W hW X _ w hw => hW X w hw
  obtain ⟨v', hv'N', hv'hw, hxv'⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG N N' (kst N hN) (kst N' hN') μ (x : V) x.2 hc hd
  refine ⟨μ, hbd, v', hv'N', hv'hw, fun hv'N => hv0 ?_⟩
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show (x : V) ∈ N
  simpa using N.add_mem hxv' hv'N

end GlobalTheory.HoweR
