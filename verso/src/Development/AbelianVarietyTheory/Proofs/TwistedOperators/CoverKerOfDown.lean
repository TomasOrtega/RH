import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
open GlobalTheory.RealPar.DerivedAdjoint
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.CoverKernel

variable {p q r s : ℕ}

/- English proof (translation)
Establish `hs : star ((2:ℂ)⁻¹) = (2:ℂ)⁻¹` using `by simp`. Establish `hs' : star (-(Complex.I * (2:ℂ)⁻¹)) = Complex.I * (2:ℂ)⁻¹`. Simplify using `[Complex.conj_I]`. Establish `hc : Complex.I * -(Complex.I * (2:ℂ)⁻¹) = (2:ℂ)⁻¹`. Take the linear combination `(-(2:ℂ)⁻¹) * Complex.I_sq`.

Use `⟨(2:ℂ)⁻¹ • (Z - adjZ Z), (-(Complex.I * (2:ℂ)⁻¹)) • (Z + adjZ Z), mem_upq_of_adjZ ?_, mem_upq_of_adjZ ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[adjZ_smul, adjZ_sub, adjZ_adjZ, hs] module`. Rewrite using `[adjZ_smul, adjZ_add, adjZ_adjZ, hs'] module`. Rewrite using `[smul_smul, hc] module`. Rewrite using `[smul_smul, hc] module`.
-/
theorem exists_real_imag (Z : Mat p q) : ∃ X Y : Mat p q, X ∈ upq p q ∧ Y ∈ upq p q ∧
    Z = X + Complex.I • Y ∧ adjZ Z = -X + Complex.I • Y := by
  have hs : star ((2:ℂ)⁻¹) = (2:ℂ)⁻¹ := by simp
  have hs' : star (-(Complex.I * (2:ℂ)⁻¹)) = Complex.I * (2:ℂ)⁻¹ := by
    simp [Complex.conj_I]
  have hc : Complex.I * -(Complex.I * (2:ℂ)⁻¹) = (2:ℂ)⁻¹ := by
    linear_combination (-(2:ℂ)⁻¹) * Complex.I_sq
  refine ⟨(2:ℂ)⁻¹ • (Z - adjZ Z), (-(Complex.I * (2:ℂ)⁻¹)) • (Z + adjZ Z),
    mem_upq_of_adjZ ?_, mem_upq_of_adjZ ?_, ?_, ?_⟩
  · rw [adjZ_smul, adjZ_sub, adjZ_adjZ, hs]
    module
  · rw [adjZ_smul, adjZ_add, adjZ_adjZ, hs']
    module
  · rw [smul_smul, hc]
    module
  · rw [smul_smul, hc]
    module

/- English proof (translation)
Introduce `X P P' y y'`. Take `⟨A, C, hA, hC, rfl, hadj⟩` from `exists_real_imag X`. Rewrite using `[hadj]`. Establish `sA` using `h.skew A hA P P' y y'`. Establish `sC` using `h.skew C hC P P' y y'`.

Simplify using `only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, Complex.conj_I]`. Take the linear combination `sA - Complex.I * sC`.
-/
theorem adjRule_of_pair {N : GKMod r s} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z} (h : IsCoverPair N B) : AdjRule B := by
  intro X P P' y y'
  obtain ⟨A, C, hA, hC, rfl, hadj⟩ := exists_real_imag X
  rw [hadj]
  have sA := h.skew A hA P P' y y'
  have sC := h.skew C hC P P' y y'
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, Complex.conj_I]
  linear_combination sA - Complex.I * sC

/- English proof (translation)
Introduce `Y P y`. Take `⟨A, C, hA, hC, rfl, hadj⟩` from `exists_real_imag Y`. Rewrite using `[hadj]`. Establish `iA` using `eq_neg_of_add_eq_zero_left (h.inv A hA P y)`. Establish `iC` using `eq_neg_of_add_eq_zero_left (h.inv C hC P y)`.

Simplify using `only [map_add, map_smul, map_neg, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, Complex.conj_I]`. Rewrite using `[iA, iC]`. Use `module`.
-/
theorem invRule_of_pair {N : GKMod r s} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z} (h : IsCoverPair N B) : InvRule N B := by
  intro Y P y
  obtain ⟨A, C, hA, hC, rfl, hadj⟩ := exists_real_imag Y
  rw [hadj]
  have iA := eq_neg_of_add_eq_zero_left (h.inv A hA P y)
  have iC := eq_neg_of_add_eq_zero_left (h.inv C hC P y)
  simp only [map_add, map_smul, map_neg, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, Complex.conj_I]
  rw [iA, iC]
  module

def pairSum {U Y Z₁ Z₂ : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₂) :
    U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] WithLp 2 (Z₁ × Z₂) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => WithLp.toLp 2 (B₁ P y, B₂ P y))
    (fun _ _ _ => by simp [← WithLp.toLp_add])
    (fun _ _ _ => by simp [← WithLp.toLp_smul])
    (fun _ _ _ => by simp [← WithLp.toLp_add])
    (fun _ _ _ => by simp [← WithLp.toLp_smul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairSum_apply {U Y Z₁ Z₂ : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₂) (P : U) (y : Y) :
    pairSum B₁ B₂ P y = WithLp.toLp 2 (B₁ P y, B₂ P y) := rfl

/- English proof (translation)
Simplify using `[contr]`.
-/
theorem contr_tmul {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  simp [contr]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v => simp only [TensorProduct.map_tmul, LinearMap.id_apply, contr_tmul, map_smul]`. Consider the case `add x w hx hw => simp only [map_add, hx, hw]`.
-/
theorem contr_map_left {A A' V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) (g : A →ₗ[ℂ] A') (t : A ⊗[ℂ] V) :
    contr ι y (TensorProduct.map g LinearMap.id t) = g (contr ι y t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp only [TensorProduct.map_tmul, LinearMap.id_apply, contr_tmul, map_smul]
  | add x w hx hw => simp only [map_add, hx, hw]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v`. Simplify using `only [TensorProduct.map_tmul, LinearMap.id_apply, contr_tmul]`. Use `congr 1`.

Establish `key` using `derived_adjoint r s T R.U R.HK R.ι R.der (adjZ Y) y v`. Rewrite `key` using `[adjZ_adjZ]`. Conclude with `key.symm`. Consider the case `add x w hx hw => simp only [map_add, hx, hw]`.
-/
theorem contr_map_right {A : Type} [AddCommGroup A] [Module ℂ A] {T : GrpData r s} (R : DSRep T)
    (Y : Mat r s) (y : R.HK.V) (t : A ⊗[ℂ] R.HK.V) :
    contr R.ι y (TensorProduct.map LinearMap.id (R.HK.act Y) t) = contr R.ι (R.HK.act (adjZ Y) y) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, contr_tmul]
    congr 1
    have key := derived_adjoint r s T R.U R.HK R.ι R.der (adjZ Y) y v
    rw [adjZ_adjZ] at key
    exact key.symm
  | add x w hx hw => simp only [map_add, hx, hw]

/- English proof (translation)
Establish `hx : x ∈ Submodule.span ℂ S`. Rewrite using `[hS]`. Conclude with `Submodule.mem_top`. Establish `hw : w ∈ Submodule.span ℂ S`. Rewrite using `[hS]`.

Conclude with `Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hxS`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hwS => exact h x hxS w hwS`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp only [map_add, inner_add_right, ha, hb]`. Consider the case `smul c a _ ha => simp only [map_smul, inner_smul_right, ha]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp only [map_add, inner_add_left, ha, hb]`.

Consider the case `smul c a _ ha => simp only [map_smul, inner_smul_left, ha]`.
-/
private theorem inner_eq_inner_of_eq_on_spanning {V W : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {S : Set V} (hS : Submodule.span ℂ S = ⊤) (f g k l : V →ₗ[ℂ] W)
    (h : ∀ x ∈ S, ∀ w ∈ S, ⟪f x, g w⟫_ℂ = ⟪k x, l w⟫_ℂ) (x w : V) : ⟪f x, g w⟫_ℂ = ⟪k x, l w⟫_ℂ := by
  have hx : x ∈ Submodule.span ℂ S := by
    rw [hS]
    exact Submodule.mem_top
  have hw : w ∈ Submodule.span ℂ S := by
    rw [hS]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hxS =>
    induction hw using Submodule.span_induction with
    | mem w hwS => exact h x hxS w hwS
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, inner_add_right, ha, hb]
    | smul c a _ ha => simp only [map_smul, inner_smul_right, ha]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, inner_add_left, ha, hb]
  | smul c a _ ha => simp only [map_smul, inner_smul_left, ha]

/- English proof (translation)
Introduce `X p q r s lam lam' hD hIrr hU hF hT Z₁ Z₂ _ _ _ _ B₁ B₂ h₁ h₂ hne`. Unfold `Formalism.MainNotions.SchurIrreducible.ARiiiDown at hD`. Unfold `Formalism.MainNotions.SchurIrreducible.IrrGK at hIrr`. Unfold `UnitaryImage at hU`. Unfold `FiniteSupport at hF`.

Unfold `TensorForm at hT`. Establish `hB : IsCoverPair (X.ds r s lam').HK (pairSum B₁ B₂)`. Prove the components needed by the constructor for the conclusion. Introduce `Y hY P P' y y'`. Simplify using `only [pairSum_apply, WithLp.prod_inner_apply]`.

Take the linear combination `h₁.skew Y hY P P' y y' + h₂.skew Y hY P P' y y'`. Introduce `Y hY P y`. Rewrite using `[pairSum_apply, pairSum_apply, ← WithLp.toLp_add, Prod.mk_add_mk, h₁.inv Y hY P y, h₂.inv Y hY P y, Prod.mk_zero_zero, WithLp.toLp_zero]`. Take `⟨A, j, B', hj, hjB, hspan, hB'act⟩` from `hU _ _ (pairSum B₁ B₂) (adjRule_of_pair hB)`. Establish `hinv' : InvRule (X.ds r s lam').HK B'`.

Introduce `Y P y`. Apply `hj` to reduce the goal to its premises. Rewrite using `[hjB, hjB]`. Conclude with `invRule_of_pair hB Y P y`. Take `⟨hsep, hfac⟩` from `hT (Pol p q r s) A.M.V (X.ds r s lam').HK.V (X.ds r s lam').U.H (X.ds r s lam').ι (X.ds r s lam').ι_inj`.

Take `⟨f, hf⟩` from `hfac B' (hF A.M.V B' hinv')`. Establish `hint1 : ∀ Y : Mat p q, f ∘ₗ (X.fock p q r s).act1 Y = TensorProduct.map (A.M.act Y) LinearMap.id ∘ₗ f`. Introduce `Y`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `hsep _ fun y => ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, contr_map_left, hf, hf]`. Conclude with `hB'act Y P y`. Establish `hint2 : ∀ Y : Mat r s, f ∘ₗ (X.fock p q r s).act2 Y = TensorProduct.map LinearMap.id ((X.ds r s lam').HK.act Y) ∘ₗ f`. Introduce `Y`.

Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `hsep _ fun y => ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, contr_map_right, hf, hf]`. Conclude with `hinv' Y P y`.

Establish `hψ : ∀ P y, WithLp.ofLp (j (B' P y)) = (B₁ P y, B₂ P y)`. Introduce `P y`. Rewrite using `[hjB, pairSum_apply, WithLp.ofLp_toLp]`. Establish `hfne : f ≠ 0`. Introduce `hf0`.

Apply `hne` to reduce the goal to its premises. Use `LinearMap.ext fun P => LinearMap.ext fun y => ?_` and prove the remaining obligations. Establish `h0 : B' P y = 0` using `by rw [← hf, hf0, LinearMap.zero_apply, map_zero]`. Establish `h1` using `hψ P y`. Rewrite `h1` using `[h0, map_zero, WithLp.ofLp_zero]`.

Take `⟨e1, -⟩` from `Prod.mk.inj (h1.symm.trans Prod.mk_zero_zero.symm)`. Rewrite using `[LinearMap.zero_apply, LinearMap.zero_apply]`. Conclude with `e1`. Establish `hIW : Formalism.BasicNotions.TH.IsIntw (X.fock p q r s) A.M (X.ds r s lam').HK f`. Unfold `Formalism.BasicNotions.TH.IsIntw`.

Conclude with `⟨hint1, hint2⟩`. Take `⟨⟨N, -, e, he, hrange⟩, -⟩` from `hD A f hIW hfne`. Establish `memN : ∀ P y, B' P y ∈ N`. Introduce `P y`. Establish `hP : f P ∈ LinearMap.range (TensorProduct.map N.subtype LinearMap.id)`.

Rewrite using `[← hrange]`. Conclude with `LinearMap.mem_range_self f P`. Take `⟨t, ht⟩` from `LinearMap.mem_range.mp hP`. Rewrite using `[← hf, ← ht, contr_map_left]`. Conclude with `(contr (X.ds r s lam').ι y t).2`.

Set `ψ₁ : A.M.V →ₗ[ℂ] Z₁` to `LinearMap.fst ℂ Z₁ Z₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (Z₁ × Z₂)).toLinearMap ∘ₗ j`. Set `ψ₂ : A.M.V →ₗ[ℂ] Z₂` to `LinearMap.snd ℂ Z₁ Z₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (Z₁ × Z₂)).toLinearMap ∘ₗ j`. Establish `hψ₁ : ∀ P y, ψ₁ (B' P y) = B₁ P y` using `fun P y => congrArg Prod.fst (hψ P y)`. Establish `hψ₂ : ∀ P y, ψ₂ (B' P y) = B₂ P y` using `fun P y => congrArg Prod.snd (hψ P y)`. Establish `hsesq : ∀ (Y : Mat p q) (x w : A.M.V), ⟪ψ₁ (A.M.act Y x), ψ₁ w⟫_ℂ = ⟪ψ₁ x, ψ₁ (A.M.act (adjZ Y) w)⟫_ℂ`.

Introduce `Y`. Use `inner_eq_inner_of_eq_on_spanning hspan (ψ₁ ∘ₗ A.M.act Y) ψ₁ ψ₁ (ψ₁ ∘ₗ A.M.act (adjZ Y)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨P, y, rfl⟩ _ ⟨P', y', rfl⟩`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[← hB'act, ← hB'act]`.

Simplify using `only [hψ₁]`. Conclude with `adjRule_of_pair h₁ Y P P' y y'`. Establish `hstab : ∀ (Y : Mat p q) (x : A.M.V), ψ₁ x = 0 → ψ₁ (A.M.act Y x) = 0`. Introduce `Y x hx`. Establish `h1` using `hsesq Y x (A.M.act Y x)`.

Rewrite `h1` using `[hx, inner_zero_left]`. Conclude with `inner_self_eq_zero.mp h1`. Set `N' : Submodule ℂ (X.ds p q lam).HK.V` to `(LinearMap.ker ψ₁).comap (N.subtype ∘ₗ e.toLinearMap)`. Establish `hN'st : ∀ (Y : Mat p q), ∀ x ∈ N', (X.ds p q lam).HK.act Y x ∈ N'`. Introduce `Y x hx`.

Establish `hx' : ψ₁ ((e x : N) : A.M.V) = 0` using `hx`. Use `show ψ₁ ((e ((X.ds p q lam).HK.act Y x) : N) : A.M.V) = 0`. Rewrite using `[he]`. Conclude with `hstab Y _ hx'`. Break down `hIrr.2 N' hN'st with hbot | htop` into its components or cases.

Introduce `n a b hsum`. Establish `hwN : ∑ i, B' (a i) (b i) ∈ N` using `Submodule.sum_mem _ fun i _ => memN (a i) (b i)`. Establish `h1 : ψ₁ (∑ i, B' (a i) (b i)) = 0`. Rewrite using `[map_sum]`. Simplify using `only [hψ₁]`.

Conclude with `hsum`. Establish `hz : e.symm ⟨_, hwN⟩ ∈ N'` using `by show ψ₁ ((e (e.symm ⟨_, hwN⟩) : N) : A.M.V) = 0`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1`. Rewrite `hz` using `[hbot, Submodule.mem_bot]`.

Establish `h0 : ∑ i, B' (a i) (b i) = 0`. Establish `h3` using `congrArg e hz`. Rewrite `h3` using `[LinearEquiv.apply_symm_apply, map_zero]`. Conclude with `congrArg Subtype.val h3`. Establish `h2` using `congrArg ψ₂ h0`.

Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [hψ₂] at h2`. Conclude with `h2`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises.

Use `LinearMap.ext fun P => LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply, LinearMap.zero_apply, ← hψ₁]`. Establish `hz : e.symm ⟨_, memN P y⟩ ∈ N'`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Establish `h1 : ψ₁ ((e (e.symm ⟨_, memN P y⟩) : N) : A.M.V) = 0` using `hz`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1`.
-/
theorem coverKer_of_down : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam lam' → Formalism.MainNotions.SchurIrreducible.IrrGK (X.ds p q lam).HK → UnitaryImage p q r s → FiniteSupport p q (X.ds r s lam') → TensorForm → CoverKer p q (X.ds r s lam').HK := by
  intro X p q r s lam lam' hD hIrr hU hF hT Z₁ Z₂ _ _ _ _ B₁ B₂ h₁ h₂ hne
  unfold Formalism.MainNotions.SchurIrreducible.ARiiiDown at hD
  unfold Formalism.MainNotions.SchurIrreducible.IrrGK at hIrr
  unfold UnitaryImage at hU
  unfold FiniteSupport at hF
  unfold TensorForm at hT

  have hB : IsCoverPair (X.ds r s lam').HK (pairSum B₁ B₂) := by
    constructor
    · intro Y hY P P' y y'
      simp only [pairSum_apply, WithLp.prod_inner_apply]
      linear_combination h₁.skew Y hY P P' y y' + h₂.skew Y hY P P' y y'
    · intro Y hY P y
      rw [pairSum_apply, pairSum_apply, ← WithLp.toLp_add, Prod.mk_add_mk, h₁.inv Y hY P y,
        h₂.inv Y hY P y, Prod.mk_zero_zero, WithLp.toLp_zero]

  obtain ⟨A, j, B', hj, hjB, hspan, hB'act⟩ := hU _ _ (pairSum B₁ B₂) (adjRule_of_pair hB)
  have hinv' : InvRule (X.ds r s lam').HK B' := by
    intro Y P y
    apply hj
    rw [hjB, hjB]
    exact invRule_of_pair hB Y P y

  obtain ⟨hsep, hfac⟩ := hT (Pol p q r s) A.M.V (X.ds r s lam').HK.V (X.ds r s lam').U.H
    (X.ds r s lam').ι (X.ds r s lam').ι_inj
  obtain ⟨f, hf⟩ := hfac B' (hF A.M.V B' hinv')
  have hint1 : ∀ Y : Mat p q,
      f ∘ₗ (X.fock p q r s).act1 Y = TensorProduct.map (A.M.act Y) LinearMap.id ∘ₗ f := by
    intro Y
    refine LinearMap.ext fun P => ?_
    rw [← sub_eq_zero]
    refine hsep _ fun y => ?_
    rw [map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, contr_map_left, hf, hf]
    exact hB'act Y P y
  have hint2 : ∀ Y : Mat r s,
      f ∘ₗ (X.fock p q r s).act2 Y = TensorProduct.map LinearMap.id ((X.ds r s lam').HK.act Y) ∘ₗ f := by
    intro Y
    refine LinearMap.ext fun P => ?_
    rw [← sub_eq_zero]
    refine hsep _ fun y => ?_
    rw [map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, contr_map_right, hf, hf]
    exact hinv' Y P y
  have hψ : ∀ P y, WithLp.ofLp (j (B' P y)) = (B₁ P y, B₂ P y) := by
    intro P y
    rw [hjB, pairSum_apply, WithLp.ofLp_toLp]
  have hfne : f ≠ 0 := by
    intro hf0
    apply hne
    refine LinearMap.ext fun P => LinearMap.ext fun y => ?_
    have h0 : B' P y = 0 := by rw [← hf, hf0, LinearMap.zero_apply, map_zero]
    have h1 := hψ P y
    rw [h0, map_zero, WithLp.ofLp_zero] at h1
    obtain ⟨e1, -⟩ := Prod.mk.inj (h1.symm.trans Prod.mk_zero_zero.symm)
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    exact e1
  have hIW : Formalism.BasicNotions.TH.IsIntw (X.fock p q r s) A.M (X.ds r s lam').HK f := by
    unfold Formalism.BasicNotions.TH.IsIntw
    exact ⟨hint1, hint2⟩

  obtain ⟨⟨N, -, e, he, hrange⟩, -⟩ := hD A f hIW hfne
  have memN : ∀ P y, B' P y ∈ N := by
    intro P y
    have hP : f P ∈ LinearMap.range (TensorProduct.map N.subtype LinearMap.id) := by
      rw [← hrange]
      exact LinearMap.mem_range_self f P
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hP
    rw [← hf, ← ht, contr_map_left]
    exact (contr (X.ds r s lam').ι y t).2

  let ψ₁ : A.M.V →ₗ[ℂ] Z₁ :=
    LinearMap.fst ℂ Z₁ Z₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (Z₁ × Z₂)).toLinearMap ∘ₗ j
  let ψ₂ : A.M.V →ₗ[ℂ] Z₂ :=
    LinearMap.snd ℂ Z₁ Z₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (Z₁ × Z₂)).toLinearMap ∘ₗ j
  have hψ₁ : ∀ P y, ψ₁ (B' P y) = B₁ P y := fun P y => congrArg Prod.fst (hψ P y)
  have hψ₂ : ∀ P y, ψ₂ (B' P y) = B₂ P y := fun P y => congrArg Prod.snd (hψ P y)

  have hsesq : ∀ (Y : Mat p q) (x w : A.M.V),
      ⟪ψ₁ (A.M.act Y x), ψ₁ w⟫_ℂ = ⟪ψ₁ x, ψ₁ (A.M.act (adjZ Y) w)⟫_ℂ := by
    intro Y
    refine inner_eq_inner_of_eq_on_spanning hspan (ψ₁ ∘ₗ A.M.act Y) ψ₁ ψ₁ (ψ₁ ∘ₗ A.M.act (adjZ Y)) ?_
    rintro _ ⟨P, y, rfl⟩ _ ⟨P', y', rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← hB'act, ← hB'act]
    simp only [hψ₁]
    exact adjRule_of_pair h₁ Y P P' y y'
  have hstab : ∀ (Y : Mat p q) (x : A.M.V), ψ₁ x = 0 → ψ₁ (A.M.act Y x) = 0 := by
    intro Y x hx
    have h1 := hsesq Y x (A.M.act Y x)
    rw [hx, inner_zero_left] at h1
    exact inner_self_eq_zero.mp h1

  let N' : Submodule ℂ (X.ds p q lam).HK.V := (LinearMap.ker ψ₁).comap (N.subtype ∘ₗ e.toLinearMap)
  have hN'st : ∀ (Y : Mat p q), ∀ x ∈ N', (X.ds p q lam).HK.act Y x ∈ N' := by
    intro Y x hx
    have hx' : ψ₁ ((e x : N) : A.M.V) = 0 := hx
    show ψ₁ ((e ((X.ds p q lam).HK.act Y x) : N) : A.M.V) = 0
    rw [he]
    exact hstab Y _ hx'
  rcases hIrr.2 N' hN'st with hbot | htop
  · intro n a b hsum
    have hwN : ∑ i, B' (a i) (b i) ∈ N := Submodule.sum_mem _ fun i _ => memN (a i) (b i)
    have h1 : ψ₁ (∑ i, B' (a i) (b i)) = 0 := by
      rw [map_sum]
      simp only [hψ₁]
      exact hsum
    have hz : e.symm ⟨_, hwN⟩ ∈ N' := by
      show ψ₁ ((e (e.symm ⟨_, hwN⟩) : N) : A.M.V) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact h1
    rw [hbot, Submodule.mem_bot] at hz
    have h0 : ∑ i, B' (a i) (b i) = 0 := by
      have h3 := congrArg e hz
      rw [LinearEquiv.apply_symm_apply, map_zero] at h3
      exact congrArg Subtype.val h3
    have h2 := congrArg ψ₂ h0
    rw [map_sum, map_zero] at h2
    simp only [hψ₂] at h2
    exact h2
  · exfalso
    apply hne
    refine LinearMap.ext fun P => LinearMap.ext fun y => ?_
    rw [LinearMap.zero_apply, LinearMap.zero_apply, ← hψ₁]
    have hz : e.symm ⟨_, memN P y⟩ ∈ N' := by
      rw [htop]
      exact Submodule.mem_top
    have h1 : ψ₁ ((e (e.symm ⟨_, memN P y⟩) : N) : A.M.V) = 0 := hz
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1

end GlobalTheory.Chain.IoLift.CoverKernel

end
