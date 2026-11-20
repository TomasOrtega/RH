import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CentralSupport

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`. Consider the case `smul_tprod r x`. Rewrite using `[map_smul, smul_comm, piTensor_tprod]`. Use `congr 1`.

Simplify using `only [h]`. Conclude with `MultilinearMap.map_smul_univ _ _ _`.
-/
theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (y : ⨂[ℂ] a, X a) : piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _

/- English proof (translation)
Simplify using `only [modExp, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter]`. Rewrite using `[sub_eq_zero, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, absPow_add]`.
-/
theorem prod_absPow {α : Type} (S : Finset α) (c : α → ℂ) : ∏ a ∈ S, absPow k (c a) = absPow k (∑ a ∈ S, c a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, absPow_add]

/- English proof (translation)
Use `ext`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, val_absPow, val_absPow, Complex.cpow_nat_mul]`.
-/
theorem absPow_pow (s : ℂ) (N : ℕ) (z : kˣ) : absPow k s (z ^ N) = absPow k (N * s) z := by
  ext
  rw [map_pow, Units.val_pow_eq_pow_val, val_absPow, val_absPow, Complex.cpow_nat_mul]

/- English proof (translation)
Establish `hd : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a)` using `fun a => by ext; simp [GeneralLinearGroup.scalar]`. Rewrite using `[deltaHalf_apply]`. Simplify using `only [hd, absPow_pow]`. Rewrite using `[← MonoidHom.finsetProd_apply, prod_absPow]`. Establish `h0 : ∑ a, ((Fintype.card (m a) : ℕ) : ℂ) * ((modExp m a : ℂ) / 2) = 0`.

Use `congrArg (fun t : ℤ => (t : ℂ) / 2) (sum_card_mul_modExp m)` as an intermediate fact. Simplify using `only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero, zero_div, Finset.sum_div] at this`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h0, absPow_zero, MonoidHom.one_apply]`.
-/
theorem deltaHalf_scalar {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) : deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have hd : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) := fun a => by
    ext; simp [GeneralLinearGroup.scalar]
  rw [deltaHalf_apply]
  simp only [hd, absPow_pow]
  rw [← MonoidHom.finsetProd_apply, prod_absPow]
  have h0 : ∑ a, ((Fintype.card (m a) : ℕ) : ℂ) * ((modExp m a : ℂ) / 2) = 0 := by
    have := congrArg (fun t : ℤ => (t : ℂ) / 2) (sum_card_mul_modExp m)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero, zero_div, Finset.sum_div] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h0, absPow_zero, MonoidHom.one_apply]

/- English proof (translation)
Introduce `z f`. Establish `h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (c a) z) = GeneralLinearGroup.scalar n z`. Use extensionality with `i j`. Take `⟨⟨b, y⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b', y'⟩, rfl⟩` from `e.surjective j`.

Distinguish the cases in `hb : b = b'`. Substitute `hb` using the available equality. Rewrite using `[leviEmb_apply_same]`. Simplify using `[GeneralLinearGroup.scalar, diagonal_apply]`. Rewrite using `[leviEmb_apply_ne _ _ _ hb]`.

Simplify using `[GeneralLinearGroup.scalar, diagonal_apply, hb]`. Establish `h4` using `parInd_law e (piTensor σ) f ⟨_, leviEmb_mem_parab k e (fun a => GeneralLinearGroup.scalar (c a) z)⟩`. Use `Subtype.ext (Subtype.ext (funext fun x => ?_))` and prove the remaining obligations. Establish `h5` using `h4 x`. Rewrite `h5` using `[leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar σ _ (fun a => (ω a z : ℂ)) (fun a => hω a z)]`.

Establish `hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x`. Use extensionality with `i j`. Simplify using `[GeneralLinearGroup.scalar, mul_comm]`. Use `show f.1.1 (x * GeneralLinearGroup.scalar n z) = ((∏ a, ω a) z : ℂ) • f.1.1 x`. Rewrite using `[hc, ← h1, MonoidHom.finsetProd_apply, Units.coe_prod]`.

Simplify using `using h5`.
-/
theorem hasCentralChar_multiProd_prod {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (ω : α → kˣ →* ℂˣ)
    (hω : ∀ a, HasCentralChar (σ a) (ω a)) : HasCentralChar (multiProd e σ) (∏ a, ω a) := by
  intro z f
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (c a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne _ _ _ hb]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hb]
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (fun a => GeneralLinearGroup.scalar (c a) z)⟩
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h5 := h4 x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar σ _ (fun a => (ω a z : ℂ)) (fun a => hω a z)] at h5
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = ((∏ a, ω a) z : ℂ) • f.1.1 x
  rw [hc, ← h1, MonoidHom.finsetProd_apply, Units.coe_prod]
  simpa using h5

/- English proof (translation)
Introduce `_ k _ _ _ _ _ x s ω hs hω`. Use `choose f _ hf using fun y : IrrGL k => LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr`. Use `⟨f, fun y _ => hf y, fun z => ?_⟩` and prove the remaining obligations. Take `⟨h, x', rfl, hi, -, e, hsub⟩` from `hs`. Establish `hcen` using `hasCentralChar_multiProd_prod e (fun a => (x' a).rep) (fun a => f (x' a)) (fun a => hf (x' a))`.

Use `Model.nontrivial_of_isIrreducible hi` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : x.2.rep.V)`. Establish `h1` using `Model.scalar_of_isSubquotient hsub (hcen z) v`. Rewrite `h1` using `[hω]`. Establish `h2` using `smul_left_injective ℂ hv h1`.

Rewrite using `[Multiset.map_map]`. Express the relevant statement in the definitionally equal form `ω z = ∏ a, f (x' a) z`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[h2, MonoidHom.finsetProd_apply]`.
-/
theorem centralChar_eq_prod_support : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s : Multiset (IrrGL k))
    (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL k → kˣ →* ℂˣ,
      (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  intro _ k _ _ _ _ _ x s ω hs hω
  choose f _ hf using fun y : IrrGL k => LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  refine ⟨f, fun y _ => hf y, fun z => ?_⟩
  obtain ⟨h, x', rfl, hi, -, e, hsub⟩ := hs
  have hcen := hasCentralChar_multiProd_prod e (fun a => (x' a).rep) (fun a => f (x' a)) (fun a => hf (x' a))
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
  rw [hω] at h1
  have h2 := smul_left_injective ℂ hv h1
  rw [Multiset.map_map]
  change ω z = ∏ a, f (x' a) z
  apply Units.ext
  rw [h2, MonoidHom.finsetProd_apply]

end GlobalTheory.CentralSupport
