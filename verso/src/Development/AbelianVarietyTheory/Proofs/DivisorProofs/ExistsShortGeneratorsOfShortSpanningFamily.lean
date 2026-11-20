import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers

set_option autoImplicit false

noncomputable section

open NumberField Module

namespace GlobalTheory

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ N L s A hLfg h0 hsm hadd hsL hsp hA`. Use `letI : Module ℚ V := Module.compHom V (algebraMap ℚ K)`. Use `haveI : IsScalarTower ℚ K V := ⟨fun q a x => by show (q • a) • x = (algebraMap ℚ K q) • (a • x)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Establish `hspL : Submodule.span K (L : Set V) = ⊤` using `eq_top_iff.2 (hsp ▸ Submodule.span_mono hsL)`.

Establish `hrk : Formalism.HN.rkK L = Module.finrank K V`. Rewrite using `[Formalism.HN.rkK, hspL, finrank_top]`. Take `⟨t, hts, htsp, hti⟩` from `exists_linearIndependent K s`. Set `vb : Basis t K V` to `Basis.mk hti (by rw [Subtype.range_coe, htsp, hsp])`. Use `haveI : Finite t := Module.Finite.finite_basis vb`.

Use `haveI : Fintype t := Fintype.ofFinite t`. Establish `hm : Fintype.card t = Formalism.HN.rkK L` using `by rw [hrk, finrank_eq_card_basis vb]`. Take `⟨ω, hωi, hωb⟩` from `exists_short_independent_integers K`. Use `haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, Module.finrank_pos⟩⟩`. Set `ob : Basis (Fin (finrank ℚ K)) ℚ K` to `basisOfLinearIndependentOfCardEqFinrank hωi (by simp)`.

Establish `hob : ∀ k, ob k = (ω k : K)` using `fun k => by`. Simplify using `[ob, coe_basisOfLinearIndependentOfCardEqFinrank]`. Set `E : Basis (Fin (finrank ℚ K) × t) ℚ V` to `ob.smulTower vb`. Establish `hE : ∀ p, E p = ω p.1 • (p.2 : V)` using `fun p => by`. Rewrite using `[Basis.smulTower_apply, hob, Basis.mk_apply]`.

Conclude with `algebraMap_smul K (ω p.1) (p.2 : V)`. Establish `hN0 : ∀ σ, N σ 0 = 0` using `fun σ => by simpa using hsm σ 0 0`. Establish `hsum : ∀ σ {ι : Type} (S : Finset ι) (f : ι → V), N σ (∑ i ∈ S, f i) ≤ ∑ i ∈ S, N σ (f i)`. Introduce `σ ι S f`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => simp [hN0]`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(hadd σ _ _).trans (add_le_add le_rfl ih)`. Establish `hq : ∀ σ (q : ℚ) x, N σ (q • x) = |(q : ℝ)| * N σ x` using `fun σ q x => by`.

Use `hsm σ (algebraMap ℚ K q) x` as an intermediate fact. Rewrite `this` using `[eq_ratCast, map_ratCast, Complex.norm_ratCast]`. Conclude with `this`. Use `set C : ℝ := (finrank ℚ K : ℝ) ^ 3 * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A with hC`. Establish `hEle : ∀ σ p, N σ (E p) ≤ C` using `fun σ p => by`.

Rewrite using `[hE p, ← algebraMap_smul K (ω p.1) (p.2 : V), hsm]`. Establish `h1` using `hA _ (hts p.2.2) σ`. Conclude with `mul_le_mul (hωb σ p.1) h1 (h0 _ _) ((norm_nonneg _).trans (hωb σ p.1))`. Set `red : V → V` to `fun x => ∑ p, Int.fract (E.repr x p) • E p`. Establish `hred_sub : ∀ x, x - red x ∈ Submodule.span ℤ (Set.range E)` using `fun x => by`.

Establish `hx : x - red x = ∑ p, (⌊E.repr x p⌋ : ℤ) • E p`. Rewrite using `[sub_eq_iff_eq_add, ← Finset.sum_add_distrib]`. Use `conv_lhs => rw [← E.sum_repr x]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.floor_add_fract]`.

Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)`. Establish `hred_le : ∀ σ x, N σ (red x) ≤ ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C` using `fun σ x => by`. Use `(hsum σ _ _).trans ?_` and prove the remaining obligations. Establish `hle : ∀ p ∈ (Finset.univ : Finset (Fin (finrank ℚ K) × t)), N σ (Int.fract (E.repr x p) • E p) ≤ C` using `fun p _ => by`.

Rewrite using `[hq]`. Establish `h1 : |((Int.fract (E.repr x p) : ℚ) : ℝ)| ≤ 1`. Rewrite using `[abs_of_nonneg (Rat.cast_nonneg.2 (Int.fract_nonneg _))]`. Conclude with `(Int.fract_lt_one _).le` after adjusting the coercions. Conclude with `(mul_le_of_le_one_left (h0 _ _) h1).trans (hEle σ p)`.

Use `(Finset.sum_le_card_nsmul _ _ _ hle).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `haveI : NoZeroSMulDivisors ℤ V := ⟨fun {c x} h => by`.

Rewrite `h` using `[← Int.cast_smul_eq_zsmul K]`. Conclude with `(smul_eq_zero.1 h).imp_left Int.cast_eq_zero.1⟩`. Set `Lz` to `L.restrictScalars ℤ`. Use `haveI : Module.Finite ℤ Lz := Module.Finite.iff_fg.2 hLfg.restrictScalars`. Use `haveI : Module.Free ℤ Lz := Module.free_of_finite_type_torsion_free'`.

Set `ZB` to `Module.Free.chooseBasis ℤ Lz`. Set `bZ : Module.Free.ChooseBasisIndex ℤ Lz → V` to `fun j => (ZB j : V)`. Establish `hZq : LinearIndependent ℚ bZ` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 (ZB.linearIndependent.map' Lz.subtype (Submodule.ker_subtype _))`. Use `haveI : Module.Finite ℚ V := Module.Finite.of_basis E`. Establish `hcardZ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Lz) ≤ Fintype.card (Fin (finrank ℚ K) × t)`.

Rewrite using `[← finrank_eq_card_basis E]`. Conclude with `hZq.fintype_card_le_finrank`. Establish `hLz : Lz = Submodule.span ℤ (Set.range bZ)`. Rewrite using `[show Set.range bZ = Lz.subtype '' Set.range ZB from Set.range_comp _ _, ← Submodule.map_span, ZB.span_eq, Submodule.map_top, Submodule.range_subtype]`. Set `F : (Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz → V` to `Sum.elim E (fun j => red (bZ j))`.

Set `e` to `Fintype.equivFin ((Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz)`. Establish `hEL : ∀ p, E p ∈ L` using `fun p => by rw [hE]; exact L.smul_mem _ (hsL (hts p.2.2))`. Establish `hspanE : Submodule.span ℤ (Set.range E) ≤ Lz` using `Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hEL p)`. Establish `hrng : Set.range (F ∘ e.symm) = Set.range F` using `e.symm.surjective.range_comp F`. Establish `hbig : ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C ≤ max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A)`.

Use `le_trans (le_of_eq ?_) (le_max_right _ _)` and prove the remaining obligations. Rewrite using `[hC]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Fintype.card _, F ∘ e.symm, max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A), ⟨fun x => ?_, fun i σ => ?_, le_max_left _ _⟩, le_rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hrng]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : x ∈ Lz` using `hx`. Rewrite `hx'` using `[hLz]`. Use `(Submodule.span_le.2 ?_) hx'` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, rfl⟩`. Establish `h1 : red (bZ j) ∈ Submodule.span ℤ (Set.range F)` using `Submodule.subset_span ⟨Sum.inr j, rfl⟩`. Establish `h2 : bZ j - red (bZ j) ∈ Submodule.span ℤ (Set.range F)` using `Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨Sum.inl p, rfl⟩) (hred_sub _)`. Simplify using `using add_mem h2 h1`. Introduce `hx`.

Establish `: x ∈ Lz` using `(Submodule.span_le (p := Lz)).2 (by`. Introduce and unpack `_ ⟨q | j, rfl⟩`. Conclude with `hEL q`. Establish `h1 : bZ j ∈ Lz` using `(ZB j).2`. Establish `h2` using `hspanE (hred_sub (bZ j))`.

Establish `e1 : red (bZ j) = bZ j - (bZ j - red (bZ j))` using `by abel`. Use `show red (bZ j) ∈ Lz`. Rewrite using `[e1]`. Conclude with `sub_mem h1 h2) hx`. Conclude with `this`.

Use `le_trans ?_ hbig` and prove the remaining obligations. Rewrite using `[Function.comp_apply]`. Generalize the expression as in `e.symm i = q`. Break down `q with q | j` into its components or cases. Establish `hC0 : 0 ≤ C` using `(h0 σ _).trans (hEle σ q)`.

Establish `hpos : 0 < Fintype.card t` using `Fintype.card_pos_iff.2 ⟨q.2⟩`. Establish `h1 : (1 : ℝ) ≤ (finrank ℚ K : ℝ) * Formalism.HN.rkK L`. Rewrite using `[← hm]`. Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Module.finrank_pos.ne' hpos.ne')` after adjusting the coercions. Conclude with `(hEle σ q).trans (le_mul_of_one_le_left hC0 h1)`.

Conclude with `hred_le σ _`. Rewrite using `[Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hm]`. Rewrite `hcardZ` using `[Fintype.card_prod, Fintype.card_fin, hm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_isShortGen_of_short_span : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) →
    (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L →
    Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) →
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧
      abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧
      n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  intro K V _ _ _ _ _ _ _ N L s A hLfg h0 hsm hadd hsL hsp hA
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K V := ⟨fun q a x => by
    show (q • a) • x = (algebraMap ℚ K q) • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hspL : Submodule.span K (L : Set V) = ⊤ := eq_top_iff.2 (hsp ▸ Submodule.span_mono hsL)
  have hrk : Formalism.HN.rkK L = Module.finrank K V := by
    rw [Formalism.HN.rkK, hspL, finrank_top]

  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent K s
  let vb : Basis t K V := Basis.mk hti (by rw [Subtype.range_coe, htsp, hsp])
  haveI : Finite t := Module.Finite.finite_basis vb
  haveI : Fintype t := Fintype.ofFinite t
  have hm : Fintype.card t = Formalism.HN.rkK L := by rw [hrk, finrank_eq_card_basis vb]

  obtain ⟨ω, hωi, hωb⟩ := exists_short_independent_integers K
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let ob : Basis (Fin (finrank ℚ K)) ℚ K := basisOfLinearIndependentOfCardEqFinrank hωi (by simp)
  have hob : ∀ k, ob k = (ω k : K) := fun k => by
    simp [ob, coe_basisOfLinearIndependentOfCardEqFinrank]
  let E : Basis (Fin (finrank ℚ K) × t) ℚ V := ob.smulTower vb
  have hE : ∀ p, E p = ω p.1 • (p.2 : V) := fun p => by
    rw [Basis.smulTower_apply, hob, Basis.mk_apply]
    exact algebraMap_smul K (ω p.1) (p.2 : V)

  have hN0 : ∀ σ, N σ 0 = 0 := fun σ => by simpa using hsm σ 0 0
  have hsum : ∀ σ {ι : Type} (S : Finset ι) (f : ι → V), N σ (∑ i ∈ S, f i) ≤ ∑ i ∈ S, N σ (f i) := by
    intro σ ι S f
    induction S using Finset.induction_on with
    | empty => simp [hN0]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  have hq : ∀ σ (q : ℚ) x, N σ (q • x) = |(q : ℝ)| * N σ x := fun σ q x => by
    have := hsm σ (algebraMap ℚ K q) x
    rw [eq_ratCast, map_ratCast, Complex.norm_ratCast] at this
    exact this

  set C : ℝ := (finrank ℚ K : ℝ) ^ 3 * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A with hC
  have hEle : ∀ σ p, N σ (E p) ≤ C := fun σ p => by
    rw [hE p, ← algebraMap_smul K (ω p.1) (p.2 : V), hsm]
    have h1 := hA _ (hts p.2.2) σ
    exact mul_le_mul (hωb σ p.1) h1 (h0 _ _) ((norm_nonneg _).trans (hωb σ p.1))

  let red : V → V := fun x => ∑ p, Int.fract (E.repr x p) • E p
  have hred_sub : ∀ x, x - red x ∈ Submodule.span ℤ (Set.range E) := fun x => by
    have hx : x - red x = ∑ p, (⌊E.repr x p⌋ : ℤ) • E p := by
      rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
      conv_lhs => rw [← E.sum_repr x]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.floor_add_fract]
    rw [hx]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have hred_le : ∀ σ x, N σ (red x) ≤ ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C := fun σ x => by
    refine (hsum σ _ _).trans ?_
    have hle : ∀ p ∈ (Finset.univ : Finset (Fin (finrank ℚ K) × t)),
        N σ (Int.fract (E.repr x p) • E p) ≤ C := fun p _ => by
      rw [hq]
      have h1 : |((Int.fract (E.repr x p) : ℚ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (Rat.cast_nonneg.2 (Int.fract_nonneg _))]
        exact_mod_cast (Int.fract_lt_one _).le
      exact (mul_le_of_le_one_left (h0 _ _) h1).trans (hEle σ p)
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hm]
    push_cast; ring

  haveI : NoZeroSMulDivisors ℤ V := ⟨fun {c x} h => by
    rw [← Int.cast_smul_eq_zsmul K] at h
    exact (smul_eq_zero.1 h).imp_left Int.cast_eq_zero.1⟩
  let Lz := L.restrictScalars ℤ
  haveI : Module.Finite ℤ Lz := Module.Finite.iff_fg.2 hLfg.restrictScalars
  haveI : Module.Free ℤ Lz := Module.free_of_finite_type_torsion_free'
  let ZB := Module.Free.chooseBasis ℤ Lz
  let bZ : Module.Free.ChooseBasisIndex ℤ Lz → V := fun j => (ZB j : V)
  have hZq : LinearIndependent ℚ bZ := (LinearIndependent.iff_fractionRing ℤ ℚ).1
    (ZB.linearIndependent.map' Lz.subtype (Submodule.ker_subtype _))
  haveI : Module.Finite ℚ V := Module.Finite.of_basis E
  have hcardZ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Lz) ≤ Fintype.card (Fin (finrank ℚ K) × t) := by
    rw [← finrank_eq_card_basis E]; exact hZq.fintype_card_le_finrank
  have hLz : Lz = Submodule.span ℤ (Set.range bZ) := by
    rw [show Set.range bZ = Lz.subtype '' Set.range ZB from Set.range_comp _ _, ← Submodule.map_span,
      ZB.span_eq, Submodule.map_top, Submodule.range_subtype]

  let F : (Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz → V := Sum.elim E (fun j => red (bZ j))
  let e := Fintype.equivFin ((Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz)
  have hEL : ∀ p, E p ∈ L := fun p => by rw [hE]; exact L.smul_mem _ (hsL (hts p.2.2))
  have hspanE : Submodule.span ℤ (Set.range E) ≤ Lz :=
    Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hEL p)
  have hrng : Set.range (F ∘ e.symm) = Set.range F := e.symm.surjective.range_comp F
  have hbig : ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C ≤ max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [hC]; ring
  refine ⟨Fintype.card _, F ∘ e.symm, max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A),
    ⟨fun x => ?_, fun i σ => ?_, le_max_left _ _⟩, le_rfl, ?_⟩
  · rw [hrng]
    constructor
    · intro hx
      have hx' : x ∈ Lz := hx
      rw [hLz] at hx'
      refine (Submodule.span_le.2 ?_) hx'
      rintro _ ⟨j, rfl⟩
      have h1 : red (bZ j) ∈ Submodule.span ℤ (Set.range F) := Submodule.subset_span ⟨Sum.inr j, rfl⟩
      have h2 : bZ j - red (bZ j) ∈ Submodule.span ℤ (Set.range F) :=
        Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨Sum.inl p, rfl⟩) (hred_sub _)
      simpa using add_mem h2 h1
    · intro hx
      have : x ∈ Lz := (Submodule.span_le (p := Lz)).2 (by
        rintro _ ⟨q | j, rfl⟩
        · exact hEL q
        · have h1 : bZ j ∈ Lz := (ZB j).2
          have h2 := hspanE (hred_sub (bZ j))
          have e1 : red (bZ j) = bZ j - (bZ j - red (bZ j)) := by abel
          show red (bZ j) ∈ Lz
          rw [e1]; exact sub_mem h1 h2) hx
      exact this
  · refine le_trans ?_ hbig
    rw [Function.comp_apply]
    generalize e.symm i = q
    rcases q with q | j
    · have hC0 : 0 ≤ C := (h0 σ _).trans (hEle σ q)
      have hpos : 0 < Fintype.card t := Fintype.card_pos_iff.2 ⟨q.2⟩
      have h1 : (1 : ℝ) ≤ (finrank ℚ K : ℝ) * Formalism.HN.rkK L := by
        rw [← hm]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Module.finrank_pos.ne' hpos.ne')
      exact (hEle σ q).trans (le_mul_of_one_le_left hC0 h1)
    · exact hred_le σ _
  · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hm]
    rw [Fintype.card_prod, Fintype.card_fin, hm] at hcardZ
    linarith

end GlobalTheory
