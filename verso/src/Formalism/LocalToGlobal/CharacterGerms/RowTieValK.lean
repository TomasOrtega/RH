import Formalism.LocalToGlobal.CharacterGerms.LinearCoeffExponentialEqIte

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

/- English proof (translation)
Use `first`. Consider the case `(have key : ∀ g : PS C 1 dd, MvPowerSeries.coeff (Finsupp.single t 1) g = MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C t g) := by`. Introduce `g`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]`. Simplify using the standard rewrite rules.

Rewrite using `[key, key, key, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]`. Use the proof step `ring)`. Consider the case `(rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]`. Simplify using `[Finset.Nat.antidiagonal_succ]`. Use the proof step `ring)`.
-/
private theorem coeff_single_one_mul' (t : Fin 1 × Fin dd) (x y : PS C 1 dd) :
    MvPowerSeries.coeff (Finsupp.single t 1) (x * y) =
      MvPowerSeries.coeff (Finsupp.single t 1) x * MvPowerSeries.constantCoeff y +
        MvPowerSeries.constantCoeff x * MvPowerSeries.coeff (Finsupp.single t 1) y := by
  first
  | (have key : ∀ g : PS C 1 dd, MvPowerSeries.coeff (Finsupp.single t 1) g =
        MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C t g) := by
      intro g
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
      simp
     rw [key, key, key, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
     ring)
  | (rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
     simp [Finset.Nat.antidiagonal_succ]
     ring)

/- English proof (translation)
Rewrite using `[pow_succ, coeff_single_one_mul']`. Simplify using `[hx]`.
-/
private theorem coeff_single_one_pow_add_two_eq_zero (x : PS C 1 dd) (hx : MvPowerSeries.constantCoeff x = 0)
    (t : Fin 1 × Fin dd) (k : ℕ) : MvPowerSeries.coeff (Finsupp.single t 1) (x ^ (k + 1 + 1)) = 0 := by
  rw [pow_succ, coeff_single_one_mul']
  simp [hx]

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction`. Use `next =>`. Simplify using `[MvPowerSeries.coeff_one]`. Use `next s b f hs hb ih =>`. Establish `hfs : f s = 0`.

Assume the negation of the conclusion as `h'`. Conclude with `hs (Finsupp.mem_support_iff.mpr h')`. Establish `hne : Finsupp.single s b + f ≠ 0`. Introduce `h`. Apply `hb` to reduce the goal to its premises.

Establish `h2` using `congrArg (fun g : Fin 1 × Fin dd →₀ ℕ => g s) h`. Simplify `h2` using `[hfs]`. Establish `hP : (Finsupp.single s b + f).prod (fun s n => a s ^ n) = a s ^ b * f.prod (fun s n => a s ^ n)`. Rewrite using `[Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`. Use `congr 1`.

Conclude with `Finsupp.prod_single_index (pow_zero _)`. Rewrite using `[hP]`. Establish `hcs : MvPowerSeries.constantCoeff (a s ^ b) = 0`. Rewrite using `[map_pow, hac s, zero_pow hb]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[map_mul, hcs, zero_mul, if_neg hne]`. Introduce `hnot`. Rewrite using `[coeff_single_one_mul', hcs, zero_mul, add_zero]`. Distinguish the cases in `hf : f = 0`. Substitute `hf` using the available equality.

Establish `hb1 : b ≠ 1`. Introduce `h1`. Conclude with `hnot s (by rw [h1, add_zero])`. Take `⟨k, rfl⟩ : ∃ k, b = k + 1 + 1` from `⟨b - 2, by omega⟩`. Rewrite using `[coeff_single_one_pow_add_two_eq_zero (a s) (hac s) t k, zero_mul]`.

Rewrite using `[ih.1, if_neg hf, mul_zero]`.
-/
private theorem constantCoeff_and_linear_coeff_finsupp_prod_pow (a : Fin 1 × Fin dd → PS C 1 dd) (hac : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (t : Fin 1 × Fin dd) (d : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.constantCoeff (d.prod fun s n => a s ^ n) = (if d = 0 then 1 else 0) ∧
      ((∀ s, d ≠ Finsupp.single s 1) →
        MvPowerSeries.coeff (Finsupp.single t 1) (d.prod fun s n => a s ^ n) = 0) := by
  induction d using Finsupp.induction
  next =>
    simp [MvPowerSeries.coeff_one]
  next s b f hs hb ih =>
    have hfs : f s = 0 := by
      by_contra h'
      exact hs (Finsupp.mem_support_iff.mpr h')
    have hne : Finsupp.single s b + f ≠ 0 := by
      intro h
      apply hb
      have h2 := congrArg (fun g : Fin 1 × Fin dd →₀ ℕ => g s) h
      simpa [hfs] using h2
    have hP : (Finsupp.single s b + f).prod (fun s n => a s ^ n) =
        a s ^ b * f.prod (fun s n => a s ^ n) := by
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      congr 1
      exact Finsupp.prod_single_index (pow_zero _)
    rw [hP]
    have hcs : MvPowerSeries.constantCoeff (a s ^ b) = 0 := by
      rw [map_pow, hac s, zero_pow hb]
    constructor
    · rw [map_mul, hcs, zero_mul, if_neg hne]
    · intro hnot
      rw [coeff_single_one_mul', hcs, zero_mul, add_zero]
      by_cases hf : f = 0
      · subst hf
        have hb1 : b ≠ 1 := by
          intro h1
          exact hnot s (by rw [h1, add_zero])
        obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 + 1 := ⟨b - 2, by omega⟩
        rw [coeff_single_one_pow_add_two_eq_zero (a s) (hac s) t k, zero_mul]
      · rw [ih.1, if_neg hf, mul_zero]

/- English proof (translation)
Establish `hev : ev ![ψ] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => ψ p.2) f`. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `⟨i, k⟩`. Rewrite using `[Fin.fin_one_eq_zero i]`.

Both sides reduce to the same expression. Establish `hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => ψ p.2)` using `by first`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun s => hψ s.2)`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => hψ s.2)`. Consider the case `exact ⟨fun s => by simp [hψ s.2], fun d => Set.toFinite _⟩`.

Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by simp [hψ s.2])`. Rewrite using `[hev, MvPowerSeries.coeff_subst hs]`. Use `(finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun s => Finsupp.single s 1) ?_).trans ?_` and prove the remaining obligations. Introduce `d hd`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hd` to reduce the goal to its premises. Apply the tactic sequence `try dsimp only`. Rewrite using `[(constantCoeff_and_linear_coeff_finsupp_prod_pow _ (fun s => hψ s.2) _ d).2 (fun s h => hne s h.symm), smul_zero]`.

Use `first`. Consider the case `rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]`. Consider the case `rw [Finset.sum_image ((Finsupp.single_left_injective one_ne_zero).injOn)]`. Rewrite using `[Fintype.sum_prod_type, Fin.sum_univ_one]`. Simplify using `[Finsupp.prod_single_index, smul_eq_mul]`.
-/
private theorem coeff_single_one_ev_eq_sum (f : PS C 1 dd) (ψ : Pt C 1 dd) (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (j : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![ψ] f) =
      ∑ k, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), k) 1) f *
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ψ k) := by
  have hev : ev ![ψ] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => ψ p.2) f := by
    unfold ev
    congr 1
    funext ⟨i, k⟩
    rw [Fin.fin_one_eq_zero i]
    rfl
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => ψ p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun s => hψ s.2)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => hψ s.2)
    | exact ⟨fun s => by simp [hψ s.2], fun d => Set.toFinite _⟩
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by simp [hψ s.2])
  rw [hev, MvPowerSeries.coeff_subst hs]
  refine (finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun s => Finsupp.single s 1) ?_).trans ?_
  · intro d hd
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hne
    push_neg at hne
    apply hd
    try dsimp only
    rw [(constantCoeff_and_linear_coeff_finsupp_prod_pow _ (fun s => hψ s.2) _ d).2 (fun s h => hne s h.symm), smul_zero]
  · first
    | rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    | rw [Finset.sum_image ((Finsupp.single_left_injective one_ne_zero).injOn)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
    simp [Finsupp.prod_single_index, smul_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [linAct, comp1, coeff_single_one_ev_eq_sum _ ψ hψ, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem linAct_comp1 (φ ψ : Pt C 1 dd) (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) (x : Fin dd → C) :
    linAct (comp1 φ ψ) x = linAct φ (linAct ψ x) := by
  funext i
  simp only [linAct, comp1, coeff_single_one_ev_eq_sum _ ψ hψ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [linAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem linAct_smul (φ : Pt C 1 dd) (c : C) (x : Fin dd → C) : linAct φ (c • x) = c • linAct φ x := by
  funext i
  simp only [linAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [linAct, Finset.sum_apply, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem linAct_sum {ι : Type} (φ : Pt C 1 dd) (s : Finset ι) (x : ι → Fin dd → C) :
    linAct φ (∑ c ∈ s, x c) = ∑ c ∈ s, linAct φ (x c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
