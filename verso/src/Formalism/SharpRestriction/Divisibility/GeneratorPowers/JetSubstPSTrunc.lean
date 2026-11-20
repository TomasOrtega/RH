import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ScaleGenIsGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

section Jet

variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/- English proof (translation)
Use `show MvPolynomial.aeval (fun _ => (0 : S)) P = _`. Simplify using `[MvPolynomial.aeval_zero']`.
-/
private theorem jetAug_mk_lemma (P : MvPolynomial κ S) :
    (jetAug : Jet S κ 0 →ₐ[S] S) (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) P) =
      MvPolynomial.constantCoeff P := by
  show MvPolynomial.aeval (fun _ => (0 : S)) P = _
  simp [MvPolynomial.aeval_zero']

/- English proof (translation)
Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective (I := orig S κ ^ (0 + 1)) x`. Rewrite using `[jetAug_mk_lemma]`. Use `show (Ideal.Quotient.mk (orig S κ ^ (0 + 1))) P = Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff P))`. Rewrite using `[Ideal.Quotient.eq]`. Establish `h` using `sub_const_mem_orig P`.

Simplify using `using h`.
-/
private theorem jet0_eq_lemma (x : Jet S κ 0) :
    x = algebraMap S (Jet S κ 0) ((jetAug : Jet S κ 0 →ₐ[S] S) x) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (0 + 1)) x
  rw [jetAug_mk_lemma]
  show (Ideal.Quotient.mk (orig S κ ^ (0 + 1))) P =
    Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff P))
  rw [Ideal.Quotient.eq]
  have h := sub_const_mem_orig P
  simpa using h

/- English proof (translation)
Use `AlgHom.ext fun x => ?_` and prove the remaining obligations. Establish `hx` using `jet0_eq_lemma x`. Rewrite using `[AlgHom.comp_apply, hx]`. Simplify using `only [AlgHom.commutes]`.
-/
theorem aug_comp_eq (f : Jet S κ 0 →ₐ[S] Jet S κ' 0) :
    (jetAug : Jet S κ' 0 →ₐ[S] S).comp f = jetAug := by
  refine AlgHom.ext fun x => ?_
  have hx := jet0_eq_lemma x
  rw [AlgHom.comp_apply, hx]
  simp only [AlgHom.commutes]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `only [degLE, Finset.mem_filter] at h`. Conclude with `h.2`. Introduce `h`.

Establish `hb : ∀ i, e i < n + 1`. Introduce `i`. Break down `Nat.eq_zero_or_pos (e i) with h0 | hpos` into its components or cases. Use linear arithmetic over natural numbers and integers. Establish `hi : i ∈ e.support` using `Finsupp.mem_support_iff.2 (by omega)`.

Establish `h1` using `Finset.single_le_sum (f := (⇑e)) (fun _ _ => Nat.zero_le _) hi`. Establish `h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j` using `rfl`. Use linear arithmetic over natural numbers and integers. Simplify using `only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]`. Use `⟨⟨fun i => ⟨e i, hb i⟩, ?_⟩, h⟩` and prove the remaining obligations.

Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
private theorem mem_degLE_lemma (n : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE n ↔ (e.sum fun _ k => k) ≤ n := by
  constructor
  · intro h
    simp only [degLE, Finset.mem_filter] at h
    exact h.2
  · intro h
    have hb : ∀ i, e i < n + 1 := by
      intro i
      rcases Nat.eq_zero_or_pos (e i) with h0 | hpos
      · omega
      · have hi : i ∈ e.support := Finsupp.mem_support_iff.2 (by omega)
        have h1 := Finset.single_le_sum (f := (⇑e)) (fun _ _ => Nat.zero_le _) hi
        have h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j := rfl
        omega
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨fun i => ⟨e i, hb i⟩, ?_⟩, h⟩
    ext i
    simp

/- English proof (translation)
Establish `hX : ∀ i, (MvPolynomial.X i : MvPolynomial κ S) ∈ orig S κ` using `fun i => Ideal.subset_span ⟨i, rfl⟩`. Establish `h1 : (e.prod fun i k => (MvPolynomial.X i : MvPolynomial κ S) ^ k) ∈ orig S κ ^ (e.sum fun _ k => k)`. Establish `h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j` using `rfl`. Rewrite using `[h2, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _`.

Rewrite using `[MvPolynomial.monomial_eq]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right h h1)`.
-/
private theorem monomial_mem_orig_pow_lemma (n : ℕ) (e : κ →₀ ℕ) (c : S)
    (h : n ≤ e.sum fun _ k => k) : MvPolynomial.monomial e c ∈ orig S κ ^ n := by
  have hX : ∀ i, (MvPolynomial.X i : MvPolynomial κ S) ∈ orig S κ :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 : (e.prod fun i k => (MvPolynomial.X i : MvPolynomial κ S) ^ k) ∈
      orig S κ ^ (e.sum fun _ k => k) := by
    have h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j := rfl
    rw [h2, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _
  rw [MvPolynomial.monomial_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right h h1)

/- English proof (translation)
Establish `hsub : (degLE n : Finset (κ →₀ ℕ)) = (degLE (n + 1)).filter (fun e => (e.sum fun _ k => k) ≤ n)`. Use extensionality with `e`. Simplify using `only [Finset.mem_filter, mem_degLE_lemma]`. Conclude with `⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩`. Unfold `psTrunc`.

Rewrite using `[hsub, ← Finset.sum_filter_add_sum_filter_not (degLE (n + 1)) (fun e => (e.sum fun _ k => k) ≤ n), add_sub_cancel_left]`. Use `Ideal.sum_mem _ fun e he => ?_` and prove the remaining obligations. Rewrite `he` using `[Finset.mem_filter, mem_degLE_lemma]`. Establish `he2` using `he.2`. Conclude with `monomial_mem_orig_pow_lemma _ _ _ (by omega)`.
-/
private theorem psTrunc_succ_sub_lemma (n : ℕ) (f : MvPowerSeries κ S) :
    psTrunc (n + 1) f - psTrunc n f ∈ orig S κ ^ (n + 1) := by
  have hsub : (degLE n : Finset (κ →₀ ℕ)) = (degLE (n + 1)).filter (fun e => (e.sum fun _ k => k) ≤ n) := by
    ext e
    simp only [Finset.mem_filter, mem_degLE_lemma]
    exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
  unfold psTrunc
  rw [hsub, ← Finset.sum_filter_add_sum_filter_not (degLE (n + 1))
    (fun e => (e.sum fun _ k => k) ≤ n), add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  rw [Finset.mem_filter, mem_degLE_lemma] at he
  have he2 := he.2
  exact monomial_mem_orig_pow_lemma _ _ _ (by omega)

/- English proof (translation)
Unfold `psTrunc`. Rewrite using `[map_sum]`. Simplify using `only [MvPolynomial.constantCoeff_monomial]`. Rewrite using `[Finset.sum_ite_eq', if_pos ((mem_degLE_lemma n 0).2 (by simp))]`. Both sides reduce to the same expression.
-/
private theorem cc_psTrunc_lemma (n : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.constantCoeff (psTrunc n f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq', if_pos ((mem_degLE_lemma n 0).2 (by simp))]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem jetTrunc_mk_lemma (n : ℕ) (P : MvPolynomial κ S) :
    (jetTrunc : Jet S κ (n + 1) →ₐ[S] Jet S κ n) (Ideal.Quotient.mk (orig S κ ^ (n + 1 + 1)) P) =
      Ideal.Quotient.mk (orig S κ ^ (n + 1)) P := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem jetSubstPS_mk_lemma (n : ℕ) (g : κ → MvPowerSeries κ' S) (P : MvPolynomial κ S) :
    (jetSubstPS (m := n) g) (Ideal.Quotient.mk (orig S κ ^ (n + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (n + 1))
        (MvPolynomial.aeval (fun i => psTrunc n (g i) -
          MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc n (g i)))) P) := rfl

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Simplify using `only [jetTrunc_mk_lemma, jetSubstPS_mk_lemma, MvPolynomial.aeval_X]`.

Rewrite using `[Ideal.Quotient.eq, cc_psTrunc_lemma, cc_psTrunc_lemma, sub_sub_sub_cancel_right]`. Conclude with `psTrunc_succ_sub_lemma m (g i)`.
-/
theorem jetSubstPS_trunc (m : ℕ) (g : κ → MvPowerSeries κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstPS (m := m + 1) g) =
      (jetSubstPS (m := m) g).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  simp only [jetTrunc_mk_lemma, jetSubstPS_mk_lemma, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq, cc_psTrunc_lemma, cc_psTrunc_lemma, sub_sub_sub_cancel_right]
  exact psTrunc_succ_sub_lemma m (g i)

/- English proof (translation)
Use `show (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) (Ideal.Quotient.mk (orig S κ ^ (m + 1 + 1)) (psTrunc (m + 1) f)) = Ideal.Quotient.mk (orig S κ ^ (m + 1)) (psTrunc m f)`. Rewrite using `[jetTrunc_mk_lemma, Ideal.Quotient.eq]`. Conclude with `psTrunc_succ_sub_lemma m f`.
-/
theorem jetTrunc_psJet (m : ℕ) (f : MvPowerSeries κ S) :
    (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) (psJet (m + 1) f) = psJet m f := by
  show (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m)
      (Ideal.Quotient.mk (orig S κ ^ (m + 1 + 1)) (psTrunc (m + 1) f)) =
    Ideal.Quotient.mk (orig S κ ^ (m + 1)) (psTrunc m f)
  rw [jetTrunc_mk_lemma, Ideal.Quotient.eq]
  exact psTrunc_succ_sub_lemma m f

/- English proof (translation)
Establish `h1` using `sub_const_mem_orig P`. Simplify `h1` using `[h]`.
-/
theorem mem_orig_of_cc' (P : MvPolynomial κ S) (h : MvPolynomial.constantCoeff P = 0) : P ∈ orig S κ := by
  have h1 := sub_const_mem_orig P
  simpa [h] using h1

/- English proof (translation)
Conclude with `cc_psTrunc_lemma m f`.
-/
theorem cc_psTrunc' (m : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  exact cc_psTrunc_lemma m f

/- English proof (translation)
Use `show Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (psTrunc 0 f) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (orig S κ ^ (0 + 1))), Ideal.Quotient.eq]`. Establish `h : psTrunc 0 f - 1 ∈ orig S κ`. Apply `mem_orig_of_cc'` to reduce the goal to its premises. Rewrite using `[map_sub, map_one, cc_psTrunc', hf, sub_self]`.

Simplify using `using h`.
-/
theorem psJet_zero_of (f : MvPowerSeries κ S) (hf : MvPowerSeries.constantCoeff f = 1) : psJet 0 f = 1 := by
  show Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (psTrunc 0 f) = 1
  rw [← map_one (Ideal.Quotient.mk (orig S κ ^ (0 + 1))), Ideal.Quotient.eq]
  have h : psTrunc 0 f - 1 ∈ orig S κ := by
    apply mem_orig_of_cc'
    rw [map_sub, map_one, cc_psTrunc', hf, sub_self]
  simpa using h

end Jet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d' => φ p.2)` using `by first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hφ p.2)`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => hφ p.2)`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hφ p.2]; exact IsNilpotent.zero)`. Unfold `compL`.

Rewrite using `[MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, d i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hd (Finsupp.ext hcon)`. Establish `h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (φ s.2) ^ e) = 0`. Rewrite using `[Finsupp.prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hi) (by rw [map_pow, hφ, zero_pow hi])`.

Simplify using `only [h0, smul_zero]`.
-/
theorem const_compL {d' : ℕ} (φ : Fin d' → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d') S) :
    MvPowerSeries.constantCoeff (compL φ g) = MvPowerSeries.constantCoeff g := by
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d' => φ p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => hφ p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hφ p.2]; exact IsNilpotent.zero)
  unfold compL
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (φ s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hi) (by rw [map_pow, hφ, zero_pow hi])
    simp only [h0, smul_zero]

/- English proof (translation)
Establish `hg' : MvPowerSeries.constantCoeff (-g) = 0` using `by rw [map_neg, hg, neg_zero]`. Establish `ha : PowerSeries.HasSubst (-g)` using `by first`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero hg'`. Consider the case `exact PowerSeries.hasSubst_of_constantCoeff_zero hg'`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero' hg'`.

Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hg']; exact IsNilpotent.zero)`. Use `show MvPowerSeries.constantCoeff (PowerSeries.subst (-g) (PowerSeries.exp S)) = 1`. Rewrite using `[PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]`. Simplify using `[PowerSeries.coeff_exp]`. Introduce `d hd`.

Simplify using `[map_pow, map_neg, hg, zero_pow hd]`.
-/
theorem const_expS_neg {d' : ℕ} (g : MvPowerSeries (Fin 1 × Fin d') S)
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (Germ.FB.expS S (-g)) = 1 := by
  have hg' : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg, neg_zero]
  have ha : PowerSeries.HasSubst (-g) := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero hg'
      | exact PowerSeries.hasSubst_of_constantCoeff_zero hg'
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hg'
      | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hg']; exact IsNilpotent.zero)
  show MvPowerSeries.constantCoeff (PowerSeries.subst (-g) (PowerSeries.exp S)) = 1
  rw [PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    simp [map_pow, map_neg, hg, zero_pow hd]

/- English proof (translation)
Establish `hL` using `Xo.univ.t.PP.isLB`. Establish `hu0 : u 0 = 1` using `Units.ext ((hu 0).trans (psJet_zero_of _ (const_expS_neg _ (by rw [const_compL φ hφ]; exact ExpGA.const_hL C))))`. Establish `hmor : ((homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left ≫ (homAt y.x (jφ φ 0)).left) = (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left`. Rewrite using `[← Over.comp_left, homAt_comp, aug_comp_eq]`. Use `corr_of_val hL fun z J hJ => ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu0, show unitΓ (1 : (Jet S (Fin 1 × Fin (dL Dw)) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one, _root_.one_mul]`. Conclude with `val_pull hJ _ _ _`. Use `_ = val (eL y C.d C.x C.B.A.act C.e C.wP 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left) z J := by`. Rewrite using `[val_corr hJ (hτc 0), Category.id_comp, Category.id_comp, hmor]`.

Use `_ = val (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) (𝟙 _) z J := (val_pull hJ _ _ _).symm.trans (val_corr hJ C.rig0 _)`.
-/
theorem rig_eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u 0)
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := by
  have hL := Xo.univ.t.PP.isLB
  have hu0 : u 0 = 1 := Units.ext ((hu 0).trans (psJet_zero_of _ (const_expS_neg _
    (by rw [const_compL φ hφ]; exact ExpGA.const_hL C))))
  have hmor : ((homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left ≫
      (homAt y.x (jφ φ 0)).left) = (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left := by
    rw [← Over.comp_left, homAt_comp, aug_comp_eq]
  refine corr_of_val hL fun z J hJ => ?_
  calc val (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) (𝟙 _) z J
      = val (ExpGA.eG C φ τ u 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z J :=
        val_pull hJ _ _ _
    _ = gm (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z ⊤ (unitΓ (u 0)) *
          val (LB.pullGen Xo.univ.t.PP.L _ _ (τ 0) (homAt y.x (jφ φ 0)).left)
            (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z J :=
        GermB.val_scale Xo.univ.t _ _ _ _ _ z J hJ
    _ = val (τ 0) ((𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) ≫
          (homAt y.x (jφ φ 0)).left) z J := by
        rw [hu0, show unitΓ (1 : (Jet S (Fin 1 × Fin (dL Dw)) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
          _root_.one_mul]
        exact val_pull hJ _ _ _
    _ = val (eL y C.d C.x C.B.A.act C.e C.wP 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
          z J := by
        rw [val_corr hJ (hτc 0), Category.id_comp, Category.id_comp, hmor]
    _ = val (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) (𝟙 _) z J :=
        (val_pull hJ _ _ _).symm.trans (val_corr hJ C.rig0 _)

/- English proof (translation)
Establish `hL` using `Xo.univ.t.PP.isLB`. Establish `hch` using `(isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart`. Establish `hT : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP (m + 1)) (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left) (eL y C.d C.x C.B.A.act C.e C.wP m)` using `corr_of_val hL fun z J hJ => by`. Rewrite using `[val_pull hJ, Category.id_comp]`. Conclude with `GermD.val_eL_trunc hch C.e C.wP htr m z J hJ`.

Establish `hmor : (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left ≫ (homAt y.x (jφ φ (m + 1))).left = (homAt y.x (jφ φ m)).left ≫ (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp]`. Unfold `jφ`. Rewrite using `[jetSubstPS_trunc]`. Establish `hUm : Units.map (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m).toMonoidHom (u (m + 1)) = u m` using `Units.ext ((congrArg _ (hu (m + 1))).trans ((jetTrunc_psJet m _).trans (hu m).symm))`.

Establish `hAB : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left) (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left) (LB.pullGen Xo.univ.t.PP.L _ …` using `corr_of_val hL fun z J hJ => by`. Rewrite using `[val_pull hJ, val_pull hJ, val_corr hJ (hτc (m + 1)), Category.id_comp]`. Rewrite using `[hmor, ← val_pull hJ, val_corr hJ hT, val_pull hJ, Category.id_comp, val_corr hJ (hτc m)]`. Establish `e1 : LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1)) (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left = scaleGenG Xo.univ.t _ _ (unitΓ (u m)) (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (h …`. Unfold `ExpGA.eG`.

Use `erw [FBIdLB.pullGen_scaleGenG, FBIdLB.unitΓ_homAt, hUm]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `FBIdLB.corr_scaleGenG Xo.univ.t hAB _`.
-/
theorem trunc_eG (C : ChartAt Xo c y) (htr : FrTruncC y C) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
      (ExpGA.eG C φ τ u m) := by
  have hL := Xo.univ.t.PP.isLB
  have hch := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  have hT : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left)
      (eL y C.d C.x C.B.A.act C.e C.wP m) := corr_of_val hL fun z J hJ => by
    rw [val_pull hJ, Category.id_comp]
    exact GermD.val_eL_trunc hch C.e C.wP htr m z J hJ
  have hmor : (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left ≫
      (homAt y.x (jφ φ (m + 1))).left = (homAt y.x (jφ φ m)).left ≫
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp]
    unfold jφ
    rw [jetSubstPS_trunc]
  have hUm : Units.map (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m).toMonoidHom
      (u (m + 1)) = u m :=
    Units.ext ((congrArg _ (hu (m + 1))).trans ((jetTrunc_psJet m _).trans (hu m).symm))
  have hAB : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left)
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
      (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left) := corr_of_val hL fun z J hJ => by
    rw [val_pull hJ, val_pull hJ, val_corr hJ (hτc (m + 1)), Category.id_comp]
    rw [hmor, ← val_pull hJ, val_corr hJ hT, val_pull hJ, Category.id_comp, val_corr hJ (hτc m)]
  have e1 : LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left =
      scaleGenG Xo.univ.t _ _ (unitΓ (u m))
        (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left)
          (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left) := by
    unfold ExpGA.eG
    erw [FBIdLB.pullGen_scaleGenG, FBIdLB.unitΓ_homAt, hUm]
    rfl
  rw [e1]
  exact FBIdLB.corr_scaleGenG Xo.univ.t hAB _

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
