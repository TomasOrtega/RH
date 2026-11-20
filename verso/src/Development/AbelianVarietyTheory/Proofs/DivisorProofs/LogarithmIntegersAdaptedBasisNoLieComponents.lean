import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstEqAddOfCob1EqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapSumSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZero
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.RedO

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv G d c k e0 lb hB hA hL h hh hcob a ha`. Establish `hF : IsFrame p C (RingHom.id O)` using `GlobalTheory.FrameIntegers.isFrame_integers p C v O hv`. Establish `hμ : ∀ i, constantCoeff (up C c.μ i) = 0` using `fun i => by`. Simplify using `[up, constantCoeff_map, c.isLaw.const i]`. Establish `lie0 : ∀ f : MvPowerSeries (Fin d) C, cob1 (up C c.μ) f = 0 → c.IsLie f 0`.

Introduce `f hf`. Establish `hd : ∀ n : ℕ, defect c.μ (p ^ n) f = defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) C)` using `fun n => by`. Rewrite using `[defect, GlobalTheory.LieZero.subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hf, sub_self, defect, ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, smul_zero, sub_zero]`. Establish `e : c.IsLie f 0 ↔ c.IsLie (0 : MvPowerSeries (Fin d) C) 0`. Unfold `Chart.IsLie`.

Simplify using `only [hd]`. Conclude with `e.2 (c.isLie_zero hv.hom_inj)`. Establish `hcobE : ∀ i, cob1 (up C c.μ) (e0 (Sum.inl i)) = 0` using `fun i => by`. Use extensionality with `α`. Take `⟨b, hb, hb'⟩` from `(hA i).1 α`.

Rewrite `hb` using `[RingHom.mem_ker, RingHom.id_apply]`. Rewrite using `[hb', hb, map_zero, map_zero]`. Set `L : Fin d ⊕ Fin k → G.dual.Lie` to `Sum.elim (fun _ => 0) lb`. Establish `hLe : ∀ x, c.IsLie (e0 x) (L x)`. Introduce and unpack `(i | j)`.

Conclude with `lie0 _ (hcobE i)`. Conclude with `hL j`. Set `e' : Unit ⊕ (Fin d ⊕ Fin k) → MvPowerSeries (Fin d) C` to `Sum.elim (fun _ => h) e0`. Set `b' : Unit ⊕ (Fin d ⊕ Fin k) → O` to `Sum.elim (fun _ => 1) (-a)`. Establish `hcomb : comb b' e' = h - comb a e0`.

Simplify using `only [comb, Fintype.sum_sum_type, e', b', Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, map_neg, neg_smul, Finset.sum_neg_distrib, map_one, one_smul, Finset.univ_unique, Finset.sum_singleton]`. Normalize the expressions using the abelian group laws. Establish `hQL : ∀ x, QL c.μ ⊤ (e' x)`. Introduce and unpack `(_ | x)`. Conclude with `hh`.

Conclude with `hB.1 x`. Establish `hLie' : ∀ x, c.IsLie (e' x) (Sum.elim (fun _ => (0 : G.dual.Lie)) L x)`. Introduce and unpack `(_ | x)`. Conclude with `lie0 h hcob`. Conclude with `hLe x`.

Establish `hs` using `GlobalTheory.QLog.Chart.isLie_comb p O C hF G d c _ e' _ b' hQL hLie'`. Rewrite `hs` using `[hcomb]`. Establish `hc0 : constantCoeff (h - comb a e0) = 0`. Rewrite using `[map_sub, hh.1, comb, map_sum]`. Simplify using `[← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, (hB.1 _).1]`.

Establish `hl0` using `(GlobalTheory.LieZero.lie_eq_zero p O C hF G d c _ _ hs).1 ha hc0`. Simplify using `only [Fintype.sum_sum_type, b', Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero, zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero, L] at hl0`. Establish `hinr : ∀ j, a (Sum.inr j) = 0` using `Fintype.linearIndependent_iff.1 lb.linearIndependent (fun j => a (Sum.inr j)) hl0`. Use `⟨hinr, fun i => ?_⟩` and prove the remaining obligations. Establish `hcobc : cob1 (up C c.μ) (h - comb a e0) = 0`.

Establish `hadd : ∀ f g, cob1 (up C c.μ) (f + g) = cob1 (up C c.μ) f + cob1 (up C c.μ) g` using `formalCoboundary_add hμ`. Set `Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C` to `AddMonoidHom.mk' (cob1 (up C c.μ)) hadd`. Establish `e1 : cob1 (up C c.μ) (comb a e0) = 0`. Express the relevant statement in the definitionally equal form `Φ (comb a e0) = 0`. Rewrite using `[comb, map_sum]`.

Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cob1 (up C c.μ) (algebraMap O C (a x) • e0 x) = 0`. Rewrite using `[formalCoboundary_smul hμ]`. Break down `x with i' | j` into its components or cases. Rewrite using `[hcobE i', smul_zero]`.

Rewrite using `[hinr j, map_zero, zero_smul]`. Rewrite using `[sub_eq_add_neg, ← neg_one_smul C (comb a e0), hadd, formalCoboundary_smul hμ, e1, smul_zero, hcob, add_zero]`. Take `⟨s, hs'⟩` from `In.top_iff.1 ha`. Establish `hs0 : s = 0` using `GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c C hF s (by rw [hs']; exact hcobc)`. Rewrite `hs'` using `[hs0, map_zero]`.

Establish `hEq : h = comb a e0` using `sub_eq_zero.1 hs'.symm`. Rewrite using `[hEq]`. Simplify using `only [lin, comb, Fintype.sum_sum_type, map_add, map_sum, coeff_smul, smul_eq_mul]`. Establish `h2 : ∀ j, algebraMap O C (a (Sum.inr j)) * coeff (Finsupp.single i 1) (e0 (Sum.inr j)) = 0` using `fun j => by rw [hinr j, map_zero, zero_mul]`. Establish `h1 : ∀ i', coeff (Finsupp.single i 1) (e0 (Sum.inl i')) = (Pi.single i' (1 : C) : Fin d → C) i` using `fun i' => congrFun (hA i').2 i`.

Simplify using `only [h2, h1, Finset.sum_const_zero, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c k e0 lb hB hA hL h hh hcob a ha
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμ : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, c.isLaw.const i]

  have lie0 : ∀ f : MvPowerSeries (Fin d) C, cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
    intro f hf
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) f = defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) C) := fun n => by
      rw [defect, GlobalTheory.LieZero.subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hf, sub_self, defect,
        ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, smul_zero, sub_zero]
    have e : c.IsLie f 0 ↔ c.IsLie (0 : MvPowerSeries (Fin d) C) 0 := by
      unfold Chart.IsLie
      simp only [hd]
    exact e.2 (c.isLie_zero hv.hom_inj)

  have hcobE : ∀ i, cob1 (up C c.μ) (e0 (Sum.inl i)) = 0 := fun i => by
    ext α
    obtain ⟨b, hb, hb'⟩ := (hA i).1 α
    rw [RingHom.mem_ker, RingHom.id_apply] at hb
    rw [hb', hb, map_zero, map_zero]
  let L : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) lb
  have hLe : ∀ x, c.IsLie (e0 x) (L x) := by
    rintro (i | j)
    · exact lie0 _ (hcobE i)
    · exact hL j

  let e' : Unit ⊕ (Fin d ⊕ Fin k) → MvPowerSeries (Fin d) C := Sum.elim (fun _ => h) e0
  let b' : Unit ⊕ (Fin d ⊕ Fin k) → O := Sum.elim (fun _ => 1) (-a)
  have hcomb : comb b' e' = h - comb a e0 := by
    simp only [comb, Fintype.sum_sum_type, e', b', Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      map_neg, neg_smul, Finset.sum_neg_distrib, map_one, one_smul, Finset.univ_unique,
      Finset.sum_singleton]
    abel
  have hQL : ∀ x, QL c.μ ⊤ (e' x) := by
    rintro (_ | x)
    · exact hh
    · exact hB.1 x
  have hLie' : ∀ x, c.IsLie (e' x) (Sum.elim (fun _ => (0 : G.dual.Lie)) L x) := by
    rintro (_ | x)
    · exact lie0 h hcob
    · exact hLe x
  have hs := GlobalTheory.QLog.Chart.isLie_comb p O C hF G d c _ e' _ b' hQL hLie'
  rw [hcomb] at hs
  have hc0 : constantCoeff (h - comb a e0) = 0 := by
    rw [map_sub, hh.1, comb, map_sum]
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_smul,
      coeff_zero_eq_constantCoeff_apply, (hB.1 _).1]
  have hl0 := (GlobalTheory.LieZero.lie_eq_zero p O C hF G d c _ _ hs).1 ha hc0
  simp only [Fintype.sum_sum_type, b', Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero,
    zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero, L] at hl0
  have hinr : ∀ j, a (Sum.inr j) = 0 :=
    Fintype.linearIndependent_iff.1 lb.linearIndependent (fun j => a (Sum.inr j)) hl0
  refine ⟨hinr, fun i => ?_⟩

  have hcobc : cob1 (up C c.μ) (h - comb a e0) = 0 := by
    have hadd : ∀ f g, cob1 (up C c.μ) (f + g) = cob1 (up C c.μ) f + cob1 (up C c.μ) g :=
      formalCoboundary_add hμ
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) hadd
    have e1 : cob1 (up C c.μ) (comb a e0) = 0 := by
      change Φ (comb a e0) = 0
      rw [comb, map_sum]
      refine Finset.sum_eq_zero fun x _ => ?_
      change cob1 (up C c.μ) (algebraMap O C (a x) • e0 x) = 0
      rw [formalCoboundary_smul hμ]
      rcases x with i' | j
      · rw [hcobE i', smul_zero]
      · rw [hinr j, map_zero, zero_smul]
    rw [sub_eq_add_neg, ← neg_one_smul C (comb a e0), hadd, formalCoboundary_smul hμ, e1, smul_zero, hcob,
      add_zero]
  obtain ⟨s, hs'⟩ := In.top_iff.1 ha
  have hs0 : s = 0 :=
    GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c C hF s (by rw [hs']; exact hcobc)
  rw [hs0, map_zero] at hs'
  have hEq : h = comb a e0 := sub_eq_zero.1 hs'.symm
  rw [hEq]
  simp only [lin, comb, Fintype.sum_sum_type, map_add, map_sum, coeff_smul, smul_eq_mul]
  have h2 : ∀ j, algebraMap O C (a (Sum.inr j)) * coeff (Finsupp.single i 1) (e0 (Sum.inr j)) = 0 :=
    fun j => by rw [hinr j, map_zero, zero_mul]
  have h1 : ∀ i', coeff (Finsupp.single i 1) (e0 (Sum.inl i')) = (Pi.single i' (1 : C) : Fin d → C) i :=
    fun i' => congrFun (hA i').2 i
  simp only [h2, h1, Finset.sum_const_zero, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.QLog.RedO
