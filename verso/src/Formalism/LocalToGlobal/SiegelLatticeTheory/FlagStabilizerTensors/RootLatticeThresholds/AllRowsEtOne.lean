import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKpp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt

noncomputable section

open MonoidAlgebra MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsEtOne

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.AllRowsTr
  Formalism.L2.SG.Pf.AllRowsEtAlg Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsWt

variable {D : D7} {X : HidaSetting D}

instance instFactG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

abbrev eJv (kv : Σ k : Fin 2, D.nd.PlG k) (ψ : AddChar (ZMod (D.host.g kv.1)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  eJ (D.host.g kv.1) D.R.r D.R.k (D.R.m / 2 - 1) ψ

/- English proof (translation)
Rewrite using `[Complex.inv_eq_conj (AddChar.norm_apply ψ x)]`. Both sides reduce to the same expression.
-/
theorem star_psi {g : ℕ} [NeZero g] (ψ : AddChar (ZMod g) ℂ) (x : ZMod g) : star (ψ x) = (ψ x)⁻¹ := by
  rw [Complex.inv_eq_conj (AddChar.norm_apply ψ x)]
  rfl

open Classical in
/- English proof (translation)
Unfold `cJ`. Rewrite using `[Nat.card_eq_fintype_card, ← Fintype.card_subtype]`. Use `congr 1`. Use `Fintype.card_congr (Equiv.subtypeEquivRight fun u => ?_)` and prove the remaining obligations. Conclude with `jPred_iff _ _ (r_eq D) _`.
-/
theorem card_PJ (D : D7) (k : Fin 2) :
    ((Finset.univ.filter fun u : GL (Fin D.R.r) (ZMod (D.host.g k)) =>
      PJ D.R.k (D.R.m / 2 - 1) (u : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))).card : ℂ) =
      (cJ D (D.host.g k) : ℂ) := by
  unfold cJ
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  congr 1
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  exact jPred_iff _ _ (r_eq D) _

/- English proof (translation)
Establish `: X.B.μf.IsHaarMeasure` using `X.B.haar`. Establish `hopen : IsOpen ((Formalism.L2.SG.Pf.AllRowsKpp.KgSub X : Set X.B.I.Gf))` using `X.B.I.topf_open X.B.g (g_pos X)`. Establish `hc` using `levelSubgroup_relIndex_eq hS`. Establish `hpos2 : (Formalism.L2.SG.Pf.AllRowsKpp.KgSub X).relIndex (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X) ≠ 0`. Rewrite using `[hc]`.

Conclude with `Nat.pos_iff_ne_zero.1 (Nat.mul_pos (pow_pos (cJ_pos D 0) _) (pow_pos (cJ_pos D 1) _))`. Establish `hμ2` using `PI.MassDataKppVolLemmas.Glob_measure_eq_relIndex_mul X.B.μf (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X) (Formalism.L2.SG.Pf.AllRowsKpp.KgSub X) (Formalism.L2.SG.Pf.AllRowsKpp.le2 X) hopen hpos2`. Unfold `HidaSetting.volK2`. Establish `e : X.B.μf X.K2 = X.B.μf (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X : Set X.B.I.Gf)` using `rfl`. Rewrite using `[e, hμ2, ENNReal.toReal_mul, ENNReal.toReal_natCast, hc]`.

Both sides reduce to the same expression.
-/
theorem levelVolume_eq_index (hS : Function.Surjective (rhoX X)) :
    X.volK2 = ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℝ) * V X := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hopen : IsOpen ((Formalism.L2.SG.Pf.AllRowsKpp.KgSub X : Set X.B.I.Gf)) := X.B.I.topf_open X.B.g (g_pos X)
  have hc := levelSubgroup_relIndex_eq hS
  have hpos2 : (Formalism.L2.SG.Pf.AllRowsKpp.KgSub X).relIndex (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X) ≠ 0 := by
    rw [hc]; exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos (pow_pos (cJ_pos D 0) _) (pow_pos (cJ_pos D 1) _))
  have hμ2 := PI.MassDataKppVolLemmas.Glob_measure_eq_relIndex_mul X.B.μf (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X) (Formalism.L2.SG.Pf.AllRowsKpp.KgSub X) (Formalism.L2.SG.Pf.AllRowsKpp.le2 X) hopen hpos2
  unfold HidaSetting.volK2
  have e : X.B.μf X.K2 = X.B.μf (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X : Set X.B.I.Gf) := rfl
  rw [e, hμ2, ENNReal.toReal_mul, ENNReal.toReal_natCast, hc]
  rfl

variable (hS : Function.Surjective (rhoX X))

/- English proof (translation)
Establish `hx : rhoX X (sec hS γ) = γ` using `rho_sec hS γ`. Unfold `hat`. Rewrite using `[X.e_eq]`. Simplify using `only [eJ_coeff]`. Distinguish the cases in `hJ : ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P γ kv)`.

Establish `hxK : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ X.K2` using `(hmem _).2 (by rw [hx]; exact hJ)`. Establish `hxK' : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw` using `hxK`. Establish `hJ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), PJ D.R.k (D.R.m / 2 - 1) (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))` using `hJ`. Rewrite using `[if_pos hxK', Finset.prod_congr rfl (fun kv _ => if_pos (hJ' kv))]`. Establish `hc` using `hchi _ hxK`.

Rewrite `hc` using `[hx]`. Establish `hv : (X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal = ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℝ) * V X` using `levelVolume_eq_index hS`. Use `show (V X : ℂ) * (star (X.chi2 (sec hS γ)) / ((X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal : ℂ)) = _`. Rewrite using `[hc, hv, star_prod]`. Simplify using `only [star_psi, card_PJ]`.

Rewrite using `[Finset.prod_div_distrib]`. Establish `hprod : ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (cJ D (D.host.g kv.1) : ℂ) = ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℂ)`. Rewrite using `[← prod_sigma_const (fun k => cJ D (D.host.g k))]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[hprod]`. Establish `hV` using `V_ne X`. Establish `hJ0 : ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℂ) ≠ 0`. Conclude with `(Nat.mul_pos (pow_pos (cJ_pos D 0) _) (pow_pos (cJ_pos D 1) _)).ne'` after adjusting the coercions. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `hxK : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∉ X.K2` using `fun h => hJ (by rw [← hx]; exact (hmem _).1 h) push Not at hJ`. Take `⟨kv, hkv⟩` from `hJ`. Establish `hxK' : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw` using `hxK`. Rewrite using `[if_neg hxK', mul_zero]`.

Use `symm`. Establish `hkv' : ¬ PJ D.R.k (D.R.m / 2 - 1) (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))` using `hkv`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ kv) (if_neg hkv')`.
-/
theorem hat_e_eq (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)))
    (γ : G0g D.nd) :
    hat hS X.B.e γ = ∏ kv, (eJv kv (ψ kv)).coeff ((P kv)⁻¹ * γ kv * P kv) := by
  classical
  have hx : rhoX X (sec hS γ) = γ := rho_sec hS γ
  unfold hat
  rw [X.e_eq]
  simp only [eJ_coeff]
  by_cases hJ : ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P γ kv)
  · have hxK : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ X.K2 := (hmem _).2 (by rw [hx]; exact hJ)
    have hxK' : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hxK
    have hJ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), PJ D.R.k (D.R.m / 2 - 1)
        (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := hJ
    rw [if_pos hxK', Finset.prod_congr rfl (fun kv _ => if_pos (hJ' kv))]
    have hc := hchi _ hxK
    rw [hx] at hc
    have hv : (X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal =
        ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℝ) * V X := levelVolume_eq_index hS
    show (V X : ℂ) * (star (X.chi2 (sec hS γ)) / ((X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal : ℂ)) = _
    rw [hc, hv, star_prod]
    simp only [star_psi, card_PJ]
    rw [Finset.prod_div_distrib]
    have hprod : ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (cJ D (D.host.g kv.1) : ℂ) =
        ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℂ) := by
      rw [← prod_sigma_const (fun k => cJ D (D.host.g k))]; push_cast; rfl
    rw [hprod]
    have hV := V_ne X
    have hJ0 : ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (pow_pos (cJ_pos D 0) _) (pow_pos (cJ_pos D 1) _)).ne'
    push_cast
    field_simp
  · have hxK : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∉ X.K2 := fun h => hJ (by rw [← hx]; exact (hmem _).1 h)
    push Not at hJ
    obtain ⟨kv, hkv⟩ := hJ
    have hxK' : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hxK
    rw [if_neg hxK', mul_zero]
    symm
    have hkv' : ¬ PJ D.R.k (D.R.m / 2 - 1)
        (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := hkv
    exact Finset.prod_eq_zero (Finset.mem_univ kv) (if_neg hkv')

/- English proof (translation)
Simplify using `[MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply, mul_assoc]`.
-/
theorem conjP_coeff {G : Type} [Group G] (P γ : G) (a : MonoidAlgebra ℂ G) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1).coeff γ = a.coeff (P⁻¹ * γ * P) := by
  simp [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply, mul_assoc]

/- English proof (translation)
Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `γ`. Rewrite using `[Ehat_coeff, pA_coeff, hat_e_eq hS P ψ hmem hchi γ]`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[conjP_coeff]`.
-/
theorem Ehat_eq (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))) :
    Ehat hS = pA (fun kv => MonoidAlgebra.single (P kv) 1 * eJv kv (ψ kv) * MonoidAlgebra.single (P kv)⁻¹ 1) := by
  classical
  apply MonoidAlgebra.ext; ext γ
  rw [Ehat_coeff, pA_coeff, hat_e_eq hS P ψ hmem hchi γ]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [conjP_coeff]

/- English proof (translation)
Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `γ`. Rewrite using `[Ea_coeff, pA_coeff]`.
-/
theorem Ea_pA (a : CV D) : Ea a = pA (fun kv => D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) := by
  classical
  apply MonoidAlgebra.ext; ext γ
  rw [Ea_coeff, pA_coeff]

/- English proof (translation)
Rewrite using `[mul_assoc (MonoidAlgebra.single P 1 * a), ← hc, ← mul_assoc, mul_assoc (MonoidAlgebra.single P 1) a e, conjP_coeff]`. Simplify using the standard rewrite rules.
-/
theorem tau_conjP {G : Type} [Group G] [Fintype G] (P : G) (a e : MonoidAlgebra ℂ G) (hc : ∀ y, e * y = y * e) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1 * e).coeff 1 = (a * e).coeff 1 := by
  rw [mul_assoc (MonoidAlgebra.single P 1 * a), ← hc, ← mul_assoc, mul_assoc (MonoidAlgebra.single P 1) a e,
    conjP_coeff]
  simp

section Val

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

def Nc (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) : ℂ := (eJk D k (ψ₀ k) * D.ntypes.eSer k f).coeff 1

def Zc (k : Fin 2) : ℂ := (eJk D k (ψ₀ k)).coeff 1

open Classical in
include hS in
/- English proof (translation)
Rewrite using `[ES_eq, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']`. Use `Finset.sum_congr (by congr 1) fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Ehat_eq hS P ψ hmem hchi, Ea_pA, pA_mul, pA_one_coeff]`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[tau_conjP _ _ _ (D.ntypes.eSer_central kv.1 _)]`.

Conclude with `(wt_indep (ψ₀ kv.1) (ψ kv) (hψ₀ kv.1) (hψ kv) _ (D.ntypes.eSer_central kv.1 _)).1`.
-/
theorem val_eT_sum (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hψ : ∀ kv, ψ kv ≠ 1) (hψ₀ : ∀ k, ψ₀ k ≠ 1)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)))
    (S : Set (Tup2 D)) :
    (Ehat hS * ES S).coeff 1 =
      ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S),
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) := by
  classical
  rw [ES_eq, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr (by congr 1) fun a _ => ?_
  rw [Ehat_eq hS P ψ hmem hchi, Ea_pA, pA_mul, pA_one_coeff]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [tau_conjP _ _ _ (D.ntypes.eSer_central kv.1 _)]
  exact (wt_indep (ψ₀ kv.1) (ψ kv) (hψ₀ kv.1) (hψ kv) _ (D.ntypes.eSer_central kv.1 _)).1

include hS in
/- English proof (translation)
Rewrite using `[Ehat_eq hS P ψ hmem hchi, pA_one_coeff]`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[conjP_coeff, mul_one, inv_mul_cancel]`. Conclude with `(wt_indep (ψ₀ kv.1) (ψ kv) (hψ₀ kv.1) (hψ kv) 1 (fun y => by rw [one_mul, mul_one])).2`.
-/
theorem val_e (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hψ : ∀ kv, ψ kv ≠ 1) (hψ₀ : ∀ k, ψ₀ k ≠ 1)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))) :
    (Ehat hS).coeff 1 = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Zc ψ₀ kv.1 := by
  classical
  rw [Ehat_eq hS P ψ hmem hchi, pA_one_coeff]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [conjP_coeff, mul_one, inv_mul_cancel]
  exact (wt_indep (ψ₀ kv.1) (ψ kv) (hψ₀ kv.1) (hψ kv) 1 (fun y => by rw [one_mul, mul_one])).2

end Val

section Fact

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

/- English proof (translation)
Distinguish the cases in `hf : f.Monic ∧ f.natDegree = D.R.r`. Establish `hc0` using `Formalism.L2.SG.Pf.RowDictPf.monicOf_coeff hf.1 hf.2`. Rewrite using `[Finset.sum_eq_single (fun i : Fin D.R.r => f.coeff i)]`. Rewrite using `[if_pos hc0, hc0]`. Introduce `c _ hc`.

Rewrite using `[if_neg]`. Introduce `h`. Apply `hc` to reduce the goal to its premises. Conclude with `monicOf_inj (h.trans hc0.symm)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_eq_zero fun c _ => if_neg fun (h : Formalism.CyclotomicNorms.monicOf c = f) => hf (h ▸ Formalism.L2.SG.Pf.RowDictPf.monicOf_monic c)]`. Unfold `Nc`. Rewrite using `[D.ntypes.eSer_zero k f (fun h => hf ⟨h.1, h.2.1⟩), mul_zero]`. Both sides reduce to the same expression.
-/
theorem sum_N_single (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), (if Formalism.CyclotomicNorms.monicOf c = f then Nc ψ₀ k (Formalism.CyclotomicNorms.monicOf c) else 0) =
      Nc ψ₀ k f := by
  classical
  by_cases hf : f.Monic ∧ f.natDegree = D.R.r
  · have hc0 := Formalism.L2.SG.Pf.RowDictPf.monicOf_coeff hf.1 hf.2
    rw [Finset.sum_eq_single (fun i : Fin D.R.r => f.coeff i)]
    · rw [if_pos hc0, hc0]
    · intro c _ hc
      rw [if_neg]
      intro h
      apply hc
      exact monicOf_inj (h.trans hc0.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero fun c _ => if_neg fun (h : Formalism.CyclotomicNorms.monicOf c = f) => hf (h ▸ Formalism.L2.SG.Pf.RowDictPf.monicOf_monic c)]
    unfold Nc
    rw [D.ntypes.eSer_zero k f (fun h => hf ⟨h.1, h.2.1⟩), mul_zero]
    rfl

/- English proof (translation)
Unfold `Nc Zc`. Use `congrArg (fun y => (eJk D k (ψ₀ k) * y).coeff 1) (sum_eSer' (D := D) k)` as an intermediate fact. Simplify using `only [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply', mul_one] at this`. Conclude with `this`.
-/
theorem sum_N_all (k : Fin 2) : ∑ c : Fin D.R.r → ZMod (D.host.g k), Nc ψ₀ k (Formalism.CyclotomicNorms.monicOf c) = Zc ψ₀ k := by
  unfold Nc Zc
  have := congrArg (fun y => (eJk D k (ψ₀ k) * y).coeff 1) (sum_eSer' (D := D) k)
  simp only [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply', mul_one] at this
  exact this

end Fact

section Cyl

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

open Classical in

/- English proof (translation)
Rewrite using `[Finset.sum_filter]`. Establish `h1 : ∀ a : CV D, (if tupOf a ∈ cyl D k (S : Set (Tup D k)) then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0) = ∑ t ∈ S, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv) …`. Introduce `a`. Rewrite using `[Finset.sum_ite_eq]`. Conclude with `if_congr (Iff.rfl) rfl rfl`.

Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use `set G : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun kv c => if kv.1 = k then (if Formalism.CyclotomicNorms.monicOf c = Function.update (0 : Tup2 D) k t kv.1 kv.2 then Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf c) else 0) else Nc ψ₀ kv.1 (For …`. Establish `h2 : ∀ a : CV D, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0) = ∏ kv, G kv (a kv)`.

Introduce `a`. Establish `hG' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), G kv (a kv) = if (kv.1 = k → Formalism.CyclotomicNorms.monicOf (a kv) = Function.update (0 : Tup2 D) k t kv.1 kv.2) then Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0`. Introduce `kv`. Distinguish the cases in `hk : kv.1 = k`. Simplify using `only [hG, hk, if_true, true_implies]`.

Simplify using `only [hG, hk, if_false, false_implies, if_true]`. Rewrite using `[Finset.prod_congr rfl fun kv _ => hG' kv, Finset.prod_ite_zero]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Introduce `h kv _ hk`. Take `⟨k', v⟩` from `kv`. Simplify using `only at hk`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self, ← h]`.

Both sides reduce to the same expression. Introduce `h`. Use function extensionality and compare the values at `v`. Use `h ⟨k, v⟩ (Finset.mem_univ _) rfl` as an intermediate fact. Rewrite `this` using `[Function.update_self]`.

Conclude with `this`. Repeatedly rewrite using `[h2]`. Rewrite using `[← Fintype.prod_sum]`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : kv.1 = k`.

Rewrite using `[if_pos hk]`. Simplify using `only [hG, hk, if_true]`. Conclude with `sum_N_single ψ₀ kv.1 _`. Rewrite using `[if_neg hk]`. Simplify using `only [hG, hk, if_false]`.

Conclude with `sum_N_all ψ₀ kv.1`.
-/
theorem sum_cyl (k : Fin 2) (S : Finset (Tup D k)) :
    ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ cyl D k (S : Set (Tup D k))),
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) =
      ∑ t ∈ S, ∏ kv : (Σ k : Fin 2, D.nd.PlG k),
        (if kv.1 = k then Nc ψ₀ kv.1 (Function.update (0 : Tup2 D) k t kv.1 kv.2) else Zc ψ₀ kv.1) := by
  rw [Finset.sum_filter]
  have h1 : ∀ a : CV D, (if tupOf a ∈ cyl D k (S : Set (Tup D k)) then
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0) =
      ∑ t ∈ S, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0) := by
    intro a
    rw [Finset.sum_ite_eq]
    exact if_congr (Iff.rfl) rfl rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  set G : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun kv c =>
    if kv.1 = k then (if Formalism.CyclotomicNorms.monicOf c = Function.update (0 : Tup2 D) k t kv.1 kv.2 then
      Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf c) else 0) else Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf c) with hG
  have h2 : ∀ a : CV D, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))
      else 0) = ∏ kv, G kv (a kv) := by
    intro a
    have hG' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), G kv (a kv) =
        if (kv.1 = k → Formalism.CyclotomicNorms.monicOf (a kv) = Function.update (0 : Tup2 D) k t kv.1 kv.2) then
          Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0 := by
      intro kv
      by_cases hk : kv.1 = k
      · simp only [hG, hk, if_true, true_implies]
      · simp only [hG, hk, if_false, false_implies, if_true]
    rw [Finset.prod_congr rfl fun kv _ => hG' kv, Finset.prod_ite_zero]
    congr 1
    apply propext
    constructor
    · intro h kv _ hk
      obtain ⟨k', v⟩ := kv
      simp only at hk
      subst hk
      rw [Function.update_self, ← h]
      rfl
    · intro h
      funext v
      have := h ⟨k, v⟩ (Finset.mem_univ _) rfl
      rw [Function.update_self] at this
      exact this
  simp_rw [h2]
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  by_cases hk : kv.1 = k
  · rw [if_pos hk]
    simp only [hG, hk, if_true]
    exact sum_N_single ψ₀ kv.1 _
  · rw [if_neg hk]
    simp only [hG, hk, if_false]
    exact sum_N_all ψ₀ kv.1

end Cyl

section Final

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

/- English proof (translation)
Establish `hc` using `D.ntypes.eSer_central k f`. Establish `hs` using `selfadj_of_central_idem _ (D.ntypes.eSer_idem k f) hc`. Establish `h` using `tau_eJ (kk := D.R.k) (s := D.R.m / 2 - 1) (ψ₀ k) _ (D.ntypes.eSer_idem k f) hc hs`. Establish `hre : Nc ψ₀ k f = ((∑ h, Complex.normSq ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) (ψ₀ k) * D.ntypes.eSer k f).coeff h) : ℝ) : ℂ)` using `h`. Rewrite using `[hre, Complex.ofReal_re]`.
-/
theorem Nc_real (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) : Nc ψ₀ k f = ((Nc ψ₀ k f).re : ℂ) := by
  have hc := D.ntypes.eSer_central k f
  have hs := selfadj_of_central_idem _ (D.ntypes.eSer_idem k f) hc
  have h := tau_eJ (kk := D.R.k) (s := D.R.m / 2 - 1) (ψ₀ k) _ (D.ntypes.eSer_idem k f) hc hs
  have hre : Nc ψ₀ k f = ((∑ h, Complex.normSq ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) (ψ₀ k) *
      D.ntypes.eSer k f).coeff h) : ℝ) : ℂ) := h
  rw [hre, Complex.ofReal_re]

/- English proof (translation)
Simplify using `[phiJ, entN, Matrix.one_apply]`. Use `intros`. Use linear arithmetic over natural numbers and integers.
-/
theorem phiJ_one' {g N kk s : ℕ} : phiJ kk s (1 : Matrix (Fin N) (Fin N) (ZMod g)) = 0 := by
  simp [phiJ, entN, Matrix.one_apply]
  intros
  omega

/- English proof (translation)
Unfold `Zc`. Use `show (eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) (ψ₀ k)).coeff 1 = _`. Rewrite using `[eJ_coeff, if_pos (by rw [Units.val_one]; exact jPred_one _ _), card_PJ, Units.val_one, phiJ_one', AddChar.map_zero_eq_one, inv_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Zc_eq (k : Fin 2) : Zc ψ₀ k = (((cJ D (D.host.g k) : ℝ)⁻¹ : ℝ) : ℂ) := by
  classical
  unfold Zc
  show (eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) (ψ₀ k)).coeff 1 = _
  rw [eJ_coeff, if_pos (by rw [Units.val_one]; exact jPred_one _ _), card_PJ, Units.val_one, phiJ_one',
    AddChar.map_zero_eq_one, inv_one]
  push_cast
  ring

end Final

section Main

/- English proof (translation)
Rewrite using `[Fintype.prod_sigma, Fin.prod_univ_two]`.
-/
theorem split_prod (F : (Σ k : Fin 2, D.nd.PlG k) → ℂ) :
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), F kv = (∏ v : D.nd.PlG 0, F ⟨0, v⟩) * ∏ v : D.nd.PlG 1, F ⟨1, v⟩ := by
  rw [Fintype.prod_sigma, Fin.prod_univ_two]

include hS in

/- English proof (translation)
Take `⟨P, ψ, hψ, hK⟩` from `hK`. Establish `hmem` using `fun x => (hK x).1`. Establish `hchi` using `fun x => (hK x).2`. Introduce `k S`. Establish `h1 : eT X (cyl D k (S : Set (Tup D k))) 1 = (Ehat hS * ES (cyl D k (S : Set (Tup D k)))).coeff 1 / (V X : ℂ)`.

Use `val_hat hS (biInv_eT X (cyl D k (S : Set (Tup D k)))) (1 : KSub X.B.I)` as an intermediate fact. Rewrite `this` using `[map_one, hat_eT']`. Conclude with `this`. Establish `h2 : X.B.e 1 = (Ehat hS).coeff 1 / (V X : ℂ)`. Use `val_hat hS (biInv_e X) (1 : KSub X.B.I)` as an intermediate fact.

Rewrite `this` using `[map_one, ← Ehat_coeff]`. Conclude with `this`. Rewrite using `[h1, h2, val_eT_sum hS ψ₀ P ψ hψ hψ₀ hmem hchi, sum_cyl ψ₀ k S, val_e hS ψ₀ P ψ hψ hψ₀ hmem hchi]`. Establish `hZ : ∀ j : Fin 2, Zc ψ₀ j = (((cJ D (D.host.g j) : ℝ)⁻¹ : ℝ) : ℂ)` using `Zc_eq ψ₀`. Establish `hzpos : ∀ j : Fin 2, (0 : ℝ) < (cJ D (D.host.g j) : ℝ)⁻¹` using `fun j => by`.

Use `cJ_pos D j` as an intermediate fact. Check the signs of the components of the expression. Establish `hw : ∀ f, wtOf D k (eJk D k (ψ₀ k)) f = (Nc ψ₀ k f).re / (cJ D (D.host.g k) : ℝ)⁻¹`. Introduce `f`. Use `show (Nc ψ₀ k f).re / (Zc ψ₀ k).re = _`.

Rewrite using `[hZ, Complex.ofReal_re]`. Simplify using `only [hw]`. Establish `hV` using `V_pos X`. Establish `hVc : (V X : ℂ) ≠ 0` using `V_ne X`. Apply the tactic sequence `obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp`.

Simplify using `only [split_prod, if_true, if_neg (show (1 : Fin 2) ≠ 0 by decide), Function.update_self, Finset.prod_const, Finset.card_univ, D.nd.card_PlG, hZ]`. Establish `e1 : ∑ x ∈ S, (∏ v, Nc ψ₀ 0 (x v)) * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f = ((∑ x ∈ S, (∏ v, (Nc ψ₀ 0 (x v)).re) * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f : ℝ) : ℂ)`. Use `push_cast`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun v _ => Nc_real ψ₀ 0 _`. Rewrite using `[e1]`. Rewrite using `[show ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f / (V X : ℂ) = ((((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f / V X : ℝ) : ℂ) by push_cast; ring]`. Rewrite using `[← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]`. Simplify using `only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, D.nd.card_PlG]`.

Rewrite using `[← Finset.sum_div, ← Finset.sum_mul]`. Establish `h0` using `hzpos 0`. Establish `h1'` using `hzpos 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_div_assoc, div_self (pow_ne_zero _ (one_div_ne_zero (by exact_mod_cast (cJ_pos D 0).ne'))), mul_one]`.

Simplify using `only [split_prod, if_true, if_neg (show (0 : Fin 2) ≠ 1 by decide), Function.update_self, Finset.prod_const, Finset.card_univ, D.nd.card_PlG, hZ]`. Establish `e1 : ∑ x ∈ S, ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * (∏ v, Nc ψ₀ 1 (x v)) = ((∑ x ∈ S, ((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * (∏ v, (Nc ψ₀ 1 (x v)).re) : ℝ) : ℂ)`. Use `push_cast`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun v _ => Nc_real ψ₀ 1 _`. Rewrite using `[e1]`. Rewrite using `[show ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f / (V X : ℂ) = ((((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f / V X : ℝ) : ℂ) by push_cast; ring]`. Rewrite using `[← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]`. Simplify using `only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, D.nd.card_PlG]`.

Rewrite using `[← Finset.sum_div, ← Finset.mul_sum]`. Establish `h0` using `hzpos 0`. Establish `h1'` using `hzpos 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_div_assoc, div_self (pow_ne_zero _ (one_div_ne_zero (by exact_mod_cast (cJ_pos D 1).ne'))), mul_one]`.
-/
theorem etOne_of (hK : KppShape X) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) :
    EtOne X ψ₀ := by
  classical
  obtain ⟨P, ψ, hψ, hK⟩ := hK
  have hmem := fun x => (hK x).1
  have hchi := fun x => (hK x).2
  intro k S
  have h1 : eT X (cyl D k (S : Set (Tup D k))) 1 =
      (Ehat hS * ES (cyl D k (S : Set (Tup D k)))).coeff 1 / (V X : ℂ) := by
    have := val_hat hS (biInv_eT X (cyl D k (S : Set (Tup D k)))) (1 : KSub X.B.I)
    rw [map_one, hat_eT'] at this
    exact this
  have h2 : X.B.e 1 = (Ehat hS).coeff 1 / (V X : ℂ) := by
    have := val_hat hS (biInv_e X) (1 : KSub X.B.I)
    rw [map_one, ← Ehat_coeff] at this
    exact this
  rw [h1, h2, val_eT_sum hS ψ₀ P ψ hψ hψ₀ hmem hchi, sum_cyl ψ₀ k S, val_e hS ψ₀ P ψ hψ hψ₀ hmem hchi]
  have hZ : ∀ j : Fin 2, Zc ψ₀ j = (((cJ D (D.host.g j) : ℝ)⁻¹ : ℝ) : ℂ) := Zc_eq ψ₀
  have hzpos : ∀ j : Fin 2, (0 : ℝ) < (cJ D (D.host.g j) : ℝ)⁻¹ := fun j => by
    have := cJ_pos D j; positivity
  have hw : ∀ f, wtOf D k (eJk D k (ψ₀ k)) f = (Nc ψ₀ k f).re / (cJ D (D.host.g k) : ℝ)⁻¹ := by
    intro f
    show (Nc ψ₀ k f).re / (Zc ψ₀ k).re = _
    rw [hZ, Complex.ofReal_re]
  simp only [hw]
  have hV := V_pos X
  have hVc : (V X : ℂ) ≠ 0 := V_ne X
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  · simp only [split_prod, if_true, if_neg (show (1 : Fin 2) ≠ 0 by decide), Function.update_self,
      Finset.prod_const, Finset.card_univ, D.nd.card_PlG, hZ]
    have e1 : ∑ x ∈ S, (∏ v, Nc ψ₀ 0 (x v)) * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f =
        ((∑ x ∈ S, (∏ v, (Nc ψ₀ 0 (x v)).re) * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      exact Finset.prod_congr rfl fun v _ => Nc_real ψ₀ 0 _
    rw [e1]
    rw [show ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f / (V X : ℂ) =
      ((((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f / V X : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    have h0 := hzpos 0
    have h1' := hzpos 1
    field_simp
    rw [mul_div_assoc, div_self (pow_ne_zero _ (one_div_ne_zero (by exact_mod_cast (cJ_pos D 0).ne'))), mul_one]
  · simp only [split_prod, if_true, if_neg (show (0 : Fin 2) ≠ 1 by decide), Function.update_self,
      Finset.prod_const, Finset.card_univ, D.nd.card_PlG, hZ]
    have e1 : ∑ x ∈ S, ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * (∏ v, Nc ψ₀ 1 (x v)) =
        ((∑ x ∈ S, ((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * (∏ v, (Nc ψ₀ 1 (x v)).re) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      exact Finset.prod_congr rfl fun v _ => Nc_real ψ₀ 1 _
    rw [e1]
    rw [show ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f / (V X : ℂ) =
      ((((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f / V X : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have h0 := hzpos 0
    have h1' := hzpos 1
    field_simp
    rw [mul_div_assoc, div_self (pow_ne_zero _ (one_div_ne_zero (by exact_mod_cast (cJ_pos D 1).ne'))), mul_one]

end Main

end Formalism.L2.SG.Pf.AllRowsEtOne
