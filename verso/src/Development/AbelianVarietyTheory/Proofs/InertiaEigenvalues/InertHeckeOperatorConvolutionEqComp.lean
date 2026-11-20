import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalFormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmulStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open GlobalTheory.SatInd

namespace GlobalTheory.InertConvMul

/- English proof (translation)
Establish `hc` using `QuotientGroup.eq.1 hab`. Use `hH a ⟨a⁻¹ * b, hc⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `H (a * (a⁻¹ * b)) = H a at this`. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`.
-/
theorem eq_of_coset {G : Type} [Group G] {K : Subgroup G} {k : Type} {H : G → k}
    (hH : ∀ (a : G) (c : K), H (a * c) = H a) {a b : G} (hab : (a : G ⧸ K) = b) : H a = H b := by
  have hc := QuotientGroup.eq.1 hab
  have := hH a ⟨a⁻¹ * b, hc⟩
  change H (a * (a⁻¹ * b)) = H a at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

/- English proof (translation)
Rewrite using `[← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]`.
-/
theorem finsum_eq_of_support_subset_range {α β M : Type} [AddCommMonoid M] {F : α → M} {e : β → α}
    (he : Function.Injective e) (hs : Function.support F ⊆ Set.range e) :
    ∑ᶠ c, F c = ∑ᶠ d, F (e d) := by
  rw [← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `set K := KU Dv.σw n with hKdef`. Set `lam : GAf L n →* GU Dv.σw n` to `MonoidHom.codRestrict (GlobalTheory.SatInd.CosetFin.locHom Dv) _ hA`. Establish `hlam : ∀ x, ((lam x : GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc x` using `fun _ => rfl`. Establish `hK1 : ∀ u ∈ Umax L n, lam u ∈ K` using `hK`. Establish `hR : ∀ x x' : GAf L n, TrivOutside {v} x → TrivOutside {v} x' → ((x : GAf L n ⧸ U) = x' ↔ ((lam x : GU Dv.σw n ⧸ K) = lam x'))`.

Introduce `x x' hx hx'`. Establish `ht : TrivOutside {v} (x⁻¹ * x')` using `GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) hx'`. Rewrite using `[QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`.

Conclude with `hK1 _ ((hU _ ht).1 hu)`. Introduce `hk`. Conclude with `(hU _ ht).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j)`. Establish `hCs : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, TrivOutside {v} x ∧ lam x = d.out` using `fun d => by`. Take `⟨x, hx, e⟩` from `hC _ d.out.2`.

Conclude with `⟨x, hx, Subtype.ext e⟩`. Use `choose s hs1 hs2 using hCs`. Establish `heT : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, (x : GAf L n ⧸ U) = (s d : GAf L n ⧸ U) ∧ TrivOutside {v} x` using `fun d => ⟨s d, rfl, hs1 d⟩`. Establish `hρ1 : ∀ d, TrivOutside {v} (heT d).choose` using `fun d => (heT d).choose_spec.2`. Establish `hρ2 : ∀ d, ((lam (heT d).choose : GU Dv.σw n) : GU Dv.σw n ⧸ K) = d` using `fun d => by`.

Rewrite using `[(hR _ _ (hρ1 d) (hs1 d)).1 (heT d).choose_spec.1, hs2 d, QuotientGroup.out_eq']`. Establish `he : Function.Injective (fun d : GU Dv.σw n ⧸ K => ((s d : GAf L n) : GAf L n ⧸ U))`. Introduce `d d' hdd`. Use `(hR _ _ (hs1 d) (hs1 d')).1 hdd` as an intermediate fact. Rewrite `this` using `[hs2, hs2, QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis.

Establish `step2 : ∀ (H : GU Dv.σw n → ℂ), (∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a) → ∀ (F : GAf L n → W) (g : GAf L n), heckeFunI L n U Dv H F g = ∑ᶠ d : GU Dv.σw n ⧸ K, H d.out • F (g * (heT d).choose)`. Introduce `H hH F g`. Use `show (∑ᶠ c : GAf L n ⧸ U, _) = _`. Rewrite using `[finsum_eq_of_support_subset_range he]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations.

Rewrite using `[dif_pos (heT d)]`. Establish `hv : Dv.hval H (Dv.loc (heT d).choose) = H d.out`. Rewrite using `[InertDatum.hval, dif_pos (hA _)]`. Conclude with `eq_of_coset hH (by rw [QuotientGroup.out_eq']; exact hρ2 d)`. Rewrite using `[hv]`.

Introduce `c hc`. Rewrite `hc` using `[Function.mem_support]`. Distinguish the cases in `hT : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x`. Take `⟨x, hxc, hx⟩` from `hT`. Use `⟨(lam x : GU Dv.σw n ⧸ K), ?_⟩` and prove the remaining obligations.

Use `show ((s _ : GAf L n) : GAf L n ⧸ U) = c`. Rewrite using `[← hxc]`. Use `(hR _ _ (hs1 _) hx).2 ?_` and prove the remaining obligations. Rewrite using `[hs2, QuotientGroup.out_eq']`. Rewrite `hc` using `[dif_neg hT]`.

Conclude with `absurd rfl hc`. Establish `hRi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a` using `fun H hH a c => by simpa using hH.1 1 c a`. Establish `hLi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (c : K) (a : GU Dv.σw n), H (c * a) = H a` using `fun H hH c a => by simpa using hH.1 c 1 a`. Establish `hconvR : ∀ (a : GU Dv.σw n) (c : K), conv K h h' (a * c) = conv K h h' a`. Introduce `a c`.

Simplify using `only [Formalism.UG.conv]`. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hRi h' hh']`. Establish `hfin : ∀ H ∈ Hecke ℂ K, Set.Finite {d : GU Dv.σw n ⧸ K | H d.out ≠ 0}`. Introduce and unpack `H ⟨-, S, hS⟩`.

Use `(S.finite_toSet.biUnion fun t _ => GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram t).subset ?_` and prove the remaining obligations. Introduce `d hd`. Take `⟨t, ht, a, b, hab⟩` from `hS _ hd`. Use `Set.mem_biUnion ht ⟨(a : GU Dv.σw n), a.2, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← QuotientGroup.out_eq' d]`.

Rewrite using `[hab]`. Conclude with `(QuotientGroup.mk_mul_of_mem _ b.2).symm`. Establish `hfU : ∀ a b : GAf L n, (a : GAf L n ⧸ U) = b → ∀ g, f (g * a) = f (g * b)`. Introduce `a b hab g`. Establish `hu` using `QuotientGroup.eq.1 hab`.

Establish `: f (g * a * (a⁻¹ * b)) = f (g * a)` using `congrFun (hf _ hu) (g * a)`. Rewrite using `[← this, mul_assoc, mul_inv_cancel_left]`. Use function extensionality and compare the values at `g`. Rewrite using `[step2 _ hconvR f g, step2 h (hRi h hh) _ g]`. Establish `inner : ∀ d : GU Dv.σw n ⧸ K, heckeFunI L n U Dv h' f (g * (heT d).choose) = ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)`.

Introduce `d`. Rewrite using `[step2 h' (hRi h' hh') f]`. Use `set x := lam (heT d).choose with hx`. Establish `hk : x⁻¹ * d.out ∈ K` using `QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq']; exact hρ2 d)`. Establish `hL : ∀ y, h' (d.out⁻¹ * y) = h' (x⁻¹ * y)`.

Introduce `y`. Use `hLi h' hh' ⟨(x⁻¹ * d.out)⁻¹, inv_mem hk⟩ (x⁻¹ * y)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use `show _ = (x⁻¹ * d.out)⁻¹ * (x⁻¹ * y)`.

Use `group`. Use `Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (GU Dv.σw n ⧸ K)))` and prove the remaining obligations. Use `finsum_congr fun e => ?_` and prove the remaining obligations. Simplify using `only [MulAction.toPerm_apply]`. Use `congr 1`.

Rewrite using `[hL]`. Use `eq_of_coset (hRi h' hh') ?_` and prove the remaining obligations. Rewrite using `[QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq', inv_smul_smul]`. Rewrite using `[mul_assoc]`. Use `hfU _ _ ((hR _ _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul (hρ1 d) (hρ1 e)) (hρ1 _)).2 ?_) g` and prove the remaining obligations.

Rewrite using `[map_mul, hρ2, ← hx, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hρ2]`. Rewrite using `[finsum_congr fun d => congrArg (h d.out • ·) (inner d)]`. Establish `hSe : Set.Finite (⋃ (d : GU Dv.σw n ⧸ K) (_ : d ∈ {d : GU Dv.σw n ⧸ K | h d.out ≠ 0}), (fun c : GU Dv.σw n ⧸ K => (d.out • c : GU Dv.σw n ⧸ K)) '' {c : GU Dv.σw n ⧸ K | h' c.out ≠ 0})` using `(hfin h hh).biUnion fun d _ => (hfin h' hh').image _`. Establish `hmem : ∀ d e : GU Dv.σw n ⧸ K, h d.out ≠ 0 → h' (d.out⁻¹ * e.out) ≠ 0 → e ∈ hSe.toFinset`. Introduce `d e hd he'`.

Rewrite using `[Set.Finite.mem_toFinset]`. Use `Set.mem_biUnion hd ⟨d.out⁻¹ • e, ?_, smul_inv_smul d.out e⟩` and prove the remaining obligations. Establish `hc : (((d.out⁻¹ • e).out : GU Dv.σw n) : GU Dv.σw n ⧸ K) = ↑(d.out⁻¹ * e.out)`. Rewrite using `[QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']`. Use `show h' (d.out⁻¹ • e).out ≠ 0`.

Rewrite using `[eq_of_coset (hRi h' hh') hc]`. Conclude with `he'`. Establish `hL1 : (∑ᶠ e : GU Dv.σw n ⧸ K, conv K h h' e.out • f (g * (heT e).choose)) = ∑ e ∈ hSe.toFinset, (∑ d ∈ (hfin h hh).toFinset, h d.out * h' (d.out⁻¹ * e.out)) • f (g * (heT e).choose)`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use `show (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out)) = _`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `d hd`. Rewrite `hd` using `[Function.mem_support]`.

Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `left_ne_zero_of_mul hd`. Introduce `e he`. Rewrite `he` using `[Function.mem_support]`. Establish `h1 : conv K h h' e.out ≠ 0` using `fun h0 => he (by rw [h0, zero_smul])`.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `h1 (finsum_eq_zero_of_forall_eq_zero hcon)`. Conclude with `hmem d e (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)`.

Establish `hR1 : (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out • ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)) = ∑ d ∈ (hfin h hh).toFinset, ∑ e ∈ hSe.toFinset, (h d.out * h' (d.out⁻¹ * e.out)) • f (g * (heT e).choose)`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := (hfin h hh).toFinset) ?_]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite `hd` using `[Set.Finite.mem_toFinset]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun e _ => by rw [mul_smul]`. Introduce `e he`. Rewrite `he` using `[Function.mem_support]`. Conclude with `hmem d e hd (fun h0 => he (by rw [h0, zero_smul]))`. Introduce `d hd`.

Rewrite `hd` using `[Function.mem_support]`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `fun h0 => hd (by rw [h0, zero_smul])`. Rewrite using `[hL1, hR1, Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun e _ => by rw [Finset.sum_smul]`.
-/
theorem conv_of (Dv : InertDatum L n v w) (U : Subgroup (GAf L n))
    (hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n))
    (hA : ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n)
    (hK : ∀ u ∈ Umax L n, (⟨Dv.loc u, hA u⟩ : GU Dv.σw n) ∈ KU Dv.σw n)
    (hC : ∀ y ∈ GU Dv.σw n, ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y)
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (h : GU Dv.σw n → ℂ) (hh : h ∈ Hecke ℂ (KU Dv.σw n))
    (h' : GU Dv.σw n → ℂ) (hh' : h' ∈ Hecke ℂ (KU Dv.σw n))
    (f : GAf L n → W) (hf : ∀ κ ∈ U, NG.rt L n κ f = f) :
    heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f =
      heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  classical
  set K := KU Dv.σw n with hKdef
  let lam : GAf L n →* GU Dv.σw n := MonoidHom.codRestrict (GlobalTheory.SatInd.CosetFin.locHom Dv) _ hA
  have hlam : ∀ x, ((lam x : GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc x := fun _ => rfl
  have hK1 : ∀ u ∈ Umax L n, lam u ∈ K := hK
  have hR : ∀ x x' : GAf L n, TrivOutside {v} x → TrivOutside {v} x' →
      ((x : GAf L n ⧸ U) = x' ↔ ((lam x : GU Dv.σw n ⧸ K) = lam x')) := by
    intro x x' hx hx'
    have ht : TrivOutside {v} (x⁻¹ * x') :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) hx'
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
    constructor
    · intro hu; exact hK1 _ ((hU _ ht).1 hu)
    · intro hk
      exact (hU _ ht).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j)
  have hCs : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, TrivOutside {v} x ∧ lam x = d.out := fun d => by
    obtain ⟨x, hx, e⟩ := hC _ d.out.2
    exact ⟨x, hx, Subtype.ext e⟩
  choose s hs1 hs2 using hCs
  have heT : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, (x : GAf L n ⧸ U) = (s d : GAf L n ⧸ U) ∧
      TrivOutside {v} x := fun d => ⟨s d, rfl, hs1 d⟩
  have hρ1 : ∀ d, TrivOutside {v} (heT d).choose := fun d => (heT d).choose_spec.2
  have hρ2 : ∀ d, ((lam (heT d).choose : GU Dv.σw n) : GU Dv.σw n ⧸ K) = d := fun d => by
    rw [(hR _ _ (hρ1 d) (hs1 d)).1 (heT d).choose_spec.1, hs2 d, QuotientGroup.out_eq']
  have he : Function.Injective (fun d : GU Dv.σw n ⧸ K => ((s d : GAf L n) : GAf L n ⧸ U)) := by
    intro d d' hdd
    have := (hR _ _ (hs1 d) (hs1 d')).1 hdd
    rwa [hs2, hs2, QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

  have step2 : ∀ (H : GU Dv.σw n → ℂ), (∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a) →
      ∀ (F : GAf L n → W) (g : GAf L n),
      heckeFunI L n U Dv H F g = ∑ᶠ d : GU Dv.σw n ⧸ K, H d.out • F (g * (heT d).choose) := by
    intro H hH F g
    show (∑ᶠ c : GAf L n ⧸ U, _) = _
    rw [finsum_eq_of_support_subset_range he]
    · refine finsum_congr fun d => ?_
      rw [dif_pos (heT d)]
      have hv : Dv.hval H (Dv.loc (heT d).choose) = H d.out := by
        rw [InertDatum.hval, dif_pos (hA _)]
        exact eq_of_coset hH (by rw [QuotientGroup.out_eq']; exact hρ2 d)
      rw [hv]
    · intro c hc
      rw [Function.mem_support] at hc
      by_cases hT : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · obtain ⟨x, hxc, hx⟩ := hT
        refine ⟨(lam x : GU Dv.σw n ⧸ K), ?_⟩
        show ((s _ : GAf L n) : GAf L n ⧸ U) = c
        rw [← hxc]
        refine (hR _ _ (hs1 _) hx).2 ?_
        rw [hs2, QuotientGroup.out_eq']
      · rw [dif_neg hT] at hc
        exact absurd rfl hc

  have hRi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a :=
    fun H hH a c => by simpa using hH.1 1 c a
  have hLi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (c : K) (a : GU Dv.σw n), H (c * a) = H a :=
    fun H hH c a => by simpa using hH.1 c 1 a
  have hconvR : ∀ (a : GU Dv.σw n) (c : K), conv K h h' (a * c) = conv K h h' a := by
    intro a c
    simp only [Formalism.UG.conv]
    refine finsum_congr fun x => ?_
    rw [← mul_assoc, hRi h' hh']
  have hfin : ∀ H ∈ Hecke ℂ K, Set.Finite {d : GU Dv.σw n ⧸ K | H d.out ≠ 0} := by
    rintro H ⟨-, S, hS⟩
    refine (S.finite_toSet.biUnion fun t _ => GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram t).subset ?_
    intro d hd
    obtain ⟨t, ht, a, b, hab⟩ := hS _ hd
    refine Set.mem_biUnion ht ⟨(a : GU Dv.σw n), a.2, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' d]
    rw [hab]
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  have hfU : ∀ a b : GAf L n, (a : GAf L n ⧸ U) = b → ∀ g, f (g * a) = f (g * b) := by
    intro a b hab g
    have hu := QuotientGroup.eq.1 hab
    have : f (g * a * (a⁻¹ * b)) = f (g * a) := congrFun (hf _ hu) (g * a)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  funext g
  rw [step2 _ hconvR f g, step2 h (hRi h hh) _ g]
  have inner : ∀ d : GU Dv.σw n ⧸ K,
      heckeFunI L n U Dv h' f (g * (heT d).choose) =
        ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose) := by
    intro d
    rw [step2 h' (hRi h' hh') f]
    set x := lam (heT d).choose with hx
    have hk : x⁻¹ * d.out ∈ K := QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq']; exact hρ2 d)
    have hL : ∀ y, h' (d.out⁻¹ * y) = h' (x⁻¹ * y) := by
      intro y
      have := hLi h' hh' ⟨(x⁻¹ * d.out)⁻¹, inv_mem hk⟩ (x⁻¹ * y)
      rw [← this]
      congr 1
      show _ = (x⁻¹ * d.out)⁻¹ * (x⁻¹ * y)
      group
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (GU Dv.σw n ⧸ K)))
    refine finsum_congr fun e => ?_
    simp only [MulAction.toPerm_apply]
    congr 1
    · rw [hL]
      refine eq_of_coset (hRi h' hh') ?_
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq',
        inv_smul_smul]
    · rw [mul_assoc]
      refine hfU _ _ ((hR _ _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul (hρ1 d) (hρ1 e)) (hρ1 _)).2 ?_) g
      rw [map_mul, hρ2, ← hx, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hρ2]
  rw [finsum_congr fun d => congrArg (h d.out • ·) (inner d)]
  have hSe : Set.Finite (⋃ (d : GU Dv.σw n ⧸ K) (_ : d ∈ {d : GU Dv.σw n ⧸ K | h d.out ≠ 0}),
      (fun c : GU Dv.σw n ⧸ K => (d.out • c : GU Dv.σw n ⧸ K)) '' {c : GU Dv.σw n ⧸ K | h' c.out ≠ 0}) :=
    (hfin h hh).biUnion fun d _ => (hfin h' hh').image _
  have hmem : ∀ d e : GU Dv.σw n ⧸ K, h d.out ≠ 0 → h' (d.out⁻¹ * e.out) ≠ 0 →
      e ∈ hSe.toFinset := by
    intro d e hd he'
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_biUnion hd ⟨d.out⁻¹ • e, ?_, smul_inv_smul d.out e⟩
    have hc : (((d.out⁻¹ • e).out : GU Dv.σw n) : GU Dv.σw n ⧸ K) = ↑(d.out⁻¹ * e.out) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    show h' (d.out⁻¹ • e).out ≠ 0
    rw [eq_of_coset (hRi h' hh') hc]
    exact he'
  have hL1 : (∑ᶠ e : GU Dv.σw n ⧸ K, conv K h h' e.out • f (g * (heT e).choose)) =
      ∑ e ∈ hSe.toFinset, (∑ d ∈ (hfin h hh).toFinset, h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_]
    · refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      show (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out)) = _
      apply finsum_eq_sum_of_support_subset
      intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact left_ne_zero_of_mul hd
    · intro e he
      rw [Function.mem_support] at he
      have h1 : conv K h h' e.out ≠ 0 := fun h0 => he (by rw [h0, zero_smul])
      obtain ⟨d, hd⟩ : ∃ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h1 (finsum_eq_zero_of_forall_eq_zero hcon)
      exact hmem d e (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  have hR1 : (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out • ∑ᶠ e : GU Dv.σw n ⧸ K,
      h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)) =
      ∑ d ∈ (hfin h hh).toFinset, ∑ e ∈ hSe.toFinset, (h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := (hfin h hh).toFinset) ?_]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_, Finset.smul_sum]
      · exact Finset.sum_congr rfl fun e _ => by rw [mul_smul]
      · intro e he
        rw [Function.mem_support] at he
        exact hmem d e hd (fun h0 => he (by rw [h0, zero_smul]))
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hd (by rw [h0, zero_smul])
  rw [hL1, hR1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_smul]

/- English proof (translation)
Introduce `L _ _ _ n v w Dv U hU W _ _ h₁ h₂ hh₁ hh₂ f hf`. Conclude with `conv_of Dv U hU (GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv) (fun u hu => GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv u hu _) (GlobalTheory.T.inertLocal_surjective_from_trivOutside L n v w Dv) W h₁ hh₁ h₂ hh₂ f hf`.
-/
theorem heckeFunI_conv_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.conv (Formalism.UG.KU Dv.σw n) h₁ h₂) f = heckeFunI L n U Dv h₁ (heckeFunI L n U Dv h₂ f) := by
  intro L _ _ _ n v w Dv U hU W _ _ h₁ h₂ hh₁ hh₂ f hf
  exact conv_of Dv U hU (GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv)
    (fun u hu => GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv u hu _) (GlobalTheory.T.inertLocal_surjective_from_trivOutside L n v w Dv) W h₁ hh₁ h₂ hh₂ f hf

end GlobalTheory.InertConvMul
