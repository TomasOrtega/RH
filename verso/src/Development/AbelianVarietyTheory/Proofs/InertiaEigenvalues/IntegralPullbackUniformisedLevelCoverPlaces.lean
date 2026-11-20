import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUpInt

/- English proof (translation)
Establish `h0 : la.valuation K x ≠ 0` using `by simpa using hx`. Rewrite using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Simplify using `only [vLa]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_lt_one_iff {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    la.valuation K x < 1 ↔ 0 < vLa la x := by
  have h0 : la.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [vLa]
  omega

/- English proof (translation)
Take `⟨N, hN, hp⟩` from `GlobalTheory.IntCoefExt.exists_nat_pos ho`. Take `⟨la', e, ho'⟩` from `GlobalTheory.IntCoefExt.exists_overLa (io₂.comp i) hN hp`. Choose the witnesses or unpack the hypotheses as in `rfl : la' = la := by`. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hx' : (x : K) ≠ 0` using `by simpa using hx`. Establish `e1` using `ho'.2 (x : K)`. Rewrite `e1` using `[RingHom.comp_apply, ho.2]`.

Rewrite using `[h, valuation_lt_one_iff la₂ ((map_ne_zero i).2 hx'), ← la'.valuation_lt_one_iff_mem (K := K)]`. Use `(valuation_lt_one_iff la' hx').trans ?_` and prove the remaining obligations. Establish `p1 : (0 : ℤ) < e` using `by exact_mod_cast ho'.1`. Establish `p2 : (0 : ℤ) < e₂` using `by exact_mod_cast ho.1`. Rewrite using `[← mul_pos_iff_of_pos_left p1, ← e1, mul_pos_iff_of_pos_left p2]`.

Conclude with `⟨e, ho'⟩`.
-/
theorem overLa_comp {K K₂ : Type} [Field K] [NumberField K] [Field K₂] [NumberField K₂] (i : K →+* K₂)
    {la : HeightOneSpectrum (𝓞 K)} {la₂ : HeightOneSpectrum (𝓞 K₂)}
    (h : ∀ x : 𝓞 K, x ∈ la.asIdeal ↔ la₂.valuation K₂ (i x) < 1) {T : CDVR} {io₂ : K₂ →+* T.Fr} {e₂ : ℕ}
    (ho : OverLa la₂ T.V io₂ e₂) : ∃ e, OverLa la T.V (io₂.comp i) e := by
  obtain ⟨N, hN, hp⟩ := GlobalTheory.IntCoefExt.exists_nat_pos ho
  obtain ⟨la', e, ho'⟩ := GlobalTheory.IntCoefExt.exists_overLa (io₂.comp i) hN hp
  obtain rfl : la' = la := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp
    have hx' : (x : K) ≠ 0 := by simpa using hx
    have e1 := ho'.2 (x : K)
    rw [RingHom.comp_apply, ho.2] at e1
    rw [h, valuation_lt_one_iff la₂ ((map_ne_zero i).2 hx'), ← la'.valuation_lt_one_iff_mem (K := K)]
    refine (valuation_lt_one_iff la' hx').trans ?_
    have p1 : (0 : ℤ) < e := by exact_mod_cast ho'.1
    have p2 : (0 : ℤ) < e₂ := by exact_mod_cast ho.1
    rw [← mul_pos_iff_of_pos_left p1, ← e1, mul_pos_iff_of_pos_left p2]
  exact ⟨e, ho'⟩

/- English proof (translation)
Introduce `D T hT j hj σ _ C _ a n _ S S₂ hS f _ hint f₂ _ hP la₂ hla₂ v hv`. Take `⟨⟨q, T', io₂, e₂, ho, y₂, hy, η, hη, rfl⟩, rfl⟩` from `hv`. Take `⟨la, hla, hl⟩` from `hS la₂ hla₂`. Take `⟨e, ho'⟩` from `overLa_comp C.inc hl ho`. Establish `hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q`.

Introduce `e`. Establish `h1` using `GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj`. Take `⟨k, hk⟩` from `r_odd D`. Use linear arithmetic over natural numbers and integers. Establish `hA : T.Q.l.A = 1` using `hT.pins.2.1.2`.

Establish `hO` using `GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d`. Establish `hK : KA T.Q.l ≤ KA C.d.l₂` using `GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _`. Set `io' : C.c'.F →+* T'.Fr` to `io₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)`. Set `io : T.Q.c.F →+* T'.Fr` to `io₂.comp C.inc`. Establish `hio : ∀ x, io' (incF T.Q.c C.c' C.hle x) = io x` using `fun _ => rfl`.

Use `letI := io₂.toAlgebra`. Use `letI := io'.toAlgebra`. Use `letI := io.toAlgebra`. Take `⟨y', hy'⟩` from `GlobalTheory.CovPull.below_exists C.d hO hK (S := T'.Fr) (fun _ => rfl) y₂.1`. Set `y : IntFr (T.Q.Xo j) T.Q.c T' io` to `⟨y'.res C.hle hio, GlobalTheory.TransferCompare.allTest_framed _ _ _ _, (GlobalTheory.IntCoefExt.integral_res_iff C.hle T' io' io hio _).1 (GlobalTheory.CoverDown.integral_below C.d T' io' io₂ (fun _ => rfl) y' y₂.1 hy' y₂.2.2)⟩`.

Establish `e1 : evI y₂ f₂ = evI y f` using `hP T'.Fr hio (fun _ => rfl) y₂.1 y' hy'`. Establish `key` using `hint la hla _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho' y hy () trivial, rfl⟩`. Use `(GlobalTheory.IntCoefExt.nval_nonneg_iff ho.1 _).2 ?_` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `(GlobalTheory.IntCoefExt.nval_nonneg_iff ho'.1 _).1 key`.
-/
theorem pull_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, (∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ la₂ ∈ S₂, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la₂, 0 ≤ v f₂ := by
  intro D T hT j hj σ _ C _ a n _ S S₂ hS f _ hint f₂ _ hP la₂ hla₂ v hv
  obtain ⟨⟨q, T', io₂, e₂, ho, y₂, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨la, hla, hl⟩ := hS la₂ hla₂
  obtain ⟨e, ho'⟩ := overLa_comp C.inc hl ho
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    intro e
    have h1 := GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj
    obtain ⟨k, hk⟩ := r_odd D
    omega
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have hO := GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d
  have hK : KA T.Q.l ≤ KA C.d.l₂ := GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _
  let io' : C.c'.F →+* T'.Fr := io₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  let io : T.Q.c.F →+* T'.Fr := io₂.comp C.inc
  have hio : ∀ x, io' (incF T.Q.c C.c' C.hle x) = io x := fun _ => rfl
  letI := io₂.toAlgebra
  letI := io'.toAlgebra
  letI := io.toAlgebra
  obtain ⟨y', hy'⟩ := GlobalTheory.CovPull.below_exists C.d hO hK (S := T'.Fr) (fun _ => rfl) y₂.1
  let y : IntFr (T.Q.Xo j) T.Q.c T' io := ⟨y'.res C.hle hio, GlobalTheory.TransferCompare.allTest_framed _ _ _ _,
    (GlobalTheory.IntCoefExt.integral_res_iff C.hle T' io' io hio _).1
      (GlobalTheory.CoverDown.integral_below C.d T' io' io₂ (fun _ => rfl) y' y₂.1 hy' y₂.2.2)⟩
  have e1 : evI y₂ f₂ = evI y f := hP T'.Fr hio (fun _ => rfl) y₂.1 y' hy'
  have key := hint la hla _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho' y hy () trivial, rfl⟩
  refine (GlobalTheory.IntCoefExt.nval_nonneg_iff ho.1 _).2 ?_
  rw [e1]
  exact (GlobalTheory.IntCoefExt.nval_nonneg_iff ho'.1 _).1 key

end GlobalTheory.CoverUpInt
