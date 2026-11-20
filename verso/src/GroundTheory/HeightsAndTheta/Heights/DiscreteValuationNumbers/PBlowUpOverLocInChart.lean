import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace BlowUpOverLocInChart

section Graded

variable {R : Type*} [CommRing R] {κ : Type*} [DecidableEq κ] {E : κ → Type*}

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => funext o`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy => rw [map_add, hx, hy, Finsupp.mapDomain_add, Finsupp.coe_add]`. Consider the case `single v n`.

Rewrite using `[Finsupp.weight_single, Finsupp.mapDomain_single]`. Use function extensionality and compare the values at `o`. Distinguish the cases in `h : v.1 = o`. Substitute `h` using the available equality. Simplify using `[blockWeight]`.

Simplify using `[blockWeight, Pi.single_apply, Ne.symm h]`.
-/
theorem weight_blockWeight (d : (Σ o, E o) →₀ ℕ) :
    Finsupp.weight (blockWeight E) d = ⇑(d.mapDomain Sigma.fst) := by
  induction d using Finsupp.induction_linear with
  | zero => funext o; simp
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.mapDomain_add, Finsupp.coe_add]
  | single v n =>
    rw [Finsupp.weight_single, Finsupp.mapDomain_single]
    funext o
    by_cases h : v.1 = o
    · subst h; simp [blockWeight]
    · simp [blockWeight, Pi.single_apply, Ne.symm h]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial d c`. Establish `hX : (monomial (d.mapDomain Sigma.fst) (1 : B) : MvPolynomial κ B) = d.prod fun v n => (X v.1 : MvPolynomial κ B) ^ n`. Rewrite using `[← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]`. Simplify using `[rename_X]`.

Establish `hC : (C (d.prod fun v n => a v ^ n) : MvPolynomial κ B) = d.prod fun v n => C (a v) ^ n`. Rewrite using `[map_finsuppProd]`. Simplify using the standard rewrite rules. Establish `h : eval₂ (C.comp f) (fun v => C (a v) * X v.1) (monomial d c) = C (eval₂ f a (monomial d c)) * monomial (d.mapDomain Sigma.fst) 1`. Rewrite using `[eval₂_monomial, eval₂_monomial, hX, map_mul, hC]`.

Simplify using `only [mul_pow, Finsupp.prod_mul, RingHom.coe_comp, Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, coeff_C_mul, coeff_monomial, weightedHomogeneousComponent_monomial', weight_blockWeight]`. Distinguish the cases in `hd : d.mapDomain Sigma.fst = e`. Substitute `hd` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hd, if_neg (fun h => hd (DFunLike.coe_injective h)), mul_zero, eval₂_zero]`. Consider the case `add p q hp hq => simp only [eval₂_add, map_add, coeff_add, hp, hq]`.
-/
theorem coeff_eval₂_C_mul_X_fst {B : Type*} [CommRing B] (f : R →+* B) (a : (Σ o, E o) → B)
    (p : MvPolynomial (Σ o, E o) R) (e : κ →₀ ℕ) :
    coeff e (eval₂ (C.comp f) (fun v => C (a v) * X v.1) p) =
      eval₂ f a (weightedHomogeneousComponent (blockWeight E) ⇑e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hX : (monomial (d.mapDomain Sigma.fst) (1 : B) : MvPolynomial κ B) =
        d.prod fun v n => (X v.1 : MvPolynomial κ B) ^ n := by
      rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
      simp [rename_X]
    have hC : (C (d.prod fun v n => a v ^ n) : MvPolynomial κ B) = d.prod fun v n => C (a v) ^ n := by
      rw [map_finsuppProd]
      simp
    have h : eval₂ (C.comp f) (fun v => C (a v) * X v.1) (monomial d c) =
        C (eval₂ f a (monomial d c)) * monomial (d.mapDomain Sigma.fst) 1 := by
      rw [eval₂_monomial, eval₂_monomial, hX, map_mul, hC]
      simp only [mul_pow, Finsupp.prod_mul, RingHom.coe_comp, Function.comp_apply]
      ring
    rw [h, coeff_C_mul, coeff_monomial, weightedHomogeneousComponent_monomial', weight_blockWeight]
    by_cases hd : d.mapDomain Sigma.fst = e
    · subst hd
      simp
    · rw [if_neg hd, if_neg (fun h => hd (DFunLike.coe_injective h)), mul_zero, eval₂_zero]
  | add p q hp hq => simp only [eval₂_add, map_add, coeff_add, hp, hq]

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[coeff_eval₂_C_mul_X_fst, coeff_monomial]`. Distinguish the cases in `he : (⇑e : κ → ℕ) = b`. Establish `: Finsupp.equivFunOnFinite.symm b = e`. Rewrite using `[← he]`.

Conclude with `Finsupp.equivFunOnFinite.symm_apply_apply e`. Rewrite using `[if_pos this, he, hp.weightedHomogeneousComponent_same]`. Establish `: Finsupp.equivFunOnFinite.symm b ≠ e` using `fun h => he (by rw [← h]; simp)`. Rewrite using `[if_neg this, hp.weightedHomogeneousComponent_ne _ he, eval₂_zero]`.
-/
theorem eval₂_C_mul_X_fst_of_homog [Fintype κ] {B : Type*} [CommRing B] (f : R →+* B)
    (a : (Σ o, E o) → B) {p : MvPolynomial (Σ o, E o) R} {b : κ → ℕ}
    (hp : IsWeightedHomogeneous (blockWeight E) p b) :
    eval₂ (C.comp f) (fun v => C (a v) * X v.1) p =
      monomial (Finsupp.equivFunOnFinite.symm b) (eval₂ f a p) := by
  classical
  ext e
  rw [coeff_eval₂_C_mul_X_fst, coeff_monomial]
  by_cases he : (⇑e : κ → ℕ) = b
  · have : Finsupp.equivFunOnFinite.symm b = e := by
      rw [← he]
      exact Finsupp.equivFunOnFinite.symm_apply_apply e
    rw [if_pos this, he, hp.weightedHomogeneousComponent_same]
  · have : Finsupp.equivFunOnFinite.symm b ≠ e := fun h => he (by rw [← h]; simp)
    rw [if_neg this, hp.weightedHomogeneousComponent_ne _ he, eval₂_zero]

/- English proof (translation)
Establish `h1 : eval₂ f (fun v => x v * s v.1) p = eval s (eval₂ (C.comp f) (fun v => C (x v) * X v.1) p)`. Rewrite using `[eval, eval₂_comp_left]`. Use `congr 1`. Use extensionality with `r`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules. Rewrite using `[h1, eval₂_C_mul_X_fst_of_homog f x hp, eval_monomial, Finsupp.prod_fintype _ _ (fun o => pow_zero _)]`. Simplify using the standard rewrite rules.
-/
theorem eval₂_mul_fst_of_homog [Fintype κ] {B : Type*} [CommRing B] (f : R →+* B)
    (x : (Σ o, E o) → B) (s : κ → B) {p : MvPolynomial (Σ o, E o) R} {b : κ → ℕ}
    (hp : IsWeightedHomogeneous (blockWeight E) p b) :
    eval₂ f (fun v => x v * s v.1) p = eval₂ f x p * ∏ o, s o ^ b o := by
  have h1 : eval₂ f (fun v => x v * s v.1) p =
      eval s (eval₂ (C.comp f) (fun v => C (x v) * X v.1) p) := by
    rw [eval, eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext v
      simp
  rw [h1, eval₂_C_mul_X_fst_of_homog f x hp, eval_monomial,
    Finsupp.prod_fintype _ _ (fun o => pow_zero _)]
  simp

end Graded

section Lift

variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

/- English proof (translation)
Establish `key : ∀ a : (Σ k, ι k) →₀ ℕ, Finsupp.weight (blockWeight (extIdx ι J)) (a.mapDomain fun v : Σ k, ι k => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o)) = liftMDeg (Finsupp.weight (blockWeight ι) a)`. Introduce `a`. Proceed by induction on `a using Finsupp.induction_linear with`. Consider the case `zero => funext o; cases o <;> simp [liftMDeg]`. Consider the case `add x y hx hy`.

Rewrite using `[Finsupp.mapDomain_add, map_add, map_add, hx, hy]`. Apply the tactic sequence `funext o; cases o <;> simp [liftMDeg]`. Consider the case `single v n`. Rewrite using `[Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]`. Apply the tactic sequence `funext o; cases o <;> simp [liftMDeg, blockWeight, Pi.single_apply]`.

Establish `inj : ∀ y z : K → ℕ, liftMDeg y = liftMDeg z ↔ y = z` using `fun y z => ⟨fun h => funext fun k => congrFun h (some k), fun h => h ▸ rfl⟩`. Proceed by induction on `g using MvPolynomial.induction_on' with`. Consider the case `monomial d r`. Simplify using `only [liftForm, rename_monomial]`. Rewrite using `[weightedHomogeneousComponent_monomial', weightedHomogeneousComponent_monomial', key, inj]`.

Use `split_ifs`. Simplify using `[rename_monomial]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem component_liftForm (g : MRing ι R) (c : K → ℕ) :
    weightedHomogeneousComponent (blockWeight (extIdx ι J)) (liftMDeg c) (liftForm g) =
      liftForm (weightedHomogeneousComponent (blockWeight ι) c g) := by
  classical
  have key : ∀ a : (Σ k, ι k) →₀ ℕ,
      Finsupp.weight (blockWeight (extIdx ι J))
        (a.mapDomain fun v : Σ k, ι k => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o)) =
      liftMDeg (Finsupp.weight (blockWeight ι) a) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => funext o; cases o <;> simp [liftMDeg]
    | add x y hx hy =>
      rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy]
      funext o; cases o <;> simp [liftMDeg]
    | single v n =>
      rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
      funext o; cases o <;> simp [liftMDeg, blockWeight, Pi.single_apply]
  have inj : ∀ y z : K → ℕ, liftMDeg y = liftMDeg z ↔ y = z :=
    fun y z => ⟨fun h => funext fun k => congrFun h (some k), fun h => h ▸ rfl⟩
  induction g using MvPolynomial.induction_on' with
  | monomial d r =>
    simp only [liftForm, rename_monomial]
    rw [weightedHomogeneousComponent_monomial', weightedHomogeneousComponent_monomial', key, inj]
    split_ifs
    · simp [rename_monomial]
    · simp
  | add p q hp hq => simp only [map_add, hp, hq]

end Lift

end BlowUpOverLocInChart

set_option maxHeartbeats 1600000 in
open BlowUpOverLocInChart in

/- English proof (translation)
Introduce `R _ K _ _ ι J P W _ hPh hW hPW hrel N u hu j huj`. Use `set L := FractionRing (MRing ι R ⧸ P)`. Set `ev : MRing ι R →+* L` to `(algebraMap (MRing ι R ⧸ P) L).comp (Ideal.Quotient.mk P)`. Establish `hev : ∀ g, ev g = algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P g)` using `fun _ => rfl`. Establish `hne : ∀ g, g ∉ W → ev g ≠ 0` using `fun g hg => HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))`.

Take `⟨Cr, hCr⟩ : ∃ Cr : Subring L, Cr = Subring.closure ((homLocRing P W : Set L) ∪ Set.range fun k => algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P (u k)) / algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P (u j)))` from `⟨_, rfl⟩`. Rewrite using `[← hCr]`. Establish `hgen : ∀ (c : K → ℕ) (x y : MRing ι R), IsMultiHomog x c → IsMultiHomog y c → y ∉ W → ev x / ev y ∈ Cr` using `fun c x y hx hy hyW => by`. Rewrite using `[hCr]`. Conclude with `Subring.subset_closure (Or.inl (Subring.subset_closure ⟨c, x, y, hx, hy, hyW, rfl⟩))`.

Establish `hrange : ∀ l, ev (u l) / ev (u j) ∈ Cr` using `fun l => by`. Rewrite using `[hCr]`. Conclude with `Subring.subset_closure (Or.inr ⟨l, rfl⟩)`. Use `clear hCr`. Establish `h1W : (1 : MRing ι R) ∉ W` using `fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)`.

Introduce `f hf`. Assume the negation of the conclusion as `hfC`. Set `𝔇 : Ideal Cr` to `{ carrier := {d | (d : L) * f ∈ Cr} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, Subring.coe_add, add_mul] at ha hb ⊢`.

Conclude with `Cr.add_mem ha hb`. Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, zero_mul]`. Conclude with `Cr.zero_mem`. Use the proof step `smul_mem' := by`.

Introduce `c d hd`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hd ⊢`. Conclude with `Cr.mul_mem c.2 hd }`. Establish `h𝔇 : 𝔇 ≠ ⊤`. Introduce `h`.

Establish `h1 : (1 : Cr) ∈ 𝔇` using `by rw [h]; trivial`. Establish `h2 : ((1 : Cr) : L) * f ∈ Cr` using `h1`. Rewrite `h2` using `[OneMemClass.coe_one, one_mul]`. Conclude with `hfC h2`. Take `⟨𝔮, h𝔮, h𝔇𝔮⟩` from `Ideal.exists_le_maximal 𝔇 h𝔇`.

Establish `h𝔮p : 𝔮.IsPrime` using `h𝔮.isPrime`. Establish `h0mem : (0 : Cr) ∈ 𝔮` using `𝔮.zero_mem`. Use `choose i hi using hrel`. Establish `hXne : ∀ k, ev (X ⟨k, i k⟩) ≠ 0` using `fun k => hne _ (hi k)`. Establish `hune : ev (u j) ≠ 0` using `HomLocRingMem.algebraMap_mk_ne_zero P huj`.

Set `Dinv : Option K → L` to `fun o => Option.elim o (ev (u j))⁻¹ fun k => (ev (X ⟨k, i k⟩))⁻¹`. Set `x : (Σ o, extIdx ι J o) → L` to `fun v => ev (blowUpAtOne u v)`. Set `aL : (Σ o, extIdx ι J o) → L` to `fun v => x v * Dinv v.1`. Establish `haL : ∀ v, aL v ∈ Cr`. Introduce and unpack `⟨o, l⟩`.

Consider the cases of `o with`. Consider the case `none`. Simplify `hrange l` using `[aL, x, Dinv, blowUpAtOne, div_eq_mul_inv]`. Consider the case `some k`. Establish `h` using `hgen (blockWeight ι ⟨k, l⟩) (X ⟨k, l⟩) (X ⟨k, i k⟩) (isWeightedHomogeneous_X R _ _) (isWeightedHomogeneous_X R _ _) (hi k)`.

Simplify `h` using `[aL, x, Dinv, blowUpAtOne, div_eq_mul_inv]`. Take `⟨aC, haC⟩ : ∃ aC : (Σ o, extIdx ι J o) → Cr, ∀ v, (aC v : L) = aL v` from `⟨fun v => ⟨aL v, haL v⟩, fun _ => rfl⟩`. Establish `hcst : ∀ r : R, ev (C r) ∈ Cr` using `fun r => by`. Establish `h` using `hgen 0 (C r) 1 (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_one _ _) h1W`. Simplify using `using h`.

Take `⟨fC, hfCv⟩ : ∃ fC : R →+* Cr, ∀ r, (fC r : L) = ev (C r)` from `⟨(ev.comp C).codRestrict Cr hcst, fun _ => rfl⟩`. Take `⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Σ o, extIdx ι J o) R →+* MvPolynomial (Option K) Cr, ψ = eval₂Hom (C.comp fC) fun v => C (aC v) * X v.1` from `⟨_, rfl⟩`. Take `⟨Q, hQdef⟩ : ∃ Q : Ideal (MRing (extIdx ι J) R), Q = RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk 𝔮)).comp ψ)` from `⟨_, rfl⟩`. Establish `memQ : ∀ F, F ∈ Q ↔ ∀ e : Option K →₀ ℕ, eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) ∈ 𝔮`. Introduce `F`.

Simplify using `only [hQdef, hψ, RingHom.mem_ker, RingHom.comp_apply, MvPolynomial.ext_iff, coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem, coe_eval₂Hom, coeff_eval₂_C_mul_X_fst]`. Establish `hσ : ∀ F, eval₂ (ev.comp C) x F = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F)`. Introduce `F`. Establish `h : (eval₂Hom (ev.comp C) x : MRing (extIdx ι J) R →+* L) = (algebraMap (MRing ι R ⧸ P) L).comp (blowUpEval P u)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using `[ev, blowUpEval]`. Apply the tactic sequence `try rfl`. Introduce and unpack `⟨o, l⟩`. Apply the tactic sequence `cases o <;> simp [x, ev, blowUpEval, blowUpAtOne, blowUpSubst]`.

Conclude with `DFunLike.congr_fun h F`. Establish `hval : ∀ (F : MRing (extIdx ι J) R) (b : Option K → ℕ), IsMultiHomog F b → ((eval₂ fC aC F : Cr) : L) = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) * ∏ o, Dinv o ^ b o`. Introduce `F b hF`. Establish `e1 : ((eval₂ fC aC F : Cr) : L) = eval₂ (ev.comp C) aL F`. Establish `h` using `eval₂_comp_left Cr.subtype fC aC F`.

Rewrite `h` using `[Subring.coe_subtype]`. Rewrite using `[h]`. Use `congr 1`. Use extensionality with `r`. Simplify using `[hfCv]`.

Use function extensionality and compare the values at `v`. Simplify using `[haC]`. Rewrite using `[e1, eval₂_mul_fst_of_homog (ev.comp C) x Dinv hF, hσ]`. Establish `hcomp : ∀ (F : MRing (extIdx ι J) R) (b : Option K → ℕ) (e : Option K →₀ ℕ), IsMultiHomog F b → eval₂ fC aC F ∈ 𝔮 → eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) ∈ 𝔮`. Introduce `F b e hF h`.

Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hF)]`. Use `split_ifs`. Conclude with `h`. Rewrite using `[eval₂_zero]`. Conclude with `𝔮.zero_mem`.

Establish `hQp : Q.IsPrime` using `hQdef ▸ RingHom.ker_isPrime _`. Establish `hQh : IsMultiHomogIdeal Q`. Introduce `F hF b`. Rewrite `hF`, the goal using `[memQ]`. Introduce `e`.

Use `hcomp _ b e (weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_` and prove the remaining obligations. Use `hF (Finsupp.equivFunOnFinite.symm b)` as an intermediate fact. Rewrite `this` using `[Finsupp.coe_equivFunOnFinite_symm]`. Then use the resulting hypothesis. Establish `hQr : IsRelevant Q`. Establish `hXnot : ∀ (o : Option K) (l : extIdx ι J o), aL ⟨o, l⟩ = 1 → (X ⟨o, l⟩ : MRing (extIdx ι J) R) ∉ Q`.

Introduce `o l h1 hmem`. Rewrite `hmem` using `[hQdef, RingHom.mem_ker, RingHom.comp_apply]`. Simplify using `only [hψ, coe_eval₂Hom, eval₂_X, map_mul, map_C, map_X] at hmem`. Establish `h2` using `congrArg (coeff (Finsupp.single o 1)) hmem`. Simplify using `only [coeff_C_mul, coeff_X, coeff_X', if_true, mul_one, coeff_zero] at h2`.

Rewrite `h2` using `[Ideal.Quotient.eq_zero_iff_mem]`. Establish `h1' : aC ⟨o, l⟩ = 1` using `Subtype.ext (by rw [haC]; exact h1)`. Rewrite `h2` using `[h1']`. Conclude with `h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h2)`. Introduce `o`.

Consider the cases of `o with`. Consider the case `none`. Use `⟨j, hXnot none j ?_⟩` and prove the remaining obligations. Simplify using `only [aL, x, Dinv, blowUpAtOne, Option.elim]`. Conclude with `mul_inv_cancel₀ hune`.

Consider the case `some k`. Use `⟨i k, hXnot (some k) (i k) ?_⟩` and prove the remaining obligations. Simplify using `only [aL, x, Dinv, blowUpAtOne, Option.elim]`. Conclude with `mul_inv_cancel₀ (hXne k)`. Establish `hQb : blowUpOf P u ≤ Q`.

Introduce `F hF`. Rewrite using `[memQ]`. Introduce `e`. Establish `hFe` using `isMultiHomogIdeal_blowUpOf hPh N u hu F hF ⇑e`. Establish `h0 : eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hval _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]`. Establish `hz : blowUpEval P u (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) = 0`. Rewrite `hFe` using `[blowUpOf, RingHom.mem_ker]`. Use `show Polynomial.eval 1 (aeval (blowUpSubst P u) _) = 0`.

Rewrite using `[hFe, Polynomial.eval_zero]`. Rewrite using `[hz, map_zero, zero_mul, ZeroMemClass.coe_zero]`. Rewrite using `[h0]`. Conclude with `h0mem`. Establish `hQW : Q.comap (liftForm (ι` using `ι) (J := J) (R := R)) ≤ W := by`.

Introduce `g hg`. Rewrite `hg` using `[Ideal.mem_comap]`. Assume the negation of the conclusion as `hgW`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, weightedHomogeneousComponent (blockWeight ι) c g ∉ W := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Apply `hgW` to reduce the goal to its premises. Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight ι) g, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp g)]`. Conclude with `Ideal.sum_mem _ fun c _ => hall c`. Establish `hmem` using `(memQ _).mp hg (Finsupp.equivFunOnFinite.symm (liftMDeg c))`.

Rewrite `hmem` using `[Finsupp.coe_equivFunOnFinite_symm, component_liftForm]`. Use `set gc := weightedHomogeneousComponent (blockWeight ι) c g with hgc_def`. Establish `hgc : IsMultiHomog gc c` using `weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Establish `hmW : (powMonomial c i : MRing ι R) ∉ W` using `fun h => (W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hi k) _) h`. Establish `hinv` using `hgen c _ _ (isMultiHomog_powMonomial c i) hgc hc`.

Establish `hv` using `hval _ _ (isMultiHomog_liftForm (J := J) hgc)`. Rewrite `hv` using `[blowUpEval_liftForm, Fintype.prod_option]`. Establish `hpm : ev (powMonomial c i) = ∏ k, ev (X ⟨k, i k⟩) ^ c k`. Simplify using `[powMonomial, map_prod, map_pow]`. Establish `hunit : eval₂ fC aC (liftForm gc) * ⟨_, hinv⟩ = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subring.coe_mul, hv]`. Simplify using `only [Dinv, liftMDeg, Option.elim, pow_zero, one_mul, inv_pow, Finset.prod_inv_distrib, OneMemClass.coe_one]`. Rewrite using `[hpm, ← hev]`. Establish `h1 : ev gc ≠ 0` using `hne _ hc`.

Establish `h2 : ∏ k, ev (X ⟨k, i k⟩) ^ c k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hXne k)`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, one_mul]`. Conclude with `h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr (hunit ▸ 𝔮.mul_mem_right _ hmem))`.

Establish `hfQ : f ∈ blowUpLocRing P u Q`. Establish `h` using `hf`. Simplify using `only [blowUpOverLoc, Subring.mem_iInf] at h`. Conclude with `h Q ⟨hQp, hQh, hQr, hQb, hQW⟩`. Establish `key : ∀ z ∈ blowUpLocRing P u Q, ∃ d : Cr, d ∉ 𝔮 ∧ (d : L) * z ∈ Cr`.

Introduce `z hz`. Use `Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨b, F, G, hF, hG, hGQ, rfl⟩`. Establish `hd : eval₂ fC aC G ∉ 𝔮` using `fun h => hGQ ((memQ G).mpr fun e => hcomp G b e hG h)`. Use `⟨eval₂ fC aC G, hd, ?_⟩` and prove the remaining obligations.

Establish `hG0 : algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G) ≠ 0`. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Establish `: eval₂ fC aC G = 0` using `Subtype.ext (by rw [hval G b hG, h0, zero_mul, ZeroMemClass.coe_zero])`. Rewrite using `[this]`.

Conclude with `𝔮.zero_mem`. Establish `e2 : ((eval₂ fC aC G : Cr) : L) * (algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) / algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G)) = ((eval₂ fC aC F : Cr) : L)`. Rewrite using `[hval G b hG, hval F b hF]`. Generalize the expression as in `algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G) = g at hG0 ⊢`. Combine the equalities or inequalities in the displayed calculation.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [mul_inv_cancel₀ hG0, mul_one]`. Rewrite using `[e2]`. Conclude with `(eval₂ fC aC F).2`. Conclude with `⟨1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simpa using Cr.zero_mem⟩`.

Conclude with `⟨1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simpa using Cr.one_mem⟩`. Introduce and unpack `a b - - ⟨d₁, h₁, e₁⟩ ⟨d₂, h₂, e₂⟩`. Use `⟨d₁ * d₂, fun h => (h𝔮p.mem_or_mem h).elim h₁ h₂, ?_⟩` and prove the remaining obligations. Establish `: ((d₁ * d₂ : Cr) : L) * (a + b) = (d₂ : L) * ((d₁ : L) * a) + (d₁ : L) * ((d₂ : L) * b)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Cr.add_mem (Cr.mul_mem d₂.2 e₁) (Cr.mul_mem d₁.2 e₂)`. Introduce and unpack `a - ⟨d, h, e⟩`. Conclude with `⟨d, h, by rw [mul_neg]; exact Cr.neg_mem e⟩`.

Introduce and unpack `a b - - ⟨d₁, h₁, e₁⟩ ⟨d₂, h₂, e₂⟩`. Use `⟨d₁ * d₂, fun h => (h𝔮p.mem_or_mem h).elim h₁ h₂, ?_⟩` and prove the remaining obligations. Establish `: ((d₁ * d₂ : Cr) : L) * (a * b) = ((d₁ : L) * a) * ((d₂ : L) * b)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Cr.mul_mem e₁ e₂`. Take `⟨d, hd, hdf⟩` from `key f hfQ`. Conclude with `hd (h𝔇𝔮 hdf)`.
-/
theorem BlowUpOverLocInChart.proof : BlowUpOverLocInChart.Statement.{u} := by
  intro R _ K _ _ ι J P W _ hPh hW hPW hrel N u hu j huj
  set L := FractionRing (MRing ι R ⧸ P)
  let ev : MRing ι R →+* L := (algebraMap (MRing ι R ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hev : ∀ g, ev g = algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P g) := fun _ => rfl
  have hne : ∀ g, g ∉ W → ev g ≠ 0 := fun g hg =>
    HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))
  obtain ⟨Cr, hCr⟩ : ∃ Cr : Subring L, Cr = Subring.closure ((homLocRing P W : Set L) ∪ Set.range fun k =>
      algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P (u k)) /
        algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P (u j))) := ⟨_, rfl⟩
  rw [← hCr]
  have hgen : ∀ (c : K → ℕ) (x y : MRing ι R), IsMultiHomog x c → IsMultiHomog y c → y ∉ W →
      ev x / ev y ∈ Cr := fun c x y hx hy hyW => by
    rw [hCr]
    exact Subring.subset_closure (Or.inl (Subring.subset_closure ⟨c, x, y, hx, hy, hyW, rfl⟩))
  have hrange : ∀ l, ev (u l) / ev (u j) ∈ Cr := fun l => by
    rw [hCr]
    exact Subring.subset_closure (Or.inr ⟨l, rfl⟩)
  clear hCr
  have h1W : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  intro f hf
  by_contra hfC

  let 𝔇 : Ideal Cr :=
    { carrier := {d | (d : L) * f ∈ Cr}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact Cr.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, zero_mul]
        exact Cr.zero_mem
      smul_mem' := by
        intro c d hd
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hd ⊢
        exact Cr.mul_mem c.2 hd }
  have h𝔇 : 𝔇 ≠ ⊤ := by
    intro h
    have h1 : (1 : Cr) ∈ 𝔇 := by rw [h]; trivial
    have h2 : ((1 : Cr) : L) * f ∈ Cr := h1
    rw [OneMemClass.coe_one, one_mul] at h2
    exact hfC h2
  obtain ⟨𝔮, h𝔮, h𝔇𝔮⟩ := Ideal.exists_le_maximal 𝔇 h𝔇
  have h𝔮p : 𝔮.IsPrime := h𝔮.isPrime
  have h0mem : (0 : Cr) ∈ 𝔮 := 𝔮.zero_mem

  choose i hi using hrel
  have hXne : ∀ k, ev (X ⟨k, i k⟩) ≠ 0 := fun k => hne _ (hi k)
  have hune : ev (u j) ≠ 0 := HomLocRingMem.algebraMap_mk_ne_zero P huj
  let Dinv : Option K → L := fun o => Option.elim o (ev (u j))⁻¹ fun k => (ev (X ⟨k, i k⟩))⁻¹
  let x : (Σ o, extIdx ι J o) → L := fun v => ev (blowUpAtOne u v)
  let aL : (Σ o, extIdx ι J o) → L := fun v => x v * Dinv v.1
  have haL : ∀ v, aL v ∈ Cr := by
    rintro ⟨o, l⟩
    cases o with
    | none =>
      simpa [aL, x, Dinv, blowUpAtOne, div_eq_mul_inv] using hrange l
    | some k =>
      have h := hgen (blockWeight ι ⟨k, l⟩) (X ⟨k, l⟩) (X ⟨k, i k⟩) (isWeightedHomogeneous_X R _ _)
        (isWeightedHomogeneous_X R _ _) (hi k)
      simpa [aL, x, Dinv, blowUpAtOne, div_eq_mul_inv] using h
  obtain ⟨aC, haC⟩ : ∃ aC : (Σ o, extIdx ι J o) → Cr, ∀ v, (aC v : L) = aL v := ⟨fun v => ⟨aL v, haL v⟩, fun _ => rfl⟩
  have hcst : ∀ r : R, ev (C r) ∈ Cr := fun r => by
    have h := hgen 0 (C r) 1 (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_one _ _) h1W
    simpa using h
  obtain ⟨fC, hfCv⟩ : ∃ fC : R →+* Cr, ∀ r, (fC r : L) = ev (C r) :=
    ⟨(ev.comp C).codRestrict Cr hcst, fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Σ o, extIdx ι J o) R →+* MvPolynomial (Option K) Cr,
      ψ = eval₂Hom (C.comp fC) fun v => C (aC v) * X v.1 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Ideal (MRing (extIdx ι J) R),
      Q = RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk 𝔮)).comp ψ) := ⟨_, rfl⟩
  have memQ : ∀ F, F ∈ Q ↔ ∀ e : Option K →₀ ℕ,
      eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) ∈ 𝔮 := by
    intro F
    simp only [hQdef, hψ, RingHom.mem_ker, RingHom.comp_apply, MvPolynomial.ext_iff, coeff_map, coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, coe_eval₂Hom, coeff_eval₂_C_mul_X_fst]

  have hσ : ∀ F, eval₂ (ev.comp C) x F = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) := by
    intro F
    have h : (eval₂Hom (ev.comp C) x : MRing (extIdx ι J) R →+* L) =
        (algebraMap (MRing ι R ⧸ P) L).comp (blowUpEval P u) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [ev, blowUpEval]
        try rfl
      · rintro ⟨o, l⟩
        cases o <;> simp [x, ev, blowUpEval, blowUpAtOne, blowUpSubst]
    exact DFunLike.congr_fun h F
  have hval : ∀ (F : MRing (extIdx ι J) R) (b : Option K → ℕ), IsMultiHomog F b →
      ((eval₂ fC aC F : Cr) : L) = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) * ∏ o, Dinv o ^ b o := by
    intro F b hF
    have e1 : ((eval₂ fC aC F : Cr) : L) = eval₂ (ev.comp C) aL F := by
      have h := eval₂_comp_left Cr.subtype fC aC F
      rw [Subring.coe_subtype] at h
      rw [h]
      congr 1
      · ext r
        simp [hfCv]
      · funext v
        simp [haC]
    rw [e1, eval₂_mul_fst_of_homog (ev.comp C) x Dinv hF, hσ]
  have hcomp : ∀ (F : MRing (extIdx ι J) R) (b : Option K → ℕ) (e : Option K →₀ ℕ), IsMultiHomog F b →
      eval₂ fC aC F ∈ 𝔮 → eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) ∈ 𝔮 := by
    intro F b e hF h
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hF)]
    split_ifs
    · exact h
    · rw [eval₂_zero]
      exact 𝔮.zero_mem

  have hQp : Q.IsPrime := hQdef ▸ RingHom.ker_isPrime _
  have hQh : IsMultiHomogIdeal Q := by
    intro F hF b
    rw [memQ] at hF ⊢
    intro e
    refine hcomp _ b e (weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_
    have := hF (Finsupp.equivFunOnFinite.symm b)
    rwa [Finsupp.coe_equivFunOnFinite_symm] at this
  have hQr : IsRelevant Q := by
    have hXnot : ∀ (o : Option K) (l : extIdx ι J o), aL ⟨o, l⟩ = 1 → (X ⟨o, l⟩ : MRing (extIdx ι J) R) ∉ Q := by
      intro o l h1 hmem
      rw [hQdef, RingHom.mem_ker, RingHom.comp_apply] at hmem
      simp only [hψ, coe_eval₂Hom, eval₂_X, map_mul, map_C, map_X] at hmem
      have h2 := congrArg (coeff (Finsupp.single o 1)) hmem
      simp only [coeff_C_mul, coeff_X, coeff_X', if_true, mul_one, coeff_zero] at h2
      rw [Ideal.Quotient.eq_zero_iff_mem] at h2
      have h1' : aC ⟨o, l⟩ = 1 := Subtype.ext (by rw [haC]; exact h1)
      rw [h1'] at h2
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    intro o
    cases o with
    | none =>
      refine ⟨j, hXnot none j ?_⟩
      simp only [aL, x, Dinv, blowUpAtOne, Option.elim]
      exact mul_inv_cancel₀ hune
    | some k =>
      refine ⟨i k, hXnot (some k) (i k) ?_⟩
      simp only [aL, x, Dinv, blowUpAtOne, Option.elim]
      exact mul_inv_cancel₀ (hXne k)
  have hQb : blowUpOf P u ≤ Q := by
    intro F hF
    rw [memQ]
    intro e
    have hFe := isMultiHomogIdeal_blowUpOf hPh N u hu F hF ⇑e
    have h0 : eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) = 0 := by
      apply Subtype.ext
      rw [hval _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
      have hz : blowUpEval P u (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) = 0 := by
        rw [blowUpOf, RingHom.mem_ker] at hFe
        show Polynomial.eval 1 (aeval (blowUpSubst P u) _) = 0
        rw [hFe, Polynomial.eval_zero]
      rw [hz, map_zero, zero_mul, ZeroMemClass.coe_zero]
    rw [h0]
    exact h0mem
  have hQW : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W := by
    intro g hg
    rw [Ideal.mem_comap] at hg
    by_contra hgW
    obtain ⟨c, hc⟩ : ∃ c, weightedHomogeneousComponent (blockWeight ι) c g ∉ W := by
      by_contra hall
      push_neg at hall
      apply hgW
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) g,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp g)]
      exact Ideal.sum_mem _ fun c _ => hall c
    have hmem := (memQ _).mp hg (Finsupp.equivFunOnFinite.symm (liftMDeg c))
    rw [Finsupp.coe_equivFunOnFinite_symm, component_liftForm] at hmem
    set gc := weightedHomogeneousComponent (blockWeight ι) c g with hgc_def
    have hgc : IsMultiHomog gc c := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hmW : (powMonomial c i : MRing ι R) ∉ W := fun h =>
      (W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hi k) _) h
    have hinv := hgen c _ _ (isMultiHomog_powMonomial c i) hgc hc
    have hv := hval _ _ (isMultiHomog_liftForm (J := J) hgc)
    rw [blowUpEval_liftForm, Fintype.prod_option] at hv
    have hpm : ev (powMonomial c i) = ∏ k, ev (X ⟨k, i k⟩) ^ c k := by
      simp [powMonomial, map_prod, map_pow]
    have hunit : eval₂ fC aC (liftForm gc) * ⟨_, hinv⟩ = 1 := by
      apply Subtype.ext
      rw [Subring.coe_mul, hv]
      simp only [Dinv, liftMDeg, Option.elim, pow_zero, one_mul, inv_pow, Finset.prod_inv_distrib,
        OneMemClass.coe_one]
      rw [hpm, ← hev]
      have h1 : ev gc ≠ 0 := hne _ hc
      have h2 : ∏ k, ev (X ⟨k, i k⟩) ^ c k ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hXne k)
      calc _ = (ev gc * (ev gc)⁻¹) * ((∏ k, ev (X ⟨k, i k⟩) ^ c k) * (∏ k, ev (X ⟨k, i k⟩) ^ c k)⁻¹) := by
            ring
        _ = 1 := by rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, one_mul]
    exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr (hunit ▸ 𝔮.mul_mem_right _ hmem))

  have hfQ : f ∈ blowUpLocRing P u Q := by
    have h := hf
    simp only [blowUpOverLoc, Subring.mem_iInf] at h
    exact h Q ⟨hQp, hQh, hQr, hQb, hQW⟩

  have key : ∀ z ∈ blowUpLocRing P u Q, ∃ d : Cr, d ∉ 𝔮 ∧ (d : L) * z ∈ Cr := by
    intro z hz
    refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨b, F, G, hF, hG, hGQ, rfl⟩
      have hd : eval₂ fC aC G ∉ 𝔮 := fun h => hGQ ((memQ G).mpr fun e => hcomp G b e hG h)
      refine ⟨eval₂ fC aC G, hd, ?_⟩
      have hG0 : algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G) ≠ 0 := by
        intro h0
        apply hd
        have : eval₂ fC aC G = 0 := Subtype.ext (by rw [hval G b hG, h0, zero_mul, ZeroMemClass.coe_zero])
        rw [this]
        exact 𝔮.zero_mem
      have e2 : ((eval₂ fC aC G : Cr) : L) *
          (algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) / algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G)) =
          ((eval₂ fC aC F : Cr) : L) := by
        rw [hval G b hG, hval F b hF]
        generalize algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G) = g at hG0 ⊢
        calc _ = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) * (∏ o, Dinv o ^ b o) * (g * g⁻¹) := by
              ring
          _ = _ := by rw [mul_inv_cancel₀ hG0, mul_one]
      rw [e2]
      exact (eval₂ fC aC F).2
    · exact ⟨1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simpa using Cr.zero_mem⟩
    · exact ⟨1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simpa using Cr.one_mem⟩
    · rintro a b - - ⟨d₁, h₁, e₁⟩ ⟨d₂, h₂, e₂⟩
      refine ⟨d₁ * d₂, fun h => (h𝔮p.mem_or_mem h).elim h₁ h₂, ?_⟩
      have : ((d₁ * d₂ : Cr) : L) * (a + b) = (d₂ : L) * ((d₁ : L) * a) + (d₁ : L) * ((d₂ : L) * b) := by
        push_cast
        ring
      rw [this]
      exact Cr.add_mem (Cr.mul_mem d₂.2 e₁) (Cr.mul_mem d₁.2 e₂)
    · rintro a - ⟨d, h, e⟩
      exact ⟨d, h, by rw [mul_neg]; exact Cr.neg_mem e⟩
    · rintro a b - - ⟨d₁, h₁, e₁⟩ ⟨d₂, h₂, e₂⟩
      refine ⟨d₁ * d₂, fun h => (h𝔮p.mem_or_mem h).elim h₁ h₂, ?_⟩
      have : ((d₁ * d₂ : Cr) : L) * (a * b) = ((d₁ : L) * a) * ((d₂ : L) * b) := by
        push_cast
        ring
      rw [this]
      exact Cr.mul_mem e₁ e₂
  obtain ⟨d, hd, hdf⟩ := key f hfQ
  exact hd (h𝔇𝔮 hdf)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
