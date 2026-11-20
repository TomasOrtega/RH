import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultisetStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ElementarySymmetricInverse
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace UpperTheory.Cb.SphericalHeckeOperators₂

section Conv

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

private def Rq (q : ℕ) (hq : q ≠ 0) : Subring ℂ where
  carrier := {x | ∃ (m : ℤ) (e : ℕ), x = (m : ℂ) / (q : ℂ) ^ e}
  mul_mem' := by
    rintro _ _ ⟨m, e, rfl⟩ ⟨m', e', rfl⟩
    exact ⟨m * m', e + e', by push_cast; rw [pow_add]; field_simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    have h0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    rintro _ _ ⟨m, e, rfl⟩ ⟨m', e', rfl⟩
    exact ⟨m * (q : ℤ) ^ e' + m' * (q : ℤ) ^ e, e + e', by push_cast; rw [pow_add]; field_simp⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, e, rfl⟩
    exact ⟨-m, e, by push_cast; ring⟩

private def cv (A B : G →₀ ℂ) : G →₀ ℂ :=
  A.sum fun g c => B.sum fun h d => Finsupp.single (g * h) (c * d)

/- English proof (translation)
Simplify using `only [cv, Finsupp.sum, Finsupp.finset_sum_apply]`. Use `R.sum_mem fun g _ => R.sum_mem fun h _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `R.mul_mem (hA g) (hB h)`.

Conclude with `R.zero_mem`.
-/
private theorem cv_mem (R : Subring ℂ) {A B : G →₀ ℂ} (hA : ∀ g, A g ∈ R) (hB : ∀ g, B g ∈ R) (x : G) :
    cv A B x ∈ R := by
  classical
  simp only [cv, Finsupp.sum, Finsupp.finset_sum_apply]
  refine R.sum_mem fun g _ => R.sum_mem fun h _ => ?_
  rw [Finsupp.single_apply]
  split_ifs
  · exact R.mul_mem (hA g) (hB h)
  · exact R.zero_mem

/- English proof (translation)
The claim follows from `(Finsupp.linearCombination_apply ℂ f).symm`.
-/
private theorem opOf_eq (ρ : Representation ℂ G V) (f : G →₀ ℂ) (v : V) :
    opOf ρ f v = Finsupp.linearCombination ℂ (fun g => ρ g v) f :=
  (Finsupp.linearCombination_apply ℂ f).symm

/- English proof (translation)
Simplify using `only [opOf_eq, map_add]`.
-/
private theorem opOf_add (ρ : Representation ℂ G V) (A B : G →₀ ℂ) (v : V) :
    opOf ρ (A + B) v = opOf ρ A v + opOf ρ B v := by
  simp only [opOf_eq, map_add]

/- English proof (translation)
Simplify using `only [opOf_eq, map_smul]`.
-/
private theorem opOf_smul (ρ : Representation ℂ G V) (c : ℂ) (A : G →₀ ℂ) (v : V) :
    opOf ρ (c • A) v = c • opOf ρ A v := by
  simp only [opOf_eq, map_smul]

/- English proof (translation)
Simplify using `only [opOf_eq, Finsupp.linearCombination_single]`.
-/
private theorem opOf_single (ρ : Representation ℂ G V) (g : G) (c : ℂ) (v : V) :
    opOf ρ (Finsupp.single g c) v = c • ρ g v := by
  simp only [opOf_eq, Finsupp.linearCombination_single]

/- English proof (translation)
Simplify using `only [opOf, Finsupp.sum, Finset.smul_sum, map_smul]`. Conclude with `Finset.sum_congr rfl fun g _ => smul_comm _ _ _`.
-/
private theorem opOf_vsmul (ρ : Representation ℂ G V) (A : G →₀ ℂ) (c : ℂ) (v : V) :
    opOf ρ A (c • v) = c • opOf ρ A v := by
  simp only [opOf, Finsupp.sum, Finset.smul_sum, map_smul]
  exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _

/- English proof (translation)
Simplify using `[opOf]`.
-/
private theorem opOf_zero (ρ : Representation ℂ G V) (A : G →₀ ℂ) : opOf ρ A (0 : V) = 0 := by
  simp [opOf]

/- English proof (translation)
Rewrite using `[opOf_eq, cv]`. Simplify using `only [Finsupp.sum, map_sum, Finsupp.linearCombination_single]`. Simplify using `only [opOf, Finsupp.sum, map_sum, Finset.smul_sum, map_smul, map_mul, Module.End.mul_apply, mul_smul]`.
-/
private theorem opOf_cv (ρ : Representation ℂ G V) (A B : G →₀ ℂ) (v : V) :
    opOf ρ (cv A B) v = opOf ρ A (opOf ρ B v) := by
  rw [opOf_eq, cv]
  simp only [Finsupp.sum, map_sum, Finsupp.linearCombination_single]
  simp only [opOf, Finsupp.sum, map_sum, Finset.smul_sum, map_smul, map_mul, Module.End.mul_apply, mul_smul]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C n`. Use `⟨Finsupp.single 1 (n : ℂ), fun g => ?_, fun V _ _ ρ v z _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply] split_ifs`. Conclude with `intCast_mem R n`.

Conclude with `R.zero_mem`. Rewrite using `[opOf_single]`. Simplify using the standard rewrite rules. Consider the case `add p r hp hr`. Take `⟨F₁, a₁, b₁⟩` from `hp`.

Take `⟨F₂, a₂, b₂⟩` from `hr`. Use `⟨F₁ + F₂, fun g => R.add_mem (a₁ g) (a₂ g), fun V _ _ ρ v z h => ?_⟩` and prove the remaining obligations. Rewrite using `[opOf_add, b₁ V ρ v z h, b₂ V ρ v z h, map_add, add_smul]`. Consider the case `mul_X p i hp`. Take `⟨F, a, b⟩` from `hp`.

Use `⟨cv F (f i), cv_mem R a (hf i), fun V _ _ ρ v z h => ?_⟩` and prove the remaining obligations. Rewrite using `[opOf_cv, h i, opOf_vsmul, b V ρ v z h, map_mul, MvPolynomial.aeval_X, smul_smul, mul_comm]`.
-/
private theorem poly_op (R : Subring ℂ) {I : Type} (f : I → G →₀ ℂ) (hf : ∀ i g, f i g ∈ R) (P : MvPolynomial I ℤ) :
    ∃ F : G →₀ ℂ, (∀ g, F g ∈ R) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V)
      (z : I → ℂ), (∀ i, opOf ρ (f i) v = z i • v) → opOf ρ F v = MvPolynomial.aeval z P • v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C n =>
    refine ⟨Finsupp.single 1 (n : ℂ), fun g => ?_, fun V _ _ ρ v z _ => ?_⟩
    · rw [Finsupp.single_apply]
      split_ifs
      · exact intCast_mem R n
      · exact R.zero_mem
    · rw [opOf_single]
      simp
  | add p r hp hr =>
    obtain ⟨F₁, a₁, b₁⟩ := hp
    obtain ⟨F₂, a₂, b₂⟩ := hr
    refine ⟨F₁ + F₂, fun g => R.add_mem (a₁ g) (a₂ g), fun V _ _ ρ v z h => ?_⟩
    rw [opOf_add, b₁ V ρ v z h, b₂ V ρ v z h, map_add, add_smul]
  | mul_X p i hp =>
    obtain ⟨F, a, b⟩ := hp
    refine ⟨cv F (f i), cv_mem R a (hf i), fun V _ _ ρ v z h => ?_⟩
    rw [opOf_cv, h i, opOf_vsmul, b V ρ v z h, map_mul, MvPolynomial.aeval_X, smul_smul, mul_comm]

/- English proof (translation)
Take `⟨P, hP⟩` from `GlobalTheory.T.exists_intPoly_esymm_eq_powerSum_multiset a n hn`. Take `⟨F, h1, h2⟩` from `poly_op R t ht P`. Use `⟨F, h1, fun V _ _ ρ v s hs h => ?_⟩` and prove the remaining obligations. Rewrite using `[h2 V ρ v (fun j => s.esymm j) h, hP s hs]`.
-/
private theorem pow_op (R : Subring ℂ) (a n : ℕ) (hn : 1 ≤ n) (t : Fin (a + 1) → G →₀ ℂ) (ht : ∀ j g, t j g ∈ R) :
    ∃ F : G →₀ ℂ, (∀ g, F g ∈ R) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V)
      (s : Multiset ℂ), Multiset.card s = a → (∀ j : Fin (a + 1), opOf ρ (t j) v = s.esymm j • v) →
      opOf ρ F v = (s.map (· ^ n)).sum • v := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_intPoly_esymm_eq_powerSum_multiset a n hn
  obtain ⟨F, h1, h2⟩ := poly_op R t ht P
  refine ⟨F, h1, fun V _ _ ρ v s hs h => ?_⟩
  rw [h2 V ρ v (fun j => s.esymm j) h, hP s hs]

end Conv

section Sym

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Function.comp_def, Multiset.sum_map_mul_left]`.
-/
private theorem esymm_cons (x : ℂ) (s : Multiset ℂ) (j : ℕ) :
    (x ::ₘ s).esymm (j + 1) = s.esymm (j + 1) + x * s.esymm j := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Function.comp_def, Multiset.sum_map_mul_left]

/- English proof (translation)
Simplify using `[Multiset.esymm]`.
-/
private theorem esymm_zero (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ h]`.
-/
private theorem esymm_of_lt {s : Multiset ℂ} {j : ℕ} (h : Multiset.card s < j) : s.esymm j = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ h]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty`. Introduce `j`. Consider the cases of `j with`. Consider the case `zero => simp [esymm_zero]`.

Consider the case `succ j`. Establish `e : (0 : Multiset ℂ).esymm (j + 1) = 0` using `esymm_of_lt (by simp)`. Simplify using `[e]`. Consider the case `cons x s ih`. Introduce `j`.

Consider the cases of `j with`. Consider the case `zero => simp [esymm_zero]`. Consider the case `succ j`. Rewrite using `[Multiset.map_cons, esymm_cons, ih, ih, esymm_cons]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem esymm_scale (c : ℂ) (s : Multiset ℂ) : ∀ j, (s.map (c * ·)).esymm j = c ^ j * s.esymm j := by
  induction s using Multiset.induction_on with
  | empty =>
    intro j
    cases j with
    | zero => simp [esymm_zero]
    | succ j =>
      have e : (0 : Multiset ℂ).esymm (j + 1) = 0 := esymm_of_lt (by simp)
      simp [e]
  | cons x s ih =>
    intro j
    cases j with
    | zero => simp [esymm_zero]
    | succ j =>
      rw [Multiset.map_cons, esymm_cons, ih, ih, esymm_cons]
      ring

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.EsymmMapInvMulProd.esymm_inv s h`.
-/
private theorem esymm_inv (s : Multiset ℂ) (h : ∀ x ∈ s, x ≠ 0) :
    ∀ j ≤ Multiset.card s, (s.map (·⁻¹)).esymm j * s.prod = s.esymm (Multiset.card s - j) :=
  _root_.UpperTheory.Reformulated.B.EsymmMapInvMulProd.esymm_inv s h

end Sym

section Local

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)

/- English proof (translation)
Simplify using `[normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
private theorem normV_eq : normV w = Formalism.UG.qV E w := by
  simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Establish `hm` using `GlobalTheory.LFun.Tj_mem_hecke (n := a) hϖ j`. Establish `hfin` using `Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w a) hm.2`. Establish `hR : ∀ g, Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j g ∈ R` using `fun g => by`. Simplify using `only [Formalism.UG.Tj, Set.indicator_apply]`. Use `split_ifs`.

Conclude with `R.one_mem`. Conclude with `R.zero_mem`. Use `⟨∑ c ∈ hfin.toFinset, Finsupp.single c.out (Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j c.out), fun g => ?_, fun V _ _ ρ x => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.finset_sum_apply]`. Use `R.sum_mem fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `hR _`. Conclude with `R.zero_mem`. Rewrite using `[opOf_eq, map_sum, GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]`.

Simplify using `only [Finsupp.linearCombination_single]`. Introduce `c hc`. Simplify using `only [Function.mem_support] at hc`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Conclude with `fun h0 => hc (by simp [h0])`.
-/
private theorem exists_Tj_op (R : Subring ℂ) {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ f : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, f g ∈ R) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (x : V),
        opOf ρ f x = GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w a) (Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j) x := by
  classical
  have hm := GlobalTheory.LFun.Tj_mem_hecke (n := a) hϖ j
  have hfin := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w a) hm.2
  have hR : ∀ g, Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j g ∈ R := fun g => by
    simp only [Formalism.UG.Tj, Set.indicator_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  refine ⟨∑ c ∈ hfin.toFinset, Finsupp.single c.out (Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j c.out), fun g => ?_,
    fun V _ _ ρ x => ?_⟩
  · rw [Finsupp.finset_sum_apply]
    refine R.sum_mem fun c _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact hR _
    · exact R.zero_mem
  · rw [opOf_eq, map_sum, GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · simp only [Finsupp.linearCombination_single]
    · intro c hc
      simp only [Function.mem_support] at hc
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      exact fun h0 => hc (by simp [h0])

/- English proof (translation)
Establish `hD : Formalism.UG.diagJ a ϖ a = (c : Matrix (Fin a) (Fin a) (w.adicCompletion E))`. Rewrite using `[hc]`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[Formalism.UG.diagJ]`. Simplify using `[Formalism.UG.diagJ, Matrix.diagonal_apply, Matrix.one_apply, h]`. Establish `hiff : ∀ g : GL (Fin a) (w.adicCompletion E), (∃ x ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov E w), ∃ y ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov E w), (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) * Formalism.UG.diag …`. Introduce `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx', y, hy, e⟩`. Establish `hg : g = c * (x * y)` using `Units.ext (by`. Rewrite using `[Units.val_mul, Units.val_mul, e, hD, hc]`. Simplify using `[Matrix.smul_mul, Matrix.mul_smul])`. Rewrite using `[hg, inv_mul_cancel_left]`.

Conclude with `(GlobalTheory.LFun.KGL w a).mul_mem hx' hy`. Introduce `hk`. Take `⟨k, rfl⟩ : ∃ k, g = c * k` from `⟨c⁻¹ * g, by group⟩`. Rewrite `hk` using `[inv_mul_cancel_left]`. Use `⟨k, hk, 1, one_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, hD, hc]`. Simplify using `[Matrix.smul_mul, Matrix.mul_smul]`. Establish `key : ∀ g, Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ a g = if c⁻¹ * g ∈ GlobalTheory.LFun.KGL w a then 1 else 0`. Introduce `g`. Simplify using `only [Formalism.UG.Tj, Set.indicator_apply, Set.mem_setOf_eq, hiff g]`.

Distinguish the cases in `h : c⁻¹ * g ∈ GlobalTheory.LFun.KGL w a`. Simplify using `[h]`. Simplify using `[h]`. Rewrite using `[GlobalTheory.LFun.heckeVec, finsum_eq_single _ (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a)]`. Establish `hk : c⁻¹ * (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out ∈ GlobalTheory.LFun.KGL w a` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm`.

Rewrite using `[key, if_pos hk, one_smul]`. Establish `e : (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out = c * (c⁻¹ * (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out)` using `by group`. Combine the equalities or inequalities in the displayed calculation. Introduce `C hC`. Rewrite using `[key, if_neg, zero_smul]`.

Introduce `hk`. Conclude with `hC ((QuotientGroup.out_eq' C).symm.trans (QuotientGroup.eq.2 hk).symm)`.
-/
private theorem heckeVec_Ta {ϖ : w.adicCompletion E} {c : GL (Fin a) (w.adicCompletion E)}
    (hc : (c : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = ϖ • 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) {x : V}
    (hx : x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w a)) :
    GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w a) (Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ a) x = ρ c x := by
  classical
  have hD : Formalism.UG.diagJ a ϖ a = (c : Matrix (Fin a) (Fin a) (w.adicCompletion E)) := by
    rw [hc]
    ext i j
    by_cases h : i = j
    · subst h
      simp [Formalism.UG.diagJ]
    · simp [Formalism.UG.diagJ, Matrix.diagonal_apply, Matrix.one_apply, h]
  have hiff : ∀ g : GL (Fin a) (w.adicCompletion E),
      (∃ x ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov E w), ∃ y ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov E w),
        (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
          (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) * Formalism.UG.diagJ a ϖ a *
            (y : Matrix (Fin a) (Fin a) (w.adicCompletion E))) ↔ c⁻¹ * g ∈ GlobalTheory.LFun.KGL w a := by
    intro g
    constructor
    · rintro ⟨x, hx', y, hy, e⟩
      have hg : g = c * (x * y) := Units.ext (by
        rw [Units.val_mul, Units.val_mul, e, hD, hc]
        simp [Matrix.smul_mul, Matrix.mul_smul])
      rw [hg, inv_mul_cancel_left]
      exact (GlobalTheory.LFun.KGL w a).mul_mem hx' hy
    · intro hk
      obtain ⟨k, rfl⟩ : ∃ k, g = c * k := ⟨c⁻¹ * g, by group⟩
      rw [inv_mul_cancel_left] at hk
      refine ⟨k, hk, 1, one_mem _, ?_⟩
      rw [Units.val_mul, hD, hc]
      simp [Matrix.smul_mul, Matrix.mul_smul]
  have key : ∀ g, Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ a g = if c⁻¹ * g ∈ GlobalTheory.LFun.KGL w a then 1 else 0 := by
    intro g
    simp only [Formalism.UG.Tj, Set.indicator_apply, Set.mem_setOf_eq, hiff g]
    by_cases h : c⁻¹ * g ∈ GlobalTheory.LFun.KGL w a
    · simp [h]
    · simp [h]
  rw [GlobalTheory.LFun.heckeVec, finsum_eq_single _ (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a)]
  · have hk : c⁻¹ * (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out ∈ GlobalTheory.LFun.KGL w a :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
    rw [key, if_pos hk, one_smul]
    have e : (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out =
        c * (c⁻¹ * (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out) := by group
    calc ρ (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out x
        = ρ (c * (c⁻¹ * (c : GL (Fin a) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w a).out)) x := by rw [← e]
      _ = ρ c x := by rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx _ hk]
  · intro C hC
    rw [key, if_neg, zero_smul]
    intro hk
    exact hC ((QuotientGroup.out_eq' C).symm.trans (QuotientGroup.eq.2 hk).symm)

/- English proof (translation)
Simplify using `[UpperTheory.V.Af.algSat, Multiset.map_map, Function.comp_def]`.
-/
private theorem algSat_eq (q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat a q B = (B.map fun b : ℂˣ => (b : ℂ)).map ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * ·) := by
  simp [UpperTheory.V.Af.algSat, Multiset.map_map, Function.comp_def]

/- English proof (translation)
Establish `hp : (0 : ℝ) < q` using `by exact_mod_cast Nat.pos_of_ne_zero hq`. Establish `e1 : (((j : ℂ) * ((a : ℂ) - j)) / 2) = (((j : ℝ) * ((a : ℝ) - j) / 2 : ℝ) : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (q : ℂ) ^ (((j : ℝ) * ((a : ℝ) - j) / 2 : ℝ) : ℂ) = (((q : ℝ) ^ ((j : ℝ) * ((a : ℝ) - j) / 2) : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_cpow hp.le]`. Simplify using the standard rewrite rules. Establish `e3 : ((q : ℝ) ^ (((a : ℝ) - 1) / 2)) ^ j = (q : ℝ) ^ j.choose 2 * (q : ℝ) ^ ((j : ℝ) * ((a : ℝ) - j) / 2)`. Rewrite using `[← Real.rpow_natCast _ j, ← Real.rpow_natCast (q : ℝ) (j.choose 2), ← Real.rpow_mul hp.le, ← Real.rpow_add hp, Nat.cast_choose_two ℝ j]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Conclude with `congrArg (fun r : ℝ => (r : ℂ)) e3` after adjusting the coercions.
-/
private theorem cR_pow {q a j : ℕ} (hq : q ≠ 0) :
    ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j =
      (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (((j : ℂ) * ((a : ℂ) - j)) / 2) := by
  have hp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have e1 : (((j : ℂ) * ((a : ℂ) - j)) / 2) = (((j : ℝ) * ((a : ℝ) - j) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : (q : ℂ) ^ (((j : ℝ) * ((a : ℝ) - j) / 2 : ℝ) : ℂ) =
      (((q : ℝ) ^ ((j : ℝ) * ((a : ℝ) - j) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hp.le]
    simp
  have e3 : ((q : ℝ) ^ (((a : ℝ) - 1) / 2)) ^ j =
      (q : ℝ) ^ j.choose 2 * (q : ℝ) ^ ((j : ℝ) * ((a : ℝ) - j) / 2) := by
    rw [← Real.rpow_natCast _ j, ← Real.rpow_natCast (q : ℝ) (j.choose 2), ← Real.rpow_mul hp.le, ← Real.rpow_add hp,
      Nat.cast_choose_two ℝ j]
    congr 1
    ring
  rw [e1, e2]
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) e3

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `GlobalTheory.LFun.exists_isUnifV w`. Establish `h0 : ϖ ≠ 0` using `fun h => by simp [Formalism.UG.IsUnifV, h] at hϖ`. Establish `hq : normV w ≠ 0` using `normV_eq w ▸ GlobalTheory.LFun.qV_ne_zero w`. Establish `hqC : ((normV w : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hq`. Use `choose f hfR hf using fun j : ℕ => exists_Tj_op w a R hϖ j`.

Set `c : GL (Fin a) (w.adicCompletion E)` to `Units.map (Matrix.scalar (Fin a)).toMonoidHom (Units.mk0 ϖ h0)`. Establish `hc : (c : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = ϖ • 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[c]`. Simplify using `[c, Matrix.one_apply, h]`. Use `⟨fun j => (((normV w : ℕ) : ℂ) ^ ((j : ℕ).choose 2)) • f j, c, fun j g => ?_, fun σ B hB v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.smul_apply, smul_eq_mul]`. Conclude with `R.mul_mem (R.pow_mem (natCast_mem R _) _) (hfR j g)`.

Establish `key : ∀ j ≤ a, GlobalTheory.LFun.heckeVec σ.ρ (GlobalTheory.LFun.KGL w a) (Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j) v = GlobalTheory.LFun.satEig (normV w) a B j • v`. Introduce `j hj`. Distinguish the cases in `hv0 : v = 0`. Substitute `hv0` using the available equality. Rewrite using `[← hf j, opOf_zero, smul_zero]`.

Use `(hB.2 v hv hv0).2.2.2 ϖ hϖ j hj` as an intermediate fact. Rewrite `this` using `[← normV_eq w]`. Then use the resulting hypothesis. Establish `es : ∀ j, (UpperTheory.V.Af.algSat a (normV w) B).esymm j = ((normV w : ℕ) : ℂ) ^ (j.choose 2) * GlobalTheory.LFun.satEig (normV w) a B j`. Introduce `j`. Rewrite using `[algSat_eq, esymm_scale, cR_pow hq, GlobalTheory.LFun.satEig, mul_assoc]`.

Use `⟨fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[opOf_smul, hf, key j (Nat.lt_succ_iff.1 j.2), smul_smul, es]`. Rewrite using `[← heckeVec_Ta w a hc σ.ρ hv, key a le_rfl, es, inv_mul_cancel_left₀ (pow_ne_zero _ hqC)]`.
-/
private theorem sat_ops (R : Subring ℂ) :
    ∃ (u : Fin (a + 1) → GL (Fin a) (w.adicCompletion E) →₀ ℂ) (c : GL (Fin a) (w.adicCompletion E)),
      (∀ j g, u j g ∈ R) ∧
      ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
        ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a),
          (∀ j : Fin (a + 1), opOf σ.ρ (u j) v = (UpperTheory.V.Af.algSat a (normV w) B).esymm j • v) ∧
          σ.ρ c v = ((((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ * (UpperTheory.V.Af.algSat a (normV w) B).esymm a) • v := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have h0 : ϖ ≠ 0 := fun h => by simp [Formalism.UG.IsUnifV, h] at hϖ
  have hq : normV w ≠ 0 := normV_eq w ▸ GlobalTheory.LFun.qV_ne_zero w
  have hqC : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq
  choose f hfR hf using fun j : ℕ => exists_Tj_op w a R hϖ j
  let c : GL (Fin a) (w.adicCompletion E) := Units.map (Matrix.scalar (Fin a)).toMonoidHom (Units.mk0 ϖ h0)
  have hc : (c : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = ϖ • 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [c]
    · simp [c, Matrix.one_apply, h]
  refine ⟨fun j => (((normV w : ℕ) : ℂ) ^ ((j : ℕ).choose 2)) • f j, c, fun j g => ?_, fun σ B hB v hv => ?_⟩
  · rw [Finsupp.smul_apply, smul_eq_mul]
    exact R.mul_mem (R.pow_mem (natCast_mem R _) _) (hfR j g)
  have key : ∀ j ≤ a, GlobalTheory.LFun.heckeVec σ.ρ (GlobalTheory.LFun.KGL w a) (Formalism.UG.Tj ℂ a (Formalism.UG.Ov E w) ϖ j) v =
      GlobalTheory.LFun.satEig (normV w) a B j • v := by
    intro j hj
    by_cases hv0 : v = 0
    · subst hv0
      rw [← hf j, opOf_zero, smul_zero]
    · have := (hB.2 v hv hv0).2.2.2 ϖ hϖ j hj
      rwa [← normV_eq w] at this
  have es : ∀ j, (UpperTheory.V.Af.algSat a (normV w) B).esymm j =
      ((normV w : ℕ) : ℂ) ^ (j.choose 2) * GlobalTheory.LFun.satEig (normV w) a B j := by
    intro j
    rw [algSat_eq, esymm_scale, cR_pow hq, GlobalTheory.LFun.satEig, mul_assoc]
  refine ⟨fun j => ?_, ?_⟩
  · rw [opOf_smul, hf, key j (Nat.lt_succ_iff.1 j.2), smul_smul, es]
  · rw [← heckeVec_Ta w a hc σ.ρ hv, key a le_rfl, es, inv_mul_cancel_left₀ (pow_ne_zero _ hqC)]

end Local

end UpperTheory.Cb.SphericalHeckeOperators₂

end

open UpperTheory.Cb.SphericalHeckeOperators₂

/- English proof (translation)
Introduce `E _ _ w a`. Use `⟨fun σ h => GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred h, fun n => ?_⟩` and prove the remaining obligations. Establish `hq : normV w ≠ 0` using `normV_eq w ▸ GlobalTheory.LFun.qV_ne_zero w`. Establish `hqC : ((normV w : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hq`. Take `⟨u, c, hu, hS⟩` from `sat_ops w a (Rq (normV w) hq)`.

Establish `hcard : ∀ B : Multiset ℂˣ, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.LFun.HasSatGL w σ.ρ B → Multiset.card (UpperTheory.V.Af.algSat a (normV w) B) = a` using `fun B σ hB => by`. Simplify `hB.card` using `[UpperTheory.V.Af.algSat]`. Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ)` from `⟨n.natAbs, by omega⟩`. Establish `hm : 1 ≤ m` using `by omega`.

Establish `hQ : ((normV w : ℕ) : ℂ) ^ a.choose 2 ≠ 0` using `pow_ne_zero _ hqC`. Establish `hQR : (((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ ∈ Rq (normV w) hq` using `⟨1, a.choose 2, by simp⟩`. Take `⟨F, h1, h2⟩` from `pow_op (Rq (normV w) hq) a m hm (fun j => (((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ • cv (u (Fin.rev j)) (Finsupp.single c⁻¹ 1)) (fun j g => by`. Rewrite using `[Finsupp.smul_apply, smul_eq_mul]`. Use `(Rq (normV w) hq).mul_mem hQR (cv_mem _ (hu _) (fun x => ?_) g)` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `(Rq (normV w) hq).one_mem`. Conclude with `(Rq (normV w) hq).zero_mem)`. Use `⟨F, h1, fun σ B hB v hv => ?_⟩` and prove the remaining obligations.

Take `⟨he, hc⟩` from `hS σ B hB v hv`. Use `set s := UpperTheory.V.Af.algSat a (normV w) B with hs`. Establish `hsc : Multiset.card s = a` using `hcard B σ hB`. Establish `hnz : ∀ x ∈ s, x ≠ 0`. Introduce `x hx`.

Rewrite `hx` using `[hs, algSat_eq, Multiset.map_map]`. Take `⟨α, -, rfl⟩` from `Multiset.mem_map.1 hx`. Use `mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne') α.ne_zero` and prove the remaining obligations. Conclude with `Nat.pos_of_ne_zero hq` after adjusting the coercions. Establish `hprod : s.prod = s.esymm a`.

Use `esymm_inv s hnz 0 (Nat.zero_le _)` as an intermediate fact. Rewrite `this` using `[esymm_zero, one_mul, Nat.sub_zero, hsc]`. Then use the resulting hypothesis. Establish `hZ : s.esymm a ≠ 0` using `hprod ▸ Multiset.prod_ne_zero fun h0 => hnz 0 h0 rfl`. Establish `hinv : σ.ρ c⁻¹ v = (((normV w : ℕ) : ℂ) ^ a.choose 2 * (s.esymm a)⁻¹) • v`. Establish `e : σ.ρ c⁻¹ (σ.ρ c v) = v`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite `e` using `[hc, map_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul]`. Establish `: ((normV w : ℕ) : ℂ) ^ a.choose 2 * (s.esymm a)⁻¹ * ((((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ * s.esymm a) = 1`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this, one_smul]`. Use `_ = _ := by rw [e]`. Establish `hres` using `h2 σ.V σ.ρ v (s.map (·⁻¹)) (by simpa using hsc) (fun j => ?_)`. Rewrite using `[hres, Multiset.map_map]`.

Use `congr 2`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[zpow_neg]`. Establish `hj : (j : ℕ) ≤ Multiset.card s`. Rewrite using `[hsc]`.

Conclude with `Nat.lt_succ_iff.1 j.2`. Establish `e` using `esymm_inv s hnz j hj`. Establish `hrev : ((Fin.rev j : Fin (a + 1)) : ℕ) = Multiset.card s - j`. Rewrite using `[Fin.val_rev, hsc]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[opOf_smul, opOf_cv, opOf_single, one_smul, hinv, opOf_vsmul, he, hrev, ← e, hprod, smul_smul, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `⟨Finsupp.single 1 (a : ℂ), fun g => ?_, fun σ B hB v _ => ?_⟩` and prove the remaining obligations. Establish `: (Finsupp.single (1 : GL (Fin a) (w.adicCompletion E)) (a : ℂ)) g ∈ Rq (normV w) hq`.

Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `natCast_mem _ a`. Conclude with `(Rq (normV w) hq).zero_mem`. Conclude with `this`.

Rewrite using `[opOf_single, map_one, Module.End.one_apply]`. Use `hcard B σ hB` as an intermediate fact. Simplify using `[this]`. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ)` from `⟨n.natAbs, by omega⟩`. Establish `hm : 1 ≤ m` using `by omega`.

Take `⟨F, h1, h2⟩` from `pow_op (Rq (normV w) hq) a m hm u hu`. Use `⟨F, h1, fun σ B hB v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[h2 σ.V σ.ρ v _ (hcard B σ hB) (hS σ B hB v hv).1]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Cb.spherical_operators_exist :
    SphOps := by
  classical
  intro E _ _ w a
  refine ⟨fun σ h => GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred h, fun n => ?_⟩
  have hq : normV w ≠ 0 := normV_eq w ▸ GlobalTheory.LFun.qV_ne_zero w
  have hqC : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq
  obtain ⟨u, c, hu, hS⟩ := sat_ops w a (Rq (normV w) hq)
  have hcard : ∀ B : Multiset ℂˣ, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      Multiset.card (UpperTheory.V.Af.algSat a (normV w) B) = a := fun B σ hB => by
    simpa [UpperTheory.V.Af.algSat] using hB.card
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
    have hm : 1 ≤ m := by omega
    have hQ : ((normV w : ℕ) : ℂ) ^ a.choose 2 ≠ 0 := pow_ne_zero _ hqC
    have hQR : (((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ ∈ Rq (normV w) hq := ⟨1, a.choose 2, by simp⟩
    obtain ⟨F, h1, h2⟩ := pow_op (Rq (normV w) hq) a m hm
      (fun j => (((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ • cv (u (Fin.rev j)) (Finsupp.single c⁻¹ 1))
      (fun j g => by
        rw [Finsupp.smul_apply, smul_eq_mul]
        refine (Rq (normV w) hq).mul_mem hQR (cv_mem _ (hu _) (fun x => ?_) g)
        rw [Finsupp.single_apply]
        split_ifs
        · exact (Rq (normV w) hq).one_mem
        · exact (Rq (normV w) hq).zero_mem)
    refine ⟨F, h1, fun σ B hB v hv => ?_⟩
    obtain ⟨he, hc⟩ := hS σ B hB v hv
    set s := UpperTheory.V.Af.algSat a (normV w) B with hs
    have hsc : Multiset.card s = a := hcard B σ hB
    have hnz : ∀ x ∈ s, x ≠ 0 := by
      intro x hx
      rw [hs, algSat_eq, Multiset.map_map] at hx
      obtain ⟨α, -, rfl⟩ := Multiset.mem_map.1 hx
      refine mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne') α.ne_zero
      exact_mod_cast Nat.pos_of_ne_zero hq
    have hprod : s.prod = s.esymm a := by
      have := esymm_inv s hnz 0 (Nat.zero_le _)
      rwa [esymm_zero, one_mul, Nat.sub_zero, hsc] at this
    have hZ : s.esymm a ≠ 0 := hprod ▸ Multiset.prod_ne_zero fun h0 => hnz 0 h0 rfl
    have hinv : σ.ρ c⁻¹ v = (((normV w : ℕ) : ℂ) ^ a.choose 2 * (s.esymm a)⁻¹) • v := by
      have e : σ.ρ c⁻¹ (σ.ρ c v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [hc, map_smul] at e
      calc σ.ρ c⁻¹ v = (((normV w : ℕ) : ℂ) ^ a.choose 2 * (s.esymm a)⁻¹) •
            ((((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ * s.esymm a) • σ.ρ c⁻¹ v := by
            rw [smul_smul]
            have : ((normV w : ℕ) : ℂ) ^ a.choose 2 * (s.esymm a)⁻¹ *
                ((((normV w : ℕ) : ℂ) ^ a.choose 2)⁻¹ * s.esymm a) = 1 := by
              field_simp
            rw [this, one_smul]
        _ = _ := by rw [e]
    have hres := h2 σ.V σ.ρ v (s.map (·⁻¹)) (by simpa using hsc) (fun j => ?_)
    · rw [hres, Multiset.map_map]
      congr 2
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [zpow_neg]
    · have hj : (j : ℕ) ≤ Multiset.card s := by
        rw [hsc]
        exact Nat.lt_succ_iff.1 j.2
      have e := esymm_inv s hnz j hj
      have hrev : ((Fin.rev j : Fin (a + 1)) : ℕ) = Multiset.card s - j := by
        rw [Fin.val_rev, hsc]
        omega
      rw [opOf_smul, opOf_cv, opOf_single, one_smul, hinv, opOf_vsmul, he, hrev, ← e, hprod, smul_smul, smul_smul]
      congr 1
      field_simp
  · refine ⟨Finsupp.single 1 (a : ℂ), fun g => ?_, fun σ B hB v _ => ?_⟩
    · have : (Finsupp.single (1 : GL (Fin a) (w.adicCompletion E)) (a : ℂ)) g ∈ Rq (normV w) hq := by
        rw [Finsupp.single_apply]
        split_ifs
        · exact natCast_mem _ a
        · exact (Rq (normV w) hq).zero_mem
      exact this
    · rw [opOf_single, map_one, Module.End.one_apply]
      have := hcard B σ hB
      simp [this]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.natAbs, by omega⟩
    have hm : 1 ≤ m := by omega
    obtain ⟨F, h1, h2⟩ := pow_op (Rq (normV w) hq) a m hm u hu
    refine ⟨F, h1, fun σ B hB v hv => ?_⟩
    rw [h2 σ.V σ.ρ v _ (hcard B σ hB) (hS σ B hB v hv).1]
    simp
