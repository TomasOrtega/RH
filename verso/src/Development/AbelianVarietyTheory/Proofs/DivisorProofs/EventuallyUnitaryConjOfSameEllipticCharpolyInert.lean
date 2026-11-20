import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.UnitInert

section Local

variable {O : Type} [CommRing O] [IsNoetherianRing O] {r : ℕ}

/- English proof (translation)
Establish `hjac` using `IsAdicComplete.le_jacobson_bot I`. Take `⟨v, hv⟩` from `GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := g) hs`. Take `⟨w, hw⟩` from `GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := h) (show h.charpoly.Separable by rwa [e])`. Take `⟨a, ha⟩` from `(isUnit_iff_isUnit_det _).2 hv`. Take `⟨b, hb⟩` from `(isUnit_iff_isUnit_det _).2 hw`.

Establish `hy : g * (a * b⁻¹ : GL (Fin r) O) = (a * b⁻¹ : GL (Fin r) O) * h`. Establish `h1` using `GlobalTheory.Orb.mul_krylov_eq g v`. Establish `h2` using `GlobalTheory.Orb.mul_krylov_eq h w`. Rewrite `h1` using `[← ha]`. Rewrite `h2` using `[← hb, e]`.

Rewrite using `[Units.val_mul, ← mul_assoc, h1, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h2, Units.inv_mul_cancel_left]`. Generalize the expression as in `a * b⁻¹ = y at hy`. Use `set s : Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) O := cT σ with hsdef`. Establish `hm : ∀ a b, s (a * b) = s b * s a` using `fun a b => cT_mul σ a b`. Establish `hadd : ∀ a b, s (a + b) = s a + s b` using `fun a b => Matrix.ext fun i j => by simp [s, cT]`.

Establish `hss : ∀ a, s (s a) = a` using `fun a => Matrix.ext fun i j => by simp [s, cT, hσ]`. Establish `hsc : ∀ c : O, s (algebraMap O _ c) = algebraMap O _ (σ c)` using `fun c => by`. Use extensionality with `i j`. Simplify using `only [s, cT, transpose_apply, map_apply, algebraMap_matrix_apply, eq_comm (a := j)]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h1 : s 1 = 1` using `by simpa using hsc 1`. Express the relevant statement in the definitionally equal form `s g * g = 1 at hg`. Express the relevant statement in the definitionally equal form `s h * h = 1 at hh`. Set `C` to `Subalgebra.centralizer O ({h} : Set (Matrix (Fin r) (Fin r) O))`. Establish `hC : ∀ {a}, a ∈ C ↔ a * h = h * a` using `by simp [C, Subalgebra.mem_centralizer_iff, eq_comm]`.

Set `_ : CommRing C` to `{ (inferInstance : Ring C) with mul_comm := fun a b => Subtype.ext (by`. Take `⟨p, hp⟩` from `GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 a.2)`. Take `⟨q, hq⟩` from `GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 b.2)`. Rewrite using `[C.coe_mul, C.coe_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]) }`. Establish `: Module.Finite O (Matrix (Fin r) (Fin r) O)` using `inferInstanceAs (Module.Finite O (Fin r → Fin r → O))`.

Establish `: Module.Finite O C` using `Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective`. Use `GlobalTheory.InertNorm.isAdicComplete_map_of_finite I C` as an intermediate fact. Use `GlobalTheory.InertNorm.finite_quotient_map_of_finite I C` as an intermediate fact. Establish `hsC : ∀ a ∈ C, s a ∈ C` using `fun a ha => hC.2 (by`. Establish `h2` using `congrArg s (hC.1 ha)`.

Rewrite `h2` using `[hm, hm]`. Combine the equalities or inequalities in the displayed calculation. Set `t : C →+* C` to `{ toFun := fun a => ⟨s a, hsC _ a.2⟩ map_one' := Subtype.ext h1 map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (hm _ _) map_zero' := Subtype.ext (by simpa using hsc 0) map_add' := fun a b => Subtype.ext (hadd _ _) }`. Establish `hιR : ∀ c, t (algebraMap O C c) = algebraMap O C (σ c)` using `fun c => Subtype.ext (hsc c)`. Establish `hl : s y * y ∈ C` using `hC.2 (by`.

Establish `h2 : s h * (s y * y) * h = s y * y`. Rewrite using `[← mul_assoc, ← hm, mul_assoc, ← hy, hm, mul_assoc, ← mul_assoc (s g), hg, one_mul]`. Use `conv_rhs => rw [← h2, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 hh, one_mul])`. Establish `hlu : (s y * y) * ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) = 1`. Rewrite using `[mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.inv_mul, h1]`.

Establish `hl' : ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) ∈ C` using `hC.2 (by`. Establish `h2` using `mul_eq_one_comm.1 hlu`. Conclude with `(Commute.units_inv_left (u := ⟨_, _, hlu, h2⟩) (hC.1 hl)).eq)`. Take `⟨ω, hω⟩` from `hω`. Take `⟨z, hz⟩` from `GlobalTheory.HenselianNorm.exists_norm_eq C (I.map (algebraMap O C)) t (fun a => Subtype.ext (hss _)) (fun x hx => (show I.map (algebraMap O C) ≤ (I.map (algebraMap O C)).comap t from Ideal.map_le_iff_le_comap.2 fun c hc => by`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hιR]`. Conclude with `Ideal.mem_map_of_mem _ (hI c hc)) hx)`. Use the proof step `⟨algebraMap O C ω, by rw [hιR, ← map_sub]; exact hω.map _⟩ ⟨_, hl'⟩ (Subtype.ext (by`. Express the relevant statement in the definitionally equal form `s _ = _`. Rewrite using `[hm, hss])) (IsUnit.of_mul_eq_one_right ⟨_, hl⟩ (Subtype.ext hlu))`.

Establish `hz' : z.1 * s z.1 = (y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)` using `congrArg Subtype.val hz`. Establish `h3 : (y * z.1) * s (y * z.1) = 1`. Rewrite using `[hm, mul_assoc, ← mul_assoc z.1, hz', mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.mul_inv, h1]`. Use `⟨⟨_, _, h3, mul_eq_one_comm.1 h3⟩, mul_eq_one_comm.1 h3, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g * (y * z.1) = y * z.1 * h`.

Rewrite using `[← mul_assoc, hy, mul_assoc, mul_assoc, hC.1 z.2]`.
-/
theorem exists_unitary_conj (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] {σ : O →+* O}
    (hσ : ∀ a, σ (σ a) = a) (hI : ∀ x ∈ I, σ x ∈ I) (hω : ∃ ω, IsUnit (ω - σ ω))
    {g h : Matrix (Fin r) (Fin r) O} (hg : cT σ g * g = 1) (hh : cT σ h * h = 1)
    (hs : g.charpoly.Separable) (e : h.charpoly = g.charpoly) :
    ∃ u : GL (Fin r) O, cT σ u.1 * u.1 = 1 ∧ g * u = u * h := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  obtain ⟨v, hv⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := g) hs
  obtain ⟨w, hw⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := h) (show h.charpoly.Separable by rwa [e])
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have hy : g * (a * b⁻¹ : GL (Fin r) O) = (a * b⁻¹ : GL (Fin r) O) * h := by
    have h1 := GlobalTheory.Orb.mul_krylov_eq g v
    have h2 := GlobalTheory.Orb.mul_krylov_eq h w
    rw [← ha] at h1
    rw [← hb, e] at h2
    rw [Units.val_mul, ← mul_assoc, h1, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h2,
      Units.inv_mul_cancel_left]
  generalize a * b⁻¹ = y at hy
  set s : Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) O := cT σ with hsdef
  have hm : ∀ a b, s (a * b) = s b * s a := fun a b => cT_mul σ a b
  have hadd : ∀ a b, s (a + b) = s a + s b := fun a b => Matrix.ext fun i j => by simp [s, cT]
  have hss : ∀ a, s (s a) = a := fun a => Matrix.ext fun i j => by simp [s, cT, hσ]
  have hsc : ∀ c : O, s (algebraMap O _ c) = algebraMap O _ (σ c) := fun c => by
    ext i j
    simp only [s, cT, transpose_apply, map_apply, algebraMap_matrix_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h1 : s 1 = 1 := by simpa using hsc 1
  change s g * g = 1 at hg
  change s h * h = 1 at hh
  let C := Subalgebra.centralizer O ({h} : Set (Matrix (Fin r) (Fin r) O))
  have hC : ∀ {a}, a ∈ C ↔ a * h = h * a := by simp [C, Subalgebra.mem_centralizer_iff, eq_comm]
  let _ : CommRing C :=
    { (inferInstance : Ring C) with
      mul_comm := fun a b => Subtype.ext (by
        obtain ⟨p, hp⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 a.2)
        obtain ⟨q, hq⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 b.2)
        rw [C.coe_mul, C.coe_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]) }
  have : Module.Finite O (Matrix (Fin r) (Fin r) O) := inferInstanceAs (Module.Finite O (Fin r → Fin r → O))
  have : Module.Finite O C := Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite I C
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite I C
  have hsC : ∀ a ∈ C, s a ∈ C := fun a ha => hC.2 (by
    have h2 := congrArg s (hC.1 ha)
    rw [hm, hm] at h2
    calc s a * h = h * (s h * s a) * h := by rw [← mul_assoc, mul_eq_one_comm.1 hh, one_mul]
      _ = h * s a := by rw [h2, mul_assoc, mul_assoc, hh, mul_one])
  let t : C →+* C :=
    { toFun := fun a => ⟨s a, hsC _ a.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (hm _ _)
      map_zero' := Subtype.ext (by simpa using hsc 0)
      map_add' := fun a b => Subtype.ext (hadd _ _) }
  have hιR : ∀ c, t (algebraMap O C c) = algebraMap O C (σ c) := fun c => Subtype.ext (hsc c)
  have hl : s y * y ∈ C := hC.2 (by
    have h2 : s h * (s y * y) * h = s y * y := by
      rw [← mul_assoc, ← hm, mul_assoc, ← hy, hm, mul_assoc, ← mul_assoc (s g), hg, one_mul]
    conv_rhs => rw [← h2, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 hh, one_mul])
  have hlu : (s y * y) * ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) = 1 := by
    rw [mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.inv_mul, h1]
  have hl' : ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) ∈ C := hC.2 (by
    have h2 := mul_eq_one_comm.1 hlu
    exact (Commute.units_inv_left (u := ⟨_, _, hlu, h2⟩) (hC.1 hl)).eq)
  obtain ⟨ω, hω⟩ := hω
  obtain ⟨z, hz⟩ := GlobalTheory.HenselianNorm.exists_norm_eq C (I.map (algebraMap O C)) t (fun a => Subtype.ext (hss _))
    (fun x hx => (show I.map (algebraMap O C) ≤ (I.map (algebraMap O C)).comap t from Ideal.map_le_iff_le_comap.2
      fun c hc => by
        rw [Ideal.mem_comap, Ideal.mem_comap, hιR]
        exact Ideal.mem_map_of_mem _ (hI c hc)) hx)
    ⟨algebraMap O C ω, by rw [hιR, ← map_sub]; exact hω.map _⟩ ⟨_, hl'⟩ (Subtype.ext (by
      change s _ = _
      rw [hm, hss])) (IsUnit.of_mul_eq_one_right ⟨_, hl⟩ (Subtype.ext hlu))
  have hz' : z.1 * s z.1 = (y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O) := congrArg Subtype.val hz
  have h3 : (y * z.1) * s (y * z.1) = 1 := by
    rw [hm, mul_assoc, ← mul_assoc z.1, hz', mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.mul_inv, h1]
  refine ⟨⟨_, _, h3, mul_eq_one_comm.1 h3⟩, mul_eq_one_comm.1 h3, ?_⟩
  change g * (y * z.1) = y * z.1 * h
  rw [← mul_assoc, hy, mul_assoc, mul_assoc, hC.1 z.2]

end Local

end GlobalTheory.BCT.UnitInert

namespace GlobalTheory.BCT.UnitInert

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `(algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2`.
-/
theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

/- English proof (translation)
Establish `h : ∀ᶠ w : Pl E in cofinite, ∀ i ∈ p.support, algebraMap E (w.adicCompletion E) (p.coeff i) ∈ w.adicCompletionIntegers E`. Rewrite using `[eventually_all_finset]`. Conclude with `fun i _ => eventually_int _`. Use `filter_upwards [h] with w hw`. Use `(Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_)` and prove the remaining obligations.

Rewrite using `[coeff_map]`. Distinguish the cases in `hi : i ∈ p.support`. Conclude with `⟨⟨_, hw i hi⟩, rfl⟩`. Rewrite using `[notMem_support_iff.1 hi, map_zero]`. Conclude with `⟨0, map_zero _⟩`.
-/
theorem eventually_lift (p : E[X]) : ∀ᶠ w : Pl E in cofinite, ∃ q : (w.adicCompletionIntegers E)[X],
    q.map (algebraMap _ (w.adicCompletion E)) = atPl w p := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ i ∈ p.support,
      algebraMap E (w.adicCompletion E) (p.coeff i) ∈ w.adicCompletionIntegers E := by
    rw [eventually_all_finset]
    exact fun i _ => eventually_int _
  filter_upwards [h] with w hw
  refine (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_)
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hw i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi, map_zero]
    exact ⟨0, map_zero _⟩

/- English proof (translation)
Take `⟨u, v, huv⟩` from `hP`. Use `filter_upwards [eventually_lift u, eventually_lift v] with w ⟨u', hu⟩ ⟨v', hv⟩ q hq`. Use `⟨u', v', Polynomial.map_injective (algebraMap _ (w.adicCompletion E)) Subtype.val_injective ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hq, hu, hv, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huv, Polynomial.map_one, Polynomial.map_one]`.
-/
theorem eventually_separable (P : E[X]) (hP : P.Separable) : ∀ᶠ w : Pl E in cofinite,
    ∀ q : (w.adicCompletionIntegers E)[X], q.map (algebraMap _ (w.adicCompletion E)) = atPl w P → q.Separable := by
  obtain ⟨u, v, huv⟩ := hP
  filter_upwards [eventually_lift u, eventually_lift v] with w ⟨u', hu⟩ ⟨v', hv⟩ q hq
  refine ⟨u', v', Polynomial.map_injective (algebraMap _ (w.adicCompletion E)) Subtype.val_injective ?_⟩
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hq, hu, hv,
    Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huv,
    Polynomial.map_one, Polynomial.map_one]

/- English proof (translation)
Introduce `E _ _ _ hU n _ P hP`. Use `filter_upwards [eventually_separable P hP.2.2.1] with w hsep hw γ γ' hγK hγ'K hγ hγ'`. Set `O` to `w.adicCompletionIntegers E`. Set `ι` to `algebraMap O (w.adicCompletion E)`. Establish `hι : Function.Injective ι` using `Subtype.val_injective`.

Take `⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1` from `(Subgroup.mem_subgroupOf.1 hγK)`. Take `⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1` from `(Subgroup.mem_subgroupOf.1 hγ'K)`. Take `⟨-, hcc, hv, h4, -⟩` from `GlobalTheory.ConjAtPlace.main E hU w`. Take `⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩` from `(h4 hw).2.1`. Establish `hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2` using `hcard`.

Use `haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w`. Use `haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)`. Set `c : O →+* O` to `(cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)`. Establish `hc : ∀ x, c (c x) = x` using `fun x => Subtype.ext (hcc _)`. Establish `hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι)` using `fun M => by`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1` using `fun x => by`. Rewrite using `[UL, if_neg hw]`. Express the relevant statement in the definitionally equal form `cT (cj w) x.val * 1 * x.val = 1 ↔ _`.

Rewrite using `[mul_one]`. Establish `hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι` using `fun x => by`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1` using `fun x hx => by`.

Use `Matrix.map_injective hι ?_` and prove the remaining obligations. Use `show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι`. Rewrite using `[Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]`. Conclude with `(hUL _).1 hx`. Establish `hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly` using `fun x => (Matrix.charpoly_map _ _).symm`.

Establish `e1 : y'.val.charpoly.map ι = atPl w P` using `by rw [hch, hy', hγ]`. Establish `e2 : z'.val.charpoly.map ι = atPl w P` using `by rw [hch, hz', hγ']`. Take `⟨u, hu, hcu⟩` from `exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc (fun x hx => by`. Rewrite `hx`, the goal using `[GlobalTheory.InertUQ.mem_max_iff]`. Conclude with `(hv _).trans_lt hx)`.

Use the proof step `⟨⟨x₀, hx₀⟩, by`. Rewrite using `[← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]`. Express the relevant statement in the definitionally equal form `¬ Valued.v (x₀ - cj w x₀) < 1`. Rewrite using `[Valuation.map_sub_swap, hx₁]`. Conclude with `lt_irrefl _⟩`.

Use the proof step `(hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1)`. Use the proof step `(Polynomial.map_injective ι hι (e2.trans e1.symm))`. Set `g : GLw n w` to `GeneralLinearGroup.map ι u`. Establish `hg : g ∈ UL n w`. Rewrite using `[hUL]`.

Use `congrArg (fun M => M.map ι) hu` as an intermediate fact. Simplify using `only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this`. Conclude with `this`. Establish `key : γ.1 * g = g * γ'.1`. Rewrite using `[← hy', ← hz', ← map_mul, ← map_mul]`.

Use `congr 1`. Conclude with `Units.ext hcu`. Use `⟨⟨g, hg⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `γ'.1 = g⁻¹ * γ.1 * g`. Rewrite using `[mul_assoc, key, inv_mul_cancel_left]`.
-/
theorem conj_of_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w →
      γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ hU n _ P hP
  filter_upwards [eventually_separable P hP.2.2.1] with w hsep hw γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1 := (Subgroup.mem_subgroupOf.1 hγK)
  obtain ⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1 := (Subgroup.mem_subgroupOf.1 hγ'K)
  obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
  have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
  have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
    ext i j; rfl
  have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
    rw [UL, if_neg hw]
    change cT (cj w) x.val * 1 * x.val = 1 ↔ _
    rw [mul_one]
  have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
    ext i j; rfl
  have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
    refine Matrix.map_injective hι ?_
    show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
    rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
    exact (hUL _).1 hx
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  obtain ⟨u, hu, hcu⟩ := exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
    (fun x hx => by
      rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
      exact (hv _).trans_lt hx)
    ⟨⟨x₀, hx₀⟩, by
      rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
      change ¬ Valued.v (x₀ - cj w x₀) < 1
      rw [Valuation.map_sub_swap, hx₁]
      exact lt_irrefl _⟩
    (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1)
    (Polynomial.map_injective ι hι (e2.trans e1.symm))
  let g : GLw n w := GeneralLinearGroup.map ι u
  have hg : g ∈ UL n w := by
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this
  have key : γ.1 * g = g * γ'.1 := by
    rw [← hy', ← hz', ← map_mul, ← map_mul]
    congr 1
    exact Units.ext hcu
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  change γ'.1 = g⁻¹ * γ.1 * g
  rw [mul_assoc, key, inv_mul_cancel_left]

end GlobalTheory.BCT.UnitInert
