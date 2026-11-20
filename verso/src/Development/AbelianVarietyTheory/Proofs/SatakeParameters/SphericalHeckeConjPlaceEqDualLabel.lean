import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsConjPrimeEqDualLabelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphConj

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [(cA D).map_zero, (cA D).map_zero]`. Consider the case `add x y hx hy => rw [(cA D).map_add, (cA D).map_add, hx, hy]`. Consider the case `tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)`.
-/
theorem cA_cA' (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(cA D).map_zero, (cA D).map_zero]
  | add x y hx hy => rw [(cA D).map_add, (cA D).map_add, hx, hy]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)

/- English proof (translation)
The claim follows from `RingOfIntegers.ext rfl`.
-/
theorem cO_eq (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E x = GlobalTheory.IdemSupport.cO D x := RingOfIntegers.ext rfl

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.IdemSupport.mem_cP]`. Express the relevant statement in the definitionally equal form `x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _`. Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[cO_eq, GlobalTheory.IdemSupport.cO_cO]`. Conclude with `hy`. Introduce `h`. Conclude with `⟨GlobalTheory.IdemSupport.cO D x, h, by rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]⟩`.
-/
theorem conjPl_eq_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl P = GlobalTheory.IdemSupport.cP P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.IdemSupport.mem_cP]
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]; exact hy
  · intro h
    exact ⟨GlobalTheory.IdemSupport.cO D x, h, by rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]⟩

/- English proof (translation)
Rewrite using `[conjPl_eq_cP]`. Conclude with `GlobalTheory.IdemSupport.mem_cP P x`.
-/
theorem mem_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (conjPl P).asIdeal ↔ GlobalTheory.IdemSupport.cO D x ∈ P.asIdeal := by
  rw [conjPl_eq_cP]; exact GlobalTheory.IdemSupport.mem_cP P x

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[mem_conjPl, mem_conjPl, GlobalTheory.IdemSupport.cO_cO]`.
-/
theorem conjPl_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl (conjPl P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [mem_conjPl, mem_conjPl, GlobalTheory.IdemSupport.cO_cO]

/- English proof (translation)
The claim follows from `(GlobalTheory.IdemSupport.isConjPl_iff P _).2 (conjPl_eq_cP P)`.
-/
theorem isConjPl_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjPl P) :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).2 (conjPl_eq_cP P)

/- English proof (translation)
Introduce `h'`. Apply `h` to reduce the goal to its premises. Establish `e1 : (conjPl P).asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)` using `rfl`. Rewrite using `[e1, ← Ideal.map_pow]`. Use `Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h'` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[cO_eq, GlobalTheory.IdemSupport.cO_cO]`.
-/
theorem not_mem_sq (P : HeightOneSpectrum (𝓞 D.host.E)) (ϖ : 𝓞 D.host.E) (h : ϖ ∉ (conjPl P).asIdeal ^ 2) :
    GlobalTheory.IdemSupport.cO D ϖ ∉ P.asIdeal ^ 2 := by
  intro h'
  apply h
  have e1 : (conjPl P).asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := rfl
  rw [e1, ← Ideal.map_pow]
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h'
  convert this using 1
  rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]

/- English proof (translation)
Break down `h with ⟨hi, rfl⟩ | ⟨rfl, h2, h3⟩` into its components or cases. Establish `hc` using `(GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2 Q (conjPl Q) e hi (isConjPl_conjPl Q)`. Conclude with `Or.inl ⟨hi, Or.inl ⟨hc, by rw [cA_cA', add_comm]⟩⟩`. Establish `h' : IsPrimeIdem Q f f` using `Or.inr ⟨rfl, h2, h3⟩`. Establish `hc` using `((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 Q f f h').2.1`.

Establish `ht : GlobalTheory.IdemSupport.Comparison₂ (GlobalTheory.IdemSupport.cP Q) f`. Use `GlobalTheory.IdemSupport.Comparison₂.conj (P := Q) (e := f) h3` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis. Use `Or.inr ⟨?_, rfl⟩` and prove the remaining obligations. Rewrite using `[conjPl_eq_cP]`.

Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `only [Submodule.zero_mem]`. Conclude with `(ht x hx).trans (h3 x hx).symm`.
-/
theorem conj_cases (V : HSp D) {Q : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem Q e f) :
    (Formalism.L2.NTheta.IsIdemAt e Q ∧ IsPrimeIdem (conjPl Q) (cA D e) f) ∨ (conjPl Q = Q ∧ f = e) := by
  rcases h with ⟨hi, rfl⟩ | ⟨rfl, h2, h3⟩
  · have hc := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2 Q (conjPl Q) e hi
      (isConjPl_conjPl Q)
    exact Or.inl ⟨hi, Or.inl ⟨hc, by rw [cA_cA', add_comm]⟩⟩
  · have h' : IsPrimeIdem Q f f := Or.inr ⟨rfl, h2, h3⟩
    have hc := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 Q f f h').2.1
    have ht : GlobalTheory.IdemSupport.Comparison₂ (GlobalTheory.IdemSupport.cP Q) f := by
      have := GlobalTheory.IdemSupport.Comparison₂.conj (P := Q) (e := f) h3
      rwa [hc] at this
    refine Or.inr ⟨?_, rfl⟩
    rw [conjPl_eq_cP]
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp only [Submodule.zero_mem]
    · exact (ht x hx).trans (h3 x hx).symm

/- English proof (translation)
Take `⟨e, f, h⟩` from `(GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P`. Break down `conj_cases V h with ⟨-, h'⟩ | ⟨hc, -⟩` into its components or cases. Rewrite using `[GlobalTheory.SphLabelOps.hyp_eq h', GlobalTheory.SphLabelOps.hyp_eq h]`. Rewrite using `[hc]`.
-/
theorem hyp_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) : hyp V (conjPl P) = hyp V P := by
  obtain ⟨e, f, h⟩ := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
  rcases conj_cases V h with ⟨-, h'⟩ | ⟨hc, -⟩
  · rw [GlobalTheory.SphLabelOps.hyp_eq h', GlobalTheory.SphLabelOps.hyp_eq h]
  · rw [hc]

/- English proof (translation)
The claim follows from `GlobalTheory.T.elementaryDivisors_conjPrime_eq_dualLabel V P e ϖ d α he h1 h2 hd`.
-/
theorem divAt_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E)
    (d : List ℤ) (α : GA D V) (he : Formalism.L2.NTheta.IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : DivAt V e (ϖ : D.host.E) d α) : DivAt V (cA D e) (star (ϖ : D.host.E)) (dualLab d) α :=
  GlobalTheory.T.elementaryDivisors_conjPrime_eq_dualLabel V P e ϖ d α he h1 h2 hd

/- English proof (translation)
Take `⟨e, f, ϖ, α, -, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩` from `hR`. Establish `hS : OffS D ∅ P` using `fun v hv => absurd hv (Finset.notMem_empty v)`. Break down `conj_cases V hef with ⟨hi, h'⟩ | ⟨hc, rfl⟩` into its components or cases. Rewrite `h'` using `[conjPl_conjPl]`. Establish `hD` using `divAt_conj V (conjPl P) e ϖ d α hi hϖ hϖ2 hdiv`.

Rewrite `hD` using `[← GlobalTheory.IdemSupport.cO_coe]`. Conclude with `⟨cA D e, f, GlobalTheory.IdemSupport.cO D ϖ, α, hS, h', (mem_conjPl P ϖ).1 hϖ, not_mem_sq P ϖ hϖ2, GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩`. Establish `hc' : conjPl P = P` using `hc.symm.trans (conjPl_conjPl P)`. Rewrite `hef`, `hϖ`, `hϖ2` using `[hc']`. Establish `he` using `(GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef).1`.

Take `⟨a, b, ha, -, hb, -, hab⟩` from `(GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hef (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).1`. Establish `h0` using `GlobalTheory.SphLabelOps.unif_ne_zero hϖ2`. Establish `hinv` using `(GlobalTheory.DivDual.divAt_inv_and_mul V f _ d α he h0 hdiv).1`. Establish `ha' : a⁻¹ ∈ KsphC V ∅` using `(GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 ha))`. Establish `hb' : b⁻¹ ∈ KsphC V ∅` using `(GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 hb))`.

Establish `hD` using `(GlobalTheory.DivDual.divAt_inv_and_mul V f _ _ α⁻¹ he h0 hinv).2 _ ha' _ hb'`. Establish `e1 : a⁻¹ * α⁻¹ * b⁻¹ = α` using `by rw [hab]; group`. Rewrite `hD` using `[e1]`. Conclude with `⟨f, f, ϖ, α, hS, hef, hϖ, hϖ2, GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩`.
-/
theorem sphOp_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (hR : SphOp V (conjPl P) d R) : SphOp V P (dualLab d) R := by
  obtain ⟨e, f, ϖ, α, -, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := hR
  have hS : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)
  rcases conj_cases V hef with ⟨hi, h'⟩ | ⟨hc, rfl⟩
  · rw [conjPl_conjPl] at h'
    have hD := divAt_conj V (conjPl P) e ϖ d α hi hϖ hϖ2 hdiv
    rw [← GlobalTheory.IdemSupport.cO_coe] at hD
    exact ⟨cA D e, f, GlobalTheory.IdemSupport.cO D ϖ, α, hS, h', (mem_conjPl P ϖ).1 hϖ, not_mem_sq P ϖ hϖ2,
      GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩
  · have hc' : conjPl P = P := hc.symm.trans (conjPl_conjPl P)
    rw [hc'] at hef hϖ hϖ2
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef).1
    obtain ⟨a, b, ha, -, hb, -, hab⟩ :=
      (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hef (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).1
    have h0 := GlobalTheory.SphLabelOps.unif_ne_zero hϖ2
    have hinv := (GlobalTheory.DivDual.divAt_inv_and_mul V f _ d α he h0 hdiv).1
    have ha' : a⁻¹ ∈ KsphC V ∅ := (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 ha))
    have hb' : b⁻¹ ∈ KsphC V ∅ := (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 hb))
    have hD := (GlobalTheory.DivDual.divAt_inv_and_mul V f _ _ α⁻¹ he h0 hinv).2 _ ha' _ hb'
    have e1 : a⁻¹ * α⁻¹ * b⁻¹ = α := by rw [hab]; group
    rw [e1] at hD
    exact ⟨f, f, ϖ, α, hS, hef, hϖ, hϖ2, GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨R, hR⟩`. Conclude with `⟨R, sphOp_conj V P d R hR⟩`. Introduce and unpack `⟨R, hR⟩`. Rewrite `hR` using `[← conjPl_conjPl P]`.

Use `sphOp_conj V (conjPl P) (dualLab d) R hR` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SphLabelOps.dualLab_dualLab]`. Conclude with `⟨R, this⟩`.
-/
theorem isLab_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    IsLab V (conjPl P) d ↔ IsLab V P (dualLab d) := by
  constructor
  · rintro ⟨R, hR⟩; exact ⟨R, sphOp_conj V P d R hR⟩
  · rintro ⟨R, hR⟩
    rw [← conjPl_conjPl P] at hR
    have := sphOp_conj V (conjPl P) (dualLab d) R hR
    rw [GlobalTheory.SphLabelOps.dualLab_dualLab] at this
    exact ⟨R, this⟩

/- English proof (translation)
Distinguish the cases in `hd : IsLab V (conjPl P) d`. Establish `h1` using `sphOp_conj V P d _ (GlobalTheory.SphLabelOps.sphOp_rep hd)`. Rewrite using `[((GlobalTheory.SphLabelOps.label_operators V P).1 _ _ h1).2 M π u hu, GlobalTheory.SphLabelOps.opOf_single]`. Establish `hd' : ¬ IsLab V P (dualLab d)` using `fun h => hd ((isLab_conj V P d).2 h)`. Rewrite using `[Hk3.rep, dif_neg hd, Hk3.rep, dif_neg hd']`.
-/
theorem sum_rep_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : GA D V →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ hyp V P, π k u = u) (d : List ℤ) :
    ∑ γ ∈ rep V (conjPl P) d, π γ u = ∑ γ ∈ rep V P (dualLab d), π γ u := by
  by_cases hd : IsLab V (conjPl P) d
  · have h1 := sphOp_conj V P d _ (GlobalTheory.SphLabelOps.sphOp_rep hd)
    rw [((GlobalTheory.SphLabelOps.label_operators V P).1 _ _ h1).2 M π u hu, GlobalTheory.SphLabelOps.opOf_single]
  · have hd' : ¬ IsLab V P (dualLab d) := fun h => hd ((isLab_conj V P d).2 h)
    rw [Hk3.rep, dif_neg hd, Hk3.rep, dif_neg hd']

/- English proof (translation)
Introduce `D V P`. Use `⟨hyp_conj V P, isLab_conj V P, fun c M _ _ π u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[opOf, opOf, dualC, Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • ∑ γ ∈ rep V P d, π γ) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]`. Simplify using `only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]`. Conclude with `Finset.sum_congr rfl fun d _ => by rw [sum_rep_conj V P π u hu d]`.
-/
theorem sph_conj : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), hyp V (conjPl P) = hyp V P ∧ (∀ d, IsLab V (conjPl P) d ↔ IsLab V P (dualLab d)) ∧ ∀ c, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π (conjPl P) c u = opOf π P (dualC c) u := by
  intro D V P
  refine ⟨hyp_conj V P, isLab_conj V P, fun c M _ _ π u hu => ?_⟩
  rw [opOf, opOf, dualC, Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • ∑ γ ∈ rep V P d, π γ) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [sum_rep_conj V P π u hu d]

end GlobalTheory.SphConj

end
