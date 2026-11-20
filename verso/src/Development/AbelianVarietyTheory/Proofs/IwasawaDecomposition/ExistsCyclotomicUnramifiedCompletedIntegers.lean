import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBoundStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CycClosure

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Simplify using `only [clC, Subring.mem_inf]`. Apply `and_congr Iff.rfl` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x ∈ PadicComplexInt l ↔ _`. Rewrite using `[PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]`. Conclude with `(Valued.toNormedField.norm_le_one_iff).symm`.
-/
theorem mem_clC {F : IntermediateField ℚ_[l] (PadicAlgCl l)} {x : ℂ_[l]} :
    x ∈ clC l F ↔ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖x‖ ≤ 1 := by
  simp only [clC, Subring.mem_inf]
  apply and_congr Iff.rfl
  change x ∈ PadicComplexInt l ↔ _
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

/- English proof (translation)
Establish `hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1)` using `IsUltrametricDist.isClopen_closedBall _ one_ne_zero`. Establish `e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} = (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hy, h⟩, rfl⟩`.

Conclude with `⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩`. Introduce and unpack `⟨⟨y, hy, rfl⟩, h⟩`. Rewrite `h` using `[mem_closedBall_zero_iff]`. Conclude with `⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩`. Rewrite using `[e]`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[SetLike.mem_coe, mem_clC]`. Conclude with `hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩`. Introduce `x hx`.

Use `closure_inter_subset_inter_closure _ _ hx` as an intermediate fact. Rewrite `this` using `[hc.isClosed.closure_eq]`. Conclude with `mem_clC.2 ⟨this.1, by simpa using this.2⟩`.
-/
theorem coe_clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    (clC l F : Set ℂ_[l]) =
      closure ((fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1}) := by
  have hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} =
      (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      rw [mem_closedBall_zero_iff] at h
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_clC] at hx
    exact hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_clC.2 ⟨this.1, by simpa using this.2⟩

/- English proof (translation)
The claim follows from `mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩`.
-/
theorem clC_mono {F G : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ G) {x : ℂ_[l]}
    (hx : x ∈ clC l F) : x ∈ clC l G :=
  mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩

/- English proof (translation)
Substitute `hF` using the available equality. Take `⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩` from `GlobalTheory.BigInt.exists_integers_completion l LL`. Establish `e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l)` using `SetLike.coe_injective (hO.trans (coe_clC _).symm)`. Substitute `e` using the available equality. Conclude with `⟨hdvr, hres, hcomp, hadic, hdiv⟩`.
-/
theorem clC_props (LL : Loc.FinExt l) (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hF : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = F) :
    ∃ _ : IsDiscreteValuationRing ↥(clC l F),
      IsAlgClosed (IsLocalRing.ResidueField ↥(clC l F)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l F)) ↥(clC l F) ∧
      IsAdic (IsLocalRing.maximalIdeal ↥(clC l F)) ∧
      (∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) := by
  subst hF
  obtain ⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩ := GlobalTheory.BigInt.exists_integers_completion l LL
  have e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l) := SetLike.coe_injective (hO.trans (coe_clC _).symm)
  subst e
  exact ⟨hdvr, hres, hcomp, hadic, hdiv⟩

/- English proof (translation)
Establish `hn : 0 < l ^ k` using `pow_pos (Fact.out : l.Prime).pos k`. Use `haveI : NeZero (l ^ k) := ⟨hn.ne'⟩`. Establish `hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite`. Use `(Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]`.

Conclude with `hx`. Use `haveI := hfin.to_subtype`. Use `⟨IntermediateField.finiteDimensional_adjoin fun x hx => ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩` and prove the remaining obligations. Establish `hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0`. Rewrite using `[degree_cyclotomic]`.

Conclude with `(Nat.totient_pos.2 hn).ne'` after adjusting the coercions. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root _ hdeg`. Establish `hp : IsPrimitiveRoot ζ (l ^ k)` using `(isRoot_cyclotomic_iff).1 hζ`. Use `⟨ζ, hp, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[muK, IntermediateField.adjoin_le_iff]`.

Introduce `x hx`. Establish `hx' : x ^ (l ^ k) = 1` using `hx`. Take `⟨i, -, rfl⟩` from `hp.eq_pow_of_pow_eq_one hx'`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _`. Rewrite using `[IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]`.

Conclude with `IntermediateField.subset_adjoin _ _ hp.pow_eq_one`.
-/
theorem muK_spec (k : ℕ) : FiniteDimensional ℚ_[l] ↥(muK l k) ∧
    ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ (l ^ k) ∧ muK l k = IntermediateField.adjoin ℚ_[l] {ζ} := by
  have hn : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  haveI : NeZero (l ^ k) := ⟨hn.ne'⟩
  classical
  have hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite := by
    refine (Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hx
  haveI := hfin.to_subtype
  refine ⟨IntermediateField.finiteDimensional_adjoin fun x hx =>
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩
  have hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : IsPrimitiveRoot ζ (l ^ k) := (isRoot_cyclotomic_iff).1 hζ
  refine ⟨ζ, hp, le_antisymm ?_ ?_⟩
  · rw [muK, IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x ^ (l ^ k) = 1 := hx
    obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx'
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ hp.pow_eq_one

end GlobalTheory.CycClosure

namespace GlobalTheory.CycClosure

/- English proof (translation)
Introduce `l _ K₀ L k`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨hfd, ζ, hζ, hmu⟩` from `muK_spec (l := l) k`. Set `LL : Loc.FinExt l` to `⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩`. Establish `hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k`.

Simplify using `only [LL, Kt]`. Conclude with `sup_right_comm _ _ _`. Set `L0 : Loc.FinExt l` to `⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩`. Take `⟨hdvr, hres, hcomp, hadic, hdiv⟩` from `clC_props LL _ hM`. Take `⟨hdvr0, -, -, -, -⟩` from `clC_props L0 (Kt l K₀ L) rfl`.

Establish `mu0 : muK l 0 = ⊥`. Rewrite using `[muK, eq_bot_iff, IntermediateField.adjoin_le_iff]`. Introduce `x hx`. Establish `: x = 1` using `by simpa using hx`. Rewrite using `[this]`.

Conclude with `one_mem _`. Establish `hn : 0 < l ^ k` using `pow_pos hp.pos k`. Establish `hint : IsIntegral ℚ_[l] ζ` using `⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩`. Take `⟨n, Cb, hC⟩` from `GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one l (Kt l K₀ L) ζ hint`. Establish `hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ})`.

Introduce `x`. Rewrite using `[hmu]`. Establish `hl : ‖(l : ℂ_[l])‖ < 1`. Rewrite using `[← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]`. Use `lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.UnramValue.norm_l]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `hl0 : (l : ℂ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl`. Establish `cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L)`.

Introduce `c hc hcb`. Use `mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[norm_mul, norm_pow]`. Establish `h1 : ‖c‖ ≤ max Cb 1` using `hcb.trans (le_max_left _ _)`. Establish `h2 : (0 : ℝ) < max Cb 1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Combine the equalities or inequalities in the displayed calculation. Use `set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'`.

Establish `hζn : ‖ζ‖ = 1`. Use `congrArg norm hζ.pow_eq_one` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this`. Establish `hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k)`.

Rewrite using `[hB]`. Use `mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `((PadicComplex.norm_extends l ζ).trans hζn).le`. Establish `hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k)` using `fun x hx => clC_mono le_sup_left hx`. Establish `hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L)` using `pow_mem (natCast_mem _ _) _`.

Establish `rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l], (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ)`. Introduce `x hx`. Rewrite `hx` using `[hB]`. Take `⟨c, hc, e⟩` from `hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2`. Conclude with `⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩`.

Use `⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩` and prove the remaining obligations. Set `g : Fin n → ℂ_[l]` to `fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)`. Set `P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l]` to `Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)`. Set `B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l]` to `{ carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l]) add_mem' := fun ha hb => add_mem ha hb zero_mem' := zero_mem _ smul_mem' := fun a x hx => by`. Rewrite using `[Subring.smul_def, smul_eq_mul]`.

Conclude with `mul_mem (hAB _ a.2) hx }`. Establish `hBP : B' ≤ P`. Introduce `x hx`. Take `⟨c, hc, rfl⟩` from `rep x hx`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Use `Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))) (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Subring.smul_def, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))`. Clear the denominators using the available nonvanishing facts.

Use `haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P := isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))`. Establish `hfg : B'.FG`. Establish `h1 : (B'.comap P.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h2` using `h1.map P.subtype`. Rewrite `h2` using `[Submodule.map_comap_subtype, inf_eq_right.2 hBP]`. Then use the resulting hypothesis.

Take `⟨T, hT⟩` from `hfg`. Conclude with `⟨T, fun x => by rw [hT]; rfl⟩`. Introduce `x hx`. Take `⟨c, hc, rfl⟩` from `rep x hx`. Use `⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))), ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩` and prove the remaining obligations.

Simplify using `only [map_sum, aeval_monomial, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  intro l _ K₀ L k
  have hp : l.Prime := Fact.out
  obtain ⟨hfd, ζ, hζ, hmu⟩ := muK_spec (l := l) k
  let LL : Loc.FinExt l := ⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  have hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k := by
    simp only [LL, Kt]; exact sup_right_comm _ _ _
  let L0 : Loc.FinExt l := ⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  obtain ⟨hdvr, hres, hcomp, hadic, hdiv⟩ := clC_props LL _ hM
  obtain ⟨hdvr0, -, -, -, -⟩ := clC_props L0 (Kt l K₀ L) rfl
  have mu0 : muK l 0 = ⊥ := by
    rw [muK, eq_bot_iff, IntermediateField.adjoin_le_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; exact one_mem _
  have hn : 0 < l ^ k := pow_pos hp.pos k
  have hint : IsIntegral ℚ_[l] ζ :=
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩
  obtain ⟨n, Cb, hC⟩ := GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one l (Kt l K₀ L) ζ hint
  have hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ}) := by
    intro x; rw [hmu]
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]
    refine lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_
    rw [GlobalTheory.UnramValue.norm_l]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl
  have cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))),
      ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L) := by
    intro c hc hcb
    refine mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩
      simp
    · rw [norm_mul, norm_pow]
      have h1 : ‖c‖ ≤ max Cb 1 := hcb.trans (le_max_left _ _)
      have h2 : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc ‖(l : ℂ_[l])‖ ^ N * ‖c‖ ≤ ‖(l : ℂ_[l])‖ ^ N * max Cb 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / max Cb 1 * max Cb 1 := mul_le_mul_of_nonneg_right hN.le h2.le
        _ = 1 := by field_simp
  set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'
  have hζn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k) := by
    rw [hB]
    refine mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩
    exact ((PadicComplex.norm_extends l ζ).trans hζn).le
  have hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k) := fun x hx => clC_mono le_sup_left hx
  have hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L) := pow_mem (natCast_mem _ _) _
  have rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l],
      (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ) := by
    intro x hx
    rw [hB] at hx
    obtain ⟨c, hc, e⟩ := hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2
    exact ⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩
  refine ⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩
  · classical
    let g : Fin n → ℂ_[l] := fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)
    let P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] := Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)
    let B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] :=
      { carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l])
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        smul_mem' := fun a x hx => by
          rw [Subring.smul_def, smul_eq_mul]
          exact mul_mem (hAB _ a.2) hx }
    have hBP : B' ≤ P := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := rep x hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L)))
        (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)
      convert this using 1
      rw [Subring.smul_def, smul_eq_mul]
      change c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))
      field_simp
    haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P :=
      isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))
    have hfg : B'.FG := by
      have h1 : (B'.comap P.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map P.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.2 hBP] at h2
    obtain ⟨T, hT⟩ := hfg
    exact ⟨T, fun x => by rw [hT]; rfl⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := rep x hx
    refine ⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))),
      ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩
    simp only [map_sum, aeval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)
    ring

end GlobalTheory.CycClosure
