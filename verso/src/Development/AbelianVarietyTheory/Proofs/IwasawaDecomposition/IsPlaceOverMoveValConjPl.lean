import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal
open GlobalTheory.AntiRamConj GlobalTheory.Mem.Chr
open scoped Pointwise

namespace GlobalTheory.AntiLAdic

section Galois

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (cc : Ω ≃+* Ω)
  (hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y)

def conjHom : Formalism.ConjugateSelfDual.G E Ω →* Formalism.ConjugateSelfDual.G E Ω where
  toFun := conjAut cc hc
  map_one' := by
    ext x
    exact cc.apply_symm_apply x
  map_mul' g h := by
    ext x
    change cc (g (h (cc.symm x))) = cc (g (cc.symm (cc (h (cc.symm x)))))
    rw [RingEquiv.symm_apply_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjHom_apply (g : Formalism.ConjugateSelfDual.G E Ω) (x : Ω) : conjHom cc hc g x = cc (g (cc.symm x)) := rfl

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (cc : Ω ≃+* Ω)
  (hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y) in

/- English proof (translation)
Take `⟨hdec, hval⟩` from `hσ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hdec`, the goal using `[ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Use extensionality with `y`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, _root_.GlobalTheory.AntiRamConj.mem_moveVal, ← map_inv, AlgEquiv.smul_def, _root_.GlobalTheory.AntiLAdic.conjHom_apply, RingEquiv.symm_apply_apply, _root_.GlobalTheory.AntiRamConj.mem_moveVal]`.

Use `conv_rhs => rw [← hdec]`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`. Introduce `x hx`. Rewrite `hx` using `[ValuationSubring.valuation_le_one_iff, _root_.GlobalTheory.AntiRamConj.mem_moveVal]`. Rewrite using `[_root_.GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_pow, _root_.GlobalTheory.AntiLAdic.conjHom_apply, RingEquiv.symm_apply_apply]`.

Conclude with `hval _ ((ValuationSubring.valuation_le_one_iff _ _).mpr hx)`.
-/
theorem _root_.GlobalTheory.AntiLAdic.isFrob_conjHom [NumberField E] {B : ValuationSubring Ω} {q : ℕ} {σ : _root_.Formalism.ConjugateSelfDual.G E Ω} (hσ : _root_.Formalism.ConjugateSelfDual.IsFrob (F := E) B q σ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob (F := E) (_root_.GlobalTheory.AntiRamConj.moveVal cc B) q (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) := by
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, _root_.GlobalTheory.AntiRamConj.mem_moveVal,
      ← map_inv, AlgEquiv.smul_def, _root_.GlobalTheory.AntiLAdic.conjHom_apply,
      RingEquiv.symm_apply_apply, _root_.GlobalTheory.AntiRamConj.mem_moveVal]
    conv_rhs => rw [← hdec]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  · intro x hx
    rw [ValuationSubring.valuation_le_one_iff, _root_.GlobalTheory.AntiRamConj.mem_moveVal] at hx
    rw [_root_.GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_pow,
      _root_.GlobalTheory.AntiLAdic.conjHom_apply, RingEquiv.symm_apply_apply]
    exact hval _ ((ValuationSubring.valuation_le_one_iff _ _).mpr hx)

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (cc : Ω ≃+* Ω)
  (hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y) in

/- English proof (translation)
Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one, Filter.tendsto_def]`. Introduce `s hs`. Take `⟨L, hL, hLs⟩` from `(krullTopology_mem_nhds_one_iff E Ω s).mp hs`. Set `b` to `Module.finBasis E L`.

Set `S : Set Ω` to `Set.range (fun i => cc.symm (b i : Ω))`. Use `(krullTopology_mem_nhds_one_iff E Ω _).mpr ⟨IntermediateField.adjoin E S, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : Finite S := Set.finite_range _ |>.to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)`. Introduce `σ hσ`.

Rewrite `hσ` using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Use `show _root_.GlobalTheory.AntiLAdic.conjHom cc hc σ ∈ s`. Apply `hLs` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Rewrite using `[_root_.GlobalTheory.AntiLAdic.conjHom_apply]`. It suffices to establish `h : cc.symm x ∈ IntermediateField.adjoin E S by`. Rewrite using `[hσ _ h, RingEquiv.apply_symm_apply]`. Establish `hsum : x = ∑ i, algebraMap E Ω (b.repr ⟨x, hx⟩ i) * (b i : Ω)`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)`.

Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul, Algebra.smul_def] at h`. Conclude with `h.symm`. Rewrite using `[hsum, map_sum]`. Use `sum_mem (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`.

Take `⟨y, hy⟩` from `hc (b.repr ⟨x, hx⟩ i)`. Rewrite using `[hy]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ y) (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)`.
-/
theorem _root_.GlobalTheory.AntiLAdic.continuous_conjHom [Algebra.IsAlgebraic E Ω] : Continuous (_root_.GlobalTheory.AntiLAdic.conjHom cc hc) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro s hs
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).mp hs
  let b := Module.finBasis E L
  let S : Set Ω := Set.range (fun i => cc.symm (b i : Ω))
  refine (krullTopology_mem_nhds_one_iff E Ω _).mpr ⟨IntermediateField.adjoin E S, ?_, ?_⟩
  · haveI : Finite S := Set.finite_range _ |>.to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  · intro σ hσ
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
    show _root_.GlobalTheory.AntiLAdic.conjHom cc hc σ ∈ s
    apply hLs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [_root_.GlobalTheory.AntiLAdic.conjHom_apply]
    suffices h : cc.symm x ∈ IntermediateField.adjoin E S by
      rw [hσ _ h, RingEquiv.apply_symm_apply]
    have hsum : x = ∑ i, algebraMap E Ω (b.repr ⟨x, hx⟩ i) * (b i : Ω) := by
      have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, Algebra.smul_def] at h
      exact h.symm
    rw [hsum, map_sum]
    refine sum_mem (fun i _ => ?_)
    rw [map_mul]
    obtain ⟨y, hy⟩ := hc (b.repr ⟨x, hx⟩ i)
    rw [hy]
    exact mul_mem (IntermediateField.algebraMap_mem _ y)
      (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)

end Galois

section Places

variable {E : Type} [Field E] [NumberField E]

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
/- English proof (translation)
Introduce `x`. Rewrite using `[← h (c x), hcc]`.
-/
theorem _root_.GlobalTheory.AntiLAdic.conjPl_symm {c : E ≃+* E} (hcc : ∀ x, c (c x) = x) {v v' : HeightOneSpectrum (𝓞 E)} (h : _root_.GlobalTheory.Mem.Chr.ConjPl c v v') :
    _root_.GlobalTheory.Mem.Chr.ConjPl c v' v := by
  intro x
  rw [← h (c x), hcc]

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in

/- English proof (translation)
Rewrite `h` using `[_root_.GlobalTheory.Mem.Chr.conjPl_iff_comap]`. Establish `hmap : v'.asIdeal = v.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv c)`. Rewrite using `[h, Ideal.map_comap_of_surjective _ (RingEquiv.surjective _)]`. Unfold `_root_.Formalism.ConjugateSelfDual.normV`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv v.asIdeal v'.asIdeal (NumberField.RingOfIntegers.mapRingEquiv c) hmap).toEquiv).symm`.
-/
theorem _root_.GlobalTheory.AntiLAdic.normV_conjPl {c : E ≃+* E} {v v' : HeightOneSpectrum (𝓞 E)} (h : _root_.GlobalTheory.Mem.Chr.ConjPl c v v') : _root_.Formalism.ConjugateSelfDual.normV v' = _root_.Formalism.ConjugateSelfDual.normV v := by
  rw [_root_.GlobalTheory.Mem.Chr.conjPl_iff_comap] at h
  have hmap : v'.asIdeal = v.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv c) := by
    rw [h, Ideal.map_comap_of_surjective _ (RingEquiv.surjective _)]
  unfold _root_.Formalism.ConjugateSelfDual.normV
  exact (Nat.card_congr
    (Ideal.quotientEquiv v.asIdeal v'.asIdeal (NumberField.RingOfIntegers.mapRingEquiv c) hmap).toEquiv).symm

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in

/- English proof (translation)
Introduce `x`. Rewrite using `[_root_.GlobalTheory.AntiRamConj.moveVal_lt_one]`. Establish `hx : cc.symm (algebraMap E Ω x) = algebraMap E Ω (c.symm x)`. Rewrite using `[RingEquiv.symm_apply_eq, hcc, RingEquiv.apply_symm_apply]`. Rewrite using `[hx]`.

Set `y : 𝓞 E` to `NumberField.RingOfIntegers.mapRingEquiv c.symm x`. Establish `hy : (y : E) = c.symm x` using `rfl`. Establish `key` using `(_root_.GlobalTheory.Mem.Chr.conjPl_iff_mem c v v').mp h y x (by rw [hy, RingEquiv.apply_symm_apply])`. Rewrite using `[← key, ← hB y, hy]`.
-/
theorem _root_.GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl {Ω : Type} [Field Ω] [Algebra E Ω] {c : E ≃+* E} {cc : Ω ≃+* Ω}
    (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : _root_.GlobalTheory.Mem.Chr.ConjPl c v v') {B : ValuationSubring Ω} (hB : _root_.Formalism.ConjugateSelfDual.IsPlaceOver B v) : _root_.Formalism.ConjugateSelfDual.IsPlaceOver (_root_.GlobalTheory.AntiRamConj.moveVal cc B) v' := by
  intro x
  rw [_root_.GlobalTheory.AntiRamConj.moveVal_lt_one]
  have hx : cc.symm (algebraMap E Ω x) = algebraMap E Ω (c.symm x) := by
    rw [RingEquiv.symm_apply_eq, hcc, RingEquiv.apply_symm_apply]
  rw [hx]
  let y : 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv c.symm x
  have hy : (y : E) = c.symm x := rfl
  have key := (_root_.GlobalTheory.Mem.Chr.conjPl_iff_mem c v v').mp h y x
    (by rw [hy, RingEquiv.apply_symm_apply])
  rw [← key, ← hB y, hy]

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in

/- English proof (translation)
Take `⟨u, hvu⟩ : ∃ u, HeightOneSpectrum.under (𝓞 F) v = u` from `⟨_, rfl⟩`. Establish `hv'u : HeightOneSpectrum.under (𝓞 F) v' = u` using `((_root_.GlobalTheory.Mem.Chr.under_eq_iff_conjPl c h2 hne v v').mpr (Or.inr h)).trans hvu`. Establish `hmem : ∀ P, P ∈ _root_.Formalism.L2.Host.aboveF (L` using `E) F u ↔ P = v ∨ P = v' := by`. Introduce `P`. Unfold `_root_.Formalism.L2.Host.aboveF`.

Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, ← hvu, _root_.GlobalTheory.Mem.Chr.under_eq_iff_conjPl c h2 hne v P]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(hP | hP)`. Conclude with `Or.inl hP`. Conclude with `Or.inr ((_root_.GlobalTheory.Mem.Chr.existsUnique_conjPl _ v).unique hP h)`.

Introduce and unpack `(hP | hP)`. Conclude with `Or.inl hP`. Conclude with `Or.inr (hP ▸ h)`. Establish `hloc : ∀ P, HeightOneSpectrum.under (𝓞 F) P = u → χ.UnrAt P → χ.locK P (_root_.Formalism.L2.Host.upF F (_root_.Formalism.L2.Host.unif u)) = χ.val P`. Introduce `P hP hPu`.

Rewrite using `[_root_.GlobalTheory.HeckeProduct.locK_unr χ hPu, hr, hP, _root_.GlobalTheory.Mem.Chr.ordF_unif_self, zpow_one]`. Establish `hprod` using `ht.1 u (_root_.Formalism.L2.Host.unif u)`. Rewrite `hprod` using `[_root_.Formalism.L2.Host.HChar.resFin_apply]`. Distinguish the cases in `hvv : v = v'`. Substitute `hvv` using the available equality.

Establish `hset : _root_.Formalism.L2.Host.aboveF (L` using `E) F u = {v} := by`. Use extensionality with `P`. Rewrite using `[hmem, Finset.mem_singleton, or_self]`. Rewrite `hprod` using `[hset, Finset.prod_singleton, hloc v hvu hu]`. Rewrite using `[hprod, one_mul]`.

Establish `hset : _root_.Formalism.L2.Host.aboveF (L` using `E) F u = {v, v'} := by`. Use extensionality with `P`. Rewrite using `[hmem, Finset.mem_insert, Finset.mem_singleton]`. Rewrite `hprod` using `[hset, Finset.prod_pair hvv, hloc v hvu hu, hloc v' hv'u hu']`. Conclude with `hprod`.
-/
theorem _root_.GlobalTheory.AntiLAdic.val_mul_val_conj {F : Type} [Field F] [NumberField F] [Algebra F E] (c : E ≃ₐ[F] E)
    (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 F)) k)
    (χ : _root_.Formalism.L2.Host.HChar E) (ht : χ.TrivOn F) {v v' : HeightOneSpectrum (𝓞 E)} (h : _root_.GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv v v')
    (hu : χ.UnrAt v) (hu' : χ.UnrAt v') : χ.val v * χ.val v' = 1 := by
  classical
  obtain ⟨u, hvu⟩ : ∃ u, HeightOneSpectrum.under (𝓞 F) v = u := ⟨_, rfl⟩
  have hv'u : HeightOneSpectrum.under (𝓞 F) v' = u :=
    ((_root_.GlobalTheory.Mem.Chr.under_eq_iff_conjPl c h2 hne v v').mpr (Or.inr h)).trans hvu
  have hmem : ∀ P, P ∈ _root_.Formalism.L2.Host.aboveF (L := E) F u ↔ P = v ∨ P = v' := by
    intro P
    unfold _root_.Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ← hvu,
      _root_.GlobalTheory.Mem.Chr.under_eq_iff_conjPl c h2 hne v P]
    constructor
    · rintro (hP | hP)
      · exact Or.inl hP
      · exact Or.inr ((_root_.GlobalTheory.Mem.Chr.existsUnique_conjPl _ v).unique hP h)
    · rintro (hP | hP)
      · exact Or.inl hP
      · exact Or.inr (hP ▸ h)
  have hloc : ∀ P, HeightOneSpectrum.under (𝓞 F) P = u → χ.UnrAt P →
      χ.locK P (_root_.Formalism.L2.Host.upF F (_root_.Formalism.L2.Host.unif u)) = χ.val P := by
    intro P hP hPu
    rw [_root_.GlobalTheory.HeckeProduct.locK_unr χ hPu, hr, hP, _root_.GlobalTheory.Mem.Chr.ordF_unif_self,
      zpow_one]
  have hprod := ht.1 u (_root_.Formalism.L2.Host.unif u)
  rw [_root_.Formalism.L2.Host.HChar.resFin_apply] at hprod
  by_cases hvv : v = v'
  · subst hvv
    have hset : _root_.Formalism.L2.Host.aboveF (L := E) F u = {v} := by
      ext P
      rw [hmem, Finset.mem_singleton, or_self]
    rw [hset, Finset.prod_singleton, hloc v hvu hu] at hprod
    rw [hprod, one_mul]
  · have hset : _root_.Formalism.L2.Host.aboveF (L := E) F u = {v, v'} := by
      ext P
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
    rw [hset, Finset.prod_pair hvv, hloc v hvu hu, hloc v' hv'u hu'] at hprod
    exact hprod

end Places

open NumberField IsDedekindDomain in
open scoped Pointwise in

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hne hinv hr Ω _ _ _ cc hcc art hart l _ ι χ n r hrc hlad ht`. Establish `hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y` using `fun x => ⟨c.symm x, by rw [RingEquiv.symm_apply_eq, hcc, AlgEquiv.apply_symm_apply]⟩`. Establish `hinv' : ∀ x, c.toRingEquiv (c.toRingEquiv x) = x` using `fun x => hinv x`. Establish `hex` using `_root_.GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv`. Use `choose conjPrime₂ hconjP using fun w => (hex w).exists`.

Establish `hconj2 : ∀ w, conjPrime₂ (conjPrime₂ w) = w` using `fun w => (hex (conjPrime₂ w)).unique (hconjP (conjPrime₂ w)) (_root_.GlobalTheory.AntiLAdic.conjPl_symm hinv' (hconjP w))`. Establish `hlfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite`. Establish `hI : Ideal.span {(l : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`.

Conclude with `(Ideal.finite_factors hI).subset (fun w hw => Ideal.dvd_span_singleton.mpr hw)`. Establish `hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ χ.UnrAt w ∨ (l : 𝓞 E) ∈ w.asIdeal}.Finite` using `(_root_.GlobalTheory.Mem.UnrAe.finite_ramified χ).union hlfin`. Use `set T := hfin.toFinset with hT`. Establish `hgood : ∀ w ∉ T, χ.UnrAt w ∧ (l : 𝓞 E) ∉ w.asIdeal`. Introduce `w hw`.

Rewrite `hw` using `[hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not]`. Conclude with `hw`. Set `φ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (_root_.Formalism.ConjugateSelfDual.Qbar l)ˣ` to `(r.comp (_root_.GlobalTheory.AntiLAdic.conjHom cc hc)) * r`. Establish `hφc : Continuous φ` using `by show Continuous (fun g => r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc g) * r g)`. Conclude with `(hrc.comp (_root_.GlobalTheory.AntiLAdic.continuous_conjHom cc hc)).mul hrc`.

Establish `hφ : φ = 1`. Use `_root_.GlobalTheory.FrobDense.eq_one_of_frob E Ω art hart _ φ hφc (T ∪ T.image conjPrime₂) ?_` and prove the remaining obligations. Introduce `v hv A hA σ hσ`. Rewrite `hv` using `[Finset.mem_union, not_or]`. Establish `hv' : conjPrime₂ v ∉ T`.

Introduce `hmemT`. Conclude with `hv.2 (Finset.mem_image.mpr ⟨conjPrime₂ v, hmemT, hconj2 v⟩)`. Take `⟨hU, hl⟩` from `hgood v hv.1`. Take `⟨hU', hl'⟩` from `hgood (conjPrime₂ v) hv'`. Establish `hA'` using `_root_.GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl hcc (hconjP v) hA`.

Establish `hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob (F` using `E) (_root_.GlobalTheory.AntiRamConj.moveVal cc A) (_root_.Formalism.ConjugateSelfDual.normV (conjPrime₂ v)) (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) := by`. Rewrite using `[_root_.GlobalTheory.AntiLAdic.normV_conjPl (hconjP v)]`. Conclude with `_root_.GlobalTheory.AntiLAdic.isFrob_conjHom cc hc hσ`. Establish `r1` using `hlad.frob_unr hart (Or.inl hl) hU hA hσ`. Establish `r2` using `hlad.frob_unr hart (Or.inl hl') hU' hA' hσ'`.

Establish `hval` using `_root_.GlobalTheory.AntiLAdic.val_mul_val_conj c h2 hne hr χ ht (hconjP v) hU hU'`. Use `show r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) * r σ = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, r1, r2, Units.val_one, ← mul_inv, ← map_mul, ← Units.val_mul, mul_comm (χ.val (conjPrime₂ v)), hval, Units.val_one, map_one, inv_one]`. Introduce `g g' hg'`.

Establish `hgg : g' = _root_.GlobalTheory.AntiLAdic.conjHom cc hc g` using `AlgEquiv.ext fun x => by rw [hg', _root_.GlobalTheory.AntiLAdic.conjHom_apply]`. Establish `h1 : r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc g) * r g = 1` using `DFunLike.congr_fun hφ g`. Rewrite using `[hgg]`. Conclude with `eq_inv_of_mul_eq_one_left h1`.
-/
theorem _root_.GlobalTheory.AntiLAdic.antiHom_of_trivOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ x, c (c x) = x) → (∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 F)) k) → ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (cc : Ω ≃+* Ω), (∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) → ∀ (art : _root_.Neutral.B1.Ideles E →* _root_.GlobalTheory.HeckeGal.Gab E Ω), _root_.GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (l : ℕ) [Fact l.Prime] (ι : _root_.Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ) (χ : _root_.Formalism.L2.Host.HChar E) (n : (E →+* ℂ) → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* (_root_.Formalism.ConjugateSelfDual.Qbar l)ˣ), Continuous r → _root_.GlobalTheory.HeckeGal.IsLAdicOf art ι χ n r → χ.TrivOn F → _root_.Formalism.BasicNotions.AntiHom cc r := by
  intro F E _ _ _ _ _ c h2 hne hinv hr Ω _ _ _ cc hcc art hart l _ ι χ n r hrc hlad ht
  classical
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x =>
    ⟨c.symm x, by rw [RingEquiv.symm_apply_eq, hcc, AlgEquiv.apply_symm_apply]⟩
  have hinv' : ∀ x, c.toRingEquiv (c.toRingEquiv x) = x := fun x => hinv x
  have hex := _root_.GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv
  choose conjPrime₂ hconjP using fun w => (hex w).exists
  have hconj2 : ∀ w, conjPrime₂ (conjPrime₂ w) = w := fun w =>
    (hex (conjPrime₂ w)).unique (hconjP (conjPrime₂ w)) (_root_.GlobalTheory.AntiLAdic.conjPl_symm hinv' (hconjP w))
  have hlfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hI : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors hI).subset (fun w hw => Ideal.dvd_span_singleton.mpr hw)
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ χ.UnrAt w ∨ (l : 𝓞 E) ∈ w.asIdeal}.Finite :=
    (_root_.GlobalTheory.Mem.UnrAe.finite_ramified χ).union hlfin
  set T := hfin.toFinset with hT
  have hgood : ∀ w ∉ T, χ.UnrAt w ∧ (l : 𝓞 E) ∉ w.asIdeal := by
    intro w hw
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hw
    exact hw
  let φ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (_root_.Formalism.ConjugateSelfDual.Qbar l)ˣ := (r.comp (_root_.GlobalTheory.AntiLAdic.conjHom cc hc)) * r
  have hφc : Continuous φ := by
    show Continuous (fun g => r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc g) * r g)
    exact (hrc.comp (_root_.GlobalTheory.AntiLAdic.continuous_conjHom cc hc)).mul hrc
  have hφ : φ = 1 := by
    refine _root_.GlobalTheory.FrobDense.eq_one_of_frob E Ω art hart _ φ hφc
      (T ∪ T.image conjPrime₂) ?_
    intro v hv A hA σ hσ
    rw [Finset.mem_union, not_or] at hv
    have hv' : conjPrime₂ v ∉ T := by
      intro hmemT
      exact hv.2 (Finset.mem_image.mpr ⟨conjPrime₂ v, hmemT, hconj2 v⟩)
    obtain ⟨hU, hl⟩ := hgood v hv.1
    obtain ⟨hU', hl'⟩ := hgood (conjPrime₂ v) hv'
    have hA' := _root_.GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl hcc (hconjP v) hA
    have hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob (F := E) (_root_.GlobalTheory.AntiRamConj.moveVal cc A) (_root_.Formalism.ConjugateSelfDual.normV (conjPrime₂ v))
        (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) := by
      rw [_root_.GlobalTheory.AntiLAdic.normV_conjPl (hconjP v)]
      exact _root_.GlobalTheory.AntiLAdic.isFrob_conjHom cc hc hσ
    have r1 := hlad.frob_unr hart (Or.inl hl) hU hA hσ
    have r2 := hlad.frob_unr hart (Or.inl hl') hU' hA' hσ'
    have hval := _root_.GlobalTheory.AntiLAdic.val_mul_val_conj c h2 hne hr χ ht (hconjP v) hU hU'
    show r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) * r σ = 1
    apply Units.ext
    rw [Units.val_mul, r1, r2, Units.val_one, ← mul_inv, ← map_mul, ← Units.val_mul,
      mul_comm (χ.val (conjPrime₂ v)), hval, Units.val_one, map_one, inv_one]
  intro g g' hg'
  have hgg : g' = _root_.GlobalTheory.AntiLAdic.conjHom cc hc g :=
    AlgEquiv.ext fun x => by rw [hg', _root_.GlobalTheory.AntiLAdic.conjHom_apply]
  have h1 : r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc g) * r g = 1 := DFunLike.congr_fun hφ g
  rw [hgg]
  exact eq_inv_of_mul_eq_one_left h1

end GlobalTheory.AntiLAdic
