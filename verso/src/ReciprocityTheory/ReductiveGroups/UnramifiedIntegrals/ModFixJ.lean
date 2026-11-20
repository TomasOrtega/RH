import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModSepInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobCong
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Conclude with `add_mem ha hb`.
-/
theorem fixJ_nonunits_add {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : a ∈ A.nonunits)
    (hb : b ∈ A.nonunits) : a + b ∈ A.nonunits := by
  exact add_mem ha hb

def fixJRoots {Ω : Type*} [Field Ω] (P : Polynomial ℤ) : Finset Ω := (P.map (Int.castRingHom Ω)).roots.toFinset

/- English proof (translation)
Rewrite using `[fixJRoots, Multiset.mem_toFinset, Polynomial.mem_roots (hP.map _).ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map]`.
-/
theorem mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) (r : Ω) :
    r ∈ fixJRoots (Ω := Ω) P ↔ P.eval₂ (Int.castRingHom Ω) r = 0 := by
  rw [fixJRoots, Multiset.mem_toFinset, Polynomial.mem_roots (hP.map _).ne_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map]

/- English proof (translation)
Rewrite `hr`, the goal using `[mem_fixJRoots hP]`. Establish `h` using `Polynomial.hom_eval₂ P (Int.castRingHom Ω) (g : Ω →+* Ω) r`. Rewrite `h` using `[hr, map_zero, RingHom.ext_int ((g : Ω →+* Ω).comp (Int.castRingHom Ω)) (Int.castRingHom Ω)]`. Conclude with `h.symm`.
-/
theorem map_mem_fixJRoots {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic)
    (g : Ω ≃ₐ[E] Ω) {r : Ω} (hr : r ∈ fixJRoots (Ω := Ω) P) : g r ∈ fixJRoots (Ω := Ω) P := by
  rw [mem_fixJRoots hP] at hr ⊢
  have h := Polynomial.hom_eval₂ P (Int.castRingHom Ω) (g : Ω →+* Ω) r
  rw [hr, map_zero, RingHom.ext_int ((g : Ω →+* Ω).comp (Int.castRingHom Ω)) (Int.castRingHom Ω)] at h
  exact h.symm

/- English proof (translation)
Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_int_eq]`. Conclude with `(mem_fixJRoots hP r).1 hr`.
-/
theorem isIntegral_of_mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) {r : Ω}
    (hr : r ∈ fixJRoots (Ω := Ω) P) : IsIntegral ℤ r := by
  refine ⟨P, hP, ?_⟩
  rw [algebraMap_int_eq]
  exact (mem_fixJRoots hP r).1 hr

def fixJStab (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω] (P : Polynomial ℤ) : Subgroup (Ω ≃ₐ[E] Ω) where
  carrier := {g | ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb r hr
    rw [AlgEquiv.mul_apply, hb r hr, ha r hr]
  inv_mem' := by
    intro a ha r hr
    have := ha r hr
    calc a⁻¹ r = a⁻¹ (a r) := by rw [this]
      _ = r := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_fixJStab {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} {g : Ω ≃ₐ[E] Ω} :
    g ∈ fixJStab E Ω P ↔ ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r := Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `n hn g`. Rewrite `hn`, the goal using `[mem_fixJStab]`. Introduce `r hr`. Establish `h1 : g⁻¹ r ∈ fixJRoots (Ω` using `Ω) P := map_mem_fixJRoots hP g⁻¹ hr`.

Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel]`. Both sides reduce to the same expression.
-/
theorem fixJStab_normal {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic) :
    (fixJStab E Ω P).Normal := by
  constructor
  intro n hn g
  rw [mem_fixJStab] at hn ⊢
  intro r hr
  have h1 : g⁻¹ r ∈ fixJRoots (Ω := Ω) P := map_mem_fixJRoots hP g⁻¹ hr
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

/- English proof (translation)
Set `K : IntermediateField E Ω` to `IntermediateField.adjoin E ((fixJRoots (Ω := Ω) P : Finset Ω) : Set Ω)`. Use `haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)`. Use `Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[mem_fixJStab]`.

Introduce `r hr`. Conclude with `hg ⟨r, IntermediateField.subset_adjoin E _ hr⟩`.
-/
theorem fixJStab_isOpen {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω]
    {P : Polynomial ℤ} : IsOpen (fixJStab E Ω P : Set (Ω ≃ₐ[E] Ω)) := by
  let K : IntermediateField E Ω := IntermediateField.adjoin E ((fixJRoots (Ω := Ω) P : Finset Ω) : Set Ω)
  haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
  intro g hg
  rw [mem_fixJStab]
  intro r hr
  exact hg ⟨r, IntermediateField.subset_adjoin E _ hr⟩

/- English proof (translation)
Use `Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `Subgroup.isClosed_topologicalClosure _`.
-/
theorem fixJ_ker_isOpen (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E)) (hk : art.ker = hilbertSubgroup E Ω) :
    IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) := by
  refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
  rw [hk]
  exact Subgroup.isClosed_topologicalClosure _

/- English proof (translation)
Take `⟨art, -, hker, hfrob⟩` from `hH (KQ d) (Om d)`. Establish `hxi : IsIntegral ℤ x`. Take `⟨y, hy, hyi⟩` from `exists_Om d (cm1 d L hsf hd hL)`. Establish `: y = x` using `Subtype.ext (hy.trans hx.symm)`. Rewrite `hyi` using `[this]`. Then use the resulting hypothesis.

Take `⟨P, hP, hPx⟩` from `hxi`. Establish `hxs : x ∈ fixJRoots (Ω` using `Om d) P := by`. Rewrite using `[mem_fixJRoots hP]`. Rewrite `hPx` using `[show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _]`. Then use the resulting hypothesis. Take `⟨n, hn0, hn⟩` from `sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)`.

Use `set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS`. Establish `hSfin : S.Finite` using `finite_places (KQ d) hn0`. Establish `key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S → ∀ r ∈ fixJRoots (Ω` using `Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by`. Introduce `A v hA hv r hr r' hr' h`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hn r hr r' hr' hne A h`. Apply `hv` to reduce the goal to its premises. Rewrite using `[hS, Set.mem_ofPred_eq, ← hA]`. Simplify using `using h1`. Use `set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH`.

Use `fixJStab_normal (E := KQ d) (Ω := Om d) hP` as an intermediate fact. Establish `hHn : H.Normal` using `inferInstance`. Establish `hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d))`. Rewrite using `[hH, Subgroup.coe_inf]`. Conclude with `(fixJ_ker_isOpen _ _ art hker).inter fixJStab_isOpen`.

Take `⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩` from `hC (KQ d) (Om d) S hSfin H hHn hHo (by`. Introduce `A v hA hv g hg`. Use `⟨by rw [hker]; exact inertiaEl_mem_hilbert hg, fun r hr => ?_⟩` and prove the remaining obligations. Conclude with `key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ`. Establish `hσ1 : art σ = 1` using `by rw [← MonoidHom.mem_ker, hker]; exact hσ`.

Establish `hφ1 : art φ = 1`. Establish `: σ⁻¹ * φ ∈ art.ker` using `hσφ.1`. Rewrite `this` using `[MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul]`. Conclude with `this`. Establish `hcl` using `hfrob v A φ hA hφ`.

Rewrite `hcl` using `[hφ1]`. Establish `h1` using `frobCong hsf hd hL x hx A v hA hp hcl.symm`. Establish `h2` using `hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))`. Establish `h3 : φ x - x ∈ A.nonunits`. Use `fixJ_nonunits_add A h2 h1` as an intermediate fact.

Simplify using `using this`. Establish `h4 : φ x = x` using `key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3`. Establish `h5` using `hσφ.2 x hxs`. Rewrite `h5` using `[AlgEquiv.mul_apply, h4]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fixJ (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt)
    {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (σ : Om d ≃ₐ[KQ d] Om d) (hσ : σ ∈ hilbertSubgroup (KQ d) (Om d)) :
    σ x = x := by
  obtain ⟨art, -, hker, hfrob⟩ := hH (KQ d) (Om d)
  have hxi : IsIntegral ℤ x := by
    obtain ⟨y, hy, hyi⟩ := exists_Om d (cm1 d L hsf hd hL)
    have : y = x := Subtype.ext (hy.trans hx.symm)
    rwa [this] at hyi
  obtain ⟨P, hP, hPx⟩ := hxi
  have hxs : x ∈ fixJRoots (Ω := Om d) P := by
    rw [mem_fixJRoots hP]
    rwa [show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _] at hPx
  obtain ⟨n, hn0, hn⟩ := sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)
  set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS
  have hSfin : S.Finite := finite_places (KQ d) hn0

  have key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S →
      ∀ r ∈ fixJRoots (Ω := Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by
    intro A v hA hv r hr r' hr' h
    by_contra hne
    have h1 := hn r hr r' hr' hne A h
    apply hv
    rw [hS, Set.mem_ofPred_eq, ← hA]
    simpa using h1
  set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH
  have := fixJStab_normal (E := KQ d) (Ω := Om d) hP
  have hHn : H.Normal := inferInstance
  have hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d)) := by
    rw [hH, Subgroup.coe_inf]
    exact (fixJ_ker_isOpen _ _ art hker).inter fixJStab_isOpen
  obtain ⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩ := hC (KQ d) (Om d) S hSfin H hHn hHo (by
    intro A v hA hv g hg
    refine ⟨by rw [hker]; exact inertiaEl_mem_hilbert hg, fun r hr => ?_⟩
    exact key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr
      (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ
  have hσ1 : art σ = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hσ
  have hφ1 : art φ = 1 := by
    have : σ⁻¹ * φ ∈ art.ker := hσφ.1
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul] at this
    exact this
  have hcl := hfrob v A φ hA hφ
  rw [hφ1] at hcl
  have h1 := frobCong hsf hd hL x hx A v hA hp hcl.symm
  have h2 := hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))
  have h3 : φ x - x ∈ A.nonunits := by
    have := fixJ_nonunits_add A h2 h1
    simpa using this
  have h4 : φ x = x := key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3
  have h5 := hσφ.2 x hxs
  rw [AlgEquiv.mul_apply, h4] at h5
  calc σ x = σ (σ⁻¹ x) := by rw [h5]
    _ = x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl

end ReciprocityTheory.ChartRestriction.L1
