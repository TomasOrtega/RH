import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBundlesAgree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace HeightOneSections

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
The claim follows from `((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩`.
-/
lemma genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

omit [IsIntegral X] in

/- English proof (translation)
Establish `h : hV.fromSpec p ∈ Set.range hV.fromSpec` using `⟨p, rfl⟩`. Rewrite `h` using `[hV.range_fromSpec]`. Then use the resulting hypothesis.
-/
lemma fromSpec_mem {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec p ∈ V := by
  have h : hV.fromSpec p ∈ Set.range hV.fromSpec := ⟨p, rfl⟩
  rwa [hV.range_fromSpec] at h

/- English proof (translation)
Use `IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_` and prove the remaining obligations. Establish `hy` using `fromSpec_mem hV ⟨P, hP.isPrime⟩`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec ⟨P, hP.isPrime⟩, hy⟩ : V)`. Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩)) P` using `hV.isLocalization_stalk' ⟨P, hP.isPrime⟩ hy`. Use `hN (hV.fromSpec ⟨P, hP.isPrime⟩)` as an intermediate fact.

Conclude with `IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩)) (Localization.AtPrime P)).toRingEquiv`.
-/
lemma isIntegrallyClosed_of_isAffineOpen (hN : IsNormalScheme X) {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  have hy := fromSpec_mem hV ⟨P, hP.isPrime⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hV.fromSpec ⟨P, hP.isPrime⟩, hy⟩ : V)
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hV.isLocalization_stalk' ⟨P, hP.isPrime⟩ hy
  have := hN (hV.fromSpec ⟨P, hP.isPrime⟩)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv

def comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens) (h : W ≤ V)
    (r : Fin n → Γ(X, W)) : Γ(E, W) :=
  ∑ i, r i • (E.presheaf.map (homOfLE h).op).hom (s i)

omit [IsIntegral X] in

/- English proof (translation)
Rewrite using `[comb, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[BundlesAgree.germ_smul']`. Use `congr 1`. Conclude with `TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE h) x hx (s i)`.
-/
lemma germ_comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens)
    (h : W ≤ V) (r : Fin n → Γ(X, W)) (x : X) (hx : x ∈ W) :
    E.presheaf.germ W x hx (comb E s W h r) =
      ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x (h hx) (s i) := by
  rw [comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul']
  congr 1
  exact TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE h) x hx (s i)

omit [IsIntegral X] in

/- English proof (translation)
Rewrite using `[comb, comb, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.map_smul]`. Use `congr 1`. Use `show (E.presheaf.map (homOfLE h).op ≫ E.presheaf.map (homOfLE h').op) (s i) = _`.

Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.
-/
lemma comb_res (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W W' : X.Opens)
    (h : W ≤ V) (h' : W' ≤ W) (r : Fin n → Γ(X, W)) :
    E.presheaf.map (homOfLE h').op (comb E s W h r) =
      comb E s W' (h'.trans h) (fun i => X.presheaf.map (homOfLE h').op (r i)) := by
  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  show (E.presheaf.map (homOfLE h).op ≫ E.presheaf.map (homOfLE h').op) (s i) = _
  rw [← Functor.map_comp]
  rfl

omit [IsIntegral X] in

/- English proof (translation)
Rewrite `e` using `[← germ_comb E s W h r x hx, ← germ_comb E s W' h' r' x hx']`. Take `⟨W'', hx'', iU, iV, e'⟩` from `E.presheaf.germ_eq x hx hx' _ _ e`. Establish `hU : iU = homOfLE iU.le` using `rfl`. Establish `hV : iV = homOfLE iV.le` using `rfl`. Rewrite `e'` using `[hU, hV, comb_res, comb_res]`.

Use `(hs W'' (iU.le.trans h)).1 e'` as an intermediate fact. Establish `hi` using `congrFun this i`. Rewrite using `[← TopCat.Presheaf.germ_res_apply X.presheaf iU x hx'' (r i), ← TopCat.Presheaf.germ_res_apply X.presheaf iV x hx'' (r' i)]`. Conclude with `congrArg (X.presheaf.germ W'' x hx'') hi`.
-/
lemma germ_coeff_unique (E : X.Modules) {V : X.Opens} {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (x : X) (hxV : x ∈ V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V)
    (hx : x ∈ W) (hx' : x ∈ W') (r : Fin n → Γ(X, W)) (r' : Fin n → Γ(X, W'))
    (e : ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x hxV (s i) =
      ∑ i, X.presheaf.germ W' x hx' (r' i) • E.presheaf.germ V x hxV (s i)) (i : Fin n) :
    X.presheaf.germ W x hx (r i) = X.presheaf.germ W' x hx' (r' i) := by
  rw [← germ_comb E s W h r x hx, ← germ_comb E s W' h' r' x hx'] at e
  obtain ⟨W'', hx'', iU, iV, e'⟩ := E.presheaf.germ_eq x hx hx' _ _ e
  have hU : iU = homOfLE iU.le := rfl
  have hV : iV = homOfLE iV.le := rfl
  rw [hU, hV, comb_res, comb_res] at e'
  have := (hs W'' (iU.le.trans h)).1 e'
  have hi := congrFun this i
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf iU x hx'' (r i),
    ← TopCat.Presheaf.germ_res_apply X.presheaf iV x hx'' (r' i)]
  exact congrArg (X.presheaf.germ W'' x hx'') hi

/- English proof (translation)
Establish `: Nonempty V` using `⟨⟨genericPoint X, hη⟩⟩`. Establish `: IsNoetherianRing Γ(X, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Use `isIntegrallyClosed_of_isAffineOpen hN hV` as an intermediate fact. Use `functionField_isFractionRing_of_isAffineOpen X V hV` as an intermediate fact. Take `⟨W0, hW0, t0, ht0⟩` from `E.presheaf.exists_germ_eq v`.

Establish `hW1 : genericPoint X ∈ W0 ⊓ V` using `⟨hW0, hη⟩`. Take `⟨r, hr⟩` from `(hs (W0 ⊓ V) inf_le_right).2 ((E.presheaf.map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op).hom t0)`. Establish `hvc : v = ∑ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) • E.presheaf.germ V (genericPoint X) hη (s i)`. Rewrite using `[← germ_comb E s (W0 ⊓ V) inf_le_right r _ hW1]`. Express the relevant statement in the definitionally equal form `v = E.presheaf.germ (W0 ⊓ V) _ hW1 (comb E s (W0 ⊓ V) inf_le_right r)`.

Rewrite using `[show comb E s (W0 ⊓ V) inf_le_right r = _ from hr, ← ht0]`. Conclude with `(TopCat.Presheaf.germ_res_apply E.presheaf _ _ hW1 t0).symm`. Establish `hmem : ∀ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) ∈ Subalgebra.toSubmodule (⊥ : Subalgebra Γ(X, V) X.functionField)`. Introduce `i`. Rewrite using `[hHOI Γ(X, V) X.functionField, Submodule.mem_iInf]`.

Introduce `p`. Rewrite using `[Submodule.mem_iInf]`. Introduce `hp1`. Establish `hy` using `fromSpec_mem hV p`. Set `y` to `hV.fromSpec p`.

Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)`. Establish `hloc : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal` using `hV.isLocalization_stalk' p hy`. Establish `hdim : ringKrullDim (X.presheaf.stalk y) = 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hp1]`. Both sides reduce to the same expression.

Take `⟨w, hw⟩` from `hv y hy hdim`. Take `⟨W2, hW2, t, rfl⟩` from `E.presheaf.exists_germ_eq w`. Establish `hη3 : genericPoint X ∈ W2 ⊓ V` using `genericPoint_mem (show y ∈ W2 ⊓ V from ⟨hW2, hy⟩)`. Take `⟨r', hr'⟩` from `(hs (W2 ⊓ V) inf_le_right).2 ((E.presheaf.map (homOfLE (inf_le_left : W2 ⊓ V ≤ W2)).op).hom t)`. Establish `hvc' : v = ∑ i, X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) • E.presheaf.germ V (genericPoint X) hη (s i)`.

Rewrite using `[← germ_comb E s (W2 ⊓ V) inf_le_right r' _ hη3]`. Express the relevant statement in the definitionally equal form `v = E.presheaf.germ (W2 ⊓ V) _ hη3 (comb E s (W2 ⊓ V) inf_le_right r')`. Rewrite using `[show comb E s (W2 ⊓ V) inf_le_right r' = _ from hr', ← hw]`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `TopCat.Presheaf.germ_stalkSpecializes_apply E.presheaf hW2 (genericPoint_specializes y) t`.

Establish `hc` using `germ_coeff_unique E hs _ hη inf_le_right inf_le_right hW1 hη3 r r' (hvc.symm.trans hvc') i`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj p.asIdeal.primeCompl (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i))`. Use `⟨b, b.2, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩` and prove the remaining obligations. Establish `hab'` using `congrArg (X.presheaf.stalkSpecializes (genericPoint_specializes y)) hab`. Rewrite `hab'` using `[map_mul]`.

Establish `h1 : X.presheaf.stalkSpecializes (genericPoint_specializes y) (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i)) = X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i)` using `TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _`. Establish `h2 : ∀ c : Γ(X, V), X.presheaf.stalkSpecializes (genericPoint_specializes y) (algebraMap Γ(X, V) (X.presheaf.stalk y) c) = algebraMap Γ(X, V) X.functionField c` using `fun c => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _`. Rewrite `hab'` using `[h1, h2, h2, ← hc]`. Rewrite using `[Algebra.smul_def, ← hab', mul_comm]`. Use `choose a ha using fun i => Algebra.mem_bot.mp (hmem i)`.

Use `⟨∑ i, a i • s i, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, hvc]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[BundlesAgree.germ_smul', ← ha i]`. Both sides reduce to the same expression.
-/
theorem exists_section_of_isBasisOn (hHOI : HeightOneIntersection.Statement)
    [IsLocallyNoetherian X] (hN : IsNormalScheme X) (E : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (v : E.presheaf.stalk (genericPoint X))
    (hv : ∀ y : X, y ∈ V → ringKrullDim (X.presheaf.stalk y) = 1 → v ∈ genericImage E y) :
    ∃ σ : Γ(E, V), E.presheaf.germ V (genericPoint X) hη σ = v := by
  have : Nonempty V := ⟨⟨genericPoint X, hη⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := isIntegrallyClosed_of_isAffineOpen hN hV
  have := functionField_isFractionRing_of_isAffineOpen X V hV

  obtain ⟨W0, hW0, t0, ht0⟩ := E.presheaf.exists_germ_eq v
  have hW1 : genericPoint X ∈ W0 ⊓ V := ⟨hW0, hη⟩
  obtain ⟨r, hr⟩ := (hs (W0 ⊓ V) inf_le_right).2
    ((E.presheaf.map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op).hom t0)
  have hvc : v = ∑ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) •
      E.presheaf.germ V (genericPoint X) hη (s i) := by
    rw [← germ_comb E s (W0 ⊓ V) inf_le_right r _ hW1]
    change v = E.presheaf.germ (W0 ⊓ V) _ hW1 (comb E s (W0 ⊓ V) inf_le_right r)
    rw [show comb E s (W0 ⊓ V) inf_le_right r = _ from hr, ← ht0]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf _ _ hW1 t0).symm

  have hmem : ∀ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) ∈
      Subalgebra.toSubmodule (⊥ : Subalgebra Γ(X, V) X.functionField) := by
    intro i
    rw [hHOI Γ(X, V) X.functionField, Submodule.mem_iInf]
    intro p
    rw [Submodule.mem_iInf]
    intro hp1
    have hy := fromSpec_mem hV p
    let y := hV.fromSpec p
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
      hV.isLocalization_stalk' p hy
    have hdim : ringKrullDim (X.presheaf.stalk y) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hp1]
      rfl
    obtain ⟨w, hw⟩ := hv y hy hdim
    obtain ⟨W2, hW2, t, rfl⟩ := E.presheaf.exists_germ_eq w
    have hη3 : genericPoint X ∈ W2 ⊓ V := genericPoint_mem (show y ∈ W2 ⊓ V from ⟨hW2, hy⟩)
    obtain ⟨r', hr'⟩ := (hs (W2 ⊓ V) inf_le_right).2
      ((E.presheaf.map (homOfLE (inf_le_left : W2 ⊓ V ≤ W2)).op).hom t)
    have hvc' : v = ∑ i, X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) •
        E.presheaf.germ V (genericPoint X) hη (s i) := by
      rw [← germ_comb E s (W2 ⊓ V) inf_le_right r' _ hη3]
      change v = E.presheaf.germ (W2 ⊓ V) _ hη3 (comb E s (W2 ⊓ V) inf_le_right r')
      rw [show comb E s (W2 ⊓ V) inf_le_right r' = _ from hr', ← hw]
      rw [TopCat.Presheaf.germ_res_apply]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply E.presheaf hW2
        (genericPoint_specializes y) t
    have hc := germ_coeff_unique E hs _ hη inf_le_right inf_le_right hW1 hη3 r r'
      (hvc.symm.trans hvc') i
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj p.asIdeal.primeCompl
      (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i))
    refine ⟨b, b.2, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
    have hab' := congrArg (X.presheaf.stalkSpecializes (genericPoint_specializes y)) hab
    rw [map_mul] at hab'
    have h1 : X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i)) = X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 : ∀ c : Γ(X, V), X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (algebraMap Γ(X, V) (X.presheaf.stalk y) c) = algebraMap Γ(X, V) X.functionField c :=
      fun c => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [h1, h2, h2, ← hc] at hab'
    rw [Algebra.smul_def, ← hab', mul_comm]
  choose a ha using fun i => Algebra.mem_bot.mp (hmem i)
  refine ⟨∑ i, a i • s i, ?_⟩
  rw [map_sum, hvc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul', ← ha i]
  rfl

end HeightOneSections

end

end GroundTheory.Heights₂.Heights.Model
