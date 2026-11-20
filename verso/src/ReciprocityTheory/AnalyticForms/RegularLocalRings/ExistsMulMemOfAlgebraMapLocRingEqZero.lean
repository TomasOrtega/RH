import ReciprocityTheory.AnalyticForms.RegularLocalRings.ClosureFromSpecMemCompsH
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

noncomputable section

section Loc

variable {m : ℕ}

/- English proof (translation)
Establish `hK : K ≤ ptIdeal p` using `fun h hh => (RingHom.mem_ker).2 (hp h hh)`. Establish `hJ : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K ≤ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p)` using `Ideal.map_mono hK`. Establish `hne : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) ≠ ⊤`. Rewrite using `[Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `Ideal.IsMaximal.ne_top inferInstance`.

Express the relevant statement in the definitionally equal form `IsUnit (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K) (algebraMap _ (locPt p) g)) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hu hg`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective v`.

Establish `h0 : (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)) (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p) g * b - 1) = 0`. Rewrite using `[map_sub, map_mul, map_one, hv, sub_self]`. Establish `h2` using `hJ (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Establish `h1 : algebraMap (MvPolynomial (Fin m) ℂ) (locPt p) g * b ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p)` using `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((RingHom.mem_ker).2 hg))`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h3` using `Ideal.sub_mem _ h1 h2`. Rewrite `h3` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Introduce `hg`. Use `IsUnit.map _ ?_` and prove the remaining obligations.

Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) g).2 (Ideal.mem_primeCompl_iff.2 fun hk => hg ((RingHom.mem_ker).1 hk))`.
-/
theorem isUnit_algebraMap_locRing_iff (K : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) (g : MvPolynomial (Fin m) ℂ) :
    IsUnit (algebraMap _ (locRing K p) g) ↔ eval p g ≠ 0 := by
  have hK : K ≤ ptIdeal p := fun h hh => (RingHom.mem_ker).2 (hp h hh)
  have hJ : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K ≤
      Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) := Ideal.map_mono hK
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) ≠ ⊤ := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.IsMaximal.ne_top inferInstance
  change IsUnit (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)
    (algebraMap _ (locPt p) g)) ↔ _
  constructor
  · intro hu hg
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have h0 : (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K))
        (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p) g * b - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hv, sub_self]
    have h2 := hJ (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : algebraMap (MvPolynomial (Fin m) ℂ) (locPt p) g * b ∈
        Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) :=
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((RingHom.mem_ker).2 hg))
    apply hne
    rw [Ideal.eq_top_iff_one]
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at h3
  · intro hg
    refine IsUnit.map _ ?_
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) g).2
      (Ideal.mem_primeCompl_iff.2 fun hk => hg ((RingHom.mem_ker).1 hk))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K) (algebraMap _ (locPt p) t) = 0 at ht`. Rewrite `ht` using `[Ideal.Quotient.eq_zero_iff_mem]`. Take `⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩` from `(IsLocalization.mem_map_algebraMap_iff (ptIdeal p).primeCompl (locPt p)).1 ht`. Simplify using `only at h`. Rewrite `h` using `[← map_mul]`.

Take `⟨⟨c, hc⟩, hc'⟩` from `(IsLocalization.eq_iff_exists (ptIdeal p).primeCompl (locPt p)).1 h`. Simplify using `only at hc'`. Use `⟨c * s, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : eval p c ≠ 0` using `fun h0 => Ideal.mem_primeCompl_iff.1 hc ((RingHom.mem_ker).2 h0)`. Establish `h2 : eval p s ≠ 0` using `fun h0 => Ideal.mem_primeCompl_iff.1 hs ((RingHom.mem_ker).2 h0)`.

Rewrite using `[map_mul]`. Conclude with `mul_ne_zero h1 h2`. Establish `h3 : c * s * t = c * a` using `by rw [← hc']; ring`. Rewrite using `[h3]`. Conclude with `Ideal.mul_mem_left _ _ ha`.
-/
theorem exists_mul_mem_of_algebraMap_locRing_eq_zero (K : Ideal (MvPolynomial (Fin m) ℂ))
    (p : Fin m → ℂ) {t : MvPolynomial (Fin m) ℂ} (ht : algebraMap _ (locRing K p) t = 0) :
    ∃ s, eval p s ≠ 0 ∧ s * t ∈ K := by
  change Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)
    (algebraMap _ (locPt p) t) = 0 at ht
  rw [Ideal.Quotient.eq_zero_iff_mem] at ht
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (ptIdeal p).primeCompl (locPt p)).1 ht
  simp only at h
  rw [← map_mul] at h
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (ptIdeal p).primeCompl (locPt p)).1 h
  simp only at hc'
  refine ⟨c * s, ?_, ?_⟩
  · have h1 : eval p c ≠ 0 := fun h0 => Ideal.mem_primeCompl_iff.1 hc ((RingHom.mem_ker).2 h0)
    have h2 : eval p s ≠ 0 := fun h0 => Ideal.mem_primeCompl_iff.1 hs ((RingHom.mem_ker).2 h0)
    rw [map_mul]
    exact mul_ne_zero h1 h2
  · have h3 : c * s * t = c * a := by rw [← hc']; ring
    rw [h3]
    exact Ideal.mul_mem_left _ _ ha

end Loc

variable {W : Scheme.{0}}

/- English proof (translation)
Establish `hB : Opens.IsBasis W.affineOpens` using `by first`. Consider the case `exact isBasis_affine_open W`. Consider the case `exact isBasis_affineOpens W`. Consider the case `exact W.isBasis_affineOpens`. Consider the case `exact Scheme.isBasis_affineOpens W`.

Consider the case `exact AlgebraicGeometry.Scheme.isBasis_affine_open W`. Take `⟨O, hO, hxO, hOle⟩` from `(Opens.isBasis_iff_nbhd.1 hB) (show x ∈ U.1 ⊓ V.1 from ⟨hU, hV⟩)`. Set `O' : W.affineOpens` to `⟨O, hO⟩`. Establish `hOU : O' ≤ U` using `fun y hy => (hOle hy).1`. Establish `hOV : O' ≤ V` using `fun y hy => (hOle hy).2`.

Establish `key : ∀ (A : W.affineOpens) (hA : O' ≤ A) (hxA : x ∈ A.1), (Z.ideal A).map (W.presheaf.germ A.1 x hxA).hom = (Z.ideal O').map (W.presheaf.germ O x hxO).hom`. Introduce `A hA hxA`. Rewrite using `[← Z.map_ideal hA, Ideal.map_map, ← CommRingCat.hom_comp]`. Use `congr 2`. Conclude with `(TopCat.Presheaf.germ_res _ _ _ _).symm`.

Rewrite using `[key V hOV hV, key U hOU hU]`.
-/
theorem stalkIdeal_eq (Z : W.IdealSheafData) (U V : W.affineOpens) (x : W) (hU : x ∈ U.1)
    (hV : x ∈ V.1) : (Z.ideal V).map (W.presheaf.germ V.1 x hV).hom =
      (Z.ideal U).map (W.presheaf.germ U.1 x hU).hom := by
  have hB : Opens.IsBasis W.affineOpens := by
    first
    | exact isBasis_affine_open W
    | exact isBasis_affineOpens W
    | exact W.isBasis_affineOpens
    | exact Scheme.isBasis_affineOpens W
    | exact AlgebraicGeometry.Scheme.isBasis_affine_open W
  obtain ⟨O, hO, hxO, hOle⟩ :=
    (Opens.isBasis_iff_nbhd.1 hB) (show x ∈ U.1 ⊓ V.1 from ⟨hU, hV⟩)
  let O' : W.affineOpens := ⟨O, hO⟩
  have hOU : O' ≤ U := fun y hy => (hOle hy).1
  have hOV : O' ≤ V := fun y hy => (hOle hy).2
  have key : ∀ (A : W.affineOpens) (hA : O' ≤ A) (hxA : x ∈ A.1),
      (Z.ideal A).map (W.presheaf.germ A.1 x hxA).hom =
        (Z.ideal O').map (W.presheaf.germ O x hxO).hom := by
    intro A hA hxA
    rw [← Z.map_ideal hA, Ideal.map_map, ← CommRingCat.hom_comp]
    congr 2
    exact (TopCat.Presheaf.germ_res _ _ _ _).symm
  rw [key V hOV hV, key U hOU hU]

/- English proof (translation)
Use `letI := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : V)`. Use `haveI := hV.isLocalization_stalk ⟨x, hx⟩`. Establish `ht' : algebraMap Γ(W, V) (W.presheaf.stalk x) t ∈ Ideal.map (algebraMap Γ(W, V) (W.presheaf.stalk x)) I` using `ht`. Take `⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩` from `(IsLocalization.mem_map_algebraMap_iff (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (W.presheaf.stalk x)).1 ht'`. Simplify using `only at h`.

Rewrite `h` using `[← map_mul]`. Take `⟨⟨c, hc⟩, hc'⟩` from `(IsLocalization.eq_iff_exists (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (W.presheaf.stalk x)).1 h`. Simplify using `only at hc'`. Use `⟨c * s, ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap Γ(W, V) (W.presheaf.stalk x) (c * s))` using `(IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x) _ (c * s)).2 ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl.mul_mem hc hs)`.

Conclude with `hu`. Establish `h3 : c * s * t = c * a` using `by rw [← hc']; ring`. Rewrite using `[h3]`. Conclude with `Ideal.mul_mem_left _ _ ha`.
-/
theorem exists_unit_mul_mem_of_germ_mem {V : W.Opens} (hV : IsAffineOpen V) (x : W) (hx : x ∈ V)
    (I : Ideal Γ(W, V)) {t : Γ(W, V)} (ht : W.presheaf.germ V x hx t ∈ I.map (W.presheaf.germ V x hx).hom) :
    ∃ d : Γ(W, V), IsUnit (W.presheaf.germ V x hx d) ∧ d * t ∈ I := by
  letI := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  have ht' : algebraMap Γ(W, V) (W.presheaf.stalk x) t ∈
      Ideal.map (algebraMap Γ(W, V) (W.presheaf.stalk x)) I := ht
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (W.presheaf.stalk x)).1 ht'
  simp only at h
  rw [← map_mul] at h
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (W.presheaf.stalk x)).1 h
  simp only at hc'
  refine ⟨c * s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(W, V) (W.presheaf.stalk x) (c * s)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x) _ (c * s)).2
        ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl.mul_mem hc hs)
    exact hu
  · have h3 : c * s * t = c * a := by rw [← hc']; ring
    rw [h3]
    exact Ideal.mul_mem_left _ _ ha

/- English proof (translation)
Unfold `IsBranchH at hb ⊢`. Take `⟨hC, hyC, hirr, hηU, hηZ⟩` from `hb`. Take `⟨U₁, hy1, t, ht⟩` from `W.presheaf.germ_exist u`. Establish `e1 : W.presheaf.germ (U ⊓ U₁) y (show y ∈ U ⊓ U₁ from ⟨hyU, hy1⟩) (W.presheaf.map (homOfLE inf_le_left).op s * W.presheaf.map (homOfLE inf_le_right).op t) = W.presheaf.germ U y hyU s * u`. Rewrite using `[map_mul]`.

Use `first`. Consider the case `(erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht])`. Consider the case `(simp only [TopCat.Presheaf.germ_res_apply, ht])`. Take `⟨O₀, hyO₀, i₁, i₂, hO₀⟩` from `W.presheaf.germ_eq y hyV (show y ∈ U ⊓ U₁ from ⟨hyU, hy1⟩) s' _ (heq.trans e1.symm)`. Establish `hsp : (IsIrreducible.genericPoint hirr) ⤳ y` using `by first`.

Consider the case `exact (IsIrreducible.isGenericPoint_genericPoint_closure hirr).specializes (subset_closure hyC)`. Consider the case `exact (IsIrreducible.genericPoint_spec hirr).specializes (subset_closure hyC)`. Establish `hηO : (IsIrreducible.genericPoint hirr) ∈ O₀` using `hsp.mem_open O₀.isOpen hyO₀`. Establish `hzV : (IsIrreducible.genericPoint hirr) ∈ V` using `i₁.le hηO`. Establish `hz1 : (IsIrreducible.genericPoint hirr) ∈ U₁` using `(i₂.le hηO).2`.

Establish `hg : W.presheaf.germ V (IsIrreducible.genericPoint hirr) hzV s' = W.presheaf.germ U (IsIrreducible.genericPoint hirr) hηU s * W.presheaf.germ U₁ (IsIrreducible.genericPoint hirr) hz1 t`. Establish `h1` using `congrArg (W.presheaf.germ O₀ (IsIrreducible.genericPoint hirr) hηO) hO₀`. Use `first`. Consider the case `(erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1; exact h1)`. Consider the case `(simp only [TopCat.Presheaf.germ_res_apply, map_mul] at h1; exact h1)`.

Use `⟨hC, hyC, hirr, hzV, ?_⟩` and prove the remaining obligations. Simplify using `only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe] at hηZ ⊢`. Rewrite `hηZ` using `[Scheme.mem_basicOpen _ _ _ hηU]`. Rewrite using `[Scheme.mem_basicOpen _ _ _ hzV, hg, IsUnit.mul_iff]`. Conclude with `fun h => hηZ h.1`.
-/
theorem isBranch_of_germ {T : Set W} (hT : IsClosed T) {U V : W.Opens} {s : Γ(W, U)}
    {s' : Γ(W, V)} {y : W} (hyU : y ∈ U) (hyV : y ∈ V) {C : Set W} (hb : IsBranchH T s y C)
    (u : W.presheaf.stalk y) (heq : W.presheaf.germ V y hyV s' = W.presheaf.germ U y hyU s * u) :
    IsBranchH T s' y C := by
  unfold IsBranchH at hb ⊢
  obtain ⟨hC, hyC, hirr, hηU, hηZ⟩ := hb
  obtain ⟨U₁, hy1, t, ht⟩ := W.presheaf.germ_exist u
  have e1 : W.presheaf.germ (U ⊓ U₁) y (show y ∈ U ⊓ U₁ from ⟨hyU, hy1⟩)
      (W.presheaf.map (homOfLE inf_le_left).op s * W.presheaf.map (homOfLE inf_le_right).op t) =
      W.presheaf.germ U y hyU s * u := by
    rw [map_mul]
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht])
    | (simp only [TopCat.Presheaf.germ_res_apply, ht])
  obtain ⟨O₀, hyO₀, i₁, i₂, hO₀⟩ :=
    W.presheaf.germ_eq y hyV (show y ∈ U ⊓ U₁ from ⟨hyU, hy1⟩) s' _ (heq.trans e1.symm)
  have hsp : (IsIrreducible.genericPoint hirr) ⤳ y := by
    first
    | exact (IsIrreducible.isGenericPoint_genericPoint_closure hirr).specializes (subset_closure hyC)
    | exact (IsIrreducible.genericPoint_spec hirr).specializes (subset_closure hyC)
  have hηO : (IsIrreducible.genericPoint hirr) ∈ O₀ := hsp.mem_open O₀.isOpen hyO₀
  have hzV : (IsIrreducible.genericPoint hirr) ∈ V := i₁.le hηO
  have hz1 : (IsIrreducible.genericPoint hirr) ∈ U₁ := (i₂.le hηO).2
  have hg : W.presheaf.germ V (IsIrreducible.genericPoint hirr) hzV s' =
      W.presheaf.germ U (IsIrreducible.genericPoint hirr) hηU s * W.presheaf.germ U₁ (IsIrreducible.genericPoint hirr) hz1 t := by
    have h1 := congrArg (W.presheaf.germ O₀ (IsIrreducible.genericPoint hirr) hηO) hO₀
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul,
        TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1; exact h1)
    | (simp only [TopCat.Presheaf.germ_res_apply, map_mul] at h1; exact h1)
  refine ⟨hC, hyC, hirr, hzV, ?_⟩
  simp only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe] at hηZ ⊢
  rw [Scheme.mem_basicOpen _ _ _ hηU] at hηZ
  rw [Scheme.mem_basicOpen _ _ _ hzV, hg, IsUnit.mul_iff]
  exact fun h => hηZ h.1

/- English proof (translation)
Take `⟨U₁, hx1, t, ht⟩` from `W.presheaf.germ_exist u`. Establish `hxt : x ∈ W.basicOpen t` using `(Scheme.mem_basicOpen _ _ x hx1).2 (by rw [ht]; exact hu)`. Establish `e1 : W.presheaf.germ (U ⊓ U₁) x ⟨hxU, hx1⟩ (W.presheaf.map (homOfLE inf_le_left).op s * W.presheaf.map (homOfLE inf_le_right).op t) = W.presheaf.germ U x hxU s * u`. Rewrite using `[map_mul]`. Use `first`.

Consider the case `(erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht])`. Consider the case `(simp only [TopCat.Presheaf.germ_res_apply, ht])`. Consider the case `(simp only [Scheme.germ_res_apply, ht])`. Take `⟨O₀, hxO₀, i₁, i₂, hO₀⟩` from `W.presheaf.germ_eq x hxV (show x ∈ U ⊓ U₁ from ⟨hxU, hx1⟩) s' _ (heq.trans e1.symm)`. Use `⟨O₀ ⊓ W.basicOpen t, ⟨hxO₀, hxt⟩, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `hzV : z ∈ V` using `i₁.le hz.1`. Establish `hzU : z ∈ U` using `(i₂.le hz.1).1`. Establish `hz1 : z ∈ U₁` using `(i₂.le hz.1).2`. Establish `hg : W.presheaf.germ V z hzV s' = W.presheaf.germ U z hzU s * W.presheaf.germ U₁ z hz1 t`. Establish `h1` using `congrArg (W.presheaf.germ O₀ z hz.1) hO₀`.

Use `first`. Consider the case `(erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1; exact h1)`. Consider the case `(simp only [TopCat.Presheaf.germ_res_apply, map_mul] at h1; exact h1)`. Consider the case `(simp only [Scheme.germ_res_apply, map_mul] at h1; exact h1)`. Establish `hunit : IsUnit (W.presheaf.germ U₁ z hz1 t)` using `(Scheme.mem_basicOpen _ _ z hz1).1 hz.2`.

Simplify using `only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe]`. Rewrite using `[Scheme.mem_basicOpen _ _ z hzU, Scheme.mem_basicOpen _ _ z hzV, hg, IsUnit.mul_iff]`. Conclude with `not_congr ⟨fun h => ⟨h, hunit⟩, fun h => h.1⟩`.
-/
theorem exists_nbhd_zeroLocus {U V : W.Opens} {x : W} (hxU : x ∈ U) (hxV : x ∈ V) (s : Γ(W, U))
    (s' : Γ(W, V)) (u : W.presheaf.stalk x) (hu : IsUnit u)
    (heq : W.presheaf.germ V x hxV s' = W.presheaf.germ U x hxU s * u) :
    ∃ O : W.Opens, x ∈ O ∧ ∀ z ∈ O, (z ∈ W.zeroLocus {s} ↔ z ∈ W.zeroLocus {s'}) := by
  obtain ⟨U₁, hx1, t, ht⟩ := W.presheaf.germ_exist u
  have hxt : x ∈ W.basicOpen t := (Scheme.mem_basicOpen _ _ x hx1).2 (by rw [ht]; exact hu)
  have e1 : W.presheaf.germ (U ⊓ U₁) x ⟨hxU, hx1⟩
      (W.presheaf.map (homOfLE inf_le_left).op s * W.presheaf.map (homOfLE inf_le_right).op t) =
      W.presheaf.germ U x hxU s * u := by
    rw [map_mul]
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht])
    | (simp only [TopCat.Presheaf.germ_res_apply, ht])
    | (simp only [Scheme.germ_res_apply, ht])
  obtain ⟨O₀, hxO₀, i₁, i₂, hO₀⟩ := W.presheaf.germ_eq x hxV (show x ∈ U ⊓ U₁ from ⟨hxU, hx1⟩) s' _ (heq.trans e1.symm)
  refine ⟨O₀ ⊓ W.basicOpen t, ⟨hxO₀, hxt⟩, fun z hz => ?_⟩
  have hzV : z ∈ V := i₁.le hz.1
  have hzU : z ∈ U := (i₂.le hz.1).1
  have hz1 : z ∈ U₁ := (i₂.le hz.1).2
  have hg : W.presheaf.germ V z hzV s' =
      W.presheaf.germ U z hzU s * W.presheaf.germ U₁ z hz1 t := by
    have h1 := congrArg (W.presheaf.germ O₀ z hz.1) hO₀
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul,
        TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1; exact h1)
    | (simp only [TopCat.Presheaf.germ_res_apply, map_mul] at h1; exact h1)
    | (simp only [Scheme.germ_res_apply, map_mul] at h1; exact h1)
  have hunit : IsUnit (W.presheaf.germ U₁ z hz1 t) := (Scheme.mem_basicOpen _ _ z hz1).1 hz.2
  simp only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe]
  rw [Scheme.mem_basicOpen _ _ z hzU, Scheme.mem_basicOpen _ _ z hzV, hg, IsUnit.mul_iff]
  exact not_congr ⟨fun h => ⟨h, hunit⟩, fun h => h.1⟩

section Chart

variable {s : W ⟶ Spec (.of ℂ)}

/- English proof (translation)
Use `haveI : IsIso P.iso.hom.appTop := inferInstanceAs (IsIso (P.iso.hom.app ⊤))`. Unfold `AffPres.secHom`. Simplify using `only [RingHom.coe_comp]`. Conclude with `(ConcreteCategory.bijective_of_isIso _).2.comp ((ConcreteCategory.bijective_of_isIso _).2.comp ((ConcreteCategory.bijective_of_isIso _).2.comp Ideal.Quotient.mk_surjective))`.
-/
theorem secHom_surjective (P : AffPres s) : Function.Surjective P.secHom := by
  haveI : IsIso P.iso.hom.appTop := inferInstanceAs (IsIso (P.iso.hom.app ⊤))
  unfold AffPres.secHom
  simp only [RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp ((ConcreteCategory.bijective_of_isIso _).2.comp
    ((ConcreteCategory.bijective_of_isIso _).2.comp Ideal.Quotient.mk_surjective))

/- English proof (translation)
Introduce `h hh`. Assume the negation of the conclusion as `hne`. Establish `hu : IsUnit (algebraMap _ (locPt p) h)` using `(IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) h).2 (Ideal.mem_primeCompl_iff.2 fun hk => hne ((RingHom.mem_ker).1 hk))`. Establish `hmem : algebraMap _ (locPt p) h ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K` using `Ideal.mem_map_of_mem _ hh`. Establish `htop` using `Ideal.eq_top_of_isUnit_mem _ hmem hu`.

Establish `h1 : (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)) 1 = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, htop]`. Conclude with `Submodule.mem_top`. Rewrite `h1` using `[map_one]`. Conclude with `one_ne_zero h1`.
-/
private theorem eval_eq_zero_of_mem_of_nontrivial_locRing {m : ℕ} (K : Ideal (MvPolynomial (Fin m) ℂ))
    (p : Fin m → ℂ) [Nontrivial (locRing K p)] : ∀ h ∈ K, eval p h = 0 := by
  intro h hh
  by_contra hne
  have hu : IsUnit (algebraMap _ (locPt p) h) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) h).2
      (Ideal.mem_primeCompl_iff.2 fun hk => hne ((RingHom.mem_ker).1 hk))
  have hmem : algebraMap _ (locPt p) h ∈
      Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K := Ideal.mem_map_of_mem _ hh
  have htop := Ideal.eq_top_of_isUnit_mem _ hmem hu
  have h1 : (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)) 1 = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, htop]
    exact Submodule.mem_top
  rw [map_one] at h1
  exact one_ne_zero h1

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `P.exists_stalkEquiv y hy hc`. Use `haveI : Nontrivial (locRing P.K (P.coord y hy)) := ψ.symm.toEquiv.nontrivial`. Rewrite using `[← isUnit_algebraMap_locRing_iff P.K (P.coord y hy) (eval_eq_zero_of_mem_of_nontrivial_locRing _ _) g, ← hψ g]`. Conclude with `⟨fun h => h.map ψ, fun h => by simpa using h.map ψ.symm⟩`.
-/
theorem germ_unit_iff (P : AffPres s) (y : W) (hy : y ∈ P.V) (hc : IsClosed ({y} : Set W))
    (g : MvPolynomial (Fin P.n) ℂ) :
    IsUnit (W.presheaf.germ P.V y hy (P.secHom g)) ↔ eval (P.coord y hy) g ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := P.exists_stalkEquiv y hy hc
  haveI : Nontrivial (locRing P.K (P.coord y hy)) := ψ.symm.toEquiv.nontrivial
  rw [← isUnit_algebraMap_locRing_iff P.K (P.coord y hy) (eval_eq_zero_of_mem_of_nontrivial_locRing _ _) g,
    ← hψ g]
  exact ⟨fun h => h.map ψ, fun h => by simpa using h.map ψ.symm⟩

/- English proof (translation)
Establish `key : y ∈ W.zeroLocus {P.secHom g} ↔ ¬ IsUnit (W.presheaf.germ P.V y hy (P.secHom g))`. Simplify using `only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe]`. Conclude with `not_congr (Scheme.mem_basicOpen _ _ y hy)`. Rewrite using `[key, germ_unit_iff P y hy hc g, not_not]`.
-/
theorem mem_zeroLocus_secHom_iff (P : AffPres s) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (g : MvPolynomial (Fin P.n) ℂ) :
    y ∈ W.zeroLocus {P.secHom g} ↔ eval (P.coord y hy) g = 0 := by
  have key : y ∈ W.zeroLocus {P.secHom g} ↔ ¬ IsUnit (W.presheaf.germ P.V y hy (P.secHom g)) := by
    simp only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe]
    exact not_congr (Scheme.mem_basicOpen _ _ y hy)
  rw [key, germ_unit_iff P y hy hc g, not_not]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← h i]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨c, hc⟩` from `(hw i).exists_right_inv`. Establish `hv : v i = u i * c` using `by rw [← h i, mul_assoc, hc, mul_one]`. Rewrite using `[hv]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)`.
-/
theorem span_range_eq_of_mul_unit {R : Type*} [CommRing R] {ι : Type*} (u v w : ι → R)
    (hw : ∀ i, IsUnit (w i)) (h : ∀ i, v i * w i = u i) :
    Ideal.span (Set.range u) = Ideal.span (Set.range v) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← h i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := (hw i).exists_right_inv
    have hv : v i = u i * c := by rw [← h i, mul_assoc, hc, mul_one]
    rw [hv]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `hpK : ∀ h ∈ P.K, eval (P.coord x hx) h = 0` using `P.eval_coord_eq_zero x hx hcl`. Establish `h1mem : W.presheaf.germ P.V x hx (P.secHom (∏ l ∈ J, a l)) ∈ I.map (W.presheaf.germ P.V x hx).hom`. Rewrite using `[hst]`. Conclude with `Ideal.mem_span_singleton.mpr ⟨_, ht⟩`. Take `⟨d₁, hd₁u, hd₁⟩` from `exists_unit_mul_mem_of_germ_mem hV x hx I h1mem`.

Take `⟨h₁, rfl⟩` from `secHom_surjective P d₁`. Establish `hh₁ : eval (P.coord x hx) h₁ ≠ 0` using `(germ_unit_iff P x hx hcl h₁).mp hd₁u`. Establish `hmemb : h₁ * ∏ l ∈ J, a l ∈ I.comap P.secHom`. Rewrite using `[Ideal.mem_comap, map_mul]`. Conclude with `hd₁`.

Establish `hper : ∀ g ∈ I.comap P.secHom, ∃ hg, eval (P.coord x hx) hg ≠ 0 ∧ hg * g ∈ Ideal.span {∏ l ∈ J, a l} ⊔ P.K`. Introduce `g hg`. Establish `hg2 : W.presheaf.germ P.V x hx (P.secHom g) ∈ Ideal.span {t}`. Rewrite using `[← hst]`. Conclude with `Ideal.mem_map_of_mem _ hg`.

Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.mp hg2`. Establish `hψg : algebraMap _ (locRing P.K (P.coord x hx)) g = P.stalkEquiv x hx hcl t * P.stalkEquiv x hx hcl w`. Rewrite using `[← P.stalkEquiv_germ, hw, map_mul]`. Establish `hbu' : IsUnit (algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, b l))` using `(isUnit_algebraMap_locRing_iff _ _ hpK _).mpr (by`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun l _ => hb l)`. Take `⟨v, hv⟩` from `hbu'.exists_right_inv`. Establish `hgd : algebraMap _ (locRing P.K (P.coord x hx)) g = algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, a l) * (v * P.stalkEquiv x hx hcl w)`. Rewrite using `[hψg, ← hprod]`. Take the linear combination `(-(P.stalkEquiv x hx hcl t * P.stalkEquiv x hx hcl w)) * hv`.

Take `⟨c', d', hd', hcd⟩` from `exists_mk_locRing P.K (P.coord x hx) (v * P.stalkEquiv x hx hcl w)`. Establish `hz : algebraMap _ (locRing P.K (P.coord x hx)) (g * d' - (∏ l ∈ J, a l) * c') = 0`. Rewrite using `[map_sub, map_mul, map_mul, hgd, ← hcd]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s', hs', hs'K⟩` from `exists_mul_mem_of_algebraMap_locRing_eq_zero P.K (P.coord x hx) hz`.

Use `⟨s' * d', by rw [map_mul]; exact mul_ne_zero hs' hd', ?_⟩` and prove the remaining obligations. Establish `: s' * d' * g = s' * (g * d' - (∏ l ∈ J, a l) * c') + (s' * c') * (∏ l ∈ J, a l)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_right hs'K) (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)))`.

Use `choose! hgf hgf1 hgf2 using hper`. Take `⟨gens, hgens⟩` from `(IsNoetherian.noetherian (I.comap P.secHom) : (I.comap P.secHom).FG)`. Establish `hgmem : ∀ g ∈ gens, g ∈ I.comap P.secHom` using `fun g hg => hgens ▸ Submodule.subset_span hg`. Use `⟨h₁ * ∏ g ∈ gens, hgf g, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_prod]`.

Conclude with `mul_ne_zero hh₁ (Finset.prod_ne_zero_iff.mpr fun g hg => hgf1 g (hgmem g hg))`. Establish `: (h₁ * ∏ g ∈ gens, hgf g) * ∏ l ∈ J, a l = (∏ g ∈ gens, hgf g) * (h₁ * ∏ l ∈ J, a l)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hmemb`.

Introduce `g hg`. Rewrite `hg` using `[← hgens]`. Use `Submodule.span_induction (p := fun g _ => (h₁ * ∏ g ∈ gens, hgf g) * g ∈ Ideal.span {∏ l ∈ J, a l} ⊔ P.K) ?_ ?_ ?_ ?_ hg` and prove the remaining obligations. Introduce `g hgs`. Establish `hsplit : (h₁ * ∏ g ∈ gens, hgf g) * g = (h₁ * ∏ g' ∈ gens.erase g, hgf g') * (hgf g * g)`.

Rewrite using `[← Finset.mul_prod_erase gens hgf hgs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Conclude with `Ideal.mul_mem_left _ _ (hgf2 g (hgmem g hgs))`. Simplify using the standard rewrite rules.

Introduce `u v _ _ hu hv`. Rewrite using `[mul_add]`. Conclude with `Ideal.add_mem _ hu hv`. Introduce `r u _ hu`. Rewrite using `[smul_eq_mul, mul_left_comm]`.

Conclude with `Ideal.mul_mem_left _ _ hu`.
-/
theorem exists_den (P : AffPres s) (x : W) (hx : x ∈ P.V) (hcl : IsClosed ({x} : Set W))
    (hV : IsAffineOpen P.V) (I : Ideal Γ(W, P.V)) {ι : Type*} (J : Finset ι)
    (a b : ι → MvPolynomial (Fin P.n) ℂ) (hb : ∀ l, eval (P.coord x hx) (b l) ≠ 0)
    (t : W.presheaf.stalk x) (hst : I.map (W.presheaf.germ P.V x hx).hom = Ideal.span {t})
    (ht : W.presheaf.germ P.V x hx (P.secHom (∏ l ∈ J, a l)) =
      t * ∏ l ∈ J, W.presheaf.germ P.V x hx (P.secHom (b l)))
    (hprod : P.stalkEquiv x hx hcl t * algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, b l) =
      algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, a l)) :
    ∃ h, eval (P.coord x hx) h ≠ 0 ∧ h * ∏ l ∈ J, a l ∈ I.comap P.secHom ∧
      ∀ g ∈ I.comap P.secHom, h * g ∈ Ideal.span {∏ l ∈ J, a l} ⊔ P.K := by
  classical
  have hpK : ∀ h ∈ P.K, eval (P.coord x hx) h = 0 := P.eval_coord_eq_zero x hx hcl
  have h1mem : W.presheaf.germ P.V x hx (P.secHom (∏ l ∈ J, a l)) ∈
      I.map (W.presheaf.germ P.V x hx).hom := by
    rw [hst]
    exact Ideal.mem_span_singleton.mpr ⟨_, ht⟩
  obtain ⟨d₁, hd₁u, hd₁⟩ := exists_unit_mul_mem_of_germ_mem hV x hx I h1mem
  obtain ⟨h₁, rfl⟩ := secHom_surjective P d₁
  have hh₁ : eval (P.coord x hx) h₁ ≠ 0 := (germ_unit_iff P x hx hcl h₁).mp hd₁u
  have hmemb : h₁ * ∏ l ∈ J, a l ∈ I.comap P.secHom := by
    rw [Ideal.mem_comap, map_mul]
    exact hd₁
  have hper : ∀ g ∈ I.comap P.secHom, ∃ hg, eval (P.coord x hx) hg ≠ 0 ∧
      hg * g ∈ Ideal.span {∏ l ∈ J, a l} ⊔ P.K := by
    intro g hg
    have hg2 : W.presheaf.germ P.V x hx (P.secHom g) ∈ Ideal.span {t} := by
      rw [← hst]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hg2
    have hψg : algebraMap _ (locRing P.K (P.coord x hx)) g =
        P.stalkEquiv x hx hcl t * P.stalkEquiv x hx hcl w := by
      rw [← P.stalkEquiv_germ, hw, map_mul]
    have hbu' : IsUnit (algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, b l)) :=
      (isUnit_algebraMap_locRing_iff _ _ hpK _).mpr (by
        rw [map_prod]
        exact Finset.prod_ne_zero_iff.mpr fun l _ => hb l)
    obtain ⟨v, hv⟩ := hbu'.exists_right_inv
    have hgd : algebraMap _ (locRing P.K (P.coord x hx)) g =
        algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, a l) *
          (v * P.stalkEquiv x hx hcl w) := by
      rw [hψg, ← hprod]
      linear_combination (-(P.stalkEquiv x hx hcl t * P.stalkEquiv x hx hcl w)) * hv
    obtain ⟨c', d', hd', hcd⟩ :=
      exists_mk_locRing P.K (P.coord x hx) (v * P.stalkEquiv x hx hcl w)
    have hz : algebraMap _ (locRing P.K (P.coord x hx)) (g * d' - (∏ l ∈ J, a l) * c') = 0 := by
      rw [map_sub, map_mul, map_mul, hgd, ← hcd]
      ring
    obtain ⟨s', hs', hs'K⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero P.K (P.coord x hx) hz
    refine ⟨s' * d', by rw [map_mul]; exact mul_ne_zero hs' hd', ?_⟩
    have : s' * d' * g = s' * (g * d' - (∏ l ∈ J, a l) * c') + (s' * c') * (∏ l ∈ J, a l) := by
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right hs'K)
      (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)))
  choose! hgf hgf1 hgf2 using hper
  obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian (I.comap P.secHom) : (I.comap P.secHom).FG)
  have hgmem : ∀ g ∈ gens, g ∈ I.comap P.secHom := fun g hg => hgens ▸ Submodule.subset_span hg
  refine ⟨h₁ * ∏ g ∈ gens, hgf g, ?_, ?_, ?_⟩
  · rw [map_mul, map_prod]
    exact mul_ne_zero hh₁ (Finset.prod_ne_zero_iff.mpr fun g hg => hgf1 g (hgmem g hg))
  · have : (h₁ * ∏ g ∈ gens, hgf g) * ∏ l ∈ J, a l = (∏ g ∈ gens, hgf g) * (h₁ * ∏ l ∈ J, a l) := by
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hmemb
  · intro g hg
    rw [← hgens] at hg
    refine Submodule.span_induction
      (p := fun g _ => (h₁ * ∏ g ∈ gens, hgf g) * g ∈ Ideal.span {∏ l ∈ J, a l} ⊔ P.K)
      ?_ ?_ ?_ ?_ hg
    · intro g hgs
      have hsplit : (h₁ * ∏ g ∈ gens, hgf g) * g =
          (h₁ * ∏ g' ∈ gens.erase g, hgf g') * (hgf g * g) := by
        rw [← Finset.mul_prod_erase gens hgf hgs]
        ring
      rw [hsplit]
      exact Ideal.mul_mem_left _ _ (hgf2 g (hgmem g hgs))
    · simp
    · intro u v _ _ hu hv
      rw [mul_add]
      exact Ideal.add_mem _ hu hv
    · intro r u _ hu
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hu

end Chart

end

end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
