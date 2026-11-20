import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

/- English proof (translation)
Take `⟨t, ht1, ht⟩` from `hS A T ι I μ hι hμι`. Establish `hu : IsUnit (algebraMap T (Localization.Away t) t)` using `IsLocalization.Away.algebraMap_isUnit t`. Establish `hloc : (algebraMap T (Localization.Away t)).Etale` using `RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)`. Establish `hμι' : ∀ a, μ (ι a) = Ideal.Quotient.mk I a` using `fun a => RingHom.congr_fun hμι a`. Establish `hμκ' : ∀ q, μ (κ q) = MvPolynomial.constantCoeff q` using `fun q => RingHom.congr_fun hμκ q`.

Establish `key : ∀ s : T, μ s = 0 → algebraMap T (Localization.Away t) s ∈ I.map ((algebraMap T (Localization.Away t)).comp ι)`. Introduce `s hs`. Establish `h1` using `Ideal.mem_map_of_mem (algebraMap T (Localization.Away t)) (ht s hs)`. Rewrite `h1` using `[Ideal.map_map, map_mul]`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).mp h1`.

Establish `hut : IsUnit (μ t)` using `by rw [ht1]; exact isUnit_one`. Set `μB : Localization.Away t →+* A ⧸ I` to `IsLocalization.Away.lift t hut`. Establish `hμB : ∀ a, μB ((algebraMap T (Localization.Away t)).comp ι a) = Ideal.Quotient.mk I a`. Introduce `a`. Simplify using `only [RingHom.comp_apply, μB, IsLocalization.Away.lift_eq, hμι']`.

Use `⟨Localization.Away t, inferInstance, (algebraMap T (Localization.Away t)).comp ι, (algebraMap T (Localization.Away t)).comp κ, ⟨RingHom.Etale.stableUnderComposition _ _ hι hloc, ?_, ?_⟩, RingHom.Etale.stableUnderComposition _ _ hκ hloc, ?_, ?_⟩` and prove the remaining obligations. Apply `Ideal.quotientMap_injective'` to reduce the goal to its premises. Introduce `a ha`. Establish `hker : I.map ((algebraMap T (Localization.Away t)).comp ι) ≤ RingHom.ker μB`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `b hb`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hb`. Use `hker (Ideal.mem_comap.mp ha)` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `this`. Introduce `z`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨⟨s, ⟨_, n, rfl⟩⟩, hbn⟩` from `IsLocalization.surj (Submonoid.powers t) b`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (μ s)`.

Use `⟨Ideal.Quotient.mk I a, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.quotientMap_mk]`. Establish `e1 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι)) (algebraMap T (Localization.Away t) t) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk _)]`. Use `Ideal.Quotient.eq.mpr ?_` and prove the remaining obligations.

Use `key (t - 1) (by rw [map_sub, map_one, ht1, sub_self])` as an intermediate fact. Simplify `this` using `[map_sub]`. Establish `e2 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι)) (algebraMap T (Localization.Away t) s) = Ideal.Quotient.mk _ (((algebraMap T (Localization.Away t)).comp ι) a)`. Use `Ideal.Quotient.eq.mpr ?_` and prove the remaining obligations. Use `key (s - ι a) (by rw [map_sub, hμι', ha, sub_self])` as an intermediate fact.

Simplify `this` using `[map_sub]`. Simplify using `only at hbn`. Rewrite using `[← e2, ← hbn, map_mul, map_pow, map_pow, e1, one_pow, mul_one]`. Rewrite using `[show I.map ((algebraMap T (Localization.Away t)).comp ι) = (Ideal.span (Set.range x)).map ((algebraMap T (Localization.Away t)).comp ι) by rw [← hI], Ideal.map_span, ← Set.range_comp]`. Use `congr 2`.

Use function extensionality and compare the values at `j`. Simplify using `[hx]`. Introduce `a`. Use `key (ι a - κ (MvPolynomial.C (Ideal.Quotient.mk I a))) (by rw [map_sub, hμι', hμκ', MvPolynomial.constantCoeff_C, sub_self])` as an intermediate fact. Simplify `this` using `[map_sub]`.
-/
theorem chart_of_data (hS : LeafSec) {d : ℕ} {A T : Type} [CommRing A] [CommRing T] (I : Ideal A) (x : Fin d → A)
    (ι : A →+* T) (κ : MvPolynomial (Fin d) (A ⧸ I) →+* T) (μ : T →+* A ⧸ I)
    (hι : ι.Etale) (hκ : κ.Etale) (hμι : μ.comp ι = Ideal.Quotient.mk I)
    (hμκ : μ.comp κ = MvPolynomial.constantCoeff) (hx : ∀ j, ι (x j) = κ (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  obtain ⟨t, ht1, ht⟩ := hS A T ι I μ hι hμι
  have hu : IsUnit (algebraMap T (Localization.Away t) t) := IsLocalization.Away.algebraMap_isUnit t
  have hloc : (algebraMap T (Localization.Away t)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)
  have hμι' : ∀ a, μ (ι a) = Ideal.Quotient.mk I a := fun a => RingHom.congr_fun hμι a
  have hμκ' : ∀ q, μ (κ q) = MvPolynomial.constantCoeff q := fun q => RingHom.congr_fun hμκ q
  have key : ∀ s : T, μ s = 0 →
      algebraMap T (Localization.Away t) s ∈ I.map ((algebraMap T (Localization.Away t)).comp ι) := by
    intro s hs
    have h1 := Ideal.mem_map_of_mem (algebraMap T (Localization.Away t)) (ht s hs)
    rw [Ideal.map_map, map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have hut : IsUnit (μ t) := by rw [ht1]; exact isUnit_one
  let μB : Localization.Away t →+* A ⧸ I := IsLocalization.Away.lift t hut
  have hμB : ∀ a, μB ((algebraMap T (Localization.Away t)).comp ι a) = Ideal.Quotient.mk I a := by
    intro a
    simp only [RingHom.comp_apply, μB, IsLocalization.Away.lift_eq, hμι']
  refine ⟨Localization.Away t, inferInstance, (algebraMap T (Localization.Away t)).comp ι,
    (algebraMap T (Localization.Away t)).comp κ, ⟨RingHom.Etale.stableUnderComposition _ _ hι hloc, ?_, ?_⟩,
    RingHom.Etale.stableUnderComposition _ _ hκ hloc, ?_, ?_⟩
  · apply Ideal.quotientMap_injective'
    intro a ha
    have hker : I.map ((algebraMap T (Localization.Away t)).comp ι) ≤ RingHom.ker μB := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]
      exact hb
    have := hker (Ideal.mem_comap.mp ha)
    rw [RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hbn⟩ := IsLocalization.surj (Submonoid.powers t) b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (μ s)
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    have e1 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) t) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _)]
      refine Ideal.Quotient.eq.mpr ?_
      have := key (t - 1) (by rw [map_sub, map_one, ht1, sub_self])
      simpa [map_sub] using this
    have e2 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) s) =
        Ideal.Quotient.mk _ (((algebraMap T (Localization.Away t)).comp ι) a) := by
      refine Ideal.Quotient.eq.mpr ?_
      have := key (s - ι a) (by rw [map_sub, hμι', ha, sub_self])
      simpa [map_sub] using this
    simp only at hbn
    rw [← e2, ← hbn, map_mul, map_pow, map_pow, e1, one_pow, mul_one]
  · rw [show I.map ((algebraMap T (Localization.Away t)).comp ι) =
        (Ideal.span (Set.range x)).map ((algebraMap T (Localization.Away t)).comp ι) by rw [← hI],
      Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [hx]
  · intro a
    have := key (ι a - κ (MvPolynomial.C (Ideal.Quotient.mk I a)))
      (by rw [map_sub, hμι', hμκ', MvPolynomial.constantCoeff_C, sub_self])
    simpa [map_sub] using this

/- English proof (translation)
Set `f : A →ₐ[P] A ⧸ I` to `Ideal.Quotient.mkₐ P I`. Establish `hg : ∀ p, (MvPolynomial.constantCoeff.comp c.symm.toRingHom) (algebraMap P Q p) = algebraMap P (A ⧸ I) p` using `fun p => by`. Rewrite using `[RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]`. Conclude with `hcomm p`. Set `g : Q →ₐ[P] A ⧸ I` to `{ MvPolynomial.constantCoeff.comp c.symm.toRingHom with commutes' := hg }`.

Set `μ` to `(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom`. Set `ι` to `algebraMap A (A ⊗[P] Q)`. Set `κ` to `((Algebra.TensorProduct.comm P Q A).toRingHom.comp (algebraMap Q (Q ⊗[P] A))).comp c.toRingHom`. Establish `hκa : ∀ q, κ q = (1 : A) ⊗ₜ c q` using `fun q => by`. Simplify using `[κ, Algebra.TensorProduct.comm_tmul]`.

Use `chart_of_data hS I x ι κ μ (RingHom.etale_algebraMap.mpr inferInstance) ?_ ?_ ?_ ?_ hI` and prove the remaining obligations. Conclude with `RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective c.bijective) (RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr inferInstance) (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P Q A).bijective))`. Use extensionality with `a`. Simplify using `[μ, ι, f, g]`. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `q`. Simplify using `[μ, hκa, f, g]`. Introduce `j`. Rewrite using `[hκa]`. Use `show x j ⊗ₜ 1 = _`.

Rewrite using `[← hpx1, ← hpx2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Q), TensorProduct.smul_tmul]`.
-/
theorem chart_of_tensor (hS : LeafSec) {d : ℕ} {P A Q : Type} [CommRing P] [CommRing A] [CommRing Q] [Algebra P A]
    [Algebra P Q] (I : Ideal A) (x : Fin d → A) (c : MvPolynomial (Fin d) (A ⧸ I) ≃+* Q) [Algebra.Etale P A]
    [Algebra.Etale P Q]
    (hcomm : ∀ p, MvPolynomial.constantCoeff (c.symm (algebraMap P Q p)) = Ideal.Quotient.mk I (algebraMap P A p))
    (px : Fin d → P) (hpx1 : ∀ j, algebraMap P A (px j) = x j)
    (hpx2 : ∀ j, algebraMap P Q (px j) = c (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  let f : A →ₐ[P] A ⧸ I := Ideal.Quotient.mkₐ P I
  have hg : ∀ p, (MvPolynomial.constantCoeff.comp c.symm.toRingHom) (algebraMap P Q p) =
      algebraMap P (A ⧸ I) p := fun p => by
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]; exact hcomm p
  let g : Q →ₐ[P] A ⧸ I := { MvPolynomial.constantCoeff.comp c.symm.toRingHom with commutes' := hg }
  let μ := (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
  let ι := algebraMap A (A ⊗[P] Q)
  let κ := ((Algebra.TensorProduct.comm P Q A).toRingHom.comp (algebraMap Q (Q ⊗[P] A))).comp c.toRingHom
  have hκa : ∀ q, κ q = (1 : A) ⊗ₜ c q := fun q => by
    simp [κ, Algebra.TensorProduct.comm_tmul]
  refine chart_of_data hS I x ι κ μ (RingHom.etale_algebraMap.mpr inferInstance) ?_ ?_ ?_ ?_ hI
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective c.bijective)
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr inferInstance)
        (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P Q A).bijective))
  · ext a; simp [μ, ι, f, g]
  · apply RingHom.ext; intro q; simp [μ, hκa, f, g]
  · intro j
    rw [hκa]
    show x j ⊗ₜ 1 = _
    rw [← hpx1, ← hpx2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Q),
      TensorProduct.smul_tmul]

/- English proof (translation)
Introduce `e d R A _ _ φ I x y hc`. Establish `hπ` using `hP e d R A φ I x y hc`. Use `set α := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hα`. Use `set π := (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) with hπdef`. Establish `hxI : ∀ j, x j ∈ I` using `fun j => hc.2 ▸ Ideal.subset_span ⟨j, rfl⟩`.

Establish `hcomm : MvPolynomial.constantCoeff.comp π = (Ideal.Quotient.mk I).comp α`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[π, α]`. Introduce `i`.

Break down `i with j | i` into its components or cases. Simplify using `[π, α, Ideal.Quotient.eq_zero_iff_mem.mpr (hxI j)]`. Simplify using `[π, α]`. Conclude with `@chart_of_tensor hS d _ A _ _ _ _ α.toAlgebra π.toAlgebra I x (RingEquiv.refl _) hc.1.toAlgebra hπ.toAlgebra (fun p => RingHom.congr_fun hcomm p) (fun j => MvPolynomial.X (Sum.inl j)) (fun j => by show α _ = x j; rw [hα]; simp) (fun j => by show π _ = _; rw [hπdef]; simp) hc.2`.
-/
theorem LeafNbhd_of (hS : LeafSec) (hP : LeafPoly) : LeafNbhd := by
  intro e d R A _ _ φ I x y hc
  have hπ := hP e d R A φ I x y hc
  set α := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hα
  set π := (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
    ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i))))
    with hπdef
  have hxI : ∀ j, x j ∈ I := fun j => hc.2 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hcomm : MvPolynomial.constantCoeff.comp π = (Ideal.Quotient.mk I).comp α := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [π, α]
    · intro i
      rcases i with j | i
      · simp [π, α, Ideal.Quotient.eq_zero_iff_mem.mpr (hxI j)]
      · simp [π, α]
  exact @chart_of_tensor hS d _ A _ _ _ _ α.toAlgebra π.toAlgebra I x (RingEquiv.refl _) hc.1.toAlgebra hπ.toAlgebra
    (fun p => RingHom.congr_fun hcomm p) (fun j => MvPolynomial.X (Sum.inl j)) (fun j => by show α _ = x j; rw [hα]; simp)
    (fun j => by show π _ = _; rw [hπdef]; simp) hc.2

end LateralTheory.CohomologicalPurity.ChartCut
