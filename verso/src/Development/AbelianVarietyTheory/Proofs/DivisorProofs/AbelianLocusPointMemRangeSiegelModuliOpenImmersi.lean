import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianIsAbelianSchemeLocalizationAbelianLocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectExtensionAbelianLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbChart

/- English proof (translation)
Introduce `g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ p _ hp κ s' hκ hs` and use `GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p (GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus R G₁ hG p hp) κ s' hκ hs`.
-/
theorem exists_siegPre_localization : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := fun g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ p _ hp κ s' hκ hs =>
  GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p (GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus R G₁ hG p hp) κ s' hκ hs

/- English proof (translation)
Introduce `n R _ _ _ b x`. Take `⟨φ, rfl⟩ : ∃ φ : cycAway n →+* FractionRing R, spMap φ = x` from `⟨(Spec.preimage x).hom, by simp [spMap]⟩`. Set `A` to `algebraMap R (FractionRing R)`. Establish `hAi : Function.Injective A` using `IsFractionRing.injective R (FractionRing R)`. Establish `hgen : ∀ (w : ℂ) (hw : w ∈ cycAway n), φ ⟨w, hw⟩ ∈ A.range`.

Introduce `w hw`. Proceed by induction on `hw using Subring.closure_induction with`. Consider the case `mem w hw`. Break down `hw with rfl | rfl` into its components or cases. Break down `Nat.eq_zero_or_pos n with h0 | hn` into its components or cases.

Substitute `h0` using the available equality. Establish `: (⟨zeta 0, Subring.subset_closure (Or.inl rfl)⟩ : cycAway 0) = 1` using `Subtype.ext (by simp [zeta])`. Rewrite using `[this, map_one]`. Conclude with `A.range.one_mem`. Establish `hpow : (⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩ : cycAway n) ^ n = 1` using `Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one)`.

Establish `hI : IsIntegral R (φ ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩)`. Use `IsIntegral.of_pow hn ?_` and prove the remaining obligations. Rewrite using `[← map_pow, hpow, map_one]`. Conclude with `isIntegral_one`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hI`.

Conclude with `⟨r, hr⟩`. Break down `Nat.eq_zero_or_pos n with h0 | hn` into its components or cases. Substitute `h0` using the available equality. Establish `: (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway 0) = 0` using `Subtype.ext (by simp)`. Rewrite using `[this, map_zero]`.

Conclude with `A.range.zero_mem`. Use `set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩`. Establish `hu : u * (n : cycAway n) = 1` using `Subtype.ext (by simp [u, hn.ne'])`. Establish `e1 : φ u * (n : FractionRing R) = 1` using `by rw [← map_natCast φ, ← map_mul, hu, map_one]`. Establish `e2 : A (b u) * (n : FractionRing R) = 1` using `by rw [← map_natCast A, ← map_mul, ← map_natCast b, ← map_mul, hu, map_one, map_one]`.

Establish `hn0 : (n : FractionRing R) ≠ 0` using `right_ne_zero_of_mul_eq_one e1`. Conclude with `⟨b u, mul_right_cancel₀ hn0 (e2.trans e1.symm)⟩`. Consider the case `zero => exact ⟨0, by rw [map_zero]; exact (map_zero φ).symm⟩`. Consider the case `one => exact ⟨1, by rw [map_one]; exact (map_one φ).symm⟩`. Consider the case `add w v hw hv ihw ihv`.

Establish `: (⟨w + v, add_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ + ⟨v, hv⟩` using `rfl`. Rewrite using `[this, map_add]`. Conclude with `A.range.add_mem ihw ihv`. Consider the case `neg w hw ih`. Establish `: (⟨-w, neg_mem hw⟩ : cycAway n) = -⟨w, hw⟩` using `rfl`.

Rewrite using `[this, map_neg]`. Conclude with `A.range.neg_mem ih`. Consider the case `mul w v hw hv ihw ihv`. Establish `: (⟨w * v, mul_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ * ⟨v, hv⟩` using `rfl`. Rewrite using `[this, map_mul]`.

Conclude with `A.range.mul_mem ihw ihv`. Set `e : R ≃+* A.range` to `RingEquiv.ofBijective A.rangeRestrict ⟨fun a a' h => hAi (congrArg Subtype.val h), A.rangeRestrict_surjective⟩`. Set `ψ : cycAway n →+* R` to `(e.symm : A.range →+* R).comp (φ.codRestrict A.range fun z => hgen z.1 z.2)`. Establish `hψ : A.comp ψ = φ`. Use extensionality with `z`.

Establish `h` using `congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hgen z.1 z.2⟩)`. Conclude with `h`. Use `⟨spMap ψ, ?_⟩` and prove the remaining obligations. Conclude with `(spMap_comp ψ A).symm.trans (congrArg spMap hψ)`.
-/
theorem exists_spMap_ext : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (b : cycAway n →+* R) (x : Sp (FractionRing R) ⟶ Sp (cycAway n)), ∃ s : Sp R ⟶ Sp (cycAway n), jK R ≫ s = x := by
  intro n R _ _ _ b x
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* FractionRing R, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  let A := algebraMap R (FractionRing R)
  have hAi : Function.Injective A := IsFractionRing.injective R (FractionRing R)
  have hgen : ∀ (w : ℂ) (hw : w ∈ cycAway n), φ ⟨w, hw⟩ ∈ A.range := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨zeta 0, Subring.subset_closure (Or.inl rfl)⟩ : cycAway 0) = 1 := Subtype.ext (by simp [zeta])
          rw [this, map_one]; exact A.range.one_mem
        · have hpow : (⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩ : cycAway n) ^ n = 1 :=
            Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one)
          have hI : IsIntegral R (φ ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩) := by
            refine IsIntegral.of_pow hn ?_
            rw [← map_pow, hpow, map_one]; exact isIntegral_one
          obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
          exact ⟨r, hr⟩
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway 0) = 0 := Subtype.ext (by simp)
          rw [this, map_zero]; exact A.range.zero_mem
        · set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
          have hu : u * (n : cycAway n) = 1 := Subtype.ext (by simp [u, hn.ne'])
          have e1 : φ u * (n : FractionRing R) = 1 := by rw [← map_natCast φ, ← map_mul, hu, map_one]
          have e2 : A (b u) * (n : FractionRing R) = 1 := by rw [← map_natCast A, ← map_mul, ← map_natCast b, ← map_mul, hu, map_one, map_one]
          have hn0 : (n : FractionRing R) ≠ 0 := right_ne_zero_of_mul_eq_one e1
          exact ⟨b u, mul_right_cancel₀ hn0 (e2.trans e1.symm)⟩
    | zero => exact ⟨0, by rw [map_zero]; exact (map_zero φ).symm⟩
    | one => exact ⟨1, by rw [map_one]; exact (map_one φ).symm⟩
    | add w v hw hv ihw ihv =>
      have : (⟨w + v, add_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ + ⟨v, hv⟩ := rfl
      rw [this, map_add]; exact A.range.add_mem ihw ihv
    | neg w hw ih =>
      have : (⟨-w, neg_mem hw⟩ : cycAway n) = -⟨w, hw⟩ := rfl
      rw [this, map_neg]; exact A.range.neg_mem ih
    | mul w v hw hv ihw ihv =>
      have : (⟨w * v, mul_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ * ⟨v, hv⟩ := rfl
      rw [this, map_mul]; exact A.range.mul_mem ihw ihv
  let e : R ≃+* A.range := RingEquiv.ofBijective A.rangeRestrict ⟨fun a a' h => hAi (congrArg Subtype.val h), A.rangeRestrict_surjective⟩
  let ψ : cycAway n →+* R := (e.symm : A.range →+* R).comp (φ.codRestrict A.range fun z => hgen z.1 z.2)
  have hψ : A.comp ψ = φ := by
    ext z
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hgen z.1 z.2⟩)
    exact h
  refine ⟨spMap ψ, ?_⟩
  exact (spMap_comp ψ A).symm.trans (congrArg spMap hψ)

/- English proof (translation)
Introduce `n K _ _ x q`. Take `⟨φ, rfl⟩ : ∃ φ : cycAway n →+* K, spMap φ = x` from `⟨(Spec.preimage x).hom, by simp [spMap]⟩`. Establish `hq : q.asIdeal = ⊥` using `(Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top`. Express the relevant statement in the definitionally equal form `Ideal.comap φ q.asIdeal = ⊥`. Rewrite using `[hq, ← RingHom.ker_eq_comap_bot]`.

Assume the negation of the conclusion as `hne`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `halg : IsAlgebraic ℤ a`. Establish `hC : ∀ z ∈ cycAway n, IsIntegral ℚ z`. Introduce `z hz`.

Use `Subring.closure_le (t := (integralClosure ℚ ℂ).toSubring) |>.2 ?_ hz` and prove the remaining obligations. Introduce and unpack `w (rfl | rfl)`. Use `show IsIntegral ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n))`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `using (isIntegral_one : IsIntegral ℚ (1 : ℂ))`.

Conclude with `((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top`. Use `show IsIntegral ℚ ((n : ℂ)⁻¹)`. Simplify using `using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := ((n : ℚ)⁻¹)))`. Establish `h1 : IsAlgebraic ℚ (a : ℂ)` using `(hC a a.2).isAlgebraic`. Establish `h2 : IsAlgebraic ℤ (a : ℂ)` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 h1`.

Conclude with `(isAlgebraic_algHom_iff ((cycAway n).subtype.toIntAlgHom) Subtype.val_injective).1 h2`. Use `Ideal.comap_ne_bot_of_algebraic_mem ha0 ha halg` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `m hm`.

Rewrite `hm` using `[Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast]`. Conclude with `(Ideal.mem_bot).2 (Int.cast_eq_zero.1 hm)`.
-/
theorem asIdeal_eq_bot_of_charZero : ∀ (n : ℕ) (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ Sp (cycAway n)) (q : Sp K), (x q).asIdeal = ⊥ := by
  intro n K _ _ x q
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* K, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  change Ideal.comap φ q.asIdeal = ⊥
  rw [hq, ← RingHom.ker_eq_comap_bot]
  by_contra hne
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have halg : IsAlgebraic ℤ a := by
    have hC : ∀ z ∈ cycAway n, IsIntegral ℚ z := by
      intro z hz
      refine Subring.closure_le (t := (integralClosure ℚ ℂ).toSubring) |>.2 ?_ hz
      rintro w (rfl | rfl)
      · show IsIntegral ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n))
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using (isIntegral_one : IsIntegral ℚ (1 : ℂ))
        · exact ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top
      · show IsIntegral ℚ ((n : ℂ)⁻¹)
        simpa using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := ((n : ℚ)⁻¹)))
    have h1 : IsAlgebraic ℚ (a : ℂ) := (hC a a.2).isAlgebraic
    have h2 : IsAlgebraic ℤ (a : ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 h1
    exact (isAlgebraic_algHom_iff ((cycAway n).subtype.toIntAlgHom) Subtype.val_injective).1 h2
  have := Ideal.comap_ne_bot_of_algebraic_mem ha0 ha halg
  apply this
  rw [eq_bot_iff]
  intro m hm
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hm
  exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 hm)

/- English proof (translation)
Introduce `g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy p hp`. Use `haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p`. Establish `hu : ∀ x : p.asIdeal.primeCompl, IsUnit (algebraMap R (FractionRing R) x)` using `fun x => IsLocalization.map_units (FractionRing R) (⟨x.1, mem_nonZeroDivisors_of_ne_zero (fun h => x.2 (h ▸ p.asIdeal.zero_mem))⟩ : nonZeroDivisors R)`. Set `lf : Localization.AtPrime p.asIdeal →+* FractionRing R` to `IsLocalization.lift hu`. Set `ιp` to `spMap (algebraMap R (Localization.AtPrime p.asIdeal))`.

Set `κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)` to `spMap lf`. Establish `hκ : κ ≫ ιp = jK R`. Rewrite using `[← spMap_comp]`. Conclude with `congrArg spMap (IsLocalization.lift_comp hu)`. Establish `hnorm` using `(GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2`.

Take `⟨s, hs⟩` from `exists_spMap_ext n R b (y ≫ F.s)`. Establish `hs' : κ ≫ ιp ≫ s = y ≫ F.s` using `by rw [← Category.assoc, hκ, hs]`. Take `⟨c, c', hc, m₁, m₂⟩` from `exists_siegPre_localization g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p hp κ (ιp ≫ s) hκ hs'`. Establish `hinj : Function.Injective lf`. Use `(IsLocalization.lift_injective_iff hu).2 fun x x' => ?_` and prove the remaining obligations.

Rewrite using `[(IsLocalization.injective (Localization.AtPrime p.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors p.asIdeal)).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]`. Use `haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot lf).1 hinj]`. Conclude with `bot_le)⟩`. Establish `hdense : Dense {x : Sp (Localization.AtPrime p.asIdeal) | ((ιp ≫ s) x).asIdeal = ⊥}`.

Use `Dense.mono ?_ hdom.denseRange` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Use `show ((ιp ≫ s) (κ q)).asIdeal = ⊥`. Rewrite using `[← Scheme.Hom.comp_apply, hs']`. Conclude with `asIdeal_eq_bot_of_charZero n (FractionRing R) (y ≫ F.s) q`.

Take `⟨f, hfs, hf⟩` from `F.rep _ (ιp ≫ s) c inferInstance hdense hc`. Establish `hfy : κ ≫ f = y` using `F.inj (FractionRing R) (κ ≫ f) y (y ≫ F.s) c' (by rw [Category.assoc, hfs, hs']) (GlobalTheory.SiegelPullComp.pb_comp hf m₁) m₂`. Establish `hξ : ιp ≫ ξ = f ≫ j`. Use `ext_of_isDominant κ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hκ, ← hy, ← Category.assoc, hfy]`.

Use `⟨f (closedPoint (Localization.AtPrime p.asIdeal)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(f ≫ j) (closedPoint _) = ξ p`. Rewrite using `[← hξ]`. Express the relevant statement in the definitionally equal form `ξ (ιp (closedPoint _)) = ξ p`. Use `congr 1`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `Localization.AtPrime.comap_maximalIdeal`.
-/
theorem mem_range_of_mem_abLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy p hp
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  have hu : ∀ x : p.asIdeal.primeCompl, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R)
      (⟨x.1, mem_nonZeroDivisors_of_ne_zero (fun h => x.2 (h ▸ p.asIdeal.zero_mem))⟩ : nonZeroDivisors R)
  let lf : Localization.AtPrime p.asIdeal →+* FractionRing R := IsLocalization.lift hu
  let ιp := spMap (algebraMap R (Localization.AtPrime p.asIdeal))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal) := spMap lf
  have hκ : κ ≫ ιp = jK R := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hnorm := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨s, hs⟩ := exists_spMap_ext n R b (y ≫ F.s)
  have hs' : κ ≫ ιp ≫ s = y ≫ F.s := by rw [← Category.assoc, hκ, hs]
  obtain ⟨c, c', hc, m₁, m₂⟩ := exists_siegPre_localization g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p hp κ (ιp ≫ s) hκ hs'
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.AtPrime p.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors p.asIdeal)).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hdense : Dense {x : Sp (Localization.AtPrime p.asIdeal) | ((ιp ≫ s) x).asIdeal = ⊥} := by
    refine Dense.mono ?_ hdom.denseRange
    rintro _ ⟨q, rfl⟩
    show ((ιp ≫ s) (κ q)).asIdeal = ⊥
    rw [← Scheme.Hom.comp_apply, hs']
    exact asIdeal_eq_bot_of_charZero n (FractionRing R) (y ≫ F.s) q
  obtain ⟨f, hfs, hf⟩ := F.rep _ (ιp ≫ s) c inferInstance hdense hc
  have hfy : κ ≫ f = y := F.inj (FractionRing R) (κ ≫ f) y (y ≫ F.s) c'
    (by rw [Category.assoc, hfs, hs']) (GlobalTheory.SiegelPullComp.pb_comp hf m₁) m₂
  have hξ : ιp ≫ ξ = f ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hfy]
  refine ⟨f (closedPoint (Localization.AtPrime p.asIdeal)), ?_⟩
  change (f ≫ j) (closedPoint _) = ξ p
  rw [← hξ]
  change ξ (ιp (closedPoint _)) = ξ p
  congr 1
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.comap_maximalIdeal

end GlobalTheory.AbChart
