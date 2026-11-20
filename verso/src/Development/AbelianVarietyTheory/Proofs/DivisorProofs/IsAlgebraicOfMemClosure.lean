import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChartQF

section Alg

variable {A R : Type} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R] (f : A →+* R)

/- English proof (translation)
Proceed by induction on `hb using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases. Take `⟨a, rfl⟩` from `hT hx`. Rewrite using `[hev]`.

Conclude with `D.algebraMap_mem _`. Conclude with `hG x hx`. Consider the case `zero => rw [map_zero]`. Conclude with `D.zero_mem`. Consider the case `one => rw [map_one]`.

Conclude with `D.one_mem`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `D.add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `D.neg_mem hx`.

Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `D.mul_mem hx hy`.
-/
theorem isAlgebraic_of_mem_closure {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T G : Set R} (hT : T ⊆ Set.range f)
    {D : Subalgebra (ResidueField A) K} (hG : ∀ g ∈ G, ev g ∈ D) {b : R} (hb : b ∈ Subring.closure (T ∪ G)) :
    ev b ∈ D := by
  induction hb using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨a, rfl⟩ := hT hx
      rw [hev]
      exact D.algebraMap_mem _
    · exact hG x hx
  | zero => rw [map_zero]; exact D.zero_mem
  | one => rw [map_one]; exact D.one_mem
  | add x y _ _ hx hy => rw [map_add]; exact D.add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact D.neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact D.mul_mem hx hy

/- English proof (translation)
Establish `hker : ∀ r ∈ maximalIdeal R, ev r = 0` using `fun r hr => by`. Rewrite using `[← RingHom.mem_ker, hk]`. Conclude with `hr`. Set `ι : ResidueField R →+* K` to `Ideal.Quotient.lift (maximalIdeal R) ev hker`. Establish `hι : ∀ r, ι (residue R r) = ev r` using `fun r => rfl`.

Set `D : Subalgebra (ResidueField A) K` to `Algebra.adjoin (ResidueField A) ((ev : R → K) '' (G : Set R))`. Establish `hDfin : Module.Finite (ResidueField A) D` using `Algebra.finite_adjoin_of_finite_of_isIntegral (G.finite_toSet.image _) (by rintro _ ⟨g, hg, rfl⟩; exact (hG g hg).isIntegral)`. Establish `hB : ∀ c ∈ Subring.closure (T ∪ (G : Set R)), ev c ∈ D` using `fun c hc => isAlgebraic_of_mem_closure f ev hev hT (D := D) (fun g hg => Algebra.subset_adjoin (Set.mem_image_of_mem _ hg)) hc`. Establish `hDint : ∀ d ∈ D, IsIntegral (ResidueField A) d` using `fun d hd => (Algebra.IsIntegral.isIntegral (R := ResidueField A) (⟨d, hd⟩ : ↥D)).map D.val`. Establish `hrange : ∀ x : ResidueField R, ι x ∈ D`.

Introduce `x`. Take `⟨r, rfl⟩` from `residue_surjective x`. Take `⟨a, ha, c, hc, hcm, hca⟩` from `hb r`. Establish `h1 : ev c * ev r = ev a`. Use `hker _ hca` as an intermediate fact.

Rewrite `this` using `[map_sub, map_mul, sub_eq_zero]`. Conclude with `this`. Establish `hc0 : ev c ≠ 0` using `fun h0 => hcm (by rw [← hk]; exact RingHom.mem_ker.mpr h0)`. Establish `h2 : ev r = ev a * (ev c)⁻¹` using `by rw [← h1]; field_simp`. Rewrite using `[hι, h2]`.

Conclude with `D.mul_mem (hB a ha) ((hDint _ (hB c hc)).inv_mem (hB c hc))`. Use `letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map f).toAlgebra`. Establish `hcompat : ∀ y : ResidueField A, ι (algebraMap _ _ y) = algebraMap (ResidueField A) K y`. Introduce `y`. Take `⟨a, rfl⟩` from `residue_surjective y`.

Use `show ι (ResidueField.map f (residue A a)) = _`. Rewrite using `[ResidueField.map_residue, hι, hev]`. Set `L : ResidueField R →ₗ[ResidueField A] D` to `{ toFun := fun x => ⟨ι x, hrange x⟩ map_add' := fun x y => Subtype.ext (map_add ι x y) map_smul' := fun y x => Subtype.ext (by`. Simplify using `only [Algebra.smul_def, map_mul, hcompat, RingHom.id_apply]`. Use the proof step `rfl) }`.

Establish `hfin : Module.Finite (ResidueField A) (ResidueField R)` using `FiniteDimensional.of_injective L (fun x y h => ι.injective (congrArg Subtype.val h))`. Rewrite using `[← ResidueField.map_comp_residue f]`. Conclude with `RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ residue_surjective)`.
-/
theorem finite_residue [IsLocalHom f] {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hk : RingHom.ker ev = maximalIdeal R)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T : Set R} {G : Finset R}
    (hT : T ⊆ Set.range f)
    (hb : ∀ r : R, ∃ a ∈ Subring.closure (T ∪ (G : Set R)), ∃ b ∈ Subring.closure (T ∪ (G : Set R)),
      b ∉ maximalIdeal R ∧ b * r - a ∈ maximalIdeal R)
    (hG : ∀ g ∈ G, IsAlgebraic (ResidueField A) (ev g)) : ((residue R).comp f).Finite := by
  classical
  have hker : ∀ r ∈ maximalIdeal R, ev r = 0 := fun r hr => by
    rw [← RingHom.mem_ker, hk]; exact hr

  let ι : ResidueField R →+* K := Ideal.Quotient.lift (maximalIdeal R) ev hker
  have hι : ∀ r, ι (residue R r) = ev r := fun r => rfl

  let D : Subalgebra (ResidueField A) K := Algebra.adjoin (ResidueField A) ((ev : R → K) '' (G : Set R))
  have hDfin : Module.Finite (ResidueField A) D :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (G.finite_toSet.image _)
      (by rintro _ ⟨g, hg, rfl⟩; exact (hG g hg).isIntegral)
  have hB : ∀ c ∈ Subring.closure (T ∪ (G : Set R)), ev c ∈ D := fun c hc =>
    isAlgebraic_of_mem_closure f ev hev hT (D := D)
      (fun g hg => Algebra.subset_adjoin (Set.mem_image_of_mem _ hg)) hc
  have hDint : ∀ d ∈ D, IsIntegral (ResidueField A) d := fun d hd =>
    (Algebra.IsIntegral.isIntegral (R := ResidueField A) (⟨d, hd⟩ : ↥D)).map D.val

  have hrange : ∀ x : ResidueField R, ι x ∈ D := by
    intro x
    obtain ⟨r, rfl⟩ := residue_surjective x
    obtain ⟨a, ha, c, hc, hcm, hca⟩ := hb r
    have h1 : ev c * ev r = ev a := by
      have := hker _ hca
      rw [map_sub, map_mul, sub_eq_zero] at this
      exact this
    have hc0 : ev c ≠ 0 := fun h0 => hcm (by rw [← hk]; exact RingHom.mem_ker.mpr h0)
    have h2 : ev r = ev a * (ev c)⁻¹ := by rw [← h1]; field_simp
    rw [hι, h2]
    exact D.mul_mem (hB a ha) ((hDint _ (hB c hc)).inv_mem (hB c hc))
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hcompat : ∀ y : ResidueField A, ι (algebraMap _ _ y) = algebraMap (ResidueField A) K y := by
    intro y
    obtain ⟨a, rfl⟩ := residue_surjective y
    show ι (ResidueField.map f (residue A a)) = _
    rw [ResidueField.map_residue, hι, hev]
  let L : ResidueField R →ₗ[ResidueField A] D :=
    { toFun := fun x => ⟨ι x, hrange x⟩
      map_add' := fun x y => Subtype.ext (map_add ι x y)
      map_smul' := fun y x => Subtype.ext (by
        simp only [Algebra.smul_def, map_mul, hcompat, RingHom.id_apply]
        rfl) }
  have hfin : Module.Finite (ResidueField A) (ResidueField R) :=
    FiniteDimensional.of_injective L (fun x y h => ι.injective (congrArg Subtype.val h))
  rw [← ResidueField.map_comp_residue f]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ residue_surjective)

end Alg

/- English proof (translation)
Use `haveI : p.asIdeal.IsPrime := p.isPrime`. Use `haveI : IsDomain (R ⧸ p.asIdeal) := Ideal.Quotient.isDomain _`. Establish `hcomap : p.asIdeal.comap (Scheme.stalkClosedPointTo ξ).hom = maximalIdeal (S.presheaf.stalk (ξ (closedPoint R)))`. Establish `e2 : S.fromSpecStalk _ (Spec.map (Scheme.stalkClosedPointTo ξ) p) = S.fromSpecStalk _ (closedPoint (S.presheaf.stalk (ξ (closedPoint R))))`. Rewrite using `[Scheme.fromSpecStalk_closedPoint, ← Scheme.Hom.comp_apply, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hp]`.

Establish `e3` using `(S.fromSpecStalk (ξ (closedPoint R))).isEmbedding.injective e2`. Conclude with `congrArg PrimeSpectrum.asIdeal e3`. Set `ev : R →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))` to `(algebraMap (FractionRing (R ⧸ p.asIdeal)) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).comp ((algebraMap (R ⧸ p.asIdeal) (FractionRing (R ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal))`. Establish `hker0 : ∀ (P : Ideal R) [P.IsPrime], RingHom.ker ((algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).comp ((algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P))) = P`. Introduce `P _`.

Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).injective, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]`. Establish `hker : RingHom.ker ev = p.asIdeal` using `hker0 p.asIdeal`. Establish `hev0 : ∀ a ∈ maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))), (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a = 0` using `fun a ha => by`. Rewrite `ha` using `[← hcomap]`.

Use `show ev ((Scheme.stalkClosedPointTo ξ).hom a) = 0`. Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `ha`. Set `ψ : ResidueField (S.presheaf.stalk (ξ (closedPoint R))) →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))` to `Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (ξ (closedPoint R)))) (ev.comp (Scheme.stalkClosedPointTo ξ).hom) hev0`. Use `letI alg : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := ψ.toAlgebra`.

Set `k₀ : Subfield (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))` to `(algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).toSubfield`. Establish `hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x` using `fun x => mem_algebraicClosure_iff`. Establish `hev : ∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) (residue (S.presheaf.stalk (ξ (closedPoint R))) a)` using `fun a => rfl`. Establish `hk₀ : IsAlgClosed (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))))` using `IsAlgClosure.isAlgClosed (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))`. Establish `hpts : ∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)`.

Introduce `q`. Use `haveI : q.asIdeal.IsPrime := q.isPrime`. Rewrite using `[Scheme.Hom.comp_apply, ← hp]`. Use `congr 1`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Use `show Ideal.comap ev q.asIdeal = p.asIdeal`. Rewrite using `[Ideal.eq_bot_of_prime q.asIdeal, ← RingHom.ker_eq_comap_bot, hker]`. Establish `hψ₀ : ∀ a, (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a ∈ k₀` using `fun a => (hmem _).mpr (by rw [RingHom.comp_apply, hev]; exact isAlgebraic_algebraMap _)`. Set `ψ₀ : S.presheaf.stalk (ξ (closedPoint R)) →+* k₀` to `(ev.comp (Scheme.stalkClosedPointTo ξ).hom).codRestrict k₀ hψ₀`. Establish `hP₀ : spMap k₀.subtype ≫ (Spec.map (CommRingCat.ofHom ψ₀) ≫ S.fromSpecStalk (ξ (closedPoint R))) = spMap ev ≫ ξ` using `by conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]`.

Rewrite using `[← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Conclude with `⟨AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)), inferInstance, inferInstance, alg, ev, k₀, hk₀, hker, hev, hmem, hpts, _, hP₀⟩`.
-/
theorem exists_geomPoint {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S) (p : Sp R)
    (hp : ξ p = ξ (closedPoint R)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K)
      (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ ∧ RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x) ∧
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) ∧ ∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  haveI : IsDomain (R ⧸ p.asIdeal) := Ideal.Quotient.isDomain _

  have hcomap : p.asIdeal.comap (Scheme.stalkClosedPointTo ξ).hom = maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))) := by
    have e2 : S.fromSpecStalk _ (Spec.map (Scheme.stalkClosedPointTo ξ) p) =
        S.fromSpecStalk _ (closedPoint (S.presheaf.stalk (ξ (closedPoint R)))) := by
      rw [Scheme.fromSpecStalk_closedPoint, ← Scheme.Hom.comp_apply,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hp]
    have e3 := (S.fromSpecStalk (ξ (closedPoint R))).isEmbedding.injective e2
    exact congrArg PrimeSpectrum.asIdeal e3

  let ev : R →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)) :=
    (algebraMap (FractionRing (R ⧸ p.asIdeal)) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).comp ((algebraMap (R ⧸ p.asIdeal) (FractionRing (R ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal))
  have hker0 : ∀ (P : Ideal R) [P.IsPrime],
      RingHom.ker ((algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).comp
        ((algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P))) = P := by
    intro P _
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker ev = p.asIdeal := hker0 p.asIdeal
  have hev0 : ∀ a ∈ maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))), (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a = 0 := fun a ha => by
    rw [← hcomap] at ha
    show ev ((Scheme.stalkClosedPointTo ξ).hom a) = 0
    rw [← RingHom.mem_ker, hker]
    exact ha
  let ψ : ResidueField (S.presheaf.stalk (ξ (closedPoint R))) →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)) := Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (ξ (closedPoint R)))) (ev.comp (Scheme.stalkClosedPointTo ξ).hom) hev0
  letI alg : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := ψ.toAlgebra
  let k₀ : Subfield (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).toSubfield
  have hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x := fun x => mem_algebraicClosure_iff
  have hev : ∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) (residue (S.presheaf.stalk (ξ (closedPoint R))) a) := fun a => rfl
  have hk₀ : IsAlgClosed (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))
      (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))) :=
    IsAlgClosure.isAlgClosed (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))

  have hpts : ∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R) := by
    intro q
    haveI : q.asIdeal.IsPrime := q.isPrime
    rw [Scheme.Hom.comp_apply, ← hp]
    congr 1
    apply PrimeSpectrum.ext
    show Ideal.comap ev q.asIdeal = p.asIdeal
    rw [Ideal.eq_bot_of_prime q.asIdeal, ← RingHom.ker_eq_comap_bot, hker]

  have hψ₀ : ∀ a, (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a ∈ k₀ := fun a =>
    (hmem _).mpr (by rw [RingHom.comp_apply, hev]; exact isAlgebraic_algebraMap _)
  let ψ₀ : S.presheaf.stalk (ξ (closedPoint R)) →+* k₀ := (ev.comp (Scheme.stalkClosedPointTo ξ).hom).codRestrict k₀ hψ₀
  have hP₀ : spMap k₀.subtype ≫ (Spec.map (CommRingCat.ofHom ψ₀) ≫ S.fromSpecStalk (ξ (closedPoint R))) =
      spMap ev ≫ ξ := by
    conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  exact ⟨AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)), inferInstance, inferInstance, alg, ev, k₀, hk₀, hker, hev, hmem, hpts, _, hP₀⟩

/- English proof (translation)
Introduce and unpack `_ ⟨c, rfl⟩`. Establish `key : ∀ g : Sp R ⟶ Sp F, g = spMap b → (Sp F).presheaf.germ ⊤ (g (closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo g = (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b`. Introduce and unpack `g rfl`. Conclude with `Scheme.germ_stalkClosedPointTo_Spec _`. Establish `e` using `key _ h`.

Rewrite `e` using `[Scheme.stalkClosedPointTo_comp]`. Use `⟨σ.stalkMap (ξ (closedPoint R)) ((Sp F).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)), ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)) e`. Establish `h2 : ((Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c) = b c` using `by simp`. Rewrite using `[← h2, ← h1]`.

Both sides reduce to the same expression.
-/
theorem range_subset_stalk {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (h : ξ ≫ σ = spMap b) :
    Set.range b ⊆ Set.range (Scheme.stalkClosedPointTo ξ).hom := by
  rintro _ ⟨c, rfl⟩
  have key : ∀ g : Sp R ⟶ Sp F, g = spMap b →
      (Sp F).presheaf.germ ⊤ (g (closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo g =
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b := by
    rintro g rfl
    exact Scheme.germ_stalkClosedPointTo_Spec _
  have e := key _ h
  rw [Scheme.stalkClosedPointTo_comp] at e
  refine ⟨σ.stalkMap (ξ (closedPoint R))
    ((Sp F).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)), ?_⟩
  have h1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)) e
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b).hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c) = b c := by simp
  rw [← h2, ← h1]
  rfl

/- English proof (translation)
Take `⟨g, rfl⟩` from `Spec.map_surjective σ`. Establish `h' : g ≫ CommRingCat.ofHom u = CommRingCat.ofHom b ≫ CommRingCat.ofHom u`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_comp]`. Conclude with `h`.

Use `show Spec.map g = Spec.map (CommRingCat.ofHom b)`. Use `congr 1`. Use extensionality with `x`. Apply `hu` to reduce the goal to its premises. Simplify using `using congrArg (fun φ => φ.hom x) h'`.
-/
theorem eq_spMap_of_injective {F R K : Type} [CommRing F] [CommRing R] [CommRing K] (u : R →+* K)
    (hu : Function.Injective u) (σ : Sp R ⟶ Sp F) (b : F →+* R) (h : spMap u ≫ σ = spMap u ≫ spMap b) :
    σ = spMap b := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective σ
  have h' : g ≫ CommRingCat.ofHom u = CommRingCat.ofHom b ≫ CommRingCat.ofHom u := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  show Spec.map g = Spec.map (CommRingCat.ofHom b)
  congr 1
  ext x
  apply hu
  simpa using congrArg (fun φ => φ.hom x) h'

/- English proof (translation)
Use `letI : Algebra k L := ψ.toAlgebra`. Set `E : IntermediateField k K` to `k₀.toIntermediateField (fun x => (hmem _).mpr (isAlgebraic_algebraMap x))`. Use `haveI : Algebra.IsAlgebraic k E := ⟨fun x => IntermediateField.isAlgebraic_iff.mpr ((hmem _).mp x.2)⟩`. Conclude with `⟨(IsAlgClosed.lift : E →ₐ[k] L).toRingHom⟩`.
-/
private theorem nonempty_ringHom_of_algebraic_subfield {k K L : Type} [Field k] [Field K] [Field L] [IsAlgClosed L] [Algebra k K]
    (k₀ : Subfield K) (hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic k x) (ψ : k →+* L) : Nonempty (k₀ →+* L) := by
  letI : Algebra k L := ψ.toAlgebra
  let E : IntermediateField k K :=
    k₀.toIntermediateField (fun x => (hmem _).mpr (isAlgebraic_algebraMap x))
  haveI : Algebra.IsAlgebraic k E :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.mpr ((hmem _).mp x.2)⟩
  exact ⟨(IsAlgClosed.lift : E →ₐ[k] L).toRingHom⟩

/- English proof (translation)
Establish `key : ∀ p : Sp R, ξ p = ξ (closedPoint R) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K) (ev : R →+* K), RingHom.ker ev = p.asIdeal ∧ (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧ (∀ r ∈ maxima …`. Introduce `p hp`. Take `⟨K, _, _, _, ev, k₀, hk₀, hker, hev, hmem, hpts, hP₀⟩` from `exists_geomPoint ξ p hp`. Establish `hemb : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R))` using `nonempty_ringHom_of_algebraic_subfield k₀ hmem ((algebraMap (ResidueField R) (AlgebraicClosure (ResidueField R))).comp (ResidueField.map (Scheme.stalkClosedPointTo ξ).hom))`. Take `⟨h1, h2⟩` from `hc K ev k₀ hk₀ hemb hpts hP₀`.

Conclude with `⟨K, inferInstance, inferInstance, ev, hker, hev, h1, fun r => (hmem _).mp (h2 r)⟩`. Prove the components needed by the constructor for the conclusion. Introduce `p hp`. Take `⟨K, _, _, ev, hker, -, h1, -⟩` from `key p hp`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Use `le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_` and prove the remaining obligations. Introduce `r hr`. Rewrite using `[← hker]`. Conclude with `h1 r hr`. Take `⟨K, _, _, ev, hker, hev, -, h2⟩` from `key (closedPoint R) rfl`.

Use `letI : Algebra F (ResidueField R) := ((residue R).comp b).toAlgebra`. Use `haveI : Algebra.EssFiniteType F (ResidueField R) := hft`. Take `⟨s, hs⟩` from `Algebra.EssFiniteType.cond (R := F) (S := ResidueField R)`. Set `lift : ResidueField R → R` to `fun z => (residue_surjective z).choose`. Establish `hlift : ∀ z, residue R (lift z) = z` using `fun z => (residue_surjective z).choose_spec`.

Set `G : Finset R` to `s.image lift`. Establish `hadj : ∀ z ∈ Algebra.adjoin F (s : Set (ResidueField R)), ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)), residue R a = z`. Introduce `z hz`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Conclude with `⟨lift x, Subring.subset_closure (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))), hlift x⟩`. Consider the case `algebraMap x => exact ⟨b x, Subring.subset_closure (Or.inl ⟨x, rfl⟩), rfl⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨c, hc, rfl⟩` from `hy`.

Conclude with `⟨a + c, add_mem ha hc, map_add _ _ _⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨c, hc, rfl⟩` from `hy`. Conclude with `⟨a * c, mul_mem ha hc, map_mul _ _ _⟩`.

Establish `hb' : ∀ r : R, ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)), ∃ c ∈ Subring.closure (Set.range b ∪ (G : Set R)), c ∉ maximalIdeal R ∧ c * r - a ∈ maximalIdeal R`. Introduce `r`. Take `⟨⟨x, y⟩, hxy⟩` from `IsLocalization.mk'_surjective ((IsUnit.submonoid (ResidueField R)).comap (algebraMap (Algebra.adjoin F (s : Set (ResidueField R))) (ResidueField R))) (S := ResidueField R) (residue R r)`. Establish `hspec` using `IsLocalization.mk'_spec (ResidueField R) x y`. Simplify using `only at hxy`.

Rewrite `hspec` using `[hxy]`. Take `⟨a, ha, hae⟩` from `hadj x.1 x.2`. Take `⟨c, hc, hce⟩` from `hadj y.1.1 y.1.2`. Establish `hyu : IsUnit (y.1.1 : ResidueField R)` using `y.2`. Use `⟨a, ha, c, hc, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← residue_eq_zero_iff, hce]`. Conclude with `hyu.ne_zero`. Rewrite using `[← residue_eq_zero_iff, map_sub, map_mul, hce, hae, mul_comm, sub_eq_zero]`. Conclude with `hspec`. Conclude with `finite_residue (Scheme.stalkClosedPointTo ξ).hom ev hker hev (range_subset_stalk ξ σ b hb) hb' (fun g _ => h2 g)`.
-/
theorem quasiFinite_of_pointRigid {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (hb : ξ ≫ σ = spMap b) (hft : ((residue R).comp b).EssFiniteType)
    (hc : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) →
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) → (∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ) →
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀) :
    (∀ p : Sp R, ξ p = ξ (closedPoint R) → p = closedPoint R) ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  classical

  have key : ∀ p : Sp R, ξ p = ξ (closedPoint R) → ∃ (K : Type) (_ : Field K)
      (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K) (ev : R →+* K),
      RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧
      ∀ r, IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (ev r) := by
    intro p hp
    obtain ⟨K, _, _, _, ev, k₀, hk₀, hker, hev, hmem, hpts, hP₀⟩ := exists_geomPoint ξ p hp
    have hemb : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) :=
      nonempty_ringHom_of_algebraic_subfield k₀ hmem ((algebraMap (ResidueField R) (AlgebraicClosure (ResidueField R))).comp
        (ResidueField.map (Scheme.stalkClosedPointTo ξ).hom))
    obtain ⟨h1, h2⟩ := hc K ev k₀ hk₀ hemb hpts hP₀
    exact ⟨K, inferInstance, inferInstance, ev, hker, hev, h1, fun r => (hmem _).mp (h2 r)⟩
  constructor
  · intro p hp
    obtain ⟨K, _, _, ev, hker, -, h1, -⟩ := key p hp
    apply PrimeSpectrum.ext
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro r hr
    rw [← hker]
    exact h1 r hr
  · obtain ⟨K, _, _, ev, hker, hev, -, h2⟩ := key (closedPoint R) rfl

    letI : Algebra F (ResidueField R) := ((residue R).comp b).toAlgebra
    haveI : Algebra.EssFiniteType F (ResidueField R) := hft
    obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := F) (S := ResidueField R)
    let lift : ResidueField R → R := fun z => (residue_surjective z).choose
    have hlift : ∀ z, residue R (lift z) = z := fun z => (residue_surjective z).choose_spec
    let G : Finset R := s.image lift
    have hadj : ∀ z ∈ Algebra.adjoin F (s : Set (ResidueField R)),
        ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)), residue R a = z := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        exact ⟨lift x, Subring.subset_closure (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))),
          hlift x⟩
      | algebraMap x => exact ⟨b x, Subring.subset_closure (Or.inl ⟨x, rfl⟩), rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨a + c, add_mem ha hc, map_add _ _ _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨a * c, mul_mem ha hc, map_mul _ _ _⟩
    have hb' : ∀ r : R, ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)),
        ∃ c ∈ Subring.closure (Set.range b ∪ (G : Set R)),
          c ∉ maximalIdeal R ∧ c * r - a ∈ maximalIdeal R := by
      intro r
      obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective
        ((IsUnit.submonoid (ResidueField R)).comap
          (algebraMap (Algebra.adjoin F (s : Set (ResidueField R))) (ResidueField R)))
        (S := ResidueField R) (residue R r)
      have hspec := IsLocalization.mk'_spec (ResidueField R) x y
      simp only at hxy
      rw [hxy] at hspec
      obtain ⟨a, ha, hae⟩ := hadj x.1 x.2
      obtain ⟨c, hc, hce⟩ := hadj y.1.1 y.1.2
      have hyu : IsUnit (y.1.1 : ResidueField R) := y.2
      refine ⟨a, ha, c, hc, ?_, ?_⟩
      · rw [← residue_eq_zero_iff, hce]
        exact hyu.ne_zero
      · rw [← residue_eq_zero_iff, map_sub, map_mul, hce, hae, mul_comm, sub_eq_zero]
        exact hspec
    exact finite_residue (Scheme.stalkClosedPointTo ξ).hom ev hker hev (range_subset_stalk ξ σ b hb) hb'
      (fun g _ => h2 g)

end GlobalTheory.ChartQF
