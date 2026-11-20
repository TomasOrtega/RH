import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealOfFlatStalkPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTestStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemIdealSheafStalkOfClosedFibreUnivClosedStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.ApproxCorr

/- English proof (translation)
Establish `h1` using `Ideal.mem_map_of_mem φ h`. Rewrite `h1` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) n h1`.
-/
theorem map_mem_pow {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    {n : ℕ} {a : A} (h : a ∈ maximalIdeal A ^ n) : φ a ∈ maximalIdeal B ^ n := by
  have h1 := Ideal.mem_map_of_mem φ h
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) n h1

/- English proof (translation)
Establish `k` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ I) (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top`. Establish `: Submodule.mkQ I c ∈ (⊥ : Submodule C (C ⧸ I))`. Rewrite using `[← k, Submodule.mem_iInf]`. Introduce `n`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (h n)`.

Establish `e : Submodule.mkQ I (a + b) = b • Submodule.mkQ I 1`. Rewrite using `[map_add, ← map_smul, smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero I).2 ha |> (Submodule.mkQ_apply I a).trans, zero_add]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul hb trivial`. Conclude with `(Submodule.Quotient.mk_eq_zero I).1 ((Submodule.mem_bot C).1 this)`.
-/
theorem mem_of_forall_mem_sup {C : Type} [CommRing C] [IsLocalRing C] [IsNoetherianRing C] (I : Ideal C) (c : C)
    (h : ∀ n : ℕ, c ∈ I ⊔ maximalIdeal C ^ n) : c ∈ I := by
  have k := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ I) (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top
  have : Submodule.mkQ I c ∈ (⊥ : Submodule C (C ⧸ I)) := by
    rw [← k, Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h n)
    have e : Submodule.mkQ I (a + b) = b • Submodule.mkQ I 1 := by
      rw [map_add, ← map_smul, smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero I).2 ha |> (Submodule.mkQ_apply I a).trans,
        zero_add]
    rw [e]
    exact Submodule.smul_mem_smul hb trivial
  exact (Submodule.Quotient.mk_eq_zero I).1 ((Submodule.mem_bot C).1 this)

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨(π.stalkMap x).hom, π.toLRSHom.prop x, Scheme.SpecMap_stalkMap_fromSpecStalk π⟩`.
-/
theorem exists_stalk_map {Z S : Scheme.{0}} (π : S ⟶ Z) (x : S) (z : Z) (h : π x = z) :
    ∃ ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x, IsLocalHom ψ ∧
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π := by
  subst h
  exact ⟨(π.stalkMap x).hom, π.toLRSHom.prop x, Scheme.SpecMap_stalkMap_fromSpecStalk π⟩

/- English proof (translation)
Rewrite using `[← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]`. Generalize the expression as in `hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ`. Establish `hfl : Flat ξ`. Rewrite using `[← hξ]`. Use `haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z`.

Use `haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi`. Use `infer_instance`. Establish `hξc : ξ (closedPoint R) = z`. Rewrite using `[← hξ]`. Establish `: Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z)` using `IsLocalRing.comap_closedPoint i`.

Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)`. Use `GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_` and prove the remaining obligations. Rewrite using `[Scheme.stalkClosedPointTo, CommRingCat.hom_comp]`. Conclude with `RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))`. Use `GlobalTheory.T.germ_mem_idealSheaf_stalk_of_closedFibre_univClosed _ R (Limits.pullback.fst ξ π) _ _ fun v hv => ?_` and prove the remaining obligations.

Use `haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)`. Use `set p := Limits.pullback.fst ξ π with hp`. Use `set q := Limits.pullback.snd ξ π with hq`. Establish `hpq : p ≫ ξ = q ≫ π` using `Limits.pullback.condition`. Establish `hx : π (q v) = z`.

Rewrite using `[← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]`. Take `⟨ψ, hψ, hψc⟩` from `exists_stalk_map π (q v) z hx`. Set `α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v` to `((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v`. Establish `hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p`. Rewrite using `[Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]`.

Use `haveI : IsLocalHom α.hom := by`. Use `(IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map α (closedPoint _) = _`. Rewrite using `[hα]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)`.

Use `haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v`. Establish `hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v`. Use `Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)` and prove the remaining obligations. Rewrite using `[Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]`. Use `erw [hψc]`.

Rewrite using `[Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]`. Establish `hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t)` using `fun t => congrArg (fun f => f.hom t) hc`. Establish `e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F` using `(Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm`. Rewrite using `[e]`. Use `mem_of_forall_mem_sup _ _ fun n => ?_` and prove the remaining obligations.

Take `⟨b, hb, c, hc, hbc⟩` from `Submodule.mem_sup.1 (H (q v) ψ hψ hψc n)`. Establish `e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a n)))`. Rewrite using `[← add_assoc, ← map_add, hbc, ← hc', map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb)) (add_mem (map_mem_pow _ hc) (map_mem_pow _ (ha n)))`.
-/
theorem mem_map_of_approx {Z S : Scheme.{0}} (π : S ⟶ Z) [IsProper π] (I : S.IdealSheafData) (z : Z)
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (i : Z.presheaf.stalk z →+* R) [IsLocalHom i] (hi : i.Flat)
    (F : R) (a : ℕ → Z.presheaf.stalk z) (ha : ∀ n, F - i (a n) ∈ maximalIdeal R ^ n)
    (H : ∀ (x : S) (ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x), IsLocalHom ψ →
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π → ∀ n, ψ (a n) ∈ FinalTheorems.stalkId I x ⊔ maximalIdeal _ ^ n) :
    F ∈ (FinalTheorems.stalkId (I.map π) z).map i := by
  rw [← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]
  generalize hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ
  have hfl : Flat ξ := by
    rw [← hξ]
    haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z
    haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi
    infer_instance
  have hξc : ξ (closedPoint R) = z := by
    rw [← hξ]
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  refine GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_
  · rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  refine GlobalTheory.T.germ_mem_idealSheaf_stalk_of_closedFibre_univClosed _ R (Limits.pullback.fst ξ π) _ _ fun v hv => ?_
  haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)
  set p := Limits.pullback.fst ξ π with hp
  set q := Limits.pullback.snd ξ π with hq
  have hpq : p ≫ ξ = q ≫ π := Limits.pullback.condition
  have hx : π (q v) = z := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]
  obtain ⟨ψ, hψ, hψc⟩ := exists_stalk_map π (q v) z hx
  let α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v
  have hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  haveI : IsLocalHom α.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_
    change Spec.map α (closedPoint _) = _
    rw [hα]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)
  haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v
  have hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v := by
    refine Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)
    rw [Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]
    erw [hψc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  have hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t) := fun t => congrArg (fun f => f.hom t) hc
  have e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F :=
    (Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm
  rw [e]
  refine mem_of_forall_mem_sup _ _ fun n => ?_
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 (H (q v) ψ hψ hψc n)
  have e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a n))) := by
    rw [← add_assoc, ← map_add, hbc, ← hc', map_sub]; ring
  rw [e2]
  exact Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb))
    (add_mem (map_mem_pow _ hc) (map_mem_pow _ (ha n)))

/- English proof (translation)
Set `y : PrimeSpectrum ℤ` to `s x`. Use `letI A : Algebra ℤ ((Sp ℤ).presheaf.stalk (s x)) := StructureSheaf.stalkAlgebra _ y`. Use `haveI : @IsLocalization.AtPrime ℤ _ ((Sp ℤ).presheaf.stalk (s x)) _ A y.asIdeal _ := StructureSheaf.IsLocalization.to_stalk _ y`. Set `φ` to `@algebraMap ℤ ((Sp ℤ).presheaf.stalk (s x)) _ _ A`. Establish `h₁ : (s.stalkMap x).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap s x`.

Establish `h₂ : φ.EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)`. Establish `hφ : Function.Injective φ` using `IsLocalization.injective ((Sp ℤ).presheaf.stalk (s x)) y.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `: IsLocalHom (s.stalkMap x).hom` using `s.toLRSHom.prop x`. Establish `hσ : Function.Injective (s.stalkMap x).hom`. Establish `h` using `Flat.stalkMap s x`.

Use `algebraize [(s.stalkMap x).hom]`. Establish `: IsLocalHom (algebraMap ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x))` using `this`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp ℤ).presheaf.stalk (s x)) (B := S.presheaf.stalk x)` as an intermediate fact. Conclude with `FaithfulSMul.algebraMap_injective ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)`. Use `⟨charZero_of_injective_ringHom (f := (s.stalkMap x).hom.comp φ) (hσ.comp hφ), ?_⟩` and prove the remaining obligations.

Use `RingHom.essFiniteType_algebraMap.1 ?_` and prove the remaining obligations. Use `h₂.comp h₁ using 1` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.
-/
theorem charZero_essFiniteType {S : Scheme.{0}} (s : S ⟶ Sp ℤ) [Flat s] [LocallyOfFiniteType s] (x : S) :
    CharZero (S.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (S.presheaf.stalk x) := by
  let y : PrimeSpectrum ℤ := s x
  letI A : Algebra ℤ ((Sp ℤ).presheaf.stalk (s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime ℤ _ ((Sp ℤ).presheaf.stalk (s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap ℤ ((Sp ℤ).presheaf.stalk (s x)) _ _ A
  have h₁ : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp ℤ).presheaf.stalk (s x)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsLocalHom (s.stalkMap x).hom := s.toLRSHom.prop x
  have hσ : Function.Injective (s.stalkMap x).hom := by
    have h := Flat.stalkMap s x
    algebraize [(s.stalkMap x).hom]
    have : IsLocalHom (algebraMap ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)) := this
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp ℤ).presheaf.stalk (s x)) (B := S.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)
  refine ⟨charZero_of_injective_ringHom (f := (s.stalkMap x).hom.comp φ) (hσ.comp hφ), ?_⟩
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert h₂.comp h₁ using 1
  exact Subsingleton.elim _ _

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Establish `hg : genericPoint S ∈ Set.range (S.fromSpecStalk x)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `genericPoint_specializes x`. Take `⟨w, hw⟩` from `hg`.

Establish `ht : (jK V ≫ spMap ρ) t ⤳ w`. Use `(PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_` and prove the remaining obligations. Establish `h0 : algebraMap V (FractionRing V) (ρ r) ∈ t.asIdeal` using `hr`. Establish `h1 : algebraMap V (FractionRing V) (ρ r) = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 (Ne.isUnit hne))`. Establish `h2 : r = 0` using `hρ (by rw [map_zero]; exact IsFractionRing.injective V (FractionRing V) (by rw [h1, map_zero]))`. Rewrite using `[h2]`. Conclude with `zero_mem _`. Establish `h3` using `ht.map (S.fromSpecStalk x).continuous`.

Rewrite using `[← Category.assoc, Scheme.Hom.comp_apply]`. Establish `h4 : S.fromSpecStalk x ((jK V ≫ spMap ρ) t) = genericPoint S` using `((show _ ⤳ genericPoint S from hw ▸ h3).antisymm (genericPoint_specializes _)).eq`. Rewrite using `[h4]`. Conclude with `((genericPoint_spec S).mem_open_set_iff U.2).2 (by simpa using hU)`.
-/
theorem range_subset {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : (U : Set S).Nonempty) (x : S)
    {V : Type} [CommRing V] [IsDomain V] (ρ : S.presheaf.stalk x →+* V) (hρ : Function.Injective ρ) :
    Set.range (jK V ≫ spMap ρ ≫ S.fromSpecStalk x) ⊆ U := by
  rintro _ ⟨t, rfl⟩
  have hg : genericPoint S ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
  obtain ⟨w, hw⟩ := hg
  have ht : (jK V ≫ spMap ρ) t ⤳ w := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h0 : algebraMap V (FractionRing V) (ρ r) ∈ t.asIdeal := hr
    have h1 : algebraMap V (FractionRing V) (ρ r) = 0 := by
      by_contra hne
      exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 (Ne.isUnit hne))
    have h2 : r = 0 := hρ (by rw [map_zero]; exact IsFractionRing.injective V (FractionRing V) (by rw [h1, map_zero]))
    rw [h2]; exact zero_mem _
  have h3 := ht.map (S.fromSpecStalk x).continuous
  rw [← Category.assoc, Scheme.Hom.comp_apply]
  have h4 : S.fromSpecStalk x ((jK V ≫ spMap ρ) t) = genericPoint S :=
    ((show _ ⤳ genericPoint S from hw ▸ h3).antisymm (genericPoint_specializes _)).eq
  rw [h4]
  exact ((genericPoint_spec S).mem_open_set_iff U.2).2 (by simpa using hU)

/- English proof (translation)
Introduce `Z S _ _ sZ _ _ π _ _ _ hS U hU E z k`. Use `haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ`. Set `K : ℕ → Ideal (Z.presheaf.stalk z)` to `fun e => { carrier := {f | ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev → spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U → ev f …`. Rewrite using `[map_add]`. Conclude with `add_mem (ha V hV ξ ev h1 h2 h3) (hb V hV ξ ev h1 h2 h3)`.

Use the proof step `zero_mem' := fun V _ _ _ _ hV ξ ev h1 h2 h3 => by rw [map_zero]; exact zero_mem _`. Use the proof step `smul_mem' := fun c a ha V _ _ _ _ hV ξ ev h1 h2 h3 => by`. Rewrite using `[smul_eq_mul, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (ha V hV ξ ev h1 h2 h3) }`. Use `GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (Z.presheaf.stalk z) K (FinalTheorems.stalkId (E.idealSheaf.map π) z) ?_ ?_ ?_ k` and prove the remaining obligations.

Introduce `m n hmn f hf V _ _ _ _ hV ξ ev h1 h2 h3`. Conclude with `(show _ ≤ (_ : Ideal V) from sup_le_sup_left (Ideal.pow_le_pow_right hmn) _) (hf V hV ξ ev h1 h2 h3)`. Introduce `e f hf V _ _ _ _ hV ξ ev h1 h2 h3`. Use `Ideal.mem_sup_right ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow]`.

Conclude with `Ideal.mem_map_of_mem _ hf`. Introduce `F a ha hK`. Use `haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (Z.presheaf.stalk z))`. Use `haveI : Module.FaithfullyFlat (Z.presheaf.stalk z) (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) := Module.FaithfullyFlat.of_flat_of_isLocalHom`. Use `mem_map_of_approx π E.idealSheaf z _ (RingHom.flat_algebraMap_iff.2 inferInstance) F a ha fun x ψ hψ hc => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩ : ∃ i, x ∈ E.U i` from `TopologicalSpace.Opens.mem_iSup.1 (E.cover ▸ trivial)`. Take `⟨h0, hft⟩` from `charZero_essFiniteType (π ≫ sZ) x`. Use `haveI := (hS x).2`. Establish `hI` using `E.stalkId_idealSheaf i x hi`. Rewrite using `[hI]`.

Use `GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test (S.presheaf.stalk x) _ (fun n => ψ (a n)) (nonZeroDivisors.ne_zero (GlobalTheory.Cartier.isRegularFn_iff_germ.1 (E.regular i) x hi)) ?_ ?_` and prove the remaining obligations. Introduce `m n hmn`. Rewrite using `[← map_sub]`. Use `map_mem_pow ψ ?_` and prove the remaining obligations. Rewrite using `[← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) (maximalIdeal (Z.presheaf.stalk z) ^ m), Ideal.mem_comap, Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, map_sub]`.

Use `sub_mem (Ideal.pow_le_pow_right hmn (ha n)) (ha m)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Introduce `V _ _ _ _ hV ρ hρ hl e`. Establish `hl' : IsLocalHom (ρ.comp ψ)` using `inferInstance`. Establish `h1` using `hK e V hV (spMap ρ ≫ S.fromSpecStalk x) (ρ.comp ψ) hl' (by`.

Rewrite using `[Category.assoc, ← hc, ← Category.assoc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]) (range_subset U hU x ρ hρ)`. Rewrite `h1` using `[GlobalTheory.PolDiv.idlAlong_fromSpecStalk, hI, Ideal.map_span, Set.image_singleton]`. Conclude with `(show _ ≤ (_ : Ideal V) from sup_le_sup_left (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (ρ.comp ψ)) e) _) h1`.
-/
theorem exists_correction : ∀ (Z S : Scheme.{0}) [IsIntegral Z] [IsIntegral S] (sZ : Z ⟶ Sp ℤ) [LocallyOfFiniteType sZ] [QuasiCompact sZ] (π : S ⟶ Z) [IsProper π] [IsDominant π] [Flat (π ≫ sZ)], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (E : GlobalTheory.EffCartierData S) (z : Z) (k : ℕ), ∃ e : ℕ, ∀ f : Z.presheaf.stalk z, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev → spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U → ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e) → f ∈ FinalTheorems.stalkId (E.idealSheaf.map π) z ⊔ maximalIdeal _ ^ k := by
  intro Z S _ _ sZ _ _ π _ _ _ hS U hU E z k
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let K : ℕ → Ideal (Z.presheaf.stalk z) := fun e =>
    { carrier := {f | ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev →
        spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U →
        ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e}
      add_mem' := fun ha hb V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [map_add]; exact add_mem (ha V hV ξ ev h1 h2 h3) (hb V hV ξ ev h1 h2 h3)
      zero_mem' := fun V _ _ _ _ hV ξ ev h1 h2 h3 => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun c a ha V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ (ha V hV ξ ev h1 h2 h3) }
  refine GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (Z.presheaf.stalk z) K (FinalTheorems.stalkId (E.idealSheaf.map π) z) ?_ ?_ ?_ k
  · intro m n hmn f hf V _ _ _ _ hV ξ ev h1 h2 h3
    exact (show _ ≤ (_ : Ideal V) from sup_le_sup_left (Ideal.pow_le_pow_right hmn) _) (hf V hV ξ ev h1 h2 h3)
  · intro e f hf V _ _ _ _ hV ξ ev h1 h2 h3
    refine Ideal.mem_sup_right ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf
  intro F a ha hK
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (Z.presheaf.stalk z))
  haveI : Module.FaithfullyFlat (Z.presheaf.stalk z) (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine mem_map_of_approx π E.idealSheaf z _ (RingHom.flat_algebraMap_iff.2 inferInstance) F a ha fun x ψ hψ hc => ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ E.U i := TopologicalSpace.Opens.mem_iSup.1 (E.cover ▸ trivial)
  obtain ⟨h0, hft⟩ := charZero_essFiniteType (π ≫ sZ) x
  haveI := (hS x).2
  have hI := E.stalkId_idealSheaf i x hi
  rw [hI]
  refine GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test (S.presheaf.stalk x) _ (fun n => ψ (a n))
    (nonZeroDivisors.ne_zero (GlobalTheory.Cartier.isRegularFn_iff_germ.1 (E.regular i) x hi)) ?_ ?_
  · intro m n hmn
    rw [← map_sub]
    refine map_mem_pow ψ ?_
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
      (maximalIdeal (Z.presheaf.stalk z) ^ m), Ideal.mem_comap, Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, map_sub]
    have := sub_mem (Ideal.pow_le_pow_right hmn (ha n)) (ha m)
    rwa [sub_sub_sub_cancel_left] at this
  · intro V _ _ _ _ hV ρ hρ hl e
    have hl' : IsLocalHom (ρ.comp ψ) := inferInstance
    have h1 := hK e V hV (spMap ρ ≫ S.fromSpecStalk x) (ρ.comp ψ) hl' (by
      rw [Category.assoc, ← hc, ← Category.assoc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]) (range_subset U hU x ρ hρ)
    rw [GlobalTheory.PolDiv.idlAlong_fromSpecStalk, hI, Ideal.map_span, Set.image_singleton] at h1
    exact (show _ ≤ (_ : Ideal V) from
      sup_le_sup_left (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (ρ.comp ψ)) e) _) h1

end GlobalTheory.ApproxCorr
