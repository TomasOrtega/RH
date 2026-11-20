import Mathlib

open IsLocalRing

namespace GlobalTheory

section Local

variable (R S X : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]

/- English proof (translation)
Rewrite using `[IsLocalRing.length_restrictScalars R S X, Module.length_eq_finrank]`.
-/
theorem length_restrictScalars_of_isLocalHom
    [Module.Finite (ResidueField R) (ResidueField S)] :
    Module.length R X =
      Module.length S X * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) := by
  rw [IsLocalRing.length_restrictScalars R S X, Module.length_eq_finrank]

/- English proof (translation)
Rewrite using `[← Module.length_ne_top_iff, ← Module.length_ne_top_iff, length_restrictScalars_of_isLocalHom R S X]`. Establish `h : (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) ≠ 0`. Conclude with `(Module.finrank_pos (R := ResidueField R) (M := ResidueField S)).ne'` after adjusting the coercions. Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`.

Conclude with `h1 (by rw [h2, ENat.top_mul h])`. Introduce `h1`. Conclude with `WithTop.mul_ne_top h1 (ENat.coe_ne_top _)`.
-/
theorem isFiniteLength_restrictScalars_iff_of_isLocalHom
    [Module.Finite (ResidueField R) (ResidueField S)] :
    IsFiniteLength R X ↔ IsFiniteLength S X := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    length_restrictScalars_of_isLocalHom R S X]
  have h : (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ResidueField R) (M := ResidueField S)).ne'
  constructor
  · intro h1 h2
    exact h1 (by rw [h2, ENat.top_mul h])
  · intro h1
    exact WithTop.mul_ne_top h1 (ENat.coe_ne_top _)

end Local

section Localized

variable {S : Type*} [CommRing S]

/- English proof (translation)
Set `e : Localization T ≃ₐ[S] A` to `IsLocalization.algEquiv T _ _`. Use `letI : Algebra (Localization T) A := e.toRingHom.toAlgebra`. Use `letI : Module (Localization T) X' := Module.compHom X' e.toRingHom`. Use `haveI : IsScalarTower (Localization T) A X' := ⟨fun a b x => mul_smul (e a) b x⟩`. Use `haveI : IsScalarTower S (Localization T) X' := ⟨fun a b x => by`.

Express the relevant statement in the definitionally equal form `e (a • b) • x = a • (e b • x)`. Rewrite using `[map_smul, smul_assoc]⟩`. Rewrite using `[← Module.length_eq_of_surjective (S := Localization T) (R := A) (M := X') e.surjective]`. Conclude with `(((IsLocalizedModule.iso T f).extendScalarsOfIsLocalization T (Localization T)).length_eq).symm`.
-/
theorem length_eq_length_localizedModule (T : Submonoid S) (A : Type*) [CommRing A] [Algebra S A]
    [IsLocalization T A] {X X' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup X']
    [Module S X'] [Module A X'] [IsScalarTower S A X'] (f : X →ₗ[S] X') [IsLocalizedModule T f] :
    Module.length A X' = Module.length (Localization T) (LocalizedModule T X) := by
  let e : Localization T ≃ₐ[S] A := IsLocalization.algEquiv T _ _
  letI : Algebra (Localization T) A := e.toRingHom.toAlgebra
  letI : Module (Localization T) X' := Module.compHom X' e.toRingHom
  haveI : IsScalarTower (Localization T) A X' := ⟨fun a b x => mul_smul (e a) b x⟩
  haveI : IsScalarTower S (Localization T) X' := ⟨fun a b x => by
    change e (a • b) • x = a • (e b • x)
    rw [map_smul, smul_assoc]⟩
  rw [← Module.length_eq_of_surjective (S := Localization T) (R := A) (M := X') e.surjective]
  exact (((IsLocalizedModule.iso T f).extendScalarsOfIsLocalization T
    (Localization T)).length_eq).symm

/- English proof (translation)
The claim follows from `Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g) (LocalizedModule.map_injective T f hf) (LocalizedModule.map_surjective T g hg) (LocalizedModule.map_exact T f g H)`.
-/
theorem length_localizedModule_eq_add_of_exact (T : Submonoid S) {N M P : Type*}
    [AddCommGroup N] [AddCommGroup M] [AddCommGroup P] [Module S N] [Module S M] [Module S P]
    (f : N →ₗ[S] M) (g : M →ₗ[S] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) +
        Module.length (Localization T) (LocalizedModule T P) :=
  Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
    (LocalizedModule.map_injective T f hf) (LocalizedModule.map_surjective T g hg)
    (LocalizedModule.map_exact T f g H)

/- English proof (translation)
The claim follows from `(IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) (Localization T) e).length_eq`.
-/
theorem length_localizedModule_congr (T : Submonoid S) {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N] (e : M ≃ₗ[S] N) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) :=
  (IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T N) (Localization T) e).length_eq

/- English proof (translation)
Use `haveI : IsSimpleModule S (S ⧸ m) := isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl _ _⟩⟩`. Use `haveI : IsLocalizedModule m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m) := { map_units := fun s => by`. Rewrite using `[Module.End.isUnit_iff]`. Use `LinearMap.bijective_of_ne_zero fun h => s.2 ?_` and prove the remaining obligations. Use `LinearMap.congr_fun h (Ideal.Quotient.mk m 1)` as an intermediate fact.

Simplify using `only [Module.algebraMap_end_apply, LinearMap.zero_apply] at this`. Rewrite `this` using `[← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Simplify using `using this`. Use `surj := fun y => ⟨(y, 1), by simp⟩`. Use `exists_of_eq := fun h => ⟨1, by simpa using h⟩ }`.

Set `e` to `IsLocalizedModule.iso m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m)`. Use `haveI : Nontrivial (LocalizedModule m.primeCompl (S ⧸ m)) := e.toEquiv.nontrivial`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← Module.length_top]`. Use `(Submodule.length_le_length_restrictScalars S _).trans ?_` and prove the remaining obligations.

Rewrite using `[Submodule.restrictScalars_top, Module.length_top, e.length_eq, Module.length_eq_one]`. Conclude with `Order.one_le_iff_pos.mpr Module.length_pos`.
-/
theorem length_localizedModule_quotient_self (m : Ideal S) [hm : m.IsMaximal] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl (S ⧸ m)) = 1 := by
  haveI : IsSimpleModule S (S ⧸ m) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl _ _⟩⟩
  haveI : IsLocalizedModule m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m) :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        refine LinearMap.bijective_of_ne_zero fun h => s.2 ?_
        have := LinearMap.congr_fun h (Ideal.Quotient.mk m 1)
        simp only [Module.algebraMap_end_apply, LinearMap.zero_apply] at this
        rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero] at this
        simpa using this
      surj := fun y => ⟨(y, 1), by simp⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  let e := IsLocalizedModule.iso m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m)
  haveI : Nontrivial (LocalizedModule m.primeCompl (S ⧸ m)) := e.toEquiv.nontrivial
  apply le_antisymm
  · rw [← Module.length_top]
    refine (Submodule.length_le_length_restrictScalars S _).trans ?_
    rw [Submodule.restrictScalars_top, Module.length_top, e.length_eq, Module.length_eq_one]
  · exact Order.one_le_iff_pos.mpr Module.length_pos

/- English proof (translation)
Rewrite using `[Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]`. Establish `: ¬ m ≤ n` using `fun hle => h (hm.eq_of_le hn.ne_top hle).symm`. Take `⟨s, hs, hs'⟩` from `SetLike.not_le_iff_exists.mp this`. Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective m x`.

Use `⟨s, hs', ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `m.mul_mem_right _ hs`.
-/
theorem length_localizedModule_quotient_of_ne (m n : Ideal S) [hm : m.IsMaximal] [hn : n.IsPrime]
    (h : n ≠ m) :
    Module.length (Localization.AtPrime n) (LocalizedModule n.primeCompl (S ⧸ m)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  have : ¬ m ≤ n := fun hle => h (hm.eq_of_le hn.ne_top hle).symm
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp this
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective m x
  refine ⟨s, hs', ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact m.mul_mem_right _ hs

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `of_subsingleton => simp`. Consider the case `@of_simple_quotient M _ _ N hs _ ih`. Rewrite using `[length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_one S (M ⧸ N)]`. Use `add_le_add ih ?_` and prove the remaining obligations.

Take `⟨m, hm, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Rewrite using `[length_localizedModule_congr _ e]`. Distinguish the cases in `hnm : n = m`. Substitute `hnm` using the available equality. Conclude with `(length_localizedModule_quotient_self n).le`.

Rewrite using `[length_localizedModule_quotient_of_ne m n hnm]`. Conclude with `zero_le_one`.
-/
theorem length_localizedModule_atPrime_le (n : Ideal S) [n.IsPrime] {X : Type*} [AddCommGroup X]
    [Module S X] (h : IsFiniteLength S X) :
    Module.length (Localization.AtPrime n) (LocalizedModule n.primeCompl X) ≤
      Module.length S X := by
  induction h with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    rw [length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_one S (M ⧸ N)]
    refine add_le_add ih ?_
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    rw [length_localizedModule_congr _ e]
    by_cases hnm : n = m
    · subst hnm
      exact (length_localizedModule_quotient_self n).le
    · rw [length_localizedModule_quotient_of_ne m n hnm]
      exact zero_le_one

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `of_subsingleton => simp`. Consider the case `@of_simple_quotient M _ _ N hs _ ih`. Take `⟨m, hm, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Use `(ih.insert ⟨m, hm⟩).subset fun n hn => ?_` and prove the remaining obligations.

Distinguish the cases in `hnm : n.asIdeal = m`. Conclude with `Or.inl (MaximalSpectrum.ext hnm)`. Use `right`. Rewrite `hn` using `[Set.mem_setOf_eq, length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), length_localizedModule_congr _ e, length_localizedModule_quotient_of_ne m _ hnm, add_zero]`. Conclude with `hn`.
-/
theorem finite_support_length_localizedModule {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) :
    {n : MaximalSpectrum S | Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) ≠ 0}.Finite := by
  induction h with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    refine (ih.insert ⟨m, hm⟩).subset fun n hn => ?_
    by_cases hnm : n.asIdeal = m
    · exact Or.inl (MaximalSpectrum.ext hnm)
    · right
      rw [Set.mem_setOf_eq, length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ
        N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        length_localizedModule_congr _ e, length_localizedModule_quotient_of_ne m _ hnm,
        add_zero] at hn
      exact hn

end Localized

section General

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/- English proof (translation)
Use `revert iR iT hT`. Proceed by induction on `h with`. Consider the case `of_subsingleton => intros`. Simplify using the standard rewrite rules. Consider the case `@of_simple_quotient M _ _ N hs _ ih`.

Introduce `iR iT hT`. Take `⟨m, hm, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Establish `key : ∀ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl M) = Module.length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl N) + Module.length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asI …` using `fun n => by`. Rewrite using `[length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), length_localizedModule_congr _ e]`. Establish `hmT : (⟨m, hm⟩ : MaximalSpectrum S) ∈ T`.

Assume the negation of the conclusion as `hc`. Establish `h0` using `hT _ hc`. Rewrite `h0` using `[key, length_localizedModule_quotient_self m]`. Simplify using `at h0`. Rewrite using `[Module.length_eq_add_of_exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R) N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), ih (fun n hn => (add_eq_zero.mp ((key n).symm.trans (hT n hn))).1), (e.restrictScalars R).length_eq]`.

Repeatedly rewrite using `[key, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single_of_mem _ hmT]`. Rewrite using `[length_localizedModule_quotient_self m, one_mul]`. Introduce `n _ hn`.

Rewrite using `[length_localizedModule_quotient_of_ne m n.asIdeal (fun hc => hn (MaximalSpectrum.ext hc)), zero_mul]`.
-/
theorem length_restrictScalars_eq_sum_of_subset {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [iR : Module R X] [iT : IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by
  revert iR iT hT
  induction h with
  | of_subsingleton => intros; simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    intro iR iT hT
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have key : ∀ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl M) = Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl N) + Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl (S ⧸ m)) := fun n => by
      rw [length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ
        N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        length_localizedModule_congr _ e]
    have hmT : (⟨m, hm⟩ : MaximalSpectrum S) ∈ T := by
      by_contra hc
      have h0 := hT _ hc
      rw [key, length_localizedModule_quotient_self m] at h0
      simp at h0
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
      N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      ih (fun n hn => (add_eq_zero.mp ((key n).symm.trans (hT n hn))).1),
      (e.restrictScalars R).length_eq]
    simp_rw [key, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem _ hmT]
    · rw [length_localizedModule_quotient_self m, one_mul]
    · intro n _ hn
      rw [length_localizedModule_quotient_of_ne m n.asIdeal
        (fun hc => hn (MaximalSpectrum.ext hc)), zero_mul]

/- English proof (translation)
Establish `hf` using `finite_support_length_localizedModule h`. Rewrite using `[length_restrictScalars_eq_sum_of_subset R h hf.toFinset (fun n hn => by simpa using hn), finsum_eq_sum_of_support_subset]`. Introduce `n hn`. Simplify using `using left_ne_zero_of_mul hn`.
-/
theorem length_restrictScalars_eq_finsum {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ᶠ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by
  have hf := finite_support_length_localizedModule h
  rw [length_restrictScalars_eq_sum_of_subset R h hf.toFinset (fun n hn => by simpa using hn),
    finsum_eq_sum_of_support_subset]
  intro n hn
  simpa using left_ne_zero_of_mul hn

/- English proof (translation)
Rewrite using `[length_restrictScalars_eq_sum_of_subset S h T hT]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `haveI : IsSimpleModule S (S ⧸ n.asIdeal) := isSimpleModule_iff_quot_maximal.mpr ⟨_, n.isMaximal, ⟨LinearEquiv.refl _ _⟩⟩`. Rewrite using `[Module.length_eq_one S (S ⧸ n.asIdeal), mul_one]`.
-/
theorem length_eq_sum_length_localizedModule {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length S X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) := by
  rw [length_restrictScalars_eq_sum_of_subset S h T hT]
  refine Finset.sum_congr rfl fun n _ => ?_
  haveI : IsSimpleModule S (S ⧸ n.asIdeal) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨_, n.isMaximal, ⟨LinearEquiv.refl _ _⟩⟩
  rw [Module.length_eq_one S (S ⧸ n.asIdeal), mul_one]

/- English proof (translation)
Use `letI := Ideal.Quotient.field p`. Rewrite using `[Module.length_eq_of_surjective (S := R) (R := R ⧸ p) Ideal.Quotient.mk_surjective, Module.length_eq_finrank]`.
-/
theorem length_quotient_eq_finrank (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.LiesOver p]
    [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (Module.finrank (R ⧸ p) (S ⧸ n) : ℕ∞) := by
  letI := Ideal.Quotient.field p
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ p) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

/- English proof (translation)
Rewrite using `[length_quotient_eq_finrank R p n, Ideal.inertiaDeg_eq_of_isMaximal p n]`.
-/
theorem length_quotient_eq_inertiaDeg (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.IsMaximal]
    [n.LiesOver p] [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (n.inertiaDeg R : ℕ∞) := by
  rw [length_quotient_eq_finrank R p n, Ideal.inertiaDeg_eq_of_isMaximal p n]

/- English proof (translation)
Rewrite using `[length_restrictScalars_eq_sum_of_subset R h T hT]`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Use `haveI := hover n hn`. Use `haveI := hfin n hn`. Use `haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n.asIdeal) := Module.Finite.of_restrictScalars_finite R _ _`.

Rewrite using `[length_quotient_eq_inertiaDeg R (maximalIdeal R) n.asIdeal]`.
-/
theorem length_restrictScalars_eq_sum_inertiaDeg_of_subset [IsLocalRing R] {X : Type*}
    [AddCommGroup X] [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0)
    (hover : ∀ n ∈ T, n.asIdeal.LiesOver (maximalIdeal R))
    (hfin : ∀ n ∈ T, Module.Finite R (S ⧸ n.asIdeal)) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) := by
  rw [length_restrictScalars_eq_sum_of_subset R h T hT]
  refine Finset.sum_congr rfl fun n hn => ?_
  haveI := hover n hn
  haveI := hfin n hn
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n.asIdeal) :=
    Module.Finite.of_restrictScalars_finite R _ _
  rw [length_quotient_eq_inertiaDeg R (maximalIdeal R) n.asIdeal]

end General

section Semilocal

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n)).symm⟩`.
-/
theorem liesOver_maximalIdeal_of_isIntegral [Algebra.IsIntegral R S] (n : Ideal S)
    [n.IsMaximal] : n.LiesOver (maximalIdeal R) :=
  ⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n)).symm⟩

/- English proof (translation)
Use `haveI := (Algebra.QuasiFinite.finite_primesOver (S := S) (maximalIdeal R)).to_subtype`. Use `Finite.of_injective (fun n : MaximalSpectrum S => (⟨n.asIdeal, n.isMaximal.isPrime, liesOver_maximalIdeal_of_isIntegral R S n.asIdeal⟩ : (maximalIdeal R).primesOver S)) fun a b hab => ?_` and prove the remaining obligations. Conclude with `MaximalSpectrum.ext (congrArg Subtype.val hab)`.
-/
theorem finite_maximalSpectrum_of_finite [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  haveI := (Algebra.QuasiFinite.finite_primesOver (S := S) (maximalIdeal R)).to_subtype
  refine Finite.of_injective (fun n : MaximalSpectrum S =>
    (⟨n.asIdeal, n.isMaximal.isPrime, liesOver_maximalIdeal_of_isIntegral R S n.asIdeal⟩ :
      (maximalIdeal R).primesOver S)) fun a b hab => ?_
  exact MaximalSpectrum.ext (congrArg Subtype.val hab)

/- English proof (translation)
The claim follows from `liesOver_maximalIdeal_of_isIntegral R S n n.inertiaDeg R = Module.finrank (R ⧸ maximalIdeal R) (S ⧸ n) := haveI := liesOver_maximalIdeal_of_isIntegral R S n Ideal.inertiaDeg_eq_of_isMaximal _ _`.
-/
theorem inertiaDeg_eq_finrank_quotient_maximalIdeal [Module.Finite R S] (n : Ideal S)
    [n.IsMaximal] :
    haveI := liesOver_maximalIdeal_of_isIntegral R S n
    n.inertiaDeg R = Module.finrank (R ⧸ maximalIdeal R) (S ⧸ n) :=
  haveI := liesOver_maximalIdeal_of_isIntegral R S n
  Ideal.inertiaDeg_eq_of_isMaximal _ _

/- English proof (translation)
The claim follows from `length_restrictScalars_eq_sum_inertiaDeg_of_subset R h Finset.univ (by simp) (fun n _ => liesOver_maximalIdeal_of_isIntegral R S n.asIdeal) (fun _ _ => inferInstance)`.
-/
theorem length_restrictScalars_eq_sum_inertiaDeg [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) :=
  length_restrictScalars_eq_sum_inertiaDeg_of_subset R h Finset.univ (by simp)
    (fun n _ => liesOver_maximalIdeal_of_isIntegral R S n.asIdeal) (fun _ _ => inferInstance)

/- English proof (translation)
Rewrite using `[length_restrictScalars_eq_sum_inertiaDeg R S h]`. Conclude with `Finset.sum_congr rfl fun n _ => by`. Rewrite using `[length_eq_length_localizedModule n.asIdeal.primeCompl (A n) (f n)]`.
-/
theorem length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)] [∀ n, Algebra S (A n)]
    [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
    (Y : MaximalSpectrum S → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module S (Y n)]
    [∀ n, Module (A n) (Y n)] [∀ n, IsScalarTower S (A n) (Y n)]
    (f : ∀ n, X →ₗ[S] Y n) [∀ n, IsLocalizedModule n.asIdeal.primeCompl (f n)] :
    Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (Y n) * (n.asIdeal.inertiaDeg R : ℕ∞) := by
  rw [length_restrictScalars_eq_sum_inertiaDeg R S h]
  exact Finset.sum_congr rfl fun n _ => by
    rw [length_eq_length_localizedModule n.asIdeal.primeCompl (A n) (f n)]

/- English proof (translation)
Use `haveI := finite_maximalSpectrum_of_finite R S`. Use `letI := Fintype.ofFinite (MaximalSpectrum S)`. Rewrite using `[← Module.length_ne_top_iff, length_restrictScalars_eq_sum_inertiaDeg R S h]`. Use `WithTop.sum_ne_top.mpr fun n _ => WithTop.mul_ne_top ?_ (ENat.coe_ne_top _)` and prove the remaining obligations. Conclude with `ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr h) (length_localizedModule_atPrime_le n.asIdeal h)`.
-/
theorem isFiniteLength_restrictScalars_of_finite [Module.Finite R S] {X : Type*} [AddCommGroup X]
    [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    IsFiniteLength R X := by
  haveI := finite_maximalSpectrum_of_finite R S
  letI := Fintype.ofFinite (MaximalSpectrum S)
  rw [← Module.length_ne_top_iff, length_restrictScalars_eq_sum_inertiaDeg R S h]
  refine WithTop.sum_ne_top.mpr fun n _ => WithTop.mul_ne_top ?_ (ENat.coe_ne_top _)
  exact ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr h)
    (length_localizedModule_atPrime_le n.asIdeal h)

end Semilocal

/- English proof (translation)
Assemble the required witnesses or components as `⟨length_restrictScalars_of_isLocalHom R S X, ⟨finite_maximalSpectrum_of_finite R S, length_restrictScalars_eq_sum_inertiaDeg R S h⟩⟩`.
-/
theorem length_restrictScalars_local_and_semilocal (R S X : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [AddCommGroup X] [Module R X] [Module S X]
    [IsScalarTower R S X] (h : IsFiniteLength S X) :
    (∀ [IsLocalRing S] [IsLocalHom (algebraMap R S)]
      [Module.Finite (ResidueField R) (ResidueField S)],
      Module.length R X =
        Module.length S X * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞)) ∧
    (∀ [Module.Finite R S], Finite (MaximalSpectrum S) ∧ ∀ [Fintype (MaximalSpectrum S)],
      Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞)) :=
  ⟨length_restrictScalars_of_isLocalHom R S X,
    ⟨finite_maximalSpectrum_of_finite R S, length_restrictScalars_eq_sum_inertiaDeg R S h⟩⟩

end GlobalTheory
