import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.CartierDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

attribute [local instance 2000] Rep.hV2

section FixedVector

variable {W : Type u} [Group W]

/- English proof (translation)
Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Set `R : Subgroup (N →ₗ[ULift.{u} ℤ] N)ˣ` to `N.ρ.asGroupHom.range`. Establish `hR : IsPGroup 2 R`. Introduce and unpack `⟨x, w, rfl⟩`. Take `⟨k, hk⟩` from `hN w`.

Use `⟨k, Subtype.ext (Units.ext ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((N.ρ.asGroupHom w ^ 2 ^ k : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) = 1`. Rewrite using `[← map_pow, Representation.asGroupHom_apply, hk]`. Establish `hcard` using `hR.card_modEq_card_fixedPoints N`. Take `⟨m₀, hm₀⟩` from `exists_ne (0 : N)`.

Establish `hord : addOrderOf m₀ = 2` using `addOrderOf_eq_prime (h2 m₀) hm₀`. Establish `h2N : 2 ∣ Nat.card N` using `hord ▸ addOrderOf_dvd_natCard m₀`. Establish `h2F : 2 ∣ Nat.card (MulAction.fixedPoints R N)` using `(hcard.dvd_iff (dvd_refl 2)).1 h2N`. Establish `h0 : (0 : N) ∈ MulAction.fixedPoints R N` using `fun r => by`. Express the relevant statement in the definitionally equal form `((r : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) 0 = 0`.

Conclude with `map_zero _`. Establish `hF : Finite (MulAction.fixedPoints R N)` using `Subtype.finite`. Establish `hlt : 1 < Nat.card (MulAction.fixedPoints R N)`. Establish `hpos : 0 < Nat.card (MulAction.fixedPoints R N)` using `Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, hF⟩`. Take `⟨c, hc⟩` from `h2F`.

Use linear arithmetic over natural numbers and integers. Take `⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩` from `Finite.one_lt_card_iff_nontrivial.1 hlt |>.exists_pair_ne`. Establish `hne : a ≠ 0 ∨ b ≠ 0`. Assume the negation of the conclusion as `h`. Simplify using `only [ne_eq, not_or, not_not] at h`.

Conclude with `hab (Subtype.ext (h.1.trans h.2.symm))`. Establish `key : ∀ c ∈ MulAction.fixedPoints R N, ∀ w : W, N.ρ w c = c` using `fun c hc w => hc ⟨N.ρ.asGroupHom w, w, rfl⟩`. Break down `hne with h | h` into its components or cases. Conclude with `⟨a, h, key a ha⟩`. Conclude with `⟨b, h, key b hb⟩`.
-/
theorem exists_ne_zero_forall_ρ_eq (N : Rep.{u} (ULift.{u} ℤ) W) [Finite N] [Nontrivial N]
    (h2 : ∀ m : N, 2 • m = 0) (hN : ∀ w : W, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) :
    ∃ m : N, m ≠ 0 ∧ ∀ w : W, N.ρ w m = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup (N →ₗ[ULift.{u} ℤ] N)ˣ := N.ρ.asGroupHom.range
  have hR : IsPGroup 2 R := by
    rintro ⟨x, w, rfl⟩
    obtain ⟨k, hk⟩ := hN w
    refine ⟨k, Subtype.ext (Units.ext ?_)⟩
    change ((N.ρ.asGroupHom w ^ 2 ^ k : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) = 1
    rw [← map_pow, Representation.asGroupHom_apply, hk]
  have hcard := hR.card_modEq_card_fixedPoints N
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : N)
  have hord : addOrderOf m₀ = 2 :=
    addOrderOf_eq_prime (h2 m₀) hm₀
  have h2N : 2 ∣ Nat.card N := hord ▸ addOrderOf_dvd_natCard m₀
  have h2F : 2 ∣ Nat.card (MulAction.fixedPoints R N) := (hcard.dvd_iff (dvd_refl 2)).1 h2N
  have h0 : (0 : N) ∈ MulAction.fixedPoints R N := fun r => by
    change ((r : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) 0 = 0
    exact map_zero _
  have hF : Finite (MulAction.fixedPoints R N) := Subtype.finite
  have hlt : 1 < Nat.card (MulAction.fixedPoints R N) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints R N) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, hF⟩
    obtain ⟨c, hc⟩ := h2F
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Finite.one_lt_card_iff_nontrivial.1 hlt |>.exists_pair_ne
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    exact hab (Subtype.ext (h.1.trans h.2.symm))
  have key : ∀ c ∈ MulAction.fixedPoints R N, ∀ w : W, N.ρ w c = c := fun c hc w =>
    hc ⟨N.ρ.asGroupHom w, w, rfl⟩
  rcases hne with h | h
  · exact ⟨a, h, key a ha⟩
  · exact ⟨b, h, key b hb⟩

end FixedVector

section ZModTwo

variable {W : Type u} [Group W]

def zmodTwoAddHom {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) : ZMod 2 →+ N :=
  ZMod.lift 2 ⟨zmultiplesHom N m, by
    change ((2 : ℕ) : ℤ) • m = 0
    rw [natCast_zsmul]
    exact hm⟩

/- English proof (translation)
The claim follows from `ZMod.lift_coe _ _ k`.
-/
theorem zmodTwoAddHom_intCast {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) (k : ℤ) :
    zmodTwoAddHom m hm (k : ZMod 2) = k • m :=
  ZMod.lift_coe _ _ k

/- English proof (translation)
Establish `h` using `zmodTwoAddHom_intCast m hm 1`. Rewrite `h` using `[Int.cast_one, one_zsmul]`. Then use the resulting hypothesis.
-/
theorem zmodTwoAddHom_one {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) :
    zmodTwoAddHom m hm 1 = m := by
  have h := zmodTwoAddHom_intCast m hm 1
  rwa [Int.cast_one, one_zsmul] at h

/- English proof (translation)
The claim follows from `(injective_iff_map_eq_zero _).2 fun a ha => by fin_cases a · rfl · exact absurd ((zmodTwoAddHom_one m hm).symm.trans ha) hm0`.
-/
theorem zmodTwoAddHom_injective {N : Type*} [AddCommGroup N] {m : N} (hm : 2 • m = 0)
    (hm0 : m ≠ 0) : Function.Injective (zmodTwoAddHom m hm) :=
  (injective_iff_map_eq_zero _).2 fun a ha => by
    fin_cases a
    · rfl
    · exact absurd ((zmodTwoAddHom_one m hm).symm.trans ha) hm0

def zmodTwoHom (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0) (hfix : ∀ w : W, N.ρ w m = m) :
    zmodRep.{u} W 2 ⟶ N :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} W 2) N).symm
    ((zmodTwoAddHom m hm).comp (AddEquiv.ulift : ULift.{u} (ZMod 2) ≃+ ZMod 2).toAddMonoidHom),
    fun w => by
      refine LinearMap.ext fun a => ?_
      obtain ⟨a⟩ := a
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
      change zmodTwoAddHom m hm (k : ZMod 2) = N.ρ w (zmodTwoAddHom m hm (k : ZMod 2))
      rw [zmodTwoAddHom_intCast, map_zsmul, hfix]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zmodTwoHom_hom_apply (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0)
    (hfix : ∀ w : W, N.ρ w m = m) (a : zmodRep.{u} W 2) :
    (zmodTwoHom N m hm hfix).hom a = zmodTwoAddHom m hm (ULift.down a) :=
  rfl

end ZModTwo

instance isDiscreteRep_zmodRep {W : Type u} [Group W] [TopologicalSpace W] (n : ℕ) :
    IsDiscreteRep (zmodRep.{u} W n) :=
  isDiscreteRep_of_isTrivial (zmodRep.{u} W n)

section Tate

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

instance isDiscreteRep_coind_zmodRep_openSubgroup (W : OpenSubgroup G) (n : ℕ) :
    IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n)) :=
  isDiscreteRep_coind W _

omit [CompactSpace G] in

/- English proof (translation)
The claim follows from `eq_zero_tateCompactCohomologyRes_of_retract φ ψ (0 : A ⟶ B) 0 (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => Subsingleton.elim _ _))) n hB x`.
-/
theorem eq_zero_tateCompactCohomologyRes_of_subsingleton {k : Type u} [CommRing k]
    {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [Subsingleton A] (n : ℕ)
    (hB : ∀ x : tateCompactCohomologyRes φ ψ B n, x = 0) (x : tateCompactCohomologyRes φ ψ A n) :
    x = 0 :=
  eq_zero_tateCompactCohomologyRes_of_retract φ ψ (0 : A ⟶ B) 0
    (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => Subsingleton.elim _ _)))
    n hB x

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `N _ _ hd`. Use `Nat.card_pos (α := N)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Consider the case `succ d ih`. Introduce `N _ _ hd h2 hN x`. Distinguish the cases in `hsub : Subsingleton N`. Establish `: Subsingleton (Rep.coind (W : Subgroup G).subtype N)` using `⟨fun a b => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩`.

Conclude with `eq_zero_tateCompactCohomologyRes_of_subsingleton φ ψ n hW x`. Rewrite `hsub` using `[not_subsingleton_iff_nontrivial]`. Take `⟨m, hm0, hfix⟩` from `exists_ne_zero_forall_ρ_eq N h2 hN`. Set `f` to `zmodTwoHom N m (h2 m) hfix`. Set `T : Submodule (ULift.{u} ℤ) N` to `LinearMap.range f.hom.toLinearMap`.

Establish `hT : ∀ w, T ≤ T.comap (N.ρ w)`. Introduce and unpack `w _ ⟨a, rfl⟩`. Use `⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f.hom a = N.ρ w (f.hom a)`. Rewrite using `[zmodTwoHom_hom_apply]`.

Take `⟨b⟩` from `a`. Take `⟨k, rfl⟩` from `ZMod.intCast_surjective b`. Express the relevant statement in the definitionally equal form `zmodTwoAddHom m (h2 m) (k : ZMod 2) = N.ρ w (zmodTwoAddHom m (h2 m) (k : ZMod 2))`. Rewrite using `[zmodTwoAddHom_intCast, map_zsmul, hfix]`. Establish `hfinj : Function.Injective f.hom` using `fun a b hab => ULift.ext _ _ (zmodTwoAddHom_injective (h2 m) hm0 hab)`.

Set `S : ShortComplex (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G))` to `ShortComplex.mk f (Rep.mkQ N T hT) (by`. Apply `Rep.hom_ext` to reduce the goal to its premises. Apply `DFunLike.ext` to reduce the goal to its premises. Introduce `a`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)`.

Establish `hS : S.ShortExact`. Use `{ exact := ?_, mono_f := (Rep.mono_iff_injective _).2 hfinj, epi_g := ?_ }` and prove the remaining obligations. Rewrite using `[← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) (ModuleCat.{u} (ULift.{u} ℤ))), ShortComplex.moduleCat_exact_iff]`. Introduce `a ha`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (p := T) a = 0 at ha`.

Take `⟨b, hb⟩` from `(Submodule.Quotient.mk_eq_zero _).1 ha`. Conclude with `⟨b, hb⟩`. Use `(Rep.epi_iff_surjective _).2 fun y => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective T y`. Conclude with `⟨a, rfl⟩`.

Establish `hCS` using `shortExact_coindShortComplexOf (W : Subgroup G) hS`. Establish `: IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₁` using `isDiscreteRep_coind W _`. Establish `: IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₂` using `isDiscreteRep_coind W _`. Establish `: IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₃` using `isDiscreteRep_coind W _`. Establish `: Finite (N ⧸ T)` using `Finite.of_surjective _ (Submodule.mkQ_surjective T)`.

Establish `hcardT : 2 ≤ Nat.card T`. Establish `h0 : (0 : N) ∈ T` using `T.zero_mem`. Establish `hm : m ∈ T` using `⟨ULift.up 1, by`. Rewrite using `[LinearMap.coe_mk]`. Conclude with `(zmodTwoHom_hom_apply N m (h2 m) hfix _).trans (zmodTwoAddHom_one m (h2 m))⟩`.

Establish `: Finite T` using `Subtype.finite`. Conclude with `Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨0, h0⟩, ⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h).symm⟩⟩`. Establish `hcardQ : Nat.card (N ⧸ T) ≤ d`. Establish `hc` using `Submodule.card_eq_card_quotient_mul_card T`. Establish `hpos : 0 < Nat.card (N ⧸ T)` using `Nat.card_pos`.

Use the polynomial consequences of the given equalities and inequalities. Use `eq_zero_tateCompactCohomologyRes_of_shortExact φ ψ hCS n hW ?_ x` and prove the remaining obligations. Use `ih (N.quotient T hT) hcardQ ?_ ?_` and prove the remaining obligations. Introduce `y`. Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective T y`.

Conclude with `(map_nsmul T.mkQ 2 a).symm.trans ((congrArg T.mkQ (h2 a)).trans (map_zero _))`. Introduce `w`. Take `⟨k, hk⟩` from `hN w`. Use `⟨k, DFunLike.ext _ _ fun y => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective T y`.

Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (p := T) (N.ρ (w ^ 2 ^ k) a) = Submodule.Quotient.mk a`. Rewrite using `[hk]`. Both sides reduce to the same expression.
-/
theorem eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul (n : ℕ) (W : OpenSubgroup G)
    (hW : ∀ x : tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n, x = 0) :
    ∀ (d : ℕ) (N : Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) [IsDiscreteRep N] [Finite N],
      Nat.card N ≤ d → (∀ m : N, 2 • m = 0) → (∀ w, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) →
      ∀ x : tateCompactCohomologyRes φ ψ (Rep.coind (W : Subgroup G).subtype N) n, x = 0 := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hd
    have := Nat.card_pos (α := N)
    omega
  | succ d ih =>
    intro N _ _ hd h2 hN x
    by_cases hsub : Subsingleton N
    · have : Subsingleton (Rep.coind (W : Subgroup G).subtype N) :=
        ⟨fun a b => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
      exact eq_zero_tateCompactCohomologyRes_of_subsingleton φ ψ n hW x
    · rw [not_subsingleton_iff_nontrivial] at hsub
      obtain ⟨m, hm0, hfix⟩ := exists_ne_zero_forall_ρ_eq N h2 hN
      let f := zmodTwoHom N m (h2 m) hfix
      let T : Submodule (ULift.{u} ℤ) N := LinearMap.range f.hom.toLinearMap
      have hT : ∀ w, T ≤ T.comap (N.ρ w) := by
        rintro w _ ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        change f.hom a = N.ρ w (f.hom a)
        rw [zmodTwoHom_hom_apply]
        obtain ⟨b⟩ := a
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective b
        change zmodTwoAddHom m (h2 m) (k : ZMod 2) = N.ρ w (zmodTwoAddHom m (h2 m) (k : ZMod 2))
        rw [zmodTwoAddHom_intCast, map_zsmul, hfix]
      have hfinj : Function.Injective f.hom := fun a b hab =>
        ULift.ext _ _ (zmodTwoAddHom_injective (h2 m) hm0 hab)
      let S : ShortComplex (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) :=
        ShortComplex.mk f (Rep.mkQ N T hT) (by
          apply Rep.hom_ext
          apply DFunLike.ext
          intro a
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)
      have hS : S.ShortExact := by
        refine { exact := ?_, mono_f := (Rep.mono_iff_injective _).2 hfinj, epi_g := ?_ }
        · rw [← ShortComplex.exact_map_iff_of_faithful _
            (forget₂ (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) (ModuleCat.{u} (ULift.{u} ℤ))),
            ShortComplex.moduleCat_exact_iff]
          intro a ha
          change Submodule.Quotient.mk (p := T) a = 0 at ha
          obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 ha
          exact ⟨b, hb⟩
        · refine (Rep.epi_iff_surjective _).2 fun y => ?_
          obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
          exact ⟨a, rfl⟩
      have hCS := shortExact_coindShortComplexOf (W : Subgroup G) hS
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₁ := isDiscreteRep_coind W _
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₂ := isDiscreteRep_coind W _
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₃ := isDiscreteRep_coind W _
      have : Finite (N ⧸ T) := Finite.of_surjective _ (Submodule.mkQ_surjective T)
      have hcardT : 2 ≤ Nat.card T := by
        have h0 : (0 : N) ∈ T := T.zero_mem
        have hm : m ∈ T := ⟨ULift.up 1, by
          rw [LinearMap.coe_mk]
          exact (zmodTwoHom_hom_apply N m (h2 m) hfix _).trans (zmodTwoAddHom_one m (h2 m))⟩
        have : Finite T := Subtype.finite
        exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨0, h0⟩, ⟨m, hm⟩,
          fun h => hm0 (congrArg Subtype.val h).symm⟩⟩
      have hcardQ : Nat.card (N ⧸ T) ≤ d := by
        have hc := Submodule.card_eq_card_quotient_mul_card T
        have hpos : 0 < Nat.card (N ⧸ T) := Nat.card_pos
        nlinarith
      refine eq_zero_tateCompactCohomologyRes_of_shortExact φ ψ hCS n hW ?_ x
      refine ih (N.quotient T hT) hcardQ ?_ ?_
      · intro y
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
        exact (map_nsmul T.mkQ 2 a).symm.trans ((congrArg T.mkQ (h2 a)).trans (map_zero _))
      · intro w
        obtain ⟨k, hk⟩ := hN w
        refine ⟨k, DFunLike.ext _ _ fun y => ?_⟩
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
        change Submodule.Quotient.mk (p := T) (N.ρ (w ^ 2 ^ k) a) = Submodule.Quotient.mk a
        rw [hk]
        rfl

/- English proof (translation)
Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Set `U : Subgroup G` to `⨅ m : M, stabilizer M.ρ m`. Establish `hU : IsOpen (U : Set G)`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_iInf]`.

Conclude with `Filter.iInter_mem.2 fun m => (isOpen_stabilizer M m).mem_nhds (one_mem _)`. Set `K₀ : Subgroup G` to `M.ρ.asGroupHom.ker`. Establish `hUK : U ≤ K₀` using `fun g hg => by`. Use `(MonoidHom.mem_ker).2 (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[Representation.asGroupHom_apply]`.

Conclude with `LinearMap.ext fun m => (Subgroup.mem_iInf.1 hg m : M.ρ g m = m)`. Set `K : OpenSubgroup G` to `⟨K₀, Subgroup.isOpen_mono hUK hU⟩`. Establish `: K₀.FiniteIndex` using `finiteIndex_openSubgroup K`. Establish `: Finite (G ⧸ K₀)` using `Subgroup.finite_quotient_of_finiteIndex`. Set `P : Sylow 2 (G ⧸ K₀)` to `Classical.arbitrary _`.

Set `W : OpenSubgroup G` to `⟨(P : Subgroup (G ⧸ K₀)).comap (QuotientGroup.mk' K₀), Subgroup.isOpen_mono (fun g hg => by`. Express the relevant statement in the definitionally equal form `QuotientGroup.mk' K₀ g ∈ (P : Subgroup (G ⧸ K₀))`. Rewrite using `[QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]`. Conclude with `one_mem _) (Subgroup.isOpen_mono hUK hU)⟩`. Establish `hidx : (W : Subgroup G).index = (P : Subgroup (G ⧸ K₀)).index` using `Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K₀)`.

Establish `: (P : Subgroup (G ⧸ K₀)).FiniteIndex` using `Subgroup.finiteIndex_of_finite`. Establish `hodd : ¬ 2 ∣ (W : Subgroup G).index` using `hidx ▸ Sylow.not_dvd_index P`. Establish `: (W : Subgroup G).FiniteIndex` using `finiteIndex_openSubgroup W`. Establish `: IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (Rep.res (W : Subgroup G).subtype M))` using `isDiscreteRep_coind W _`. Establish `hunit : coindUnit (W : Subgroup G) M ≫ coindTrace (W : Subgroup G) M = 𝟙 M`.

Rewrite using `[coindUnit_comp_coindTrace]`. Take `⟨c, hc⟩` from `Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `(W : Subgroup G).index • a = a`. Rewrite using `[hc, add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul]`.

Use `eq_zero_tateCompactCohomologyRes_of_retract φ ψ _ _ hunit n ?_ x` and prove the remaining obligations. Use `eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul φ ψ n W (hW W) _ (Rep.res (W : Subgroup G).subtype M) le_rfl (fun m => h2 m) ?_` and prove the remaining obligations. Introduce `w`. Take `⟨k, hk⟩` from `P.isPGroup' ⟨QuotientGroup.mk' K₀ (w : G), w.2⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `hk' : (w : G) ^ 2 ^ k ∈ K₀`. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]`. Conclude with `congrArg Subtype.val hk`. Establish `h1` using `congrArg Units.val ((MonoidHom.mem_ker).1 hk')`. Rewrite `h1` using `[Representation.asGroupHom_apply]`.

Conclude with `h1`.
-/
theorem eq_zero_tateCompactCohomologyRes_of_two_nsmul (n : ℕ)
    (hW : ∀ W : OpenSubgroup G, ∀ x : tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n, x = 0)
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (h2 : ∀ m : M, 2 • m = 0)
    (x : tateCompactCohomologyRes φ ψ M n) : x = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup G := ⨅ m : M, stabilizer M.ρ m
  have hU : IsOpen (U : Set G) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    rw [Subgroup.coe_iInf]
    exact Filter.iInter_mem.2 fun m => (isOpen_stabilizer M m).mem_nhds (one_mem _)
  let K₀ : Subgroup G := M.ρ.asGroupHom.ker
  have hUK : U ≤ K₀ := fun g hg => by
    refine (MonoidHom.mem_ker).2 (Units.ext ?_)
    rw [Representation.asGroupHom_apply]
    exact LinearMap.ext fun m => (Subgroup.mem_iInf.1 hg m : M.ρ g m = m)
  let K : OpenSubgroup G := ⟨K₀, Subgroup.isOpen_mono hUK hU⟩
  have : K₀.FiniteIndex := finiteIndex_openSubgroup K
  have : Finite (G ⧸ K₀) := Subgroup.finite_quotient_of_finiteIndex
  let P : Sylow 2 (G ⧸ K₀) := Classical.arbitrary _
  let W : OpenSubgroup G := ⟨(P : Subgroup (G ⧸ K₀)).comap (QuotientGroup.mk' K₀),
    Subgroup.isOpen_mono (fun g hg => by
      change QuotientGroup.mk' K₀ g ∈ (P : Subgroup (G ⧸ K₀))
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
      exact one_mem _) (Subgroup.isOpen_mono hUK hU)⟩
  have hidx : (W : Subgroup G).index = (P : Subgroup (G ⧸ K₀)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K₀)
  have : (P : Subgroup (G ⧸ K₀)).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hodd : ¬ 2 ∣ (W : Subgroup G).index := hidx ▸ Sylow.not_dvd_index P
  have : (W : Subgroup G).FiniteIndex := finiteIndex_openSubgroup W
  have : IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (Rep.res (W : Subgroup G).subtype M)) :=
    isDiscreteRep_coind W _
  have hunit : coindUnit (W : Subgroup G) M ≫ coindTrace (W : Subgroup G) M = 𝟙 M := by
    rw [coindUnit_comp_coindTrace]
    obtain ⟨c, hc⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    ext a
    change (W : Subgroup G).index • a = a
    rw [hc, add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul]
  refine eq_zero_tateCompactCohomologyRes_of_retract φ ψ _ _ hunit n ?_ x
  refine eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul φ ψ n W (hW W) _
    (Rep.res (W : Subgroup G).subtype M) le_rfl (fun m => h2 m) ?_
  intro w
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' K₀ (w : G), w.2⟩
  refine ⟨k, ?_⟩
  have hk' : (w : G) ^ 2 ^ k ∈ K₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact congrArg Subtype.val hk
  have h1 := congrArg Units.val ((MonoidHom.mem_ker).1 hk')
  rw [Representation.asGroupHom_apply] at h1
  exact h1

end Tate

end GroundTheory.ProfCoh
