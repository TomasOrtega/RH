import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.LiftInduct

/- English proof (translation)
The claim follows from `LBIso.chartPull (h := (lift (fst A Y') (snd A Y' ≫ e)).left) (chartPullSame N _ _ _ _ fun _ => by rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]) (chartPullSame M _ _ _ _ fun _ => by rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.a …`.
-/
theorem same_comp {S : Scheme.{0}} (A : Over S) {T U Y Y' : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (e : Y' ⟶ Y) {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) : Same A N M (e ≫ y) (e ≫ u) :=
  LBIso.chartPull (h := (lift (fst A Y') (snd A Y' ≫ e)).left)
    (chartPullSame N _ _ _ _ fun _ => by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc])
    (chartPullSame M _ _ _ _ fun _ => by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]) h

variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)

def LiftsVia {B C : Type} [CommRing B] [CommRing C] (φ : B →+* C) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

/- English proof (translation)
Introduce `T N _ y u₀ h`. Establish `hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_id, Spec.map_id]`. Set `e : Over.mk (y ≫ T.hom) ⟶ Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom)` to `Over.homMk (Spec.map (CommRingCat.ofHom ψ)) (by simp [reassoc_of% hs])`. Use `⟨e ≫ u₀, ?_⟩` and prove the remaining obligations.

Establish `h'` using `same_comp A e h`. Use `h' using 1` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[e, reassoc_of% hs]`.
-/
theorem liftsVia_of_leftInverse {B C : Type} [CommRing B] [CommRing C] (φ : B →+* C) (ψ : C →+* B)
    (hψ : ψ.comp φ = RingHom.id B) : LiftsVia A M φ := by
  intro T N _ y u₀ h
  have hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_id, Spec.map_id]
  let e : Over.mk (y ≫ T.hom) ⟶ Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ)) (by simp [reassoc_of% hs])
  refine ⟨e ≫ u₀, ?_⟩
  have h' := same_comp A e h
  convert h' using 1
  ext
  simp [e, reassoc_of% hs]

/- English proof (translation)
Introduce `T N hN y u₀ h`. Establish `k : Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ)`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`. Set `e : Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ y ≫ T.hom)` to `Over.homMk (𝟙 _) (by simp [k])`. Take `⟨u₁, h₁⟩` from `hψ T N hN (Spec.map (CommRingCat.ofHom φ) ≫ y) (e ≫ u₀) (by`.

Establish `h'` using `same_comp A e h`. Use `h' using 1` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[e, k])`. Set `e' : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ Over.mk ((Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom)` to `Over.homMk (𝟙 _) (by simp)`.

Conclude with `hφ T N hN y (e' ≫ u₁) (by`. Establish `h'` using `same_comp A e' h₁`. Use `h' using 1` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[e'])`.
-/
theorem liftsVia_comp {B C D : Type} [CommRing B] [CommRing C] [CommRing D] (φ : B →+* C) (ψ : C →+* D)
    (hφ : LiftsVia A M φ) (hψ : LiftsVia A M ψ) : LiftsVia A M (ψ.comp φ) := by
  intro T N hN y u₀ h
  have k : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let e : Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ y ≫ T.hom) := Over.homMk (𝟙 _) (by simp [k])
  obtain ⟨u₁, h₁⟩ := hψ T N hN (Spec.map (CommRingCat.ofHom φ) ≫ y) (e ≫ u₀) (by
    have h' := same_comp A e h
    convert h' using 1
    ext
    simp [e, k])
  let e' : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶
      Over.mk ((Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) := Over.homMk (𝟙 _) (by simp)
  exact hφ T N hN y (e' ≫ u₁) (by
    have h' := same_comp A e' h₁
    convert h' using 1
    ext
    simp [e'])

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `B _ _ _ C _ φ l hl hs hk _ _`. Establish `hl0 : l = []` using `List.eq_nil_of_length_eq_zero hl`.

Substitute `hl0` using the available equality. Establish `hinj : Function.Injective φ`. Rewrite using `[RingHom.injective_iff_ker_eq_bot, hk]`. Simplify using the standard rewrite rules. Set `e` to `RingEquiv.ofBijective φ ⟨hinj, hs⟩`.

Use `liftsVia_of_leftInverse A M φ e.symm.toRingHom ?_` and prove the remaining obligations. Use extensionality with `x`. Conclude with `e.symm_apply_apply x`. Consider the case `succ n ih`. Introduce `B _ _ _ C _ φ l hl hs hk hkm hmk`.

Choose the witnesses or unpack the hypotheses as in `⟨t, l', rfl⟩ : ∃ t l', l = t :: l' := by`. Consider the cases of `l with`. Consider the case `nil => simp at hl`. Consider the case `cons t l' => exact ⟨t, l', rfl⟩`. Establish `ht : t ∈ RingHom.ker φ` using `hk ▸ Ideal.subset_span (by simp)`.

Establish `hJ : Ideal.span {t} ≤ RingHom.ker φ` using `(Ideal.span_singleton_le_iff_mem _).2 ht`. Set `ψ : B ⧸ Ideal.span {t} →+* C` to `Ideal.Quotient.lift _ φ (fun a ha => hJ ha)`. Establish `hcomp : ψ.comp (Ideal.Quotient.mk _) = φ`. Use extensionality with `x`. Both sides reduce to the same expression.

Establish `hprin : LiftsVia A M (Ideal.Quotient.mk (Ideal.span {t}))` using `hyp B t (hkm ht) (le_bot_iff.1 ((Ideal.mul_mono_right hJ).trans hmk.le))`. Establish `hne : Ideal.span {t} ≠ ⊤` using `fun h => (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hJ.trans hkm))`. Use `haveI : Nontrivial (B ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 hne`. Use `haveI : IsLocalRing (B ⧸ Ideal.span {t}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective`. Establish `hψs : Function.Surjective ψ` using `Ideal.Quotient.lift_surjective_of_surjective _ _ hs`.

Establish `hC : Nontrivial C`. Break down `subsingleton_or_nontrivial C with hC | hC` into its components or cases. Conclude with `absurd (hkm (RingHom.mem_ker.2 (Subsingleton.elim _ _))) ((Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal B).ne_top)`. Conclude with `hC`. Establish `h0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self t)`.

Establish `hker : RingHom.ker ψ = (RingHom.ker φ).map (Ideal.Quotient.mk (Ideal.span {t}))`. Use `le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (RingHom.mem_ker.1 hx))`. Conclude with `RingHom.mem_ker.2 (RingHom.mem_ker.1 hb)`.

Establish `hkerψ : RingHom.ker ψ = Ideal.span {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))}`. Rewrite using `[hker, hk, Ideal.map_span]`. Establish `hset : (Ideal.Quotient.mk (Ideal.span {t})) '' {x | x ∈ t :: l'} = insert 0 {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))}`. Use extensionality with `x`. Simplify using `only [List.mem_cons, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl | ha, rfl⟩`. Conclude with `Or.inl h0`. Conclude with `Or.inr ⟨a, ha, rfl⟩`. Introduce and unpack `(rfl | ⟨a, ha, rfl⟩)`.

Conclude with `⟨t, Or.inl rfl, h0⟩`. Conclude with `⟨a, Or.inr ha, rfl⟩`. Rewrite using `[hset, Ideal.span_insert_zero]`. Establish `hkm' : RingHom.ker ψ ≤ IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t})` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)`. Establish `hmk' : IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) * RingHom.ker ψ = ⊥`.

Rewrite using `[eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `ha : a ∈ IsLocalRing.maximalIdeal B`.

Rewrite `hx`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun h => hx (h.map _)`. Establish `hb : b ∈ RingHom.ker φ` using `RingHom.mem_ker.2 (RingHom.mem_ker.1 hy)`. Establish `hab : a * b = 0`. Use `Ideal.mul_mem_mul ha hb` as an intermediate fact.

Rewrite `this` using `[hmk]`. Simplify using `using this`. Rewrite using `[Ideal.mem_bot, ← map_mul, hab, map_zero]`. Establish `hlen : (l'.map (Ideal.Quotient.mk (Ideal.span {t}))).length = n`. Simplify using `using hl`.

Establish `hψ` using `ih (B ⧸ Ideal.span {t}) C ψ _ hlen hψs hkerψ hkm' hmk'`. Rewrite using `[← hcomp]`. Conclude with `liftsVia_comp A M _ _ hprin hψ`.
-/
theorem liftsVia_of_list
    (hyp : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (t : B),
      t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ →
      LiftsAlong A M B (Ideal.span {t})) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (C : Type) [CommRing C] (φ : B →+* C)
      (l : List B), l.length = n → Function.Surjective φ → RingHom.ker φ = Ideal.span {x | x ∈ l} →
      RingHom.ker φ ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * RingHom.ker φ = ⊥ →
      LiftsVia A M φ := by
  intro n
  induction n with
  | zero =>
    intro B _ _ _ C _ φ l hl hs hk _ _
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero hl
    subst hl0
    have hinj : Function.Injective φ := by
      rw [RingHom.injective_iff_ker_eq_bot, hk]
      simp
    let e := RingEquiv.ofBijective φ ⟨hinj, hs⟩
    refine liftsVia_of_leftInverse A M φ e.symm.toRingHom ?_
    ext x
    exact e.symm_apply_apply x
  | succ n ih =>
    intro B _ _ _ C _ φ l hl hs hk hkm hmk
    obtain ⟨t, l', rfl⟩ : ∃ t l', l = t :: l' := by
      cases l with
      | nil => simp at hl
      | cons t l' => exact ⟨t, l', rfl⟩
    have ht : t ∈ RingHom.ker φ := hk ▸ Ideal.subset_span (by simp)
    have hJ : Ideal.span {t} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).2 ht
    let ψ : B ⧸ Ideal.span {t} →+* C := Ideal.Quotient.lift _ φ (fun a ha => hJ ha)
    have hcomp : ψ.comp (Ideal.Quotient.mk _) = φ := by
      ext x
      rfl
    have hprin : LiftsVia A M (Ideal.Quotient.mk (Ideal.span {t})) :=
      hyp B t (hkm ht) (le_bot_iff.1 ((Ideal.mul_mono_right hJ).trans hmk.le))
    have hne : Ideal.span {t} ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hJ.trans hkm))
    haveI : Nontrivial (B ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (B ⧸ Ideal.span {t}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hψs : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hs
    have hC : Nontrivial C := by
      rcases subsingleton_or_nontrivial C with hC | hC
      · exact absurd (hkm (RingHom.mem_ker.2 (Subsingleton.elim _ _)))
          ((Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal B).ne_top)
      · exact hC
    have h0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self t)
    have hker : RingHom.ker ψ = (RingHom.ker φ).map (Ideal.Quotient.mk (Ideal.span {t})) := by
      refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
      · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (RingHom.mem_ker.1 hx))
      · exact RingHom.mem_ker.2 (RingHom.mem_ker.1 hb)
    have hkerψ : RingHom.ker ψ =
        Ideal.span {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))} := by
      rw [hker, hk, Ideal.map_span]
      have hset : (Ideal.Quotient.mk (Ideal.span {t})) '' {x | x ∈ t :: l'} =
          insert 0 {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))} := by
        ext x
        simp only [List.mem_cons, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_map]
        constructor
        · rintro ⟨a, rfl | ha, rfl⟩
          · exact Or.inl h0
          · exact Or.inr ⟨a, ha, rfl⟩
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨t, Or.inl rfl, h0⟩
          · exact ⟨a, Or.inr ha, rfl⟩
      rw [hset, Ideal.span_insert_zero]
    have hkm' : RingHom.ker ψ ≤ IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
    have hmk' : IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) * RingHom.ker ψ = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have ha : a ∈ IsLocalRing.maximalIdeal B := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
        exact fun h => hx (h.map _)
      have hb : b ∈ RingHom.ker φ := RingHom.mem_ker.2 (RingHom.mem_ker.1 hy)
      have hab : a * b = 0 := by
        have := Ideal.mul_mem_mul ha hb
        rw [hmk] at this
        simpa using this
      rw [Ideal.mem_bot, ← map_mul, hab, map_zero]
    have hlen : (l'.map (Ideal.Quotient.mk (Ideal.span {t}))).length = n := by
      simpa using hl
    have hψ := ih (B ⧸ Ideal.span {t}) C ψ _ hlen hψs hkerψ hkm' hmk'
    rw [← hcomp]
    exact liftsVia_comp A M _ _ hprin hψ

end GlobalTheory.DualCon.LiftInduct

namespace GlobalTheory.DualCon

/- English proof (translation)
Introduce `R _ A _ U M hyp B _ _ _ I hI hmI`. Take `⟨s, hs⟩ : I.FG` from `IsNoetherian.noetherian I`. Use `LiftInduct.liftsVia_of_list A M hyp _ B (B ⧸ I) (Ideal.Quotient.mk I) s.toList rfl Ideal.Quotient.mk_surjective ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.mk_ker, ← hs]`. Use `congr 1`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[Ideal.mk_ker]` and apply the resulting hypothesis. Rewrite using `[Ideal.mk_ker]` and apply the resulting hypothesis.
-/
theorem liftsAlong_of_principal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t})) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → LiftsAlong A M B I := by
  intro R _ A _ U M hyp B _ _ _ I hI hmI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  refine LiftInduct.liftsVia_of_list A M hyp _ B (B ⧸ I) (Ideal.Quotient.mk I) s.toList rfl
    Ideal.Quotient.mk_surjective ?_ ?_ ?_
  · rw [Ideal.mk_ker, ← hs]
    congr 1
    ext x
    simp
  · rwa [Ideal.mk_ker]
  · rwa [Ideal.mk_ker]

end GlobalTheory.DualCon
