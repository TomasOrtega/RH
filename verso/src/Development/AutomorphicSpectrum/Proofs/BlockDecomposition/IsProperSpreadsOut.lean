import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteAffineCover

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter

namespace GlobalTheory.CompanionTheory.Ultra

section Core

variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))

def baseHom (W : X.affineOpens) : R₀ →+* Γ(X, W.1) :=
  (Spec.preimage (W.2.fromSpec ≫ f₀)).hom

/- English proof (translation)
Simplify using `[baseHom]`.
-/
lemma fromSpec_comp (W : X.affineOpens) :
    W.2.fromSpec ≫ f₀ = Spec.map (CommRingCat.ofHom (baseHom f₀ W)) := by
  simp [baseHom]

/- English proof (translation)
Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
lemma spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : B →+* C) (q : A →+* B) :
    Spec.map (CommRingCat.ofHom (p.comp q)) =
      Spec.map (CommRingCat.ofHom p) ≫ Spec.map (CommRingCat.ofHom q) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
lemma spec_inj {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B}
    (h : Spec.map (CommRingCat.ofHom p) = Spec.map (CommRingCat.ofHom q)) : p = q :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Rewrite using `[pt, Category.assoc, fromSpec_comp, spec_comp]`.
-/
lemma pt_comp (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A) :
    pt W p ≫ f₀ = Spec.map (CommRingCat.ofHom (p.comp (baseHom f₀ W))) := by
  rw [pt, Category.assoc, fromSpec_comp, spec_comp]

/- English proof (translation)
Apply `spec_inj` to reduce the goal to its premises. Rewrite using `[← pt_comp, ← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, spec_comp]`.
-/
lemma base_eq {T A : Type} [CommRing T] [CommRing A] (ψ : R₀ →+* T) (W : X.affineOpens)
    (p : Γ(X, W.1) →+* A) (t : T →+* A)
    (l : Spec (CommRingCat.of A) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h1 : l ≫ pullback.fst _ _ = pt W p)
    (h2 : l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom t)) :
    p.comp (baseHom f₀ W) = t.comp ψ := by
  apply spec_inj
  rw [← pt_comp, ← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, spec_comp]

variable {f₀}

/- English proof (translation)
Set `ã : Spec (CommRingCat.of L) ⟶ Y` to `hpb.lift a₀ (Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ))) (by rw [H, ← spec_comp])`. Establish `ã₁ : ã ≫ π = a₀` using `hpb.lift_fst _ _ _`. Establish `ã₂ : ã ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ))` using `hpb.lift_snd _ _ _`. Set `sq : ValuativeCommSq f` to `{ R := B, K := L, i₁ := ã, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := ⟨by rw [ã₂, spec_comp]⟩ }`. Take `⟨u⟩` from `hval sq`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `l` to `(u.default : sq.commSq.LiftStruct)`. Establish `l₁ : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ l.l = ã` using `l.fac_left`. Establish `l₂ : l.l ≫ f = Spec.map (CommRingCat.ofHom ρ)` using `l.fac_right`. Use `⟨l.l ≫ π, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hpb.w, ← Category.assoc, l₂, spec_comp]`. Rewrite using `[← Category.assoc, l₁, ã₁]`. Introduce `ℓ₁ ℓ₂ e₁ e₂ d₁ d₂`. Establish `mk : ∀ ℓ : Spec (CommRingCat.of B) ⟶ X, ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) → Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀ → ∃ l : sq.commSq.LiftStruct, l.l ≫ π = ℓ`. Introduce `ℓ e d`.

Set `m : Spec (CommRingCat.of B) ⟶ Y` to `hpb.lift ℓ (Spec.map (CommRingCat.ofHom ρ)) (by rw [e, spec_comp])`. Establish `m₁ : m ≫ π = ℓ` using `hpb.lift_fst _ _ _`. Establish `m₂ : m ≫ f = Spec.map (CommRingCat.ofHom ρ)` using `hpb.lift_snd _ _ _`. Use `⟨⟨m, ?_, m₂⟩, m₁⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ m = ã`.

Apply `hpb.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, m₁, d, ã₁]`. Rewrite using `[Category.assoc, m₂, ã₂, spec_comp]`. Take `⟨l₁, rfl⟩` from `mk ℓ₁ e₁ d₁`. Take `⟨l₂, rfl⟩` from `mk ℓ₂ e₂ d₂`.

Rewrite using `[show l₁ = l₂ from (u.uniq l₁).trans (u.uniq l₂).symm]`.
-/
lemma val_lift {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L]
    [IsFractionRing B L] (ρ : R →+* B) (a₀ : Spec (CommRingCat.of L) ⟶ X)
    (H : a₀ ≫ f₀ = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp (ρ.comp φ)))) :
    (∃ ℓ : Spec (CommRingCat.of B) ⟶ X, ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀) ∧
    ∀ ℓ₁ ℓ₂ : Spec (CommRingCat.of B) ⟶ X,
      ℓ₁ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      ℓ₂ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₁ = a₀ →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₂ = a₀ → ℓ₁ = ℓ₂ := by
  let ã : Spec (CommRingCat.of L) ⟶ Y :=
    hpb.lift a₀ (Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ)))
      (by rw [H, ← spec_comp])
  have ã₁ : ã ≫ π = a₀ := hpb.lift_fst _ _ _
  have ã₂ : ã ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ)) := hpb.lift_snd _ _ _
  let sq : ValuativeCommSq f :=
    { R := B, K := L, i₁ := ã, i₂ := Spec.map (CommRingCat.ofHom ρ),
      commSq := ⟨by rw [ã₂, spec_comp]⟩ }
  obtain ⟨u⟩ := hval sq
  refine ⟨?_, ?_⟩
  · let l := (u.default : sq.commSq.LiftStruct)
    have l₁ : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ l.l = ã := l.fac_left
    have l₂ : l.l ≫ f = Spec.map (CommRingCat.ofHom ρ) := l.fac_right
    refine ⟨l.l ≫ π, ?_, ?_⟩
    · rw [Category.assoc, hpb.w, ← Category.assoc, l₂, spec_comp]
    · rw [← Category.assoc, l₁, ã₁]
  · intro ℓ₁ ℓ₂ e₁ e₂ d₁ d₂
    have mk : ∀ ℓ : Spec (CommRingCat.of B) ⟶ X,
        ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
        Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀ →
        ∃ l : sq.commSq.LiftStruct, l.l ≫ π = ℓ := by
      intro ℓ e d
      let m : Spec (CommRingCat.of B) ⟶ Y :=
        hpb.lift ℓ (Spec.map (CommRingCat.ofHom ρ)) (by rw [e, spec_comp])
      have m₁ : m ≫ π = ℓ := hpb.lift_fst _ _ _
      have m₂ : m ≫ f = Spec.map (CommRingCat.ofHom ρ) := hpb.lift_snd _ _ _
      refine ⟨⟨m, ?_, m₂⟩, m₁⟩
      change Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ m = ã
      apply hpb.hom_ext
      · rw [Category.assoc, m₁, d, ã₁]
      · rw [Category.assoc, m₂, ã₂, spec_comp]
    obtain ⟨l₁, rfl⟩ := mk ℓ₁ e₁ d₁
    obtain ⟨l₂, rfl⟩ := mk ℓ₂ e₂ d₂
    rw [show l₁ = l₂ from (u.uniq l₁).trans (u.uniq l₂).symm]

variable (f₀)

variable {ι : Type} (U : Ultrafilter ι) {T V K : ι → Type} [∀ i, CommRing (T i)]
  [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)] [∀ i, IsFractionRing (V i) (K i)]
  (ψ : ∀ i, R₀ →+* T i)
  (a : ∀ i, Spec (CommRingCat.of (K i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))))
  (β : ∀ i, T i →+* V i)

omit [∀ i, IsFractionRing (V i) (K i)] [∀ i, Field (K i)] [∀ i, Algebra (V i) (K i)] in
/- English proof (translation)
The claim follows from `ValuationRing.isLocalRing _`.
-/
lemma isLocalRing_ult : IsLocalRing (Ult U V) := ValuationRing.isLocalRing _

omit [∀ i, ValuationRing (V i)] [∀ i, IsFractionRing (V i) (K i)] in
/- English proof (translation)
Use `⟨?_, fun b => ?_⟩` and prove the remaining obligations. Use `filter_upwards [r.1] with i ⟨p, hp⟩`. Conclude with `⟨(algebraMap (V i) (K i)).comp p, by funext b; simp [← hp]⟩`. Rewrite using `[RingHom.comp_apply, r.2, algebraMap_mk]`.
-/
lemma rep_alg {B : Type} [CommRing B] {h : ∀ i, B → V i} {g : B →+* Ult U V} (r : Rep U h g) :
    Rep U (fun i b => algebraMap (V i) (K i) (h i b))
      ((algebraMap (Ult U V) (Ult U K)).comp g) := by
  refine ⟨?_, fun b => ?_⟩
  · filter_upwards [r.1] with i ⟨p, hp⟩
    exact ⟨(algebraMap (V i) (K i)).comp p, by funext b; simp [← hp]⟩
  · rw [RingHom.comp_apply, r.2, algebraMap_mk]

/- English proof (translation)
Take `⟨S, hSf, -, hS2⟩` from `exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)`. Establish `hQ : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, ∃ p : Γ(X, W.1) →+* K i, a i ≫ pullback.fst _ _ = pt W p`. Use `Filter.Eventually.of_forall fun i => ?_` and prove the remaining obligations. Take `⟨W, hW, hx⟩` from `hS2 ((a i ≫ pullback.fst _ _) (IsLocalRing.closedPoint (K i) : PrimeSpectrum (K i))) trivial`. Conclude with `⟨W, hW, exists_pt_of_isLocalRing _ W hx⟩`.

Take `⟨W₁, -, hQ⟩` from `exists_of_finite U hSf hQ`. Take `⟨h₁, hh⟩` from `exists_family U hQ`. Establish `ae : IsAEHom U h₁` using `by filter_upwards [hh] with i ⟨p, hp, _⟩`. Conclude with `⟨p, hp⟩`. Use `⟨W₁, h₁, homOf U h₁ ae, rep_homOf U h₁ ae, hh, ?_⟩` and prove the remaining obligations.

Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, homOf_apply, RingHom.comp_apply, RingHom.comp_apply, hρ, algebraMap_mk, mk_eq_mk_iff]`. Use `filter_upwards [hh] with i ⟨p, hp, e⟩`. Use `base_eq f₀ (ψ i) W₁ p ((algebraMap (V i) (K i)).comp (β i)) (a i) e (hsq i)` as an intermediate fact. Rewrite using `[← hp]`.

Conclude with `RingHom.congr_fun this r`.
-/
theorem exists_limit_point [CompactSpace X] (φ : R₀ →+* R)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∃ (W₁ : X.affineOpens) (h₁ : ∀ i, Γ(X, W₁.1) → K i) (P : Γ(X, W₁.1) →+* Ult U K),
      Rep U h₁ P ∧
      (∀ᶠ i in (U : Filter ι), ∃ p : Γ(X, W₁.1) →+* K i, ⇑p = h₁ i ∧
        a i ≫ pullback.fst _ _ = pt W₁ p) ∧
      P.comp (baseHom f₀ W₁) = (algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ) := by
  obtain ⟨S, hSf, -, hS2⟩ := exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, ∃ p : Γ(X, W.1) →+* K i,
      a i ≫ pullback.fst _ _ = pt W p := by
    refine Filter.Eventually.of_forall fun i => ?_
    obtain ⟨W, hW, hx⟩ := hS2 ((a i ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (K i) : PrimeSpectrum (K i))) trivial
    exact ⟨W, hW, exists_pt_of_isLocalRing _ W hx⟩
  obtain ⟨W₁, -, hQ⟩ := exists_of_finite U hSf hQ
  obtain ⟨h₁, hh⟩ := exists_family U hQ
  have ae : IsAEHom U h₁ := by
    filter_upwards [hh] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  refine ⟨W₁, h₁, homOf U h₁ ae, rep_homOf U h₁ ae, hh, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, homOf_apply, RingHom.comp_apply, RingHom.comp_apply, hρ, algebraMap_mk,
    mk_eq_mk_iff]
  filter_upwards [hh] with i ⟨p, hp, e⟩
  have := base_eq f₀ (ψ i) W₁ p ((algebraMap (V i) (K i)).comp (β i)) (a i) e (hsq i)
  rw [← hp]
  exact RingHom.congr_fun this r

/- English proof (translation)
Take `⟨W₁, h₁, P, rP, ha, hP⟩` from `exists_limit_point f₀ U ψ a β φ hsq ρ hρ`. Establish `H : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ)))` using `by rw [pt_comp, hP]`. Take `⟨⟨ℓ, e1, e2⟩, -⟩` from `val_lift hpb hval ρ (pt W₁ P) H`. Use `haveI := isLocalRing_ult U (V := V)`. Take `⟨W₂, hx, -⟩` from `exists_affine_le (show ℓ (IsLocalRing.closedPoint (Ult U V) : PrimeSpectrum (Ult U V)) ∈ (⊤ : X.Opens) from trivial)`.

Take `⟨γ, rfl⟩` from `exists_pt_of_isLocalRing ℓ W₂ hx`. Use `haveI := hfp W₂`. Take `⟨h₂, r₂⟩` from `exists_rep U γ`. Establish `hγ : γ.comp (baseHom f₀ W₂) = ρ.comp φ` using `spec_inj (by rw [← pt_comp, e1])`. Establish `c1 : ∀ᶠ i in (U : Filter ι), (fun b => h₂ i (baseHom f₀ W₂ b)) = fun r => β i (ψ i r)`.

Use `ae_eq_of_fg U (h := fun i b => h₂ i (baseHom f₀ W₂ b)) (h' := fun i r => β i (ψ i r)) ?_ (Filter.Eventually.of_forall fun i => ⟨(β i).comp (ψ i), rfl⟩) ?_` and prove the remaining obligations. Use `filter_upwards [r₂.1] with i ⟨p, hp⟩`. Conclude with `⟨p.comp (baseHom f₀ W₂), by funext b; simp [← hp]⟩`. Introduce `r`. Rewrite using `[← r₂.2, ← hρ]`.

Conclude with `RingHom.congr_fun hγ r`. Establish `c2` using `ae_pt_eq_of_pt_eq U hfp (rep_alg U (K := K) r₂) rP (by rw [← map_pt, e2])`. Use `filter_upwards [r₂.1, c1, c2, ha] with i ⟨p, hp⟩ d1 d2 ⟨q, hq, eq⟩`. Establish `hb : p.comp (baseHom f₀ W₂) = (β i).comp (ψ i)`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations.

Use `congrFun d1 r` as an intermediate fact. Rewrite `this` using `[← hp]`. Conclude with `this`. Use `⟨pullback.lift (pt W₂ p) (Spec.map (CommRingCat.ofHom (β i))) (by rw [pt_comp, hb, spec_comp]), ?_, pullback.lift_snd _ _ _⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, pullback.lift_fst, map_pt, eq]`. Conclude with `d2 ((algebraMap (V i) (K i)).comp p) q (by funext b; simp [← hp]) hq`. Rewrite using `[Category.assoc, pullback.lift_snd, hsq, spec_comp]`.
-/
theorem ae_exists_lift [CompactSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), ∃ l : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))),
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) := by
  obtain ⟨W₁, h₁, P, rP, ha, hP⟩ := exists_limit_point f₀ U ψ a β φ hsq ρ hρ
  have H : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom
      ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ))) := by rw [pt_comp, hP]
  obtain ⟨⟨ℓ, e1, e2⟩, -⟩ := val_lift hpb hval ρ (pt W₁ P) H
  haveI := isLocalRing_ult U (V := V)
  obtain ⟨W₂, hx, -⟩ := exists_affine_le (show ℓ (IsLocalRing.closedPoint (Ult U V) :
    PrimeSpectrum (Ult U V)) ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨γ, rfl⟩ := exists_pt_of_isLocalRing ℓ W₂ hx
  haveI := hfp W₂
  obtain ⟨h₂, r₂⟩ := exists_rep U γ
  have hγ : γ.comp (baseHom f₀ W₂) = ρ.comp φ := spec_inj (by rw [← pt_comp, e1])
  have c1 : ∀ᶠ i in (U : Filter ι), (fun b => h₂ i (baseHom f₀ W₂ b)) = fun r => β i (ψ i r) := by
    refine ae_eq_of_fg U (h := fun i b => h₂ i (baseHom f₀ W₂ b)) (h' := fun i r => β i (ψ i r))
      ?_ (Filter.Eventually.of_forall fun i => ⟨(β i).comp (ψ i), rfl⟩) ?_
    · filter_upwards [r₂.1] with i ⟨p, hp⟩
      exact ⟨p.comp (baseHom f₀ W₂), by funext b; simp [← hp]⟩
    · intro r
      rw [← r₂.2, ← hρ]
      exact RingHom.congr_fun hγ r
  have c2 := ae_pt_eq_of_pt_eq U hfp (rep_alg U (K := K) r₂) rP (by rw [← map_pt, e2])
  filter_upwards [r₂.1, c1, c2, ha] with i ⟨p, hp⟩ d1 d2 ⟨q, hq, eq⟩
  have hb : p.comp (baseHom f₀ W₂) = (β i).comp (ψ i) := by
    refine RingHom.ext fun r => ?_
    have := congrFun d1 r
    rw [← hp] at this
    exact this
  refine ⟨pullback.lift (pt W₂ p) (Spec.map (CommRingCat.ofHom (β i)))
    (by rw [pt_comp, hb, spec_comp]), ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, map_pt, eq]
    exact d2 ((algebraMap (V i) (K i)).comp p) q (by funext b; simp [← hp]) hq
  · rw [Category.assoc, pullback.lift_snd, hsq, spec_comp]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pt_comp]`. Use `congr 2`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, r.2, RingHom.comp_apply, hρ, mk_eq_mk_iff]`.

Use `filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩`. Use `base_eq f₀ (ψ i) W p (β i) l h1 h2` as an intermediate fact. Rewrite using `[← hp]`. Conclude with `RingHom.congr_fun this x`. Rewrite using `[map_pt]`.

Use `pt_eq_of_ae_pt_eq U (rep_alg U (K := K) r) rP ?_` and prove the remaining obligations. Use `filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩`. Use `⟨(algebraMap (V i) (K i)).comp p, q, by funext b; simp [← hp], hq, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pt, ← h1, ← Category.assoc, h3, h4]`.
-/
lemma limit_lift [QuasiSeparatedSpace X] {φ : R₀ →+* R}
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    {W W₁ : X.affineOpens} {h : ∀ i, Γ(X, W.1) → V i} {G : Γ(X, W.1) →+* Ult U V} (r : Rep U h G)
    {h₁ : ∀ i, Γ(X, W₁.1) → K i} {P : Γ(X, W₁.1) →+* Ult U K} (rP : Rep U h₁ P)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W.1) →+* V i) (q : Γ(X, W₁.1) →+* K i)
      (l : Spec (CommRingCat.of (V i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))),
      ⇑p = h i ∧ ⇑q = h₁ i ∧ l ≫ pullback.fst _ _ = pt W p ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      a i ≫ pullback.fst _ _ = pt W₁ q) :
    pt W G ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
    Spec.map (CommRingCat.ofHom (algebraMap (Ult U V) (Ult U K))) ≫ pt W G = pt W₁ P := by
  refine ⟨?_, ?_⟩
  · rw [pt_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, r.2, RingHom.comp_apply, hρ, mk_eq_mk_iff]
    filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩
    have := base_eq f₀ (ψ i) W p (β i) l h1 h2
    rw [← hp]
    exact RingHom.congr_fun this x
  · rw [map_pt]
    refine pt_eq_of_ae_pt_eq U (rep_alg U (K := K) r) rP ?_
    filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩
    refine ⟨(algebraMap (V i) (K i)).comp p, q, by funext b; simp [← hp], hq, ?_⟩
    rw [← map_pt, ← h1, ← Category.assoc, h3, h4]

/- English proof (translation)
Take `⟨W₁, h₁, P, rP, ha, hP⟩` from `exists_limit_point f₀ U ψ a β φ hsq ρ hρ`. Establish `HP : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ)))` using `by rw [pt_comp, hP]`. Use `haveI := isLocalRing_ult U (V := V)`. Take `⟨S, hSf, -, hS2⟩` from `exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)`. Establish `hQ : ∀ᶠ i in (U : Filter ι), ∃ w ∈ S ×ˢ S, ∃ (p : Γ(X, w.1.1) →+* V i) (q : Γ(X, w.2.1) →+* V i) (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), l₁ ≠ l₂ ∧ Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧ Spec.map (CommRi …` using `by filter_upwards [H] with i ⟨l₁, l₂, hne, a1, a2, s1, s2⟩`.

Take `⟨A₁, hA₁, x₁⟩` from `hS2 ((l₁ ≫ pullback.fst _ _) (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial`. Take `⟨A₂, hA₂, x₂⟩` from `hS2 ((l₂ ≫ pullback.fst _ _) (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial`. Take `⟨p, hp⟩` from `exists_pt_of_isLocalRing _ A₁ x₁`. Take `⟨q, hq⟩` from `exists_pt_of_isLocalRing _ A₂ x₂`. Conclude with `⟨(A₁, A₂), ⟨hA₁, hA₂⟩, p, q, l₁, l₂, hne, a1, a2, s1, s2, hp, hq⟩`.

Take `⟨⟨W₂, W₃⟩, -, hQ⟩` from `exists_of_finite U (hSf.prod hSf) hQ`. Simplify using `only at hQ`. Take `⟨h₂, hh₂⟩` from `exists_family U hQ`. Establish `hQ' : ∀ᶠ i in (U : Filter ι), ∃ (q : Γ(X, W₃.1) →+* V i) (p : Γ(X, W₂.1) →+* V i) (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), ⇑p = h₂ i ∧ l₁ ≠ l₂ ∧ Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧ Spec.map (CommRingC …` using `by filter_upwards [hh₂] with i ⟨p, hp, q, l₁, l₂, hne, a1, a2, s1, s2, f1, f2⟩`. Conclude with `⟨q, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩`.

Take `⟨h₃, hh₃⟩` from `exists_family U hQ'`. Establish `ae₂ : IsAEHom U h₂` using `by filter_upwards [hh₂] with i ⟨p, hp, _⟩`. Conclude with `⟨p, hp⟩`. Establish `ae₃ : IsAEHom U h₃` using `by filter_upwards [hh₃] with i ⟨p, hp, _⟩`. Conclude with `⟨p, hp⟩`.

Establish `L₂` using `limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₂ ae₂) rP (by filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩`. Conclude with `⟨p, t, l₁, hp, ht, f1, s1, a1, et⟩)`. Establish `L₃` using `limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₃ ae₃) rP (by filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩`. Conclude with `⟨q, t, l₂, hq, ht, f2, s2, a2, et⟩)`. Establish `E` using `(val_lift hpb hval ρ (pt W₁ P) HP).2 _ _ L₂.1 L₃.1 L₂.2 L₃.2`.

Establish `c` using `ae_pt_eq_of_pt_eq U hfp (rep_homOf U h₂ ae₂) (rep_homOf U h₃ ae₃) E`. Take `⟨i, d, q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩` from `(c.and hh₃).exists`. Apply `hne` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[f1, f2]`.

Conclude with `d p q hp hq`. Rewrite using `[s1, s2]`.
-/
theorem not_ae_two_lifts [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    (H : ∀ᶠ i in (U : Filter ι), ∃ l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i))) : False := by
  obtain ⟨W₁, h₁, P, rP, ha, hP⟩ := exists_limit_point f₀ U ψ a β φ hsq ρ hρ
  have HP : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom
      ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ))) := by rw [pt_comp, hP]
  haveI := isLocalRing_ult U (V := V)
  obtain ⟨S, hSf, -, hS2⟩ := exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ w ∈ S ×ˢ S, ∃ (p : Γ(X, w.1.1) →+* V i)
      (q : Γ(X, w.2.1) →+* V i) (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₁ ≫ pullback.fst _ _ = pt w.1 p ∧ l₂ ≫ pullback.fst _ _ = pt w.2 q := by
    filter_upwards [H] with i ⟨l₁, l₂, hne, a1, a2, s1, s2⟩
    obtain ⟨A₁, hA₁, x₁⟩ := hS2 ((l₁ ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial
    obtain ⟨A₂, hA₂, x₂⟩ := hS2 ((l₂ ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial
    obtain ⟨p, hp⟩ := exists_pt_of_isLocalRing _ A₁ x₁
    obtain ⟨q, hq⟩ := exists_pt_of_isLocalRing _ A₂ x₂
    exact ⟨(A₁, A₂), ⟨hA₁, hA₂⟩, p, q, l₁, l₂, hne, a1, a2, s1, s2, hp, hq⟩
  obtain ⟨⟨W₂, W₃⟩, -, hQ⟩ := exists_of_finite U (hSf.prod hSf) hQ
  dsimp only at hQ
  obtain ⟨h₂, hh₂⟩ := exists_family U hQ
  have hQ' : ∀ᶠ i in (U : Filter ι), ∃ (q : Γ(X, W₃.1) →+* V i) (p : Γ(X, W₂.1) →+* V i)
      (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), ⇑p = h₂ i ∧ l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₁ ≫ pullback.fst _ _ = pt W₂ p ∧ l₂ ≫ pullback.fst _ _ = pt W₃ q := by
    filter_upwards [hh₂] with i ⟨p, hp, q, l₁, l₂, hne, a1, a2, s1, s2, f1, f2⟩
    exact ⟨q, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩
  obtain ⟨h₃, hh₃⟩ := exists_family U hQ'
  have ae₂ : IsAEHom U h₂ := by
    filter_upwards [hh₂] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have ae₃ : IsAEHom U h₃ := by
    filter_upwards [hh₃] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have L₂ := limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₂ ae₂) rP (by
    filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩
    exact ⟨p, t, l₁, hp, ht, f1, s1, a1, et⟩)
  have L₃ := limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₃ ae₃) rP (by
    filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩
    exact ⟨q, t, l₂, hq, ht, f2, s2, a2, et⟩)
  have E := (val_lift hpb hval ρ (pt W₁ P) HP).2 _ _ L₂.1 L₃.1 L₂.2 L₃.2
  have c := ae_pt_eq_of_pt_eq U hfp (rep_homOf U h₂ ae₂) (rep_homOf U h₃ ae₃) E
  obtain ⟨i, d, q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ := (c.and hh₃).exists
  apply hne
  apply pullback.hom_ext
  · rw [f1, f2]
    exact d p q hp hq
  · rw [s1, s2]

/- English proof (translation)
Establish `hsq : ∀ i, (S i).i₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ((algebraMap (S i).R (S i).K).comp (β i)))` using `fun i => by`. Rewrite using `[(S i).commSq.w, hβ, spec_comp]`. Establish `E` using `ae_exists_lift f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ`. Establish `Uq : ∀ᶠ i in (U : Filter ι), Subsingleton (S i).commSq.LiftStruct`. Assume the negation of the conclusion as `hc`.

Establish `hc'` using `Ultrafilter.eventually_not.2 hc`. Use `not_ae_two_lifts f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ ?_` and prove the remaining obligations. Use `filter_upwards [hc'] with i hi`. Take `⟨l₁, l₂, hne⟩` from `(not_subsingleton_iff_nontrivial.1 hi).exists_pair_ne`. Conclude with `⟨l₁.l, l₂.l, fun h => hne (CommSq.LiftStruct.ext h), l₁.fac_left, l₂.fac_left, l₁.fac_right.trans (hβ i), l₂.fac_right.trans (hβ i)⟩`.

Use `filter_upwards [E, Uq] with i ⟨l, h1, h2⟩ hs`. Establish `hn : Nonempty (S i).commSq.LiftStruct` using `⟨⟨l, h1, h2.trans (hβ i).symm⟩⟩`. Conclude with `unique_iff_subsingleton_and_nonempty _ |>.2 ⟨hs, hn⟩`.
-/
theorem ae_unique_lift [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {ι : Type} (U : Ultrafilter ι) {T : ι → Type} [∀ i, CommRing (T i)] (ψ : ∀ i, R₀ →+* T i)
    (S : ∀ i, ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (ψ i)))))
    (β : ∀ i, T i →+* (S i).R) (hβ : ∀ i, (S i).i₂ = Spec.map (CommRingCat.ofHom (β i)))
    (ρ : R →+* Ult U (fun i => (S i).R))
    (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), Nonempty (Unique (S i).commSq.LiftStruct) := by
  have hsq : ∀ i, (S i).i₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      ((algebraMap (S i).R (S i).K).comp (β i))) := fun i => by
    rw [(S i).commSq.w, hβ, spec_comp]
  have E := ae_exists_lift f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ
    (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ
  have Uq : ∀ᶠ i in (U : Filter ι), Subsingleton (S i).commSq.LiftStruct := by
    by_contra hc
    have hc' := Ultrafilter.eventually_not.2 hc
    refine not_ae_two_lifts f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ
      (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ ?_
    filter_upwards [hc'] with i hi
    obtain ⟨l₁, l₂, hne⟩ := (not_subsingleton_iff_nontrivial.1 hi).exists_pair_ne
    exact ⟨l₁.l, l₂.l, fun h => hne (CommSq.LiftStruct.ext h), l₁.fac_left, l₂.fac_left,
      l₁.fac_right.trans (hβ i), l₂.fac_right.trans (hβ i)⟩
  filter_upwards [E, Uq] with i ⟨l, h1, h2⟩ hs
  have hn : Nonempty (S i).commSq.LiftStruct := ⟨⟨l, h1, h2.trans (hβ i).symm⟩⟩
  exact unique_iff_subsingleton_and_nonempty _ |>.2 ⟨hs, hn⟩

omit [CommRing R] in
/- English proof (translation)
Establish `h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (baseHom f₀ W)))`. Rewrite using `[← fromSpec_comp]`. Use `infer_instance`. Establish `h2 : (baseHom f₀ W).FinitePresentation` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h1`. Establish `h3 : Algebra.FinitePresentation ℤ R₀` using `Algebra.FinitePresentation.of_finiteType.1 inferInstance`.

Establish `h4` using `h2.comp ((RingHom.finitePresentation_algebraMap).2 h3)`. Rewrite using `[← RingHom.finitePresentation_algebraMap]`. Use `h4` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`.
-/
lemma fp_sections [LocallyOfFinitePresentation f₀] [Algebra.FiniteType ℤ R₀] (W : X.affineOpens) :
    Algebra.FinitePresentation ℤ Γ(X, W.1) := by
  have h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (baseHom f₀ W))) := by
    rw [← fromSpec_comp]; infer_instance
  have h2 : (baseHom f₀ W).FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h1
  have h3 : Algebra.FinitePresentation ℤ R₀ := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have h4 := h2.comp ((RingHom.finitePresentation_algebraMap).2 h3)
  rw [← RingHom.finitePresentation_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

end Core

def lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) (S₀ : Set R₀) (F : Finset R) :
    Subalgebra ℤ R :=
  Algebra.adjoin ℤ (φ '' S₀ ∪ (F : Set R))

/- English proof (translation)
Establish `hr : r ∈ Algebra.adjoin ℤ S₀` using `hS₀ ▸ Algebra.mem_top`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)`. Consider the case `algebraMap z => simpa using (lvl φ S₀ F).algebraMap_mem z`. Consider the case `add x y _ _ hx hy => simpa using (lvl φ S₀ F).add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => simpa using (lvl φ S₀ F).mul_mem hx hy`.
-/
lemma map_mem_lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) (F : Finset R) (r : R₀) : φ r ∈ lvl φ S₀ F := by
  have hr : r ∈ Algebra.adjoin ℤ S₀ := hS₀ ▸ Algebra.mem_top
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  | algebraMap z => simpa using (lvl φ S₀ F).algebraMap_mem z
  | add x y _ _ hx hy => simpa using (lvl φ S₀ F).add_mem hx hy
  | mul x y _ _ hx hy => simpa using (lvl φ S₀ F).mul_mem hx hy

/- English proof (translation)
The claim follows from `(Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, (hS₀.image φ).union F.finite_toSet, rfl⟩)`.
-/
lemma finiteType_lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : S₀.Finite) (F : Finset R) : Algebra.FiniteType ℤ (lvl φ S₀ F) :=
  (Subalgebra.fg_iff_finiteType _).1
    (Subalgebra.fg_def.2 ⟨_, (hS₀.image φ).union F.finite_toSet, rfl⟩)

def lvlHom {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) (F : Finset R) : R₀ →+* lvl φ S₀ F :=
  φ.codRestrict (lvl φ S₀ F) (map_mem_lvl φ hS₀ F)

/- English proof (translation)
Establish `hmem : ∀ r : R, ∀ᶠ F in (U : Filter (Finset R)), r ∈ lvl φ S₀ F`. Introduce `r`. Use `filter_upwards [hU (eventually_ge_atTop ({r} : Finset R))] with F hF`. Conclude with `Algebra.subset_adjoin (Or.inr (by simpa using hF))`. Set `h : ∀ F, R → V F` to `fun F r => if hr : r ∈ lvl φ S₀ F then β F ⟨r, hr⟩ else 0`.

Establish `hv : ∀ (F : Finset R) (r : R) (hr : r ∈ lvl φ S₀ F), h F r = β F ⟨r, hr⟩` using `fun F r hr => dif_pos hr`. Use `⟨ofFamily U h ?_ ?_ ?_, fun r => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hmem 1] with F h1`. Rewrite using `[hv F 1 h1]`. Conclude with `map_one (β F)`.

Introduce `a b filter_upwards [hmem a, hmem b, hmem (a + b)] with F ha hb hab`. Rewrite using `[hv F _ hab, hv F _ ha, hv F _ hb, ← map_add]`. Both sides reduce to the same expression. Introduce `a b filter_upwards [hmem a, hmem b, hmem (a * b)] with F ha hb hab`. Rewrite using `[hv F _ hab, hv F _ ha, hv F _ hb, ← map_mul]`.

Both sides reduce to the same expression. Use `(ofFamily_apply U h _ _ _ (φ r)).trans ((mk_eq_mk_iff U).2 ?_)` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun F => ?_` and prove the remaining obligations. Rewrite using `[hv F _ (map_mem_lvl φ hS₀ F r)]`. Both sides reduce to the same expression.
-/
lemma exists_limit_hom {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) {V : Finset R → Type} [∀ F, CommRing (V F)]
    (β : ∀ F, lvl φ S₀ F →+* V F) (U : Ultrafilter (Finset R))
    (hU : (U : Filter (Finset R)) ≤ atTop) :
    ∃ ρ : R →+* Ult U V, ∀ r, ρ (φ r) = mk U (fun F => β F (lvlHom φ hS₀ F r)) := by
  classical
  have hmem : ∀ r : R, ∀ᶠ F in (U : Filter (Finset R)), r ∈ lvl φ S₀ F := by
    intro r
    filter_upwards [hU (eventually_ge_atTop ({r} : Finset R))] with F hF
    exact Algebra.subset_adjoin (Or.inr (by simpa using hF))
  let h : ∀ F, R → V F := fun F r => if hr : r ∈ lvl φ S₀ F then β F ⟨r, hr⟩ else 0
  have hv : ∀ (F : Finset R) (r : R) (hr : r ∈ lvl φ S₀ F), h F r = β F ⟨r, hr⟩ :=
    fun F r hr => dif_pos hr
  refine ⟨ofFamily U h ?_ ?_ ?_, fun r => ?_⟩
  · filter_upwards [hmem 1] with F h1
    rw [hv F 1 h1]
    exact map_one (β F)
  · intro a b
    filter_upwards [hmem a, hmem b, hmem (a + b)] with F ha hb hab
    rw [hv F _ hab, hv F _ ha, hv F _ hb, ← map_add]
    rfl
  · intro a b
    filter_upwards [hmem a, hmem b, hmem (a * b)] with F ha hb hab
    rw [hv F _ hab, hv F _ ha, hv F _ hb, ← map_mul]
    rfl
  · refine (ofFamily_apply U h _ _ _ (φ r)).trans ((mk_eq_mk_iff U).2 ?_)
    refine Filter.Eventually.of_forall fun F => ?_
    rw [hv F _ (map_mem_lvl φ hS₀ F r)]
    rfl

end GlobalTheory.CompanionTheory.Ultra

namespace GlobalTheory.CompanionTheory.SpreadingModels

open GlobalTheory.CompanionTheory.Ultra

/- English proof (translation)
Introduce `R R₀ _ _ φ Y Y₀ f f₀ π ⟨hft, hlfp, hqc, hqs, hpb⟩ hprop`. Establish `hprop' : IsProper f` using `hprop`. Establish `hval : ValuativeCriterion f`. Rewrite `hprop'` using `[IsProper.eq_valuativeCriterion]`. Conclude with `hprop'.1.1.1`.

Use `haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀`. Use `haveI : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated f₀`. Establish `hfp` using `fp_sections f₀ (R₀ := R₀)`. Take `⟨S₀, hS₀⟩` from `hft.out`. Establish `hS₀f : (S₀ : Set R₀).Finite` using `S₀.finite_toSet`.

It suffices to establish `h : ∃ F, IsProper (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (lvlHom φ hS₀ F)))) by`. Take `⟨F, hF⟩` from `h`. Conclude with `⟨lvl φ S₀ F, inferInstance, lvlHom φ hS₀ F, (lvl φ S₀ F).val.toRingHom, rfl, finiteType_lvl φ hS₀f F, hF⟩`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hS : ∀ F, ∃ S : ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (lvlHom φ hS₀ F)))), ¬ Nonempty (Unique S.commSq.LiftStruct)`. Introduce `F`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hcon F` to reduce the goal to its premises.

Rewrite using `[IsProper.eq_valuativeCriterion]`. Conclude with `⟨⟨⟨h, inferInstance⟩, inferInstance⟩, inferInstance⟩`. Use `choose S hS using hS`. Set `U : Ultrafilter (Finset R)` to `Ultrafilter.of atTop`. Establish `hU : (U : Filter (Finset R)) ≤ atTop` using `Ultrafilter.of_le _`.

Set `β : ∀ F, lvl φ S₀ F →+* (S F).R` to `fun F => (Spec.preimage (S F).i₂).hom`. Establish `hβ : ∀ F, (S F).i₂ = Spec.map (CommRingCat.ofHom (β F))` using `fun F => by simp [β]`. Take `⟨ρ, hρ⟩` from `exists_limit_hom φ hS₀ (V := fun F => (S F).R) β U hU`. Take `⟨F, hF⟩` from `(ae_unique_lift f₀ hfp hpb hval U (lvlHom φ hS₀) S β hβ ρ hρ).exists`. Conclude with `hS F hF`.
-/
theorem properSpreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hft, hlfp, hqc, hqs, hpb⟩ hprop
  have hprop' : IsProper f := hprop
  have hval : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hprop'
    exact hprop'.1.1.1
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  haveI : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated f₀
  have hfp := fp_sections f₀ (R₀ := R₀)
  obtain ⟨S₀, hS₀⟩ := hft.out
  have hS₀f : (S₀ : Set R₀).Finite := S₀.finite_toSet
  suffices h : ∃ F, IsProper (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (lvlHom φ hS₀ F)))) by
    obtain ⟨F, hF⟩ := h
    exact ⟨lvl φ S₀ F, inferInstance, lvlHom φ hS₀ F, (lvl φ S₀ F).val.toRingHom, rfl,
      finiteType_lvl φ hS₀f F, hF⟩
  by_contra hcon
  push_neg at hcon
  have hS : ∀ F, ∃ S : ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom
      (lvlHom φ hS₀ F)))), ¬ Nonempty (Unique S.commSq.LiftStruct) := by
    intro F
    by_contra h
    push_neg at h
    apply hcon F
    rw [IsProper.eq_valuativeCriterion]
    exact ⟨⟨⟨h, inferInstance⟩, inferInstance⟩, inferInstance⟩
  choose S hS using hS
  let U : Ultrafilter (Finset R) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset R)) ≤ atTop := Ultrafilter.of_le _
  let β : ∀ F, lvl φ S₀ F →+* (S F).R := fun F => (Spec.preimage (S F).i₂).hom
  have hβ : ∀ F, (S F).i₂ = Spec.map (CommRingCat.ofHom (β F)) := fun F => by simp [β]
  obtain ⟨ρ, hρ⟩ := exists_limit_hom φ hS₀ (V := fun F => (S F).R) β U hU
  obtain ⟨F, hF⟩ := (ae_unique_lift f₀ hfp hpb hval U (lvlHom φ hS₀) S β hβ ρ hρ).exists
  exact hS F hF

end GlobalTheory.CompanionTheory.SpreadingModels
