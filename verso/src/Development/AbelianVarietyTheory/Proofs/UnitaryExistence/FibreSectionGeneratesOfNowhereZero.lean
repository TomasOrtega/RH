import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSectionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.NonzeroGenerates

/- English proof (translation)
Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
The claim follows from `Spec.map_id (CommRingCat.of A)`.
-/
theorem spMap_id' {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) :=
  Spec.map_id (CommRingCat.of A)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S T U : Type} [CommRing S] [CommRing T] [CommRing U]

/- English proof (translation)
Rewrite using `[spMap_id', Category.id_comp]`.
-/
theorem eq_id_comp (x : Sp S ⟶ Xo.X) : x = spMap (RingHom.id S) ≫ x := by
  rw [spMap_id', Category.id_comp]

/- English proof (translation)
The claim follows from `((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 a b i).1`.
-/
theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) : scal x (a * b) i = scal x a i * scal x b i :=
  ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 a b i).1

/- English proof (translation)
The claim follows from `((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 1 1 i).2.2`.
-/
theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 :=
  ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 1 1 i).2.2

/- English proof (translation)
The claim follows from `(GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.1 a s t`.
-/
theorem secBC_id_iff (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.1 a s t

/- English proof (translation)
Take `⟨t, ht, -⟩` from `GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S S (RingHom.id S) a x x (eq_id_comp x) s`. Conclude with `⟨t, (secBC_id_iff x a s t).1 ht⟩`.
-/
theorem exists_mul (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) :
    ∃ t : LB.Sec (PPx x), ∀ i, t.f i = scal x a i * s.f i := by
  obtain ⟨t, ht, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S S (RingHom.id S) a x x (eq_id_comp x) s
  exact ⟨t, (secBC_id_iff x a s t).1 ht⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S T φ 1 x x' hx s).exists`.
-/
theorem exists_pull (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (hx : x' = spMap φ ≫ x)
    (s : LB.Sec (PPx x)) : ∃ s' : LB.Sec (PPx x'), SecBC φ 1 x x' s s' :=
  (GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S T φ 1 x x' hx s).exists

/- English proof (translation)
The claim follows from `(GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T U φ ψ x x' x'' hx hx').1 a s s' s'' h`.
-/
theorem pull_trans_iff {φ : S →+* T} {ψ : T →+* U} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} {x'' : Sp U ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) (hx' : x'' = spMap ψ ≫ x') {a : S} {s s' s''} (h : SecBC φ a x x' s s') :
    SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'' :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T U φ ψ x x' x'' hx hx').1 a s s' s'' h

/- English proof (translation)
The claim follows from `(GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T T φ _ x x' x' hx (eq_id_comp x')).2.2.1 a s s' t' h`.
-/
theorem pull_mul_iff {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') :
    SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T T φ _ x x' x' hx (eq_id_comp x')).2.2.1 a s s' t' h

/- English proof (translation)
Rewrite using `[pull_trans_iff (eq_id_comp x) hx ((secBC_id_iff x a s t).2 hst), RingHom.comp_id, pull_mul_iff hx h]`.
-/
theorem pull_iff_of_mul {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s t : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (hst : ∀ i, t.f i = scal x a i * s.f i)
    (h : SecBC φ 1 x x' s s') : SecBC φ 1 x x' t t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i := by
  rw [pull_trans_iff (eq_id_comp x) hx ((secBC_id_iff x a s t).2 hst), RingHom.comp_id, pull_mul_iff hx h]

/- English proof (translation)
Establish `e : scal x a i = ((Formalism.L2.PjFree.gxSnd x).appLE ⊤ ((PPx x).U i) le_top).hom (toΓ S a)` using `rfl`. Rewrite `hq` using `[e]`. Use `erw [Scheme.basicOpen_appLE] at hq`. Establish `h2` using `hq.2`. Establish `e2 : (Sp S).basicOpen (toΓ S a) = PrimeSpectrum.basicOpen a` using `basicOpen_eq_of_affine (R := CommRingCat.of S) a`.

Use `erw [e2] at h2`. Conclude with `h2`.
-/
theorem not_mem_of_mem_basicOpen_scal (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) (q : Gx x)
    (hq : q ∈ (Gx x).basicOpen (scal x a i)) : a ∉ (Formalism.L2.PjFree.gxSnd x q).asIdeal := by
  have e : scal x a i = ((Formalism.L2.PjFree.gxSnd x).appLE ⊤ ((PPx x).U i) le_top).hom (toΓ S a) := rfl
  rw [e] at hq
  erw [Scheme.basicOpen_appLE] at hq
  have h2 := hq.2
  have e2 : (Sp S).basicOpen (toΓ S a) = PrimeSpectrum.basicOpen a :=
    basicOpen_eq_of_affine (R := CommRingCat.of S) a
  erw [e2] at h2
  exact h2

/- English proof (translation)
Take `⟨a, ha, -⟩` from `hθ s`. Establish `hu : IsUnit a`. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, ham⟩` from `exists_max_ideal_of_mem_nonunits hn`. Take `⟨q, i, hq, hqi⟩` from `hs ⟨m, hm.isPrime⟩`.

Rewrite `hqi` using `[ha i, Scheme.basicOpen_mul]`. Use `not_mem_of_mem_basicOpen_scal x a i q hqi.1` as an intermediate fact. Rewrite `this` using `[hq]`. Conclude with `this ham`. Take `⟨u, rfl⟩` from `hu`.

Introduce `t`. Take `⟨b, hb, hbu⟩` from `hθ t`. Use `⟨b * ↑u⁻¹, fun i => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[hb i, ha i, ← _root_.mul_assoc, ← scal_mul, Units.inv_mul_cancel_right]`. Establish `: c * u = b` using `hbu _ fun i => by rw [hc i, ha i, ← _root_.mul_assoc, ← scal_mul]`.

Rewrite using `[← this, Units.mul_inv_cancel_right]`.
-/
theorem secGen_of_secGen {x : Sp S ⟶ Xo.X} {θ s : LB.Sec (PPx x)} (hθ : SecGen x θ) (hs : SecNZ x s) :
    SecGen x s := by
  obtain ⟨a, ha, -⟩ := hθ s
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits hn
    obtain ⟨q, i, hq, hqi⟩ := hs ⟨m, hm.isPrime⟩
    rw [ha i, Scheme.basicOpen_mul] at hqi
    have := not_mem_of_mem_basicOpen_scal x a i q hqi.1
    rw [hq] at this
    exact this ham
  obtain ⟨u, rfl⟩ := hu
  intro t
  obtain ⟨b, hb, hbu⟩ := hθ t
  refine ⟨b * ↑u⁻¹, fun i => ?_, fun c hc => ?_⟩
  · rw [hb i, ha i, ← _root_.mul_assoc, ← scal_mul, Units.inv_mul_cancel_right]
  · have : c * u = b := hbu _ fun i => by rw [hc i, ha i, ← _root_.mul_assoc, ← scal_mul]
    rw [← this, Units.mul_inv_cancel_right]

/- English proof (translation)
Introduce `p'` and use `(GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo S T φ x x' hx s s' h p').2 (hs _)`.
-/
theorem secNZ_pull {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') (hs : SecNZ x s) : SecNZ x' s' :=
  fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo S T φ x x' hx s s' h p').2 (hs _)

/- English proof (translation)
Consider the cases of `s`. Consider the cases of `t`. Reduce the equality to equality of the corresponding arguments. Conclude with `funext h`.
-/
theorem sec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr
  exact funext h

end GlobalTheory.Frames.NonzeroGenerates

open GlobalTheory.Frames.NonzeroGenerates in

/- English proof (translation)
Introduce `hBC E _ _ _ H Dw l Xo S _ x s hs t`. Set `G : Set S` to `{g | ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (φ : S →+* T), ψ.comp (algebraMap S (Localization.Away g)) = φ → ∀ s' : LB.Sec (PPx (spMap φ ≫ x)), SecBC φ 1 x _ s s' → SecGen _ s'}`. Establish `hG : Ideal.span G = ⊤`. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hn`.

Take `⟨g, hg, θ, hθ⟩` from `GlobalTheory.T.exists_local_generator_stable_baseChange hBC E H Dw l Xo S x ⟨m, hm.isPrime⟩`. Use `hg (hle (Ideal.subset_span ?_))` and prove the remaining obligations. Introduce `T _ ψ φ hφ s' hs'`. Establish `e : spMap φ ≫ x = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x`. Rewrite using `[← hφ, spMap_comp', Category.assoc]`.

Take `⟨θ', hθ'⟩` from `exists_pull ψ _ _ e θ`. Conclude with `secGen_of_secGen (hθ T ψ _ θ' e hθ').1 (secNZ_pull rfl hs' hs)`. Use `choose sl hsl using fun g : S => exists_pull (algebraMap S (Localization.Away g)) x _ rfl s`. Use `choose tl htl using fun g : S => exists_pull (algebraMap S (Localization.Away g)) x _ rfl t`. Establish `hgen : ∀ g : G, SecGen _ (sl g)` using `fun g => g.2 _ (RingHom.id _) _ (RingHom.id_comp _) _ (hsl g)`.

Use `choose c hc hcu using fun g : G => hgen g (tl g)`. Establish `key : ∀ (g : G) (h : S) (α : Localization.Away g.1 →+* Localization.Away h), α.comp (algebraMap S _) = algebraMap S _ → ∀ i, (tl h).f i = scal _ (α (c g)) i * (sl h).f i`. Introduce `g h α hα`. Establish `e : spMap (algebraMap S (Localization.Away h)) ≫ x = spMap α ≫ spMap (algebraMap S (Localization.Away g.1)) ≫ x`. Rewrite using `[← hα, spMap_comp', Category.assoc]`.

Establish `h1 : SecBC α 1 _ _ (sl g) (sl h)` using `(pull_trans_iff rfl e (hsl g)).2 (by rw [hα]; exact hsl h)`. Establish `h2 : SecBC α 1 _ _ (tl g) (tl h)` using `(pull_trans_iff rfl e (htl g)).2 (by rw [hα]; exact htl h)`. Conclude with `(pull_iff_of_mul e (hc g) h1).1 h2`. Take `⟨a, ha, hau⟩` from `Localization.existsUnique_algebraMap_eq_of_span_eq_top G hG c (fun g h => by`. Establish `hα : (IsLocalization.Away.awayToAwayRight (S` using `Localization.Away g.1) (P := Localization.Away (g.1 * h.1)) g.1 h.1).comp (algebraMap S _) = algebraMap S _ := RingHom.ext fun r => IsLocalization.Away.awayToAwayRight_eq g.1 h.1 r`.

Establish `hβ : (IsLocalization.Away.awayToAwayLeft (S` using `Localization.Away h.1) (P := Localization.Away (g.1 * h.1)) h.1 g.1).comp (algebraMap S _) = algebraMap S _ := RingHom.ext fun r => IsLocalization.Away.awayToAwayLeft_eq h.1 g.1 r`. Conclude with `(g.2 _ _ _ hα _ (hsl _) (tl _)).unique (key g _ _ hα) (key h _ _ hβ))`. Use `⟨a, ?_, fun b hb => hau b fun g => hcu g _ ((pull_iff_of_mul rfl hb (hsl g)).1 (htl g))⟩` and prove the remaining obligations. Take `⟨t₀, ht₀⟩` from `exists_mul x a s`. Establish `hloc : ∀ g : G, SecBC (algebraMap S (Localization.Away g.1)) 1 x _ t₀ (tl g)` using `fun g => (pull_iff_of_mul rfl ht₀ (hsl g)).2 (by rw [ha g]; exact hc g)`.

Take `⟨F, hF, h1⟩` from `Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 hG)`. Set `h : Fin F.card → S` to `fun i => (F.equivFin.symm i).1`. Establish `hr : Set.range h = F`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(F.equivFin.symm i).2`. Introduce `hy`. Conclude with `⟨F.equivFin ⟨y, hy⟩, by simp [h]⟩`. Establish `hh : Ideal.span (Set.range h) = ⊤`.

Rewrite using `[hr]`. Conclude with `(Ideal.eq_top_iff_one _).2 h1`. Establish `hmem : ∀ i, h i ∈ G` using `fun i => hF (F.equivFin.symm i).2`. Establish `glue` using `GlobalTheory.T.existsUnique_glue_sections_principal_cover E H Dw l Xo S x F.card h hh (fun i => tl (h i)) (fun i j α β hα hβ u hu => by`. Establish `e1 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x = spMap α ≫ spMap (algebraMap S (Localization.Away (h i))) ≫ x`.

Rewrite using `[← hα, spMap_comp', Category.assoc]`. Establish `e2 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x = spMap β ≫ spMap (algebraMap S (Localization.Away (h j))) ≫ x`. Rewrite using `[← hβ, spMap_comp', Category.assoc]`. Establish `h3` using `(pull_trans_iff rfl e1 (htl (h i))).1 hu`. Rewrite `h3` using `[hα]`.

Conclude with `(pull_trans_iff rfl e2 (htl (h j))).2 (by rw [hβ]; exact h3))`. Establish `: t = t₀` using `glue.unique (fun i => htl (h i)) (fun i => hloc ⟨h i, hmem i⟩)`. Rewrite using `[this]`. Conclude with `ht₀`.
-/
theorem GlobalTheory.Frames.secGen_of_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecNZ x s → SecGen x s := by
  intro hBC E _ _ _ H Dw l Xo S _ x s hs t
  classical

  let G : Set S := {g | ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (φ : S →+* T),
    ψ.comp (algebraMap S (Localization.Away g)) = φ → ∀ s' : LB.Sec (PPx (spMap φ ≫ x)),
      SecBC φ 1 x _ s s' → SecGen _ s'}
  have hG : Ideal.span G = ⊤ := by
    by_contra hn
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.T.exists_local_generator_stable_baseChange hBC E H Dw l Xo S x ⟨m, hm.isPrime⟩
    refine hg (hle (Ideal.subset_span ?_))
    intro T _ ψ φ hφ s' hs'
    have e : spMap φ ≫ x = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x := by
      rw [← hφ, spMap_comp', Category.assoc]
    obtain ⟨θ', hθ'⟩ := exists_pull ψ _ _ e θ
    exact secGen_of_secGen (hθ T ψ _ θ' e hθ').1 (secNZ_pull rfl hs' hs)
  choose sl hsl using fun g : S => exists_pull (algebraMap S (Localization.Away g)) x _ rfl s
  choose tl htl using fun g : S => exists_pull (algebraMap S (Localization.Away g)) x _ rfl t
  have hgen : ∀ g : G, SecGen _ (sl g) := fun g => g.2 _ (RingHom.id _) _ (RingHom.id_comp _) _ (hsl g)
  choose c hc hcu using fun g : G => hgen g (tl g)
  have key : ∀ (g : G) (h : S) (α : Localization.Away g.1 →+* Localization.Away h),
      α.comp (algebraMap S _) = algebraMap S _ →
      ∀ i, (tl h).f i = scal _ (α (c g)) i * (sl h).f i := by
    intro g h α hα
    have e : spMap (algebraMap S (Localization.Away h)) ≫ x =
        spMap α ≫ spMap (algebraMap S (Localization.Away g.1)) ≫ x := by
      rw [← hα, spMap_comp', Category.assoc]
    have h1 : SecBC α 1 _ _ (sl g) (sl h) := (pull_trans_iff rfl e (hsl g)).2 (by rw [hα]; exact hsl h)
    have h2 : SecBC α 1 _ _ (tl g) (tl h) := (pull_trans_iff rfl e (htl g)).2 (by rw [hα]; exact htl h)
    exact (pull_iff_of_mul e (hc g) h1).1 h2
  obtain ⟨a, ha, hau⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top G hG c (fun g h => by
    have hα : (IsLocalization.Away.awayToAwayRight (S := Localization.Away g.1)
        (P := Localization.Away (g.1 * h.1)) g.1 h.1).comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayRight_eq g.1 h.1 r
    have hβ : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away h.1)
        (P := Localization.Away (g.1 * h.1)) h.1 g.1).comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayLeft_eq h.1 g.1 r
    exact (g.2 _ _ _ hα _ (hsl _) (tl _)).unique (key g _ _ hα) (key h _ _ hβ))
  refine ⟨a, ?_, fun b hb => hau b fun g => hcu g _ ((pull_iff_of_mul rfl hb (hsl g)).1 (htl g))⟩
  obtain ⟨t₀, ht₀⟩ := exists_mul x a s
  have hloc : ∀ g : G, SecBC (algebraMap S (Localization.Away g.1)) 1 x _ t₀ (tl g) := fun g =>
    (pull_iff_of_mul rfl ht₀ (hsl g)).2 (by rw [ha g]; exact hc g)
  obtain ⟨F, hF, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 hG)
  let h : Fin F.card → S := fun i => (F.equivFin.symm i).1
  have hr : Set.range h = F := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (F.equivFin.symm i).2
    · intro hy
      exact ⟨F.equivFin ⟨y, hy⟩, by simp [h]⟩
  have hh : Ideal.span (Set.range h) = ⊤ := by
    rw [hr]; exact (Ideal.eq_top_iff_one _).2 h1
  have hmem : ∀ i, h i ∈ G := fun i => hF (F.equivFin.symm i).2
  have glue := GlobalTheory.T.existsUnique_glue_sections_principal_cover E H Dw l Xo S x F.card h hh (fun i => tl (h i)) (fun i j α β hα hβ u hu => by
    have e1 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x =
        spMap α ≫ spMap (algebraMap S (Localization.Away (h i))) ≫ x := by
      rw [← hα, spMap_comp', Category.assoc]
    have e2 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x =
        spMap β ≫ spMap (algebraMap S (Localization.Away (h j))) ≫ x := by
      rw [← hβ, spMap_comp', Category.assoc]
    have h3 := (pull_trans_iff rfl e1 (htl (h i))).1 hu
    rw [hα] at h3
    exact (pull_trans_iff rfl e2 (htl (h j))).2 (by rw [hβ]; exact h3))
  have : t = t₀ := glue.unique (fun i => htl (h i)) (fun i => hloc ⟨h i, hmem i⟩)
  rw [this]
  exact ht₀
