import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.BaseMdl

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {S : Type} [CommRing S] {x' : Sp S ⟶ X'}

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem one_left_congr {B T : Scheme.{0}} {G : Over B} [GrpObj G] {a b : T ⟶ B} (h : a = b) :
    (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by subst h; rfl

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]`.
-/
theorem prod_left_congr {B T : Scheme.{0}} {G : Over B} [GrpObj G] {a b : T ⟶ B} (h : a = b) {n : ℕ}
    (u : Fin n → (Over.mk a ⟶ G)) (u' : Fin n → (Over.mk b ⟶ G)) (hu : ∀ i, (u i).left = (u' i).left) :
    (List.ofFn u).prod.left = (List.ofFn u').prod.left := by
  subst h
  rw [show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]

/- English proof (translation)
Establish `e : (epsMul c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S)`. Apply the tactic sequence `ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]`. Use `conv_rhs => rw [← e]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem epsMul_comp (c : S) :
    spMap (epsMul c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsMul c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Establish `e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S`. Use extensionality with `s`. Simplify using the standard rewrite rules. Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, e]`.

Simplify using the standard rewrite rules.
-/
theorem fst_comp :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext s; simp
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  simp

/- English proof (translation)
The claim follows from `congrArg (fun q => q.left) (map_one (pushHom m.cart (Over.mk x')))`.
-/
theorem one_push : (1 : Over.mk x' ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x' ≫ f) ⟶ t.G).left :=
  congrArg (fun q => q.left) (map_one (pushHom m.cart (Over.mk x')))

/- English proof (translation)
Establish `e : (List.ofFn u).prod.left ≫ m.φ = (List.ofFn fun i => pushPt m.cart.1.w (u i)).prod.left` using `congrArg (fun q => q.left) ((map_list_prod (pushHom m.cart (tEpsG x')) _).trans (by rw [List.map_ofFn]; rfl))`. Conclude with `e.trans (prod_left_congr (Category.assoc _ _ _) _ _ fun i => (h i).symm)`.
-/
theorem prod_push {n : ℕ} (u : Fin n → (tEpsG x' ⟶ t'.G)) (u' : Fin n → (tEpsG (x' ≫ f) ⟶ t.G))
    (h : ∀ i, (u' i).left = (u i).left ≫ m.φ) :
    (List.ofFn u).prod.left ≫ m.φ = (List.ofFn u').prod.left := by
  have e : (List.ofFn u).prod.left ≫ m.φ =
      (List.ofFn fun i => pushPt m.cart.1.w (u i)).prod.left :=
    congrArg (fun q => q.left) ((map_list_prod (pushHom m.cart (tEpsG x')) _).trans (by rw [List.map_ofFn]; rfl))
  exact e.trans (prod_left_congr (Category.assoc _ _ _) _ _ fun i => (h i).symm)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, m.cart.1.w, ← Category.assoc, hv, Category.assoc]`. Rewrite using `[← Category.assoc, h.2, one_push]`.

Introduce `h`. Use `⟨hv, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Conclude with `h.2.trans (one_push m).symm`. Rewrite using `[Category.assoc, hv, ← Category.assoc, fst_comp, Category.id_comp]`.

Conclude with `(Over.w (1 : Over.mk x' ⟶ t'.G)).symm`.
-/
theorem tan_push {v : Sp (DualNumber S) ⟶ t'.G.left}
    (hv : v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsTanAtG t' x' v ↔ IsTanAtG t (x' ≫ f) (v ≫ m.φ) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hv, Category.assoc]
    · rw [← Category.assoc, h.2, one_push]
  · intro h
    refine ⟨hv, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]
      exact h.2.trans (one_push m).symm
    · rw [Category.assoc, hv, ← Category.assoc, fst_comp, Category.id_comp]
      exact (Over.w (1 : Over.mk x' ⟶ t'.G)).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨m.cart.1.lift w _ (hw.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩`.
-/
theorem exists_lift {w : Sp (DualNumber S) ⟶ t.G.left}
    (hw : w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f) :
    ∃ v : Sp (DualNumber S) ⟶ t'.G.left, v ≫ m.φ = w ∧ v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' :=
  ⟨m.cart.1.lift w _ (hw.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩

/- English proof (translation)
Establish `e : (v ≫ m.φ) ≫ (t.act.act a).left = (v ≫ (t'.act.act a).left) ≫ m.φ`. Rewrite using `[Category.assoc, Category.assoc, m.act a]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[h, Category.assoc]`. Introduce `h`. Use `m.cart.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w (t'.act.act a), Category.assoc, hv, ← Category.assoc, epsMul_comp]`.
-/
theorem eig_push {v : Sp (DualNumber S) ⟶ t'.G.left}
    (hv : v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') (a : 𝓞 E) (r : S) :
    v ≫ (t'.act.act a).left = spMap (epsMul r) ≫ v ↔
      (v ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul r) ≫ v ≫ m.φ := by
  have e : (v ≫ m.φ) ≫ (t.act.act a).left = (v ≫ (t'.act.act a).left) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, m.act a]
  rw [e]
  constructor
  · intro h
    rw [h, Category.assoc]
  · intro h
    refine m.cart.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_
    rw [Category.assoc, Over.w (t'.act.act a), Category.assoc, hv, ← Category.assoc, epsMul_comp]

/- English proof (translation)
Establish `hs : ∀ i, (spMap (epsMul (cf i)) ≫ v i) ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x'` using `fun i => by`. Rewrite using `[Category.assoc, hv, ← Category.assoc, epsMul_comp]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Use `⟨fun i => Over.homMk ((u i).left ≫ m.φ) ?_, fun i => ?_, (prod_push m u _ fun i => rfl).symm⟩` and prove the remaining obligations.

Use `show ((u i).left ≫ m.φ) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f`. Rewrite using `[Category.assoc, m.cart.1.w, ← Category.assoc, hu, hs, Category.assoc]`. Use `show (u i).left ≫ m.φ = _`. Rewrite using `[hu, Category.assoc]`. Introduce and unpack `⟨u, hu, hp⟩`.

Set `u' : Fin n → (tEpsG x' ⟶ t'.G)` to `fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (hs i)`. Use `⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Conclude with `(prod_push m u' u fun i => (hu i).trans (Category.assoc _ _ _).symm).trans hp`. Conclude with `(Over.w (List.ofFn u').prod).trans hw.symm`.
-/
theorem comb_push {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') (cf : Fin n → S)
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsCombAtG t' x' v cf w ↔ IsCombAtG t (x' ≫ f) (fun i => v i ≫ m.φ) cf (w ≫ m.φ) := by
  have hs : ∀ i, (spMap (epsMul (cf i)) ≫ v i) ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' := fun i => by
    rw [Category.assoc, hv, ← Category.assoc, epsMul_comp]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => Over.homMk ((u i).left ≫ m.φ) ?_, fun i => ?_, (prod_push m u _ fun i => rfl).symm⟩
    · show ((u i).left ≫ m.φ) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hu, hs, Category.assoc]
    · show (u i).left ≫ m.φ = _
      rw [hu, Category.assoc]
  · rintro ⟨u, hu, hp⟩
    let u' : Fin n → (tEpsG x' ⟶ t'.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (hs i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · exact (prod_push m u' u fun i => (hu i).trans (Category.assoc _ _ _).symm).trans hp
    · exact (Over.w (List.ofFn u').prod).trans hw.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun τ i => ⟨(tan_push m (hu τ i)).1 (h1 τ i).1, fun a => (eig_push m (hu τ i) a _).1 ((h1 τ i).2 a)⟩, fun τ w hw he => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl, hv⟩` from `exists_lift m hw.1`. Use `h2 τ v ((tan_push m hv).2 hw) fun a => (eig_push m hv a _).2 (he a)` as an intermediate fact.

Simplify `this` using `only [comb_push m (hu τ) _ hv]`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun τ i => ⟨(tan_push m (hu τ i)).2 (h1 τ i).1, fun a => (eig_push m (hu τ i) a _).2 ((h1 τ i).2 a)⟩, fun τ w hw he => ?_⟩` and prove the remaining obligations. Use `h2 τ _ ((tan_push m hw.1).1 hw) fun a => (eig_push m hw.1 a _).1 (he a)` as an intermediate fact. Simplify `this` using `only [comb_push m (hu τ) _ hw.1]`.
-/
theorem frame_push {l : Level H} {c : Coeff l} (g : c.F →+* S) (u : Vecs Dw t' S)
    (hu : ∀ τ i, u τ i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsFrame t' g x' u ↔ IsFrame t g (x' ≫ f) (fun τ i => u τ i ≫ m.φ : Vecs Dw t S) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ i => ⟨(tan_push m (hu τ i)).1 (h1 τ i).1, fun a => (eig_push m (hu τ i) a _).1 ((h1 τ i).2 a)⟩,
      fun τ w hw he => ?_⟩
    obtain ⟨v, rfl, hv⟩ := exists_lift m hw.1
    have := h2 τ v ((tan_push m hv).2 hw) fun a => (eig_push m hv a _).2 (he a)
    simpa only [comb_push m (hu τ) _ hv] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ i => ⟨(tan_push m (hu τ i)).2 (h1 τ i).1, fun a => (eig_push m (hu τ i) a _).2 ((h1 τ i).2 a)⟩,
      fun τ w hw he => ?_⟩
    have := h2 τ _ ((tan_push m hw.1).1 hw) fun a => (eig_push m hw.1 a _).1 (he a)
    simpa only [comb_push m (hu τ) _ hw.1] using this

include m in

/- English proof (translation)
Use `choose u' h1 h2 using fun τ i => exists_lift m (hu.1 τ i).1.1`. Use `⟨u', (frame_push m g u' h2).2 ?_⟩` and prove the remaining obligations. Rewrite using `[show (fun τ i => u' τ i ≫ m.φ : Vecs Dw t S) = u from funext fun τ => funext fun i => h1 τ i]`. Conclude with `hu`.
-/
theorem frame_lift {l : Level H} {c : Coeff l} (g : c.F →+* S) (u : Vecs Dw t S) (hu : IsFrame t g (x' ≫ f) u) :
    ∃ u' : Vecs Dw t' S, IsFrame t' g x' u' := by
  choose u' h1 h2 using fun τ i => exists_lift m (hu.1 τ i).1.1
  refine ⟨u', (frame_push m g u' h2).2 ?_⟩
  rw [show (fun τ i => u' τ i ≫ m.φ : Vecs Dw t S) = u from funext fun τ => funext fun i => h1 τ i]
  exact hu

end Push

section Generic

/- English proof (translation)
Establish `hp0 : (p : F) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hm : ((p : ℕ) : V) ∈ IsLocalRing.maximalIdeal V` using `ValuationSubring.coe_mem_nonunits_iff.1 (by simpa using hV)`. Establish `key : ∀ x : F, ∃ (k : ℕ) (a : V), x * (p : F) ^ k = a`. Introduce `x`. Establish `hx : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)`.

Take `⟨n, hn, hi⟩` from `hx.exists_integral_multiple`. Establish `hi' : IsIntegral ℤ ((n.natAbs : ℤ) • x)`. Break down `Int.natAbs_eq n with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `hi`.

Rewrite using `[show (n.natAbs : ℤ) = -n by omega, neg_smul]; exact hi.neg`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi'.tower_top`. Take `⟨e, n', hn', he⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hn) p hp.ne_one`. Establish `hu : IsUnit ((n' : ℕ) : V)`. Assume the negation of the conclusion as `h`.

Establish `h' : ((n' : ℕ) : V) ∈ IsLocalRing.maximalIdeal V` using `h`. Establish `hc : IsCoprime ((p : ℕ) : V) ((n' : ℕ) : V)` using `((Nat.Prime.coprime_iff_not_dvd hp).2 hn').cast`. Take `⟨a, b, hab⟩` from `hc`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ h')))`. Take `⟨w, hw⟩` from `hu.exists_left_inv`.

Establish `hw' : (w : F) * (n' : F) = 1` using `by simpa using congrArg (fun z : V => (z : F)) hw`. Use `⟨e, w * y, ?_⟩` and prove the remaining obligations. Establish `hy' : (y : F) = (p : F) ^ e * n' * x`. Rewrite using `[show (y : F) = algebraMap V F y from rfl, hy, he]`. Simplify using the standard rewrite rules.

Use `push_cast`. Rewrite using `[hy']`. Take the linear combination `(-(x * (p : F) ^ e)) * hw'`. Use `IsLocalization.Away.mk _ ?_ (fun s => ?_) fun a b h => ⟨0, by rw [Subtype.val_injective h]⟩` and prove the remaining obligations. Rewrite using `[map_natCast]`.

Conclude with `IsUnit.mk0 _ hp0`. Rewrite using `[map_natCast]`. Conclude with `key s`.
-/
theorem away_of_valuation (F : Type) [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (V : ValuationSubring F) (p : ℕ)
    (hp : p.Prime) (hV : (p : F) ∈ V.nonunits) : IsLocalization.Away ((p : ℕ) : V) F := by
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hm : ((p : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := ValuationSubring.coe_mem_nonunits_iff.1 (by simpa using hV)
  have key : ∀ x : F, ∃ (k : ℕ) (a : V), x * (p : F) ^ k = a := by
    intro x
    have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨n, hn, hi⟩ := hx.exists_integral_multiple
    have hi' : IsIntegral ℤ ((n.natAbs : ℤ) • x) := by
      rcases Int.natAbs_eq n with h | h
      · rw [← h]; exact hi
      · rw [show (n.natAbs : ℤ) = -n by omega, neg_smul]; exact hi.neg
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi'.tower_top
    obtain ⟨e, n', hn', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hn) p hp.ne_one
    have hu : IsUnit ((n' : ℕ) : V) := by
      by_contra h
      have h' : ((n' : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := h
      have hc : IsCoprime ((p : ℕ) : V) ((n' : ℕ) : V) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').cast
      obtain ⟨a, b, hab⟩ := hc
      exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ h')))
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hw' : (w : F) * (n' : F) = 1 := by simpa using congrArg (fun z : V => (z : F)) hw
    refine ⟨e, w * y, ?_⟩
    have hy' : (y : F) = (p : F) ^ e * n' * x := by
      rw [show (y : F) = algebraMap V F y from rfl, hy, he]; simp
    push_cast
    rw [hy']
    linear_combination (-(x * (p : F) ^ e)) * hw'
  refine IsLocalization.Away.mk _ ?_ (fun s => ?_) fun a b h => ⟨0, by rw [Subtype.val_injective h]⟩
  · rw [map_natCast]; exact IsUnit.mk0 _ hp0
  · rw [map_natCast]; exact key s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`.
-/
theorem j_s {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `hV : (p : c.F) ∈ (c.V W).nonunits`. Rewrite `hW`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`. Use `Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_` and prove the remaining obligations. Establish `h2 : c.F.val.toRingHom (p : c.F)⁻¹ ∈ W` using `h`.

Simplify using `using h2`. Use `away_of_valuation c.F (c.V W) p hp hV` as an intermediate fact. Establish `: IsOpenImmersion (spMap (c.V W).subtype)` using `IsOpenImmersion.of_isLocalization (S := c.F) ((p : ℕ) : c.V W)`. Use `Y.jQ_open` as an intermediate fact. Unfold `Model.j`.

Use `infer_instance`.
-/
theorem isOpenImmersion_j {p : ℕ} {W : ValuationSubring ℂ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  have := c.fin
  have hV : (p : c.F) ∈ (c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c.F.val.toRingHom (p : c.F)⁻¹ ∈ W := h
    simpa using h2
  have := away_of_valuation c.F (c.V W) p hp hV
  have : IsOpenImmersion (spMap (c.V W).subtype) := IsOpenImmersion.of_isLocalization (S := c.F) ((p : ℕ) : c.V W)
  have := Y.jQ_open
  unfold Model.j
  infer_instance

/- English proof (translation)
Use `Y.flat` as an intermediate fact. Establish `h1 : DenseRange (pullback.fst Y.s (spMap β))`. Introduce `x`. Set `q : Sp c.F` to `(⊥ : PrimeSpectrum c.F)`. Establish `hs : spMap β q ⤳ Y.s x`.

Use `(PrimeSpectrum.le_iff_specializes _ _).1 ?_` and prove the remaining obligations. Use `show Ideal.comap β ⊥ ≤ _`. Rewrite using `[Ideal.comap_bot_of_injective _ hβ]`. Conclude with `bot_le`. Take `⟨x', hx', e⟩` from `Flat.generalizingMap Y.s hs`.

Use `closure_mono ?_ (specializes_iff_mem_closure.1 hx')` and prove the remaining obligations. Rewrite using `[Set.singleton_subset_iff, Scheme.Pullback.range_fst]`. Conclude with `⟨q, e.symm⟩`. Use `h1.comp Y.jQ_dense (pullback.fst Y.s (spMap β)).continuous` as an intermediate fact. Use `this.mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨t, Scheme.Hom.comp_apply _ _ _⟩`.
-/
theorem dense_j {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β) (Y : Model Xo c β) :
    Dense (Set.range Y.j) := by
  have := Y.flat
  have h1 : DenseRange (pullback.fst Y.s (spMap β)) := by
    intro x
    let q : Sp c.F := (⊥ : PrimeSpectrum c.F)
    have hs : spMap β q ⤳ Y.s x := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      show Ideal.comap β ⊥ ≤ _
      rw [Ideal.comap_bot_of_injective _ hβ]
      exact bot_le
    obtain ⟨x', hx', e⟩ := Flat.generalizingMap Y.s hs
    refine closure_mono ?_ (specializes_iff_mem_closure.1 hx')
    rw [Set.singleton_subset_iff, Scheme.Pullback.range_fst]
    exact ⟨q, e.symm⟩
  have := h1.comp Y.jQ_dense (pullback.fst Y.s (spMap β)).continuous
  refine this.mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Scheme.Hom.comp_apply _ _ _⟩

/- English proof (translation)
Establish `h : IsFrame Xo.univ.t (algebraMap c.F S) y.x y.u` using `⟨fun τ i => ⟨y.tan τ i, y.eig τ i⟩, y.basis⟩`. Rewrite `h` using `[hy]`. Take `⟨u, hu⟩` from `frame_lift Y.m0.toSABMap _ _ h`. Conclude with `⟨_, (frame_push Y.m _ u fun τ i => (hu.1 τ i).1.1).1 hu⟩`.
-/
theorem exists_frame_of_frPt {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Type} [CommRing S]
    [Algebra c.F S] (jS : Sp S ⟶ Xo.XF c) (y : FrPt Xo c S) (hy : y.x = jS ≫ pullback.fst _ _) :
    ∃ u : Vecs Dw Y.t S, IsFrame Y.t (algebraMap c.F S) (jS ≫ Y.j) u := by
  have h : IsFrame Xo.univ.t (algebraMap c.F S) y.x y.u := ⟨fun τ i => ⟨y.tan τ i, y.eig τ i⟩, y.basis⟩
  rw [hy] at h
  obtain ⟨u, hu⟩ := frame_lift Y.m0.toSABMap _ _ h
  exact ⟨_, (frame_push Y.m _ u fun τ i => (hu.1 τ i).1.1).1 hu⟩

/- English proof (translation)
Establish `hU : IsAffineOpen g.opensRange` using `isAffineOpen_opensRange g`. Conclude with `⟨⟨_, hU⟩, rfl, (IsOpenImmersion.isoOfRangeEq hU.fromSpec g hU.range_fromSpec).hom, IsOpenImmersion.isoOfRangeEq_hom_fac hU.fromSpec g hU.range_fromSpec⟩`.
-/
theorem exists_affineOpen {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Sp R ⟶ Z) [IsOpenImmersion g] :
    ∃ U : Z.affineOpens, Set.range g = U.1 ∧ ∃ e : Sp Γ(Z, U.1) ⟶ Sp R, e ≫ g = U.2.fromSpec := by
  have hU : IsAffineOpen g.opensRange := isAffineOpen_opensRange g
  exact ⟨⟨_, hU⟩, rfl, (IsOpenImmersion.isoOfRangeEq hU.fromSpec g hU.range_fromSpec).hom,
    IsOpenImmersion.isoOfRangeEq_hom_fac hU.fromSpec g hU.range_fromSpec⟩

/- English proof (translation)
Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨R, jR, y₀, ⟨ho, hx, hs⟩, q, rfl⟩` from `GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c z`. Set `g : Sp R.R ⟶ Z` to `jR ≫ Y.j ≫ inv π`. Take `⟨U, hU, e, he⟩` from `exists_affineOpen g`. Set `ψ : R.R →+* Γ(Z, U.1)` to `(Spec.preimage e).hom`.

Establish `hψ : spMap ψ = e` using `Spec.map_preimage _`. Use `letI : Algebra c.F Γ(Z, U.1) := (ψ.comp (algebraMap c.F R.R)).toAlgebra`. Set `ψ' : R.R →ₐ[c.F] Γ(Z, U.1)` to `{ ψ with commutes' := fun _ => rfl }`. Take `⟨y, hy, -⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ ψ' y₀`. Establish `hj : (e ≫ jR) ≫ Y.j = U.2.fromSpec ≫ π`.

Rewrite using `[← he]`. Simplify using `[g]`. Take `⟨fr, hfr⟩` from `exists_frame_of_frPt Y (e ≫ jR) y (by rw [hy, ← hx, Category.assoc, ← hψ])`. Use `⟨U, algebraMap _ _, e ≫ jR, fr, hU.subset ⟨q, Scheme.Hom.comp_apply _ _ _⟩, hj, ?_, hj ▸ hfr⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hs, ← hψ]`.

Conclude with `(Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm`.
-/
theorem exists_chart {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) [IsOpenImmersion Y.j] {Z : Scheme.{0}}
    (π : Z ⟶ Y.X) [IsIso π] (z : Xo.XF c) :
    ∃ (U : Z.affineOpens) (alg : c.F →+* Γ(Z, U.1)) (jU : Sp Γ(Z, U.1) ⟶ Xo.XF c) (fr : Vecs Dw Y.t Γ(Z, U.1)),
      (Y.j ≫ inv π) z ∈ U.1 ∧ jU ≫ Y.j = U.2.fromSpec ≫ π ∧ jU ≫ pullback.snd _ _ = spMap alg ∧
      IsFrame Y.t alg (U.2.fromSpec ≫ π) fr := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨R, jR, y₀, ⟨ho, hx, hs⟩, q, rfl⟩ := GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c z
  let g : Sp R.R ⟶ Z := jR ≫ Y.j ≫ inv π
  obtain ⟨U, hU, e, he⟩ := exists_affineOpen g
  let ψ : R.R →+* Γ(Z, U.1) := (Spec.preimage e).hom
  have hψ : spMap ψ = e := Spec.map_preimage _
  letI : Algebra c.F Γ(Z, U.1) := (ψ.comp (algebraMap c.F R.R)).toAlgebra
  let ψ' : R.R →ₐ[c.F] Γ(Z, U.1) := { ψ with commutes' := fun _ => rfl }
  obtain ⟨y, hy, -⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ ψ' y₀
  have hj : (e ≫ jR) ≫ Y.j = U.2.fromSpec ≫ π := by
    rw [← he]; simp [g]
  obtain ⟨fr, hfr⟩ := exists_frame_of_frPt Y (e ≫ jR) y (by rw [hy, ← hx, Category.assoc, ← hψ])
  refine ⟨U, algebraMap _ _, e ≫ jR, fr, hU.subset ⟨q, Scheme.Hom.comp_apply _ _ _⟩, hj, ?_, hj ▸ hfr⟩
  rw [Category.assoc, hs, ← hψ]
  exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm

/- English proof (translation)
Introduce `z`. Take `⟨h1, h2⟩` from `h (π z)`. Set `e` to `(asIso (π.stalkMap z)).commRingCatIsoToRingEquiv`. Conclude with `⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩`.
-/
theorem normal_of_iso {X Z : Scheme.{0}} (π : Z ⟶ X) [IsIso π] (h : Geo.Tor.IsNormalScheme X) :
    Geo.Tor.IsNormalScheme Z := by
  intro z
  obtain ⟨h1, h2⟩ := h (π z)
  let e := (asIso (π.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

/- English proof (translation)
Take `⟨n, em, hem, hs⟩` from `(Y i).proj`. Establish `hj` using `isOpenImmersion_j hp hW (Y i)`. Set `π : em.ker.subscheme ⟶ (Y i).X` to `inv em.toImage`. Establish `hπ : IsIso π` using `inferInstanceAs (IsIso (inv em.toImage))`. Establish `hπs : π ≫ (Y i).s = em.ker.subschemeι ≫ PSpace.str _ n`.

Rewrite using `[← hs, ← Category.assoc]`. Conclude with `congrArg (· ≫ _) ((IsIso.inv_comp_eq em.toImage).2 em.toImage_imageι.symm)`. Use `choose U alg jU fr hU hjU halg hfr using exists_chart (Y i) π`. Establish `hr : Set.range ((Y i).j ≫ inv π) = π ⁻¹' Set.range (Y i).j`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z, by rw [← Scheme.Hom.comp_apply]; simp⟩`. Introduce and unpack `⟨z, hz⟩`. Conclude with `⟨z, by rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply]; simp⟩`.

Establish `hsub : ∀ z, ((U z).1 : Set em.ker.subscheme) ⊆ π ⁻¹' Set.range (Y i).j` using `fun z x hx => by`. Rewrite `hx` using `[← (U z).2.range_fromSpec]`. Take `⟨q, rfl⟩` from `hx`. Conclude with `⟨jU z q, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjU]⟩`. Establish `hn` using `normal_of_iso π (Y i).normal`.

Establish `hop : ∀ z, IsOpenImmersion (U z).2.fromSpec` using `fun z => IsAffineOpen.isOpenImmersion_fromSpec (U z).2`. Use `Formalism.L2.Pj.CompFin.isNoetherian_XF (Xo i.l) i.c` as an intermediate fact. Take `⟨T, hT⟩` from `(isCompact_range ((Y i).j ≫ inv π).continuous).elim_finite_subcover (fun z => ((U z).1 : Set em.ker.subscheme)) (fun z => (U z).1.isOpen) (by`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `Set.mem_iUnion.2 ⟨z, hU z⟩)`.

Set `e : Fin T.card → (Xo i.l).XF i.c` to `fun a => T.equivFin.symm a`. Set `P : Pre Y i₀` to `{ i := i, dvd := hd, le := hle, n := n, I := em.ker, π := π, ty := fun _ => ∅, m := T.card U := fun a => U (e a), alg := fun a => alg (e a), fr := fun a => fr (e a) }`. Establish `hcov : ⋃ a, ((U (e a)).1 : Set em.ker.subscheme) = π ⁻¹' Set.range (Y i).j`. Use `Set.Subset.antisymm (Set.iUnion_subset fun a => hsub _) fun x hx => ?_` and prove the remaining obligations. Take `⟨z, hz, hxz⟩` from `Set.mem_iUnion₂.1 (hT (hr ▸ hx))`.

Use `Set.mem_iUnion.2 ⟨T.equivFin ⟨z, hz⟩, ?_⟩` and prove the remaining obligations. Establish `: e (T.equivFin ⟨z, hz⟩) = z` using `congrArg Subtype.val (T.equivFin.symm_apply_apply ⟨z, hz⟩)`. Rewrite using `[this]`. Conclude with `hxz`. Use `⟨{ toPre := P, π_s := hπs, normal := ⟨fun x => (hn x).1, fun x => (hn x).2⟩, flat := ?_, dense := ?_, cover := hcov alg_s := fun a => ?_, smooth := fun a => ?_, frame := fun a => hfr (e a) glue := fun k _ a a' φ φ' _ τ k hk => absurd hk (Finset.notMem_empty _) bij := fun k _ f y …` and prove the remaining obligations.

Use `(Y i).flat show Flat (em.ker.subschemeι ≫ PSpace.str _ n)` as an intermediate fact. Rewrite using `[← hπs]`. Use `infer_instance`. Conclude with `(dense_j Subtype.val_injective (Y i)).preimage π.homeomorph.isOpenMap`. Use `show (U (e a)).2.fromSpec ≫ em.ker.subschemeι ≫ PSpace.str _ n = spMap ((alg (e a)).comp (i.c.V W).subtype)`.

Rewrite using `[← hπs, ← Category.assoc, ← hjU, Category.assoc, j_s, ← Category.assoc, halg]`. Conclude with `(Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm`. Conclude with `(inferInstance : Smooth ((U (e a)).2.fromSpec ≫ π))`. Establish `hw : (y ≫ (Y i).j ≫ inv π) ≫ π = y ≫ (Y i).j` using `by simp`. Use `⟨y ≫ (Y i).j ≫ inv π, ⟨hw, ?_⟩, fun w' h => ?_⟩` and prove the remaining obligations.

Set `q : Sp k` to `(⊥ : PrimeSpectrum k)`. Establish `hq : (y ≫ (Y i).j ≫ inv π) q ∈ π ⁻¹' Set.range (Y i).j` using `hr ▸ ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Take `⟨a, ha⟩` from `Set.mem_iUnion.1 (hcov ▸ hq)`. Establish `hle : Set.range (y ≫ (Y i).j ≫ inv π) ⊆ Set.range (U (e a)).2.fromSpec`. Introduce and unpack `_ ⟨q', rfl⟩`.

Rewrite using `[(U (e a)).2.range_fromSpec, Subsingleton.elim q' q]`. Conclude with `ha`. Set `g` to `IsOpenImmersion.lift (U (e a)).2.fromSpec _ hle`. Establish `hg : g ≫ (U (e a)).2.fromSpec = y ≫ (Y i).j ≫ inv π` using `IsOpenImmersion.lift_fac _ _ _`. Set `φ : Γ(em.ker.subscheme, (U (e a)).1) →+* k` to `(Spec.preimage g).hom`.

Establish `hφ : spMap φ = g` using `Spec.map_preimage _`. Establish `hy' : g ≫ jU (e a) = y`. Rewrite using `[← cancel_mono (Y i).j, Category.assoc, hjU, ← Category.assoc, hg, hw]`. Establish `hf : φ.comp (alg (e a)) = f`. Establish `h1 : spMap (φ.comp (alg (e a))) = spMap f`.

Rewrite using `[← hy, ← hy', Category.assoc, halg, ← hφ]`. Conclude with `Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Use `⟨a, φ, (congrArg (· ≫ _) hφ).trans hg, ?_, fun τ k hk => absurd hk (Finset.notMem_empty _)⟩` and prove the remaining obligations. Use `show IsFrame (Y i).t (φ.comp (alg (e a))) ((y ≫ (Y i).j ≫ inv π) ≫ π) u`.

Rewrite using `[hf, hw]`. Conclude with `hu`. Conclude with `(cancel_mono π).1 (h.1.trans hw.symm)`.
-/
theorem exists_mdl (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Y : LocalSystem Xo p W) (i₀ i : Idx H p)
    (hd : i₀.l.Dvd i.l) (hle : i₀.c.F ≤ i.c.F) :
    ∃ Z : Mdl Y i₀, Z.i = i ∧ IsIso Z.π ∧ ∀ σ, Z.ty σ = ∅ := by
  classical
  obtain ⟨n, em, hem, hs⟩ := (Y i).proj
  have hj := isOpenImmersion_j hp hW (Y i)
  let π : em.ker.subscheme ⟶ (Y i).X := inv em.toImage
  have hπ : IsIso π := inferInstanceAs (IsIso (inv em.toImage))
  have hπs : π ≫ (Y i).s = em.ker.subschemeι ≫ PSpace.str _ n := by
    rw [← hs, ← Category.assoc]
    exact congrArg (· ≫ _) ((IsIso.inv_comp_eq em.toImage).2 em.toImage_imageι.symm)
  choose U alg jU fr hU hjU halg hfr using exists_chart (Y i) π
  have hr : Set.range ((Y i).j ≫ inv π) = π ⁻¹' Set.range (Y i).j := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← Scheme.Hom.comp_apply]; simp⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply]; simp⟩
  have hsub : ∀ z, ((U z).1 : Set em.ker.subscheme) ⊆ π ⁻¹' Set.range (Y i).j := fun z x hx => by
    rw [← (U z).2.range_fromSpec] at hx
    obtain ⟨q, rfl⟩ := hx
    exact ⟨jU z q, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjU]⟩
  have hn := normal_of_iso π (Y i).normal
  have hop : ∀ z, IsOpenImmersion (U z).2.fromSpec := fun z => IsAffineOpen.isOpenImmersion_fromSpec (U z).2
  have := Formalism.L2.Pj.CompFin.isNoetherian_XF (Xo i.l) i.c
  obtain ⟨T, hT⟩ := (isCompact_range ((Y i).j ≫ inv π).continuous).elim_finite_subcover
    (fun z => ((U z).1 : Set em.ker.subscheme)) (fun z => (U z).1.isOpen) (by
      rintro _ ⟨z, rfl⟩
      exact Set.mem_iUnion.2 ⟨z, hU z⟩)
  let e : Fin T.card → (Xo i.l).XF i.c := fun a => T.equivFin.symm a
  let P : Pre Y i₀ :=
    { i := i, dvd := hd, le := hle, n := n, I := em.ker, π := π, ty := fun _ => ∅, m := T.card
      U := fun a => U (e a), alg := fun a => alg (e a), fr := fun a => fr (e a) }
  have hcov : ⋃ a, ((U (e a)).1 : Set em.ker.subscheme) = π ⁻¹' Set.range (Y i).j := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun a => hsub _) fun x hx => ?_
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (hT (hr ▸ hx))
    refine Set.mem_iUnion.2 ⟨T.equivFin ⟨z, hz⟩, ?_⟩
    have : e (T.equivFin ⟨z, hz⟩) = z := congrArg Subtype.val (T.equivFin.symm_apply_apply ⟨z, hz⟩)
    rw [this]; exact hxz
  refine ⟨{ toPre := P, π_s := hπs, normal := ⟨fun x => (hn x).1, fun x => (hn x).2⟩, flat := ?_, dense := ?_, cover := hcov
            alg_s := fun a => ?_, smooth := fun a => ?_, frame := fun a => hfr (e a)
            glue := fun k _ a a' φ φ' _ τ k hk => absurd hk (Finset.notMem_empty _)
            bij := fun k _ f y hy u hu => ?_ }, rfl, hπ, fun _ => rfl⟩
  · have := (Y i).flat
    show Flat (em.ker.subschemeι ≫ PSpace.str _ n)
    rw [← hπs]
    infer_instance
  · exact (dense_j Subtype.val_injective (Y i)).preimage π.homeomorph.isOpenMap
  · show (U (e a)).2.fromSpec ≫ em.ker.subschemeι ≫ PSpace.str _ n = spMap ((alg (e a)).comp (i.c.V W).subtype)
    rw [← hπs, ← Category.assoc, ← hjU, Category.assoc, j_s, ← Category.assoc, halg]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  · exact (inferInstance : Smooth ((U (e a)).2.fromSpec ≫ π))
  · have hw : (y ≫ (Y i).j ≫ inv π) ≫ π = y ≫ (Y i).j := by simp
    refine ⟨y ≫ (Y i).j ≫ inv π, ⟨hw, ?_⟩, fun w' h => ?_⟩
    · let q : Sp k := (⊥ : PrimeSpectrum k)
      have hq : (y ≫ (Y i).j ≫ inv π) q ∈ π ⁻¹' Set.range (Y i).j := hr ▸ ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (hcov ▸ hq)
      have hle : Set.range (y ≫ (Y i).j ≫ inv π) ⊆ Set.range (U (e a)).2.fromSpec := by
        rintro _ ⟨q', rfl⟩
        rw [(U (e a)).2.range_fromSpec, Subsingleton.elim q' q]
        exact ha
      let g := IsOpenImmersion.lift (U (e a)).2.fromSpec _ hle
      have hg : g ≫ (U (e a)).2.fromSpec = y ≫ (Y i).j ≫ inv π := IsOpenImmersion.lift_fac _ _ _
      let φ : Γ(em.ker.subscheme, (U (e a)).1) →+* k := (Spec.preimage g).hom
      have hφ : spMap φ = g := Spec.map_preimage _
      have hy' : g ≫ jU (e a) = y := by
        rw [← cancel_mono (Y i).j, Category.assoc, hjU, ← Category.assoc, hg, hw]
      have hf : φ.comp (alg (e a)) = f := by
        have h1 : spMap (φ.comp (alg (e a))) = spMap f := by
          rw [← hy, ← hy', Category.assoc, halg, ← hφ]
          exact Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      refine ⟨a, φ, (congrArg (· ≫ _) hφ).trans hg, ?_, fun τ k hk => absurd hk (Finset.notMem_empty _)⟩
      show IsFrame (Y i).t (φ.comp (alg (e a))) ((y ≫ (Y i).j ≫ inv π) ≫ π) u
      rw [hf, hw]
      exact hu
    · exact (cancel_mono π).1 (h.1.trans hw.symm)

/- English proof (translation)
Consider the cases of `b with`. Consider the case `none => exact ⟨i₀, ⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, rfl⟩`. Consider the case `some n`. Set `l : Level H` to `{ i₀.l with A := i₀.l.A * p ^ n, A_pos := Nat.mul_pos i₀.l.A_pos (pow_pos hp.pos n) }`. Establish `hz : zeta l.M' ∈ i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'}` using `(le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ _)`.

Establish `hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'}` using `fun τ a => (le_sup_left : i₀.c.F ≤ _) (i₀.c.conj τ a)`. Set `c : Coeff l` to `{ F := i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'} fin := by`. Use `i₀.c.fin` as an intermediate fact. Use `IntermediateField.adjoin.finiteDimensional (GlobalTheory.LevelExist.isIntegral_zeta (GlobalTheory.LevelExist.M'_pos l) : IsIntegral ℚ (zeta l.M'))` as an intermediate fact. Conclude with `IntermediateField.finiteDimensional_sup _ _`.

Use `conj := hc`. Use `zeta_mem := hz`. Use `le := (GlobalTheory.HostModel.coeff l).le.trans ((GlobalTheory.HostModel.coeff_F_le_iff l _).2 ⟨hz, hc⟩) }`. Conclude with `⟨⟨l, c, i₀.good⟩, ⟨dvd_rfl, le_rfl, dvd_mul_right _ _⟩, le_sup_left, rfl, rfl, rfl, rfl⟩`.
-/
theorem exists_idx (hp : p.Prime) (i₀ : Idx H p) (b : Option ℕ) :
    ∃ i : Idx H p, i₀.l.Dvd i.l ∧ i₀.c.F ≤ i.c.F ∧ IsLvl i₀ i b := by
  cases b with
  | none => exact ⟨i₀, ⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, rfl⟩
  | some n =>
    let l : Level H := { i₀.l with A := i₀.l.A * p ^ n, A_pos := Nat.mul_pos i₀.l.A_pos (pow_pos hp.pos n) }
    have hz : zeta l.M' ∈ i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'} :=
      (le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
    have hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'} := fun τ a =>
      (le_sup_left : i₀.c.F ≤ _) (i₀.c.conj τ a)
    let c : Coeff l :=
      { F := i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'}
        fin := by
          have := i₀.c.fin
          have := IntermediateField.adjoin.finiteDimensional
            (GlobalTheory.LevelExist.isIntegral_zeta (GlobalTheory.LevelExist.M'_pos l) : IsIntegral ℚ (zeta l.M'))
          exact IntermediateField.finiteDimensional_sup _ _
        conj := hc
        zeta_mem := hz
        le := (GlobalTheory.HostModel.coeff l).le.trans ((GlobalTheory.HostModel.coeff_F_le_iff l _).2 ⟨hz, hc⟩) }
    exact ⟨⟨l, c, i₀.good⟩, ⟨dvd_rfl, le_rfl, dvd_mul_right _ _⟩, le_sup_left, rfl, rfl, rfl, rfl⟩

end GlobalTheory.LocM.BaseMdl

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W hp hW Y i₀ _`. Use `choose i hd hle hl using GlobalTheory.LocM.BaseMdl.exists_idx hp i₀`. Use `choose Z hi hiso hty using fun b => GlobalTheory.LocM.BaseMdl.exists_mdl hp hW Y i₀ (i b) (hd b) (hle b)`. Conclude with `⟨⟨Z, fun b => (hi b).symm ▸ hl b, hiso, hty⟩⟩`.
-/
theorem GlobalTheory.LocM.exists_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p),
    1 ≤ Dw.p + Dw.q → Nonempty (GlobalTheory.LocM.Bases Y i₀) := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ _
  choose i hd hle hl using GlobalTheory.LocM.BaseMdl.exists_idx hp i₀
  choose Z hi hiso hty using fun b => GlobalTheory.LocM.BaseMdl.exists_mdl hp hW Y i₀ (i b) (hd b) (hle b)
  exact ⟨⟨Z, fun b => (hi b).symm ▸ hl b, hiso, hty⟩⟩
