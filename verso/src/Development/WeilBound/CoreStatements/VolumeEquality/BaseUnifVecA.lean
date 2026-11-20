import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefsB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove GlobalTheory.VerticalDeriv GlobalTheory.FibreDeriv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}
  {f : X' ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : RiemLat E g Λ}

/- English proof (translation)
Substitute `hz` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩`. Take `⟨w, hw, -⟩` from `m.lin`. Take `⟨v₁, hv₁⟩` from `lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw⟩ φ`.

Establish `h₁` using `pull_isLB t'.PP.isLB φ`. Establish `h₂` using `pull_isLB t.PP.isLB (φ ≫ m.cm.F)`. Use `⟨A, inferInstance, φ ≫ m.cm.F, GlobalTheory.ArchMetricCompare.carry u h₁ h₂ hv₁, χ, hpb.comp m.cart, GlobalTheory.ArchMetricCompare.carry_isAH h₁ h₂ hv₁ hAH, fun a p => ?_, hinj, hmem, fun i => ?_⟩` and prove the remaining obligations. Use `show (u.ex (R.B a p)).left ≫ φ ≫ m.cm.F = (u.ex p).left ≫ (φ ≫ m.cm.F) ≫ (t.act.act a).left`. Rewrite using `[← Category.assoc, hact a p, Category.assoc, Category.assoc, Category.assoc, m.act a]`.

Take `⟨w₁, e₁, d₁⟩` from `hvec i`. Conclude with `⟨w₁, by rw [← Category.assoc, e₁]; exact hv i, d₁⟩`. Introduce and unpack `⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩`. Establish `hp` using `m.cart.1`. Take `⟨F, rfl, hw⟩ : ∃ F : A.left ⟶ t'.G.left, F ≫ m.cm.F = φ ∧ F ≫ t'.G.hom = A.hom ≫ z` from `⟨hp.lift φ (A.hom ≫ z) (by rw [hpb.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩`.

Take `⟨w, hw', -⟩` from `m.lin`. Take `⟨v₁, hv₁⟩` from `(lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw'⟩ F).symm`. Establish `h₁` using `pull_isLB t'.PP.isLB F`. Establish `h₂` using `pull_isLB t.PP.isLB (F ≫ m.cm.F)`. Use `⟨A, inferInstance, F, GlobalTheory.ArchMetricCompare.carry u h₂ h₁ hv₁, χ, m.cart.cancel hpb hw, GlobalTheory.ArchMetricCompare.carry_isAH h₂ h₁ hv₁ hAH, fun a p => ?_, hinj, hmem, fun i => ?_⟩` and prove the remaining obligations.

Use `show (u.ex (R.B a p)).left ≫ F = (u.ex p).left ≫ F ≫ (t'.act.act a).left`. Apply `hp.hom_ext` to reduce the goal to its premises. Establish `e` using `hact a p`. Simplify using `only [Category.assoc] at e ⊢`. Rewrite using `[m.act a]`.

Conclude with `e`. Simplify using `only [Category.assoc]`. Rewrite using `[Over.w (t'.act.act a), hw, ← Category.assoc, ← Category.assoc, Over.w (u.ex _), Over.w (u.ex _)]`. Take `⟨w₁, e₁, d₁⟩` from `hvec i`. Use `⟨w₁, hp.hom_ext ?_ ?_, d₁⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, e₁]`. Conclude with `(hv i).symm`. Rewrite using `[Category.assoc, hw, ← Category.assoc, Over.w w₁, Over.w (v' i)]`. Both sides reduce to the same expression.
-/
theorem fibreLatVec_move (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ f = z₀) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v' : A₀ → (epsAt z ⟶ t'.G)) (v : A₀ → (epsAt z₀ ⟶ t.G)) (hv : ∀ i, (v' i).left ≫ m.φ = (v i).left) :
    FibreLatVec t' z R x v' ↔ FibreLatVec t z₀ R x v := by
  subst hz
  constructor
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩
    obtain ⟨w, hw, -⟩ := m.lin
    obtain ⟨v₁, hv₁⟩ := lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw⟩ φ
    have h₁ := pull_isLB t'.PP.isLB φ
    have h₂ := pull_isLB t.PP.isLB (φ ≫ m.cm.F)
    refine ⟨A, inferInstance, φ ≫ m.cm.F, GlobalTheory.ArchMetricCompare.carry u h₁ h₂ hv₁, χ, hpb.comp m.cart,
      GlobalTheory.ArchMetricCompare.carry_isAH h₁ h₂ hv₁ hAH, fun a p => ?_, hinj, hmem, fun i => ?_⟩
    · show (u.ex (R.B a p)).left ≫ φ ≫ m.cm.F = (u.ex p).left ≫ (φ ≫ m.cm.F) ≫ (t.act.act a).left
      rw [← Category.assoc, hact a p, Category.assoc, Category.assoc, Category.assoc, m.act a]
    · obtain ⟨w₁, e₁, d₁⟩ := hvec i
      exact ⟨w₁, by rw [← Category.assoc, e₁]; exact hv i, d₁⟩
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩
    have hp := m.cart.1
    obtain ⟨F, rfl, hw⟩ : ∃ F : A.left ⟶ t'.G.left, F ≫ m.cm.F = φ ∧ F ≫ t'.G.hom = A.hom ≫ z :=
      ⟨hp.lift φ (A.hom ≫ z) (by rw [hpb.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    obtain ⟨w, hw', -⟩ := m.lin
    obtain ⟨v₁, hv₁⟩ := (lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw'⟩ F).symm
    have h₁ := pull_isLB t'.PP.isLB F
    have h₂ := pull_isLB t.PP.isLB (F ≫ m.cm.F)
    refine ⟨A, inferInstance, F, GlobalTheory.ArchMetricCompare.carry u h₂ h₁ hv₁, χ, m.cart.cancel hpb hw,
      GlobalTheory.ArchMetricCompare.carry_isAH h₂ h₁ hv₁ hAH, fun a p => ?_, hinj, hmem, fun i => ?_⟩
    · show (u.ex (R.B a p)).left ≫ F = (u.ex p).left ≫ F ≫ (t'.act.act a).left
      apply hp.hom_ext
      · have e := hact a p
        simp only [Category.assoc] at e ⊢
        rw [m.act a]
        exact e
      · simp only [Category.assoc]
        rw [Over.w (t'.act.act a), hw, ← Category.assoc, ← Category.assoc, Over.w (u.ex _), Over.w (u.ex _)]
    · obtain ⟨w₁, e₁, d₁⟩ := hvec i
      refine ⟨w₁, hp.hom_ext ?_ ?_, d₁⟩
      · rw [Category.assoc, e₁]
        exact (hv i).symm
      · rw [Category.assoc, hw, ← Category.assoc, Over.w w₁, Over.w (v' i)]
        rfl

structure GoodExp (t : SAB H X) (z : Sp ℂ ⟶ X) (R : RiemLat E g Λ) (h : (Fin g → ℂ) → Fin g → ℂ)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)) : Prop where
  hol : IsHolTo Set.univ e
  vert : ∀ ζ, e ζ ≫ t.G.hom = z
  zero : e 0 = (1 : Over.mk z ⟶ t.G).left
  uniq : ∀ w₁ w₂ u, IsDerivAt0 e w₁ u → IsDerivAt0 e w₂ u → w₁ = w₂
  onto : ∀ u : Sp (DualNumber ℂ) ⟶ t.G.left, u ≫ t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z →
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ u = e 0 → ∃ w, IsDerivAt0 e w u
  lat : ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), (∀ a, IsDerivAt0 e (h (x a)) (v a).left) →
    FibreLatVec t z R x v

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.
-/
theorem fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

variable {h : (Fin g → ℂ) → Fin g → ℂ}

/- English proof (translation)
Establish `hp` using `m.cart.1`. Establish `key : ∀ w u, IsDerivAt0 (fun ζ => e' ζ ≫ m.φ) w u → ∃ u', IsDerivAt0 e' w u' ∧ u' ≫ m.φ = u ∧ u' ≫ t'.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z` using `fun w u hu => by`. Take `⟨u', hu'⟩` from `exists_isDerivAt0 G.hol w`. Conclude with `⟨u', hu', isDerivAt0_unique (isDerivAt0_comp hu' m.φ) hu, isDerivAt0_vertical _ _ G.vert hu'⟩`. Use `⟨GlobalTheory.HolTorsion.isHolTo_comp G.hol _, fun ζ => ?_, ?_, fun w₁ w₂ u h₁ h₂ => ?_, fun u hu h0 => ?_, fun A₀ x v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hp.w, ← Category.assoc, G.vert, hz]`. Substitute `hz` using the available equality. Rewrite using `[G.zero]`. Conclude with `LiePull.one_left m.cart z`. Take `⟨u₁, a₁, b₁, c₁⟩` from `key _ _ h₁`.

Take `⟨u₂, a₂, b₂, c₂⟩` from `key _ _ h₂`. Establish `: u₁ = u₂` using `hp.hom_ext (b₁.trans b₂.symm) (c₁.trans c₂.symm)`. Substitute `this` using the available equality. Conclude with `G.uniq _ _ _ a₁ a₂`. Establish `hc : u ≫ t.G.hom = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z) ≫ f` using `by rw [hu, Category.assoc, hz]`.

Take `⟨w, hw⟩` from `G.onto (hp.lift u _ hc) (hp.lift_snd _ _ _) (hp.hom_ext (by rw [Category.assoc, hp.lift_fst]; exact h0) (by rw [Category.assoc, hp.lift_snd, ← Category.assoc, fst_alg, Category.id_comp, G.vert]))`. Use `isDerivAt0_comp hw m.φ` as an intermediate fact. Rewrite `this` using `[show hp.lift u _ hc ≫ m.φ = u from hp.lift_fst _ _ _]`. Conclude with `⟨w, this⟩`. Use `choose u' a b c using fun a => key _ _ (hv a)`.

Set `v' : A₀ → (epsAt z ⟶ t'.G)` to `fun a => Over.homMk (u' a) (c a)`. Conclude with `(fibreLatVec_move m hz x v' v b).1 (G.lat A₀ x v' a)`.
-/
theorem GoodExp.push (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ f = z₀)
    {e' : (Fin g → ℂ) → (Sp ℂ ⟶ t'.G.left)} (G : GoodExp t' z R h e') : GoodExp t z₀ R h fun ζ => e' ζ ≫ m.φ := by
  have hp := m.cart.1
  have key : ∀ w u, IsDerivAt0 (fun ζ => e' ζ ≫ m.φ) w u → ∃ u', IsDerivAt0 e' w u' ∧ u' ≫ m.φ = u ∧
      u' ≫ t'.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z := fun w u hu => by
    obtain ⟨u', hu'⟩ := exists_isDerivAt0 G.hol w
    exact ⟨u', hu', isDerivAt0_unique (isDerivAt0_comp hu' m.φ) hu, isDerivAt0_vertical _ _ G.vert hu'⟩
  refine ⟨GlobalTheory.HolTorsion.isHolTo_comp G.hol _, fun ζ => ?_, ?_, fun w₁ w₂ u h₁ h₂ => ?_, fun u hu h0 => ?_,
    fun A₀ x v hv => ?_⟩
  · rw [Category.assoc, hp.w, ← Category.assoc, G.vert, hz]
  · subst hz
    rw [G.zero]
    exact LiePull.one_left m.cart z
  · obtain ⟨u₁, a₁, b₁, c₁⟩ := key _ _ h₁
    obtain ⟨u₂, a₂, b₂, c₂⟩ := key _ _ h₂
    have : u₁ = u₂ := hp.hom_ext (b₁.trans b₂.symm) (c₁.trans c₂.symm)
    subst this
    exact G.uniq _ _ _ a₁ a₂
  · have hc : u ≫ t.G.hom = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z) ≫ f := by rw [hu, Category.assoc, hz]
    obtain ⟨w, hw⟩ := G.onto (hp.lift u _ hc) (hp.lift_snd _ _ _) (hp.hom_ext
      (by rw [Category.assoc, hp.lift_fst]; exact h0)
      (by rw [Category.assoc, hp.lift_snd, ← Category.assoc, fst_alg, Category.id_comp, G.vert]))
    have := isDerivAt0_comp hw m.φ
    rw [show hp.lift u _ hc ≫ m.φ = u from hp.lift_fst _ _ _] at this
    exact ⟨w, this⟩
  · choose u' a b c using fun a => key _ _ (hv a)
    let v' : A₀ → (epsAt z ⟶ t'.G) := fun a => Over.homMk (u' a) (c a)
    exact (fibreLatVec_move m hz x v' v b).1 (G.lat A₀ x v' a)

/- English proof (translation)
Establish `hp` using `m.cart.1`. Establish `he : (fun ζ => e' ζ ≫ m.φ) = e` using `funext h₁`. Establish `key : ∀ w u, IsDerivAt0 e' w u → IsDerivAt0 e w (u ≫ m.φ)` using `fun w u hu => he ▸ isDerivAt0_comp hu m.φ`. Use `⟨hol, h₂, ?_, fun w₁ w₂ u a₁ a₂ => G.uniq _ _ _ (key _ _ a₁) (key _ _ a₂), fun u hu h0 => ?_, fun A₀ x v hv => ?_⟩` and prove the remaining obligations. Substitute `hz` using the available equality.

Use `hp.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[h₁, G.zero]`. Conclude with `(LiePull.one_left m.cart z).symm`. Rewrite using `[h₂, Over.w]`. Both sides reduce to the same expression.

Take `⟨w, hw⟩` from `G.onto (u ≫ m.φ) (by rw [Category.assoc, hp.w, ← Category.assoc, hu, Category.assoc, hz]) (by rw [← Category.assoc, h0, h₁])`. Take `⟨u', hu'⟩` from `exists_isDerivAt0 hol w`. Establish `: u' = u` using `hp.hom_ext (isDerivAt0_unique (key _ _ hu') hw) ((isDerivAt0_vertical _ _ h₂ hu').trans hu.symm)`. Conclude with `⟨w, this ▸ hu'⟩`. Set `v₀ : A₀ → (epsAt z₀ ⟶ t.G)` to `fun a => Over.homMk ((v a).left ≫ m.φ) (by`.

Rewrite using `[Category.assoc, hp.w, ← Category.assoc, Over.w (v a), ← hz]`. Conclude with `Category.assoc _ _ _)`. Conclude with `(fibreLatVec_move m hz x v v₀ fun _ => rfl).2 (G.lat A₀ x v₀ fun a => key _ _ (hv a))`.
-/
theorem GoodExp.pull (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ f = z₀)
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (G : GoodExp t z₀ R h e) {e' : (Fin g → ℂ) → (Sp ℂ ⟶ t'.G.left)}
    (hol : IsHolTo Set.univ e') (h₁ : ∀ ζ, e' ζ ≫ m.φ = e ζ) (h₂ : ∀ ζ, e' ζ ≫ t'.G.hom = z) : GoodExp t' z R h e' := by
  have hp := m.cart.1
  have he : (fun ζ => e' ζ ≫ m.φ) = e := funext h₁
  have key : ∀ w u, IsDerivAt0 e' w u → IsDerivAt0 e w (u ≫ m.φ) := fun w u hu => he ▸ isDerivAt0_comp hu m.φ
  refine ⟨hol, h₂, ?_, fun w₁ w₂ u a₁ a₂ => G.uniq _ _ _ (key _ _ a₁) (key _ _ a₂), fun u hu h0 => ?_, fun A₀ x v hv => ?_⟩
  · subst hz
    refine hp.hom_ext ?_ ?_
    · rw [h₁, G.zero]
      exact (LiePull.one_left m.cart z).symm
    · rw [h₂, Over.w]
      rfl
  · obtain ⟨w, hw⟩ := G.onto (u ≫ m.φ) (by rw [Category.assoc, hp.w, ← Category.assoc, hu, Category.assoc, hz])
      (by rw [← Category.assoc, h0, h₁])
    obtain ⟨u', hu'⟩ := exists_isDerivAt0 hol w
    have : u' = u := hp.hom_ext (isDerivAt0_unique (key _ _ hu') hw) ((isDerivAt0_vertical _ _ h₂ hu').trans hu.symm)
    exact ⟨w, this ▸ hu'⟩
  · let v₀ : A₀ → (epsAt z₀ ⟶ t.G) := fun a => Over.homMk ((v a).left ≫ m.φ) (by
      rw [Category.assoc, hp.w, ← Category.assoc, Over.w (v a), ← hz]
      exact Category.assoc _ _ _)
    exact (fibreLatVec_move m hz x v v₀ fun _ => rfl).2 (G.lat A₀ x v₀ fun a => key _ _ (hv a))

end SheetDecomposition
