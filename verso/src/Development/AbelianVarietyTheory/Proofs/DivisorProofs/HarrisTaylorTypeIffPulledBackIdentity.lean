import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

/- English proof (translation)
Establish `hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w]`. Both sides reduce to the same expression. Set `x₀ : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) hw`. Establish `e` using `h.2 T 1 1 x₀ x₀ rfl rfl`.

Rewrite `e` using `[_root_.mul_one]`. Establish `hxx : x₀ * x₀ = x₀`. Use `ext`. Conclude with `e`. Establish `h1 : x₀ = 1` using `mul_eq_right.mp hxx`.

Conclude with `congrArg Over.Hom.left h1`.
-/
theorem tjAt_pull_one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

/- English proof (translation)
Introduce `p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ r w j hB hψ`. Establish `key : ∀ (k : Type) [Field k] (σ : Sp k ⟶ T), ((∀ g : Over.mk (σ ≫ t) ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧ Nat.card {g : Over.mk (σ ≫ t) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)) ↔ ((∀ g : Over.mk σ ⟶ o₁.A, g ≫ ψ …`. Introduce `k _ σ`. Take `⟨e, he, -⟩` from `m.exists_ptEquiv (Over.mk (σ ≫ t)) σ rfl`. Establish `hker : ∀ g : Over.mk σ ⟶ o₁.A, e g ≫ ψ = 1 ↔ g ≫ ψ₁ = 1`.

Introduce `g`. Establish `h1 : (e g ≫ ψ).left = (g ≫ ψ₁).left ≫ θ`. Rewrite using `[Over.comp_left, he, Category.assoc, hψ, Over.comp_left, Category.assoc]`. Establish `h2 : (1 : Over.mk (σ ≫ t) ⟶ B).left = (1 : Over.mk σ ⟶ B₁).left ≫ θ` using `(tjAt_pull_one_left hB (Over.mk σ)).symm`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hB.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← h1, ← h2, h]`. Rewrite using `[Over.w, Over.w]`.

Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[h1, h2, h]`. Establish `hact : ∀ (g : Over.mk σ ⟶ o₁.A) (c : D.O), e g ≫ o.act.act c = e (g ≫ o₁.act.act c)` using `fun g c => by`. Use `ext`.

Rewrite using `[Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]`. Establish `hkill : ∀ (v : Ideal (𝓞 D.F)) (g : Over.mk σ ⟶ o₁.A), KilledBy o v (e g) ↔ KilledBy o₁ v g` using `fun v g => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective`. Use `and_congr ⟨fun h g hg hu => ?_, fun h g hg hu => ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[← hkill]`. Rewrite `hg` using `[← hker]`.

Take `⟨n, hn⟩` from `hu`. Conclude with `h (e g) hg ⟨n, (hkill _ g).2 hn⟩`. Take `⟨g₀, rfl⟩` from `e.surjective g`. Rewrite using `[hkill]`. Rewrite `hg` using `[hker]`.

Take `⟨n, hn⟩` from `hu`. Conclude with `h g₀ hg ⟨n, (hkill _ g₀).1 hn⟩`. Rewrite using `[Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by`. Express the relevant statement in the definitionally equal form `_ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)`. Rewrite using `[hker, hkill]).symm)]`.

Prove the components needed by the constructor for the conclusion. Introduce `h k _ _ _ x₁ _`. Conclude with `(key k x₁).1 (h k (x₁ ≫ t) ⟨x₁, rfl⟩)`. Introduce `h k _ _ _ x ⟨σ, hσ⟩`. Substitute `hσ` using the available equality.

Conclude with `(key k σ).2 (h k σ ⟨σ, Category.comp_id σ⟩)`.
-/
theorem tjAt_iff_tjAt_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ r w j hB hψ
  have key : ∀ (k : Type) [Field k] (σ : Sp k ⟶ T),
      ((∀ g : Over.mk (σ ≫ t) ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
        Nat.card {g : Over.mk (σ ≫ t) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)) ↔
      ((∀ g : Over.mk σ ⟶ o₁.A, g ≫ ψ₁ = 1 → (∃ e : ℕ, KilledBy o₁ (uIdeal D r ^ e) g) → KilledBy o₁ w g) ∧
        Nat.card {g : Over.mk σ ⟶ o₁.A // g ≫ ψ₁ = 1 ∧ KilledBy o₁ w g} = Ideal.absNorm w ^ (D.m * j)) := by
    intro k _ σ
    obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk (σ ≫ t)) σ rfl
    have hker : ∀ g : Over.mk σ ⟶ o₁.A, e g ≫ ψ = 1 ↔ g ≫ ψ₁ = 1 := by
      intro g
      have h1 : (e g ≫ ψ).left = (g ≫ ψ₁).left ≫ θ := by
        rw [Over.comp_left, he, Category.assoc, hψ, Over.comp_left, Category.assoc]
      have h2 : (1 : Over.mk (σ ≫ t) ⟶ B).left = (1 : Over.mk σ ⟶ B₁).left ≫ θ :=
        (tjAt_pull_one_left hB (Over.mk σ)).symm
      constructor
      · intro h
        apply Over.OverMorphism.ext
        apply hB.1.hom_ext
        · rw [← h1, ← h2, h]
        · rw [Over.w, Over.w]
      · intro h
        apply Over.OverMorphism.ext
        rw [h1, h2, h]
    have hact : ∀ (g : Over.mk σ ⟶ o₁.A) (c : D.O), e g ≫ o.act.act c = e (g ≫ o₁.act.act c) := fun g c => by
      ext
      rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
    have hkill : ∀ (v : Ideal (𝓞 D.F)) (g : Over.mk σ ⟶ o₁.A), KilledBy o v (e g) ↔ KilledBy o₁ v g :=
      fun v g => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
    refine and_congr ⟨fun h g hg hu => ?_, fun h g hg hu => ?_⟩ ?_
    · rw [← hkill]
      rw [← hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h (e g) hg ⟨n, (hkill _ g).2 hn⟩
    · obtain ⟨g₀, rfl⟩ := e.surjective g
      rw [hkill]
      rw [hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
    · rw [Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
        change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
        rw [hker, hkill]).symm)]
  constructor
  · intro h k _ _ _ x₁ _
    exact (key k x₁).1 (h k (x₁ ≫ t) ⟨x₁, rfl⟩)
  · intro h k _ _ _ x ⟨σ, hσ⟩
    subst hσ
    exact (key k σ).2 (h k σ ⟨σ, Category.comp_id σ⟩)

end GlobalTheory.UPel.HT.ES
