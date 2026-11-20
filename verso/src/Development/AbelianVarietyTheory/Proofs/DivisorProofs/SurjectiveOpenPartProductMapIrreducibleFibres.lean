import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Use `⟨Over.homMk (IsOpenImmersion.lift e.left f.left h) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w e, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w f]`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem exists_over_lift_of_range_subset {T : Scheme.{0}} {Z H V : Over T} (e : V ⟶ H) [IsOpenImmersion e.left]
    (f : Z ⟶ H) (h : Set.range f.left ⊆ Set.range e.left) : ∃ a : Z ⟶ V, a ≫ e = f := by
  refine ⟨Over.homMk (IsOpenImmersion.lift e.left f.left h) ?_, ?_⟩
  · rw [← Over.w e, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w f]
  · ext
    simp

/- English proof (translation)
Introduce `T H V _ e he hV hirr`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Set `t : Spec (CommRingCat.of (H.left.residueField x)) ⟶ T` to `H.left.fromSpecResidueField x ≫ H.hom`. Set `g : Over.mk t ⟶ H` to `Over.homMk (H.left.fromSpecResidueField x) rfl`. Establish `hI` using `hirr (H.left.residueField x) t`.

Set `X : Over T` to `Over.mk (pullback.snd H.hom t ≫ t)`. Set `p : X ⟶ H` to `Over.homMk (pullback.fst H.hom t) pullback.condition`. Set `c : X ⟶ Over.mk t` to `Over.homMk (pullback.snd H.hom t) rfl`. Set `φ : X ⟶ H` to `(c ≫ g) * p⁻¹`. Set `Y : Over T` to `Over.mk (pullback.snd V.hom t ≫ t)`.

Set `q : Y ⟶ V` to `Over.homMk (pullback.fst V.hom t) pullback.condition`. Set `d : Y ⟶ Over.mk t` to `Over.homMk (pullback.snd V.hom t) rfl`. Establish `hl : ∀ h : Y ⟶ H, ∃ l : Y ⟶ X, l ≫ p = h ∧ l ≫ c = d`. Introduce `h`. Use `⟨Over.homMk (pullback.lift h.left (pullback.snd V.hom t) (Over.w h)) ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `pullback.lift_snd_assoc _ _ _ _`. Use `ext`. Conclude with `pullback.lift_fst _ _ _`. Use `ext`. Conclude with `pullback.lift_snd _ _ _`.

Establish `hY : Nonempty Y.left`. Establish `: Surjective (pullback.snd V.hom t)` using `inferInstance`. Take `⟨y, -⟩` from `(pullback.snd V.hom t).surjective (closedPoint _)`. Conclude with `⟨y⟩`. Take `⟨y⟩` from `hY`.

Establish `hopen : IsOpen (Set.range e.left)` using `e.left.isOpenEmbedding.isOpen_range`. Establish `hne : ∀ (l : Y ⟶ X) (ψ : X ⟶ H), l ≫ ψ = q ≫ e → (ψ.left ⁻¹' Set.range e.left).Nonempty`. Introduce `l ψ h`. Use `⟨l.left y, q.left y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(q ≫ e).left y = (l ≫ ψ).left y`.

Rewrite using `[h]`. Establish `h1 : (p.left ⁻¹' Set.range e.left).Nonempty`. Take `⟨l, hlp, -⟩` from `hl (q ≫ e)`. Conclude with `hne l p hlp`. Establish `h2 : (φ.left ⁻¹' Set.range e.left).Nonempty`.

Take `⟨l, hlp, hlc⟩` from `hl ((q ≫ e)⁻¹ * (d ≫ g))`. Use `hne l φ ?_` and prove the remaining obligations. Simplify using `only [φ]`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hlp, ← Category.assoc, hlc]`. Use `group`.

Establish `hI' : IrreducibleSpace X.left` using `hI`. Establish `ho1 : IsOpen (p.left ⁻¹' Set.range e.left)` using `hopen.preimage p.left.continuous`. Establish `ho2 : IsOpen (φ.left ⁻¹' Set.range e.left)` using `hopen.preimage φ.left.continuous`. Take `⟨z, hz1, hz2⟩` from `nonempty_preirreducible_inter ho1 ho2 h1 h2`. Set `U : X.left.Opens` to `⟨_, ho1.inter ho2⟩`.

Set `Z : Over T` to `Over.mk (U.ι ≫ X.hom)`. Set `j : Z ⟶ X` to `Over.homMk U.ι rfl`. Take `⟨a, ha⟩` from `exists_over_lift_of_range_subset e (j ≫ φ) (by`. Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `u.2.2)`.

Take `⟨b, hb⟩` from `exists_over_lift_of_range_subset e (j ≫ p) (by`. Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `u.2.1)`. Establish `key : lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e)) = j ≫ c ≫ g`. Rewrite using `[MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, hb, ← MonObj.comp_mul]`.

Simplify using `only [φ, inv_mul_cancel_right]`. Set `u : Z.left` to `(⟨z, hz1, hz2⟩ : U)`. Use `⟨(lift a b).left u, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e))).left u = x`. Rewrite using `[key]`.

Conclude with `H.left.fromSpecResidueField_apply x _`.
-/
theorem surjective_mul_of_open_of_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hV hirr
  refine ⟨fun x => ?_⟩
  let t : Spec (CommRingCat.of (H.left.residueField x)) ⟶ T := H.left.fromSpecResidueField x ≫ H.hom
  let g : Over.mk t ⟶ H := Over.homMk (H.left.fromSpecResidueField x) rfl
  have hI := hirr (H.left.residueField x) t
  let X : Over T := Over.mk (pullback.snd H.hom t ≫ t)
  let p : X ⟶ H := Over.homMk (pullback.fst H.hom t) pullback.condition
  let c : X ⟶ Over.mk t := Over.homMk (pullback.snd H.hom t) rfl
  let φ : X ⟶ H := (c ≫ g) * p⁻¹
  let Y : Over T := Over.mk (pullback.snd V.hom t ≫ t)
  let q : Y ⟶ V := Over.homMk (pullback.fst V.hom t) pullback.condition
  let d : Y ⟶ Over.mk t := Over.homMk (pullback.snd V.hom t) rfl
  have hl : ∀ h : Y ⟶ H, ∃ l : Y ⟶ X, l ≫ p = h ∧ l ≫ c = d := by
    intro h
    refine ⟨Over.homMk (pullback.lift h.left (pullback.snd V.hom t) (Over.w h)) ?_, ?_, ?_⟩
    · exact pullback.lift_snd_assoc _ _ _ _
    · ext; exact pullback.lift_fst _ _ _
    · ext; exact pullback.lift_snd _ _ _
  have hY : Nonempty Y.left := by
    have : Surjective (pullback.snd V.hom t) := inferInstance
    obtain ⟨y, -⟩ := (pullback.snd V.hom t).surjective (closedPoint _)
    exact ⟨y⟩
  obtain ⟨y⟩ := hY
  have hopen : IsOpen (Set.range e.left) := e.left.isOpenEmbedding.isOpen_range
  have hne : ∀ (l : Y ⟶ X) (ψ : X ⟶ H), l ≫ ψ = q ≫ e → (ψ.left ⁻¹' Set.range e.left).Nonempty := by
    intro l ψ h
    refine ⟨l.left y, q.left y, ?_⟩
    change (q ≫ e).left y = (l ≫ ψ).left y
    rw [h]
  have h1 : (p.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, -⟩ := hl (q ≫ e)
    exact hne l p hlp
  have h2 : (φ.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, hlc⟩ := hl ((q ≫ e)⁻¹ * (d ≫ g))
    refine hne l φ ?_
    simp only [φ]
    rw [MonObj.comp_mul, GrpObj.comp_inv, hlp, ← Category.assoc, hlc]
    group
  have hI' : IrreducibleSpace X.left := hI
  have ho1 : IsOpen (p.left ⁻¹' Set.range e.left) := hopen.preimage p.left.continuous
  have ho2 : IsOpen (φ.left ⁻¹' Set.range e.left) := hopen.preimage φ.left.continuous
  obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter ho1 ho2 h1 h2
  let U : X.left.Opens := ⟨_, ho1.inter ho2⟩
  let Z : Over T := Over.mk (U.ι ≫ X.hom)
  let j : Z ⟶ X := Over.homMk U.ι rfl
  obtain ⟨a, ha⟩ := exists_over_lift_of_range_subset e (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.2)
  obtain ⟨b, hb⟩ := exists_over_lift_of_range_subset e (j ≫ p) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.1)
  have key : lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e)) = j ≫ c ≫ g := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, hb, ← MonObj.comp_mul]
    simp only [φ, inv_mul_cancel_right]
  let u : Z.left := (⟨z, hz1, hz2⟩ : U)
  refine ⟨(lift a b).left u, ?_⟩
  change (lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e))).left u = x
  rw [key]
  exact H.left.fromSpecResidueField_apply x _

end GlobalTheory.Mum
