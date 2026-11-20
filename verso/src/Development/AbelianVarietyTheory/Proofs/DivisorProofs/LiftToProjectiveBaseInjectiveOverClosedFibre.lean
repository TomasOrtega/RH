import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ _ M G' _ _ _ E z w hz hwz`. Use `set p := PSpace.str R E.N`. Use `set Φ : E.H.toScheme ⟶ pullback p M.π := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over with hΦ`. Use `set s := G'.hom (E.H.ι z) with hs`. Set `Ω` to `M.S.residueField s`.

Set `x : Sp Ω ⟶ M.S` to `M.S.fromSpecResidueField s`. Set `φ : R →+* Ω` to `(Spec.preimage (x ≫ M.π)).hom`. Establish `hφ : spMap φ = x ≫ M.π` using `by unfold spMap; simp [φ]`. Establish `hker : ∀ r ∈ maximalIdeal R, φ r = 0`. Introduce `r hr`.

Take `⟨pt⟩ : Nonempty (Sp Ω)` from `inferInstance`. Establish `h1 : (x ≫ M.π) pt = closedPoint R`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`. Conclude with `hz`. Rewrite `h1` using `[← hφ]`.

Establish `h2 : (spMap φ) pt = PrimeSpectrum.comap φ pt` using `rfl`. Establish `h3 : pt.asIdeal = ⊥` using `by haveI := pt.isPrime; exact Ideal.eq_bot_of_prime _`. Establish `h4 : r ∈ ((spMap φ) pt).asIdeal` using `by rw [h1]; exact hr`. Rewrite `h4` using `[h2]`. Express the relevant statement in the definitionally equal form `φ r ∈ pt.asIdeal at h4`.

Rewrite `h4` using `[h3]`. Conclude with `h4`. Set `κ : ResidueField R →+* Ω` to `Ideal.Quotient.lift (maximalIdeal R) φ hker`. Establish `hκ : κ.comp (residue R) = φ` using `by ext r; rfl`. Establish `hx : x ≫ M.π = spMap (κ.comp (residue R))` using `by rw [hκ, hφ]`.

Take `⟨Ω', _, io, e, l, -, hl, hlf⟩` from `E.fib Ω x κ hx`. Establish `hx'π : (spMap io ≫ x) ≫ M.π = spMap (io.comp κ) ≫ spMap (residue R)`. Rewrite using `[Category.assoc, hx]`. Unfold `spMap`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `hψ : (l ≫ Φ) ≫ pullback.snd p M.π = pullback.snd G'.hom (spMap io ≫ x) ≫ (spMap io ≫ x)`. Establish `: Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom` using `by rw [hΦ]; exact pullback.lift_snd _ _ _`. Rewrite using `[Category.assoc, this, ← Category.assoc, hl]`. Conclude with `pullback.condition`.

Set `ψ : pullback G'.hom (spMap io ≫ x) ⟶ pullback (pullback.snd p M.π) (spMap io ≫ x)` to `pullback.lift (l ≫ Φ) (pullback.snd _ _) hψ`. Establish `hψinj : Function.Injective ψ` using `by haveI : IsImmersion E.j := E.imm`. Set `h : pullback (pullback.snd p M.π) (spMap io ≫ x) ⟶ PSpace R E.N` to `pullback.fst _ _ ≫ pullback.fst _ _`. Establish `hΦf : Φ ≫ pullback.fst p M.π = E.f` using `by rw [hΦ]; exact pullback.lift_fst _ _ _`. Establish `hψ1 : ψ ≫ pullback.fst _ _ = l ≫ Φ` using `pullback.lift_fst _ _ _`.

Establish `hψh : ψ ≫ h = l ≫ E.f` using `by show ψ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _`. Rewrite using `[← Category.assoc, hψ1, Category.assoc, hΦf]`. Establish `hθ : (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = ψ ≫ h`. Rewrite using `[hψh, hlf, Category.assoc]`. Set `θ : pullback G'.hom (spMap io ≫ x) ⟶ pullback E.j h` to `pullback.lift _ _ hθ`.

Use `haveI : Mono (spMap (residue R)) := by`. Establish `: IsClosedImmersion (spMap (residue R))` using `IsClosedImmersion.spec_of_surjective _ residue_surjective`. Use `infer_instance`. Establish `hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom` using `by rw [hΦ]; exact pullback.lift_snd _ _ _`. Establish `hρ : pullback.fst E.j h ≫ E.Y.hom = (pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ)`.

Rewrite using `[← cancel_mono (spMap (residue R))]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [h, Category.assoc]`. Rewrite using `[pullback.condition]`. Use `_ = pullback.snd E.j h ≫ pullback.snd _ _ ≫ (spMap io ≫ x) ≫ M.π := by`.

Rewrite using `[← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]`. Use `_ = ((pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ)) ≫ spMap (residue R) := by`. Rewrite using `[hx'π]`. Simplify using `only [Category.assoc]`. Set `ρ : pullback E.j h ⟶ pullback E.Y.hom (spMap (io.comp κ))` to `pullback.lift _ _ hρ`.

Establish `hθ1 : θ ≫ pullback.fst E.j h = e.hom.left ≫ pullback.fst _ _` using `pullback.lift_fst _ _ _`. Establish `hθ2 : θ ≫ pullback.snd E.j h = ψ` using `pullback.lift_snd _ _ _`. Establish `hρ1 : ρ ≫ pullback.fst _ _ = pullback.fst E.j h` using `pullback.lift_fst _ _ _`. Establish `hρ2 : ρ ≫ pullback.snd _ _ = pullback.snd E.j h ≫ pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `hψ2 : ψ ≫ pullback.snd _ _ = pullback.snd G'.hom (spMap io ≫ x)` using `pullback.lift_snd _ _ _`.

Establish `hθρ : θ ≫ ρ = e.hom.left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hρ1, hθ1]`. Rewrite using `[Category.assoc, hρ2, ← Category.assoc, hθ2, hψ2]`. Conclude with `(Over.w e.hom).symm`.

Introduce `a b hab`. Establish `h1 : θ a = θ b`. Apply `(pullback.snd E.j h).isEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]`. Conclude with `hab`.

Establish `h2 : e.hom.left a = e.hom.left b`. Rewrite using `[← hθρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1]`. Establish `h3` using `congrArg e.inv.left h2`. Rewrite `h3` using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id, Over.id_left]`. Then use the resulting hypothesis. Take `⟨τ⟩ : Nonempty (Sp Ω')` from `inferInstance`.

Establish `hτ : (spMap io ≫ x) τ = s`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _`. Establish `hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom` using `by rw [hΦ]; exact pullback.lift_snd _ _ _`. Establish `hq : pullback.snd p M.π (Φ z) = (spMap io ≫ x) τ`.

Rewrite using `[hτ, ← Scheme.Hom.comp_apply, hΦs, Scheme.Hom.comp_apply]`. Take `⟨c, hc1, hc2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p M.π) (g := spMap io ≫ x) _ _ hq`. Establish `hm : (pullback.fst Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ E.H.ι) ≫ G'.hom = (pullback.snd Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ pullback.snd _ _) ≫ (spMap io ≫ x)`. Rewrite using `[Category.assoc, ← hΦs, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition, Category.assoc]`. Set `m : pullback Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ⟶ pullback G'.hom (spMap io ≫ x)` to `pullback.lift _ _ hm`.

Establish `hm1 : m ≫ l = pullback.fst _ _`. Rewrite using `[← cancel_mono E.H.ι, Category.assoc, hl]`. Conclude with `pullback.lift_fst _ _ _`. Establish `hm2 : m ≫ ψ = pullback.snd _ _`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, pullback.lift_fst, ← Category.assoc, hm1, pullback.condition]`. Rewrite using `[Category.assoc, pullback.lift_snd]`. Conclude with `pullback.lift_snd _ _ _`. Establish `lift_pt : ∀ u : E.H.toScheme, Φ u = Φ z → ∃ a, l a = u ∧ ψ a = c`. Introduce `u hu`.

Take `⟨pu, h1, h2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Φ) (g := pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) u c (hu.trans hc1.symm)`. Conclude with `⟨m pu, by rw [← Scheme.Hom.comp_apply, hm1, h1], by rw [← Scheme.Hom.comp_apply, hm2, h2]⟩`. Take `⟨a, ha1, ha2⟩` from `lift_pt w hwz`. Take `⟨b, hb1, hb2⟩` from `lift_pt z rfl`. Rewrite using `[← ha1, ← hb1, hψinj (ha2.trans hb2.symm)]`.
-/
theorem Emb.chart_injective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ z w : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over w = pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over z → w = z := by
  intro R _ _ _ _ M G' _ _ _ E z w hz hwz

  set p := PSpace.str R E.N
  set Φ : E.H.toScheme ⟶ pullback p M.π := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over with hΦ
  set s := G'.hom (E.H.ι z) with hs

  let Ω := M.S.residueField s
  let x : Sp Ω ⟶ M.S := M.S.fromSpecResidueField s
  let φ : R →+* Ω := (Spec.preimage (x ≫ M.π)).hom
  have hφ : spMap φ = x ≫ M.π := by unfold spMap; simp [φ]
  have hker : ∀ r ∈ maximalIdeal R, φ r = 0 := by
    intro r hr
    obtain ⟨pt⟩ : Nonempty (Sp Ω) := inferInstance
    have h1 : (x ≫ M.π) pt = closedPoint R := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hz
    rw [← hφ] at h1
    have h2 : (spMap φ) pt = PrimeSpectrum.comap φ pt := rfl
    have h3 : pt.asIdeal = ⊥ := by haveI := pt.isPrime; exact Ideal.eq_bot_of_prime _
    have h4 : r ∈ ((spMap φ) pt).asIdeal := by rw [h1]; exact hr
    rw [h2] at h4
    change φ r ∈ pt.asIdeal at h4
    rw [h3] at h4
    exact h4
  let κ : ResidueField R →+* Ω := Ideal.Quotient.lift (maximalIdeal R) φ hker
  have hκ : κ.comp (residue R) = φ := by ext r; rfl
  have hx : x ≫ M.π = spMap (κ.comp (residue R)) := by rw [hκ, hφ]
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω x κ hx

  have hx'π : (spMap io ≫ x) ≫ M.π = spMap (io.comp κ) ≫ spMap (residue R) := by
    rw [Category.assoc, hx]; unfold spMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hψ : (l ≫ Φ) ≫ pullback.snd p M.π = pullback.snd G'.hom (spMap io ≫ x) ≫ (spMap io ≫ x) := by
    have : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    rw [Category.assoc, this, ← Category.assoc, hl]; exact pullback.condition
  let ψ : pullback G'.hom (spMap io ≫ x) ⟶ pullback (pullback.snd p M.π) (spMap io ≫ x) :=
    pullback.lift (l ≫ Φ) (pullback.snd _ _) hψ

  have hψinj : Function.Injective ψ := by
    haveI : IsImmersion E.j := E.imm
    let h : pullback (pullback.snd p M.π) (spMap io ≫ x) ⟶ PSpace R E.N := pullback.fst _ _ ≫ pullback.fst _ _
    have hΦf : Φ ≫ pullback.fst p M.π = E.f := by rw [hΦ]; exact pullback.lift_fst _ _ _
    have hψ1 : ψ ≫ pullback.fst _ _ = l ≫ Φ := pullback.lift_fst _ _ _
    have hψh : ψ ≫ h = l ≫ E.f := by
      show ψ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
      rw [← Category.assoc, hψ1, Category.assoc, hΦf]
    have hθ : (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = ψ ≫ h := by
      rw [hψh, hlf, Category.assoc]
    let θ : pullback G'.hom (spMap io ≫ x) ⟶ pullback E.j h := pullback.lift _ _ hθ
    haveI : Mono (spMap (residue R)) := by
      have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
      infer_instance
    have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    have hρ : pullback.fst E.j h ≫ E.Y.hom = (pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ) := by
      rw [← cancel_mono (spMap (residue R))]
      calc pullback.fst E.j h ≫ E.Y.hom ≫ spMap (residue R) = pullback.fst E.j h ≫ E.j ≫ p := by rw [E.j_over]
        _ = pullback.snd E.j h ≫ h ≫ p := by rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = pullback.snd E.j h ≫ pullback.fst _ _ ≫ pullback.snd p M.π ≫ M.π := by
          simp only [h, Category.assoc]; rw [pullback.condition]
        _ = pullback.snd E.j h ≫ pullback.snd _ _ ≫ (spMap io ≫ x) ≫ M.π := by
          rw [← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]
        _ = ((pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ)) ≫ spMap (residue R) := by
          rw [hx'π]; simp only [Category.assoc]
    let ρ : pullback E.j h ⟶ pullback E.Y.hom (spMap (io.comp κ)) := pullback.lift _ _ hρ
    have hθ1 : θ ≫ pullback.fst E.j h = e.hom.left ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hθ2 : θ ≫ pullback.snd E.j h = ψ := pullback.lift_snd _ _ _
    have hρ1 : ρ ≫ pullback.fst _ _ = pullback.fst E.j h := pullback.lift_fst _ _ _
    have hρ2 : ρ ≫ pullback.snd _ _ = pullback.snd E.j h ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
    have hψ2 : ψ ≫ pullback.snd _ _ = pullback.snd G'.hom (spMap io ≫ x) := pullback.lift_snd _ _ _
    have hθρ : θ ≫ ρ = e.hom.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hρ1, hθ1]
      · rw [Category.assoc, hρ2, ← Category.assoc, hθ2, hψ2]
        exact (Over.w e.hom).symm
    intro a b hab
    have h1 : θ a = θ b := by
      apply (pullback.snd E.j h).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hab
    have h2 : e.hom.left a = e.hom.left b := by
      rw [← hθρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1]
    have h3 := congrArg e.inv.left h2
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id, Over.id_left] at h3

  obtain ⟨τ⟩ : Nonempty (Sp Ω') := inferInstance
  have hτ : (spMap io ≫ x) τ = s := by
    rw [Scheme.Hom.comp_apply]; exact Scheme.fromSpecResidueField_apply _ _
  have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
  have hq : pullback.snd p M.π (Φ z) = (spMap io ≫ x) τ := by
    rw [hτ, ← Scheme.Hom.comp_apply, hΦs, Scheme.Hom.comp_apply]
  obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p M.π) (g := spMap io ≫ x) _ _ hq

  have hm : (pullback.fst Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ E.H.ι) ≫ G'.hom =
      (pullback.snd Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ pullback.snd _ _) ≫ (spMap io ≫ x) := by
    rw [Category.assoc, ← hΦs, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
      Category.assoc]
  let m : pullback Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ⟶ pullback G'.hom (spMap io ≫ x) :=
    pullback.lift _ _ hm
  have hm1 : m ≫ l = pullback.fst _ _ := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl]; exact pullback.lift_fst _ _ _
  have hm2 : m ≫ ψ = pullback.snd _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hm1, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd]; exact pullback.lift_snd _ _ _
  have lift_pt : ∀ u : E.H.toScheme, Φ u = Φ z → ∃ a, l a = u ∧ ψ a = c := by
    intro u hu
    obtain ⟨pu, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Φ) (g := pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) u c (hu.trans hc1.symm)
    exact ⟨m pu, by rw [← Scheme.Hom.comp_apply, hm1, h1], by rw [← Scheme.Hom.comp_apply, hm2, h2]⟩
  obtain ⟨a, ha1, ha2⟩ := lift_pt w hwz
  obtain ⟨b, hb1, hb2⟩ := lift_pt z rfl
  rw [← ha1, ← hb1, hψinj (ha2.trans hb2.symm)]

end GlobalTheory.Mum
