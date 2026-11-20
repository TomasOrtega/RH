import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRetractionOfProjective
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FunIdx

section Gen

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ProjectiveRetraction.exists_retraction`. Consider the case `exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction`. Consider the case `(apply _root_.GlobalTheory.ProjectiveRetraction.exists_retraction <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ProjectiveRetraction.exists_retraction <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ProjectiveRetraction.exists_retraction <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction ..)`.
-/
theorem exists_retraction (M0 L : Submodule (𝓞 E) V) (hL : L.FG) (h : IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨x, h.1 x.2⟩ = x := by
  first
  | exact @_root_.GlobalTheory.ProjectiveRetraction.exists_retraction
  | exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction
  | (apply _root_.GlobalTheory.ProjectiveRetraction.exists_retraction <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProjectiveRetraction.exists_retraction <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProjectiveRetraction.exists_retraction <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction ..)

/- English proof (translation)
Use `haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype := by`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[Module.End.isUnit_iff]`. Establish `ha0 : ((a : 𝓞 E) : E) ≠ 0`.

Use `nonZeroDivisors.ne_zero a.2` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `e : ⇑(algebraMap (𝓞 E) (Module.End (𝓞 E) V) a) = fun v => ((a : 𝓞 E) : E) • v`. Use function extensionality and compare the values at `v`. Conclude with `(algebraMap_smul E (a : 𝓞 E) v).symm`.

Rewrite using `[e]`. Conclude with `MulAction.bijective (Units.mk0 _ ha0)`. Introduce `y`. Establish `hy : y ∈ Submodule.span E (L : Set V)` using `hL ▸ Submodule.mem_top`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy`.

Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨(⟨_, ht⟩, t), rfl⟩`. Introduce `x y hxy`. Conclude with `⟨1, by rw [Subtype.ext hxy]⟩`. Set `g : L →ₗ[𝓞 E] E` to `Algebra.linearMap (𝓞 E) E ∘ₗ ψ`.

Establish `hu : ∀ a : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) a)` using `fun a => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) a`. Use `⟨(IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype g hu).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E, fun x => ?_⟩` and prove the remaining obligations. Conclude with `IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype g hu x`.
-/
theorem exists_extend_fun (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤)
    (ψ : L →ₗ[𝓞 E] 𝓞 E) : ∃ φ : V →ₗ[E] E, ∀ x : L, φ x = (ψ x : E) := by
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [Module.End.isUnit_iff]
      have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
        have := nonZeroDivisors.ne_zero a.2
        exact_mod_cast this
      have e : ⇑(algebraMap (𝓞 E) (Module.End (𝓞 E) V) a) = fun v => ((a : 𝓞 E) : E) • v := by
        funext v
        exact (algebraMap_smul E (a : 𝓞 E) v).symm
      rw [e]
      exact MulAction.bijective (Units.mk0 _ ha0)
    · intro y
      have hy : y ∈ Submodule.span E (L : Set V) := hL ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  let g : L →ₗ[𝓞 E] E := Algebra.linearMap (𝓞 E) E ∘ₗ ψ
  have hu : ∀ a : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) a) :=
    fun a => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) a
  refine ⟨(IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype g hu).extendScalarsOfIsLocalization
    (nonZeroDivisors (𝓞 E)) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype g hu x

end Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Set `G : S.V →ₗ[E] (Fin S.rank → E)` to `LinearMap.pi fun i => S.hT (S.frame i)`. Establish `hG : Function.Injective G`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Apply `S.nondeg.2 y` to reduce the goal to its premises.

Introduce `x`. Establish `: S.hT.flip y = 0` using `S.frame.ext fun i => congrFun hy i`. Conclude with `LinearMap.congr_fun this x`. Establish `hs : Function.Surjective G` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [S.rank_eq])).1 hG`. Take `⟨w, hw⟩` from `hs fun i => star (φ (S.frame i))`.

Use `⟨w, fun x => LinearMap.congr_fun (S.frame.ext fun i => ?_ : φ = S.hT w) x⟩` and prove the remaining obligations. Establish `h1 : S.hT (S.frame i) w = star (φ (S.frame i))` using `congrFun hw i`. Establish `h2 : star (S.hT (S.frame i) w) = S.hT w (S.frame i)` using `S.herm.eq _ _`. Rewrite using `[← h2, h1, star_star]`.
-/
theorem exists_vec (S : HSpace E) (φ : S.V →ₗ[E] E) : ∃ w, ∀ x, φ x = S.hT w x := by
  let G : S.V →ₗ[E] (Fin S.rank → E) := LinearMap.pi fun i => S.hT (S.frame i)
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply S.nondeg.2 y
    intro x
    have : S.hT.flip y = 0 := S.frame.ext fun i => congrFun hy i
    exact LinearMap.congr_fun this x
  have hs : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [S.rank_eq])).1 hG
  obtain ⟨w, hw⟩ := hs fun i => star (φ (S.frame i))
  refine ⟨w, fun x => LinearMap.congr_fun (S.frame.ext fun i => ?_ : φ = S.hT w) x⟩
  have h1 : S.hT (S.frame i) w = star (φ (S.frame i)) := congrFun hw i
  have h2 : star (S.hT (S.frame i) w) = S.hT w (S.frame i) := S.herm.eq _ _
  rw [← h2, h1, star_star]

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_retraction M0 L hL.fg h`. Take `⟨φ, hφ⟩` from `exists_extend_fun L hL.span_eq_top (ψ ∘ₗ r)`. Take `⟨w, hw⟩` from `exists_vec S φ`. Use `⟨⟨w, ?_, ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).2 fun y => (Submodule.mem_iInf _).2 fun hy => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `S.hT y w ∈ (1 : Submodule (𝓞 E) E)`. Establish `h2 : star (S.hT w y) = S.hT y w` using `S.herm.eq _ _`. Establish `h3 : IsIntegral ℤ (S.hT y w)`. Rewrite using `[← h2, ← hw, hφ ⟨y, hy⟩]`. Conclude with `(RingOfIntegers.isIntegral_coe _).map (starRingEnd E).toIntAlgHom`.

Conclude with `Submodule.mem_one.2 ⟨⟨_, h3⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `w ∈ Submodule.span E (L : Set S.V)`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Use `hφ ⟨x, h.1 x.2⟩` as an intermediate fact.

Rewrite `this` using `[LinearMap.comp_apply, hr]`. Rewrite using `[← this, hw]`.
-/
theorem exists_dual_vec (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (h : IsPrimitiveSub M0 L) (ψ : M0 →ₗ[𝓞 E] 𝓞 E) :
    ∃ w : dualInH S.hT L, ∀ x : M0, (ψ x : E) = S.hT w x := by
  obtain ⟨r, hr⟩ := exists_retraction M0 L hL.fg h
  obtain ⟨φ, hφ⟩ := exists_extend_fun L hL.span_eq_top (ψ ∘ₗ r)
  obtain ⟨w, hw⟩ := exists_vec S φ
  refine ⟨⟨w, ?_, ?_⟩, fun x => ?_⟩
  · refine (Submodule.mem_iInf _).2 fun y => (Submodule.mem_iInf _).2 fun hy => ?_
    change S.hT y w ∈ (1 : Submodule (𝓞 E) E)
    have h2 : star (S.hT w y) = S.hT y w := S.herm.eq _ _
    have h3 : IsIntegral ℤ (S.hT y w) := by
      rw [← h2, ← hw, hφ ⟨y, hy⟩]
      exact (RingOfIntegers.isIntegral_coe _).map (starRingEnd E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨_, h3⟩, rfl⟩
  · change w ∈ Submodule.span E (L : Set S.V)
    rw [hL.span_eq_top]; trivial
  · have := hφ ⟨x, h.1 x.2⟩
    rw [LinearMap.comp_apply, hr] at this
    rw [← this, hw]

/- English proof (translation)
Use `choose w hw using exists_dual_vec S M0 L hL h`. Use `haveI : Finite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) := Nat.finite_of_card_ne_zero (by omega)`. Use `letI := Fintype.ofFinite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)`. Set `g : (M0 →ₗ[𝓞 E] 𝓞 E) → (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)` to `fun ψ => Submodule.Quotient.mk (w ψ)`. Use `⟨Finset.univ.image (Function.invFun g), ?_, fun ψ => ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Finset.card_image_le`. Use `⟨Function.invFun g (g ψ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Establish `h1 : g ψ = g (Function.invFun g (g ψ))` using `(Function.invFun_eq ⟨ψ, rfl⟩).symm`. Establish `h2` using `(Submodule.Quotient.eq _).1 h1`.

Use `⟨_, h2, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.subtype_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply, ← hw, ← hw]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem exists_reps (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (h : IsPrimitiveSub M0 L)
    (hfin : 1 ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)) :
    ∃ reps : Finset (M0 →ₗ[𝓞 E] 𝓞 E),
      reps.card ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) ∧
      ∀ ψ : M0 →ₗ[𝓞 E] 𝓞 E, ∃ ψ₀ ∈ reps, ∃ v ∈ L, ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 E) : E) = S.hT v x := by
  choose w hw using exists_dual_vec S M0 L hL h
  haveI : Finite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)
  let g : (M0 →ₗ[𝓞 E] 𝓞 E) → (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    fun ψ => Submodule.Quotient.mk (w ψ)
  refine ⟨Finset.univ.image (Function.invFun g), ?_, fun ψ => ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact Finset.card_image_le
  · refine ⟨Function.invFun g (g ψ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 : g ψ = g (Function.invFun g (g ψ)) := (Function.invFun_eq ⟨ψ, rfl⟩).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    refine ⟨_, h2, fun x => ?_⟩
    rw [Submodule.subtype_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply, ← hw, ← hw]
    push_cast
    rfl

/- English proof (translation)
Introduce `D u u' F0 Λ hS hB hR M0 hM`. Take `⟨-, -, hpd, hlat, hint, hdet, -⟩` from `GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hS hB hR`. Take `⟨h1, h2, -⟩` from `GlobalTheory.LoopC.DetCard.main D _ hlat.fg hpd hint`. Take `⟨reps, hc, hr⟩` from `exists_reps (D.sp.X 0) M0 _ hlat hM h1`. Use `⟨reps, ?_, hr⟩` and prove the remaining obligations.

Rewrite using `[← hdet, ← h2]`. Conclude with `hc` after adjusting the coercions.
-/
theorem funIdx : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ M0 : LatW D, IsPrimitiveSub M0 (L0X D Λ (lf D F0)) → ∃ reps : Finset (M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (reps.card : ℝ) ≤ NT D u ^ 2 ∧ ∀ ψ : M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ reps, ∃ v ∈ L0X D Λ (lf D F0), ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v x := by
  intro D u u' F0 Λ hS hB hR M0 hM
  obtain ⟨-, -, hpd, hlat, hint, hdet, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hS hB hR
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LoopC.DetCard.main D _ hlat.fg hpd hint
  obtain ⟨reps, hc, hr⟩ := exists_reps (D.sp.X 0) M0 _ hlat hM h1
  refine ⟨reps, ?_, hr⟩
  rw [← hdet, ← h2]
  exact_mod_cast hc

end GlobalTheory.LoopC.FunIdx
