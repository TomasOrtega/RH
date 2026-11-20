import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL.SupportUnique

variable {G H V Y Y' W₀ W₁ : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Y'] [Module ℂ Y'] [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁]

/- English proof (translation)
Establish `hv : ∀ v : V, v ∈ T.toSubmodule`. Substitute `hT` using the available equality. Introduce `v`. Conclude with `Submodule.mem_top`. Set `j : V →ₗ[ℂ] T.toSubmodule` to `LinearMap.codRestrict T.toSubmodule LinearMap.id hv`.

Set `L : V →ₗ[ℂ] Y` to `E.toIntertwiningMap.toLinearMap ∘ₗ (Submodule.mkQ _) ∘ₗ j`. Establish `hL : ∀ v, L v = E.toIntertwiningMap (Submodule.Quotient.mk (j v))` using `fun v => rfl`. Establish `hint : ∀ (g : G) (v : V), L (μ g v) = τ g (L v)`. Introduce `g v`. Rewrite using `[hL, hL]`.

Use `Eq.trans ?_ (Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g _)` and prove the remaining obligations. Both sides reduce to the same expression. Use `⟨L.intertwiningMap_of_isIntertwiningMap μ τ hint, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨w, hw⟩` from `Submodule.Quotient.mk_surjective _ (E.symm y)`.

Use `⟨(w : V), ?_⟩` and prove the remaining obligations. Use `show L w = y`. Rewrite using `[hL]`. Establish `hj : j w = w` using `Subtype.ext rfl`. Rewrite using `[hj, hw]`.

Conclude with `E.apply_symm_apply y`. Introduce `v show L v = 0 ↔ v ∈ A.toSubmodule`. Rewrite using `[hL]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Establish `h1 : (Submodule.Quotient.mk (j v) : T.toSubmodule ⧸ A.toSubmodule.comap T.toSubmodule.subtype) = 0`. Rewrite using `[← E.symm_apply_apply (Submodule.Quotient.mk (j v))]`. Express the relevant statement in the definitionally equal form `E.symm (E.toIntertwiningMap (Submodule.Quotient.mk (j v))) = 0`. Rewrite using `[h0]`. Conclude with `map_zero E.symm.toIntertwiningMap`.

Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Conclude with `h1`. Introduce `h0`. Establish `h1 : (Submodule.Quotient.mk (j v) : T.toSubmodule ⧸ A.toSubmodule.comap T.toSubmodule.subtype) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Conclude with `h0`. Rewrite using `[h1]`. Conclude with `map_zero E.toIntertwiningMap`.
-/
theorem exists_quot_map {μ : Representation ℂ G V} {τ : Representation ℂ G Y}
    (A T : Subrepresentation μ) (hT : T = ⊤) (E : (subQuot T A).Equiv τ) :
    ∃ q : μ.IntertwiningMap τ, Function.Surjective q ∧ ∀ v, q v = 0 ↔ v ∈ A.toSubmodule := by
  have hv : ∀ v : V, v ∈ T.toSubmodule := by
    subst hT
    intro v
    exact Submodule.mem_top
  let j : V →ₗ[ℂ] T.toSubmodule := LinearMap.codRestrict T.toSubmodule LinearMap.id hv
  let L : V →ₗ[ℂ] Y := E.toIntertwiningMap.toLinearMap ∘ₗ (Submodule.mkQ _) ∘ₗ j
  have hL : ∀ v, L v = E.toIntertwiningMap (Submodule.Quotient.mk (j v)) := fun v => rfl
  have hint : ∀ (g : G) (v : V), L (μ g v) = τ g (L v) := by
    intro g v
    rw [hL, hL]
    refine Eq.trans ?_ (Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g _)
    rfl
  refine ⟨L.intertwiningMap_of_isIntertwiningMap μ τ hint, ?_, ?_⟩
  · intro y
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (E.symm y)
    refine ⟨(w : V), ?_⟩
    show L w = y
    rw [hL]
    have hj : j w = w := Subtype.ext rfl
    rw [hj, hw]
    exact E.apply_symm_apply y
  · intro v
    show L v = 0 ↔ v ∈ A.toSubmodule
    rw [hL]
    constructor
    · intro h0
      have h1 : (Submodule.Quotient.mk (j v) : T.toSubmodule ⧸ A.toSubmodule.comap T.toSubmodule.subtype) = 0 := by
        rw [← E.symm_apply_apply (Submodule.Quotient.mk (j v))]
        change E.symm (E.toIntertwiningMap (Submodule.Quotient.mk (j v))) = 0
        rw [h0]
        exact map_zero E.symm.toIntertwiningMap
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
      exact h1
    · intro h0
      have h1 : (Submodule.Quotient.mk (j v) : T.toSubmodule ⧸ A.toSubmodule.comap T.toSubmodule.subtype) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        exact h0
      rw [h1]
      exact map_zero E.toIntertwiningMap

/- English proof (translation)
Substitute `hB` using the available equality. Set `m : X.toRepresentation.IntertwiningMap (subQuot X ⊥)` to `⟨Submodule.mkQ _, fun g => LinearMap.ext fun _ => rfl⟩`. Establish `hm : Function.Injective m`. Introduce `x y hxy`. Establish `h1 : x - y ∈ (⊥ : Subrepresentation μ).toSubmodule.comap X.toSubmodule.subtype` using `(Submodule.Quotient.eq _).1 hxy`.

Rewrite `h1` using `[Submodule.mem_comap]`. Establish `h0 : ((x - y : X.toSubmodule) : V) = 0` using `(Submodule.mem_bot ℂ).1 h1`. Conclude with `sub_eq_zero.1 (Submodule.coe_eq_zero.1 h0)`. Establish `hms : Function.Surjective m` using `Submodule.Quotient.mk_surjective _`. Establish `hE : Function.Injective E.toIntertwiningMap`.

Introduce `x y hxy`. Rewrite using `[← E.symm_apply_apply x, ← E.symm_apply_apply y]`. Conclude with `congrArg E.symm hxy`. Establish `hEs : Function.Surjective E.toIntertwiningMap` using `fun y => ⟨E.symm y, E.apply_symm_apply y⟩`. Set `f` to `E.toIntertwiningMap.comp m`.

Establish `bij : Function.Bijective f` using `⟨hE.comp hm, hEs.comp hms⟩`. Conclude with `⟨Representation.Equiv.mk' f (Function.surjInv bij.2) (Function.leftInverse_surjInv bij) (Function.rightInverse_surjInv bij.2)⟩`.
-/
theorem exists_sub_equiv {μ : Representation ℂ G V} {τ : Representation ℂ G Y}
    (X B : Subrepresentation μ) (hB : B = ⊥) (E : (subQuot X B).Equiv τ) :
    Nonempty (X.toRepresentation.Equiv τ) := by
  subst hB
  let m : X.toRepresentation.IntertwiningMap (subQuot X ⊥) :=
    ⟨Submodule.mkQ _, fun g => LinearMap.ext fun _ => rfl⟩
  have hm : Function.Injective m := by
    intro x y hxy
    have h1 : x - y ∈ (⊥ : Subrepresentation μ).toSubmodule.comap X.toSubmodule.subtype :=
      (Submodule.Quotient.eq _).1 hxy
    rw [Submodule.mem_comap] at h1
    have h0 : ((x - y : X.toSubmodule) : V) = 0 := (Submodule.mem_bot ℂ).1 h1
    exact sub_eq_zero.1 (Submodule.coe_eq_zero.1 h0)
  have hms : Function.Surjective m := Submodule.Quotient.mk_surjective _
  have hE : Function.Injective E.toIntertwiningMap := by
    intro x y hxy
    rw [← E.symm_apply_apply x, ← E.symm_apply_apply y]
    exact congrArg E.symm hxy
  have hEs : Function.Surjective E.toIntertwiningMap := fun y => ⟨E.symm y, E.apply_symm_apply y⟩
  let f := E.toIntertwiningMap.comp m
  have bij : Function.Bijective f := ⟨hE.comp hm, hEs.comp hms⟩
  exact ⟨Representation.Equiv.mk' f (Function.surjInv bij.2) (Function.leftInverse_surjInv bij)
    (Function.rightInverse_surjInv bij.2)⟩

/- English proof (translation)
Establish `hcomm : ∀ (g : G) (v : V), μ z (μ g v) = μ g (μ z v)`. Introduce `g v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← hz g, map_mul, Module.End.mul_apply]`. Establish `hD : ∀ v : V, μ z v - c • v ∈ X.toSubmodule`. Introduce `v`.

Rewrite using `[← hq, map_sub, map_smul, Representation.IntertwiningMap.isIntertwining _ _ q, hc, sub_self]`. Set `P : V →ₗ[ℂ] X.toSubmodule` to `LinearMap.codRestrict X.toSubmodule (μ z - c • LinearMap.id) (fun v => hD v)`. Establish `hP : ∀ v, (P v : V) = μ z v - c • v` using `fun v => rfl`. Establish `hPg : ∀ (g : G) (v : V), P (μ g v) = X.toRepresentation g (P v)`. Introduce `g v`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hP]`. Use `show μ z (μ g v) - c • μ g v = μ g (P v : V)`. Rewrite using `[hP, map_sub, map_smul, hcomm]`. Set `φL : V →ₗ[ℂ] Y` to `a.toIntertwiningMap.toLinearMap ∘ₗ P`.

Establish `hφ : ∀ (g : G) (v : V), φL (μ g v) = τ g (φL v)`. Introduce `g v`. Use `show a.toIntertwiningMap (P (μ g v)) = τ g (a.toIntertwiningMap (P v))`. Rewrite using `[hPg]`. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g (P v)`.

Distinguish the cases in `hex : ∃ v, φL v ≠ 0`. Take `⟨v, hv⟩` from `hex`. Conclude with `Or.inl ⟨φL.intertwiningMap_of_isIntertwiningMap μ τ hφ, v, hv⟩`. Use `push_neg at hex right`. Introduce `v`.

Establish `h1 : P v = 0`. Rewrite using `[← a.symm_apply_apply (P v)]`. Express the relevant statement in the definitionally equal form `a.symm (φL v) = 0`. Rewrite using `[hex v]`. Conclude with `map_zero a.symm.toIntertwiningMap`.

Establish `h2 : (P v : V) = 0` using `by rw [h1]; rfl`. Rewrite `h2` using `[hP]`. Conclude with `sub_eq_zero.1 h2`.
-/
theorem central_dichotomy {μ : Representation ℂ G V} {τ : Representation ℂ G Y} {ρ : Representation ℂ G Y'}
    (X : Subrepresentation μ) (a : X.toRepresentation.Equiv τ) (q : μ.IntertwiningMap ρ)
    (hq : ∀ v, q v = 0 ↔ v ∈ X.toSubmodule) (z : G) (hz : ∀ g, g * z = z * g) (c : ℂ)
    (hc : ∀ y, ρ z y = c • y) :
    (∃ (φ : μ.IntertwiningMap τ) (v : V), φ v ≠ 0) ∨ ∀ v, μ z v = c • v := by
  have hcomm : ∀ (g : G) (v : V), μ z (μ g v) = μ g (μ z v) := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, ← hz g, map_mul, Module.End.mul_apply]
  have hD : ∀ v : V, μ z v - c • v ∈ X.toSubmodule := by
    intro v
    rw [← hq, map_sub, map_smul, Representation.IntertwiningMap.isIntertwining _ _ q, hc, sub_self]
  let P : V →ₗ[ℂ] X.toSubmodule :=
    LinearMap.codRestrict X.toSubmodule (μ z - c • LinearMap.id) (fun v => hD v)
  have hP : ∀ v, (P v : V) = μ z v - c • v := fun v => rfl
  have hPg : ∀ (g : G) (v : V), P (μ g v) = X.toRepresentation g (P v) := by
    intro g v
    apply Subtype.ext
    rw [hP]
    show μ z (μ g v) - c • μ g v = μ g (P v : V)
    rw [hP, map_sub, map_smul, hcomm]
  let φL : V →ₗ[ℂ] Y := a.toIntertwiningMap.toLinearMap ∘ₗ P
  have hφ : ∀ (g : G) (v : V), φL (μ g v) = τ g (φL v) := by
    intro g v
    show a.toIntertwiningMap (P (μ g v)) = τ g (a.toIntertwiningMap (P v))
    rw [hPg]
    exact Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g (P v)
  by_cases hex : ∃ v, φL v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    exact Or.inl ⟨φL.intertwiningMap_of_isIntertwiningMap μ τ hφ, v, hv⟩
  · push_neg at hex
    right
    intro v
    have h1 : P v = 0 := by
      rw [← a.symm_apply_apply (P v)]
      change a.symm (φL v) = 0
      rw [hex v]
      exact map_zero a.symm.toIntertwiningMap
    have h2 : (P v : V) = 0 := by rw [h1]; rfl
    rw [hP] at h2
    exact sub_eq_zero.1 h2

def imageSub (ψ : H →* G) (A : Representation ℂ H W₀) (μ : Representation ℂ G V)
    (hdec : ∀ g, ∃ (h : H) (g' : G), g = ψ h * g' ∧ ∀ x, ψ x * g' = g' * ψ x) : Subrepresentation μ where
  toSubmodule := Submodule.span ℂ {u | ∃ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w = u}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨h, g', rfl, hg'⟩ := hdec g
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ι, w, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨μ g' ∘ₗ ι.toLinearMap, fun x => LinearMap.ext fun w => ?_⟩, A h w, ?_⟩
      · show μ g' (ι (A x w)) = μ (ψ x) (μ g' (ι w))
        have h1 : ι (A x w) = μ (ψ x) (ι w) := ι.isIntertwining _ _ x w
        rw [h1, ← Module.End.mul_apply, ← map_mul, ← hg', map_mul, Module.End.mul_apply]
      · show μ g' (ι (A h w)) = μ (ψ h * g') (ι w)
        have h1 : ι (A h w) = μ (ψ h) (ι w) := ι.isIntertwining _ _ h w
        rw [h1, ← Module.End.mul_apply, ← map_mul, ← hg']
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Use `haveI := hτ`. Use `haveI := hρ`. Set `W'` to `imageSub ψ A μ hdec`. Establish `hWspan : W'.toSubmodule = Submodule.span ℂ {u | ∃ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w = u}` using `rfl`. Establish `hmemW : ∀ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w ∈ W'.toSubmodule` using `fun ι w => Submodule.subset_span ⟨ι, w, rfl⟩`.

Set `P' : Subrepresentation τ` to `{ toSubmodule := W'.toSubmodule.comap (X.toSubmodule.subtype ∘ₗ a.symm.toIntertwiningMap.toLinearMap) apply_mem_toSubmodule := by`. Introduce `g y hy`. Rewrite `hy`, the goal using `[Submodule.mem_comap]`. Use `show ((a.symm.toIntertwiningMap (τ g y) : X.toSubmodule) : V) ∈ W'.toSubmodule`. Rewrite using `[Representation.IntertwiningMap.isIntertwining _ _ a.symm.toIntertwiningMap g y]`.

Conclude with `W'.apply_mem_toSubmodule g hy }`. Break down `eq_bot_or_eq_top P' with hP | hP` into its components or cases. Establish `hXW0 : ∀ x : V, x ∈ X.toSubmodule → x ∈ W'.toSubmodule → x = 0`. Introduce `x hx hxW`. Establish `h1 : a ⟨x, hx⟩ ∈ P'.toSubmodule`.

Rewrite using `[Submodule.mem_comap]`. Use `show ((a.symm (a ⟨x, hx⟩) : X.toSubmodule) : V) ∈ W'.toSubmodule`. Rewrite using `[a.symm_apply_apply]`. Conclude with `hxW`. Rewrite `h1` using `[hP]`.

Establish `h2 : a ⟨x, hx⟩ = 0` using `(Submodule.mem_bot ℂ).1 h1`. Establish `h3 : (⟨x, hx⟩ : X.toSubmodule) = 0`. Rewrite using `[← a.symm_apply_apply ⟨x, hx⟩, h2]`. Conclude with `map_zero a.symm.toIntertwiningMap`. Conclude with `congrArg Subtype.val h3`.

Establish `hqW : ∀ w1 w2 : V, w1 ∈ W'.toSubmodule → w2 ∈ W'.toSubmodule → q w1 = q w2 → w1 = w2`. Introduce `w1 w2 h1 h2 h12`. Establish `h3 : w1 - w2 ∈ X.toSubmodule` using `by rw [← hq, map_sub, h12, sub_self]`. Conclude with `sub_eq_zero.1 (hXW0 _ h3 (W'.toSubmodule.sub_mem h1 h2))`. Set `incl : W'.toRepresentation.IntertwiningMap μ` to `⟨W'.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩`.

Set `r` to `q.comp incl`. Establish `hι : ∃ w, ι₀ w ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hι₀ (Representation.IntertwiningMap.ext (LinearMap.ext hcon))`.

Take `⟨w0, hw0⟩` from `hι`. Establish `hrange : r.range = ⊤`. Break down `eq_bot_or_eq_top r.range with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hm : r ⟨ι₀ w0, hmemW ι₀ w0⟩ ∈ r.range.toSubmodule` using `LinearMap.mem_range_self r.toLinearMap _`.

Rewrite `hm` using `[h]`. Establish `h0 : q (ι₀ w0) = 0` using `(Submodule.mem_bot ℂ).1 hm`. Conclude with `hw0 (hXW0 _ ((hq _).1 h0) (hmemW ι₀ w0))`. Conclude with `h`. Establish `hrs : Function.Surjective r`.

Introduce `y`. Establish `hy : y ∈ r.range.toSubmodule` using `by rw [hrange]; exact Submodule.mem_top`. Take `⟨x, hx⟩` from `LinearMap.mem_range.1 hy`. Conclude with `⟨x, hx⟩`. Establish `hri : Function.Injective r`.

Introduce `x1 x2 h12`. Conclude with `Subtype.ext (hqW _ _ x1.2 x2.2 h12)`. Set `e : W'.toSubmodule ≃ₗ[ℂ] Y'` to `LinearEquiv.ofBijective r.toLinearMap ⟨hri, hrs⟩`. Set `s : V →ₗ[ℂ] V` to `W'.toSubmodule.subtype ∘ₗ e.symm.toLinearMap ∘ₗ q.toLinearMap`. Establish `hsW : ∀ v, s v ∈ W'.toSubmodule` using `fun v => (e.symm (q v)).2`.

Establish `hqs' : ∀ v, q (s v) = q v`. Introduce `v`. Use `show r (e.symm (q v)) = q v`. Conclude with `e.apply_symm_apply (q v)`. Establish `hsg : ∀ (g : G) (v : V), s (μ g v) = μ g (s v)`.

Introduce `g v`. Apply `hqW _ _ (hsW _) (W'.apply_mem_toSubmodule g (hsW v))` to reduce the goal to its premises. Rewrite using `[hqs', Representation.IntertwiningMap.isIntertwining _ _ q, Representation.IntertwiningMap.isIntertwining _ _ q, hqs']`. Establish `hPX : ∀ v, v - s v ∈ X.toSubmodule`. Introduce `v`.

Rewrite using `[← hq, map_sub, hqs', sub_self]`. Set `P : V →ₗ[ℂ] X.toSubmodule` to `LinearMap.codRestrict X.toSubmodule (LinearMap.id - s) (fun v => hPX v)`. Set `φL : V →ₗ[ℂ] Y` to `a.toIntertwiningMap.toLinearMap ∘ₗ P`. Establish `hPg : ∀ (g : G) (v : V), P (μ g v) = X.toRepresentation g (P v)`. Introduce `g v`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show μ g v - s (μ g v) = μ g (v - s v)`. Rewrite using `[hsg, map_sub]`. Establish `hφ : ∀ (g : G) (v : V), φL (μ g v) = τ g (φL v)`. Introduce `g v`.

Use `show a.toIntertwiningMap (P (μ g v)) = τ g (a.toIntertwiningMap (P v))`. Rewrite using `[hPg]`. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g (P v)`. Establish `hY : ∃ y : Y, y ≠ 0`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `(bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use extensionality with `y`. Rewrite using `[hcon y]`.

Conclude with `⟨fun _ => zero_mem _, fun _ => zero_mem _⟩`. Take `⟨y, hy⟩` from `hY`. Use `⟨φL.intertwiningMap_of_isIntertwiningMap μ τ hφ, ((a.symm y : X.toSubmodule) : V), ?_⟩` and prove the remaining obligations. Use `show a.toIntertwiningMap (P _) ≠ 0`. Establish `hq0 : q ((a.symm y : X.toSubmodule) : V) = 0` using `(hq _).2 (a.symm y).2`.

Establish `hs0 : s ((a.symm y : X.toSubmodule) : V) = 0` using `by show ((e.symm (q _) : W'.toSubmodule) : V) = 0`. Rewrite using `[hq0, map_zero]`. Both sides reduce to the same expression. Establish `hP0 : P ((a.symm y : X.toSubmodule) : V) = a.symm y`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ((a.symm y : X.toSubmodule) : V) - s ((a.symm y : X.toSubmodule) : V) = ((a.symm y : X.toSubmodule) : V)`. Rewrite using `[hs0, sub_zero]`. Rewrite using `[hP0]`. Express the relevant statement in the definitionally equal form `a (a.symm y) ≠ 0`. Rewrite using `[a.apply_symm_apply]`.

Conclude with `hy`. It suffices to derive a contradiction. Apply `hAB` to reduce the goal to its premises. Establish `hXW : ∀ x ∈ X.toSubmodule, x ∈ W'.toSubmodule`. Introduce `x hx`.

Establish `h1 : a ⟨x, hx⟩ ∈ P'.toSubmodule` using `by rw [hP]; exact Submodule.mem_top`. Rewrite `h1` using `[Submodule.mem_comap]`. Establish `h2 : ((a.symm (a ⟨x, hx⟩) : X.toSubmodule) : V) ∈ W'.toSubmodule` using `h1`. Rewrite `h2` using `[a.symm_apply_apply]`. Conclude with `h2`.

Set `f : τ.IntertwiningMap W'.toRepresentation` to `⟨LinearMap.codRestrict W'.toSubmodule (X.toSubmodule.subtype ∘ₗ a.symm.toIntertwiningMap.toLinearMap) (fun y => hXW _ (a.symm y).2), fun g => by`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((a.symm.toIntertwiningMap (τ g y) : X.toSubmodule) : V) = μ g ((a.symm.toIntertwiningMap y : X.toSubmodule) : V)`. Rewrite using `[Representation.IntertwiningMap.isIntertwining _ _ a.symm.toIntertwiningMap g y]`.

Use the proof step `rfl⟩`. Establish `hfi : Function.Injective f`. Introduce `y1 y2 h12`. Establish `h4 : ((f y1 : W'.toSubmodule) : V) = ((f y2 : W'.toSubmodule) : V)` using `congrArg Subtype.val h12`. Establish `h3 : a.symm y1 = a.symm y2` using `Subtype.ext h4`.

Rewrite using `[← a.apply_symm_apply y1, ← a.apply_symm_apply y2, h3]`. Establish `hsub1 : IsSubquotient τ W'.toRepresentation` using `GlobalTheory.SmGL.IsSubquotient.of_injective f hfi`. Establish `hsub2` using `GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hsub1 ψ`. Establish `hsub3` using `GlobalTheory.SmGL.IsSubquotient.trans hBτ hsub2`. Establish `hspan : Submodule.span ℂ {u : W'.toSubmodule | ∃ (ι : A.IntertwiningMap (W'.toRepresentation.comp ψ)) (w : W₀), ι w = u} = ⊤`.

Apply `Submodule.map_injective_of_injective W'.toSubmodule.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_subtype_top]`. Use `Eq.trans ?_ hWspan.symm` and prove the remaining obligations. Use `congr 1`. Use extensionality with `u`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u', ⟨ι, w, rfl⟩, rfl⟩`. Use `⟨⟨W'.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun g => LinearMap.ext fun w' => ?_⟩, w, rfl⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ ι g w')`. Introduce and unpack `⟨ι, w, rfl⟩`.

Use `⟨⟨ι w, hmemW ι w⟩, ⟨⟨LinearMap.codRestrict W'.toSubmodule ι.toLinearMap (fun w' => hmemW ι w'), fun g => LinearMap.ext fun w' => ?_⟩, w, rfl⟩, rfl⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ ι g w'`. Conclude with `GlobalTheory.LocGL.SupportUnique.isSubquotient_of_span hB hsub3 hspan`.
-/
theorem exists_map_of_image (ψ : H →* G) {A : Representation ℂ H W₀} {B : Representation ℂ H W₁}
    (hB : B.IsIrreducible) (hAB : ¬ IsSubquotient B A) {μ : Representation ℂ G V} {τ : Representation ℂ G Y}
    {ρ : Representation ℂ G Y'} (hτ : τ.IsIrreducible) (hρ : ρ.IsIrreducible)
    (X : Subrepresentation μ) (a : X.toRepresentation.Equiv τ) (q : μ.IntertwiningMap ρ)
    (hqs : Function.Surjective q) (hq : ∀ v, q v = 0 ↔ v ∈ X.toSubmodule)
    (hBτ : IsSubquotient B (τ.comp ψ : Representation ℂ H Y))
    (ι₀ : A.IntertwiningMap (μ.comp ψ)) (hι₀ : ι₀ ≠ 0)
    (hdec : ∀ g, ∃ (h : H) (g' : G), g = ψ h * g' ∧ ∀ x, ψ x * g' = g' * ψ x) :
    ∃ (φ : μ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  classical
  haveI := hτ
  haveI := hρ
  let W' := imageSub ψ A μ hdec
  have hWspan : W'.toSubmodule =
      Submodule.span ℂ {u | ∃ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w = u} := rfl
  have hmemW : ∀ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w ∈ W'.toSubmodule :=
    fun ι w => Submodule.subset_span ⟨ι, w, rfl⟩
  let P' : Subrepresentation τ :=
    { toSubmodule := W'.toSubmodule.comap (X.toSubmodule.subtype ∘ₗ a.symm.toIntertwiningMap.toLinearMap)
      apply_mem_toSubmodule := by
        intro g y hy
        rw [Submodule.mem_comap] at hy ⊢
        show ((a.symm.toIntertwiningMap (τ g y) : X.toSubmodule) : V) ∈ W'.toSubmodule
        rw [Representation.IntertwiningMap.isIntertwining _ _ a.symm.toIntertwiningMap g y]
        exact W'.apply_mem_toSubmodule g hy }
  rcases eq_bot_or_eq_top P' with hP | hP
  · have hXW0 : ∀ x : V, x ∈ X.toSubmodule → x ∈ W'.toSubmodule → x = 0 := by
      intro x hx hxW
      have h1 : a ⟨x, hx⟩ ∈ P'.toSubmodule := by
        rw [Submodule.mem_comap]
        show ((a.symm (a ⟨x, hx⟩) : X.toSubmodule) : V) ∈ W'.toSubmodule
        rw [a.symm_apply_apply]
        exact hxW
      rw [hP] at h1
      have h2 : a ⟨x, hx⟩ = 0 := (Submodule.mem_bot ℂ).1 h1
      have h3 : (⟨x, hx⟩ : X.toSubmodule) = 0 := by
        rw [← a.symm_apply_apply ⟨x, hx⟩, h2]
        exact map_zero a.symm.toIntertwiningMap
      exact congrArg Subtype.val h3
    have hqW : ∀ w1 w2 : V, w1 ∈ W'.toSubmodule → w2 ∈ W'.toSubmodule → q w1 = q w2 → w1 = w2 := by
      intro w1 w2 h1 h2 h12
      have h3 : w1 - w2 ∈ X.toSubmodule := by rw [← hq, map_sub, h12, sub_self]
      exact sub_eq_zero.1 (hXW0 _ h3 (W'.toSubmodule.sub_mem h1 h2))
    let incl : W'.toRepresentation.IntertwiningMap μ :=
      ⟨W'.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
    let r := q.comp incl
    have hι : ∃ w, ι₀ w ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hι₀ (Representation.IntertwiningMap.ext (LinearMap.ext hcon))
    obtain ⟨w0, hw0⟩ := hι
    have hrange : r.range = ⊤ := by
      rcases eq_bot_or_eq_top r.range with h | h
      · exfalso
        have hm : r ⟨ι₀ w0, hmemW ι₀ w0⟩ ∈ r.range.toSubmodule := LinearMap.mem_range_self r.toLinearMap _
        rw [h] at hm
        have h0 : q (ι₀ w0) = 0 := (Submodule.mem_bot ℂ).1 hm
        exact hw0 (hXW0 _ ((hq _).1 h0) (hmemW ι₀ w0))
      · exact h
    have hrs : Function.Surjective r := by
      intro y
      have hy : y ∈ r.range.toSubmodule := by rw [hrange]; exact Submodule.mem_top
      obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hy
      exact ⟨x, hx⟩
    have hri : Function.Injective r := by
      intro x1 x2 h12
      exact Subtype.ext (hqW _ _ x1.2 x2.2 h12)
    let e : W'.toSubmodule ≃ₗ[ℂ] Y' := LinearEquiv.ofBijective r.toLinearMap ⟨hri, hrs⟩
    let s : V →ₗ[ℂ] V := W'.toSubmodule.subtype ∘ₗ e.symm.toLinearMap ∘ₗ q.toLinearMap
    have hsW : ∀ v, s v ∈ W'.toSubmodule := fun v => (e.symm (q v)).2
    have hqs' : ∀ v, q (s v) = q v := by
      intro v
      show r (e.symm (q v)) = q v
      exact e.apply_symm_apply (q v)
    have hsg : ∀ (g : G) (v : V), s (μ g v) = μ g (s v) := by
      intro g v
      apply hqW _ _ (hsW _) (W'.apply_mem_toSubmodule g (hsW v))
      rw [hqs', Representation.IntertwiningMap.isIntertwining _ _ q,
        Representation.IntertwiningMap.isIntertwining _ _ q, hqs']
    have hPX : ∀ v, v - s v ∈ X.toSubmodule := by
      intro v
      rw [← hq, map_sub, hqs', sub_self]
    let P : V →ₗ[ℂ] X.toSubmodule :=
      LinearMap.codRestrict X.toSubmodule (LinearMap.id - s) (fun v => hPX v)
    let φL : V →ₗ[ℂ] Y := a.toIntertwiningMap.toLinearMap ∘ₗ P
    have hPg : ∀ (g : G) (v : V), P (μ g v) = X.toRepresentation g (P v) := by
      intro g v
      apply Subtype.ext
      show μ g v - s (μ g v) = μ g (v - s v)
      rw [hsg, map_sub]
    have hφ : ∀ (g : G) (v : V), φL (μ g v) = τ g (φL v) := by
      intro g v
      show a.toIntertwiningMap (P (μ g v)) = τ g (a.toIntertwiningMap (P v))
      rw [hPg]
      exact Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g (P v)
    have hY : ∃ y : Y, y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      ext y
      rw [hcon y]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    obtain ⟨y, hy⟩ := hY
    refine ⟨φL.intertwiningMap_of_isIntertwiningMap μ τ hφ, ((a.symm y : X.toSubmodule) : V), ?_⟩
    show a.toIntertwiningMap (P _) ≠ 0
    have hq0 : q ((a.symm y : X.toSubmodule) : V) = 0 := (hq _).2 (a.symm y).2
    have hs0 : s ((a.symm y : X.toSubmodule) : V) = 0 := by
      show ((e.symm (q _) : W'.toSubmodule) : V) = 0
      rw [hq0, map_zero]
      rfl
    have hP0 : P ((a.symm y : X.toSubmodule) : V) = a.symm y := by
      apply Subtype.ext
      show ((a.symm y : X.toSubmodule) : V) - s ((a.symm y : X.toSubmodule) : V) = ((a.symm y : X.toSubmodule) : V)
      rw [hs0, sub_zero]
    rw [hP0]
    change a (a.symm y) ≠ 0
    rw [a.apply_symm_apply]
    exact hy
  · exfalso
    apply hAB
    have hXW : ∀ x ∈ X.toSubmodule, x ∈ W'.toSubmodule := by
      intro x hx
      have h1 : a ⟨x, hx⟩ ∈ P'.toSubmodule := by rw [hP]; exact Submodule.mem_top
      rw [Submodule.mem_comap] at h1
      have h2 : ((a.symm (a ⟨x, hx⟩) : X.toSubmodule) : V) ∈ W'.toSubmodule := h1
      rw [a.symm_apply_apply] at h2
      exact h2
    let f : τ.IntertwiningMap W'.toRepresentation :=
      ⟨LinearMap.codRestrict W'.toSubmodule (X.toSubmodule.subtype ∘ₗ a.symm.toIntertwiningMap.toLinearMap)
        (fun y => hXW _ (a.symm y).2), fun g => by
          refine LinearMap.ext fun y => ?_
          apply Subtype.ext
          show ((a.symm.toIntertwiningMap (τ g y) : X.toSubmodule) : V) =
            μ g ((a.symm.toIntertwiningMap y : X.toSubmodule) : V)
          rw [Representation.IntertwiningMap.isIntertwining _ _ a.symm.toIntertwiningMap g y]
          rfl⟩
    have hfi : Function.Injective f := by
      intro y1 y2 h12
      have h4 : ((f y1 : W'.toSubmodule) : V) = ((f y2 : W'.toSubmodule) : V) := congrArg Subtype.val h12
      have h3 : a.symm y1 = a.symm y2 := Subtype.ext h4
      rw [← a.apply_symm_apply y1, ← a.apply_symm_apply y2, h3]
    have hsub1 : IsSubquotient τ W'.toRepresentation := GlobalTheory.SmGL.IsSubquotient.of_injective f hfi
    have hsub2 := GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hsub1 ψ
    have hsub3 := GlobalTheory.SmGL.IsSubquotient.trans hBτ hsub2
    have hspan : Submodule.span ℂ {u : W'.toSubmodule |
        ∃ (ι : A.IntertwiningMap (W'.toRepresentation.comp ψ)) (w : W₀), ι w = u} = ⊤ := by
      apply Submodule.map_injective_of_injective W'.toSubmodule.injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top]
      refine Eq.trans ?_ hWspan.symm
      congr 1
      ext u
      constructor
      · rintro ⟨u', ⟨ι, w, rfl⟩, rfl⟩
        refine ⟨⟨W'.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun g => LinearMap.ext fun w' => ?_⟩, w, rfl⟩
        exact congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ ι g w')
      · rintro ⟨ι, w, rfl⟩
        refine ⟨⟨ι w, hmemW ι w⟩, ⟨⟨LinearMap.codRestrict W'.toSubmodule ι.toLinearMap (fun w' => hmemW ι w'),
          fun g => LinearMap.ext fun w' => ?_⟩, w, rfl⟩, rfl⟩
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ ι g w'
    exact GlobalTheory.LocGL.SupportUnique.isSubquotient_of_span hB hsub3 hspan

/- English proof (translation)
Use `le_antisymm (fun x hx => ?_) hBA` and prove the remaining obligations. Establish `h1 : (Submodule.Quotient.mk ⟨x, hx⟩ : A.toSubmodule ⧸ B.toSubmodule.comap A.toSubmodule.subtype) = 0` using `Subsingleton.elim _ _`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `h1`.
-/
theorem eq_of_subsingleton_step {μ : Representation ℂ G V} {A B : Subrepresentation μ} (hBA : B ≤ A)
    (h : Subsingleton (A.toSubmodule ⧸ B.toSubmodule.comap A.toSubmodule.subtype)) : A = B := by
  refine le_antisymm (fun x hx => ?_) hBA
  have h1 : (Submodule.Quotient.mk ⟨x, hx⟩ : A.toSubmodule ⧸ B.toSubmodule.comap A.toSubmodule.subtype) = 0 :=
    Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

/- English proof (translation)
Establish `hij' : i.val ≤ j.val` using `hij`. Establish `key : ∀ k : ℕ, ∀ hk : i.val + k < N + 1, i.val + k ≤ j.val → S i = S ⟨i.val + k, hk⟩`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `hk _`. Both sides reduce to the same expression. Consider the case `succ k ih`. Introduce `hk hkj`. Establish `hk' : i.val + k < N` using `by omega`.

Rewrite using `[ih (by omega) (by omega)]`. Establish `hst` using `h ⟨i.val + k, hk'⟩ (by rw [Fin.le_def]; exact Nat.le_add_right _ _) (by rw [Fin.le_def]; show i.val + k + 1 ≤ j.val; omega)`. Establish `e` using `eq_of_subsingleton_step (hS (Fin.castSucc_le_succ (⟨i.val + k, hk'⟩ : Fin N))) hst`. Conclude with `e.symm`. Rewrite using `[key (j.val - i.val) (by omega) (by omega)]`.

Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Use `show i.val + (j.val - i.val) = j.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_steps {μ : Representation ℂ G V} {N : ℕ} (S : Fin (N + 1) → Subrepresentation μ) (hS : Monotone S)
    (i j : Fin (N + 1)) (hij : i ≤ j)
    (h : ∀ t : Fin N, i ≤ t.castSucc → t.succ ≤ j → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype)) : S i = S j := by
  have hij' : i.val ≤ j.val := hij
  have key : ∀ k : ℕ, ∀ hk : i.val + k < N + 1, i.val + k ≤ j.val → S i = S ⟨i.val + k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk _
      rfl
    | succ k ih =>
      intro hk hkj
      have hk' : i.val + k < N := by omega
      rw [ih (by omega) (by omega)]
      have hst := h ⟨i.val + k, hk'⟩ (by rw [Fin.le_def]; exact Nat.le_add_right _ _)
        (by rw [Fin.le_def]; show i.val + k + 1 ≤ j.val; omega)
      have e := eq_of_subsingleton_step (hS (Fin.castSucc_le_succ (⟨i.val + k, hk'⟩ : Fin N))) hst
      exact e.symm
  rw [key (j.val - i.val) (by omega) (by omega)]
  congr 1
  apply Fin.ext
  show i.val + (j.val - i.val) = j.val
  omega

/- English proof (translation)
Establish `htop : S t₀.succ = ⊤`. Rewrite using `[← hN]`. Apply `eq_of_steps S hS t₀.succ (Fin.last N) (Fin.le_last _)` to reduce the goal to its premises. Introduce `t ht1 _`. Apply `h t` to reduce the goal to its premises.

Establish `h2 : t₀.val + 1 ≤ t.val` using `ht1`. Conclude with `(show t₀.val < t.val by omega)`. Take `⟨q, hqs, _⟩` from `exists_quot_map (S t₀.castSucc) (S t₀.succ) htop E`. Take `⟨y, hy⟩` from `exists_ne (0 : Y)`. Take `⟨v, rfl⟩` from `hqs y`.

Conclude with `⟨q, v, hy⟩`.
-/
theorem exists_map_of_top {μ : Representation ℂ G V} {τ : Representation ℂ G Y} [Nontrivial Y] {N : ℕ}
    (S : Fin (N + 1) → Subrepresentation μ) (hS : Monotone S) (hN : S (Fin.last N) = ⊤) (t₀ : Fin N)
    (h : ∀ t : Fin N, t₀ < t → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype))
    (E : (subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) : ∃ (φ : μ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  have htop : S t₀.succ = ⊤ := by
    rw [← hN]
    apply eq_of_steps S hS t₀.succ (Fin.last N) (Fin.le_last _)
    intro t ht1 _
    apply h t
    have h2 : t₀.val + 1 ≤ t.val := ht1
    exact (show t₀.val < t.val by omega)
  obtain ⟨q, hqs, _⟩ := exists_quot_map (S t₀.castSucc) (S t₀.succ) htop E
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hqs y
  exact ⟨q, v, hy⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

end
