import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

section Generic
variable {O : Type} [CommRing O] [StarRing O]

omit [StarRing O] in

/- English proof (translation)
Set `_ : Module O V` to `Module.compHom V F`. Establish `e0 : ex 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`.

Establish `c0 : c 0 = 1`. Use `hc 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`. Set `P : Submodule O (X × V)` to `{ carrier := {p | ex p.2 = c p.1} zero_mem' := e0.trans c0.symm add_mem' := fun {p q} hp hq => by`.

Express the relevant statement in the definitionally equal form `ex (p.2 + q.2) = c (p.1 + q.1)`. Rewrite using `[hadd, hc, (show ex p.2 = _ from hp), (show ex q.2 = _ from hq)]`. Use the proof step `smul_mem' := fun a p hp => hl a p.1 p.2 hp }`. Take `⟨g, hg⟩` from `GlobalTheory.Forms.exists_linearMap_lift_of_int (LinearMap.fst O X V ∘ₗ P.subtype) (fun x => by`. Take `⟨z, hz⟩` from `hs (c x)`.

Conclude with `⟨⟨(x, z), hz⟩, rfl⟩) LinearMap.id`. Use `⟨(LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).toAddMonoidHom, fun a x => (LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).map_smul a x, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (g x).1.1 = x` using `hg x`. Establish `h2 : ex (g x).1.2 = c (g x).1.1` using `(g x).2`. Rewrite `h2` using `[h1]`.

Conclude with `h2.symm`.
-/
theorem exists_lift_ct [IsDedekindDomain O] [Module.Finite ℤ O] {V G X : Type} [AddCommGroup V] [Module ℂ V] [CommGroup G]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (F : O →+* Module.End ℂ V) (ex : V → G)
    (hadd : ∀ z w, ex (z + w) = ex z * ex w) (hs : Function.Surjective ex) (c : X → G)
    (hc : ∀ x y, c (x + y) = c x * c y) (hl : ∀ (a : O) x z, ex z = c x → ex (F a z) = c (a • x)) :
    ∃ ct : X →+ V, (∀ (a : O) x, ct (a • x) = F a (ct x)) ∧ ∀ x, c x = ex (ct x) := by
  let _ : Module O V := Module.compHom V F
  have e0 : ex 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have c0 : c 0 = 1 := by
    have := hc 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let P : Submodule O (X × V) :=
    { carrier := {p | ex p.2 = c p.1}
      zero_mem' := e0.trans c0.symm
      add_mem' := fun {p q} hp hq => by
        change ex (p.2 + q.2) = c (p.1 + q.1)
        rw [hadd, hc, (show ex p.2 = _ from hp), (show ex q.2 = _ from hq)]
      smul_mem' := fun a p hp => hl a p.1 p.2 hp }
  obtain ⟨g, hg⟩ := GlobalTheory.Forms.exists_linearMap_lift_of_int (LinearMap.fst O X V ∘ₗ P.subtype)
    (fun x => by
      obtain ⟨z, hz⟩ := hs (c x)
      exact ⟨⟨(x, z), hz⟩, rfl⟩) LinearMap.id
  refine ⟨(LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).toAddMonoidHom,
    fun a x => (LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).map_smul a x, fun x => ?_⟩
  have h1 : (g x).1.1 = x := hg x
  have h2 : ex (g x).1.2 = c (g x).1.1 := (g x).2
  rw [h1] at h2
  exact h2.symm

/- English proof (translation)
Use `GlobalTheory.Forms.projective_of_int O X` as an intermediate fact. Establish `: Module.Finite O X` using `Module.Finite.of_restrictScalars_finite ℤ O X`. Take `⟨T, h1, h2, h3⟩` from `GlobalTheory.Forms.exists_log_of_bimul hw (fun x y : X => N.τ (e x) (e y) * fr (ct x + ct y) / fr (ct x) / fr (ct y)) (fun y x x' => by`. Establish `a` using `congrArg Additive.ofMul (N.τ_add_right (e y) (e x) (e x'))`. Establish `b` using `congrArg Additive.ofMul (hab.2.2.2.2.2.1 (ct x) (ct x') (ct y))`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [hc, map_add, add_comm (ct y), ofMul_mul, ofMul_div] at a b ⊢`. Take the linear combination `(norm := abel) a - b)`. Use the proof step `(fun y x => by rw [N.τ_symm, add_comm, div_right_comm])`. Use the proof step `(fun a y x => by`.

Establish `b` using `hbal a y x`. Simplify using `only [← Units.val_mul, Units.val_inj] at b`. Use `replace b := congrArg Additive.ofMul b`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div] at b ⊢`.

Take the linear combination `(norm := abel) b)`. Use `⟨AddMonoidHom.mk' (fun x => (T x).toAddMonoidHom) fun x y => by ext; simp, h1, h2, fun x y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (2 * Real.pi * Complex.I * T x y) * _ * _ = _`. Rewrite using `[← h3]`. Simplify using `only [← Units.val_mul, Units.val_inj]`.

Rewrite using `[mul_right_comm, div_mul_cancel, div_mul_cancel]`.
-/
theorem exists_log_frame [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O] {N : NumD ℂ} {B : AnArc O}
    {ex : (Fin B.gB → ℂ) → N.A} {fr : (Fin B.gB → ℂ) → ℂˣ} {th : (Fin B.gB → ℂ) → ℂ} (hab : IsAbFrame N.toNumB B ex fr th)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (e : X ≃+ N.X)
    (ct : X →+ (Fin B.gB → ℂ)) (hc : ∀ x, N.c (e x) = ex (ct x)) {w : O} (hw : w + star w = 1)
    (hbal : ∀ (a : O) y x, (N.τ (e (a • y)) (e x) : ℂ) * fr (ct (a • y) + ct x) * fr (ct y) * fr (ct (star a • x)) =
      N.τ (e y) (e (star a • x)) * fr (ct y + ct (star a • x)) * fr (ct (a • y)) * fr (ct x)) :
    ∃ T : X →+ X →+ ℂ, (∀ x y, T x y = T y x) ∧ (∀ (a : O) y x, T (a • y) x = T y (star a • x)) ∧
      ∀ x y, eTwoPi (T x y) * fr (ct x) * fr (ct y) = N.τ (e x) (e y) * fr (ct x + ct y) := by
  have := GlobalTheory.Forms.projective_of_int O X
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  obtain ⟨T, h1, h2, h3⟩ := GlobalTheory.Forms.exists_log_of_bimul hw
    (fun x y : X => N.τ (e x) (e y) * fr (ct x + ct y) / fr (ct x) / fr (ct y))
    (fun y x x' => by
      have a := congrArg Additive.ofMul (N.τ_add_right (e y) (e x) (e x'))
      have b := congrArg Additive.ofMul (hab.2.2.2.2.2.1 (ct x) (ct x') (ct y))
      apply Additive.ofMul.injective
      simp only [hc, map_add, add_comm (ct y), ofMul_mul, ofMul_div] at a b ⊢
      linear_combination (norm := abel) a - b)
    (fun y x => by rw [N.τ_symm, add_comm, div_right_comm])
    (fun a y x => by
      have b := hbal a y x
      simp only [← Units.val_mul, Units.val_inj] at b
      replace b := congrArg Additive.ofMul b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div] at b ⊢
      linear_combination (norm := abel) b)
  refine ⟨AddMonoidHom.mk' (fun x => (T x).toAddMonoidHom) fun x y => by ext; simp, h1, h2, fun x y => ?_⟩
  change Complex.exp (2 * Real.pi * Complex.I * T x y) * _ * _ = _
  rw [← h3]
  simp only [← Units.val_mul, Units.val_inj]
  rw [mul_right_comm, div_mul_cancel, div_mul_cancel]

end Generic

/- English proof (translation)
Introduce `hBr hVal E _ _ _ H D R _ _ _ A k β hβ`. Set `_` to `H.starRing`. Take `⟨B, ex, fr, th, hab, hth, hchi, hsig, hF, hros, hprim⟩` from `hVal E H D R A`. Use `A.closed` as an intermediate fact. Take `⟨b1, b2, b3⟩` from `hBr R A.D₀ A.even A.bimult ℂ A.N A.ν (𝓞 E) A.oa`.

Use `A.D₀.freeX` as an intermediate fact. Use `A.D₀.finX` as an intermediate fact. Use `set e : A.D₀.X ≃+ A.N.X := A.ν.eX.symm with he`. Establish `hee : ∀ x, A.ν.eX (e x) = x` using `A.ν.eX.apply_symm_apply`. Establish `hw : H.w0 + star H.w0 = 1` using `by show H.w0 + H.bar H.w0 = 1`.

Rewrite using `[GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]`. Take `⟨ct, hct, hc⟩` from `exists_lift_ct B.F ex hab.1 hab.2.1 (fun x : A.D₀.X => A.N.c (e x)) (fun x y => by rw [map_add, A.N.c_add]) (fun a x z hz => A.ν.eA.injective (by`. Rewrite using `[hF, hz, A.ν.c_eq, A.ν.c_eq, hee, hee, DegPre.cF, DegPre.cF, A.oa.c_lin, Category.assoc]))`. Take `⟨T, hT1, hT2, hT⟩` from `exists_log_frame hab e ct hc hw (fun a y x => by`. Take `⟨r, hr, h⟩` from `b1 a`.

Establish `h1` using `h (e y) (e x)`. Establish `h2` using `hros a (star a) r hr (ct y) (ct x)`. Rewrite `h1` using `[hee, hee, hc, hc]`. Rewrite using `[← h1, hct, hct]`. Take the linear combination `-(A.N.τ (e (a • y)) (e x) : ℂ) * h2)`.

Establish `hact : ∀ (a : 𝓞 E) x, e (a • x) = A.act a (e x)` using `fun a x => by rw [ArcF.act, hee]`. Set `B' : An H` to `{ B with X := A.D₀.X acg := inferInstance free := inferInstance fin := inferInstance mod := inferInstance ct := ct ct_smul := hct T := T T_symm := hT1 T_adj := hT2 psi := fun x => A.N.ψ (e x) * fr (ct x) psi_neg := fun x => by`. Rewrite using `[map_neg, map_neg, ← hab.2.2.2.2.2.2.1, ← hc, ← _root_.mul_assoc, A.N.even]`. Use `psi_add := fun x y => by`. Establish `h` using `hT x y`.

Rewrite using `[map_add, map_add, A.N.ψ_add]`. Use `push_cast`. Take the linear combination `-(A.N.ψ (e x) : ℂ) * A.N.ψ (e y) * h`. Use `be := β.be.comp e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap`. Use `be_symm := fun x y => β.symm _ _`.

Use `be_pos := fun x hx => β.pos _ fun h => hx (e.map_eq_zero_iff.1 h)`. Use `be_adj := fun a y x => by`. Express the relevant statement in the definitionally equal form `β.be (e (a • y)) (e x) = β.be (e y) (e (star a • x))`. Rewrite using `[hact, hact]`. Conclude with `hβ a _ _`.

Use `be_even := fun x => (dvd_mul_right 2 (k : ℤ)).trans (β.dvd _ _) }`. Establish `hab' : IsAbFrame A.N.toNumB B' ex fr th`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩` from `hab`. Use `⟨a1, a2, a3, a4, a5, a6, a7, ⟨a8.1, fun l z => ?_⟩, a9⟩` and prove the remaining obligations. Use `a8.2 l z` as an intermediate fact.

Rewrite `this`, the goal using `[map_zero]`. Conclude with `this`. Use `⟨B', ⟨e, ex, fr, th, hab', hc, fun _ => rfl⟩, ⟨hact, ?_⟩, fun _ _ => rfl, ⟨hw, hchi, fun y => ?_⟩, hth, hsig⟩` and prove the remaining obligations. Introduce and unpack `a g g' c c' v hg hg' hgg ⟨hv1, hv2⟩`. Take `⟨r, hr, h⟩` from `b2 a`.

Take `⟨h1, h2⟩` from `h g g' c c' hg hg' hgg`. Express the relevant statement in the definitionally equal form `c.b = ex v.2 at hv1`. Use `⟨A.ν.eA.injective (by rw [h1, hv1]; exact (hF a v.2).symm), fun x : A.D₀.X => ?_⟩` and prove the remaining obligations. Establish `h3` using `h2 (e x)`. Establish `h4 : (c.s (e (star a • x)) : ℂ) * fr (ct (star a • x) + v.2) = eTwoPi (v.1 (star a • x)) * fr (ct (star a • x)) * fr v.2` using `hv2 (star a • x)`.

Establish `h5` using `hros (star a) a r hr (ct x) v.2`. Rewrite `h3` using `[hee, hc, hv1]`. Rewrite `h4` using `[hct]`. Express the relevant statement in the definitionally equal form `(c'.s (e x) : ℂ) * fr (ct x + B.F a v.2) = eTwoPi (v.1 (star a • x)) * fr (ct x) * fr (B.F a v.2)`. Use `mul_right_cancel₀ (mul_ne_zero (fr (B.F (star a) (ct x))).ne_zero (fr v.2).ne_zero) ?_` and prove the remaining obligations.

Rewrite using `[h3]`. Take the linear combination `(c.s (e (star a • x)) : ℂ) * h5 + (fr (ct x) : ℂ) * fr (B.F a v.2) * h4`. Take `⟨t, ht, h⟩` from `b3 H.w0 A.w0`. Establish `h1` using `h (e y)`. Establish `h2` using `hprim t ht (ct y)`.

Establish `h3` using `hT y (H.w0 • y)`. Rewrite `h1` using `[hee, hc]`. Rewrite `h3` using `[hct]`. Express the relevant statement in the definitionally equal form `((A.N.ψ (e y) * fr (ct y) : ℂˣ) : ℂ) = eTwoPi (T y (H.w0 • y))`. Use `mul_right_cancel₀ (mul_ne_zero (fr (ct y)).ne_zero (fr (B.F H.w0 (ct y))).ne_zero) ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, ← h1]`. Take the linear combination `(A.N.τ (e y) (e (H.w0 • y)) : ℂ) * h2 - h3`.
-/
theorem dict_of_val : BrActSt → ValSt → DictSt := by
  intro hBr hVal E _ _ _ H D R _ _ _ A k β hβ
  let _ := H.starRing
  obtain ⟨B, ex, fr, th, hab, hth, hchi, hsig, hF, hros, hprim⟩ := hVal E H D R A
  have := A.closed
  obtain ⟨b1, b2, b3⟩ := hBr R A.D₀ A.even A.bimult ℂ A.N A.ν (𝓞 E) A.oa
  have := A.D₀.freeX
  have := A.D₀.finX
  set e : A.D₀.X ≃+ A.N.X := A.ν.eX.symm with he
  have hee : ∀ x, A.ν.eX (e x) = x := A.ν.eX.apply_symm_apply
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  obtain ⟨ct, hct, hc⟩ := exists_lift_ct B.F ex hab.1 hab.2.1 (fun x : A.D₀.X => A.N.c (e x))
    (fun x y => by rw [map_add, A.N.c_add]) (fun a x z hz => A.ν.eA.injective (by
      rw [hF, hz, A.ν.c_eq, A.ν.c_eq, hee, hee, DegPre.cF, DegPre.cF, A.oa.c_lin, Category.assoc]))
  obtain ⟨T, hT1, hT2, hT⟩ := exists_log_frame hab e ct hc hw (fun a y x => by
    obtain ⟨r, hr, h⟩ := b1 a
    have h1 := h (e y) (e x)
    have h2 := hros a (star a) r hr (ct y) (ct x)
    rw [hee, hee, hc, hc] at h1
    rw [← h1, hct, hct]
    linear_combination -(A.N.τ (e (a • y)) (e x) : ℂ) * h2)
  have hact : ∀ (a : 𝓞 E) x, e (a • x) = A.act a (e x) := fun a x => by rw [ArcF.act, hee]
  let B' : An H :=
    { B with
      X := A.D₀.X
      acg := inferInstance
      free := inferInstance
      fin := inferInstance
      mod := inferInstance
      ct := ct
      ct_smul := hct
      T := T
      T_symm := hT1
      T_adj := hT2
      psi := fun x => A.N.ψ (e x) * fr (ct x)
      psi_neg := fun x => by
        rw [map_neg, map_neg, ← hab.2.2.2.2.2.2.1, ← hc, ← _root_.mul_assoc, A.N.even]
      psi_add := fun x y => by
        have h := hT x y
        rw [map_add, map_add, A.N.ψ_add]
        push_cast
        linear_combination -(A.N.ψ (e x) : ℂ) * A.N.ψ (e y) * h
      be := β.be.comp e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap
      be_symm := fun x y => β.symm _ _
      be_pos := fun x hx => β.pos _ fun h => hx (e.map_eq_zero_iff.1 h)
      be_adj := fun a y x => by
        change β.be (e (a • y)) (e x) = β.be (e y) (e (star a • x))
        rw [hact, hact]
        exact hβ a _ _
      be_even := fun x => (dvd_mul_right 2 (k : ℤ)).trans (β.dvd _ _) }
  have hab' : IsAbFrame A.N.toNumB B' ex fr th := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hab
    refine ⟨a1, a2, a3, a4, a5, a6, a7, ⟨a8.1, fun l z => ?_⟩, a9⟩
    have := a8.2 l z
    rw [map_zero] at this ⊢
    exact this
  refine ⟨B', ⟨e, ex, fr, th, hab', hc, fun _ => rfl⟩, ⟨hact, ?_⟩, fun _ _ => rfl, ⟨hw, hchi, fun y => ?_⟩, hth, hsig⟩
  · rintro a g g' c c' v hg hg' hgg ⟨hv1, hv2⟩
    obtain ⟨r, hr, h⟩ := b2 a
    obtain ⟨h1, h2⟩ := h g g' c c' hg hg' hgg
    change c.b = ex v.2 at hv1
    refine ⟨A.ν.eA.injective (by rw [h1, hv1]; exact (hF a v.2).symm), fun x : A.D₀.X => ?_⟩
    have h3 := h2 (e x)
    have h4 : (c.s (e (star a • x)) : ℂ) * fr (ct (star a • x) + v.2) =
      eTwoPi (v.1 (star a • x)) * fr (ct (star a • x)) * fr v.2 := hv2 (star a • x)
    have h5 := hros (star a) a r hr (ct x) v.2
    rw [hee, hc, hv1] at h3
    rw [hct] at h4
    change (c'.s (e x) : ℂ) * fr (ct x + B.F a v.2) = eTwoPi (v.1 (star a • x)) * fr (ct x) * fr (B.F a v.2)
    refine mul_right_cancel₀ (mul_ne_zero (fr (B.F (star a) (ct x))).ne_zero (fr v.2).ne_zero) ?_
    rw [h3]
    linear_combination (c.s (e (star a • x)) : ℂ) * h5 + (fr (ct x) : ℂ) * fr (B.F a v.2) * h4
  · obtain ⟨t, ht, h⟩ := b3 H.w0 A.w0
    have h1 := h (e y)
    have h2 := hprim t ht (ct y)
    have h3 := hT y (H.w0 • y)
    rw [hee, hc] at h1
    rw [hct] at h3
    change ((A.N.ψ (e y) * fr (ct y) : ℂˣ) : ℂ) = eTwoPi (T y (H.w0 • y))
    refine mul_right_cancel₀ (mul_ne_zero (fr (ct y)).ne_zero (fr (B.F H.w0 (ct y))).ne_zero) ?_
    rw [Units.val_mul, ← h1]
    linear_combination (A.N.τ (e y) (e (H.w0 • y)) : ℂ) * h2 - h3

end GlobalTheory.Ex.Arch
end
