import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}

/- English proof (translation)
Take `⟨φ, hφ⟩` from `val_ringHom s U x hx hc`. Rewrite using `[← hφ, eval₂_comp_left]`. Establish `h1 : φ.comp (constSec s U) = RingHom.id ℂ`. Use extensionality with `c`. Simplify using `only [RingHom.comp_apply, hφ, RingHom.id_apply]`.

Conclude with `val_const s U x hx hc c`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `eval₂ (RingHom.id ℂ) (φ ∘ u) F = eval₂ (RingHom.id ℂ) _ F`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Conclude with `hφ (u t)`.
-/
theorem val_eval₂ {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] {U : S.Opens}
    {σ : Type} (u : σ → Γ(S, U)) (F : MvPolynomial σ ℂ) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    val s (eval₂ (constSec s U) u F) x hx = eval (fun t => val s (u t) x hx) F := by
  obtain ⟨φ, hφ⟩ := val_ringHom s U x hx hc
  rw [← hφ, eval₂_comp_left]
  have h1 : φ.comp (constSec s U) = RingHom.id ℂ := by
    ext c
    simp only [RingHom.comp_apply, hφ, RingHom.id_apply]
    exact val_const s U x hx hc c
  rw [h1]
  change eval₂ (RingHom.id ℂ) (φ ∘ u) F = eval₂ (RingHom.id ℂ) _ F
  congr 1
  funext t
  exact hφ (u t)

namespace AffPres

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫ P.iso.hom.appTop ≫ P.V.topIso.hom = (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top`. Rewrite using `[← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]`. Simplify using `only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]`. Both sides reduce to the same expression. Establish `e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫ (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫ P.iso.hom.appTop ≫ P.V.topIso.hom) c` using `rfl`.

Rewrite using `[e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]`. Both sides reduce to the same expression.
-/
theorem secHom_C (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top := by
    rw [← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]
    rfl
  have e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom) c := rfl
  rw [e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]
  rfl

/- English proof (translation)
Introduce `a`. Establish `h1 : Function.Surjective P.V.topIso.hom.hom` using `(ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2`. Establish `h2 : Function.Surjective (P.iso.hom.app ⊤).hom` using `(ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2`. Establish `h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2`. Take `⟨a1, rfl⟩` from `h1 a`.

Take `⟨a2, rfl⟩` from `h2 a1`. Take `⟨a3, rfl⟩` from `h3 a2`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective a3`. Conclude with `⟨f, rfl⟩`.
-/
theorem secHom_surjective (P : AffPres sW) : Function.Surjective P.secHom := by
  intro a
  have h1 : Function.Surjective P.V.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2
  have h2 : Function.Surjective (P.iso.hom.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  obtain ⟨a1, rfl⟩ := h1 a
  obtain ⟨a2, rfl⟩ := h2 a1
  obtain ⟨a3, rfl⟩ := h3 a2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a3
  exact ⟨f, rfl⟩

/- English proof (translation)
Take `⟨φ, hφ⟩` from `val_ringHom sW P.V y hy hc`. Establish `hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0`. Introduce `g hg`. Rewrite using `[val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]`. Apply `(IsLocalRing.residue_eq_zero_iff _).mpr` to reduce the goal to its premises.

Establish `h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈ (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc)`. Rewrite using `[P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]`. Conclude with `Ideal.mem_map_of_mem _ hg`. Take `⟨w, hw, hwe⟩` from `(Ideal.mem_map_of_equiv _ _).mp h2`. Rewrite `hw` using `[(P.stalkEquiv y hy hc).injective hwe]`.

Conclude with `hw`. Set `ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ` to `φ.comp P.secHom`. Establish `hψ : ∀ g, ψ g = val sW (P.secHom g) y hy` using `fun g => hφ _`. Establish `hC : ∀ c, ψ (C c) = c` using `fun c => by`. Rewrite using `[hψ, secHom_C, val_const sW P.V y hy hc]`.

Establish `hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j` using `fun j => by`. Establish `hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy)`. Simplify using `[ptIdeal, RingHom.mem_ker]`. Use `hker _ hm` as an intermediate fact. Rewrite `this` using `[← hψ, map_sub, hC, sub_eq_zero]`.

Conclude with `this`. Establish `hext : ψ = MvPolynomial.eval (P.coord y hy)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Rewrite using `[hC, eval_C]`.

Introduce `j`. Rewrite using `[hX, eval_X]`. Rewrite using `[← hψ, hext]`.
-/
theorem val_secHom [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by
  obtain ⟨φ, hφ⟩ := val_ringHom sW P.V y hy hc
  have hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0 := by
    intro g hg
    rw [val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    have h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈
        (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc) := by
      rw [P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_of_equiv _ _).mp h2
    rw [(P.stalkEquiv y hy hc).injective hwe] at hw
    exact hw
  let ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ := φ.comp P.secHom
  have hψ : ∀ g, ψ g = val sW (P.secHom g) y hy := fun g => hφ _
  have hC : ∀ c, ψ (C c) = c := fun c => by
    rw [hψ, secHom_C, val_const sW P.V y hy hc]
  have hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j := fun j => by
    have hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy) := by
      simp [ptIdeal, RingHom.mem_ker]
    have := hker _ hm
    rw [← hψ, map_sub, hC, sub_eq_zero] at this
    exact this
  have hext : ψ = MvPolynomial.eval (P.coord y hy) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hψ, hext]

end AffPres

/- English proof (translation)
Consider the cases of `nonempty_fintype ι`. Set `z : V` to `⟨g.base x, hxV⟩`. Set `: Algebra Γ(T, V) (T.presheaf.stalk (g.base x))` to `TopCat.Presheaf.algebra_section_stalk T.presheaf z`. Establish `: IsLocalization.AtPrime (T.presheaf.stalk (g.base x)) (hV.primeIdealOf z).asIdeal` using `hV.isLocalization_stalk z`. Establish `hw : ∀ i, ∃ w : T.presheaf.stalk (g.base x), g.stalkMap x w = S.presheaf.germ Ω x hxΩ (e i)` using `fun i => hsurj _`.

Use `choose w hw using hw`. Take `⟨⟨b, hb⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (hV.primeIdealOf z).asIdeal.primeCompl w`. Establish `hint' : ∀ i, ∃ a : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) a = b • w i` using `fun i => hint i`. Use `choose a ha using hint'`. Establish `halg : ∀ c : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) c = T.presheaf.germ V (g.base x) hxV c` using `fun c => rfl`.

Establish `hunit : IsUnit (T.presheaf.germ V (g.base x) hxV b)`. Rewrite using `[← halg]`. Conclude with `IsLocalization.map_units (T.presheaf.stalk (g.base x)) (⟨b, hb⟩ : (hV.primeIdealOf z).asIdeal.primeCompl)`. Set `Ω' : S.Opens` to `Ω ⊓ g ⁻¹ᵁ V`. Establish `hΩ'V : Ω' ≤ g ⁻¹ᵁ V` using `inf_le_right`.

Establish `hΩ'Ω : Ω' ≤ Ω` using `inf_le_left`. Establish `hxΩ' : x ∈ Ω'` using `⟨hxΩ, hxV⟩`. Establish `hgerm : ∀ c : Γ(T, V), S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V c) = g.stalkMap x (T.presheaf.germ V (g.base x) hxV c)`. Introduce `c`. Rewrite using `[Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]`.

Establish `hEq : ∀ i, S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V b * S.presheaf.map (homOfLE hΩ'Ω).op (e i)) = S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V (a i))`. Introduce `i`. Rewrite using `[map_mul, hgerm, hgerm, TopCat.Presheaf.germ_res_apply, ← hw i, ← map_mul]`. Use `congr 1`. Rewrite using `[← halg, ← halg, ha i, Algebra.smul_def]`.

Establish `hO` using `fun i => TopCat.Presheaf.germ_eq S.presheaf x hxΩ' hxΩ' _ _ (hEq i)`. Use `choose Oi hxOi iU iV hOi using hO`. Take `⟨q, hq⟩` from `hu b`. Use `choose F hF using fun i => hu (a i)`. Set `O : S.Opens` to `(g ⁻¹ᵁ T.basicOpen b) ⊓ Ω' ⊓ Finset.univ.inf Oi`.

Establish `hmemO : ∀ y, y ∈ O → y ∈ g ⁻¹ᵁ T.basicOpen b ∧ y ∈ Ω' ∧ ∀ i, y ∈ Oi i`. Introduce `y hy`. Use `⟨hy.1.1, hy.1.2, fun i => ?_⟩` and prove the remaining obligations. Establish `h2` using `hy.2`. Rewrite `h2` using `[TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]`.

Simplify using `only [Set.iInf_eq_iInter, Set.mem_iInter] at h2`. Conclude with `h2 i (Finset.mem_univ i)`. Establish `hne : ∀ (y : S) (hyV : g.base y ∈ V), IsClosed ({y} : Set S) → g.base y ∈ T.basicOpen b → eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0`. Introduce `y hyV hcy hyb`. Establish `hcy'` using `isClosed_image_of_closed s t g hg y hcy`.

Rewrite using `[← val_eval₂ t u q _ hyV hcy', ← hq]`. Introduce `h0`. Rewrite `h0` using `[val_eq_zero_iff t b _ hyV hcy', ← Scheme.germ_residue, CommRingCat.comp_apply]`. Establish `hu'` using `(T.mem_basicOpen b (g.base y) hyV).mp hyb`. Conclude with `(hu'.map (T.residue (g.base y)).hom).ne_zero h0`.

Use `⟨O, ?_, fun y hy => (hmemO y hy).2.1, q, F, ?_, ?_⟩` and prove the remaining obligations. Use `⟨⟨?_, hxΩ'⟩, ?_⟩` and prove the remaining obligations. Conclude with `(T.mem_basicOpen b (g.base x) hxV).mpr hunit`. Use `show x ∈ ((Finset.univ.inf Oi : S.Opens) : Set S)`. Rewrite using `[TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]`.

Simplify using `only [Set.iInf_eq_iInter, Set.mem_iInter]`. Conclude with `fun i _ => hxOi i`. Conclude with `hne x hxV hc ((T.mem_basicOpen b (g.base x) hxV).mpr hunit)`. Introduce `y hyΩ hyV hyO hcy`. Take `⟨hyb, hyΩ', hyOi⟩` from `hmemO y hyO`.

Establish `hcy'` using `isClosed_image_of_closed s t g hg y hcy`. Use `⟨hne y hyV hcy hyb, fun i => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `val_ringHom s Ω' y hyΩ' hcy`. Establish `h1` using `congrArg (fun f => val s f y (hyOi i)) (hOi i)`. Simplify using `only at h1`.

Rewrite `h1` using `[show iU i = homOfLE (leOfHom (iU i)) from rfl, show iV i = homOfLE (leOfHom (iV i)) from rfl, val_restrict, val_restrict, ← hφ, map_mul, hφ, hφ, val_restrict]`. Rewrite `h1` using `[(val_comp s t g hg hΩ'V b y hyΩ' hcy).2, (val_comp s t g hg hΩ'V (a i) y hyΩ' hcy).2]`. Establish `e1 : val t b (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) q`. Rewrite using `[hq]`. Conclude with `val_eval₂ t u q _ hyV hcy'`.

Establish `e2 : val t (a i) (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) (F i)`. Rewrite using `[hF i]`. Conclude with `val_eval₂ t u (F i) _ hyV hcy'`. Rewrite `h1` using `[e1, e2]`. Rewrite using `[mul_comm]`.

Conclude with `h1`.
-/
theorem exists_ratio_core {S T : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (t : T ⟶ Spec (.of ℂ))
    (g : S ⟶ T) (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (V : T.Opens) (hV : IsAffineOpen V) {σ : Type} (u : σ → Γ(T, V))
    (hu : ∀ a : Γ(T, V), ∃ F : MvPolynomial σ ℂ, a = eval₂ (constSec t V) u F)
    {ι : Type} [Finite ι] (Ω : S.Opens) (e : ι → Γ(S, Ω)) (x : S) (hxΩ : x ∈ Ω)
    (hxV : g.base x ∈ V) (hc : IsClosed ({x} : Set S))
    (hsurj : Function.Surjective (g.stalkMap x)) :
    ∃ O : S.Opens, x ∈ O ∧ O ≤ Ω ⊓ g ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial σ ℂ) (F : ι → MvPolynomial σ ℂ),
        eval (fun a => val t (u a) (g.base x) hxV) q ≠ 0 ∧
        ∀ (y : S) (hyΩ : y ∈ Ω) (hyV : g.base y ∈ V), y ∈ O → IsClosed ({y} : Set S) →
          eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 ∧
          ∀ i, val s (e i) y hyΩ * eval (fun a => val t (u a) (g.base y) hyV) q =
            eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
  classical
  cases nonempty_fintype ι
  let z : V := ⟨g.base x, hxV⟩
  let : Algebra Γ(T, V) (T.presheaf.stalk (g.base x)) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf z
  have : IsLocalization.AtPrime (T.presheaf.stalk (g.base x)) (hV.primeIdealOf z).asIdeal :=
    hV.isLocalization_stalk z
  have hw : ∀ i, ∃ w : T.presheaf.stalk (g.base x),
      g.stalkMap x w = S.presheaf.germ Ω x hxΩ (e i) := fun i => hsurj _
  choose w hw using hw
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (hV.primeIdealOf z).asIdeal.primeCompl w
  have hint' : ∀ i, ∃ a : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) a = b • w i :=
    fun i => hint i
  choose a ha using hint'
  have halg : ∀ c : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) c =
      T.presheaf.germ V (g.base x) hxV c := fun c => rfl
  have hunit : IsUnit (T.presheaf.germ V (g.base x) hxV b) := by
    rw [← halg]
    exact IsLocalization.map_units (T.presheaf.stalk (g.base x))
      (⟨b, hb⟩ : (hV.primeIdealOf z).asIdeal.primeCompl)
  let Ω' : S.Opens := Ω ⊓ g ⁻¹ᵁ V
  have hΩ'V : Ω' ≤ g ⁻¹ᵁ V := inf_le_right
  have hΩ'Ω : Ω' ≤ Ω := inf_le_left
  have hxΩ' : x ∈ Ω' := ⟨hxΩ, hxV⟩
  have hgerm : ∀ c : Γ(T, V), S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V c) =
      g.stalkMap x (T.presheaf.germ V (g.base x) hxV c) := by
    intro c
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hEq : ∀ i, S.presheaf.germ Ω' x hxΩ'
      (g.appLE V Ω' hΩ'V b * S.presheaf.map (homOfLE hΩ'Ω).op (e i)) =
      S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V (a i)) := by
    intro i
    rw [map_mul, hgerm, hgerm, TopCat.Presheaf.germ_res_apply, ← hw i, ← map_mul]
    congr 1
    rw [← halg, ← halg, ha i, Algebra.smul_def]
  have hO := fun i => TopCat.Presheaf.germ_eq S.presheaf x hxΩ' hxΩ' _ _ (hEq i)
  choose Oi hxOi iU iV hOi using hO
  obtain ⟨q, hq⟩ := hu b
  choose F hF using fun i => hu (a i)
  let O : S.Opens := (g ⁻¹ᵁ T.basicOpen b) ⊓ Ω' ⊓ Finset.univ.inf Oi
  have hmemO : ∀ y, y ∈ O → y ∈ g ⁻¹ᵁ T.basicOpen b ∧ y ∈ Ω' ∧ ∀ i, y ∈ Oi i := by
    intro y hy
    refine ⟨hy.1.1, hy.1.2, fun i => ?_⟩
    have h2 := hy.2
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf] at h2
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h2
    exact h2 i (Finset.mem_univ i)

  have hne : ∀ (y : S) (hyV : g.base y ∈ V), IsClosed ({y} : Set S) →
      g.base y ∈ T.basicOpen b → eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 := by
    intro y hyV hcy hyb
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    rw [← val_eval₂ t u q _ hyV hcy', ← hq]
    intro h0
    rw [val_eq_zero_iff t b _ hyV hcy', ← Scheme.germ_residue, CommRingCat.comp_apply] at h0
    have hu' := (T.mem_basicOpen b (g.base y) hyV).mp hyb
    exact (hu'.map (T.residue (g.base y)).hom).ne_zero h0
  refine ⟨O, ?_, fun y hy => (hmemO y hy).2.1, q, F, ?_, ?_⟩
  · refine ⟨⟨?_, hxΩ'⟩, ?_⟩
    · exact (T.mem_basicOpen b (g.base x) hxV).mpr hunit
    · show x ∈ ((Finset.univ.inf Oi : S.Opens) : Set S)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
      simp only [Set.iInf_eq_iInter, Set.mem_iInter]
      exact fun i _ => hxOi i
  · exact hne x hxV hc ((T.mem_basicOpen b (g.base x) hxV).mpr hunit)
  · intro y hyΩ hyV hyO hcy
    obtain ⟨hyb, hyΩ', hyOi⟩ := hmemO y hyO
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    refine ⟨hne y hyV hcy hyb, fun i => ?_⟩
    obtain ⟨φ, hφ⟩ := val_ringHom s Ω' y hyΩ' hcy
    have h1 := congrArg (fun f => val s f y (hyOi i)) (hOi i)
    simp only at h1
    rw [show iU i = homOfLE (leOfHom (iU i)) from rfl, show iV i = homOfLE (leOfHom (iV i)) from rfl,
      val_restrict, val_restrict, ← hφ, map_mul, hφ, hφ, val_restrict] at h1
    rw [(val_comp s t g hg hΩ'V b y hyΩ' hcy).2, (val_comp s t g hg hΩ'V (a i) y hyΩ' hcy).2] at h1
    have e1 : val t b (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) q := by
      rw [hq]; exact val_eval₂ t u q _ hyV hcy'
    have e2 : val t (a i) (g.base y) (hΩ'V hyΩ') =
        eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
      rw [hF i]; exact val_eval₂ t u (F i) _ hyV hcy'
    rw [e1, e2] at h1
    rw [mul_comm]
    exact h1

end

end ReciprocityTheory.AnForm.R
