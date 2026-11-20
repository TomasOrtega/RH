import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.RelConstThickening

/- English proof (translation)
Set `_ : Algebra K A` to `c.toAlgebra`. Set `_ : Algebra A A'` to `p.hom.toAlgebra`. Set `_ : Algebra (DualNumber K) A'` to `s.toAlgebra`. Set `_ : Algebra K A'` to `(s.comp (algebraMap K (DualNumber K))).toAlgebra`. Establish `: IsScalarTower K (DualNumber K) A'` using `.of_algebraMap_eq fun _ => rfl`.

Establish `: IsScalarTower K A A'` using `.of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm`. Establish `h : Algebra.IsPushout K A (DualNumber K) A'` using `CommRingCat.isPushout_iff_isPushout.mp H`. Set `b : Module.Basis (Fin 2) K (DualNumber K)` to `Module.Basis.finTwoProd K`. Establish `b0 : b 0 = 1` using `Module.Basis.finTwoProd_zero K`. Establish `b1 : b 1 = DualNumber.eps` using `Module.Basis.finTwoProd_one K`.

Set `B` to `h.out.basis b`. Establish `B0 : B 0 = 1`. Rewrite using `[h.out.basis_apply, b0]`. Conclude with `map_one s`. Establish `B1 : B 1 = s DualNumber.eps`.

Rewrite using `[h.out.basis_apply, b1]`. Both sides reduce to the same expression. Establish `key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y]` using `fun x y => by`. Rewrite using `[Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_comm (s _)]`. Both sides reduce to the same expression.

Use `⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F = _`. Rewrite using `[key, LinearEquiv.eq_symm_apply]`. Apply the tactic sequence `ext i; fin_cases i <;> rfl`. Use `replace hab : F = _ := hab`.

Rewrite `hab` using `[key, LinearEquiv.eq_symm_apply]`. Rewrite using `[hab]`. Both sides reduce to the same expression.
-/
theorem existsUnique_of_isPushout {K : Type} [CommRing K] {A A' : CommRingCat.{0}} (c : K →+* A) (p : A ⟶ A')
    (s : DualNumber K →+* A')
    (H : IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap K (DualNumber K))) p (CommRingCat.ofHom s))
    (F : A') : ∃! ab : A × A, F = p.hom ab.1 + s DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra K A := c.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber K) A' := s.toAlgebra
  let _ : Algebra K A' := (s.comp (algebraMap K (DualNumber K))).toAlgebra
  have : IsScalarTower K (DualNumber K) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout K A (DualNumber K) A' := CommRingCat.isPushout_iff_isPushout.mp H
  let b : Module.Basis (Fin 2) K (DualNumber K) := Module.Basis.finTwoProd K
  have b0 : b 0 = 1 := Module.Basis.finTwoProd_zero K
  have b1 : b 1 = DualNumber.eps := Module.Basis.finTwoProd_one K
  let B := h.out.basis b
  have B0 : B 0 = 1 := by
    rw [h.out.basis_apply, b0]; exact map_one s
  have B1 : B 1 = s DualNumber.eps := by
    rw [h.out.basis_apply, b1]; rfl
  have key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y] := fun x y => by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one,
      _root_.mul_comm (s _)]
    rfl
  refine ⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩
  · change F = _
    rw [key, LinearEquiv.eq_symm_apply]
    ext i; fin_cases i <;> rfl
  · replace hab : F = _ := hab
    rw [key, LinearEquiv.eq_symm_apply] at hab
    rw [hab]; rfl

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/- English proof (translation)
Conclude with `congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn f U a) = constFn f V a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]`. Both sides reduce to the same expression.
-/
theorem res_app {X X' : Scheme.{0}} (f : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (X'.presheaf.map (homOfLE h').op).hom ((f.app U).hom a) = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Conclude with `(congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)`.
-/
theorem fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

/- English proof (translation)
Use `existsUnique_of_isPushout (K := Γ(X, U.1)) (h.appLE U.1 V hVU).hom (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F` and prove the remaining obligations. Establish `e0 : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1` using `U.2.fromSpec_preimage_self.ge`. Establish `e : (⊤ : (Sp (DualNumber Γ(X, U.1))).Opens) ≤ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) ⁻¹ᵁ U.1` using `fun x _ => e0 (Set.mem_univ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) x))`. Establish `po` using `(isIso_pushoutSection_iff H (US := U.1) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) e hVU (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ U.2 (isAffineOpen_top _) hV)`. Use `po.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `e1 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U).appLE U.1 ⊤ e = U.2.fromSpec.appLE U.1 ⊤ e0 ≫ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top` using `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm`. Establish `e2 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))).hom = (Scheme.ΓSpecIso (.of Γ(X, U.1))).hom ≫ CommRingCat.ofHom (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))`. Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.

Establish `e3` using `fromSpec_appLE_top U.2 e0`. Rewrite using `[e1, e3]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ·) e2).trans (Iso.inv_hom_id_assoc _ _))`. Simplify using `[Scheme.Hom.app_eq_appLE]`. Use extensionality with `x`.

Simplify using `[constHom]`.
-/
theorem existsUnique_affine {X Z P : Scheme.{0}} (U : X.affineOpens) (h : Z ⟶ X)
    (p₁ : P ⟶ Sp (DualNumber Γ(X, U.1))) (p₂ : P ⟶ Z)
    (H : IsPullback p₂ p₁ h (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U))
    {V : Z.Opens} (hV : IsAffineOpen V) (hVU : V ≤ h ⁻¹ᵁ U.1) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := Γ(X, U.1)) (h.appLE U.1 V hVU).hom (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have e0 : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e : (⊤ : (Sp (DualNumber Γ(X, U.1))).Opens) ≤
      (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) ⁻¹ᵁ U.1 := fun x _ =>
    e0 (Set.mem_univ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) x))
  have po := (isIso_pushoutSection_iff H (US := U.1) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) e hVU
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ U.2
      (isAffineOpen_top _) hV)
  refine po.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · have e1 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U).appLE U.1 ⊤ e =
        U.2.fromSpec.appLE U.1 ⊤ e0 ≫ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top ≫
        (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))).hom =
        (Scheme.ΓSpecIso (.of Γ(X, U.1))).hom ≫ CommRingCat.ofHom (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := by
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e3 := fromSpec_appLE_top U.2 e0
    rw [e1, e3]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ·) e2).trans (Iso.inv_hom_id_assoc _ _))
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]

section Glue

variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {π : Y' ⟶ Sp R} {ρ : Y' ⟶ Y} {ε : R}

/- English proof (translation)
Rewrite using `[map_add, map_mul, res_app ρ h, res_app ρ h, res_constFn]`.
-/
theorem res_comb {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ ε * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ ε * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add, map_mul, res_app ρ h, res_app ρ h, res_constFn]

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩`.
-/
theorem le_iSup_affine (O : Y.Opens) : O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := fun x hx => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

/- English proof (translation)
Establish `loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) = ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b')` using `fun U => by`. Establish `h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O` using `fun x hx => U.2.2 hx`. Establish `e` using `congrArg (Y'.presheaf.map (homOfLE h').op).hom h`. Rewrite `e` using `[res_comb U.2.2, res_comb U.2.2]`. Conclude with `(H _ U.2.1 (U.2.2.trans hO) _).unique rfl e`.

Conclude with `⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a' fun U => congrArg Prod.fst (loc U), Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b' fun U => congrArg Prod.snd (loc U)⟩`.
-/
theorem unique_comb {W : Y.Opens}
    (H : ∀ V : Y.Opens, IsAffineOpen V → V ≤ W → ∀ F : Γ(Y', ρ ⁻¹ᵁ V), ∃! ab : Γ(Y, V) × Γ(Y, V),
      F = (ρ.app V).hom ab.1 + constFn π _ ε * (ρ.app V).hom ab.2)
    {O : Y.Opens} (hO : O ≤ W) {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ ε * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ ε * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (H _ U.2.1 (U.2.2.trans hO) _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩

/- English proof (translation)
Establish `hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O` using `fun U x hx => U.2.2 hx`. Use `choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => (H _ U.2.1 (U.2.2.trans hO) ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists`. Establish `comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 = (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧ (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab …` using `fun U V => by`. Apply `unique_comb H ((inf_le_left.trans U.2.2).trans hO)` to reduce the goal to its premises. Rewrite using `[← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]`.

Conclude with `(res_res _ _ F).trans (res_res _ _ F).symm`. Take `⟨a, ha, -⟩` from `Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) (fun U => (ab U).1) (fun U V => (comp U V).1)`. Take `⟨b, hb, -⟩` from `Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) (fun U => (ab U).2) (fun U V => (comp U V).2)`. Establish `hF : F = (ρ.app O).hom a + constFn π _ ε * (ρ.app O).hom b`. Use `Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _ (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_` and prove the remaining obligations.

Take `⟨U, hU⟩` from `TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩`. Use `(hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)` and prove the remaining obligations. Rewrite using `[← ha U, ← hb U]`. Both sides reduce to the same expression.

Use `⟨(a, b), hF, fun c hc => ?_⟩` and prove the remaining obligations. Use `unique_comb H hO (hc.symm.trans hF)` as an intermediate fact. Conclude with `Prod.ext this.1 this.2`.
-/
theorem existsUnique_comb {W : Y.Opens}
    (H : ∀ V : Y.Opens, IsAffineOpen V → V ≤ W → ∀ F : Γ(Y', ρ ⁻¹ᵁ V), ∃! ab : Γ(Y, V) × Γ(Y, V),
      F = (ρ.app V).hom ab.1 + constFn π _ ε * (ρ.app V).hom ab.2)
    (O : Y.Opens) (hO : O ≤ W)
    (F : Γ(Y', ρ ⁻¹ᵁ O)) : ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ ε * (ρ.app O).hom ab.2 := by
  have hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun U x hx => U.2.2 hx
  choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (H _ U.2.1 (U.2.2.trans hO) ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists
  have comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).2 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).2 := fun U V => by
    apply unique_comb H ((inf_le_left.trans U.2.2).trans hO)
    rw [← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]
    exact (res_res _ _ F).trans (res_res _ _ F).symm
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).1) (fun U V => (comp U V).1)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).2) (fun U V => (comp U V).2)
  have hF : F = (ρ.app O).hom a + constFn π _ ε * (ρ.app O).hom b := by
    refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
      (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_
    · obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    · refine (hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)
      rw [← ha U, ← hb U]
      rfl
  refine ⟨(a, b), hF, fun c hc => ?_⟩
  have := unique_comb H hO (hc.symm.trans hF)
  exact Prod.ext this.1 this.2

end Glue

/- English proof (translation)
Introduce `U h p₁ p₂ H O hO F` and use `existsUnique_comb (fun _ hV hVU F => existsUnique_affine U h p₁ p₂ H hV hVU F) O hO F`.
-/
theorem existsUnique_decomp : ∀ {X Z P : Scheme.{0}} (U : X.affineOpens) (h : Z ⟶ X) (p₁ : P ⟶ Sp (DualNumber Γ(X, U.1))) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) → ∀ (O : Z.Opens), O ≤ h ⁻¹ᵁ U.1 → ∀ F : Γ(P, p₂ ⁻¹ᵁ O), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun U h p₁ p₂ H O hO F =>
    existsUnique_comb (fun _ hV hVU F => existsUnique_affine U h p₁ p₂ H hV hVU F) O hO F

end GlobalTheory.RelConstThickening
end
