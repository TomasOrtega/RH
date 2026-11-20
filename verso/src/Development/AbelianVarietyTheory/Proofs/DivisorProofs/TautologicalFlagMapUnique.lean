import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecSecCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepMapSectionRangeStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagZ.TautUniq
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

/- English proof (translation)
Introduce `N A _ g h l hs i j hj hl`. Establish `hc : (fun m => h.1 m j) ∈ Submodule.span A (Set.range fun k : Fin l => fun m => g.1 m (Fin.castLE l.is_le k))` using `hs (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun A).1 hc`. Establish `hcol : ∀ m, h.1 m j = ∑ k, c k * g.1 m (Fin.castLE l.is_le k)` using `fun m => by`. Use `congrFun hc m` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Conclude with `this.symm`. Establish `hgg : (g⁻¹).1 * g.1 = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Use `_ = ∑ k, c k * ((g⁻¹).1 * g.1) i (Fin.castLE l.is_le k) := by`. Repeatedly rewrite using `[hcol, Matrix.mul_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by`. Rewrite using `[hgg]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply_ne, mul_zero]`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.coe_castLE] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem below_zero_of_span_le : ∀ (N : ℕ) (A : Type) [CommRing A] (g h : GL (Fin N) A) (l : Fin (N + 1)),
    Submodule.span A (Set.range fun j : Fin l => fun i => h.1 i (Fin.castLE l.is_le j)) ≤
      Submodule.span A (Set.range fun j : Fin l => fun i => g.1 i (Fin.castLE l.is_le j)) →
    ∀ i j : Fin N, (j : ℕ) < l → (l : ℕ) ≤ i → (g⁻¹ * h).1 i j = 0 := by
  intro N A _ g h l hs i j hj hl
  have hc : (fun m => h.1 m j) ∈
      Submodule.span A (Set.range fun k : Fin l => fun m => g.1 m (Fin.castLE l.is_le k)) :=
    hs (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hc
  have hcol : ∀ m, h.1 m j = ∑ k, c k * g.1 m (Fin.castLE l.is_le k) := fun m => by
    have := congrFun hc m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hgg : (g⁻¹).1 * g.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (g⁻¹ * h).1 i j = ∑ m, (g⁻¹).1 i m * h.1 m j := by
        rw [Units.val_mul, Matrix.mul_apply]
    _ = ∑ k, c k * ((g⁻¹).1 * g.1) i (Fin.castLE l.is_le k) := by
        simp_rw [hcol, Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
        ring
    _ = 0 := by
        rw [hgg]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Matrix.one_apply_ne, mul_zero]
        intro e
        have := congrArg Fin.val e
        simp only [Fin.coe_castLE] at this
        omega

/- English proof (translation)
Introduce `S Z T Y x g₁ s g w E F u`. Substitute `w` using the available equality. Establish `A` using `congrArg (fun τ => τ.app E) (Scheme.Modules.pseudofunctor_associativity x g₁ s)`. Simplify using `at A`. Establish `nat` using `(Scheme.Modules.pullbackComp x g₁).hom.naturality u`.

Simplify using `at nat`. Simplify using `only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id, Functor.map_comp, Category.assoc]`. Rewrite using `[← reassoc_of% nat]`. Use `congr 1`. Rewrite using `[← cancel_epi ((Scheme.Modules.pullbackComp x (g₁ ≫ s)).inv.app E ≫ (Scheme.Modules.pullback x).map ((Scheme.Modules.pullbackComp g₁ s).inv.app E))]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% A]`. Simplify using `only [eqToHom_trans, eqToHom_refl]`. Rewrite using `[← Functor.map_comp_assoc, Iso.inv_hom_id_app]`. Simplify using the standard rewrite rules.
-/
theorem pullback_map_comp_pullbackComp : ∀ {S Z T Y : Scheme.{0}} (x : Y ⟶ T) (g₁ : T ⟶ Z) (s : Z ⟶ S) (g : T ⟶ S) (w : g₁ ≫ s = g)
    (E : S.Modules) (F : Z.Modules) (u : F ⟶ (Scheme.Modules.pullback s).obj E),
    (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback g₁).map u ≫
        (Scheme.Modules.pullbackComp g₁ s).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E) ≫
      (Scheme.Modules.pullbackComp x g).hom.app E =
    (Scheme.Modules.pullbackComp x g₁).hom.app F ≫ (Scheme.Modules.pullback (x ≫ g₁)).map u ≫
      (Scheme.Modules.pullbackComp (x ≫ g₁) s).hom.app E ≫
        (Scheme.Modules.pullbackCongr (show (x ≫ g₁) ≫ s = x ≫ g by rw [Category.assoc, w])).hom.app E := by
  intro S Z T Y x g₁ s g w E F u
  subst w
  have A := congrArg (fun τ => τ.app E) (Scheme.Modules.pseudofunctor_associativity x g₁ s)
  simp at A
  have nat := (Scheme.Modules.pullbackComp x g₁).hom.naturality u
  simp at nat
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nat]
  congr 1
  rw [← cancel_epi ((Scheme.Modules.pullbackComp x (g₁ ≫ s)).inv.app E ≫
    (Scheme.Modules.pullback x).map ((Scheme.Modules.pullbackComp g₁ s).inv.app E))]
  simp only [Category.assoc]
  rw [reassoc_of% A]
  simp only [eqToHom_trans, eqToHom_refl]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end GlobalTheory.FlagZ.TautUniq

namespace GlobalTheory.FlagZ.TautUniq
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

/- English proof (translation)
Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨e.app U a, rfl⟩`. Introduce and unpack `⟨b, rfl⟩`.

Use `⟨(inv e).app U b, ?_⟩` and prove the remaining obligations. Establish `: (inv e ≫ e ≫ v).app U b = v.app U b` using `by rw [IsIso.inv_hom_id_assoc]`. Conclude with `this`.
-/
theorem range_app_isIso_comp {X : Scheme.{0}} {A B C : X.Modules} (e : A ⟶ B) [IsIso e] (v : B ⟶ C)
    (U : X.Opens) : Set.range ((e ≫ v).app U) = Set.range (v.app U) := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e.app U a, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(inv e).app U b, ?_⟩
    have : (inv e ≫ e ≫ v).app U b = v.app U b := by rw [IsIso.inv_hom_id_assoc]
    exact this

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem mem_range_stepMap_congr {ι : Type} [Fintype ι] {N : ℕ}
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N) {Y : Scheme.{0}}
    {φ φ' : Y ⟶ Fl ι N} (e : φ = φ') (y : Y ⟶ Sp ℤ) (hy : φ ≫ flStr ι N = y) (hy' : φ' ≫ flStr ι N = y)
    (a : ι) (l : Fin (N + 1)) (s : Γ((Scheme.Modules.pullback y).obj (Taut.stdE N), ⊤)) :
    s ∈ Set.range ((stepMap ι N fl φ y hy a l).app ⊤) ↔ s ∈ Set.range ((stepMap ι N fl φ' y hy' a l).app ⊤) := by
  subst e
  rfl

/- English proof (translation)
Introduce `ι _ N fl hT T g fl' g₁ g₂ w₁ w₂ H₁ H₂`. Use `GlobalTheory.hom_ext_of_fromSpecStalk fun t => ?_` and prove the remaining obligations. Establish `hr : ∀ (gₖ : T ⟶ Fl ι N) (wₖ : gₖ ≫ flStr ι N = g) (a : ι) (l : Fin (N + 1)), (∃ e : (Scheme.Modules.pullback gₖ).obj ((fl a).F l) ≅ (fl' a).F l, e.hom ≫ (fl' a).ι l = (Scheme.Modules.pullback gₖ).map ((fl a).ι l) ≫ (Scheme.Modules.pullbackComp gₖ (flStr ι N)).hom.app (Taut.stdE …`. Introduce and unpack `gₖ wₖ a l ⟨e, he⟩`. Establish `c` using `pullback_map_comp_pullbackComp (T.fromSpecStalk t) gₖ (flStr ι N) g wₖ (Taut.stdE N) ((fl a).F l) ((fl a).ι l)`.

Rewrite `c` using `[← he, Functor.map_comp, Category.assoc]`. Establish `c'` using `congrArg (fun m => Set.range (m.app ⊤)) c`. Simplify using `only at c'`. Rewrite `c'` using `[range_app_isIso_comp ((Scheme.Modules.pullback (T.fromSpecStalk t)).map e.hom), range_app_isIso_comp ((Scheme.Modules.pullbackComp (T.fromSpecStalk t) gₖ).hom.app ((fl a).F l))]`. Conclude with `c'.symm`.

Take `⟨h₁, e₁⟩` from `@exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd (T.presheaf.stalk t) _ inferInstance (T.fromSpecStalk t ≫ g₁)`. Take `⟨h₂, e₂⟩` from `@exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd (T.presheaf.stalk t) _ inferInstance (T.fromSpecStalk t ≫ g₂)`. Establish `hs : ∀ (a : ι) (l : Fin (N + 1)), Submodule.span (T.presheaf.stalk t) (Set.range fun j : Fin l => fun i => (h₂ a).1 i (Fin.castLE l.is_le j)) ≤ Submodule.span (T.presheaf.stalk t) (Set.range fun j : Fin l => fun i => (h₁ a).1 i (Fin.castLE l.is_le j))`. Introduce `a l`. Establish `E : ∀ (gₖ : T ⟶ Fl ι N) (wₖ : gₖ ≫ flStr ι N = g) (h : ι → GL (Fin N) (T.presheaf.stalk t)) (eₖ : T.fromSpecStalk t ≫ gₖ = flagPt Prod.fst Prod.snd h) (v : Fin N → T.presheaf.stalk t), vecSec (T.fromSpecStalk t ≫ g) v ∈ Set.range ((stepMap ι N fl (T.fromSpecStalk t ≫ gₖ) (T.fromS …`.

Introduce `gₖ wₖ h eₖ v`. Use `GlobalTheory.T.step_map_section_range ι N fl hT (T.presheaf.stalk t) h (T.fromSpecStalk t ≫ g) (by rw [← eₖ, Category.assoc, wₖ]) a l v` as an intermediate fact. Conclude with `(mem_range_stepMap_congr fl eₖ _ _ _ a l _).trans this`. Introduce `v hv`. Rewrite using `[← E g₁ w₁ h₁ e₁, hr g₁ w₁ a l (H₁ a l), ← hr g₂ w₂ a l (H₂ a l), E g₂ w₂ h₂ e₂]`.

Conclude with `hv`. Rewrite using `[e₁, e₂]`. Establish `hmul : h₁ * (fun τ => (h₁ τ)⁻¹ * h₂ τ) = h₂`. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules.

Rewrite using `[← hmul]`. Use `(flagPt_mul Prod.fst Prod.snd h₁ _ ?_).symm` and prove the remaining obligations. Introduce `k i j hj hl`. Conclude with `below_zero_of_span_le N _ (h₁ k.1) (h₂ k.1) k.2 (hs k.1 k.2) i j hj hl`.
-/
theorem eq_of_pullback_taut :
    ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N)
    (g₁ g₂ : T ⟶ GlobalTheory.FlagZ.Fl ι N) (w₁ : g₁ ≫ GlobalTheory.FlagZ.flStr ι N = g) (w₂ : g₂ ≫ GlobalTheory.FlagZ.flStr ι N = g),
    (∀ a i, ∃ e : (Scheme.Modules.pullback g₁).obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g₁).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g₁ (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w₁).hom.app (GlobalTheory.FlagZ.Taut.stdE N)) →
    (∀ a i, ∃ e : (Scheme.Modules.pullback g₂).obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g₂).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g₂ (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w₂).hom.app (GlobalTheory.FlagZ.Taut.stdE N)) → g₁ = g₂ := by
  intro ι _ N fl hT T g fl' g₁ g₂ w₁ w₂ H₁ H₂
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun t => ?_

  have hr : ∀ (gₖ : T ⟶ Fl ι N) (wₖ : gₖ ≫ flStr ι N = g) (a : ι) (l : Fin (N + 1)),
      (∃ e : (Scheme.Modules.pullback gₖ).obj ((fl a).F l) ≅ (fl' a).F l,
        e.hom ≫ (fl' a).ι l = (Scheme.Modules.pullback gₖ).map ((fl a).ι l) ≫
          (Scheme.Modules.pullbackComp gₖ (flStr ι N)).hom.app (Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr wₖ).hom.app (Taut.stdE N)) →
      Set.range ((stepMap ι N fl (T.fromSpecStalk t ≫ gₖ) (T.fromSpecStalk t ≫ g)
          (by rw [Category.assoc, wₖ]) a l).app ⊤) =
        Set.range (((Scheme.Modules.pullback (T.fromSpecStalk t)).map ((fl' a).ι l) ≫
          (Scheme.Modules.pullbackComp (T.fromSpecStalk t) g).hom.app (Taut.stdE N)).app ⊤) := by
    rintro gₖ wₖ a l ⟨e, he⟩
    have c := pullback_map_comp_pullbackComp (T.fromSpecStalk t) gₖ (flStr ι N) g wₖ (Taut.stdE N) ((fl a).F l) ((fl a).ι l)
    rw [← he, Functor.map_comp, Category.assoc] at c
    have c' := congrArg (fun m => Set.range (m.app ⊤)) c
    simp only at c'
    rw [range_app_isIso_comp ((Scheme.Modules.pullback (T.fromSpecStalk t)).map e.hom),
      range_app_isIso_comp ((Scheme.Modules.pullbackComp (T.fromSpecStalk t) gₖ).hom.app ((fl a).F l))] at c'
    exact c'.symm
  obtain ⟨h₁, e₁⟩ := @exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd
    (T.presheaf.stalk t) _ inferInstance (T.fromSpecStalk t ≫ g₁)
  obtain ⟨h₂, e₂⟩ := @exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd
    (T.presheaf.stalk t) _ inferInstance (T.fromSpecStalk t ≫ g₂)

  have hs : ∀ (a : ι) (l : Fin (N + 1)),
      Submodule.span (T.presheaf.stalk t) (Set.range fun j : Fin l => fun i => (h₂ a).1 i (Fin.castLE l.is_le j)) ≤
        Submodule.span (T.presheaf.stalk t) (Set.range fun j : Fin l => fun i => (h₁ a).1 i (Fin.castLE l.is_le j)) := by
    intro a l
    have E : ∀ (gₖ : T ⟶ Fl ι N) (wₖ : gₖ ≫ flStr ι N = g) (h : ι → GL (Fin N) (T.presheaf.stalk t))
        (eₖ : T.fromSpecStalk t ≫ gₖ = flagPt Prod.fst Prod.snd h) (v : Fin N → T.presheaf.stalk t),
        vecSec (T.fromSpecStalk t ≫ g) v ∈ Set.range ((stepMap ι N fl (T.fromSpecStalk t ≫ gₖ)
          (T.fromSpecStalk t ≫ g) (by rw [Category.assoc, wₖ]) a l).app ⊤) ↔
        v ∈ Submodule.span (T.presheaf.stalk t)
          (Set.range fun j : Fin l => fun i => (h a).1 i (Fin.castLE l.is_le j)) := by
      intro gₖ wₖ h eₖ v
      have := GlobalTheory.T.step_map_section_range ι N fl hT (T.presheaf.stalk t) h (T.fromSpecStalk t ≫ g)
        (by rw [← eₖ, Category.assoc, wₖ]) a l v
      exact (mem_range_stepMap_congr fl eₖ _ _ _ a l _).trans this
    intro v hv
    rw [← E g₁ w₁ h₁ e₁, hr g₁ w₁ a l (H₁ a l), ← hr g₂ w₂ a l (H₂ a l), E g₂ w₂ h₂ e₂]
    exact hv
  rw [e₁, e₂]
  have hmul : h₁ * (fun τ => (h₁ τ)⁻¹ * h₂ τ) = h₂ := by
    funext τ
    simp
  rw [← hmul]
  refine (flagPt_mul Prod.fst Prod.snd h₁ _ ?_).symm
  intro k i j hj hl
  exact below_zero_of_span_le N _ (h₁ k.1) (h₂ k.1) k.2 (hs k.1 k.2) i j hj hl

end GlobalTheory.FlagZ.TautUniq
