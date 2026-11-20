import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
open GlobalTheory.Vanishing.H0 GlobalTheory.CompHS

namespace GlobalTheory.HSApp

/- English proof (translation)
Use `M.iso` as an intermediate fact. Establish `hne : (M.opn : Set M.X).Nonempty` using `M.dense.nonempty`. Establish `hm : genericPoint M.X ∈ M.opn` using `((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `(M.σ ∣_ U).surjective ⟨η, hη⟩`.

Establish `hx' : M.σ x.1 = η` using `(morphismRestrict_base_coe M.σ U x).symm.trans (congrArg Subtype.val hx)`. Establish `hcl : η ∈ closure {M.σ (genericPoint M.X)}`. Rewrite using `[← hx', ← Set.image_singleton]`. Conclude with `image_closure_subset_closure_image M.σ.continuous ⟨x.1, by rw [(genericPoint_spec M.X).def]; trivial, rfl⟩`. Establish `hgen : IsGenericPoint (M.σ (genericPoint M.X)) Set.univ`.

Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations. Rewrite using `[← hg.def]`. Conclude with `closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure`. Conclude with `hgen.eq hg`.
-/
theorem modif_generic_map {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IrreducibleSpace M.X] (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    genericPoint M.X ∈ M.opn ∧ M.σ (genericPoint M.X) = η := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hm : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  refine ⟨hm, ?_⟩
  obtain ⟨x, hx⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hx' : M.σ x.1 = η := (morphismRestrict_base_coe M.σ U x).symm.trans (congrArg Subtype.val hx)
  have hcl : η ∈ closure {M.σ (genericPoint M.X)} := by
    rw [← hx', ← Set.image_singleton]
    exact image_closure_subset_closure_image M.σ.continuous
      ⟨x.1, by rw [(genericPoint_spec M.X).def]; trivial, rfl⟩
  have hgen : IsGenericPoint (M.σ (genericPoint M.X)) Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure
  exact hgen.eq hg

/- English proof (translation)
Use `M.iso` as an intermediate fact. Establish `: IsIso (M.σ.stalkMap z)` using `((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap M.σ U ⟨z, hz⟩)).1 (((isIso_iff_isIso_stalkMap (M.σ ∣_ U)).1 M.iso).2 ⟨z, hz⟩)`. Establish `hst : Function.Surjective (M.σ.stalkMap z).hom` using `(ConcreteCategory.bijective_of_isIso _).2`. Introduce `y`. Take `⟨a, rfl⟩` from `M.X.residue_surjective z y`.

Take `⟨b, rfl⟩` from `hst a`. Conclude with `⟨Y.residue _ b, congr($(Scheme.residue_residueFieldMap M.σ z).hom b)⟩`.
-/
theorem modif_residueFieldMap_surjective {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) (z : M.X) (hz : z ∈ M.opn) : Function.Surjective (M.σ.residueFieldMap z).hom := by
  have := M.iso
  have : IsIso (M.σ.stalkMap z) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap M.σ U ⟨z, hz⟩)).1
      (((isIso_iff_isIso_stalkMap (M.σ ∣_ U)).1 M.iso).2 ⟨z, hz⟩)
  have hst : Function.Surjective (M.σ.stalkMap z).hom := (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨a, rfl⟩ := M.X.residue_surjective z y
  obtain ⟨b, rfl⟩ := hst a
  exact ⟨Y.residue _ b, congr($(Scheme.residue_residueFieldMap M.σ z).hom b)⟩

/- English proof (translation)
Use `set S := (M.sys Δ φ f abelian₂).toLinSys`. Establish `hp : Adelic.ptOf (Adelic.resPt z) = z` using `Adelic.ptOf_resPt z`. Establish `hj : z ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))` using `(congrArg (fun y => y ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))) hp).mp (S.mem_chartAt (Adelic.ptOf (Adelic.resPt z)))`. Use `set j := S.chartAt (Adelic.ptOf (Adelic.resPt z))`. Establish `hi0 : M.σ z ∈ B.U (j.1 PUnit.unit)` using `mem_pull.1 hj.1`.

Establish `hu : IsUnit (ger z hj.2 (Δ.t.f j.2))` using `(isUnit_ger_iff _ hj.2).2 ((Δ.mem_nonzeroLocus z).2 (M.notMem_support hnb z (M.off_eq.ge hz)))`. Use `⟨(M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (tr B (M.σ z) i (j.1 PUnit.unit)).val) * (M.X.residue z).hom (ger z hj.2 (Δ.t.f j.2)), mul_ne_zero ?_ ?_, fun w => ?_⟩` and prove the remaining obligations. Conclude with `(map_ne_zero _).2 (((tr B (M.σ z) i (j.1 PUnit.unit)).isUnit.map (Y.residue (M.σ z)).hom).ne_zero)`. Conclude with `(hu.map (M.X.residue z).hom).ne_zero`. Establish `hv : S.val (Adelic.resPt z) (toSec (Δ.lift w)) = (M.X.residue z).hom (germ j z (memTop z) hj (Δ.lift w))`.

Rewrite using `[Adelic.LinSys.val, Adelic.projSys.valR_resPt z _ hj, ← ger_toSec]`. Both sides reduce to the same expression. Rewrite using `[hv, germ_change i (j.1 PUnit.unit) (M.σ z) (memTop _) hi hi0, map_mul, map_mul, mul_assoc]`. Use `congr 1`. Rewrite using `[← map_mul (M.X.residue z).hom, Δ.germ_lift w j z hj]`.

Use `Eq.trans ?_ (congrArg (M.X.residue z).hom (GlobalTheory.Vanishing.H0.germ_pull (p := p) M.σ le_top j.1 z (memTop z) hj.1 w.1)).symm` and prove the remaining obligations. Conclude with `congr($(Scheme.residue_residueFieldMap M.σ z).hom _)`.
-/
theorem modif_residueFieldMap_germ {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    (hnb : NoBase hB W U) (z : M.X) (hz : z ∈ M.opn) (i : B.ι) (hi : M.σ z ∈ B.U i) :
    ∃ c : M.X.residueField z, c ≠ 0 ∧ ∀ w : W,
      (M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (germ i (M.σ z) (memTop _) hi w.1)) =
        c * (M.sys Δ φ f abelian₂).toLinSys.val (Adelic.resPt z) (toSec (Δ.lift w)) := by
  set S := (M.sys Δ φ f abelian₂).toLinSys
  have hp : Adelic.ptOf (Adelic.resPt z) = z := Adelic.ptOf_resPt z
  have hj : z ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z))) :=
    (congrArg (fun y => y ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))) hp).mp
      (S.mem_chartAt (Adelic.ptOf (Adelic.resPt z)))
  set j := S.chartAt (Adelic.ptOf (Adelic.resPt z))
  have hi0 : M.σ z ∈ B.U (j.1 PUnit.unit) := mem_pull.1 hj.1
  have hu : IsUnit (ger z hj.2 (Δ.t.f j.2)) :=
    (isUnit_ger_iff _ hj.2).2 ((Δ.mem_nonzeroLocus z).2 (M.notMem_support hnb z (M.off_eq.ge hz)))
  refine ⟨(M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (tr B (M.σ z) i (j.1 PUnit.unit)).val) *
    (M.X.residue z).hom (ger z hj.2 (Δ.t.f j.2)), mul_ne_zero ?_ ?_, fun w => ?_⟩
  · exact (map_ne_zero _).2 (((tr B (M.σ z) i (j.1 PUnit.unit)).isUnit.map (Y.residue (M.σ z)).hom).ne_zero)
  · exact (hu.map (M.X.residue z).hom).ne_zero
  have hv : S.val (Adelic.resPt z) (toSec (Δ.lift w)) = (M.X.residue z).hom (germ j z (memTop z) hj (Δ.lift w)) := by
    rw [Adelic.LinSys.val, Adelic.projSys.valR_resPt z _ hj, ← ger_toSec]
    rfl
  rw [hv, germ_change i (j.1 PUnit.unit) (M.σ z) (memTop _) hi hi0, map_mul, map_mul, mul_assoc]
  congr 1
  rw [← map_mul (M.X.residue z).hom, Δ.germ_lift w j z hj]
  refine Eq.trans ?_ (congrArg (M.X.residue z).hom
    (GlobalTheory.Vanishing.H0.germ_pull (p := p) M.σ le_top j.1 z (memTop z) hj.1 w.1)).symm
  exact congr($(Scheme.residue_residueFieldMap M.σ z).hom _)

/- English proof (translation)
Take `⟨hmem, hσ⟩` from `modif_generic_map M η hη hg`. Substitute `hσ` using the available equality. Use `set S := (M.sys Δ φ f abelian₂).toLinSys with hS`. Use `set z := genericPoint M.X with hz`. Establish `hsurj` using `modif_residueFieldMap_surjective M z hmem`.

Establish `hbpf : S.BasePointFree` using `Δ.iSup_nonzeroLocus (f.b.map φ).span_eq`. Take `⟨j0, hj0⟩` from `Function.ne_iff.1 (hbpf.coords_ne_zero (Adelic.resPt z))`. Establish `key : ∀ w : W, S.val (Adelic.resPt z) (toSec (Δ.lift w)) / S.coords (Adelic.resPt z) j0 ∈ S.ratioField (Adelic.resPt z)` using `fun w => by set u := f.b.equivFun (φ.symm w)`. Establish `e : toSec (Δ.lift w) = S.comb u`. Use `(bijective_ofSec_top (p := M.str)).1 ?_` and prove the remaining obligations.

Rewrite using `[ofSec_toSec]`. Use `Eq.trans ?_ (M.ofSec_comb Δ φ f abelian₂ u).symm` and prove the remaining obligations. Simplify using `[u]`. Rewrite using `[e, S.val_comb, Finset.sum_div]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_div_assoc]`. Conclude with `mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨j, j0, rfl⟩))`. Establish `hgen : ∀ r ∈ {r | ∃ (i : B.ι) (hi : M.σ z ∈ B.U i) (s s' : H0 p B U), s ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧ s' ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧ r = (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s) / (Y.residue (M.σ z)).hom (germ i …`. Introduce and unpack `r ⟨i, hi, _, _, ⟨w, rfl⟩, ⟨w', rfl⟩, rfl⟩`. Take `⟨c, hc, hcw⟩` from `modif_residueFieldMap_germ M Δ φ f abelian₂ hnb z hmem i hi`.

Rewrite using `[germ_restr, germ_restr, map_div₀, hcw, hcw, mul_div_mul_left _ _ hc, ← div_div_div_cancel_right₀ hj0]`. Conclude with `div_mem (key w) (key w')`. Establish `hle : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) (M.σ z) hη ≤ (S.ratioField (Adelic.resPt z)).comap (M.σ.residueFieldMap z).hom` using `Subfield.closure_le.2 hgen`. Use `⟨z, genericPoint_spec M.X, eq_top_iff.2 fun x _ => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj x`.

Conclude with `hle (hr.symm ▸ Subfield.mem_top y)`.
-/
theorem sys_birational_of_ratField {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    [IsIntegral M.X] (hnb : NoBase hB W U) (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ)
    (hr : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) η hη = ⊤) :
    (M.sys Δ φ f abelian₂).toLinSys.Birational := by
  classical
  obtain ⟨hmem, hσ⟩ := modif_generic_map M η hη hg
  subst hσ
  set S := (M.sys Δ φ f abelian₂).toLinSys with hS
  set z := genericPoint M.X with hz
  have hsurj := modif_residueFieldMap_surjective M z hmem
  have hbpf : S.BasePointFree := Δ.iSup_nonzeroLocus (f.b.map φ).span_eq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 (hbpf.coords_ne_zero (Adelic.resPt z))
  have key : ∀ w : W, S.val (Adelic.resPt z) (toSec (Δ.lift w)) / S.coords (Adelic.resPt z) j0 ∈
      S.ratioField (Adelic.resPt z) := fun w => by
    set u := f.b.equivFun (φ.symm w)
    have e : toSec (Δ.lift w) = S.comb u := by
      refine (bijective_ofSec_top (p := M.str)).1 ?_
      rw [ofSec_toSec]
      refine Eq.trans ?_ (M.ofSec_comb Δ φ f abelian₂ u).symm
      simp [u]
    rw [e, S.val_comb, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨j, j0, rfl⟩))
  have hgen : ∀ r ∈ {r | ∃ (i : B.ι) (hi : M.σ z ∈ B.U i) (s s' : H0 p B U),
      s ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      s' ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      r = (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s) / (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s')},
      (M.σ.residueFieldMap z).hom r ∈ S.ratioField (Adelic.resPt z) := by
    rintro r ⟨i, hi, _, _, ⟨w, rfl⟩, ⟨w', rfl⟩, rfl⟩
    obtain ⟨c, hc, hcw⟩ := modif_residueFieldMap_germ M Δ φ f abelian₂ hnb z hmem i hi
    rw [germ_restr, germ_restr, map_div₀, hcw, hcw, mul_div_mul_left _ _ hc,
      ← div_div_div_cancel_right₀ hj0]
    exact div_mem (key w) (key w')
  have hle : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) (M.σ z) hη ≤
      (S.ratioField (Adelic.resPt z)).comap (M.σ.residueFieldMap z).hom :=
    Subfield.closure_le.2 hgen
  refine ⟨z, genericPoint_spec M.X, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hr.symm ▸ Subfield.mem_top y)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hR`. Take `⟨η, hη, hgen, hrat⟩` from `hR`. Establish `: IsIntegral R.X` using `(h.geo f₁ f₂ th k).isIntegral`. Use `sys_birational_of_ratField R.toModif R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ h.free₂ η hη hgen ?_` and prove the remaining obligations. Use `hrat using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Conclude with `⟨h.ext₂.equiv.symm w, by rw [← h.ext₂.restr_equiv, LinearEquiv.apply_symm_apply]⟩`. Introduce and unpack `⟨g, rfl⟩`.

Conclude with `⟨h.ext₂.equiv g, h.ext₂.restr_equiv g⟩`.
-/
theorem geo_second_birational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₂ → (h.geo f₁ f₂ th k).second.Birational := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hR
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  have : IsIntegral R.X := (h.geo f₁ f₂ th k).isIntegral
  refine sys_birational_of_ratField R.toModif R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ h.free₂ η hη hgen ?_
  convert hrat using 2
  ext s
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨h.ext₂.equiv.symm w, by rw [← h.ext₂.restr_equiv, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨h.ext₂.equiv g, h.ext₂.restr_equiv g⟩

end GlobalTheory.HSApp
