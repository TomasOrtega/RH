import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound
import Formalism.AdmissibleDesigns.InertiaActsTrivially
import Formalism.AdmissibleDesigns.SelfGood

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

section Gen

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

include hφ

/- English proof (translation)
Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem symm_equiv (g : G) (w : W) : φ.symm (ρW g w) = ρM g (φ.symm w) := by
  apply φ.injective
  rw [hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def psiZ : ReciprocityTheory.Gal.Z1 ρW →ₗ[O] coZ1s ρM where
  toFun f := ⟨fun g => φ.symm (f.1 g), fun g h => by
    show φ.symm (f.1 (g * h)) = φ.symm (f.1 g) + ρM g (φ.symm (f.1 h))
    rw [f.2.2 g h, map_add, symm_equiv ρM ρW φ hφ]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiZ_apply (f : ReciprocityTheory.Gal.Z1 ρW) (g : G) :
    (psiZ ρM ρW φ hφ f : G → M) g = φ.symm (f.1 g) := rfl

def psi : ReciprocityTheory.Gal.H1 ρW →ₗ[O] H1z ρM :=
  Submodule.mapQ _ _ (psiZ ρM ρW φ hφ) (by
    intro f hf
    obtain ⟨w, hw⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 ρW _).1 hf
    refine ⟨φ.symm w, funext fun g => ?_⟩
    change ρM g (φ.symm w) - φ.symm w = φ.symm (f.1 g)
    rw [show f.1 g = ρW g w - w from hw g, map_sub, symm_equiv ρM ρW φ hφ])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psi_mk (f : ReciprocityTheory.Gal.Z1 ρW) :
    psi ρM ρW φ hφ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (psiZ ρM ρW φ hφ f) := rfl

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[LinearMap.mem_ker, psi_mk, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`.

Take `⟨m, hm⟩` from `hx`. Use `show f.1 ∈ ReciprocityTheory.Gal.B1 ρW`. Rewrite using `[ReciprocityTheory.Gal.mem_coboundaries1]`. Use `⟨φ m, fun g => ?_⟩` and prove the remaining obligations. Establish `h2 : φ.symm (f.1 g) = ρM g m - m` using `by first`.

Consider the case `exact (congrFun hm g).symm`. Consider the case `exact hm g`. Consider the case `exact (hm g).symm`. Consider the case `exact congrFun hm g`. Rewrite using `[← hφ, ← map_sub, ← h2, LinearEquiv.apply_symm_apply]`.
-/
theorem psi_injective : Function.Injective (psi ρM ρW φ hφ) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, psi_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  obtain ⟨m, hm⟩ := hx
  show f.1 ∈ ReciprocityTheory.Gal.B1 ρW
  rw [ReciprocityTheory.Gal.mem_coboundaries1]
  refine ⟨φ m, fun g => ?_⟩
  have h2 : φ.symm (f.1 g) = ρM g m - m := by
    first
    | exact (congrFun hm g).symm
    | exact hm g
    | exact (hm g).symm
    | exact congrFun hm g
  rw [← hφ, ← map_sub, ← h2, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `hx`. Establish `hc' : IsLocallyConstant (c : G → M)` using `hc`. Establish `hcont : Continuous (fun g => φ ((c : G → M) g))` using `(hc'.comp (⇑φ)).continuous`. Establish `hcoc : ∀ g h, φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρW g (φ ((c : G → M) h))`. Introduce `g h`.

Rewrite using `[c.2 g h, map_add, hφ]`. Use `⟨Submodule.Quotient.mk ⟨fun g => φ ((c : G → M) g), hcont, hcoc⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[psi_mk]`. Use `show Submodule.Quotient.mk _ = Submodule.Quotient.mk c`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Simplify using `only [psiZ_apply, LinearEquiv.symm_apply_apply]`.
-/
theorem lc_mem_range {x : H1z ρM} (hx : x ∈ lcH1 ρM) : ∃ y, psi ρM ρW φ hφ y = x := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hc' : IsLocallyConstant (c : G → M) := hc
  have hcont : Continuous (fun g => φ ((c : G → M) g)) := (hc'.comp (⇑φ)).continuous
  have hcoc : ∀ g h, φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρW g (φ ((c : G → M) h)) := by
    intro g h
    rw [c.2 g h, map_add, hφ]
  refine ⟨Submodule.Quotient.mk ⟨fun g => φ ((c : G → M) g), hcont, hcoc⟩, ?_⟩
  rw [psi_mk]
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk c
  congr 1
  apply Subtype.ext
  funext g
  simp only [psiZ_apply, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Set `T : Submodule O (ReciprocityTheory.Gal.H1 ρW)` to `S.comap (psi ρM ρW φ hφ)`. Set `gT : T →ₗ[O] S` to `(psi ρM ρW φ hφ).restrict (fun x hx => hx)`. Establish `hg : Function.Bijective gT`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `psi_injective ρM ρW φ hφ` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hab`. Introduce and unpack `⟨x, hx⟩`. Take `⟨y, hy⟩` from `lc_mem_range ρM ρW φ hφ (hS hx)`.

Use `⟨⟨y, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show psi ρM ρW φ hφ y ∈ S`. Rewrite using `[hy]`. Conclude with `hx`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `hy`. Set `e` to `LinearEquiv.ofBijective gT hg`. Use `⟨(Submodule.inclusion (fun y hy => h y hy)).comp e.symm.toLinearMap, ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.inclusion_injective (fun y hy => h y hy)).comp e.symm.injective`.
-/
theorem injTie_of {S : Submodule O (H1z ρM)} {S' : Submodule O (ReciprocityTheory.Gal.H1 ρW)}
    (hS : S ≤ lcH1 ρM) (h : ∀ y, psi ρM ρW φ hφ y ∈ S → y ∈ S') : InjTie S S' := by
  let T : Submodule O (ReciprocityTheory.Gal.H1 ρW) := S.comap (psi ρM ρW φ hφ)
  let gT : T →ₗ[O] S := (psi ρM ρW φ hφ).restrict (fun x hx => hx)
  have hg : Function.Bijective gT := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply psi_injective ρM ρW φ hφ
      exact congrArg Subtype.val hab
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := lc_mem_range ρM ρW φ hφ (hS hx)
      refine ⟨⟨y, ?_⟩, ?_⟩
      · show psi ρM ρW φ hφ y ∈ S
        rw [hy]
        exact hx
      · apply Subtype.ext
        exact hy
  let e := LinearEquiv.ofBijective gT hg
  refine ⟨(Submodule.inclusion (fun y hy => h y hy)).comp e.symm.toLinearMap, ?_⟩
  exact (Submodule.inclusion_injective (fun y hy => h y hy)).comp e.symm.injective

end Gen

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions

section Unr

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite `h` using `[psi_mk]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (restrictCocycles1 ρM I (psiZ ρM ρW φ hφ f)) = 0 at h`. Rewrite `h` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨m, hm⟩` from `h`.

Use `show Submodule.Quotient.mk _ = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]`. Use `⟨φ m, fun g => ?_⟩` and prove the remaining obligations. Establish `hg' : φ.symm (f.1 ((g : Dg) : G)) = ρM ((g : Dg) : G) m - m`. Establish `h1` using `congrFun hm ⟨((g : Dg) : G), g.2⟩`.

Use `first`. Consider the case `exact h1.symm`. Consider the case `(simp [Formalism.NG.coD0] at h1; exact h1.symm)`. Consider the case `(simp [Formalism.NG.coD0] at h1; rw [← h1]; rfl)`. Use `show f.1 ((g : Dg) : G) = ρW ((g : Dg) : G) (φ m) - φ m`.

Rewrite using `[← hφ, ← map_sub, ← hg', LinearEquiv.apply_symm_apply]`.
-/
theorem unr_tie {I Dg : Subgroup G} (y : ReciprocityTheory.Gal.H1 ρW)
    (h : Formalism.NG.resH1 ρM I (psi ρM ρW φ hφ y) = 0) :
    ReciprocityTheory.Gal.resH1 (ρW.comp Dg.subtype) (I.subgroupOf Dg).subtype continuous_subtype_val
      (ReciprocityTheory.Gal.resH1 ρW Dg.subtype continuous_subtype_val y) = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [psi_mk] at h
  change Submodule.Quotient.mk (restrictCocycles1 ρM I (psiZ ρM ρW φ hφ f)) = 0 at h
  rw [Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨m, hm⟩ := h
  show Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
  refine ⟨φ m, fun g => ?_⟩
  have hg' : φ.symm (f.1 ((g : Dg) : G)) = ρM ((g : Dg) : G) m - m := by
    have h1 := congrFun hm ⟨((g : Dg) : G), g.2⟩
    first
    | exact h1.symm
    | (simp [Formalism.NG.coD0] at h1; exact h1.symm)
    | (simp [Formalism.NG.coD0] at h1; rw [← h1]; rfl)
  show f.1 ((g : Dg) : G) = ρW ((g : Dg) : G) (φ m) - φ m
  rw [← hφ, ← map_sub, ← hg', LinearEquiv.apply_symm_apply]

end Unr

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

def BkAt (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : ReciprocityTheory.Gal.H1 (Br.WKO i ρ π)),
    Formalism.NG.resH1 (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) (idx i dc w))
              (psi (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ x) ∈ F (idx i dc w) →
      ReciprocityTheory.Gal.resH1 (Br.WKO i ρ π) (decS D.nd w) continuous_subtype_val x ∈
        Br.bk D.loc D.nbr i w hw (WpO D.nd i ρ π)

/- English proof (translation)
Break down `(dc.cover w).mpr hw with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)`. Conclude with `Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩)`.
-/
theorem idx_mem_rows_cols {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    idx i dc w ∈ rowsN i dc ∪ Finset.univ.image (colIdx i dc) := by
  rcases (dc.cover w).mpr hw with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩)

/- English proof (translation)
Use `injTie_of (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).1`. Introduce `y hy`. Take `⟨hy1, hloc⟩` from `Submodule.mem_inf.mp hy`.

Establish `hunr` using `(Submodule.mem_inf.mp hy1).2`. Unfold `Br.selPi Br.selG Formalism.GaloisCohomology.SelAll`. Use `(ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).2 fun v => ?_` and prove the remaining obligations. Unfold `Formalism.GaloisCohomology.bkCond`. Use `split_ifs with h1 h2`.

Establish `hw : v ∈ placesOver D.host.E (D.nd.l i)` using `h1`. Establish `hm` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hloc (idx i dc v)) (idx_mem_rows_cols i dc hw)`. Establish `hb` using `hBk v hw y hm`. Unfold `Br.LlG`. Rewrite using `[dif_pos hw]`.

Conclude with `hb`. Conclude with `Submodule.mem_top`. Establish `hS : v ∉ D.nd.S i` using `fun h => h2 (Or.inl h)`. Establish `hQ : v ∉ D.nd.Q i` using `fun h => h2 (Or.inr h)`. Set `vo : K.QS.Vo i` to `⟨v, h1, hS, hQ⟩`.

Establish `hu` using `(Submodule.mem_iInf _).1 hunr vo`. Conclude with `unr_tie (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ y hu`.
-/
theorem tieSel1_of
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w))))
    (hBk : BkAt i dc ρ π M r χ φ hφ F) :
    TieSel1 i ρ π M r χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F (K.QS.Io i) := by
  refine injTie_of (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ ?_ ?_
  · intro x hx
    exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).1
  · intro y hy
    obtain ⟨hy1, hloc⟩ := Submodule.mem_inf.mp hy
    have hunr := (Submodule.mem_inf.mp hy1).2
    unfold Br.selPi Br.selG Formalism.GaloisCohomology.SelAll
    refine (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).2 fun v => ?_
    unfold Formalism.GaloisCohomology.bkCond
    split_ifs with h1 h2
    · have hw : v ∈ placesOver D.host.E (D.nd.l i) := h1
      have hm := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hloc (idx i dc v))
        (idx_mem_rows_cols i dc hw)
      have hb := hBk v hw y hm
      unfold Br.LlG
      rw [dif_pos hw]
      exact hb
    · exact Submodule.mem_top
    · have hS : v ∉ D.nd.S i := fun h => h2 (Or.inl h)
      have hQ : v ∉ D.nd.Q i := fun h => h2 (Or.inr h)
      let vo : K.QS.Vo i := ⟨v, h1, hS, hQ⟩
      have hu := (Submodule.mem_iInf _).1 hunr vo
      exact unr_tie (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ y hu

end Rec

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Row

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def LenOlSelf : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    lenOl (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) = eON i

def RowTie (rowLen : ℕ → ℕ∞) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (b : ℚ),
    RowAt (Br.PD D.loc D.nbr i (plOf i dc n) hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw).LL))
        (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (rDuO D.nd i r x)))
        ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (T2O D.nd i ρ π)) b →
      rowLen n ≠ ⊤ ∧
        ((rowLen n).toNat : ℚ) ≤
          b * ((lenOl (Br.PD D.loc D.nbr i (plOf i dc n) hw)
            (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw).LL))).toNat : ℚ)

/- English proof (translation)
Establish `h1 : idx i dc v = ((plSet i dc).equivFin ⟨v, hv⟩ : ℕ)`. Unfold `idx`. Rewrite using `[dif_pos hv]`. Rewrite using `[h1]`. Unfold `plOf`.

Rewrite using `[dif_pos (Fin.is_lt _)]`. Simplify using the standard rewrite rules.
-/
private theorem plOf_idx_of_mem_plSet (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ plSet i dc) :
    plOf i dc (idx i dc v) = v := by
  have h1 : idx i dc v = ((plSet i dc).equivFin ⟨v, hv⟩ : ℕ) := by
    unfold idx
    rw [dif_pos hv]
  rw [h1]
  unfold plOf
  rw [dif_pos (Fin.is_lt _)]
  simp

/- English proof (translation)
Unfold `rowsN at hn`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.mp hn`. Establish `hvp : v ∈ plSet i dc`. Unfold `plSet`. Simplify using `[hv]`.

Rewrite using `[plOf_idx_of_mem_plSet i dc v hvp]`. Conclude with `hv`.
-/
theorem plOf_mem_row {n : ℕ} (hn : n ∈ rowsN i dc) : plOf i dc n ∈ dc.row := by
  unfold rowsN at hn
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
  have hvp : v ∈ plSet i dc := by
    unfold plSet
    simp [hv]
  rw [plOf_idx_of_mem_plSet i dc v hvp]
  exact hv

/- English proof (translation)
Introduce `n hn`. Establish `hrow` using `plOf_mem_row i dc hn`. Establish `hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i)` using `(dc.cover _).mp (Or.inl hrow)`. Establish `hb` using `hadm (plOf i dc n) hw hrow (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (hG _ hw)`. Take `⟨h1, h2⟩` from `hT n hn hw (lenRow (plOf i dc n)) hb`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[hlen (plOf i dc n) hw]`. Combine the linear relations using `[h2, mul_comm (lenRow (plOf i dc n)) (((eON i).toNat : ℚ))]`.
-/
theorem tieRow_of (rowLen : ℕ → ℕ∞) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (hG : K.SelfGood i) (hadm : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow) (hlen : LenOlSelf i)
    (hT : RowTie i dc r ρ π rowLen) : TieRow i dc rowLen lenRow := by
  intro n hn
  have hrow := plOf_mem_row i dc hn
  have hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i) := (dc.cover _).mp (Or.inl hrow)
  have hb := hadm (plOf i dc n) hw hrow (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (hG _ hw)
  obtain ⟨h1, h2⟩ := hT n hn hw (lenRow (plOf i dc n)) hb
  refine ⟨h1, ?_⟩
  rw [hlen (plOf i dc n) hw] at h2
  linarith [h2, mul_comm (lenRow (plOf i dc n)) (((eON i).toNat : ℚ))]

end Row

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions

section ResCompat

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `first`. Consider the case `rfl`. Consider the case `(simp only [ReciprocityTheory.Gal.resH1, Formalism.NG.resH1, Submodule.mapQ_apply, psi_mk]; rfl)`.
-/
theorem psi_res (Dg : Subgroup G) (x : ReciprocityTheory.Gal.H1 ρW) :
    psi (resRep ρM Dg) (ρW.comp Dg.subtype) φ (fun g m => hφ g m)
        (ReciprocityTheory.Gal.resH1 ρW Dg.subtype continuous_subtype_val x) =
      Formalism.NG.resH1 ρM Dg (psi ρM ρW φ hφ x) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  first
  | rfl
  | (simp only [ReciprocityTheory.Gal.resH1, Formalism.NG.resH1, Submodule.mapQ_apply, psi_mk]; rfl)

end ResCompat

section RecLoc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

def BkLoc (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ n ∈ rowsN i dc ∪ Finset.univ.image (colIdx i dc),
    ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
      (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))),
      psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
          ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈ F n →
        y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π)

/- English proof (translation)
Introduce `w hw x hx`. Establish `hmem` using `idx_mem_rows_cols i dc hw`. Establish `hwp : w ∈ plSet i dc`. Unfold `plSet`. Break down `(dc.cover w).mpr hw with h' | h'` into its components or cases.

Simplify using `[h']`. Simplify using `[h']`. Establish `e : plOf i dc (idx i dc w) = w` using `plOf_idx_of_mem_plSet i dc w hwp`. Generalize the expression as in `hn : idx i dc w = n at *`. Substitute `e` using the available equality.

Apply `h n hmem hw` to reduce the goal to its premises. Use `first`. Consider the case `(rw [psi_res]; exact hx)`. Consider the case `(erw [psi_res]; exact hx)`.
-/
theorem bkAt_of_loc
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w))))
    (h : BkLoc i dc ρ π M r χ φ hφ F) : BkAt i dc ρ π M r χ φ hφ F := by
  intro w hw x hx
  have hmem := idx_mem_rows_cols i dc hw
  have hwp : w ∈ plSet i dc := by
    unfold plSet
    rcases (dc.cover w).mpr hw with h' | h'
    · simp [h']
    · simp [h']
  have e : plOf i dc (idx i dc w) = w := plOf_idx_of_mem_plSet i dc w hwp
  generalize hn : idx i dc w = n at *
  subst e
  apply h n hmem hw
  first
  | (rw [psi_res]; exact hx)
  | (erw [psi_res]; exact hx)

end RecLoc

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section LenUnit

/- English proof (translation)
Use `first`. Consider the case `(unfold Module.length; congr 1; exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f))`. Consider the case `(simp only [Module.length, Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f)])`. Consider the case `(unfold Module.length; exact Order.height_orderIso (Submodule.orderIsoMapComap f) ⊤)`.
-/
theorem length_semilinear {R S N M : Type} [CommRing R] [CommRing S] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module S M] (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (f : N ≃ₛₗ[(e : R →+* S)] M) :
    Module.length R N = Module.length S M := by
  first
  | (unfold Module.length; congr 1; exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f))
  | (simp only [Module.length, Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f)])
  | (unfold Module.length; exact Order.height_orderIso (Submodule.orderIsoMapComap f) ⊤)

def quotSL {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (x : R) :
    (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) where
  toFun := Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  invFun := (Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)).symm
  left_inv := RingEquiv.symm_apply_apply _
  right_inv := RingEquiv.apply_symm_apply _
  map_add' := map_add _
  map_smul' := by
    intro r y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, map_mul]
    rfl

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `w hw`. Unfold `lenOl eON`. Rewrite using `[Br.PD_p]`. Establish `h1` using `RingHomInvPair.of_ringEquiv (D.nbr i w hw).eO`. Establish `h2` using `RingHomInvPair.symm ((D.nbr i w hw).eO : D.nd.O i →+* ↥(OL (D.nbr i w hw).LL)) ((D.nbr i w hw).eO.symm : ↥(OL (D.nbr i w hw).LL) →+* D.nd.O i)`.

Establish `h` using `length_semilinear (D.nbr i w hw).eO (quotSL (D.nbr i w hw).eO ((D.nd.l i : ℕ) : D.nd.O i))`. Rewrite `h` using `[map_natCast]`. Conclude with `h.symm`.
-/
theorem lenOlSelf {D : D7} (i : D.nd.Loc) : LenOlSelf i := by
  intro w hw
  unfold lenOl eON
  rw [Br.PD_p]
  have h1 := RingHomInvPair.of_ringEquiv (D.nbr i w hw).eO
  have h2 := RingHomInvPair.symm ((D.nbr i w hw).eO : D.nd.O i →+* ↥(OL (D.nbr i w hw).LL))
    ((D.nbr i w hw).eO.symm : ↥(OL (D.nbr i w hw).LL) →+* D.nd.O i)
  have h := length_semilinear (D.nbr i w hw).eO (quotSL (D.nbr i w hw).eO ((D.nd.l i : ℕ) : D.nd.O i))
  rw [map_natCast] at h
  exact h.symm

/- English proof (translation)
Use `first`. Consider the case `exact tieRow_of i dc r ρ π rowLen lenRow hG hadm (lenOlSelf i) hT`. Consider the case `exact tieRow_of _ _ _ _ _ rowLen lenRow hG hadm (lenOlSelf i) hT`.
-/
theorem tieRow_rec {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (rowLen : ℕ → ℕ∞) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (hG : K.SelfGood i) (hadm : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow) (hT : RowTie i dc r ρ π rowLen) :
    TieRow i dc rowLen lenRow := by
  first
  | exact tieRow_of i dc r ρ π rowLen lenRow hG hadm (lenOlSelf i) hT
  | exact tieRow_of _ _ _ _ _ rowLen lenRow hG hadm (lenOlSelf i) hT

end LenUnit

end Formalism.MainNotions.N.K.Sel

end
