import Formalism.AdmissibleDesigns.InertiaActsTrivially

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.QS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Eval
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

structure Ev (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) : Prop where
  r_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
  chi_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    (((Dd.χ g : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)
  smul_eval : ∀ (f : Dd.T') (a : Dd.R') (x' : Dd.X'),
    ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x'
  blk_smul : ∀ (f : Dd.T') k (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k), f • m = ((f : Dd.X' → D.nd.O i) Dd.π') • m
  ρπ_eval : ∀ a : Dd.R', (Dd.ρπ a).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
    (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) Dd.π'
  ρk_eval : ∀ (a : Dd.R') k, (Dd.ρπ a).toSquareBlock (RepresentationBoundsCohomology.blk D.R) k = Dd.ρk k a
  pπ : Dd.p Dd.π' = π
  comp_mem : ∀ f ∈ D.nd.T i, (f ∘ Dd.p) ∈ Dd.T'

/- English proof (translation)
Take `⟨-, -, h3, -, h5, -, h7, -, h9, -, h11, h12, -, -, -, -, h17, h18, -⟩` from `hD`. Use `⟨h7, h12, h9, h11, h17, h18, h5, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Conclude with `Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)`.
-/
theorem ev_of (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Ev r π Dd := by
  obtain ⟨-, -, h3, -, h5, -, h7, -, h9, -, h11, h12, -, -, -, -, h17, h18, -⟩ := hD
  refine ⟨h7, h12, h9, h11, h17, h18, h5, fun f hf => ?_⟩
  rw [h3]
  exact Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct]`. Both sides reduce to the same expression.
-/
theorem act_eval (a : Dd.R') (x' : Dd.X') (η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') :
    ((a • η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') : Fin D.R.nV → FractionRing (D.nd.O i)) =
      ((a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x').mulVec
        (η : Fin D.R.nV → FractionRing (D.nd.O i)) := by
  funext k
  simp only [Matrix.mulVec, dotProduct]
  rfl

/- English proof (translation)
Take `⟨e, he⟩` from `hdec`. Establish `h` using `he g (e.symm (0, fun _ => 1))`. Establish `h1 : (mapM (toK D.nd i) (rO D.nd i r π)) g = 1`. Simplify using `only [mapM, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, hg, map_one]`. Rewrite `h` using `[h1, Matrix.one_mulVec, LinearEquiv.apply_symm_apply]`.

Establish `h2` using `congrFun (congrArg Prod.snd h) ⟨0, RepresentationBoundsCohomology.one_le_letterBlockLength D.R⟩`. Simplify using `only [mul_one] at h2`. Apply `Units.ext` to reduce the goal to its premises. Apply `IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))` to reduce the goal to its premises. Simplify using `using h2.symm`.
-/
theorem character_trivial_where_lattice {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (g : GE D.nd) (hg : rO D.nd i r π g = 1) : D.nd.chi i 1 g = 1 := by
  obtain ⟨e, he⟩ := hdec
  have h := he g (e.symm (0, fun _ => 1))
  have h1 : (mapM (toK D.nd i) (rO D.nd i r π)) g = 1 := by
    simp only [mapM, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, hg, map_one]
  rw [h1, Matrix.one_mulVec, LinearEquiv.apply_symm_apply] at h
  have h2 := congrFun (congrArg Prod.snd h) ⟨0, RepresentationBoundsCohomology.one_le_letterBlockLength D.R⟩
  simp only [mul_one] at h2
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  simpa using h2.symm

end Eval

section G4
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

/- English proof (translation)
Establish `h` using `hG4 x v.1 v.2.1 v.2.2.1 v.2.2.2 g hg`. Simplify using `[rO, h]`.
-/
theorem rO_one_of_Io (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (v : Vo i) (g : GE D.nd) (hg : g ∈ Io i v) (x : D.nd.X i) :
    rO D.nd i r x g = 1 := by
  have h := hG4 x v.1 v.2.1 v.2.2.1 v.2.2.2 g hg
  simp [rO, h]

/- English proof (translation)
Introduce `v g hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x'`. Rewrite using `[hE.r_eval, rO_one_of_Io i r hG4 v g hg]`.

Simplify using the standard rewrite rules. Establish `hc` using `character_trivial_where_lattice hdec g (rO_one_of_Io i r hG4 v g hg π)`. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x'`.

Rewrite using `[hE.chi_eval, hc]`. Simplify using the standard rewrite rules.
-/
theorem inertia_triviality_clause (hE : Ev r π Dd) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) : InertiaActsTrivially i Dd := by
  intro v g hg
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    funext x'
    rw [hE.r_eval, rO_one_of_Io i r hG4 v g hg]
    simp
  · have hc := character_trivial_where_lattice hdec g (rO_one_of_Io i r hG4 v g hg π)
    apply Units.ext
    apply Subtype.ext
    funext x'
    rw [hE.chi_eval, hc]
    simp

/- English proof (translation)
Introduce `x' hx η _ hη`. Take `⟨g, hg⟩` from `Inst.exists_nonfixed_twisted_vector (N := D.nd) (r := r) hG6 (Dd.p x') hx η hη`. Use `⟨g, fun h => hg ?_⟩` and prove the remaining obligations. Establish `h2 : ((((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') : Fin D.R.nV → FractionRing (D.nd.O i)) = (η : Fin D.R.nV → FractionRing (D.nd.O i))` using `h`. Rewrite `h2` using `[act_eval, hE.smul_eval, hE.r_eval]`.

Establish `hi : ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)`. Rewrite using `[← map_inv, hE.chi_eval, map_inv]`. Rewrite `h2` using `[hi]`. Establish `e : ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) • (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).mulVec (η : Fin D.R.nV → FractionRing (D.nd.O i)) = (algebraMap (D.nd.O i) (FractionRing (D.nd …` using `by first`. Consider the case `exact Matrix.smul_mulVec_assoc _ _ _`.

Consider the case `exact Matrix.smul_mulVec _ _ _`. Conclude with `e.symm.trans h2`.
-/
theorem no_fixed_vector_off_z (hE : Ev r π Dd) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : NoFixedVectorOffZ i Dd := by
  intro x' hx η _ hη
  obtain ⟨g, hg⟩ := Inst.exists_nonfixed_twisted_vector (N := D.nd) (r := r) hG6 (Dd.p x') hx η hη
  refine ⟨g, fun h => hg ?_⟩
  have h2 : ((((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') :
      Fin D.R.nV → FractionRing (D.nd.O i)) = (η : Fin D.R.nV → FractionRing (D.nd.O i)) := h
  rw [act_eval, hE.smul_eval, hE.r_eval] at h2
  have hi : ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' =
      (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [← map_inv, hE.chi_eval, map_inv]
  rw [hi] at h2
  have e : ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).mulVec
        (η : Fin D.R.nV → FractionRing (D.nd.O i)) =
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
      ((rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).mulVec
        (η : Fin D.R.nV → FractionRing (D.nd.O i)) := by
    first
    | exact Matrix.smul_mulVec_assoc _ _ _
    | exact Matrix.smul_mulVec _ _ _
  exact e.symm.trans h2
end G4

section Cover
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

/- English proof (translation)
Unfold `Fpos`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `inf_le_right`. Conclude with `bot_le`.

Conclude with `le_rfl`. Conclude with `bot_le`.
-/
theorem first_character_unramified (w : ℕ) : Fpos i dc Dd (c1 (D := D)) w ≤ unrH1 (resU i dc Dd (c1 (D := D)) w) (I i dc w) := by
  unfold Fpos
  split_ifs
  · exact le_rfl
  · exact inf_le_right
  · exact bot_le
  · exact le_rfl
  · exact bot_le

/- English proof (translation)
Establish `hA : Aw i dc (idx i dc v) = Av v`. Unfold `Aw Av`. Rewrite using `[plOf_idx i dc hv]`. Introduce `g hg`. Establish `hg' : g ∈ Ine (F` using `D.host.E) (Aw i dc (idx i dc v)) := hA ▸ hg`.

Use `Subgroup.mem_map.2 ⟨⟨g, Ine_le_Dec _ hg'⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_subgroupOf.2 hg'`.
-/
theorem ine_le_I {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc) :
    Ine (F := D.host.E) (Av v) ≤ (I i dc (idx i dc v)).map (decs D.host.E (Aw i dc) (idx i dc v)).subtype := by
  have hA : Aw i dc (idx i dc v) = Av v := by
    unfold Aw Av
    rw [plOf_idx i dc hv]
  intro g hg
  have hg' : g ∈ Ine (F := D.host.E) (Aw i dc (idx i dc v)) := hA ▸ hg
  refine Subgroup.mem_map.2 ⟨⟨g, Ine_le_Dec _ hg'⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 hg'

/- English proof (translation)
Introduce `v`. Distinguish the cases in `hl : v ∈ placesOver D.host.E (D.nd.l i)`. Use `right`. Use `right`. Establish `hrc` using `(dc.cover v).2 hl`.

Establish `hv : v ∈ plSet i dc`. Unfold `plSet`. Break down `hrc with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ h)`. Conclude with `Finset.mem_union_left _ (Finset.mem_union_right _ h)`.

Use `⟨idx i dc v, ?_, I i dc (idx i dc v), first_character_unramified i dc Dd _, ine_le_I i dc hv⟩` and prove the remaining obligations. Break down `hrc with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))`. Conclude with `Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩)`. Distinguish the cases in `hS : v ∈ D.nd.S i`.

Conclude with `Or.inr (Or.inl ⟨⟨v, hS⟩, le_rfl⟩)`. Distinguish the cases in `hQ : v ∈ D.nd.Q i`. Use `right`. Use `right`. Establish `hv : v ∈ plSet i dc` using `Finset.mem_union_right _ hQ`.

Conclude with `⟨idx i dc v, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ)), I i dc (idx i dc v), first_character_unramified i dc Dd _, ine_le_I i dc hv⟩`. Conclude with `Or.inl ⟨⟨v, hl, hS, hQ⟩, le_rfl⟩`.
-/
theorem coverClause : CoverClause i dc Dd := by
  intro v
  by_cases hl : v ∈ placesOver D.host.E (D.nd.l i)
  · right; right
    have hrc := (dc.cover v).2 hl
    have hv : v ∈ plSet i dc := by
      unfold plSet
      rcases hrc with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    refine ⟨idx i dc v, ?_, I i dc (idx i dc v), first_character_unramified i dc Dd _, ine_le_I i dc hv⟩
    rcases hrc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩)
  by_cases hS : v ∈ D.nd.S i
  · exact Or.inr (Or.inl ⟨⟨v, hS⟩, le_rfl⟩)
  by_cases hQ : v ∈ D.nd.Q i
  · right; right
    have hv : v ∈ plSet i dc := Finset.mem_union_right _ hQ
    exact ⟨idx i dc v, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ)),
      I i dc (idx i dc v), first_character_unramified i dc Dd _, ine_le_I i dc hv⟩
  · exact Or.inl ⟨⟨v, hl, hS, hQ⟩, le_rfl⟩

end Cover

section GlobalTheory
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

/- English proof (translation)
Establish `h'` using `h`. Simplify using `only [RepresentationBoundsCohomology.blk, RepresentationBoundsCohomology.blkG] at h'`. Use `split_ifs at h' with h1`. Conclude with `absurd h'.symm (Fin.succ_ne_zero c')`. Apply `Fin.ext` to reduce the goal to its premises.

Establish `h2` using `congrArg Fin.val h'`. Simplify using `only [Fin.val_succ] at h2`. Simplify using `only [Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem blk_eq {c' : Fin D.R.t} (a : Fin D.R.nV) (h : RepresentationBoundsCohomology.blk D.R a = c'.succ) :
    a = (Fin.natAdd D.R.r c' : Fin (D.R.r + D.R.t)) := by
  have h' := h
  simp only [RepresentationBoundsCohomology.blk, RepresentationBoundsCohomology.blkG] at h'
  split_ifs at h' with h1
  · exact absurd h'.symm (Fin.succ_ne_zero c')
  · apply Fin.ext
    have h2 := congrArg Fin.val h'
    simp only [Fin.val_succ] at h2
    simp only [Fin.val_natAdd]
    omega

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `hk : ∀ j : {a // RepresentationBoundsCohomology.blk D.R a = c'.succ}, j = k`. Introduce `j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[blk_eq j.1 j.2, blk_eq k.1 k.2]`.

Use `show ∑ j, (Dd.ρk c'.succ a) k j • m j = _`. Rewrite using `[Finset.sum_eq_single k (fun j _ hj => absurd (hk j) hj) (fun h => absurd (Finset.mem_univ k) h)]`. Rewrite using `[← hE.ρk_eval]`. Use `show Dd.ρπ a k.1 k.1 • m k = Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') • m k`. Rewrite using `[blk_eq k.1 k.2]`.
-/
theorem blk_act (c' : Fin D.R.t) (a : Dd.R') (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) (hE : Ev r π Dd) :
    a • m = (Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) • m := by
  funext k
  have hk : ∀ j : {a // RepresentationBoundsCohomology.blk D.R a = c'.succ}, j = k := by
    intro j
    apply Subtype.ext
    rw [blk_eq j.1 j.2, blk_eq k.1 k.2]
  show ∑ j, (Dd.ρk c'.succ a) k j • m j = _
  rw [Finset.sum_eq_single k (fun j _ hj => absurd (hk j) hj) (fun h => absurd (Finset.mem_univ k) h)]
  rw [← hE.ρk_eval]
  show Dd.ρπ a k.1 k.1 • m k = Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') • m k
  rw [blk_eq k.1 k.2]

end GlobalTheory

section LocQ
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

variable {i r ρ π Dd} in

/- English proof (translation)
Apply `IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))` to reduce the goal to its premises. Establish `h1 : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (rO D.nd i r π g (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c'))`. Establish `h` using `congrFun (congrFun (hE.ρπ_eval (Dd.r g)) (Fin.natAdd D.R.r c')) (Fin.natAdd D.R.r c')`. Rewrite `h` using `[hE.r_eval, hE.pπ]`. Conclude with `h`.

Rewrite using `[h1]`. Conclude with `congrArg _ (hN.2.1 g c')`.
-/
theorem rblk (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd) :
    Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') =
      ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have h1 : algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (rO D.nd i r π g (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) := by
    have h := congrFun (congrFun (hE.ρπ_eval (Dd.r g)) (Fin.natAdd D.R.r c')) (Fin.natAdd D.R.r c')
    rw [hE.r_eval, hE.pπ] at h
    exact h
  rw [h1]
  exact congrArg _ (hN.2.1 g c')

variable {i r ρ π Dd} in

/- English proof (translation)
Rewrite using `[blk_act c' _ m hE, rblk hE hN c' g]`.
-/
theorem r_act (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd)
    (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) :
    Dd.r g • m = ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) • m := by
  rw [blk_act c' _ m hE, rblk hE hN c' g]

/- English proof (translation)
The claim follows from `(h5x v hv).2.1 ((c' : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by have := c'.2; omega⟩) g hg`.
-/
theorem chi_c_eq (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ D.nd.S i ∨ v ∈ D.nd.Q i)
    (c' : Fin D.R.t) (g : GE D.nd) (hg : g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    D.nd.chi i ((c' : ℕ) + 1) g = D.nd.chi i 1 g :=
  (h5x v hv).2.1 ((c' : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by have := c'.2; omega⟩) g hg

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[mul_assoc]`.
-/
theorem conj_eq {M : Type*} [Monoid M] (u : Mˣ) (b c : M) (h : ↑u⁻¹ * b * ↑u = c) : b = ↑u * c * ↑u⁻¹ := by
  subst h
  simp [mul_assoc]

/- English proof (translation)
Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hw`. Rewrite using `[plOf_idx i dc (Finset.mem_union_right _ hv)]`. Conclude with `hv`.
-/
theorem plOf_mem_Q {w : ℕ} (hw : w ∈ qsN i dc) : plOf i dc w ∈ D.nd.Q i := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  rw [plOf_idx i dc (Finset.mem_union_right _ hv)]
  exact hv

/- English proof (translation)
Introduce `w hw`. Establish `hq` using `plOf_mem_Q i dc hw`. Establish `hγ : D.nd.gam0 i (plOf i dc w) ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 (plOf i dc w)) := D.nd.locNd_chebotarevPlace_mem i _`. Establish `hdiag` using `fun x => ((hG5 (plOf i dc w) (Or.inr hq)).1 (Or.inl hq) x)`. Use `⟨?_, Subgroup.mem_subgroupOf.2 hγ, ?_, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `Fpos`. Rewrite using `[if_pos hw]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x'`. Simplify using `only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one, ZeroMemClass.coe_zero, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval]`. Apply the tactic sequence `try simp only [OneMemClass.coe_one, Pi.one_apply]`. Establish `hz : ((ζ i dc Dd w : Dd.T') : Dd.X' → D.nd.O i) x' = ((D.nd.chi i 1 (D.nd.gam0 i (plOf i dc w)) : (D.nd.O i)ˣ) : D.nd.O i)` using `hE.chi_eval _ x'`. Rewrite using `[hz]`. Establish `h0` using `congrArg (fun X => X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) ((hdiag (Dd.p x')).1 _ hγ)`.

Apply the tactic sequence `try dsimp only at h0`. Rewrite `h0` using `[Matrix.map_zero _ (map_zero _)]`. Establish `hs : (chi1 D.nd i (D.nd.gam0 i (plOf i dc w)) • (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (chi1 D.nd i (D.nd.gam0 i (plOf i dc w))) • 1`. Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [h]`.

Rewrite using `[← h0, Matrix.map_mul, Matrix.map_sub, Matrix.map_sub, Matrix.map_one, hs]`. Both sides reduce to the same expression. Apply the tactic sequence `all_goals simp`. Introduce `g hg`. Establish `hg' : (g : GE D.nd) ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 (plOf i dc w)) := Subgroup.mem_subgroupOf.1 hg`.

Establish `hex : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n` using `hQP _ hq _ hg'`. Establish `hn : D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ nQ i dc w g`. Unfold `nQ`. Rewrite using `[dif_pos hex]`. Conclude with `Nat.find_spec hex`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x'`. Simplify using `only [SubmonoidClass.coe_pow, Pi.pow_apply]`. Rewrite using `[hE.r_eval, hE.r_eval]`.

Take `⟨Pm, hPm⟩` from `(hdiag (Dd.p x')).2`. Establish `h1` using `hPm _ hg'`. Establish `h2` using `hPm _ hγ`. Rewrite `h1`, `h2` using `[Units.val_mul, Units.val_mul]`. Establish `e1` using `conj_eq Pm _ _ h1`.

Establish `e2` using `conj_eq Pm _ _ h2`. Establish `m1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (g : GE D.nd) : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))` using `rfl`. Establish `m2 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (D.nd.gam0 i (plOf i dc w)) : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = (rO D.nd i r (Dd.p x') (γQ i dc w : GE D.nd)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))` using `rfl`. Rewrite `e1` using `[m1]`. Rewrite `e2` using `[m2]`.

Rewrite using `[e1, e2, Units.conj_pow, Matrix.diagonal_pow]`. Use `congr 2`. Use `congr 1`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `try simp only [Pi.pow_apply]`.

Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[← map_pow]`. Use `congr 1`. Use `congrArg (fun u : (D.nd.O i)ˣ => (u : D.nd.O i)) hn` as an intermediate fact.

Simplify using `only [Units.val_pow_eq_pow_val] at this`. Conclude with `this`. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x'`.

Simplify using `only [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, Pi.pow_apply]`. Rewrite using `[hE.chi_eval, hE.chi_eval, hn, Units.val_pow_eq_pow_val]`. Introduce `g hg m`. Establish `hg' : (g : GE D.nd) ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 (plOf i dc w)) := Subgroup.mem_subgroupOf.1 hg`. Unfold `uElt`.

Rewrite using `[smul_assoc, r_act hE hN c', hE.blk_smul, chi_c_eq i h5x _ (Or.inr hq) c' _ hg']`. Establish `hi : ((((Dd.χ (g : GE D.nd))⁻¹ : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) Dd.π' = (((D.nd.chi i 1 (g : GE D.nd))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)`. Rewrite using `[← map_inv, hE.chi_eval, map_inv]`. Rewrite using `[hi, smul_smul, Units.inv_mul, one_smul]`. Introduce `m`.

Rewrite using `[r_act hE hN c', chi_c_eq i h5x _ (Or.inr hq) c' (γQ i dc w : GE D.nd) hγ]`. Both sides reduce to the same expression.
-/
theorem locQ (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (hQP : QPow i) (c' : Fin D.R.t) :
    ∀ w ∈ qsN i dc, Fpos i dc Dd c'.succ w = unrH1 (resU i dc Dd c'.succ w) (I i dc w) ∧ γQ i dc w ∈ I i dc w ∧
      (Dd.r (γQ i dc w : GE D.nd) - 1) * (Dd.r (γQ i dc w : GE D.nd) - algebraMap Dd.T' Dd.R' (ζ i dc Dd w)) = 0 ∧
      ((Dd.χ (γQ i dc w : GE D.nd) : Dd.T'ˣ) : Dd.T') = ζ i dc Dd w ∧
      (∀ g ∈ I i dc w, Dd.r (g : GE D.nd) = Dd.r (γQ i dc w : GE D.nd) ^ nQ i dc w g ∧
        Dd.χ (g : GE D.nd) = Dd.χ (γQ i dc w : GE D.nd) ^ nQ i dc w g) ∧
      (∀ g ∈ I i dc w, ∀ m : Mc i Dd c'.succ, uElt Dd.r Dd.χ (g : GE D.nd) • m = m) ∧
      (∀ m : Mc i Dd c'.succ, Dd.r (γQ i dc w : GE D.nd) • m = ζO i dc w • m) := by
  intro w hw
  have hq := plOf_mem_Q i dc hw
  have hγ : D.nd.gam0 i (plOf i dc w) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (plOf i dc w)) := D.nd.locNd_chebotarevPlace_mem i _
  have hdiag := fun x => ((hG5 (plOf i dc w) (Or.inr hq)).1 (Or.inl hq) x)
  refine ⟨?_, Subgroup.mem_subgroupOf.2 hγ, ?_, rfl, ?_, ?_, ?_⟩
  · unfold Fpos
    rw [if_pos hw]
  · apply Subtype.ext
    funext x'
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]
    rw [Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval]
    try simp only [OneMemClass.coe_one, Pi.one_apply]
    have hz : ((ζ i dc Dd w : Dd.T') : Dd.X' → D.nd.O i) x' =
        ((D.nd.chi i 1 (D.nd.gam0 i (plOf i dc w)) : (D.nd.O i)ˣ) : D.nd.O i) := hE.chi_eval _ x'
    rw [hz]
    have h0 := congrArg (fun X => X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
      ((hdiag (Dd.p x')).1 _ hγ)
    try dsimp only at h0
    rw [Matrix.map_zero _ (map_zero _)] at h0
    have hs : (chi1 D.nd i (D.nd.gam0 i (plOf i dc w)) • (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))).map
        (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
        algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (chi1 D.nd i (D.nd.gam0 i (plOf i dc w))) • 1 := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [← h0, Matrix.map_mul, Matrix.map_sub, Matrix.map_sub, Matrix.map_one, hs]
    · rfl
    all_goals simp
  · intro g hg
    have hg' : (g : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (plOf i dc w)) := Subgroup.mem_subgroupOf.1 hg
    have hex : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n :=
      hQP _ hq _ hg'
    have hn : D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ nQ i dc w g := by
      unfold nQ
      rw [dif_pos hex]
      exact Nat.find_spec hex
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      funext x'
      simp only [SubmonoidClass.coe_pow, Pi.pow_apply]
      rw [hE.r_eval, hE.r_eval]
      obtain ⟨Pm, hPm⟩ := (hdiag (Dd.p x')).2
      have h1 := hPm _ hg'
      have h2 := hPm _ hγ
      rw [Units.val_mul, Units.val_mul] at h1 h2
      have e1 := conj_eq Pm _ _ h1
      have e2 := conj_eq Pm _ _ h2
      have m1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (g : GE D.nd) : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
          (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
      have m2 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (D.nd.gam0 i (plOf i dc w)) : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
          (rO D.nd i r (Dd.p x') (γQ i dc w : GE D.nd)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
      rw [m1] at e1
      rw [m2] at e2
      rw [e1, e2, Units.conj_pow, Matrix.diagonal_pow]
      congr 2
      congr 1
      funext k
      try simp only [Pi.pow_apply]
      split_ifs
      · simp
      · rw [← map_pow]
        congr 1
        have := congrArg (fun u : (D.nd.O i)ˣ => (u : D.nd.O i)) hn
        simp only [Units.val_pow_eq_pow_val] at this
        exact this
    · apply Units.ext
      apply Subtype.ext
      funext x'
      simp only [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, Pi.pow_apply]
      rw [hE.chi_eval, hE.chi_eval, hn, Units.val_pow_eq_pow_val]
  · intro g hg m
    have hg' : (g : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (plOf i dc w)) := Subgroup.mem_subgroupOf.1 hg
    unfold uElt
    rw [smul_assoc, r_act hE hN c', hE.blk_smul, chi_c_eq i h5x _ (Or.inr hq) c' _ hg']
    have hi : ((((Dd.χ (g : GE D.nd))⁻¹ : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) Dd.π' =
        (((D.nd.chi i 1 (g : GE D.nd))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      rw [← map_inv, hE.chi_eval, map_inv]
    rw [hi, smul_smul, Units.inv_mul, one_smul]
  · intro m
    rw [r_act hE hN c', chi_c_eq i h5x _ (Or.inr hq) c' (γQ i dc w : GE D.nd) hγ]
    rfl

end LocQ

section Assemble
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def LocS (c : Fin (D.R.t + 1)) : Prop :=
  ∀ v, ∀ g ∈ IS i v, ∃ a : Dd.R', a * ((Dd.r g - algebraMap Dd.T' Dd.R' ((Dd.χ g : Dd.T'ˣ) : Dd.T')) * Dd.E) = 0 ∧
    ∀ m : Mc i Dd c, a • m = 0 → m = 0

/- English proof (translation)
Assemble the required witnesses or components as `⟨locQ i dc r ρ π Dd hE hN hG5 h5x hQP c', inertia_triviality_clause i r ρ π Dd hE hG4 hdec, hS⟩`.
-/
theorem locClause (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QPow i) (c' : Fin D.R.t)
    (hS : LocS i Dd c'.succ) : LocClause i dc Dd c'.succ :=
  ⟨locQ i dc r ρ π Dd hE hN hG5 h5x hQP c', inertia_triviality_clause i r ρ π Dd hE hG4 hdec, hS⟩

/- English proof (translation)
The claim follows from `Fin.ext rfl`.
-/
theorem c1_eq : (c1 (D := D)) = Fin.succ (⟨0, RepresentationBoundsCohomology.one_le_letterBlockLength D.R⟩ : Fin D.R.t) := Fin.ext rfl

end Assemble

section LocSpde
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

/- English proof (translation)
Simplify using `only [mul_sub, sub_mul, mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]`.
-/
theorem conj_prod {M : Type*} [Ring M] (u : Mˣ) (a b x y : M) :
    (↑u * a * ↑u⁻¹ - x) * (↑u * b * ↑u⁻¹ - y) =
      ↑u * ((a - ↑u⁻¹ * x * ↑u) * (b - ↑u⁻¹ * y * ↑u)) * ↑u⁻¹ := by
  simp only [mul_sub, sub_mul, mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left,
    Units.mul_inv, mul_one]

/- English proof (translation)
Take `⟨h1, -⟩` from `(D.nd.S_def i v).1 hS`. Break down `h1 with h | h | h` into its components or cases. Conclude with `absurd ⟨0, h⟩ hv`. Conclude with `absurd ⟨1, h⟩ hv`. Use `split_ifs at h with hl`.

Conclude with `Or.inr ⟨hl, h⟩`. Conclude with `Or.inl h`.
-/
theorem S_pde {v : HeightOneSpectrum (𝓞 D.host.E)} (hS : v ∈ D.nd.S i)
    (hv : ¬ ∃ k, v ∈ placesOver D.host.E (D.host.g k)) :
    v ∈ placesOver D.host.E D.host.pde ∨ (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde') := by
  obtain ⟨h1, -⟩ := (D.nd.S_def i v).1 hS
  rcases h1 with h | h | h
  · exact absurd ⟨0, h⟩ hv
  · exact absurd ⟨1, h⟩ hv
  · split_ifs at h with hl
    · exact Or.inr ⟨hl, h⟩
    · exact Or.inl h

/- English proof (translation)
Establish `hS` using `v.2`. Establish `hcase` using `S_pde i hS hv`. Establish `hA` using `(hG5 v.1 (Or.inl hS)).1 (by`. Break down `hcase with h | h` into its components or cases. Conclude with `Or.inr (Or.inl h)`.

Conclude with `Or.inr (Or.inr h))`. Establish `hu : IsUnit (D.nd.zeta i v.1 - 1)` using `(h5x v.1 (Or.inl hS)).2.2.2 hS hcase`. Establish `hγ` using `D.nd.locNd_chebotarevPlace_mem i v.1`. Use `⟨Dd.r (D.nd.gam0 i v.1) - 1, ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `x'`. Simplify using `only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one, ZeroMemClass.coe_zero, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]`. Rewrite using `[Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval, hE.r_eval, hE.chi_eval]`. Apply the tactic sequence `try simp only [OneMemClass.coe_one, Pi.one_apply]`. Rewrite using `[← mul_assoc]`.

Use `(congrArg (· * _) ?_).trans (zero_mul _)` and prove the remaining obligations. Take `⟨Pm, hPm⟩` from `(hA (Dd.p x')).2`. Establish `h1` using `hPm _ hγ`. Establish `h2` using `hPm _ hg`. Rewrite `h1`, `h2` using `[Units.val_mul, Units.val_mul]`.

Establish `e1` using `conj_eq Pm _ _ h1`. Establish `e2` using `conj_eq Pm _ _ h2`. Establish `m1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (D.nd.gam0 i v.1) : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = (rO D.nd i r (Dd.p x') (D.nd.gam0 i v.1)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))` using `rfl`. Establish `m2 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))` using `rfl`. Rewrite `e1` using `[m1]`.

Rewrite `e2` using `[m2]`. Rewrite using `[e1, e2, conj_prod]`. Establish `hc1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = 1` using `by simp`. Establish `hc2 : ∀ c : KK D.nd i, ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (c • (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i))) * ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = c • 1` using `by intro c; simp`. Rewrite using `[hc1, hc2]`.

Establish `hz : ∀ (d : Fin D.R.nV → KK D.nd i) (c : KK D.nd i), (Matrix.diagonal d - c • 1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Matrix.diagonal (fun k => d k - c)`. Introduce `d c`. Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [h]`. Establish `hz1 : ∀ (d : Fin D.R.nV → KK D.nd i), (Matrix.diagonal d - 1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Matrix.diagonal (fun k => d k - 1)`.

Introduce `d`. Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [h]`. Rewrite using `[hz1, hz, Matrix.diagonal_mul_diagonal]`. Establish `hd : ∀ f : Fin D.R.nV → KK D.nd i, f = 0 → ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * Matrix.diagonal f * ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = 0`.

Introduce `f hf`. Substitute `hf` using the available equality. Simplify using the standard rewrite rules. Apply `hd` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp [chi1]`. Introduce `m hm`. Rewrite `hm` using `[sub_smul, r_act hE hN c', one_smul, chi_c_eq i h5x _ (Or.inl hS) c' _ hγ]`. Establish `h1 : (D.nd.zeta i v.1 - 1) • m = 0`.

Rewrite using `[sub_smul, one_smul]`. Conclude with `hm`. Take `⟨u, hu'⟩` from `hu`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`.

Use `_ = 0 := by rw [hu', h1, smul_zero]`.
-/
theorem locS_pde (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (c' : Fin D.R.t) (v : VS i) (hv : ¬ ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)) (g : GE D.nd)
    (hg : g ∈ IS i v) :
    ∃ a : Dd.R', a * ((Dd.r g - algebraMap Dd.T' Dd.R' ((Dd.χ g : Dd.T'ˣ) : Dd.T')) * Dd.E) = 0 ∧
      ∀ m : Mc i Dd c'.succ, a • m = 0 → m = 0 := by
  have hS := v.2
  have hcase := S_pde i hS hv
  have hA := (hG5 v.1 (Or.inl hS)).1 (by
    rcases hcase with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))
  have hu : IsUnit (D.nd.zeta i v.1 - 1) := (h5x v.1 (Or.inl hS)).2.2.2 hS hcase
  have hγ := D.nd.locNd_chebotarevPlace_mem i v.1
  refine ⟨Dd.r (D.nd.gam0 i v.1) - 1, ?_, ?_⟩
  · apply Subtype.ext
    funext x'
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]
    rw [Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval, hE.r_eval, hE.chi_eval]
    try simp only [OneMemClass.coe_one, Pi.one_apply]
    rw [← mul_assoc]
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    obtain ⟨Pm, hPm⟩ := (hA (Dd.p x')).2
    have h1 := hPm _ hγ
    have h2 := hPm _ hg
    rw [Units.val_mul, Units.val_mul] at h1 h2
    have e1 := conj_eq Pm _ _ h1
    have e2 := conj_eq Pm _ _ h2
    have m1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (D.nd.gam0 i v.1) : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        (rO D.nd i r (Dd.p x') (D.nd.gam0 i v.1)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
    have m2 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
    rw [m1] at e1
    rw [m2] at e2
    rw [e1, e2, conj_prod]
    have hc1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = 1 := by simp
    have hc2 : ∀ c : KK D.nd i, ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (c • (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i))) * ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        c • 1 := by intro c; simp
    rw [hc1, hc2]
    have hz : ∀ (d : Fin D.R.nV → KK D.nd i) (c : KK D.nd i),
        (Matrix.diagonal d - c • 1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Matrix.diagonal (fun k => d k - c) := by
      intro d c
      ext a b
      by_cases h : a = b <;> simp [h]
    have hz1 : ∀ (d : Fin D.R.nV → KK D.nd i),
        (Matrix.diagonal d - 1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Matrix.diagonal (fun k => d k - 1) := by
      intro d
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hz1, hz, Matrix.diagonal_mul_diagonal]
    have hd : ∀ f : Fin D.R.nV → KK D.nd i, f = 0 →
        ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * Matrix.diagonal f * ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = 0 := by
      intro f hf
      subst hf
      simp
    apply hd
    funext k
    simp only [Pi.zero_apply]
    split_ifs <;> simp [chi1]
  · intro m hm
    rw [sub_smul, r_act hE hN c', one_smul, chi_c_eq i h5x _ (Or.inl hS) c' _ hγ] at hm
    have h1 : (D.nd.zeta i v.1 - 1) • m = 0 := by
      rw [sub_smul, one_smul]
      exact hm
    obtain ⟨u, hu'⟩ := hu
    calc m = ((u⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ((u : D.nd.O i) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu', h1, smul_zero]
end LocSpde

section LocSg
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

/- English proof (translation)
Establish `hS` using `v.2`. Establish `hT : TameGen D.nd (D.nd.plOm.1 v.1) (D.nd.gam0 i v.1)` using `(D.nd.restN_tameGenerator_generates i v.1 (Or.inl hS)).2`. Take `⟨Pp, hPu, hPx⟩` from `(hG5 v.1 (Or.inl hS)).2 hv hS hT`. Establish `hγ` using `D.nd.locNd_chebotarevPlace_mem i v.1`. Set `φ : D.nd.T i → Dd.T'` to `fun f => ⟨(f : D.nd.X i → D.nd.O i) ∘ Dd.p, hE.comp_mem _ f.2⟩`.

Use `⟨∑ k ∈ Finset.range (Pp.natDegree + 1), φ (Pp.coeff k) • Dd.r (D.nd.gam0 i v.1) ^ k, ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x'`. Establish `hdeg : (Pp.map ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) (Dd.p x')).comp (D.nd.T i).val.toRingHom)).natDegree < Pp.natDegree + 1` using `Nat.lt_succ_of_le (Polynomial.natDegree_map_le)`. Establish `h0` using `congrArg (fun X => X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) (hPx (Dd.p x') g hg)`.

Apply the tactic sequence `try dsimp only at h0`. Rewrite `h0` using `[Matrix.map_zero _ (map_zero _), Polynomial.aeval_eq_sum_range' hdeg]`. Establish `hF : ∀ A : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i), A.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) = (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix A` using `fun _ => rfl`. Establish `hsm : ∀ (c : D.nd.O i) (B : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)), (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix (c • B) = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c • (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix B`. Introduce `c B`.

Use extensionality with `a b`. Simplify using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`. Simplify using `only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero, Pi.mul_apply, Pi.sub_apply, Pi.zero_apply]`. Rewrite using `[← mul_assoc]`. Use `(congrArg (· * _) ?_).trans (zero_mul _)` and prove the remaining obligations.

Rewrite using `[← h0, Matrix.map_mul]`. Use `congr 1`. Rewrite using `[AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, hF, map_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[hE.smul_eval, SubmonoidClass.coe_pow, Pi.pow_apply, hE.r_eval, Polynomial.coeff_map, hsm, hF, ← map_pow]`.

Both sides reduce to the same expression. Rewrite using `[Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval, hE.chi_eval]`. Simplify using `only [OneMemClass.coe_one, Pi.one_apply]`. Rewrite using `[hF (((r (Dd.p x') g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) - chi1 D.nd i g • 1), map_sub, hsm, map_one]`. Both sides reduce to the same expression.

Introduce `m hm`. Establish `hterm : ∀ k, (φ (Pp.coeff k) • Dd.r (D.nd.gam0 i v.1) ^ k) • m = (((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) π * ((D.nd.chi i 1 (D.nd.gam0 i v.1) : (D.nd.O i)ˣ) : D.nd.O i) ^ k) • m`. Introduce `k`. Rewrite using `[smul_assoc, hE.blk_smul, ← map_pow, r_act hE hN c', chi_c_eq i h5x _ (Or.inl hS) c' _ (pow_mem hγ k), map_pow, Units.val_pow_eq_pow_val, smul_smul]`. Use `show (((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) (Dd.p Dd.π') * _) • m = _`.

Rewrite using `[hE.pπ]`. Rewrite `hm` using `[Finset.sum_smul, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_smul]`. Establish `hu : IsUnit (∑ k ∈ Finset.range (Pp.natDegree + 1), ((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) π * ((D.nd.chi i 1 (D.nd.gam0 i v.1) : (D.nd.O i)ˣ) : D.nd.O i) ^ k)`. Establish `h` using `hPu.map (evT D.nd i π)`. Rewrite `h` using `[Polynomial.eval_eq_sum_range, map_sum]`.

Simplify `h` using `[evT, chi1]`. Take `⟨u, hu'⟩` from `hu`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`. Use `_ = 0 := by rw [hu', hm, smul_zero]`.
-/
theorem locS_g (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (c' : Fin D.R.t) (v : VS i) (hv : ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)) (g : GE D.nd)
    (hg : g ∈ IS i v) :
    ∃ a : Dd.R', a * ((Dd.r g - algebraMap Dd.T' Dd.R' ((Dd.χ g : Dd.T'ˣ) : Dd.T')) * Dd.E) = 0 ∧
      ∀ m : Mc i Dd c'.succ, a • m = 0 → m = 0 := by
  have hS := v.2
  have hT : TameGen D.nd (D.nd.plOm.1 v.1) (D.nd.gam0 i v.1) := (D.nd.restN_tameGenerator_generates i v.1 (Or.inl hS)).2
  obtain ⟨Pp, hPu, hPx⟩ := (hG5 v.1 (Or.inl hS)).2 hv hS hT
  have hγ := D.nd.locNd_chebotarevPlace_mem i v.1
  let φ : D.nd.T i → Dd.T' := fun f => ⟨(f : D.nd.X i → D.nd.O i) ∘ Dd.p, hE.comp_mem _ f.2⟩
  refine ⟨∑ k ∈ Finset.range (Pp.natDegree + 1), φ (Pp.coeff k) • Dd.r (D.nd.gam0 i v.1) ^ k, ?_, ?_⟩
  · apply Subtype.ext
    funext x'
    have hdeg : (Pp.map ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) (Dd.p x')).comp
        (D.nd.T i).val.toRingHom)).natDegree < Pp.natDegree + 1 :=
      Nat.lt_succ_of_le (Polynomial.natDegree_map_le)
    have h0 := congrArg (fun X => X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) (hPx (Dd.p x') g hg)
    try dsimp only at h0
    rw [Matrix.map_zero _ (map_zero _), Polynomial.aeval_eq_sum_range' hdeg] at h0
    have hF : ∀ A : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i),
        A.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
          (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix A := fun _ => rfl
    have hsm : ∀ (c : D.nd.O i) (B : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)),
        (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix (c • B) =
          algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c •
            (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix B := by
      intro c B
      ext a b
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.zero_apply]
    rw [← mul_assoc]
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    rw [← h0, Matrix.map_mul]
    congr 1
    · rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, hF, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hE.smul_eval, SubmonoidClass.coe_pow, Pi.pow_apply, hE.r_eval, Polynomial.coeff_map, hsm, hF, ← map_pow]
      rfl
    · rw [Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval, hE.chi_eval]
      simp only [OneMemClass.coe_one, Pi.one_apply]
      rw [hF (((r (Dd.p x') g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) - chi1 D.nd i g • 1),
        map_sub, hsm, map_one]
      rfl
  · intro m hm
    have hterm : ∀ k, (φ (Pp.coeff k) • Dd.r (D.nd.gam0 i v.1) ^ k) • m =
        (((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) π *
          ((D.nd.chi i 1 (D.nd.gam0 i v.1) : (D.nd.O i)ˣ) : D.nd.O i) ^ k) • m := by
      intro k
      rw [smul_assoc, hE.blk_smul, ← map_pow, r_act hE hN c', chi_c_eq i h5x _ (Or.inl hS) c' _ (pow_mem hγ k),
        map_pow, Units.val_pow_eq_pow_val, smul_smul]
      show (((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) (Dd.p Dd.π') * _) • m = _
      rw [hE.pπ]
    rw [Finset.sum_smul, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_smul] at hm
    have hu : IsUnit (∑ k ∈ Finset.range (Pp.natDegree + 1), ((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) π *
        ((D.nd.chi i 1 (D.nd.gam0 i v.1) : (D.nd.O i)ˣ) : D.nd.O i) ^ k) := by
      have h := hPu.map (evT D.nd i π)
      rw [Polynomial.eval_eq_sum_range, map_sum] at h
      simpa [evT, chi1] using h
    obtain ⟨u, hu'⟩ := hu
    calc m = ((u⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ((u : D.nd.O i) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu', hm, smul_zero]

end LocSg

section Final
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

/- English proof (translation)
Introduce `v g hg`. Distinguish the cases in `hv : ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)`. Conclude with `locS_g i r ρ π Dd hE hN hG5 h5x c' v hv g hg`. Conclude with `locS_pde i r ρ π Dd hE hN hG5 h5x c' v hv g hg`.
-/
theorem locS (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (c' : Fin D.R.t) : LocS i Dd c'.succ := by
  intro v g hg
  by_cases hv : ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)
  · exact locS_g i r ρ π Dd hE hN hG5 h5x c' v hv g hg
  · exact locS_pde i r ρ π Dd hE hN hG5 h5x c' v hv g hg

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fall_succ (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c' : Fin D.R.t) :
    Fall i dc Dd F0 c'.succ = Fpos i dc Dd c'.succ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fall_zero (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) :
    Fall i dc Dd F0 0 = F0 := rfl

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, hG4, -, hG5, h5x, hG6, -, -, -, -, hdec, -⟩` from `hAdm`. Establish `hE` using `ev_of hD`. Establish `hloc : ∀ c : Fin (D.R.t + 1), c ≠ 0 → LocClause i dc Dd c`. Introduce `c hc`. Take `⟨c', rfl⟩` from `Fin.exists_succ_eq.2 hc`.

Conclude with `locClause i dc r ρ π Dd hE hN hG4 hdec hG5 h5x hQP c' (locS i r ρ π Dd hE hN hG5 h5x c')`. Use `⟨inertia_triviality_clause i r ρ π Dd hE hG4 hdec, hloc, hloc _ ?_, coverClause i dc Dd, no_fixed_vector_off_z i r π Dd hE hG6⟩` and prove the remaining obligations. Rewrite using `[c1_eq]`. Conclude with `Fin.succ_ne_zero _`.
-/
theorem qsAll (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hAdm : LargeLevelLemmas.admitted i r ρ π) (hQP : QPow i) :
    InertiaActsTrivially i Dd ∧ (∀ c : Fin (D.R.t + 1), c ≠ 0 → LocClause i dc Dd c) ∧ LocClause i dc Dd (c1 (D := D)) ∧
      CoverClause i dc Dd ∧ NoFixedVectorOffZ i Dd := by
  obtain ⟨-, -, -, -, -, -, -, hG4, -, hG5, h5x, hG6, -, -, -, -, hdec, -⟩ := hAdm
  have hE := ev_of hD
  have hloc : ∀ c : Fin (D.R.t + 1), c ≠ 0 → LocClause i dc Dd c := by
    intro c hc
    obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.2 hc
    exact locClause i dc r ρ π Dd hE hN hG4 hdec hG5 h5x hQP c' (locS i r ρ π Dd hE hN hG5 h5x c')
  refine ⟨inertia_triviality_clause i r ρ π Dd hE hG4 hdec, hloc, hloc _ ?_, coverClause i dc Dd, no_fixed_vector_off_z i r π Dd hE hG6⟩
  rw [c1_eq]
  exact Fin.succ_ne_zero _

end Final

section Shape
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

/- English proof (translation)
Introduce `h`. Take `⟨u, hu, he⟩` from `Finset.mem_image.1 h`. Establish `huv` using `idx_inj i dc (Finset.mem_union_right _ hu) hv he`. Conclude with `D.nd.SQ_l i u (Or.inr hu) (huv ▸ hl)`.
-/
theorem idx_not_qs {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc)
    (hl : v ∈ placesOver D.host.E (D.nd.l i)) : idx i dc v ∉ qsN i dc := by
  intro h
  obtain ⟨u, hu, he⟩ := Finset.mem_image.1 h
  have huv := idx_inj i dc (Finset.mem_union_right _ hu) hv he
  exact D.nd.SQ_l i u (Or.inr hu) (huv ▸ hl)

/- English proof (translation)
The claim follows from `Finset.mem_union_left _ (Finset.mem_union_left _ hv)`.
-/
theorem row_mem_pl {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ dc.row) : v ∈ plSet i dc :=
  Finset.mem_union_left _ (Finset.mem_union_left _ hv)

/- English proof (translation)
The claim follows from `Finset.mem_union_left _ (Finset.mem_union_right _ hv)`.
-/
theorem col_mem_pl {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ dc.col) : v ∈ plSet i dc :=
  Finset.mem_union_left _ (Finset.mem_union_right _ hv)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hq : w ∉ qsN i dc`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hw`. Conclude with `idx_not_qs i dc (row_mem_pl i dc hv) ((dc.cover v).1 (Or.inl hv))`. Unfold `Fpos`. Simplify using `only [if_neg hq, if_pos hw]`.
-/
theorem Fpos_row (c : Fin (D.R.t + 1)) {w : ℕ} (hw : w ∈ rowsN i dc) :
    Fpos i dc Dd c w = if (c : ℕ) = 1 then lcH1 (resU i dc Dd c w) ⊓
        unrH1 (resU i dc Dd c w) ((Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w))
      else ⊥ := by
  have hq : w ∉ qsN i dc := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact idx_not_qs i dc (row_mem_pl i dc hv) ((dc.cover v).1 (Or.inl hv))
  unfold Fpos
  simp only [if_neg hq, if_pos hw]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hpl` using `col_mem_pl i dc l.2`. Establish `hl` using `(dc.cover l.1).1 (Or.inr l.2)`. Establish `hr : colIdx i dc l ∉ rowsN i dc`. Introduce `h`. Take `⟨u, hu, he⟩` from `Finset.mem_image.1 h`.

Establish `huv` using `idx_inj i dc (row_mem_pl i dc hu) hpl he`. Conclude with `Finset.disjoint_left.1 dc.disj hu (huv ▸ l.2)`. Establish `hq : colIdx i dc l ∉ qsN i dc` using `idx_not_qs i dc hpl hl`. Unfold `Fpos`. Simplify using `only [if_neg hq, if_neg hr]`.
-/
theorem Fpos_col (c : Fin (D.R.t + 1)) (l : Col i dc) :
    Fpos i dc Dd c (colIdx i dc l) =
      if (c : ℕ) = 1 then unrH1 (resU i dc Dd c (colIdx i dc l)) (I i dc (colIdx i dc l)) else ⊥ := by
  have hpl := col_mem_pl i dc l.2
  have hl := (dc.cover l.1).1 (Or.inr l.2)
  have hr : colIdx i dc l ∉ rowsN i dc := by
    intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.1 h
    have huv := idx_inj i dc (row_mem_pl i dc hu) hpl he
    exact Finset.disjoint_left.1 dc.disj hu (huv ▸ l.2)
  have hq : colIdx i dc l ∉ qsN i dc := idx_not_qs i dc hpl hl
  unfold Fpos
  simp only [if_neg hq, if_neg hr]

/- English proof (translation)
Unfold `Fpos`. Rewrite using `[if_pos hw]`.
-/
theorem Fpos_qs (c : Fin (D.R.t + 1)) {w : ℕ} (hw : w ∈ qsN i dc) :
    Fpos i dc Dd c w = unrH1 (resU i dc Dd c w) (I i dc w) := by
  unfold Fpos
  rw [if_pos hw]

end Shape

end Formalism.MainNotions.N.K.QS

end
