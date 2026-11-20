import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCoverStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

variable {Z : Scheme.{0}}

/- English proof (translation)
The claim follows from `(congrArg (fun q => q.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm`.
-/
theorem sf_resG_resG {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun q => q.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

/- English proof (translation)
The claim follows from `congrArg (fun q => q.hom x) (Z.presheaf.map_id (Opposite.op U))`.
-/
theorem sf_resG_id {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : resG Z h x = x :=
  congrArg (fun q => q.hom x) (Z.presheaf.map_id (Opposite.op U))

/- English proof (translation)
Use `congrArg (resG Z h') e` as an intermediate fact. Rewrite `this` using `[sf_resG_resG, sf_resG_resG, sf_resG_id, sf_resG_id]`. Then use the resulting hypothesis.
-/
theorem sf_resG_inj {U V : Z.Opens} (h : V ≤ U) (h' : U ≤ V) {x y : Γ(Z, U)}
    (e : resG Z h x = resG Z h y) : x = y := by
  have := congrArg (resG Z h') e
  rwa [sf_resG_resG, sf_resG_resG, sf_resG_id, sf_resG_id] at this

variable {J : Type} (W : J → Z.Opens) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))

def sfCr (U : Z.Opens) (i i' : J) (h : U ≤ W i ⊓ W i') : Γ(Z, U) := resG Z h (c i i')

/- English proof (translation)
The claim follows from `sf_resG_resG _ _ _`.
-/
theorem sfCr_res {U V : Z.Opens} (i i' : J) (h : U ≤ W i ⊓ W i') (h' : V ≤ U) :
    resG Z h' (sfCr W c U i i' h) = sfCr W c V i i' (h'.trans h) :=
  sf_resG_resG _ _ _

/- English proof (translation)
Establish `e` using `congrArg (resG Z h) (hc i i' i'')`. Rewrite `e` using `[map_add, sf_resG_resG, sf_resG_resG, sf_resG_resG]`. Conclude with `e`.
-/
theorem sfCr_add (hc : IsCoc W c) (U : Z.Opens) (i i' i'' : J) (h : U ≤ W i ⊓ W i' ⊓ W i'') :
    sfCr W c U i i' (h.trans inf_le_left) +
      sfCr W c U i' i'' (h.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) =
      sfCr W c U i i'' (h.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := by
  have e := congrArg (resG Z h) (hc i i' i'')
  rw [map_add, sf_resG_resG, sf_resG_resG, sf_resG_resG] at e
  exact e

/- English proof (translation)
Establish `e` using `sfCr_add W c hc U i i i (le_inf h (h.trans inf_le_left))`. Establish `e2 : sfCr W c U i i h + sfCr W c U i i h = sfCr W c U i i h` using `e`. Take the linear combination `e2`.
-/
theorem sfCr_self (hc : IsCoc W c) (U : Z.Opens) (i : J) (h : U ≤ W i ⊓ W i) :
    sfCr W c U i i h = 0 := by
  have e := sfCr_add W c hc U i i i (le_inf h (h.trans inf_le_left))
  have e2 : sfCr W c U i i h + sfCr W c U i i h = sfCr W c U i i h := e
  linear_combination e2

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem sfCr_congr (U : Z.Opens) {i j i' : J} (e : i = j) (h : U ≤ W i ⊓ W i') (h' : U ≤ W j ⊓ W i') :
    sfCr W c U i i' h = sfCr W c U j i' h' := by subst e; rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem sfCr_congr2 (U : Z.Opens) {i i' j' : J} (e : i' = j') (h : U ≤ W i ⊓ W i') (h' : U ≤ W i ⊓ W j') :
    sfCr W c U i i' h = sfCr W c U i j' h' := by subst e; rfl

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem cechAffineCochainValue_congr_source (f : C1 (OAff s)) {A A' B : Z.affineOpens} (e : A = A') (h : B.1 ≤ A.1) (h' : B.1 ≤ A'.1) :
    fv s f h = fv s f h' := by subst e; rfl

end GlobalTheory.CechFin

open GlobalTheory.CechPoset in

/- English proof (translation)
Introduce `R _ Z s J W hW hW2 hI S hS c hc`. Set `κ` to `{j // j ∈ S}`. Use `letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective`. Set `D : κ → Z.Opens` to `fun k => W k.1`. Establish `hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ k ∈ I, D k)` using `by classical`.

Introduce `I hIn`. Use `hI (I.image Subtype.val) (hIn.image _)` as an intermediate fact. Rewrite `this` using `[Finset.iInf_finset_image]`. Then use the resulting hypothesis. Establish `hcov : ⨆ k, D k = ⊤`. Rewrite using `[← hS, iSup_subtype']`.

Establish `hinf : ∀ a b : NE κ, (cov D hD (a ⊓ b)).1 = (cov D hD a).1 ⊓ (cov D hD b).1` using `fun a b => Finset.iInf_union`. Establish `hsup : ⨆ a, (cov D hD a).1 = ⊤`. Use `eq_top_iff.2 (hcov.symm.le.trans (iSup_le fun k => ?_))` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (le_iSup (fun a => (cov D hD a).1) (OrderDual.toDual ⟨{k}, Finset.singleton_nonempty k⟩))` and prove the remaining obligations. Simplify using `[cov]`.

Establish `hmem : ∀ (a : (NE κ)ᵒᵖ) (k : κ), k ∈ sub a → (cov D hD a.unop).1 ≤ W k.1` using `fun a k hk => biInf_le (fun k => D k) hk`. Set `Fv : C1 (covF s D hD)` to `fun a b φ => sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 (le_inf (hmem b _ (mn_mem b)) (hmem b _ (sub_subset φ (mn_mem a))))`. Establish `hF : Fv ∈ Z1 (covF s D hD)`. Introduce `a b d φ ψ`. Establish `e` using `sfCr_add W c hc (cov D hD d.unop).1 (mn d).1 (mn b).1 (mn a).1 (le_inf (le_inf (hmem d _ (mn_mem d)) (hmem d _ (sub_subset ψ (mn_mem b)))) (hmem d _ (sub_subset ψ (sub_subset φ (mn_mem a)))))`.

Use `show sfCr W c (cov D hD d.unop).1 (mn d).1 (mn a).1 _ = resG Z (cov_mono D hD (leOfHom ψ.unop)) (sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 _) + sfCr W c (cov D hD d.unop).1 (mn d).1 (mn b).1 _`. Rewrite using `[sfCr_res]`. Rewrite using `[add_comm]`. Conclude with `e.symm`. Take `⟨y, hy⟩` from `(GlobalTheory.T.cech_pull_one_bijective_lattice_cover R Z s (NE κ) (cov D hD) (cov_mono D hD) hinf hsup).2 (H1.mk _ ⟨Fv, hF⟩)`.

Take `⟨f0, rfl⟩` from `H1.mk_surjective _ y`. Rewrite `hy` using `[CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]`. Take `⟨g, hg⟩` from `hy`. Set `hfun : ∀ i, Γ(Z, W i)` to `fun i => @dite _ (i ∈ S) (Classical.propDecidable _) (fun hi => -resG Z (le_of_eq (Finset.iInf_singleton (⟨i, hi⟩ : κ) D).symm : W i ≤ (cov D hD (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)).unop).1) (g (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)))) (fun _ => 0)`. Use `⟨-f0, hfun, fun i hi i' hi' => ?_⟩` and prove the remaining obligations.

Set `k : κ` to `⟨i, hi⟩`. Set `k' : κ` to `⟨i', hi'⟩`. Set `a` to `ne {k} (Finset.singleton_nonempty k)`. Set `a'` to `ne {k'} (Finset.singleton_nonempty k')`. Set `b` to `ne {k, k'} (Finset.insert_nonempty k {k'})`.

Establish `ca : (cov D hD a.unop).1 = W i` using `Finset.iInf_singleton k D`. Establish `ca' : (cov D hD a'.unop).1 = W i'` using `Finset.iInf_singleton k' D`. Establish `cb : (cov D hD b.unop).1 = W i ⊓ W i'` using `by show (⨅ j ∈ ({k, k'} : Finset κ), D j) = _`. Rewrite using `[Finset.iInf_insert, Finset.iInf_singleton]`. Set `φ : a ⟶ b` to `homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k {k'}))`.

Set `φ' : a' ⟶ b` to `homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k')))`. Establish `hab : (cov D hD b.unop).1 ≤ (cov D hD a.unop).1` using `cov_mono D hD (leOfHom φ.unop)`. Establish `ha'b : (cov D hD b.unop).1 ≤ (cov D hD a'.unop).1` using `cov_mono D hD (leOfHom φ'.unop)`. Establish `hBP : (cov D hD b.unop).1 ≤ W i ⊓ W i'` using `cb.le`. Establish `hPB : W i ⊓ W i' ≤ (cov D hD b.unop).1` using `cb.ge`.

Establish `mna : mn a = k` using `Finset.min'_singleton k`. Establish `mna' : mn a' = k'` using `Finset.min'_singleton k'`. Establish `hxB : (cov D hD b.unop).1 ≤ W (mn b).1` using `hmem b _ (mn_mem b)`. Establish `h4` using `congrFun (congrFun (congrFun hg a) b) φ`. Establish `h5` using `congrFun (congrFun (congrFun hg a') b) φ'`.

Establish `h4' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z hab (g a) = fv s f0.1 (A` using `cov D hD a.unop) (B := cov D hD b.unop) hab - sfCr W c (cov D hD b.unop).1 (mn b).1 i (le_inf hxB (hBP.trans inf_le_left)) := by`. Rewrite using `[← sfCr_congr2 W c _ (congrArg Subtype.val mna) (le_inf hxB (hab.trans (hmem a _ (mn_mem a))))]`. Conclude with `h4`. Establish `h5' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z ha'b (g a') = fv s f0.1 (A` using `cov D hD a'.unop) (B := cov D hD b.unop) ha'b - sfCr W c (cov D hD b.unop).1 (mn b).1 i' (le_inf hxB (hBP.trans inf_le_right)) := by`. Rewrite using `[← sfCr_congr2 W c _ (congrArg Subtype.val mna') (le_inf hxB (ha'b.trans (hmem a' _ (mn_mem a'))))]`.

Conclude with `h5`. Establish `c1` using `sfCr_add W c hc (cov D hD b.unop).1 i (mn b).1 i' (le_inf (le_inf (hBP.trans inf_le_left) hxB) (hBP.trans inf_le_right))`. Establish `c2` using `sfCr_add W c hc (cov D hD b.unop).1 (mn b).1 i (mn b).1 (le_inf (le_inf hxB (hBP.trans inf_le_left)) hxB)`. Rewrite `c2` using `[sfCr_self W c hc]`. Establish `r1` using `res_val s f0 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop) inf_le_left hBP`.

Establish `r2` using `res_val s f0 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop) inf_le_right hBP`. Rewrite `r1` using `[cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca.symm) _ hab]`. Rewrite `r2` using `[cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca'.symm) _ ha'b]`. Establish `erho : resG Z hBP (rho W s hW hW2 (-f0).1 i i') = -resG Z hBP (fv s f0.1 (A` using `⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left) + resG Z hBP (fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) := by show resG Z hBP (-fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left - -fv s f0.1 (A := ⟨W i', hW i'⟩) (B := …`. Rewrite using `[map_sub, map_neg, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e0 : resG Z hBP (c i i') = sfCr W c (cov D hD b.unop).1 i i' hBP` using `rfl`. Establish `t1 : resG Z hBP (resG Z inf_le_left (hfun i)) = -resG Z hab (g a)`. Simplify using `only [hfun, @dif_pos _ (Classical.propDecidable _) hi]`. Rewrite using `[map_neg, map_neg]`.

Conclude with `congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))`. Establish `t2 : resG Z hBP (resG Z inf_le_right (hfun i')) = -resG Z ha'b (g a')`. Simplify using `only [hfun, @dif_pos _ (Classical.propDecidable _) hi']`. Rewrite using `[map_neg, map_neg]`. Conclude with `congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))`.

Rewrite `erho` using `[r1, r2]`. Apply `sf_resG_inj hBP hPB` to reduce the goal to its premises. Rewrite using `[map_add, map_sub, t1, t2]`. Take the linear combination `e0 - erho - h4' + h5' - c1 + c2`.
-/
theorem GlobalTheory.CechFin.cocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  intro R _ Z s J W hW hW2 hI S hS c hc
  let κ := {j // j ∈ S}
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  let D : κ → Z.Opens := fun k => W k.1
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ k ∈ I, D k) := by
    classical
    intro I hIn
    have := hI (I.image Subtype.val) (hIn.image _)
    rwa [Finset.iInf_finset_image] at this
  have hcov : ⨆ k, D k = ⊤ := by
    rw [← hS, iSup_subtype']
  have hinf : ∀ a b : NE κ, (cov D hD (a ⊓ b)).1 = (cov D hD a).1 ⊓ (cov D hD b).1 :=
    fun a b => Finset.iInf_union
  have hsup : ⨆ a, (cov D hD a).1 = ⊤ := by
    refine eq_top_iff.2 (hcov.symm.le.trans (iSup_le fun k => ?_))
    refine le_trans (le_of_eq ?_) (le_iSup (fun a => (cov D hD a).1)
      (OrderDual.toDual ⟨{k}, Finset.singleton_nonempty k⟩))
    simp [cov]
  have hmem : ∀ (a : (NE κ)ᵒᵖ) (k : κ), k ∈ sub a → (cov D hD a.unop).1 ≤ W k.1 :=
    fun a k hk => biInf_le (fun k => D k) hk
  let Fv : C1 (covF s D hD) := fun a b φ =>
    sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1
      (le_inf (hmem b _ (mn_mem b)) (hmem b _ (sub_subset φ (mn_mem a))))
  have hF : Fv ∈ Z1 (covF s D hD) := by
    intro a b d φ ψ
    have e := sfCr_add W c hc (cov D hD d.unop).1 (mn d).1 (mn b).1 (mn a).1
      (le_inf (le_inf (hmem d _ (mn_mem d)) (hmem d _ (sub_subset ψ (mn_mem b))))
        (hmem d _ (sub_subset ψ (sub_subset φ (mn_mem a)))))
    show sfCr W c (cov D hD d.unop).1 (mn d).1 (mn a).1 _ =
      resG Z (cov_mono D hD (leOfHom ψ.unop)) (sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 _) +
        sfCr W c (cov D hD d.unop).1 (mn d).1 (mn b).1 _
    rw [sfCr_res]
    rw [add_comm]
    exact e.symm
  obtain ⟨y, hy⟩ := (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R Z s (NE κ) (cov D hD) (cov_mono D hD) hinf hsup).2
    (H1.mk _ ⟨Fv, hF⟩)
  obtain ⟨f0, rfl⟩ := H1.mk_surjective _ y
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hy
  obtain ⟨g, hg⟩ := hy

  let hfun : ∀ i, Γ(Z, W i) := fun i => @dite _ (i ∈ S) (Classical.propDecidable _) (fun hi =>
      -resG Z (le_of_eq (Finset.iInf_singleton (⟨i, hi⟩ : κ) D).symm :
        W i ≤ (cov D hD (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)).unop).1)
        (g (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)))) (fun _ => 0)
  refine ⟨-f0, hfun, fun i hi i' hi' => ?_⟩
  let k : κ := ⟨i, hi⟩
  let k' : κ := ⟨i', hi'⟩
  let a := ne {k} (Finset.singleton_nonempty k)
  let a' := ne {k'} (Finset.singleton_nonempty k')
  let b := ne {k, k'} (Finset.insert_nonempty k {k'})
  have ca : (cov D hD a.unop).1 = W i := Finset.iInf_singleton k D
  have ca' : (cov D hD a'.unop).1 = W i' := Finset.iInf_singleton k' D
  have cb : (cov D hD b.unop).1 = W i ⊓ W i' := by
    show (⨅ j ∈ ({k, k'} : Finset κ), D j) = _
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  let φ : a ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k {k'}))
  let φ' : a' ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k')))
  have hab : (cov D hD b.unop).1 ≤ (cov D hD a.unop).1 := cov_mono D hD (leOfHom φ.unop)
  have ha'b : (cov D hD b.unop).1 ≤ (cov D hD a'.unop).1 := cov_mono D hD (leOfHom φ'.unop)
  have hBP : (cov D hD b.unop).1 ≤ W i ⊓ W i' := cb.le
  have hPB : W i ⊓ W i' ≤ (cov D hD b.unop).1 := cb.ge
  have mna : mn a = k := Finset.min'_singleton k
  have mna' : mn a' = k' := Finset.min'_singleton k'
  have hxB : (cov D hD b.unop).1 ≤ W (mn b).1 := hmem b _ (mn_mem b)
  have h4 := congrFun (congrFun (congrFun hg a) b) φ
  have h5 := congrFun (congrFun (congrFun hg a') b) φ'
  have h4' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z hab (g a) = fv s f0.1 (A := cov D hD a.unop) (B := cov D hD b.unop) hab -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i (le_inf hxB (hBP.trans inf_le_left)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna) (le_inf hxB (hab.trans (hmem a _ (mn_mem a))))]
    exact h4
  have h5' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z ha'b (g a') = fv s f0.1 (A := cov D hD a'.unop) (B := cov D hD b.unop) ha'b -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i' (le_inf hxB (hBP.trans inf_le_right)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna') (le_inf hxB (ha'b.trans (hmem a' _ (mn_mem a'))))]
    exact h5
  have c1 := sfCr_add W c hc (cov D hD b.unop).1 i (mn b).1 i'
    (le_inf (le_inf (hBP.trans inf_le_left) hxB) (hBP.trans inf_le_right))
  have c2 := sfCr_add W c hc (cov D hD b.unop).1 (mn b).1 i (mn b).1
    (le_inf (le_inf hxB (hBP.trans inf_le_left)) hxB)
  rw [sfCr_self W c hc] at c2
  have r1 := res_val s f0 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_left hBP
  have r2 := res_val s f0 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_right hBP
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca.symm) _ hab] at r1
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca'.symm) _ ha'b] at r2
  have erho : resG Z hBP (rho W s hW hW2 (-f0).1 i i') =
      -resG Z hBP (fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left) +
        resG Z hBP (fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) := by
    show resG Z hBP (-fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
      -fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) = _
    rw [map_sub, map_neg, map_neg]; ring
  have e0 : resG Z hBP (c i i') = sfCr W c (cov D hD b.unop).1 i i' hBP := rfl
  have t1 : resG Z hBP (resG Z inf_le_left (hfun i)) = -resG Z hab (g a) := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi]
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  have t2 : resG Z hBP (resG Z inf_le_right (hfun i')) = -resG Z ha'b (g a') := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi']
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  rw [r1, r2] at erho
  apply sf_resG_inj hBP hPB
  rw [map_add, map_sub, t1, t2]
  linear_combination e0 - erho - h4' + h5' - c1 + c2
