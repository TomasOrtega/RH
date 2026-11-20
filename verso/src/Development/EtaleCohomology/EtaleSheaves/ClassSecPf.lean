import Development.EtaleCohomology.EtaleSheaves.LocSecPfB

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ClassSecPf

section
variable {R : Type} [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ)

abbrev S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
  (LateralTheory.E.LeafLocPf.secCx F X).sc' (n - 1) n (n + 1)

def fz (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) : (free R).obj (yoneda.obj X) ⟶ (res R F).X n :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((free R).obj (yoneda.obj X))).inv ≫ (z : Cochain _ _ n).v 0 n (zero_add n)

/- English proof (translation)
Simplify using `[fz]`.
-/
theorem fz_add (z w : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    fz X F n (z + w) = fz X F n z + fz X F n w := by
  simp [fz]

/- English proof (translation)
Unfold `fz`. Rewrite using `[Cocycle.fromSingleMk_coe]`. Use `erw [Cochain.fromSingleMk_v f (zero_add n)]`. Simplify using the standard rewrite rules.
-/
theorem fz_mk (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X n) (hf : f ≫ (res R F).d n (n + 1) = 0) :
    fz X F n (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf) = f := by
  unfold fz
  rw [Cocycle.fromSingleMk_coe]
  erw [Cochain.fromSingleMk_v f (zero_add n)]
  simp

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl`. Rewrite using `[fz_mk]`. Conclude with `⟨hf, rfl⟩`.
-/
theorem exists_mk (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    ∃ (hf : fz X F n z ≫ (res R F).d n (n + 1) = 0),
      Cocycle.fromSingleMk (fz X F n z) (zero_add n) (n + 1) rfl hf = z := by
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
  rw [fz_mk]
  exact ⟨hf, rfl⟩

variable (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X)
  (he : ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f))

def ee (k : ℤ) : ((free R).obj (yoneda.obj X) ⟶ (res R F).X k) ≃+ (LateralTheory.E.LeafLocPf.secCx F X).X k :=
  e ((res R F).X k)

include he in
/- English proof (translation)
The claim follows from `he _ f`.
-/
theorem ee_comp (i j : ℤ) (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X i) :
    ee X F e j (f ≫ (res R F).d i j) = ((LateralTheory.E.LeafLocPf.secCx F X).d i j).hom (ee X F e i f) :=
  he _ f

include he in
/- English proof (translation)
Rewrite using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `((LateralTheory.E.LeafLocPf.secCx F X).d n (n + 1)).hom (ee X F e n f) = 0`. Rewrite using `[← ee_comp X F e he, hf, map_zero]`.
-/
theorem mem_ker (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X n) (hf : f ≫ (res R F).d n (n + 1) = 0) :
    (show (S X F n).X₂ from ee X F e n f) ∈ LinearMap.ker (S X F n).g.hom := by
  rw [LinearMap.mem_ker]
  change ((LateralTheory.E.LeafLocPf.secCx F X).d n (n + 1)).hom (ee X F e n f) = 0
  rw [← ee_comp X F e he, hf, map_zero]

def cyc (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) : LinearMap.ker (S X F n).g.hom :=
  ⟨ee X F e n (fz X F n z), mem_ker X F n e he _ (exists_mk X F n z).1⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ee X F e n (fz X F n (z + w)) = ee X F e n (fz X F n z) + ee X F e n (fz X F n w)`. Rewrite using `[fz_add, map_add]`.
-/
theorem cyc_add (z w : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    cyc X F n e he (z + w) = cyc X F n e he z + cyc X F n e he w := by
  apply Subtype.ext
  change ee X F e n (fz X F n (z + w)) = ee X F e n (fz X F n z) + ee X F e n (fz X F n w)
  rw [fz_add, map_add]

def phi : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n →+ (S X F n).moduleCatLeftHomologyData.H where
  toFun z := (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z)
  map_zero' := by
    have : cyc X F n e he 0 = 0 := by
      have h := cyc_add X F n e he 0 0
      rw [add_zero] at h
      exact (add_eq_left.mp h.symm)
    rw [this, map_zero]
    rfl
  map_add' z w := by
    rw [cyc_add, map_add]
    rfl

/- English proof (translation)
Take `⟨hf, hz⟩` from `exists_mk X F n z`. Establish `key : z ∈ coboundaries (LateralTheory.E.LocSecPf.pt R X) (res R F) n ↔ ∃ g : (free R).obj (yoneda.obj X) ⟶ (res R F).X (n - 1), g ≫ (res R F).d (n - 1) n = fz X F n z` using `by conv_lhs => rw [← hz]`. Conclude with `Cocycle.fromSingleMk_mem_coboundaries_iff (K := res R F) (fz X F n z) (zero_add n) (n + 1) rfl hf (n - 1) (by omega)`. Rewrite using `[key]`. Express the relevant statement in the definitionally equal form `(LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z) = 0 ↔ _`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs⟩`. Use `⟨(ee X F e (n - 1)).symm s, (ee X F e n).injective ?_⟩` and prove the remaining obligations. Rewrite using `[ee_comp X F e he]`.

Use `erw [AddEquiv.apply_symm_apply]`. Conclude with `congrArg Subtype.val hs`. Introduce and unpack `⟨g, hg⟩`. Use `⟨ee X F e (n - 1) g, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((LateralTheory.E.LeafLocPf.secCx F X).d (n - 1) n).hom (ee X F e (n - 1) g) = ee X F e n (fz X F n z)`.

Rewrite using `[← ee_comp X F e he, hg]`.
-/
theorem phi_eq_zero_iff (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    phi X F n e he z = 0 ↔ z ∈ coboundaries _ _ _ := by
  obtain ⟨hf, hz⟩ := exists_mk X F n z
  have key : z ∈ coboundaries (LateralTheory.E.LocSecPf.pt R X) (res R F) n ↔
      ∃ g : (free R).obj (yoneda.obj X) ⟶ (res R F).X (n - 1), g ≫ (res R F).d (n - 1) n = fz X F n z := by
    conv_lhs => rw [← hz]
    exact Cocycle.fromSingleMk_mem_coboundaries_iff (K := res R F) (fz X F n z) (zero_add n) (n + 1) rfl hf
      (n - 1) (by omega)
  rw [key]
  change (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(ee X F e (n - 1)).symm s, (ee X F e n).injective ?_⟩
    rw [ee_comp X F e he]; erw [AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val hs
  · rintro ⟨g, hg⟩
    refine ⟨ee X F e (n - 1) g, Subtype.ext ?_⟩
    change ((LateralTheory.E.LeafLocPf.secCx F X).d (n - 1) n).hom (ee X F e (n - 1) g) = ee X F e n (fz X F n z)
    rw [← ee_comp X F e he, hg]

def psi : CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n →+ (S X F n).moduleCatLeftHomologyData.H :=
  CohomologyClass.descAddMonoidHom (phi X F n e he) (fun z hz => (phi_eq_zero_iff X F n e he z).2 hz)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨z, rfl⟩` from `CohomologyClass.mk_surjective c`. Rewrite using `[CohomologyClass.mk_eq_zero_iff, ← phi_eq_zero_iff X F n e he]`.

Conclude with `hc`. Introduce `c`. Take `⟨⟨s, hs⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Establish `hf : (ee X F e n).symm s ≫ (res R F).d n (n + 1) = 0`. Apply `(ee X F e (n + 1)).injective` to reduce the goal to its premises.

Rewrite using `[ee_comp X F e he, map_zero]`. Use `erw [AddEquiv.apply_symm_apply]`. Conclude with `hs`. Use `⟨CohomologyClass.mk (Cocycle.fromSingleMk _ (zero_add n) (n + 1) rfl hf), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he _) = Submodule.Quotient.mk _`.

Rewrite using `[Submodule.mkQ_apply]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ee X F e n (fz X F n _) = s`. Rewrite using `[fz_mk]`.

Conclude with `(ee X F e n).apply_symm_apply s`.
-/
theorem psi_bijective : Function.Bijective (psi X F n e he) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    rw [CohomologyClass.mk_eq_zero_iff, ← phi_eq_zero_iff X F n e he]
    exact hc
  · intro c
    obtain ⟨⟨s, hs⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hf : (ee X F e n).symm s ≫ (res R F).d n (n + 1) = 0 := by
      apply (ee X F e (n + 1)).injective
      rw [ee_comp X F e he, map_zero]; erw [AddEquiv.apply_symm_apply]
      exact hs
    refine ⟨CohomologyClass.mk (Cocycle.fromSingleMk _ (zero_add n) (n + 1) rfl hf), ?_⟩
    change (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he _) = Submodule.Quotient.mk _
    rw [Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    change ee X F e n (fz X F n _) = s
    rw [fz_mk]
    exact (ee X F e n).apply_symm_apply s

end

/- English proof (translation)
Introduce `R _ X e he F n`. Use `⟨(AddEquiv.ofBijective _ (psi_bijective X F n e he)).trans ?_⟩` and prove the remaining obligations. Conclude with `((LateralTheory.E.LeafLocPf.secCx F X).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫ (S X F n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.symm`.
-/
theorem classSec : LateralTheory.E.LocSecPfB.ClassSec := by
  intro R _ X e he F n
  refine ⟨(AddEquiv.ofBijective _ (psi_bijective X F n e he)).trans ?_⟩
  exact ((LateralTheory.E.LeafLocPf.secCx F X).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    (S X F n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.symm

/- English proof (translation)
The claim follows from `classSec`.
-/
theorem ClassSec_of : LateralTheory.E.LocSecPfB.ClassSec := classSec

end LateralTheory.E.ClassSecPf
