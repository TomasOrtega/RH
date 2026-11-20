import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BocksteinLemmas

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison.CyclicComplexMaps

open GlobalTheory.EtC

/- English proof (translation)
Establish `hq : q ≠ 0`. Introduce and unpack `rfl`. Conclude with `hQ (Nat.eq_zero_of_zero_dvd h)`. Establish `hμ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Q)) Q` using `Complex.isPrimitiveRoot_exp Q hQ`. Establish `hm0 : Q / q ≠ 0` using `(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) h) (Nat.pos_of_ne_zero hq)).ne'`.

Establish `hξ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Q) ^ (Q / q)) q`. Use `hμ.pow_of_dvd hm0 (Nat.div_dvd_of_dvd h)` as an intermediate fact. Rewrite `this` using `[Nat.div_div_self h hQ]`. Then use the resulting hypothesis. Rewrite using `[Polynomial.cyclotomic_eq_minpoly hμ (Nat.pos_of_ne_zero hQ)]`. Apply `minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (Nat.pos_of_ne_zero hQ))` to reduce the goal to its premises.

Rewrite using `[Polynomial.aeval_comp, map_pow, Polynomial.aeval_X, Polynomial.cyclotomic_eq_minpoly hξ (Nat.pos_of_ne_zero hq), minpoly.aeval]`.
-/
theorem cyc_dvd (Q q : ℕ) (hQ : Q ≠ 0) (h : q ∣ Q) :
    Polynomial.cyclotomic Q ℤ ∣ (Polynomial.cyclotomic q ℤ).comp (Polynomial.X ^ (Q / q)) := by
  have hq : q ≠ 0 := by
    rintro rfl
    exact hQ (Nat.eq_zero_of_zero_dvd h)
  have hμ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Q)) Q := Complex.isPrimitiveRoot_exp Q hQ
  have hm0 : Q / q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) h) (Nat.pos_of_ne_zero hq)).ne'
  have hξ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Q) ^ (Q / q)) q := by
    have := hμ.pow_of_dvd hm0 (Nat.div_dvd_of_dvd h)
    rwa [Nat.div_div_self h hQ] at this
  rw [Polynomial.cyclotomic_eq_minpoly hμ (Nat.pos_of_ne_zero hQ)]
  apply minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (Nat.pos_of_ne_zero hQ))
  rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X,
    Polynomial.cyclotomic_eq_minpoly hξ (Nat.pos_of_ne_zero hq), minpoly.aeval]

/- English proof (translation)
Establish `hQ : Q ≠ 0` using `NeZero.ne Q`. Use `⟨Subtype.mk (ζ.1 ^ (Q / q)) ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hmul : (q : A) * ((Q / q : ℕ) : A) = (Q : A)`. Rewrite using `[← Nat.cast_mul, Nat.mul_div_cancel' h]`. Conclude with `isUnit_of_mul_isUnit_left (by rw [hmul]; exact ζ.2.1)`.

Take `⟨r, hr⟩` from `cyc_dvd Q q hQ h`. Establish `h0 : Polynomial.aeval ζ.1 ((Polynomial.cyclotomic q ℤ).comp (Polynomial.X ^ (Q / q))) = 0`. Rewrite using `[hr, map_mul, ζ.2.2, zero_mul]`. Rewrite `h0` using `[Polynomial.aeval_comp, map_pow, Polynomial.aeval_X]`. Then use the resulting hypothesis.
-/
theorem prim_pow {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) :
    ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ (Q / q) := by
  have hQ : Q ≠ 0 := NeZero.ne Q
  refine ⟨Subtype.mk (ζ.1 ^ (Q / q)) ⟨?_, ?_⟩, rfl⟩
  · have hmul : (q : A) * ((Q / q : ℕ) : A) = (Q : A) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' h]
    exact isUnit_of_mul_isUnit_left (by rw [hmul]; exact ζ.2.1)
  · obtain ⟨r, hr⟩ := cyc_dvd Q q hQ h
    have h0 : Polynomial.aeval ζ.1 ((Polynomial.cyclotomic q ℤ).comp (Polynomial.X ^ (Q / q))) = 0 := by
      rw [hr, map_mul, ζ.2.2, zero_mul]
    rwa [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X] at h0

/- English proof (translation)
Apply `Sheaf.hom_ext` to reduce the goal to its premises. Use `sheafify_hom_ext _ _ _ G.property ?_` and prove the remaining obligations. Apply `NatTrans.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises.

Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Apply `Finsupp.lhom_ext'` to reduce the goal to its premises. Introduce `ζ`. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Conclude with `h U.unop ζ`.
-/
theorem tw_ext {Q : ℕ} {i : ℤ} {G : Shv (ZMod Q)} (f g : tw Q i ⟶ G)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map f (twGen i ζ) = Sec.map g (twGen i ζ)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext _ _ _ G.property ?_
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext'
  intro ζ
  apply LinearMap.ext_ring
  exact h U.unop ζ

variable {Q : ℕ} [NeZero Q]

/- English proof (translation)
Establish `hc : c = ((c.down.val : ℕ) : ULift.{1} (ZMod Q))` using `ULift.ext _ _ (ZMod.natCast_zmod_val c.down).symm`. Rewrite using `[hc]`. Simplify using `only [Nat.cast_smul_eq_nsmul, map_nsmul]`.
-/
theorem zmod_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} (ZMod Q)) M]
    [Module (ULift.{1} (ZMod Q)) N] (f : M →+ N) (c : ULift.{1} (ZMod Q)) (x : M) : f (c • x) = c • f x := by
  have hc : c = ((c.down.val : ℕ) : ULift.{1} (ZMod Q)) :=
    ULift.ext _ _ (ZMod.natCast_zmod_val c.down).symm
  rw [hc]
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

def shHom {F G : Shv (ZMod Q)} (a : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (ha : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U), Sec.res g (a U x) = a V (Sec.res g x)) : F ⟶ G :=
  ⟨{ app := fun U => ModuleCat.ofHom { toFun := a U.unop, map_add' := map_add _, map_smul' := zmod_smul (a U.unop) }
     naturality := fun U V g => by
       ext x
       exact (ha g.unop x).symm }⟩

def cxHom {I J : Cx (ZMod Q)} (σ : SemiMap I J) : I ⟶ J where
  f s := shHom (fun U => σ.app U s) (fun g x => σ.nat g s x)
  comm' s t _ := by
    apply Sheaf.hom_ext
    ext U x
    exact σ.comm U.unop s t x

/- English proof (translation)
Use `delta ev Sec.map`. Simplify using `[Cochain.comp_zero_cochain_v, Cochain.ofHom_v]`.
-/
theorem ev_comp {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (g : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom g) (add_zero n)) p s h U x = Sec.map (g.f s) (ev α p s h U x) := by
  delta ev Sec.map
  simp [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

/- English proof (translation)
Use `delta resι InjectiveResolution.ι' HomologicalComplex.extendSingleIso ComplexShape.Embedding.extendFunctor`. Simplify using `[HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)]`.
-/
private theorem resι_eq_singleObjXSelf_inv_comp {R : Type} [CommRing R] (X : Shv R) :
    resι R X = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).inv ≫
      (injectiveResolution X).ι.f 0 ≫
        (HomologicalComplex.extendXIso (injectiveResolution X).cocomplex ComplexShape.embeddingUpNat
          (i := 0) (i' := 0) rfl).inv := by
  delta resι InjectiveResolution.ι' HomologicalComplex.extendSingleIso ComplexShape.Embedding.extendFunctor
  simp [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)]

/- English proof (translation)
Set `g₀ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex` to `{ f := fun i => (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ g.f (i : ℤ) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat (i := i) (i' := ((i : …`. Establish `hdF : (injectiveResolution F).cochainComplex.d (i : ℤ) (j : ℤ) = (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat (i` using `i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ (injectiveResolution F).cocomplex.d i j ≫ (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat (i := j) (i' := ((j : ℕ) : ℤ)) rfl).inv := HomologicalComplex.extend_d_eq _ _ rfl rfl`. Establish `hdG : (injectiveResolution G).cochainComplex.d (i : ℤ) (j : ℤ) = (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat (i` using `i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ (injectiveResolution G).cocomplex.d i j ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat (i := j) (i' := ((j : ℕ) : ℤ)) rfl).inv := HomologicalComplex.extend_d_eq _ _ rfl rfl`. Establish `h1` using `g.comm (i : ℤ) (j : ℤ)`. Rewrite `h1` using `[hdF, hdG]`.

Establish `h2` using `congrArg (fun t => (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ t ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat (i := j) (i' := ((j : ℕ) : ℤ) …`. Simplify using `only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] at h2`. Simplify `h2 }` using `only [Category.assoc]`. Establish `hext : g = HomologicalComplex.extendMap g₀ ComplexShape.embeddingUpNat`. Use extensionality with `j : 1`.

Distinguish the cases in `hj : ∃ i : ℕ, (i : ℤ) = j`. Take `⟨i, rfl⟩` from `hj`. Rewrite using `[HomologicalComplex.extendMap_f g₀ ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl]`. Use `show _ = (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ ((HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ …`. Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]`.

Conclude with `(HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hj ⟨i, hi⟩)).eq_of_src _ _`. Establish `hι : (injectiveResolution F).ι ≫ g₀ = (CochainComplex.single₀ (Shv R)).map φ ≫ (injectiveResolution G).ι`. Apply `HomologicalComplex.from_single_hom_ext` to reduce the goal to its premises. Rewrite using `[HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self]`. Establish `hg'` using `hg`.

Rewrite `hg'` using `[resι_eq_singleObjXSelf_inv_comp, resι_eq_singleObjXSelf_inv_comp]`. Establish `h3` using `congrArg (fun t => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).hom ≫ t ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom) hg'`. Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at h3`. Conclude with `h3`. Rewrite using `[CrystallineSemistableComparison.PostcompositionHomotopy.post_eq K φ g₀ hι n x, ← hext]`.

Both sides reduce to the same expression.
-/
theorem cpost_of_aug {R : Type} [CommRing R] (K : Cx R) {F G : Shv R} (φ : F ⟶ G)
    (g : (injectiveResolution F).cochainComplex ⟶ (injectiveResolution G).cochainComplex)
    (hg : resι R F ≫ g.f 0 = φ ≫ resι R G) (n : ℤ) (x : HK R K F n) :
    cpost K (Cocycle.ofHom g) n n (add_zero n) x = HK.post R K φ n x := by
  let g₀ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex :=
    { f := fun i => (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ g.f (i : ℤ) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom
      comm' := fun i j _ => by
        have hdF : (injectiveResolution F).cochainComplex.d (i : ℤ) (j : ℤ) =
            (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ (injectiveResolution F).cocomplex.d i j ≫ (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := j) (i' := ((j : ℕ) : ℤ)) rfl).inv :=
          HomologicalComplex.extend_d_eq _ _ rfl rfl
        have hdG : (injectiveResolution G).cochainComplex.d (i : ℤ) (j : ℤ) =
            (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ (injectiveResolution G).cocomplex.d i j ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := j) (i' := ((j : ℕ) : ℤ)) rfl).inv :=
          HomologicalComplex.extend_d_eq _ _ rfl rfl
        have h1 := g.comm (i : ℤ) (j : ℤ)
        rw [hdF, hdG] at h1
        have h2 := congrArg (fun t => (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ t ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := j) (i' := ((j : ℕ) : ℤ)) rfl).hom) h1
        simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] at h2
        simpa only [Category.assoc] using h2 }
  have hext : g = HomologicalComplex.extendMap g₀ ComplexShape.embeddingUpNat := by
    ext j : 1
    by_cases hj : ∃ i : ℕ, (i : ℤ) = j
    · obtain ⟨i, rfl⟩ := hj
      rw [HomologicalComplex.extendMap_f g₀ ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl]
      show _ = (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ ((HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ g.f (i : ℤ) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hj ⟨i, hi⟩)).eq_of_src _ _
  have hι : (injectiveResolution F).ι ≫ g₀ =
      (CochainComplex.single₀ (Shv R)).map φ ≫ (injectiveResolution G).ι := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self]
    have hg' := hg
    rw [resι_eq_singleObjXSelf_inv_comp, resι_eq_singleObjXSelf_inv_comp] at hg'
    have h3 := congrArg (fun t => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).hom ≫ t ≫
      (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := 0) (i' := 0) rfl).hom) hg'
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at h3
    exact h3
  rw [CrystallineSemistableComparison.PostcompositionHomotopy.post_eq K φ g₀ hι n x, ← hext]
  rfl

end CrystallineSemistableComparison.CyclicComplexMaps
