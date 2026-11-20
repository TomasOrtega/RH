import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.CotSheaf

def evF (p : ℕ) (V : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p)) ⋙ (evaluation Scheme.{0}ᵒᵖ Type).obj (op V)

instance (A B : Spc) (p : ℕ) (V : Scheme.{0}) : PreservesLimit (pair A B) (evF p V) := by
  unfold evF; infer_instance

def prodEquiv (A B : Spc) (p : ℕ) (V : Scheme.{0}) : Sx (A ⨯ B) p V ≃ Sx A p V × Sx B p V :=
  ((PreservesLimitPair.iso (evF p V) A B) ≪≫ Types.binaryProductIso _ _).toEquiv

/- English proof (translation)
Establish `e1` using `ConcreteCategory.congr_hom (prodComparison_fst (evF p V) A B) y`. Establish `e2` using `ConcreteCategory.congr_hom (prodComparison_snd (evF p V) A B) y`. Simplify using `only [prodEquiv, Iso.toEquiv, Iso.trans_hom, PreservesLimitPair.iso_hom]`. Use `ext`. Simplify using the standard rewrite rules.

Conclude with `e1`. Simplify using the standard rewrite rules. Conclude with `e2`.
-/
theorem prodEquiv_apply {A B : Spc} {p : ℕ} {V : Scheme.{0}} (y : Sx (A ⨯ B) p V) :
    prodEquiv A B p V y = (Sx.map prod.fst y, Sx.map prod.snd y) := by
  have e1 := ConcreteCategory.congr_hom (prodComparison_fst (evF p V) A B) y
  have e2 := ConcreteCategory.congr_hom (prodComparison_snd (evF p V) A B) y
  simp only [prodEquiv, Iso.toEquiv, Iso.trans_hom, PreservesLimitPair.iso_hom]
  ext
  · simp
    exact e1
  · simp
    exact e2

variable {p : ℕ}

/- English proof (translation)
The claim follows from `ConcreteCategory.congr_hom ((φ.app (op (SimplexCategory.mk p))).naturality k.op) y`.
-/
theorem map_res' {E E' : Spc} (φ : E ⟶ E') {V W : Scheme.{0}} (k : W ⟶ V) (y : Sx E p V) :
    Sx.map φ (y.res k) = (Sx.map φ y).res k :=
  ConcreteCategory.congr_hom ((φ.app (op (SimplexCategory.mk p))).naturality k.op) y

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_comp' {E E' E'' : Spc} (φ : E ⟶ E') (ψ : E' ⟶ E'') {V : Scheme.{0}} (y : Sx E p V) :
    Sx.map (φ ≫ ψ) y = Sx.map ψ (Sx.map φ y) := rfl

/- English proof (translation)
The claim follows from `(ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_comp k.op g.op) y).symm`.
-/
theorem res_res {E : Spc} {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (y : Sx E p V) :
    (y.res k).res g = y.res (g ≫ k) :=
  (ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_comp k.op g.op) y).symm

/- English proof (translation)
The claim follows from `ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_id (op V)) y`.
-/
theorem res_id {E : Spc} {V : Scheme.{0}} (y : Sx E p V) : y.res (𝟙 V) = y :=
  ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_id (op V)) y

/- English proof (translation)
The claim follows from `(prodEquiv A B p V).injective (by rw [prodEquiv_apply, prodEquiv_apply, h1, h2])`.
-/
theorem prod_ext {A B : Spc} {V : Scheme.{0}} {y y' : Sx (A ⨯ B) p V} (h1 : Sx.map prod.fst y = Sx.map prod.fst y')
    (h2 : Sx.map prod.snd y = Sx.map prod.snd y') : y = y' :=
  (prodEquiv A B p V).injective (by rw [prodEquiv_apply, prodEquiv_apply, h1, h2])

def mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx (A ⨯ B) p V := (prodEquiv A B p V).symm (a, b)

/- English proof (translation)
Use `(prodEquiv A B p V).apply_symm_apply (a, b)` as an intermediate fact. Rewrite `this` using `[prodEquiv_apply]`. Conclude with `congrArg Prod.fst this`.
-/
theorem fst_mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx.map prod.fst (mkS a b) = a := by
  have := (prodEquiv A B p V).apply_symm_apply (a, b)
  rw [prodEquiv_apply] at this
  exact congrArg Prod.fst this

/- English proof (translation)
Use `(prodEquiv A B p V).apply_symm_apply (a, b)` as an intermediate fact. Rewrite `this` using `[prodEquiv_apply]`. Conclude with `congrArg Prod.snd this`.
-/
theorem snd_mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx.map prod.snd (mkS a b) = b := by
  have := (prodEquiv A B p V).apply_symm_apply (a, b)
  rw [prodEquiv_apply] at this
  exact congrArg Prod.snd this

def mk1 {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : Sx (sch.obj W ⨯ F) p W := mkS (A := sch.obj W) (𝟙 W) z

/- English proof (translation)
The claim follows from `fst_mkS (A := sch.obj W) _ _`.
-/
theorem simplexImage_fst_schemeProductSimplexIdFirst {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : (Sx.map prod.fst (mk1 z) : W ⟶ W) = 𝟙 W :=
  fst_mkS (A := sch.obj W) _ _

/- English proof (translation)
The claim follows from `snd_mkS (A := sch.obj W) _ _`.
-/
theorem simplexImage_snd_schemeProductSimplexIdFirst {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : Sx.map prod.snd (mk1 z) = z :=
  snd_mkS (A := sch.obj W) _ _

/- English proof (translation)
Rewrite using `[← map_comp', prod.map_fst, map_comp']`. Both sides reduce to the same expression.
-/
theorem fst_pm {F : Spc} {U U' V : Scheme.{0}} (f : U' ⟶ U) (y : Sx (sch.obj U' ⨯ F) p V) :
    (Sx.map prod.fst (Sx.map (prod.map (sch.map f) (𝟙 F)) y) : V ⟶ U) = (Sx.map prod.fst y : V ⟶ U') ≫ f := by
  rw [← map_comp', prod.map_fst, map_comp']
  rfl

/- English proof (translation)
Rewrite using `[← map_comp', prod.map_snd, Category.comp_id]`.
-/
theorem snd_pm {F : Spc} {U U' V : Scheme.{0}} (f : U' ⟶ U) (y : Sx (sch.obj U' ⨯ F) p V) :
    Sx.map prod.snd (Sx.map (prod.map (sch.map f) (𝟙 F)) y) = Sx.map prod.snd y := by
  rw [← map_comp', prod.map_snd, Category.comp_id]

/- English proof (translation)
Rewrite using `[map_res']`. Both sides reduce to the same expression.
-/
theorem fst_res {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    (Sx.map prod.fst (y.res k) : W ⟶ U) = k ≫ (Sx.map prod.fst y : V ⟶ U) := by
  rw [map_res']
  rfl

/- English proof (translation)
The claim follows from `map_res' _ _ _`.
-/
theorem snd_res {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    Sx.map prod.snd (y.res k) = (Sx.map prod.snd y).res k :=
  map_res' _ _ _

/- English proof (translation)
The claim follows from `prod_ext (by rw [fst_pm, simplexImage_fst_schemeProductSimplexIdFirst, Category.id_comp, fst_res]) (by rw [snd_pm, simplexImage_snd_schemeProductSimplexIdFirst, snd_res])`.
-/
theorem yres_eq {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    y.res k = Sx.map (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 F)) (mk1 ((Sx.map prod.snd y).res k)) :=
  prod_ext (by rw [fst_pm, simplexImage_fst_schemeProductSimplexIdFirst, Category.id_comp, fst_res]) (by rw [snd_pm, simplexImage_snd_schemeProductSimplexIdFirst, snd_res])

/- English proof (translation)
Rewrite using `[Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]`. Establish `hQ : ∀ s, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))` using `fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).cond)`. Establish `sres_res : ∀ (s : ℤ) {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (v : Sec (I.X s) V), Sec.res g (Sec.res k v) = Sec.res (g ≫ k) v` using `fun s V W W' k g v => (ConcreteCategory.congr_hom (((I.X s).obj).map_comp k.op g.op) v).symm`. Establish `sres_id : ∀ (s : ℤ) {V : Scheme.{0}} (v : Sec (I.X s) V), Sec.res (𝟙 V) v = v` using `fun s V v => ConcreteCategory.congr_hom (((I.X s).obj).map_id (op V)) v`. Introduce `U S hS`.

Establish `hsep : Presieve.IsSeparatedFor (cotPre R q N I n ⋙ forget _) S.arrows`. Introduce `x α β hα hβ`. Establish `hc : ∀ (W : Scheme.{0}) (c : W ⟶ U), S.arrows c → (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) = (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp β (zero_add n)` using `fun W c hc => (hα c hc).trans (hβ c hc).symm`. Use `ev_ext _ _ fun p s h V y => ?_` and prove the remaining obligations. Use `(hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).isSeparatedFor.ext fun W k hk => ?_` and prove the remaining obligations.

Establish `e1` using `ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) α p s h k y`. Establish `e2` using `ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) β p s h k y`. Use `e1.trans (Eq.trans ?_ e2.symm)` and prove the remaining obligations. Establish `e3` using `ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) α p s h W (mk1 ((Sx.map prod.snd y).res k))`. Establish `e4` using `ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) β p s h W (mk1 ((Sx.map prod.snd y).res k))`.

Rewrite using `[yres_eq k y, ← e3, ← e4, hc _ _ hk]`. Use `hsep.isSheafFor fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `(Presieve.compatible_iff_sieveCompatible x).1 hx`. Establish `evx : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c c' : W ⟶ U) (hc : S.arrows c) (hc' : S.arrows c') (w w' : Sx (sch.obj W ⨯ fibQ q N) p V), c = c' → w = w' → ev (x c hc) p s h V w = ev (x c' hc') p s h V w'`. Introduce and unpack `p s h V W c c' hc hc' w w' rfl rfl`.

Both sides reduce to the same expression. Establish `gen : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c : W ⟶ U) (hc : S.arrows c) (w : Sx (sch.obj W ⨯ fibQ q N) p V), ev (x c hc) p s h V w = ev (x ((Sx.map prod.fst w : V ⟶ W) ≫ c) (S.downward_closed hc _)) p s h V (mk1 (Sx.map prod.snd w))`. Introduce `p s h V W c hc w`. Establish `e2` using `ev_pull (R := R) (I := I) (n := n) (E := sch.obj W ⨯ fibQ q N) (prod.map (sch.map (Sx.map prod.fst w : V ⟶ W)) (𝟙 (fibQ q N))) (x c hc) p s h V (mk1 (Sx.map prod.snd w))`. Rewrite using `[hx' c (Sx.map prod.fst w : V ⟶ W) hc]`.

Use `Eq.trans ?_ e2.symm` and prove the remaining obligations. Use `congr 1`. Conclude with `(prod_ext ((fst_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (by rw [simplexImage_fst_schemeProductSimplexIdFirst]; exact Category.id_comp _)) ((snd_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (simplexImage_snd_schemeProductSimplexIdFirst _) …`. Set `φ : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V), Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (S.pullback (Sx.map prod.fst y : V ⟶ U)).arrows` to `fun p s h V y W k hk => ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k))`. Establish `hφ : ∀ p s h V y, (φ p s h V y).Compatible`.

Introduce `p s h V y`. Rewrite using `[Presieve.compatible_iff_sieveCompatible]`. Introduce `W W' k g hk`. Express the relevant statement in the definitionally equal form `ev (x (g ≫ k ≫ _) _) p s h W' (mk1 _) = Sec.res g (ev (x (k ≫ _) hk) p s h W (mk1 _))`. Use `Eq.trans ?_ (ev_res (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) (n := n) (x (k ≫ _) hk) p s h g _).symm` and prove the remaining obligations.

Use `Eq.trans ?_ (gen p s h _ hk _).symm` and prove the remaining obligations. Apply `evx` to reduce the goal to its premises. Rewrite using `[fst_res, simplexImage_fst_schemeProductSimplexIdFirst, Category.comp_id]`. Rewrite using `[snd_res, simplexImage_snd_schemeProductSimplexIdFirst, res_res]`. Set `val : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}), Sx (sch.obj U ⨯ fibQ q N) p V → Sec (I.X s) V` to `fun p s h V y => (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).amalgamate (φ p s h V y) (hφ p s h V y)`.

Establish `hval : ∀ p s h V y {W : Scheme.{0}} (k : W ⟶ V) (hk : S.arrows (k ≫ Sx.map prod.fst y)), Sec.res k (val p s h V y) = ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k))` using `fun p s h V y W k hk => (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).valid_glue (hφ p s h V y) k hk`. Establish `hnat : ∀ p s h (V V' : Scheme.{0}) (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V), Sec.res g (val p s h V y) = val p s h V' (y.res g)`. Introduce `p s h V V' g y`. Use `(hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst (y.res g) : V' ⟶ U) hS)).isSeparatedFor.ext fun W k hk => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Sec.res k (Sec.res g _) = Sec.res k (val p s h V' (y.res g))`.

Establish `hk' : S.arrows ((k ≫ g) ≫ Sx.map prod.fst y)`. Establish `: S.arrows (k ≫ Sx.map prod.fst (y.res g))` using `hk`. Rewrite `this` using `[fst_res]`. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `Category.assoc _ _ _`.

Rewrite using `[sres_res, hval _ _ _ _ _ _ hk', hval _ _ _ _ _ _ hk]`. Apply `evx` to reduce the goal to its premises. Rewrite using `[fst_res]`. Conclude with `Category.assoc _ _ _`. Rewrite using `[snd_res, res_res]`.

Take `⟨α, hα⟩` from `ev_exists (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) val (fun p s h V' V g y => hnat p s h V V' g y)`. Use `⟨α, fun W c hc => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) = x c hc`. Use `ev_ext _ _ fun p s h V w => ?_` and prove the remaining obligations. Establish `h1 : S.arrows (𝟙 V ≫ Sx.map prod.fst (Sx.map (prod.map (sch.map c) (𝟙 (fibQ q N))) w))`.

Use `S.downward_closed hc (Sx.map prod.fst w : V ⟶ W)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `(Category.id_comp _).trans (fst_pm c w)`. Use `(ev_pull (R := R) (I := I) (n := n) (E := sch.obj U ⨯ fibQ q N) _ α p s h V w).trans ?_` and prove the remaining obligations. Rewrite using `[hα]`.

Use `(sres_id s _).symm.trans ((hval _ _ _ _ _ _ h1).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (gen p s h c hc w).symm` and prove the remaining obligations. Apply `evx` to reduce the goal to its premises. Conclude with `(Category.id_comp _).trans (fst_pm c w)`. Rewrite using `[res_id, snd_pm]`.
-/
theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hQ : ∀ s, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).cond)
  have sres_res : ∀ (s : ℤ) {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (v : Sec (I.X s) V),
      Sec.res g (Sec.res k v) = Sec.res (g ≫ k) v := fun s V W W' k g v =>
    (ConcreteCategory.congr_hom (((I.X s).obj).map_comp k.op g.op) v).symm
  have sres_id : ∀ (s : ℤ) {V : Scheme.{0}} (v : Sec (I.X s) V), Sec.res (𝟙 V) v = v := fun s V v =>
    ConcreteCategory.congr_hom (((I.X s).obj).map_id (op V)) v
  intro U S hS
  have hsep : Presieve.IsSeparatedFor (cotPre R q N I n ⋙ forget _) S.arrows := by
    intro x α β hα hβ
    have hc : ∀ (W : Scheme.{0}) (c : W ⟶ U), S.arrows c →
        (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp β (zero_add n) :=
      fun W c hc => (hα c hc).trans (hβ c hc).symm
    refine ev_ext _ _ fun p s h V y => ?_
    refine (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).isSeparatedFor.ext
      fun W k hk => ?_
    have e1 := ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) α p s h k y
    have e2 := ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) β p s h k y
    refine e1.trans (Eq.trans ?_ e2.symm)
    have e3 := ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) α
      p s h W (mk1 ((Sx.map prod.snd y).res k))
    have e4 := ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) β
      p s h W (mk1 ((Sx.map prod.snd y).res k))
    rw [yres_eq k y, ← e3, ← e4, hc _ _ hk]
  refine hsep.isSheafFor fun x hx => ?_
  have hx' := (Presieve.compatible_iff_sieveCompatible x).1 hx
  have evx : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c c' : W ⟶ U) (hc : S.arrows c)
      (hc' : S.arrows c') (w w' : Sx (sch.obj W ⨯ fibQ q N) p V), c = c' → w = w' →
        ev (x c hc) p s h V w = ev (x c' hc') p s h V w' := by
    rintro p s h V W c c' hc hc' w w' rfl rfl
    rfl
  have gen : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c : W ⟶ U) (hc : S.arrows c)
      (w : Sx (sch.obj W ⨯ fibQ q N) p V), ev (x c hc) p s h V w =
        ev (x ((Sx.map prod.fst w : V ⟶ W) ≫ c) (S.downward_closed hc _)) p s h V (mk1 (Sx.map prod.snd w)) := by
    intro p s h V W c hc w
    have e2 := ev_pull (R := R) (I := I) (n := n) (E := sch.obj W ⨯ fibQ q N)
      (prod.map (sch.map (Sx.map prod.fst w : V ⟶ W)) (𝟙 (fibQ q N))) (x c hc) p s h V (mk1 (Sx.map prod.snd w))
    rw [hx' c (Sx.map prod.fst w : V ⟶ W) hc]
    refine Eq.trans ?_ e2.symm
    congr 1
    exact (prod_ext ((fst_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (by rw [simplexImage_fst_schemeProductSimplexIdFirst]; exact Category.id_comp _))
      ((snd_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (simplexImage_snd_schemeProductSimplexIdFirst _))).symm
  let φ : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V),
      Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (Sx.map prod.fst y : V ⟶ U)).arrows :=
    fun p s h V y W k hk => ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k))
  have hφ : ∀ p s h V y, (φ p s h V y).Compatible := by
    intro p s h V y
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W W' k g hk
    change ev (x (g ≫ k ≫ _) _) p s h W' (mk1 _) = Sec.res g (ev (x (k ≫ _) hk) p s h W (mk1 _))
    refine Eq.trans ?_ (ev_res (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) (n := n) (x (k ≫ _) hk) p s h g _).symm
    refine Eq.trans ?_ (gen p s h _ hk _).symm
    apply evx
    · rw [fst_res, simplexImage_fst_schemeProductSimplexIdFirst, Category.comp_id]
    · rw [snd_res, simplexImage_snd_schemeProductSimplexIdFirst, res_res]
  let val : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}), Sx (sch.obj U ⨯ fibQ q N) p V → Sec (I.X s) V :=
    fun p s h V y => (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).amalgamate
      (φ p s h V y) (hφ p s h V y)
  have hval : ∀ p s h V y {W : Scheme.{0}} (k : W ⟶ V) (hk : S.arrows (k ≫ Sx.map prod.fst y)),
      Sec.res k (val p s h V y) = ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k)) :=
    fun p s h V y W k hk =>
      (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).valid_glue (hφ p s h V y) k hk
  have hnat : ∀ p s h (V V' : Scheme.{0}) (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V),
      Sec.res g (val p s h V y) = val p s h V' (y.res g) := by
    intro p s h V V' g y
    refine (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst (y.res g) : V' ⟶ U) hS)).isSeparatedFor.ext
      fun W k hk => ?_
    change Sec.res k (Sec.res g _) = Sec.res k (val p s h V' (y.res g))
    have hk' : S.arrows ((k ≫ g) ≫ Sx.map prod.fst y) := by
      have : S.arrows (k ≫ Sx.map prod.fst (y.res g)) := hk
      rw [fst_res] at this
      convert this using 2
      exact Category.assoc _ _ _
    rw [sres_res, hval _ _ _ _ _ _ hk', hval _ _ _ _ _ _ hk]
    apply evx
    · rw [fst_res]
      exact Category.assoc _ _ _
    · rw [snd_res, res_res]
  obtain ⟨α, hα⟩ := ev_exists (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) val
    (fun p s h V' V g y => hnat p s h V V' g y)
  refine ⟨α, fun W c hc => ?_⟩
  change (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) = x c hc
  refine ev_ext _ _ fun p s h V w => ?_
  have h1 : S.arrows (𝟙 V ≫ Sx.map prod.fst (Sx.map (prod.map (sch.map c) (𝟙 (fibQ q N))) w)) := by
    have := S.downward_closed hc (Sx.map prod.fst w : V ⟶ W)
    convert this using 2
    exact (Category.id_comp _).trans (fst_pm c w)
  refine (ev_pull (R := R) (I := I) (n := n) (E := sch.obj U ⨯ fibQ q N) _ α p s h V w).trans ?_
  rw [hα]
  refine (sres_id s _).symm.trans ((hval _ _ _ _ _ _ h1).trans ?_)
  refine Eq.trans ?_ (gen p s h c hc w).symm
  apply evx
  · exact (Category.id_comp _).trans (fst_pm c w)
  · rw [res_id, snd_pm]

end GlobalTheory.EtC.CotSheaf

end
