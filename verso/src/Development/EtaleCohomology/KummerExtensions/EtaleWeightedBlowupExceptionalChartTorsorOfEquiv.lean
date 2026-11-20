import Mathlib
import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf
import Development.EtaleCohomology.CohomologicalPurity.LeafWCechRec

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.Thom LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

namespace WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence

def ringOf {A : Type} [CommRing A] {U : Scheme.{0}} (h : U ⟶ Spec (CommRingCat.of A)) : A →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ h.appTop).hom

def ptOf {A : Type} [CommRing A] {U : Scheme.{0}} (E : A →+* Γ(U, ⊤)) : U ⟶ Spec (CommRingCat.of A) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom E)

/- English proof (translation)
Rewrite using `[ringOf, ringOf, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
theorem ringOf_comp {A : Type} [CommRing A] {U V : Scheme.{0}} (f : V ⟶ U) (h : U ⟶ Spec (CommRingCat.of A)) :
    ringOf (f ≫ h) = f.appTop.hom.comp (ringOf h) := by
  rw [ringOf, ringOf, Scheme.Hom.comp_appTop]; rfl

/- English proof (translation)
Establish `: (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ptOf E).appTop = CommRingCat.ofHom E`. Rewrite using `[ptOf, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]`. Rewrite using `[ringOf, this]`. Both sides reduce to the same expression.
-/
theorem ringOf_ptOf {A : Type} [CommRing A] {U : Scheme.{0}} (E : A →+* Γ(U, ⊤)) : ringOf (ptOf E) = E := by
  have : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ptOf E).appTop = CommRingCat.ofHom E := by
    rw [ptOf, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rw [ringOf, this]; rfl

/- English proof (translation)
Apply `ext_to_Spec` to reduce the goal to its premises. Conclude with `CommRingCat.hom_ext e`.
-/
theorem point_ext {A : Type} [CommRing A] {U : Scheme.{0}} {h h' : U ⟶ Spec (CommRingCat.of A)}
    (e : ringOf h = ringOf h') : h = h' := by
  apply ext_to_Spec
  exact CommRingCat.hom_ext e

/- English proof (translation)
The claim follows from `point_ext (ringOf_ptOf _)`.
-/
theorem ptOf_ringOf {A : Type} [CommRing A] {U : Scheme.{0}} (h : U ⟶ Spec (CommRingCat.of A)) :
    ptOf (ringOf h) = h := point_ext (ringOf_ptOf _)

variable {d : ℕ} {R : Type} [CommRing R]

def unit0 {U : Scheme.{0}} (v : WVec d U) : (Γ(U, ⊤))ˣ := v.2.unit

def ratio {U : Scheme.{0}} (v : WVec d U) (k : Fin d) : Γ(U, ⊤) := v.1.1 k.succ * ((unit0 v)⁻¹ : (Γ(U, ⊤))ˣ)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `h0 : v.1.1 0 = (a.1 : Γ(U, ⊤)) * w.1.1 0` using `a.2 0`. Establish `hu : unit0 v = a.1 * unit0 w` using `Units.ext h0`. Establish `hk : v.1.1 k.succ = (a.1 : Γ(U, ⊤)) * w.1.1 k.succ` using `a.2 k.succ`. Rewrite using `[ratio, ratio, hk, hu, mul_inv_rev, Units.val_mul]`.

Establish `: (a.1 : Γ(U, ⊤)) * ((a.1⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = 1` using `Units.mul_inv _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ratio_hom {U : Scheme.{0}} {v w : WVec d U} (a : v ⟶ w) : ratio v = ratio w := by
  funext k
  have h0 : v.1.1 0 = (a.1 : Γ(U, ⊤)) * w.1.1 0 := a.2 0
  have hu : unit0 v = a.1 * unit0 w := Units.ext h0
  have hk : v.1.1 k.succ = (a.1 : Γ(U, ⊤)) * w.1.1 k.succ := a.2 k.succ
  rw [ratio, ratio, hk, hu, mul_inv_rev, Units.val_mul]
  have : (a.1 : Γ(U, ⊤)) * ((a.1⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = 1 := Units.mul_inv _
  calc _ = ((a.1 : Γ(U, ⊤)) * ((a.1⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤))) * (w.1.1 k.succ * (((unit0 w)⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤))) := by ring
    _ = _ := by rw [this, one_mul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Establish `ha : v.1.1 0 = (a.1 : Γ(U, ⊤)) * w.1.1 0` using `a.2 0`. Establish `hb : v.1.1 0 = (b.1 : Γ(U, ⊤)) * w.1.1 0` using `b.2 0`. Conclude with `(unit0 w).isUnit.mul_right_cancel (ha.symm.trans hb)`.
-/
theorem wvec_hom_sub {U : Scheme.{0}} {v w : WVec d U} (a b : v ⟶ w) : a = b := by
  apply Subtype.ext
  apply Units.ext
  have ha : v.1.1 0 = (a.1 : Γ(U, ⊤)) * w.1.1 0 := a.2 0
  have hb : v.1.1 0 = (b.1 : Γ(U, ⊤)) * w.1.1 0 := b.2 0
  exact (unit0 w).isUnit.mul_right_cancel (ha.symm.trans hb)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `Fin.cases (congrArg Units.val h0) (fun k => ?_) i` and prove the remaining obligations. Establish `hk` using `congrFun h k`.

Rewrite `hk` using `[ratio, ratio, h0]`. Conclude with `(unit0 w)⁻¹.isUnit.mul_right_cancel hk`.
-/
theorem wvec_ext {U : Scheme.{0}} {v w : WVec d U} (h0 : unit0 v = unit0 w) (h : ratio v = ratio w) : v = w := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  refine Fin.cases (congrArg Units.val h0) (fun k => ?_) i
  have hk := congrFun h k
  rw [ratio, ratio, h0] at hk
  exact (unit0 w)⁻¹.isUnit.mul_right_cancel hk

/- English proof (translation)
Establish `h : unit0 ((WVec.map d f).obj v) = Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤)) (unit0 v)` using `Units.ext rfl`. Rewrite using `[ratio, ratio, h, ← map_inv, map_mul]`. Both sides reduce to the same expression.
-/
theorem ratio_map {U V : Scheme.{0}} (f : V ⟶ U) (v : WVec d U) (k : Fin d) :
    ratio ((WVec.map d f).obj v) k = f.appTop.hom (ratio v k) := by
  have h : unit0 ((WVec.map d f).obj v) = Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤)) (unit0 v) := Units.ext rfl
  rw [ratio, ratio, h, ← map_inv, map_mul]
  rfl

def ringA {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of R)) (v : WVec d U) : MvPolynomial (Fin d) R →+* Γ(U, ⊤) :=
  MvPolynomial.eval₂Hom (ringOf s) (ratio v)

def ringG {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : LaurentPolynomial ℤ →+* Γ(U, ⊤) :=
  LaurentPolynomial.eval₂ (Int.castRingHom _) u

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[ringA, ringOf_comp]`. Introduce `k`. Simplify using `[ringA, ratio_map]`.
-/
theorem ringA_map {U V : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of R)) (v : WVec d U) :
    ringA (f ≫ s) ((WVec.map d f).obj v) = f.appTop.hom.comp (ringA s v) := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [ringA, ringOf_comp]
  · intro k; simp [ringA, ratio_map]

/- English proof (translation)
Apply `point_ext` to reduce the goal to its premises. Rewrite using `[ringOf_comp, ringOf_ptOf, ringOf_ptOf]`.
-/
theorem comp_ptOf {A : Type} [CommRing A] {U V : Scheme.{0}} (f : V ⟶ U) (E : A →+* Γ(U, ⊤)) :
    f ≫ ptOf E = ptOf (f.appTop.hom.comp E) := by
  apply point_ext
  rw [ringOf_comp, ringOf_ptOf, ringOf_ptOf]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [ringG]`.
-/
theorem ringG_map {U V : Scheme.{0}} (f : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    ringG (Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤)) u) = f.appTop.hom.comp (ringG u) := by
  ext x <;> simp [ringG]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun F => F (LaurentPolynomial.T 1)) h` as an intermediate fact. Simplify `this` using `[ringG]`.
-/
theorem ringG_inj {U : Scheme.{0}} {u w : (Γ(U, ⊤))ˣ} (h : ringG u = ringG w) : u = w := by
  apply Units.ext
  have := congrArg (fun F => F (LaurentPolynomial.T 1)) h
  simpa [ringG] using this

/- English proof (translation)
The claim follows from `ConcreteCategory.congr_hom ((f.app n).naturality t) a`.
-/
theorem simplicial_presheaf_hom_scheme_naturality_apply {E E' : Spc} (f : E ⟶ E') (n : SimplexCategoryᵒᵖ) {T T' : Scheme.{0}ᵒᵖ} (t : T ⟶ T')
    (a : (E.obj n).obj T) : (f.app n).app T' ((E.obj n).map t a) = (E'.obj n).map t ((f.app n).app T a) :=
  ConcreteCategory.congr_hom ((f.app n).naturality t) a

/- English proof (translation)
The claim follows from `ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality θ) T) a`.
-/
theorem nat_N {E E' : Spc} (f : E ⟶ E') {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (T : Scheme.{0}ᵒᵖ)
    (a : (E.obj n).obj T) : (f.app m).app T ((E.map θ).app T a) = (E'.map θ).app T ((f.app n).app T a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality θ) T) a

def chn {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    ComposableArrows (WVec d T.unop) n.unop.len :=
  ((prod.fst : W d R ⟶ Wsp d).app n).app T a

def bas {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    T.unop ⟶ Spec (CommRingCat.of R) :=
  ((prod.snd : W d R ⟶ sp R).app n).app T a

/- English proof (translation)
The claim follows from `simplicial_presheaf_hom_scheme_naturality_apply (prod.fst : W d R ⟶ Wsp d) n t a`.
-/
theorem chn_mapT {n : SimplexCategoryᵒᵖ} {T T' : Scheme.{0}ᵒᵖ} (t : T ⟶ T') (a : ((W d R).obj n).obj T) :
    chn (((W d R).obj n).map t a) = (chn a ⋙ WVec.map d t.unop : ComposableArrows (WVec d T'.unop) n.unop.len) :=
  simplicial_presheaf_hom_scheme_naturality_apply (prod.fst : W d R ⟶ Wsp d) n t a

/- English proof (translation)
The claim follows from `simplicial_presheaf_hom_scheme_naturality_apply (prod.snd : W d R ⟶ sp R) n t a`.
-/
theorem bas_mapT {n : SimplexCategoryᵒᵖ} {T T' : Scheme.{0}ᵒᵖ} (t : T ⟶ T') (a : ((W d R).obj n).obj T) :
    bas (((W d R).obj n).map t a) = t.unop ≫ bas a :=
  simplicial_presheaf_hom_scheme_naturality_apply (prod.snd : W d R ⟶ sp R) n t a

/- English proof (translation)
Rewrite using `[chn, nat_N]`. Both sides reduce to the same expression.
-/
theorem chn_mapN {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) (i) :
    (chn (((W d R).map θ).app T a)).obj i = (chn a).obj ((SimplexCategory.toCat.map θ.unop).toFunctor.obj i) := by
  rw [chn, nat_N]; rfl

/- English proof (translation)
The claim follows from `nat_N (prod.snd : W d R ⟶ sp R) θ T a`.
-/
theorem bas_mapN {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    bas (((W d R).map θ).app T a) = bas a :=
  nat_N (prod.snd : W d R ⟶ sp R) θ T a

/- English proof (translation)
Break down `le_total i j with h | h` into its components or cases. Conclude with `ratio_hom (c.map (homOfLE h))`. Conclude with `(ratio_hom (c.map (homOfLE h))).symm`.
-/
theorem ratio_chain {U : Scheme.{0}} {m : ℕ} (c : ComposableArrows (WVec d U) m) (i j : Fin (m + 1)) :
    ratio (c.obj i) = ratio (c.obj j) := by
  rcases le_total i j with h | h
  · exact ratio_hom (c.map (homOfLE h))
  · exact (ratio_hom (c.map (homOfLE h))).symm

/- English proof (translation)
Rewrite using `[ringA, ringA, h]`.
-/
theorem ringA_congr {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of R)) {v w : WVec d U} (h : ratio v = ratio w) :
    ringA s v = ringA s w := by
  rw [ringA, ringA, h]

def ptW {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    T.unop ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)) :=
  ptOf (ringA (bas a) ((chn a).obj 0))

/- English proof (translation)
Rewrite using `[ptW, ptW, comp_ptOf, bas_mapT, chn_mapT, ← ringA_map]`. Both sides reduce to the same expression.
-/
theorem ptW_mapT {n : SimplexCategoryᵒᵖ} {T T' : Scheme.{0}ᵒᵖ} (t : T ⟶ T') (a : ((W d R).obj n).obj T) :
    ptW (((W d R).obj n).map t a) = t.unop ≫ ptW a := by
  rw [ptW, ptW, comp_ptOf, bas_mapT, chn_mapT, ← ringA_map]
  rfl

/- English proof (translation)
Rewrite using `[ptW, ptW, bas_mapN, chn_mapN]`. Conclude with `congrArg ptOf (ringA_congr _ (ratio_chain _ _ _))`.
-/
theorem ptW_mapN {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    ptW (((W d R).map θ).app T a) = ptW a := by
  rw [ptW, ptW, bas_mapN, chn_mapN]
  exact congrArg ptOf (ringA_congr _ (ratio_chain _ _ _))

def rW (d : ℕ) (R : Type) [CommRing R] :
    W d R ⟶ disc.obj (yoneda.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) R)))) where
  app n :=
    { app := fun T => TypeCat.ofHom fun a => ptW a
      naturality := fun T T' t => by
        ext a
        exact ptW_mapT t a }
  naturality n m θ := by
    ext T a
    exact ptW_mapN θ a

def lif {S T : Scheme.{0}} (V : S.Opens) (g : T ⟶ S) (h : ∀ p, g p ∈ V) : T ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι g (by rintro _ ⟨p, rfl⟩; rw [Scheme.Opens.range_ι]; exact h p)

/- English proof (translation)
The claim follows from `IsOpenImmersion.lift_fac _ _ _`.
-/
theorem lif_ι {S T : Scheme.{0}} (V : S.Opens) (g : T ⟶ S) (h : ∀ p, g p ∈ V) : lif V g h ≫ V.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

def evS {E : Spc} {S : Scheme.{0}} (f : E ⟶ sch.obj S) (n : SimplexCategoryᵒᵖ) (T : Scheme.{0}ᵒᵖ)
    (x : (E.obj n).obj T) : T.unop ⟶ S := (f.app n).app T x

def liftOpen {E : Spc} {S : Scheme.{0}} (V : S.Opens) (f : E ⟶ sch.obj S)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (T : Scheme.{0}ᵒᵖ) (x : (E.obj n).obj T) (p : T.unop), evS f n T x p ∈ V) :
    E ⟶ sch.obj V.toScheme where
  app n :=
    { app := fun T => TypeCat.ofHom fun x => lif V (evS f n T x) (h n T x)
      naturality := fun T T' t => by
        ext x
        refine (cancel_mono V.ι).1 ?_
        change lif V (evS f n T' ((E.obj n).map t x)) (h n T' _) ≫ V.ι =
          (t.unop ≫ lif V (evS f n T x) (h n T x)) ≫ V.ι
        rw [lif_ι, Category.assoc, lif_ι]
        exact simplicial_presheaf_hom_scheme_naturality_apply f n t x }
  naturality n m θ := by
    ext T x
    refine (cancel_mono V.ι).1 ?_
    change lif V (evS f m T ((E.map θ).app T x)) (h m T _) ≫ V.ι = lif V (evS f n T x) (h n T x) ≫ V.ι
    rw [lif_ι, lif_ι]
    exact nat_N f θ T x

/- English proof (translation)
Use extensionality with `n T x`. Conclude with `lif_ι V (evS f n T x) (h n T x)`.
-/
theorem liftOpen_comp {E : Spc} {S : Scheme.{0}} (V : S.Opens) (f : E ⟶ sch.obj S) (h) :
    liftOpen V f h ≫ sch.map V.ι = f := by
  ext n T x
  exact lif_ι V (evS f n T x) (h n T x)

/- English proof (translation)
Establish `e : U.basicOpen (ringOf h r) = h ⁻¹ᵁ (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)`. Rewrite using `[Scheme.preimage_basicOpen_top]`. Both sides reduce to the same expression. Establish `hb : (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) = PrimeSpectrum.basicOpen r` using `basicOpen_eq_of_affine (R := CommRingCat.of A) r`. Rewrite using `[e, hb]`.

Conclude with `Iff.rfl`.
-/
theorem mem_basicOpen_ringOf {A : Type} [CommRing A] {U : Scheme.{0}} (h : U ⟶ Spec (CommRingCat.of A)) (p : U) (r : A) :
    p ∈ U.basicOpen (ringOf h r) ↔ r ∉ (h p).asIdeal := by
  have e : U.basicOpen (ringOf h r) = h ⁻¹ᵁ (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) := by
    rw [Scheme.preimage_basicOpen_top]; rfl
  have hb : (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) =
      PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine (R := CommRingCat.of A) r
  rw [e, hb]
  exact Iff.rfl

/- English proof (translation)
Simplify using `only [mem_basicOpen_ringOf]`. Establish `key : ∀ P : PrimeSpectrum A, P ∉ PrimeSpectrum.zeroLocus (I : Set A) ↔ ∃ k, x k ∉ P.asIdeal`. Introduce `P`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, ← hI, SetLike.coe_subset_coe, Ideal.span_le]`. Simplify using `[Set.range_subset_iff]`.

Conclude with `key (h p)`.
-/
theorem mem_off {A : Type} [CommRing A] {U : Scheme.{0}} (h : U ⟶ Spec (CommRingCat.of A)) (p : U) {m : ℕ}
    (x : Fin m → A) (I : Ideal A) (hI : Ideal.span (Set.range x) = I) :
    h p ∈ off A I ↔ ∃ k, p ∈ U.basicOpen (ringOf h (x k)) := by
  simp only [mem_basicOpen_ringOf]
  have key : ∀ P : PrimeSpectrum A, P ∉ PrimeSpectrum.zeroLocus (I : Set A) ↔ ∃ k, x k ∉ P.asIdeal := by
    intro P
    rw [PrimeSpectrum.mem_zeroLocus, ← hI, SetLike.coe_subset_coe, Ideal.span_le]
    simp [Set.range_subset_iff]
  exact key (h p)

abbrev Xs (d : ℕ) (R : Type) [CommRing R] : Spc := pullback (wb d R) (pr d R).hom

def xa {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj n).obj T) : ((W d R).obj n).obj T :=
  ((pullback.fst (wb d R) (pr d R).hom).app n).app T x

/- English proof (translation)
The claim follows from `simplicial_presheaf_hom_scheme_naturality_apply (pullback.fst (wb d R) (pr d R).hom) n t x`.
-/
theorem xa_mapT {n : SimplexCategoryᵒᵖ} {T T' : Scheme.{0}ᵒᵖ} (t : T ⟶ T') (x : ((Xs d R).obj n).obj T) :
    xa (((Xs d R).obj n).map t x) = ((W d R).obj n).map t (xa x) :=
  simplicial_presheaf_hom_scheme_naturality_apply (pullback.fst (wb d R) (pr d R).hom) n t x

/- English proof (translation)
The claim follows from `nat_N (pullback.fst (wb d R) (pr d R).hom) θ T x`.
-/
theorem xa_mapN {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj n).obj T) :
    xa (((Xs d R).map θ).app T x) = ((W d R).map θ).app T (xa x) :=
  nat_N (pullback.fst (wb d R) (pr d R).hom) θ T x

/- English proof (translation)
Set `b : ((PR (d + 1) 1 R).obj n).obj T` to `((pullback.snd (wb d R) (pr d R).hom).app n).app T x`. Set `c1 : ComposableArrows (Vec (d + 1) 1 T.unop) n.unop.len` to `((prod.fst : PR (d + 1) 1 R ⟶ Pj (d + 1) 1).app n).app T b`. Establish `hc : ((wb d R).app n).app T (xa x) = ((pr d R).hom.app n).app T b` using `ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app (pullback.condition (f := wb d R) (g := (pr d R).hom)) n) T) x`. Establish `e1 : wb d R ≫ prod.fst = prod.fst ≫ Wincl d` using `prod.map_fst _ _`. Establish `e2 : (pr d R).hom ≫ (prod.fst : PR (d + 1) 0 R ⟶ _) = prod.fst ≫ Pj.incl (d + 1)` using `prod.map_fst _ _`.

Establish `key : ((Wincl d).app n).app T (chn (xa x)) = ((Pj.incl (d + 1)).app n).app T c1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((chn (xa x)).obj i).1 = (Vec.incl (d + 1) T.unop).obj (c1.obj i)` using `congrArg (fun K : ComposableArrows (Vec (d + 1) 0 T.unop) n.unop.len => K.obj i) key`. Establish `hv : ((chn (xa x)).obj i).1.1 = (c1.obj i).1` using `congrArg Subtype.val h2`. Take `⟨j, hj, hp⟩` from `(c1.obj i).2 p`.

Conclude with `⟨j, hj, by rw [hv]; exact hp⟩`.
-/
theorem tail_of_X {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj n).obj T) (i) (p : T.unop) :
    ∃ j : Fin (d + 1), 1 ≤ j.val ∧ p ∈ T.unop.basicOpen (((chn (xa x)).obj i).1.1 j) := by
  let b : ((PR (d + 1) 1 R).obj n).obj T := ((pullback.snd (wb d R) (pr d R).hom).app n).app T x
  let c1 : ComposableArrows (Vec (d + 1) 1 T.unop) n.unop.len := ((prod.fst : PR (d + 1) 1 R ⟶ Pj (d + 1) 1).app n).app T b
  have hc : ((wb d R).app n).app T (xa x) = ((pr d R).hom.app n).app T b :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app
      (pullback.condition (f := wb d R) (g := (pr d R).hom)) n) T) x
  have e1 : wb d R ≫ prod.fst = prod.fst ≫ Wincl d := prod.map_fst _ _
  have e2 : (pr d R).hom ≫ (prod.fst : PR (d + 1) 0 R ⟶ _) = prod.fst ≫ Pj.incl (d + 1) := prod.map_fst _ _
  have key : ((Wincl d).app n).app T (chn (xa x)) = ((Pj.incl (d + 1)).app n).app T c1 := by
    calc ((Wincl d).app n).app T (chn (xa x))
        = ((prod.fst ≫ Wincl d).app n).app T (xa x) := rfl
      _ = ((wb d R ≫ prod.fst).app n).app T (xa x) := by rw [e1]
      _ = ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app T (((wb d R).app n).app T (xa x)) := rfl
      _ = ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app T (((pr d R).hom.app n).app T b) := by rw [hc]
      _ = (((pr d R).hom ≫ (prod.fst : PR (d + 1) 0 R ⟶ _)).app n).app T b := rfl
      _ = ((prod.fst ≫ Pj.incl (d + 1)).app n).app T b := by rw [e2]; rfl
  have h2 : ((chn (xa x)).obj i).1 = (Vec.incl (d + 1) T.unop).obj (c1.obj i) :=
    congrArg (fun K : ComposableArrows (Vec (d + 1) 0 T.unop) n.unop.len => K.obj i) key
  have hv : ((chn (xa x)).obj i).1.1 = (c1.obj i).1 := congrArg Subtype.val h2
  obtain ⟨j, hj, hp⟩ := (c1.obj i).2 p
  exact ⟨j, hj, by rw [hv]; exact hp⟩

/- English proof (translation)
Rewrite using `[mem_off _ p MvPolynomial.X I hI]`. Take `⟨j, hj, hp⟩` from `tail_of_X x 0 p`. Take `⟨k, rfl⟩` from `Fin.exists_succ_eq.2 (show j ≠ 0 by rintro rfl; simp at hj)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hu : p ∈ T.unop.basicOpen ((((unit0 ((chn (xa x)).obj 0))⁻¹ : (Γ(T.unop, ⊤))ˣ) : Γ(T.unop, ⊤)))`.

Rewrite using `[Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]`. Discharge the goal by the elementary cases of `trivial`. Rewrite using `[ptW, ringOf_ptOf, ringA, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, ratio, Scheme.basicOpen_mul]`. Conclude with `⟨hp, hu⟩`.
-/
theorem ptW_mem (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I)
    {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj n).obj T) (p : T.unop) :
    ptW (xa x) p ∈ off (MvPolynomial (Fin d) R) I := by
  rw [mem_off _ p MvPolynomial.X I hI]
  obtain ⟨j, hj, hp⟩ := tail_of_X x 0 p
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 (show j ≠ 0 by rintro rfl; simp at hj)
  refine ⟨k, ?_⟩
  have hu : p ∈ T.unop.basicOpen ((((unit0 ((chn (xa x)).obj 0))⁻¹ : (Γ(T.unop, ⊤))ˣ) : Γ(T.unop, ⊤))) := by
    rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]; trivial
  rw [ptW, ringOf_ptOf, ringA, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, ratio, Scheme.basicOpen_mul]
  exact ⟨hp, hu⟩

def rX (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I) :
    Xs d R ⟶ sch.obj (Uo d R I) :=
  liftOpen (off (MvPolynomial (Fin d) R) I) (pullback.fst (wb d R) (pr d R).hom ≫ rW d R)
    fun _ _ x p => ptW_mem I hI x p

/- English proof (translation)
The claim follows from `liftOpen_comp _ _ _`.
-/
theorem rX_comp (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I) :
    rX I hI ≫ sch.map (off (MvPolynomial (Fin d) R) I).ι = pullback.fst (wb d R) (pr d R).hom ≫ rW d R :=
  liftOpen_comp _ _ _

/- English proof (translation)
The claim follows from `lif_ι (off (MvPolynomial (Fin d) R) I) (evS (pullback.fst (wb d R) (pr d R).hom ≫ rW d R) n T x) (fun p => ptW_mem I hI x p)`.
-/
theorem rX_ι (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I)
    {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj n).obj T) :
    evS (rX I hI) n T x ≫ (off (MvPolynomial (Fin d) R) I).ι = ptW (xa x) :=
  lif_ι (off (MvPolynomial (Fin d) R) I) (evS (pullback.fst (wb d R) (pr d R).hom ≫ rW d R) n T x)
    (fun p => ptW_mem I hI x p)

def tPt {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) : T.unop ⟶ Gm :=
  ptOf (ringG (unit0 ((chn a).obj 0)))

/- English proof (translation)
Rewrite using `[tPt, tPt, comp_ptOf, chn_mapT, ← ringG_map]`. Both sides reduce to the same expression.
-/
theorem tPt_mapT {n : SimplexCategoryᵒᵖ} {T T' : Scheme.{0}ᵒᵖ} (t : T ⟶ T') (a : ((W d R).obj n).obj T) :
    tPt (((W d R).obj n).map t a) = t.unop ≫ tPt a := by
  rw [tPt, tPt, comp_ptOf, chn_mapT, ← ringG_map]
  rfl

def gX (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I) :
    (Xs d R).obj (op (SimplexCategory.mk 0)) ⟶ yoneda.obj (Uo d R I ⨯ Gm) where
  app T := TypeCat.ofHom fun x => prod.lift (evS (rX I hI) _ T x) (tPt (xa x))
  naturality T T' t := by
    ext x
    change prod.lift (evS (rX I hI) _ T' (((Xs d R).obj _).map t x)) (tPt (xa (((Xs d R).obj _).map t x))) =
      t.unop ≫ prod.lift (evS (rX I hI) _ T x) (tPt (xa x))
    rw [prod.comp_lift, xa_mapT, tPt_mapT]
    congr 1
    exact simplicial_presheaf_hom_scheme_naturality_apply (rX I hI) _ t x

/- English proof (translation)
Use extensionality with `T x`. Conclude with `prod.lift_fst _ _`.
-/
theorem gX_fst (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I) :
    gX I hI ≫ yoneda.map (gmU d R I) = (rX I hI).app (op (SimplexCategory.mk 0)) := by
  ext T x
  exact prod.lift_fst _ _

/- English proof (translation)
Establish `: (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (h ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ h.appTop`. Rewrite using `[Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]`. Rewrite using `[ringOf, this]`. Both sides reduce to the same expression.
-/
theorem ringOf_specMap {A B : Type} [CommRing A] [CommRing B] {U : Scheme.{0}} (h : U ⟶ Spec (CommRingCat.of B))
    (φ : A →+* B) : ringOf (h ≫ Spec.map (CommRingCat.ofHom φ)) = (ringOf h).comp φ := by
  have : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (h ≫ Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ h.appTop := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rw [ringOf, this]; rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) 0) = 1`. Rewrite using `[Fin.cons_zero, map_one]`.
-/
theorem weighted_vector_leading_one_unit_eq_one {A : Type} [CommRing A] (x : Fin d → A) : unit0 (wvec1 x) = 1 := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) 0) = 1
  rw [Fin.cons_zero, map_one]

/- English proof (translation)
Rewrite using `[ratio, weighted_vector_leading_one_unit_eq_one, inv_one, Units.val_one, mul_one]`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) k.succ) = _`. Rewrite using `[Fin.cons_succ]`.
-/
theorem ratio_wvec1 {A : Type} [CommRing A] (x : Fin d → A) (k : Fin d) :
    ratio (wvec1 x) k = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (x k) := by
  rw [ratio, weighted_vector_leading_one_unit_eq_one, inv_one, Units.val_one, mul_one]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) k.succ) = _
  rw [Fin.cons_succ]

/- English proof (translation)
Use extensionality with `n T f`. Establish `h1 : chn ((((wa d R).app n).app T) f) = (((Wpt (wvec1 MvPolynomial.X)).app n).app T f)`. Express the relevant statement in the definitionally equal form `((wa d R ≫ prod.fst).app n).app T f = _`. Rewrite using `[wa, prod.lift_fst]`. Establish `h2 : bas ((((wa d R).app n).app T) f) = ((spMap (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)).app n).app T f`.

Express the relevant statement in the definitionally equal form `((wa d R ≫ prod.snd).app n).app T f = _`. Rewrite using `[wa, prod.lift_snd]`. Express the relevant statement in the definitionally equal form `ptW (((wa d R).app n).app T f) = f`. Rewrite using `[ptW, h1, h2]`. Express the relevant statement in the definitionally equal form `ptOf (ringA (f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) ((WVec.map d f).obj (wvec1 MvPolynomial.X))) = f`.

Establish `key : ∀ f' : T.unop ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)), ringA (f' ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) ((WVec.map d f').obj (wvec1 MvPolynomial.X)) = ringOf f'`. Introduce `f'`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[ringA, ringOf_specMap]`.

Introduce `k`. Simplify using `only [ringA, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, ratio_map, ratio_wvec1]`. Both sides reduce to the same expression. Rewrite using `[key f]`. Conclude with `ptOf_ringOf f`.
-/
theorem wa_rW : wa d R ≫ rW d R = 𝟙 _ := by
  ext n T f
  have h1 : chn ((((wa d R).app n).app T) f) = (((Wpt (wvec1 MvPolynomial.X)).app n).app T f) := by
    change ((wa d R ≫ prod.fst).app n).app T f = _
    rw [wa, prod.lift_fst]
  have h2 : bas ((((wa d R).app n).app T) f) = ((spMap (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)).app n).app T f := by
    change ((wa d R ≫ prod.snd).app n).app T f = _
    rw [wa, prod.lift_snd]
  change ptW (((wa d R).app n).app T f) = f
  rw [ptW, h1, h2]
  change ptOf (ringA (f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)))
    ((WVec.map d f).obj (wvec1 MvPolynomial.X))) = f
  have key : ∀ f' : T.unop ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)),
      ringA (f' ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)))
        ((WVec.map d f').obj (wvec1 MvPolynomial.X)) = ringOf f' := by
    intro f'
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ringA, ringOf_specMap]
    · intro k
      simp only [ringA, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, ratio_map, ratio_wvec1]
      rfl
  rw [key f]
  exact ptOf_ringOf f

abbrev evF (n : SimplexCategoryᵒᵖ) (T : Scheme.{0}ᵒᵖ) : Spc ⥤ Type :=
  (evaluation _ _).obj n ⋙ (evaluation _ _).obj T

/- English proof (translation)
Establish `hl` using `mapIsLimitOfPreservesOfIsLimit (evF n T) (prod.fst : A ⨯ B ⟶ A) prod.snd (prodIsProd A B)`. Set `f1 : PUnit ⟶ (evF n T).obj (A ⨯ B)` to `TypeCat.ofHom fun _ => w`. Set `f2 : PUnit ⟶ (evF n T).obj (A ⨯ B)` to `TypeCat.ofHom fun _ => w'`. Establish `: f1 = f2` using `BinaryFan.IsLimit.hom_ext hl (by ext _; exact h1) (by ext _; exact h2)`. Conclude with `ConcreteCategory.congr_hom this PUnit.unit`.
-/
theorem prod_ext {A B : Spc} {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} {w w' : ((A ⨯ B).obj n).obj T}
    (h1 : ((prod.fst : A ⨯ B ⟶ A).app n).app T w = ((prod.fst : A ⨯ B ⟶ A).app n).app T w')
    (h2 : ((prod.snd : A ⨯ B ⟶ B).app n).app T w = ((prod.snd : A ⨯ B ⟶ B).app n).app T w') : w = w' := by
  have hl := mapIsLimitOfPreservesOfIsLimit (evF n T) (prod.fst : A ⨯ B ⟶ A) prod.snd (prodIsProd A B)
  let f1 : PUnit ⟶ (evF n T).obj (A ⨯ B) := TypeCat.ofHom fun _ => w
  let f2 : PUnit ⟶ (evF n T).obj (A ⨯ B) := TypeCat.ofHom fun _ => w'
  have : f1 = f2 := BinaryFan.IsLimit.hom_ext hl (by ext _; exact h1) (by ext _; exact h2)
  exact ConcreteCategory.congr_hom this PUnit.unit

/- English proof (translation)
Establish `hl` using `mapIsLimitOfPreservesOfIsLimit (evF n T) (prod.fst : A ⨯ B ⟶ A) prod.snd (prodIsProd A B)`. Take `⟨l, h1, h2⟩` from `BinaryFan.IsLimit.lift' hl (W := PUnit) (TypeCat.ofHom fun _ => a) (TypeCat.ofHom fun _ => b)`. Conclude with `⟨l PUnit.unit, ConcreteCategory.congr_hom h1 PUnit.unit, ConcreteCategory.congr_hom h2 PUnit.unit⟩`.
-/
theorem prod_mk {A B : Spc} {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : (A.obj n).obj T) (b : (B.obj n).obj T) :
    ∃ w : ((A ⨯ B).obj n).obj T, ((prod.fst : A ⨯ B ⟶ A).app n).app T w = a ∧
      ((prod.snd : A ⨯ B ⟶ B).app n).app T w = b := by
  have hl := mapIsLimitOfPreservesOfIsLimit (evF n T) (prod.fst : A ⨯ B ⟶ A) prod.snd (prodIsProd A B)
  obtain ⟨l, h1, h2⟩ := BinaryFan.IsLimit.lift' hl (W := PUnit) (TypeCat.ofHom fun _ => a) (TypeCat.ofHom fun _ => b)
  exact ⟨l PUnit.unit, ConcreteCategory.congr_hom h1 PUnit.unit, ConcreteCategory.congr_hom h2 PUnit.unit⟩

/- English proof (translation)
Establish `hp` using `(IsPullback.of_hasPullback f g).map (evF n T)`. Use `⟨hp.lift (TypeCat.ofHom fun _ : PUnit => a) (TypeCat.ofHom fun _ => b) (by ext _; exact h) PUnit.unit, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ConcreteCategory.congr_hom (hp.lift_fst _ _ _) PUnit.unit`. Conclude with `ConcreteCategory.congr_hom (hp.lift_snd _ _ _) PUnit.unit`.
-/
theorem pb_mk {A B C : Spc} (f : A ⟶ C) (g : B ⟶ C) {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ}
    (a : (A.obj n).obj T) (b : (B.obj n).obj T) (h : (f.app n).app T a = (g.app n).app T b) :
    ∃ x : ((pullback f g).obj n).obj T, ((pullback.fst f g).app n).app T x = a ∧
      ((pullback.snd f g).app n).app T x = b := by
  have hp := (IsPullback.of_hasPullback f g).map (evF n T)
  refine ⟨hp.lift (TypeCat.ofHom fun _ : PUnit => a) (TypeCat.ofHom fun _ => b) (by ext _; exact h) PUnit.unit, ?_, ?_⟩
  · exact ConcreteCategory.congr_hom (hp.lift_fst _ _ _) PUnit.unit
  · exact ConcreteCategory.congr_hom (hp.lift_snd _ _ _) PUnit.unit

/- English proof (translation)
The claim follows from `prod_ext h1 h2`.
-/
theorem W_ext {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} {a a' : ((W d R).obj n).obj T}
    (h1 : chn a = chn a') (h2 : bas a = bas a') : a = a' := prod_ext h1 h2

/- English proof (translation)
Establish `h1 : Mono (pullback.fst (wb d R) (pr d R).hom)` using `(IsPullback.of_hasPullback (wb d R) (pr d R).hom).mono_fst_of_mono hm`. Establish `h2` using `(NatTrans.mono_iff_mono_app _).1 h1 n`. Establish `h3` using `(NatTrans.mono_iff_mono_app _).1 h2 T`. Conclude with `(mono_iff_injective _).1 h3 h`.
-/
theorem xa_inj (hm : Mono (pr d R).hom) {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} {x x' : ((Xs d R).obj n).obj T}
    (h : xa x = xa x') : x = x' := by
  have h1 : Mono (pullback.fst (wb d R) (pr d R).hom) := (IsPullback.of_hasPullback (wb d R) (pr d R).hom).mono_fst_of_mono hm
  have h2 := (NatTrans.mono_iff_mono_app _).1 h1 n
  have h3 := (NatTrans.mono_iff_mono_app _).1 h2 T
  exact (mono_iff_injective _).1 h3 h

def wv {U : Scheme.{0}} (τ : (Γ(U, ⊤))ˣ) (x : Fin d → Γ(U, ⊤)) : WVec d U :=
  ⟨⟨Fin.cons (τ : Γ(U, ⊤)) (fun k => (τ : Γ(U, ⊤)) * x k), fun p => ⟨0, Nat.zero_le _, by
    rw [Fin.cons_zero, Scheme.basicOpen_of_isUnit _ τ.isUnit]; trivial⟩⟩, by
    change IsUnit ((Fin.cons (τ : Γ(U, ⊤)) (fun k => (τ : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) 0)
    rw [Fin.cons_zero]; exact τ.isUnit⟩

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(Fin.cons (τ : Γ(U, ⊤)) (fun k => (τ : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) 0 = _`. Rewrite using `[Fin.cons_zero]`.
-/
theorem weighted_vector_of_unit_leading_unit_eq {U : Scheme.{0}} (τ : (Γ(U, ⊤))ˣ) (x : Fin d → Γ(U, ⊤)) : unit0 (wv τ x) = τ := by
  apply Units.ext
  change (Fin.cons (τ : Γ(U, ⊤)) (fun k => (τ : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) 0 = _
  rw [Fin.cons_zero]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[ratio, weighted_vector_of_unit_leading_unit_eq]`. Express the relevant statement in the definitionally equal form `(Fin.cons (τ : Γ(U, ⊤)) (fun k => (τ : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) k.succ * _ = _`. Rewrite using `[Fin.cons_succ, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]`.
-/
theorem ratio_wv {U : Scheme.{0}} (τ : (Γ(U, ⊤))ˣ) (x : Fin d → Γ(U, ⊤)) : ratio (wv τ x) = x := by
  funext k
  rw [ratio, weighted_vector_of_unit_leading_unit_eq]
  change (Fin.cons (τ : Γ(U, ⊤)) (fun k => (τ : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) k.succ * _ = _
  rw [Fin.cons_succ, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def chainW {U : Scheme.{0}} {m : ℕ} (τ : Fin (m + 1) → (Γ(U, ⊤))ˣ) (x : Fin d → Γ(U, ⊤)) :
    ComposableArrows (WVec d U) m where
  obj i := wv (τ i) x
  map {i j} _ := ⟨τ i * (τ j)⁻¹, fun l => by
    refine Fin.cases ?_ (fun k => ?_) l
    · change (Fin.cons (τ i : Γ(U, ⊤)) (fun k => (τ i : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) 0 =
        ((τ i * (τ j)⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) *
          (Fin.cons (τ j : Γ(U, ⊤)) (fun k => (τ j : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) 0
      rw [Fin.cons_zero, Fin.cons_zero, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    · change (Fin.cons (τ i : Γ(U, ⊤)) (fun k => (τ i : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) k.succ =
        ((τ i * (τ j)⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) *
          (Fin.cons (τ j : Γ(U, ⊤)) (fun k => (τ j : Γ(U, ⊤)) * x k) : Fin (d + 1) → Γ(U, ⊤)) k.succ
      rw [Fin.cons_succ, Fin.cons_succ, Units.val_mul, mul_assoc, ← mul_assoc _ (τ j : Γ(U, ⊤)), Units.inv_mul, one_mul]⟩
  map_id _ := wvec_hom_sub _ _
  map_comp _ _ := wvec_hom_sub _ _

def chainL {U : Scheme.{0}} {m : ℕ} (c : ComposableArrows (WVec d U) m)
    (h : ∀ i (p : U), ∃ j : Fin (d + 1), 1 ≤ j.val ∧ p ∈ U.basicOpen ((c.obj i).1.1 j)) :
    ComposableArrows (Vec (d + 1) 1 U) m where
  obj i := ⟨(c.obj i).1.1, h i⟩
  map f := c.map f
  map_id i := c.map_id i
  map_comp f g := c.map_comp f g

def unitOf {U : Scheme.{0}} (q : U ⟶ Gm) : (Γ(U, ⊤))ˣ :=
  Units.map (ringOf q : LaurentPolynomial ℤ →* Γ(U, ⊤)) (LaurentPolynomial.isUnit_T 1).unit

/- English proof (translation)
Apply `point_ext` to reduce the goal to its premises. Rewrite using `[ringOf_ptOf]`. Use extensionality with `x`. Simplify using `[ringG]`. Express the relevant statement in the definitionally equal form `ringG (unitOf q) (LaurentPolynomial.T 1) = ringOf q (LaurentPolynomial.T 1)`.

Simplify using `[ringG, unitOf]`.
-/
theorem ptOf_unitOf {U : Scheme.{0}} (q : U ⟶ Gm) : ptOf (ringG (unitOf q)) = q := by
  apply point_ext
  rw [ringOf_ptOf]
  ext x
  · simp [ringG]
  · change ringG (unitOf q) (LaurentPolynomial.T 1) = ringOf q (LaurentPolynomial.T 1)
    simp [ringG, unitOf]

/- English proof (translation)
The claim follows from `nat_N (rX I hI) (vtx n i).op T x`.
-/
theorem rX_vtx (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I)
    {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj (op (SimplexCategory.mk n))).obj T) (i : Fin (n + 1)) :
    evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x) = evS (rX I hI) _ T x :=
  nat_N (rX I hI) (vtx n i).op T x

/- English proof (translation)
Rewrite using `[tPt, xa_mapN, chn_mapN]`. Both sides reduce to the same expression.
-/
theorem tPt_vtx {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : ((Xs d R).obj (op (SimplexCategory.mk n))).obj T) (i : Fin (n + 1)) :
    tPt (xa (((Xs d R).map (vtx n i).op).app T x)) = ptOf (ringG (unit0 ((chn (xa x)).obj i))) := by
  rw [tPt, xa_mapN, chn_mapN]
  rfl

/- English proof (translation)
Establish `hl : ∀ i, (prod.lift (evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x)) (tPt (xa (((Xs d R).map (vtx n i).op).app T x))) : T.unop ⟶ Uo d R I ⨯ Gm) = prod.lift (evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x')) (tPt (xa (((Xs d R).map (vtx n i).op).app T x')))` using `h`. Establish `hr : ∀ i, evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x) = evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x')` using `fun i => (prod.lift_fst _ _).symm.trans ((congrArg (· ≫ (prod.fst : Uo d R I ⨯ Gm ⟶ _)) (hl i)).trans (prod.lift_fst _ _))`. Establish `ht : ∀ i, tPt (xa (((Xs d R).map (vtx n i).op).app T x)) = tPt (xa (((Xs d R).map (vtx n i).op).app T x'))` using `fun i => (prod.lift_snd _ _).symm.trans ((congrArg (· ≫ (prod.snd : Uo d R I ⨯ Gm ⟶ _)) (hl i)).trans (prod.lift_snd _ _))`. Establish `h0 : evS (rX I hI) _ T x = evS (rX I hI) _ T x'`. Use `hr 0` as an intermediate fact.

Rewrite `this` using `[rX_vtx, rX_vtx]`. Then use the resulting hypothesis. Establish `hp : ptW (xa x) = ptW (xa x')` using `by rw [← rX_ι I hI, ← rX_ι I hI, h0]`. Establish `hring : ringA (bas (xa x)) ((chn (xa x)).obj 0) = ringA (bas (xa x')) ((chn (xa x')).obj 0)`. Use `congrArg ringOf hp` as an intermediate fact. Rewrite `this` using `[ptW, ptW, ringOf_ptOf, ringOf_ptOf]`. Then use the resulting hypothesis.

Establish `hb : bas (xa x) = bas (xa x')`. Apply `point_ext` to reduce the goal to its premises. Use extensionality with `r`. Use `congrArg (fun F => F (MvPolynomial.C r)) hring` as an intermediate fact. Simplify `this` using `[ringA]`.

Establish `hratio : ratio ((chn (xa x)).obj 0) = ratio ((chn (xa x')).obj 0)`. Use function extensionality and compare the values at `k`. Use `congrArg (fun F => F (MvPolynomial.X k)) hring` as an intermediate fact. Simplify `this` using `[ringA]`. Establish `hobj : ∀ i, (chn (xa x)).obj i = (chn (xa x')).obj i` using `fun i => by`.

Apply `wvec_ext` to reduce the goal to its premises. Apply `ringG_inj` to reduce the goal to its premises. Use `ht i` as an intermediate fact. Rewrite `this` using `[tPt_vtx, tPt_vtx]`. Use `congrArg ringOf this` as an intermediate fact.

Rewrite `this` using `[ringOf_ptOf, ringOf_ptOf]`. Then use the resulting hypothesis. Rewrite using `[ratio_chain _ i 0, ratio_chain _ i 0, hratio]`. Apply `xa_inj hm` to reduce the goal to its premises. Apply `W_ext _ hb` to reduce the goal to its premises. Conclude with `CategoryTheory.Functor.ext hobj (fun _ _ _ => wvec_hom_sub _ _)`.
-/
theorem gX_inj (hm : Mono (pr d R).hom) (I : Ideal (MvPolynomial (Fin d) R))
    (hI : Ideal.span (Set.range MvPolynomial.X) = I) (n : ℕ) (T : Scheme.{0}ᵒᵖ)
    (x x' : ((Xs d R).obj (op (SimplexCategory.mk n))).obj T)
    (h : ∀ i, (gX I hI).app T (((Xs d R).map (vtx n i).op).app T x) =
      (gX I hI).app T (((Xs d R).map (vtx n i).op).app T x')) : x = x' := by
  have hl : ∀ i, (prod.lift (evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x))
        (tPt (xa (((Xs d R).map (vtx n i).op).app T x))) : T.unop ⟶ Uo d R I ⨯ Gm) =
      prod.lift (evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x'))
        (tPt (xa (((Xs d R).map (vtx n i).op).app T x'))) := h
  have hr : ∀ i, evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x) =
      evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x') := fun i =>
    (prod.lift_fst _ _).symm.trans ((congrArg (· ≫ (prod.fst : Uo d R I ⨯ Gm ⟶ _)) (hl i)).trans (prod.lift_fst _ _))
  have ht : ∀ i, tPt (xa (((Xs d R).map (vtx n i).op).app T x)) =
      tPt (xa (((Xs d R).map (vtx n i).op).app T x')) := fun i =>
    (prod.lift_snd _ _).symm.trans ((congrArg (· ≫ (prod.snd : Uo d R I ⨯ Gm ⟶ _)) (hl i)).trans (prod.lift_snd _ _))
  have h0 : evS (rX I hI) _ T x = evS (rX I hI) _ T x' := by
    have := hr 0
    rwa [rX_vtx, rX_vtx] at this
  have hp : ptW (xa x) = ptW (xa x') := by rw [← rX_ι I hI, ← rX_ι I hI, h0]
  have hring : ringA (bas (xa x)) ((chn (xa x)).obj 0) = ringA (bas (xa x')) ((chn (xa x')).obj 0) := by
    have := congrArg ringOf hp
    rwa [ptW, ptW, ringOf_ptOf, ringOf_ptOf] at this
  have hb : bas (xa x) = bas (xa x') := by
    apply point_ext
    ext r
    have := congrArg (fun F => F (MvPolynomial.C r)) hring
    simpa [ringA] using this
  have hratio : ratio ((chn (xa x)).obj 0) = ratio ((chn (xa x')).obj 0) := by
    funext k
    have := congrArg (fun F => F (MvPolynomial.X k)) hring
    simpa [ringA] using this
  have hobj : ∀ i, (chn (xa x)).obj i = (chn (xa x')).obj i := fun i => by
    apply wvec_ext
    · apply ringG_inj
      have := ht i
      rw [tPt_vtx, tPt_vtx] at this
      have := congrArg ringOf this
      rwa [ringOf_ptOf, ringOf_ptOf] at this
    · rw [ratio_chain _ i 0, ratio_chain _ i 0, hratio]
  apply xa_inj hm
  apply W_ext _ hb
  exact CategoryTheory.Functor.ext hobj (fun _ _ _ => wvec_hom_sub _ _)

/- English proof (translation)
Establish `e1 : wb d R ≫ prod.fst = prod.fst ≫ Wincl d` using `prod.map_fst _ _`. Conclude with `ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e1 n) T) a`.
-/
theorem wb_fst {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app T (((wb d R).app n).app T a) = ((Wincl d).app n).app T (chn a) := by
  have e1 : wb d R ≫ prod.fst = prod.fst ≫ Wincl d := prod.map_fst _ _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e1 n) T) a

/- English proof (translation)
Establish `e1 : wb d R ≫ prod.snd = prod.snd ≫ 𝟙 _` using `prod.map_snd _ _`. Rewrite `e1` using `[Category.comp_id]`. Conclude with `ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e1 n) T) a`.
-/
theorem wb_snd {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (a : ((W d R).obj n).obj T) :
    ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app T (((wb d R).app n).app T a) = bas a := by
  have e1 : wb d R ≫ prod.snd = prod.snd ≫ 𝟙 _ := prod.map_snd _ _
  rw [Category.comp_id] at e1
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e1 n) T) a

/- English proof (translation)
Establish `e2 : (pr d R).hom ≫ (prod.fst : PR (d + 1) 0 R ⟶ _) = prod.fst ≫ Pj.incl (d + 1)` using `prod.map_fst _ _`. Conclude with `ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e2 n) T) b`.
-/
theorem prh_fst {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (b : ((PR (d + 1) 1 R).obj n).obj T) :
    ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app T (((pr d R).hom.app n).app T b) =
      ((Pj.incl (d + 1)).app n).app T (((prod.fst : PR (d + 1) 1 R ⟶ Pj (d + 1) 1).app n).app T b) := by
  have e2 : (pr d R).hom ≫ (prod.fst : PR (d + 1) 0 R ⟶ _) = prod.fst ≫ Pj.incl (d + 1) := prod.map_fst _ _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e2 n) T) b

/- English proof (translation)
Establish `e2 : (pr d R).hom ≫ (prod.snd : PR (d + 1) 0 R ⟶ _) = prod.snd ≫ 𝟙 _` using `prod.map_snd _ _`. Rewrite `e2` using `[Category.comp_id]`. Conclude with `ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e2 n) T) b`.
-/
theorem prh_snd {n : SimplexCategoryᵒᵖ} {T : Scheme.{0}ᵒᵖ} (b : ((PR (d + 1) 1 R).obj n).obj T) :
    ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app T (((pr d R).hom.app n).app T b) =
      ((prod.snd : PR (d + 1) 1 R ⟶ sp R).app n).app T b := by
  have e2 : (pr d R).hom ≫ (prod.snd : PR (d + 1) 0 R ⟶ _) = prod.snd ≫ 𝟙 _ := prod.map_snd _ _
  rw [Category.comp_id] at e2
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app e2 n) T) b

/- English proof (translation)
Set `V : Scheme.{0}` to `T.unop`. Set `h : V ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R))` to `(show V ⟶ Uo d R I from z) ≫ (off _ I).ι`. Set `E` to `ringOf h`. Set `s : V ⟶ Spec (CommRingCat.of R)` to `h ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))`. Set `xs : Fin d → Γ(V, ⊤)` to `fun k => E (MvPolynomial.X k)`.

Set `τ : Fin (n + 1) → (Γ(V, ⊤))ˣ` to `fun i => unitOf ((show V ⟶ Uo d R I ⨯ Gm from y i) ≫ prod.snd)`. Set `c : ComposableArrows (WVec d V) n` to `chainW τ xs`. Establish `hE : ringA s ((c.obj 0)) = E`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[ringA, s, ringOf_specMap, E]`. Introduce `k`. Establish `: ratio (c.obj 0) = xs` using `ratio_wv _ _`. Simplify using `[ringA, this, xs]`. Establish `htail : ∀ i (p : V), ∃ j : Fin (d + 1), 1 ≤ j.val ∧ p ∈ V.basicOpen ((c.obj i).1.1 j)`.

Introduce `i p`. Establish `hp : h p ∈ off (MvPolynomial (Fin d) R) I`. Establish `e : h p = (off (MvPolynomial (Fin d) R) I).ι ((show V ⟶ Uo d R I from z) p)` using `rfl`. Rewrite using `[e]`. Use `Set.mem_range_self (f := (off (MvPolynomial (Fin d) R) I).ι) ((show V ⟶ Uo d R I from z) p)` as an intermediate fact.

Rewrite `this` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Take `⟨k, hk⟩` from `(mem_off h p MvPolynomial.X I hI).1 hp`. Use `⟨k.succ, by simp, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p ∈ V.basicOpen ((Fin.cons (τ i : Γ(V, ⊤)) (fun k => (τ i : Γ(V, ⊤)) * xs k) : Fin (d + 1) → Γ(V, ⊤)) k.succ)`. Rewrite using `[Fin.cons_succ, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (τ i).isUnit]`.

Conclude with `⟨trivial, hk⟩`. Set `c1 : ComposableArrows (Vec (d + 1) 1 V) n` to `chainL c htail`. Take `⟨a, ha1, ha2⟩` from `prod_mk (A := Wsp d) (B := sp R) (n := op (SimplexCategory.mk n)) (T := T) c s`. Take `⟨b, hb1, hb2⟩` from `prod_mk (A := Pj (d + 1) 1) (B := sp R) (n := op (SimplexCategory.mk n)) (T := T) c1 s`. Establish `hca : chn a = c` using `ha1`.

Establish `hsa : bas a = s` using `ha2`. Establish `hcond : ((wb d R).app (op (SimplexCategory.mk n))).app T a = ((pr d R).hom.app (op (SimplexCategory.mk n))).app T b`. Apply `prod_ext` to reduce the goal to its premises. Rewrite using `[wb_fst, prh_fst, hca, hb1]`. Both sides reduce to the same expression.

Rewrite using `[wb_snd, prh_snd, hsa, hb2]`. Take `⟨x, hx1, -⟩` from `pb_mk (wb d R) (pr d R).hom a b hcond`. Establish `hxa : xa x = a` using `hx1`. Use `⟨x, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(prod.lift (evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x)) (tPt (xa (((Xs d R).map (vtx n i).op).app T x))) : V ⟶ Uo d R I ⨯ Gm) = y i`.

Apply `prod.hom_ext` to reduce the goal to its premises. Rewrite using `[prod.lift_fst, rX_vtx]`. Establish `hz : (show V ⟶ Uo d R I ⨯ Gm from y i) ≫ prod.fst = z` using `hy i`. Rewrite using `[hz]`. Use `(cancel_mono (off (MvPolynomial (Fin d) R) I).ι).1 ?_` and prove the remaining obligations.

Rewrite using `[rX_ι, hxa, ptW, hsa, hca, hE]`. Conclude with `ptOf_ringOf h`. Rewrite using `[prod.lift_snd, tPt_vtx, hxa, hca]`. Establish `: unit0 (c.obj i) = τ i` using `weighted_vector_of_unit_leading_unit_eq _ _`. Rewrite using `[this]`.

Conclude with `ptOf_unitOf _`.
-/
theorem gX_surj (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I)
    (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → (yoneda.obj (Uo d R I ⨯ Gm)).obj T)
    (z : (yoneda.obj (Uo d R I)).obj T) (hy : ∀ i, (yoneda.map (gmU d R I)).app T (y i) = z) :
    ∃ x : ((Xs d R).obj (op (SimplexCategory.mk n))).obj T,
      ∀ i, (gX I hI).app T (((Xs d R).map (vtx n i).op).app T x) = y i := by
  let V : Scheme.{0} := T.unop
  let h : V ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)) := (show V ⟶ Uo d R I from z) ≫ (off _ I).ι
  let E := ringOf h
  let s : V ⟶ Spec (CommRingCat.of R) :=
    h ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))
  let xs : Fin d → Γ(V, ⊤) := fun k => E (MvPolynomial.X k)
  let τ : Fin (n + 1) → (Γ(V, ⊤))ˣ := fun i => unitOf ((show V ⟶ Uo d R I ⨯ Gm from y i) ≫ prod.snd)
  let c : ComposableArrows (WVec d V) n := chainW τ xs
  have hE : ringA s ((c.obj 0)) = E := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ringA, s, ringOf_specMap, E]
    · intro k
      have : ratio (c.obj 0) = xs := ratio_wv _ _
      simp [ringA, this, xs]
  have htail : ∀ i (p : V), ∃ j : Fin (d + 1), 1 ≤ j.val ∧ p ∈ V.basicOpen ((c.obj i).1.1 j) := by
    intro i p
    have hp : h p ∈ off (MvPolynomial (Fin d) R) I := by
      have e : h p = (off (MvPolynomial (Fin d) R) I).ι ((show V ⟶ Uo d R I from z) p) := rfl
      rw [e]
      have := Set.mem_range_self (f := (off (MvPolynomial (Fin d) R) I).ι) ((show V ⟶ Uo d R I from z) p)
      rwa [Scheme.Opens.range_ι] at this
    obtain ⟨k, hk⟩ := (mem_off h p MvPolynomial.X I hI).1 hp
    refine ⟨k.succ, by simp, ?_⟩
    change p ∈ V.basicOpen ((Fin.cons (τ i : Γ(V, ⊤)) (fun k => (τ i : Γ(V, ⊤)) * xs k) : Fin (d + 1) → Γ(V, ⊤)) k.succ)
    rw [Fin.cons_succ, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (τ i).isUnit]
    exact ⟨trivial, hk⟩
  let c1 : ComposableArrows (Vec (d + 1) 1 V) n := chainL c htail
  obtain ⟨a, ha1, ha2⟩ := prod_mk (A := Wsp d) (B := sp R) (n := op (SimplexCategory.mk n)) (T := T) c s
  obtain ⟨b, hb1, hb2⟩ := prod_mk (A := Pj (d + 1) 1) (B := sp R) (n := op (SimplexCategory.mk n)) (T := T) c1 s
  have hca : chn a = c := ha1
  have hsa : bas a = s := ha2
  have hcond : ((wb d R).app (op (SimplexCategory.mk n))).app T a =
      ((pr d R).hom.app (op (SimplexCategory.mk n))).app T b := by
    apply prod_ext
    · rw [wb_fst, prh_fst, hca, hb1]; rfl
    · rw [wb_snd, prh_snd, hsa, hb2]
  obtain ⟨x, hx1, -⟩ := pb_mk (wb d R) (pr d R).hom a b hcond
  have hxa : xa x = a := hx1
  refine ⟨x, fun i => ?_⟩
  change (prod.lift (evS (rX I hI) _ T (((Xs d R).map (vtx n i).op).app T x))
    (tPt (xa (((Xs d R).map (vtx n i).op).app T x))) : V ⟶ Uo d R I ⨯ Gm) = y i
  apply prod.hom_ext
  · rw [prod.lift_fst, rX_vtx]
    have hz : (show V ⟶ Uo d R I ⨯ Gm from y i) ≫ prod.fst = z := hy i
    rw [hz]
    refine (cancel_mono (off (MvPolynomial (Fin d) R) I).ι).1 ?_
    rw [rX_ι, hxa, ptW, hsa, hca, hE]
    exact ptOf_ringOf h
  · rw [prod.lift_snd, tPt_vtx, hxa, hca]
    have : unit0 (c.obj i) = τ i := weighted_vector_of_unit_leading_unit_eq _ _
    rw [this]
    exact ptOf_unitOf _

/- English proof (translation)
Use `(cancel_mono m).1 ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, h1, ← Category.assoc, h2, Category.assoc, h3, Category.comp_id, Category.id_comp]`.
-/
theorem abs_cancel {A B C D : Spc} (g : A ⟶ B) (r : B ⟶ A) (m : A ⟶ D) (f : B ⟶ C) (w : D ⟶ C) (q : C ⟶ D)
    (hm : Mono m) (h1 : r ≫ m = f ≫ q) (h2 : g ≫ f = m ≫ w) (h3 : w ≫ q = 𝟙 D) : g ≫ r = 𝟙 A := by
  refine (cancel_mono m).1 ?_
  rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc, h3, Category.comp_id, Category.id_comp]

/- English proof (translation)
The claim follows from `abs_cancel g (rX I hI) (sch.map (off (MvPolynomial (Fin d) R) I).ι) (pullback.fst (wb d R) (pr d R).hom) (wa d R) (rW d R) (opn_mono (off (MvPolynomial (Fin d) R) I)) (rX_comp I hI) hg wa_rW`.
-/
theorem sec_id (I : Ideal (MvPolynomial (Fin d) R)) (hI : Ideal.span (Set.range MvPolynomial.X) = I)
    (g : sch.obj (Uo d R I) ⟶ Xs d R)
    (hg : g ≫ pullback.fst (wb d R) (pr d R).hom = sch.map (off (MvPolynomial (Fin d) R) I).ι ≫ wa d R) :
    g ≫ rX I hI = 𝟙 _ :=
  abs_cancel g (rX I hI) (sch.map (off (MvPolynomial (Fin d) R) I).ι) (pullback.fst (wb d R) (pr d R).hom) (wa d R)
    (rW d R) (opn_mono (off (MvPolynomial (Fin d) R) I)) (rX_comp I hI) hg wa_rW

end WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence

/- English proof (translation)
Introduce `_ hG _ _ _ d R _ I hI`. Take `⟨ψ, hψ, he⟩` from `leafCechRec (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.Xs d R) _ _ (yoneda.map (gmU d R I)) (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.rX I hI) (WeightedBlowupChartPointUnits …`. Use `⟨@asIso _ _ _ _ ψ hψ, fun g hg => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g ≫ ψ ≫ (Arrow.mk (yoneda.map (gmU d R I))).augmentedCechNerve.hom = 𝟙 _`. Rewrite using `[he]`.

Conclude with `WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.sec_id I hI g hg`.
-/
theorem WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvR → LateralTheory.CohomologicalPurity.Thom.LeafGeo → LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.Thom.LeafExcSp → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWTors := by
  intro _ hG _ _ _ d R _ I hI
  obtain ⟨ψ, hψ, he⟩ := leafCechRec (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.Xs d R) _ _ (yoneda.map (gmU d R I))
    (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.rX I hI) (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.gX I hI) (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.gX_fst I hI)
    (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.gX_inj (hG.1 d R) I hI) (WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.gX_surj I hI)
  refine ⟨@asIso _ _ _ _ ψ hψ, fun g hg => ?_⟩
  change g ≫ ψ ≫ (Arrow.mk (yoneda.map (gmU d R I))).augmentedCechNerve.hom = 𝟙 _
  rw [he]
  exact WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence.sec_id I hI g hg
end
end
