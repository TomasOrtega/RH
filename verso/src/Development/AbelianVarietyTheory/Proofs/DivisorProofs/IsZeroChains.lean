import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R]

/- English proof (translation)
Apply `((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective` to reduce the goal to its premises. Use extensionality with `U : 2`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `x`. Conclude with `h U.unop x.down`.
-/
theorem free_ext {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G)
    (h : ∀ U x, Sec.map a (freeGen R P U x) = Sec.map b (freeGen R P U x)) : a = b := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down

/- English proof (translation)
Set `η : (freeP R).obj P ⟶ F.obj` to `{ app := fun U => ModuleCat.freeDesc (TypeCat.ofHom fun x => a U.unop x.down) naturality := fun U V g => by`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `x`. Express the relevant statement in the definitionally equal form `(ModuleCat.freeDesc _) ((ModuleCat.free _).map _ (ModuleCat.freeMk x)) = (F.obj.map g) ((ModuleCat.freeDesc _) (ModuleCat.freeMk x))`. Rewrite using `[ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]`.

Conclude with `(ha V.unop U.unop g.unop x.down).symm }`. Use `⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm η, fun U x => ?_⟩` and prove the remaining obligations. Establish `h` using `((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ F).apply_symm_apply η`. Establish `h2` using `ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h) (ModuleCat.freeMk (ULift.up x))`. Conclude with `h2.trans (ModuleCat.freeDesc_apply _ _)`.
-/
theorem free_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let η : (freeP R).obj P ⟶ F.obj :=
    { app := fun U => ModuleCat.freeDesc (TypeCat.ofHom fun x => a U.unop x.down)
      naturality := fun U V g => by
        apply ModuleCat.free_hom_ext
        intro x
        change (ModuleCat.freeDesc _) ((ModuleCat.free _).map _ (ModuleCat.freeMk x)) =
          (F.obj.map g) ((ModuleCat.freeDesc _) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        exact (ha V.unop U.unop g.unop x.down).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm η,
    fun U x => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ F).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h) (ModuleCat.freeMk (ULift.up x))
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

/- English proof (translation)
Establish `h` using `ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op) (ModuleCat.freeMk (ULift.up x))`. Use `h.symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom (ModuleCat.free_map_apply _ _)`.
-/
theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom (ModuleCat.free_map_apply _ _)

/- English proof (translation)
Establish `h` using `ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))) (ModuleCat.freeMk (ULift.up x))`. Use `h.symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.free_map_apply _ _)`.
-/
theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))) (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.free_map_apply _ _)

/- English proof (translation)
The claim follows from `(ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm`.
-/
theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

def mapHom (F G : Shv R) {U : Scheme.{0}} (x : Sec F U) : (F ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun φ => Sec.map φ x) (fun _ _ => rfl)

/- English proof (translation)
Use `HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-(i : ℤ) = p at hi`. Use linear arithmetic over natural numbers and integers.
-/
theorem isZero_chains (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => ?_)
  change -(i : ℤ) = p at hi
  omega

/- English proof (translation)
Establish `h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv` using `HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl`. Establish `h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)` using `AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p`. Rewrite using `[h1, Iso.inv_hom_id_assoc]`. Conclude with `congrArg (· ≫ (chainsXIso R E p).inv) h2`.
-/
theorem chains_d (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl
  have h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p
  rw [h1, Iso.inv_hom_id_assoc]
  exact congrArg (· ≫ (chainsXIso R E p).inv) h2

/- English proof (translation)
Establish `h1 : ((chains R).map f).f (-(p : ℤ)) = (chainsXIso R E p).hom ≫ ((chainsN R).map f).f p ≫ (chainsXIso R E' p).inv` using `HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) rfl`. Rewrite using `[h1, Iso.inv_hom_id_assoc]`. Both sides reduce to the same expression.
-/
theorem chains_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ ((chainsN R).map f).f p ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

variable {E : Spc} {I : Cx R} {n : ℤ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_def (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl

/- English proof (translation)
Use extensionality with `p s hs : 1`. Distinguish the cases in `hp : p ≤ 0`. Take `⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ)` from `⟨(-p).toNat, by omega⟩`. Rewrite using `[← cancel_epi (chainsXIso R E k).inv]`. Conclude with `free_ext _ _ (fun U x => h k s hs U x)`.

Conclude with `(isZero_chains E p (by omega)).eq_of_src _ _`.
-/
theorem ev_ext (α β : Cochain ((chains R).obj E) I n) (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  ext p s hs : 1
  by_cases hp : p ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    exact free_ext _ _ (fun U x => h k s hs U x)
  · exact (isZero_chains E p (by omega)).eq_of_src _ _

/- English proof (translation)
Establish `key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x, Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) = a p j (hp ▸ hij) U x`. Introduce `i j hij`. Distinguish the cases in `hi : i ≤ 0`. Take `⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ)` from `⟨(-i).toNat, by omega⟩`. Take `⟨φ, hφ⟩` from `free_exists (R := R) _ _ (a k j hij) (ha k j hij)`.

Use `⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩` and prove the remaining obligations. Take `rfl : k = p` from `by omega`. Rewrite using `[eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]`. Conclude with `hφ U x`. Conclude with `⟨0, fun p hp => by omega⟩`.

Use `choose φ hφ using key`. Use `⟨Cochain.mk φ, fun p s h U x => ?_⟩` and prove the remaining obligations. Use `hφ _ _ h p rfl U x` as an intermediate fact. Rewrite `this` using `[eqToHom_refl, Category.id_comp]`. Conclude with `this`.
-/
theorem ev_exists (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x := by
  have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
      Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
        a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using key
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

/- English proof (translation)
Rewrite using `[ev_def, map_res, freeGen_res]`. Both sides reduce to the same expression.
-/
theorem ev_res (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sx E p U) : Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  rw [ev_def, map_res, freeGen_res]
  rfl

/- English proof (translation)
Simplify using `[ev, Cochain.add_v]`.
-/
theorem ev_add (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
  simp [ev, Cochain.add_v]

def evHom (I : Cx R) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun a => ev a p s h U x) (fun a b => ev_add a b p s h U x)

/- English proof (translation)
The claim follows from `map_zero (evHom I n p s h U x)`.
-/
theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := map_zero (evHom I n p s h U x)

/- English proof (translation)
The claim follows from `map_zsmul (evHom I n p s h U x) c a`.
-/
theorem ev_zsmul (c : ℤ) (a : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • a) p s h U x = c • ev a p s h U x := map_zsmul (evHom I n p s h U x) c a

/- English proof (translation)
Rewrite using `[ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]`. Express the relevant statement in the definitionally equal form `Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _`. Rewrite using `[freeGen_map]`. Both sides reduce to the same expression.
-/
theorem ev_pull {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

/- English proof (translation)
Rewrite using `[ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp), (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]`. Both sides reduce to the same expression.
-/
theorem ev_δ_zero {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (s t : ℤ)
    (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
    ev (δ n m α) 0 t ht U x = Sec.map (I.d s t) (ev α 0 s hs U x) := by
  rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
    (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
  rfl

/- English proof (translation)
Rewrite using `[ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]`. Use `(map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_sum, Units.smul_def]`. Use `congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[Preadditive.zsmul_comp, map_zsmul]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _`. Rewrite using `[freeGen_map]`. Both sides reduce to the same expression.
-/
theorem ev_δ_succ {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
    Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
  refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
  rw [map_zsmul, map_sum, Units.smul_def]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [Preadditive.zsmul_comp, map_zsmul]
  congr 1
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

end GlobalTheory.EtC.CupSpec

end
