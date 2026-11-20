import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section NiCoh

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

/- English proof (translation)
Rewrite using `[← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]`.
-/
theorem ni_nat {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') {T T' : C} (φ : T ⟶ T') (x : F.obj T) :
    (β.app T').hom ((F.map φ).hom x) = (F'.map φ).hom ((β.app T).hom x) := by
  rw [← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]

/- English proof (translation)
Establish `hb : d F' n (fun s => (β.app _).hom (a s)) = 0` using `((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])`. Conclude with `⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩`.
-/
theorem ni_pull_cls {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (n : ℕ) (a : Cn F n) (ha : d F n a = 0) :
    ∃ hb, (Mor.ofNatTrans β).pull n ((cx F).cls a ha) = (cx F').cls (fun s => (β.app _).hom (a s)) hb := by
  have hb : d F' n (fun s => (β.app _).hom (a s)) = 0 :=
    ((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])
  exact ⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x`. Take `⟨h1, e1⟩` from `ni_pull_cls (β + β') n a ha`. Take `⟨h2, e2⟩` from `ni_pull_cls β n a ha`. Take `⟨h3, e3⟩` from `ni_pull_cls β' n a ha`. Rewrite using `[e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add, h2, h3, add_zero])]`.

Use `congr 1`.
-/
theorem ni_pull_add {F F' : C ⥤ ModuleCat.{w} R} (β β' : F ⟶ F') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β + β')).pull n x = (Mor.ofNatTrans β).pull n x + (Mor.ofNatTrans β').pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β + β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n a ha
  rw [e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add, h2, h3, add_zero])]
  congr 1

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x`. Take `⟨h1, e1⟩` from `ni_pull_cls (0 : F ⟶ F') n a ha`. Rewrite using `[e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]`. Establish `: (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n)`. Use function extensionality and compare the values at `s`.

Simplify using `only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.
-/
theorem ni_pull_zero {F F' : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (0 : F ⟶ F')).pull n x = 0 := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (0 : F ⟶ F') n a ha
  rw [e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]
  have : (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n) := by
    funext s
    simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
  rw [this]
  exact Submodule.zero_mem _

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]`. Consider the case `insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]`.
-/
theorem ni_pull_sum {ι : Type} {F F' : C ⥤ ModuleCat.{w} R} (β : ι → (F ⟶ F')) (S : Finset ι) (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (∑ k ∈ S, β k)).pull n x = ∑ k ∈ S, (Mor.ofNatTrans (β k)).pull n x := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]
  | insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x`. Take `⟨h1, e1⟩` from `ni_pull_cls (β ≫ β') n a ha`. Take `⟨h2, e2⟩` from `ni_pull_cls β n a ha`. Take `⟨h3, e3⟩` from `ni_pull_cls β' n _ h2`. Rewrite using `[e1, e2, e3]`.

Both sides reduce to the same expression.
-/
theorem ni_pull_comp {F F' F'' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (β' : F' ⟶ F'') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β ≫ β')).pull n x = (Mor.ofNatTrans β').pull n ((Mor.ofNatTrans β).pull n x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β ≫ β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n _ h2
  rw [e1, e2, e3]
  rfl

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x`. Take `⟨h1, e1⟩` from `ni_pull_cls (𝟙 F) n a ha`. Rewrite using `[e1]`. Both sides reduce to the same expression.
-/
theorem ni_pull_id {F : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (𝟙 F)).pull n x = x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (𝟙 F) n a ha
  rw [e1]
  rfl

def fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) : SubF F where
  S T := LinearMap.ker ((e.app T).hom - LinearMap.id)
  map_mem := fun {_ _} φ {_} hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [ni_nat, hx]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (T : C) (x : F.obj T) :
    x ∈ (fixF e).S T ↔ (e.app T).hom x = x := by
  change x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def fixP {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : F ⟶ (fixF e).fn where
  app T := ModuleCat.ofHom (LinearMap.codRestrict _ (e.app T).hom fun x => by
    rw [mem_fixF, ← ModuleCat.comp_apply, ← NatTrans.comp_app, he])
  naturality T T' φ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (ni_nat e φ x))

def fixI {F : C ⥤ ModuleCat.{w} R} (S : SubF F) : S.fn ⟶ F where
  app T := ModuleCat.ofHom (S.S T).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/- English proof (translation)
The claim follows from `NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))`.
-/
theorem fixP_fixI {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : fixP e he ≫ fixI (fixF e) = e :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

def gNat {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) : G ⟶ G where
  app _ := G.map (X := SingleObj.star _) (Y := SingleObj.star _) g
  naturality X Y a := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact mul_comm (g : Gam d) (a : Gam d)

/- English proof (translation)
Use `CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G) { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) } (fun T x => rfl) n x` as an intermediate fact. Rewrite using `[this]`. Conclude with `((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)`.
-/
theorem gNat_pull {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (n : ℕ) (x : H G n) :
    (Mor.ofNatTrans (gNat G g)).pull n x = x := by
  have := CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G)
    { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) }
    (fun T x => rfl) n x
  rw [this]
  exact ((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)

/- English proof (translation)
Take `⟨x, hx⟩` from `(CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z`. Rewrite using `[← hx]`. Establish `e1` using `ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x`. Rewrite `e1` using `[sub_add_cancel, gNat_pull, ni_pull_id]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem killed_of {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (s : R)
    (hu : ∀ T, UpTo s ((gNat G g - 𝟙 G).app T).hom) (n : ℕ) (z : H G n) : s ^ 2 • z = 0 := by
  obtain ⟨x, hx⟩ := (CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z
  rw [← hx]
  have e1 := ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x
  rw [sub_add_cancel, gNat_pull, ni_pull_id] at e1
  calc _ = ((Mor.ofNatTrans (gNat G g - 𝟙 G)).pull n x + x) - x := (add_sub_cancel_right _ _).symm
    _ = x - x := by rw [← e1]
    _ = 0 := sub_self x

/- English proof (translation)
Use `killed_of _ (gen k) s (fun T => ?_) n z` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom`. Establish `hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y = ((fixF (h.π k)).fn.map (X` using `SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl`. Use `⟨fun y hy => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[hδ, sub_eq_zero]`.

Establish `h1 : ((h.π k).app _).hom y.1 = y.1` using `(mem_fixF (h.π k) _ y.1).1 y.2`. Conclude with `Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))`. Establish `h1 : ((h.π k).app _).hom y.1 = y.1` using `(mem_fixF (h.π k) _ y.1).1 y.2`. Take `⟨x, hx, hx2⟩` from `h.surj k y.1 h1`. Conclude with `⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩`.
-/
theorem ni_killed {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) (h : NI s α) (k : Fin d)
    (n : ℕ) (z : H (fixF (h.π k)).fn n) : s ^ 2 • z = 0 := by
  refine killed_of _ (gen k) s (fun T => ?_) n z
  change UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom
  have hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y =
      ((fixF (h.π k)).fn.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [hδ, sub_eq_zero] at hy
    have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    exact Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))
  · have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    obtain ⟨x, hx, hx2⟩ := h.surj k y.1 h1
    exact ⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩

end NiCoh

end CrystallineSemistableComparison.B

/- English proof (translation)
Introduce `R _ d s M N α h n j _`. Use `⟨fun x hx => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `e` using `ni_pull_comp α h.ρ j x`. Rewrite `e` using `[h.αρ, ni_pull_id, hx, map_zero]`. Rewrite using `[e, smul_zero]`.

Use `⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩` and prove the remaining obligations. Rewrite using `[← ni_pull_comp]`. Establish `e` using `ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)`. Rewrite `e` using `[h.sum, ni_pull_id, ni_pull_sum]`. Establish `hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0`.

Introduce `k`. Rewrite using `[← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]`. Rewrite `e` using `[Finset.sum_eq_zero (fun k _ => hk k), add_zero]`. Conclude with `e.symm`.
-/
theorem CrystallineSemistableComparison.B.P.ni_coh : ∀ {R : Type} [CommRing R] {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N), NI s α → ∀ n, IsoLe (s ^ 2) n (Mor.ofNatTrans α) := by
  intro R _ d s M N α h n j _
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have e := ni_pull_comp α h.ρ j x
    rw [h.αρ, ni_pull_id, hx, map_zero] at e
    rw [e, smul_zero]
  · refine ⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩
    rw [← ni_pull_comp]
    have e := ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)
    rw [h.sum, ni_pull_id, ni_pull_sum] at e
    have hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0 := by
      intro k
      rw [← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]
    rw [Finset.sum_eq_zero (fun k _ => hk k), add_zero] at e
    exact e.symm
