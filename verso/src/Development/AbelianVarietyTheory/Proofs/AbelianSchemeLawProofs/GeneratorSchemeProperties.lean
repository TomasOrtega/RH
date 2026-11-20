import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory

namespace GenScheme

def pb {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (f.appLE U W h).hom

section Calc

variable {X Y Z : Scheme.{0}}

/- English proof (translation)
The claim follows from `Units.ext (congr($(f.appLE_map h (homOfLE h').op).hom a.val))`.
-/
theorem res_pb (f : Y ⟶ X) (U : X.Opens) (W W' : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W)
    (a : Γ(X, U)ˣ) : res h' (pb f U W h a) = pb f U W' (h'.trans h) a :=
  Units.ext (congr($(f.appLE_map h (homOfLE h').op).hom a.val))

/- English proof (translation)
The claim follows from `Units.ext (congr($(f.map_appLE h (homOfLE h').op).hom a.val))`.
-/
theorem pb_res (f : Y ⟶ X) (U U' : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (a : Γ(X, U)ˣ) : pb f U' W h (res h' a) = pb f U W (h.trans (f.preimage_mono h')) a :=
  Units.ext (congr($(f.map_appLE h (homOfLE h').op).hom a.val))

/- English proof (translation)
The claim follows from `Units.ext (congr($(Scheme.Hom.appLE_comp_appLE g f U V W h h').hom a.val))`.
-/
theorem pb_pb (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h a) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) a :=
  Units.ext (congr($(Scheme.Hom.appLE_comp_appLE g f U V W h h').hom a.val))

/- English proof (translation)
The claim follows from `Units.ext (congr($(f.app_eq_appLE (U := U)).hom a.val))`.
-/
theorem pullU_eq (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)ˣ) :
    pullU f U a = pb f U _ le_rfl a :=
  Units.ext (congr($(f.app_eq_appLE (U := U)).hom a.val))

/- English proof (translation)
The claim follows from `Units.ext (congr($((X.presheaf.map_comp (homOfLE h).op (homOfLE h').op).symm).hom a.val))`.
-/
theorem res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a :=
  Units.ext (congr($((X.presheaf.map_comp (homOfLE h).op (homOfLE h').op).symm).hom a.val))

/- English proof (translation)
The claim follows from `Units.ext (congr($(X.presheaf.map_id (Opposite.op U)).hom a.val))`.
-/
theorem res_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a :=
  Units.ext (congr($(X.presheaf.map_id (Opposite.op U)).hom a.val))

/- English proof (translation)
Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.
-/
theorem pb_top_val (f : Y ⟶ X) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) (a : Γ(X, ⊤)ˣ) :
    (pb f ⊤ ⊤ h a).val = f.appTop.hom a.val := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

end Calc

section One

variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)

def Compat (s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ) : Prop :=
  ∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_right : L.U i ⊓ L.U i' ≤ L.U i')) (s i') =
    pullU b _ (L.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : L.U i ⊓ L.U i' ≤ L.U i)) (s i)

variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)

def extend (t : Γ(Z, ⊤)ˣ) (i : L.ι) : Γ(Z, b ⁻¹ᵁ L.U i)ˣ :=
  pb b (L.U j ⊓ L.U i) _ (fun x hx => ⟨hj trivial, hx⟩) (L.g j i) * res le_top t

variable {L}

/- English proof (translation)
Introduce `i i'`. Establish `h` using `congrArg (pb b (L.U j ⊓ L.U i ⊓ L.U i') (b ⁻¹ᵁ (L.U i ⊓ L.U i')) (fun x hx => ⟨⟨hj trivial, hx.1⟩, hx.2⟩)) (hL.cocycle j i i')`. Rewrite `h` using `[map_mul, pb_res, pb_res, pb_res]`. Simplify using `only [extend, map_mul, res_pb, res_res, pullU_eq]`. Rewrite using `[← h, ← _root_.mul_assoc, _root_.mul_comm (pb b _ _ _ (L.g i i'))]`.
-/
theorem compat_extend (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : Compat L b (extend L b j hj t) := by
  intro i i'
  have h := congrArg (pb b (L.U j ⊓ L.U i ⊓ L.U i') (b ⁻¹ᵁ (L.U i ⊓ L.U i'))
    (fun x hx => ⟨⟨hj trivial, hx.1⟩, hx.2⟩)) (hL.cocycle j i i')
  rw [map_mul, pb_res, pb_res, pb_res] at h
  simp only [extend, map_mul, res_pb, res_res, pullU_eq]
  rw [← h, ← _root_.mul_assoc, _root_.mul_comm (pb b _ _ _ (L.g i i'))]

/- English proof (translation)
Establish `h` using `congrArg (pb b (L.U j) ⊤ hj) (hL.g_self j)`. Rewrite `h` using `[pb_res, map_one]`. Simplify using `only [extend, map_mul, res_pb, res_res, res_self]`. Rewrite using `[h, _root_.one_mul]`.
-/
theorem res_extend_self (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : res hj (extend L b j hj t j) = t := by
  have h := congrArg (pb b (L.U j) ⊤ hj) (hL.g_self j)
  rw [pb_res, map_one] at h
  simp only [extend, map_mul, res_pb, res_res, res_self]
  rw [h, _root_.one_mul]

/- English proof (translation)
Establish `h` using `congrArg (res (show b ⁻¹ᵁ L.U i ≤ b ⁻¹ᵁ (L.U j ⊓ L.U i) from fun x hx => ⟨hj trivial, hx⟩)) (hs j i)`. Rewrite `h` using `[map_mul, res_res, res_res, res_self, pullU_eq, res_pb]`. Rewrite using `[h, extend, res_res]`.
-/
theorem eq_extend {s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ} (hs : Compat L b s) (i : L.ι) :
    s i = extend L b j hj (res hj (s j)) i := by
  have h := congrArg (res (show b ⁻¹ᵁ L.U i ≤ b ⁻¹ᵁ (L.U j ⊓ L.U i) from
    fun x hx => ⟨hj trivial, hx⟩)) (hs j i)
  rw [map_mul, res_res, res_res, res_self, pullU_eq, res_pb] at h
  rw [h, extend, res_res]

/- English proof (translation)
Substitute `hg` using the available equality. Introduce `i i'`. Establish `h` using `congrArg (pb g (q ⁻¹ᵁ (L.U i ⊓ L.U i')) ((g ≫ q) ⁻¹ᵁ (L.U i ⊓ L.U i')) le_rfl) (hu i i')`. Rewrite `h` using `[map_mul, pb_res, pb_res, pullU_eq, pb_pb]`. Rewrite using `[res_pb, res_pb, pullU_eq]`.

Conclude with `h`.
-/
theorem compat_pb {G : Scheme.{0}} {q : G ⟶ B} {u : ∀ i : L.ι, Γ(G, q ⁻¹ᵁ L.U i)ˣ}
    (hu : Compat L q u) (g : Z ⟶ G) (hg : g ≫ q = b) :
    Compat L b fun i => pb g (q ⁻¹ᵁ L.U i) (b ⁻¹ᵁ L.U i) (by rw [← hg]; exact le_rfl) (u i) := by
  subst hg
  intro i i'
  have h := congrArg (pb g (q ⁻¹ᵁ (L.U i ⊓ L.U i')) ((g ≫ q) ⁻¹ᵁ (L.U i ⊓ L.U i')) le_rfl) (hu i i')
  rw [map_mul, pb_res, pb_res, pullU_eq, pb_pb] at h
  rw [res_pb, res_pb, pullU_eq]
  exact h

end One

section Many

variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}

variable (N q u) in

def Univ : Prop :=
  ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ),
    (∀ k, Compat (N k) b (s k)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i,
      (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val =
        (s k i).val

/- English proof (translation)
Take `⟨g, ⟨hg, h⟩, -⟩` from `hU Z b (fun k => extend (N k) b (j k) (hj k) (t k)) fun k => compat_extend b (j k) (hj k) (hN k) (t k)`. Use `⟨g, hg, fun k => ?_⟩` and prove the remaining obligations. Establish `e : pb g (q ⁻¹ᵁ (N k).U (j k)) (b ⁻¹ᵁ (N k).U (j k)) (by rw [← hg]; exact le_rfl) (u k (j k)) = extend (N k) b (j k) (hj k) (t k) (j k)` using `Units.ext (h k (j k))`. Rewrite using `[← res_extend_self b (j k) (hj k) (hN k) (t k), ← e, res_pb]`.
-/
theorem exists_hom (hN : ∀ k, (N k).IsLB) (hU : Univ N q u) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (t : κ → Γ(Z, ⊤)ˣ) :
    ∃ (g : Z ⟶ G) (hg : g ≫ q = b), ∀ k,
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (by subst hg; exact hj k) (u k (j k)) = t k := by
  obtain ⟨g, ⟨hg, h⟩, -⟩ := hU Z b (fun k => extend (N k) b (j k) (hj k) (t k))
    fun k => compat_extend b (j k) (hj k) (hN k) (t k)
  refine ⟨g, hg, fun k => ?_⟩
  have e : pb g (q ⁻¹ᵁ (N k).U (j k)) (b ⁻¹ᵁ (N k).U (j k)) (by rw [← hg]; exact le_rfl) (u k (j k)) =
      extend (N k) b (j k) (hj k) (t k) (j k) := Units.ext (h k (j k))
  rw [← res_extend_self b (j k) (hj k) (hN k) (t k), ← e, res_pb]

/- English proof (translation)
Establish `c` using `fun k => compat_pb (g ≫ q) (hu k) g rfl`. Establish `c'` using `fun k => compat_pb (g ≫ q) (hu k) g' hg`. Use `(hU Z (g ≫ q) _ c).unique ⟨hg, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩` and prove the remaining obligations. Establish `e` using `eq_extend (g ≫ q) (j k) (hj k) (c k) i`. Establish `e'` using `eq_extend (g ≫ q) (j k) (hj k) (c' k) i`.

Simplify using `only [res_pb] at e e'`. Rewrite `e'` using `[h k, ← e]`. Conclude with `congrArg Units.val e'`.
-/
theorem hom_ext (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) {Z : Scheme.{0}}
    (j : ∀ k, (N k).ι) (g g' : Z ⟶ G) (hg : g' ≫ q = g ≫ q)
    (hj : ∀ k, ⊤ ≤ g ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)) (hj' : ∀ k, ⊤ ≤ g' ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k))
    (h : ∀ k, pb g' (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj' k) (u k (j k)) =
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj k) (u k (j k))) : g' = g := by
  have c := fun k => compat_pb (g ≫ q) (hu k) g rfl
  have c' := fun k => compat_pb (g ≫ q) (hu k) g' hg
  refine (hU Z (g ≫ q) _ c).unique ⟨hg, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩
  have e := eq_extend (g ≫ q) (j k) (hj k) (c k) i
  have e' := eq_extend (g ≫ q) (j k) (hj k) (c' k) i
  simp only [res_pb] at e e'
  rw [h k, ← e] at e'
  exact congrArg Units.val e'

open SplitTorus in
/- English proof (translation)
Apply `(pointsEquiv T (κ →₀ ℤ)).injective` to reduce the goal to its premises. Use `Finsupp.addHom_ext' fun k => AddMonoidHom.ext_int ?_` and prove the remaining obligations. Conclude with `Additive.toMul.injective (Units.ext (h k))`.
-/
theorem torus_hom_ext {S : Scheme.{0}} {T : Over S} {a a' : T ⟶ splitTorus S (κ →₀ ℤ)}
    (h : ∀ k, val a (Finsupp.single k 1) = val a' (Finsupp.single k 1)) : a = a' := by
  apply (pointsEquiv T (κ →₀ ℤ)).injective
  refine Finsupp.addHom_ext' fun k => AddMonoidHom.ext_int ?_
  exact Additive.toMul.injective (Units.ext (h k))

open SplitTorus in
/- English proof (translation)
Use `⟨ofVal (Finsupp.liftAddHom fun k => zmultiplesHom _ (Additive.ofMul (t k))), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[val_ofVal]`. Simplify using the standard rewrite rules.
-/
theorem exists_torus_hom {S : Scheme.{0}} {T : Over S} (t : κ → Γ(T.left, ⊤)ˣ) :
    ∃ a : T ⟶ splitTorus S (κ →₀ ℤ), ∀ k, val a (Finsupp.single k 1) = (t k).val := by
  refine ⟨ofVal (Finsupp.liftAddHom fun k => zmultiplesHom _ (Additive.ofMul (t k))), fun k => ?_⟩
  rw [val_ofVal]
  simp

open SplitTorus in

/- English proof (translation)
Set `T` to `splitTorus V (κ →₀ ℤ)`. Establish `lands : ∀ {Z : Scheme.{0}} (c : Z ⟶ V) k, ⊤ ≤ (c ≫ v) ⁻¹ᵁ (N k).U (j k)` using `fun c k => c.preimage_mono (hj k)`. Establish `lands' : ∀ {Z : Scheme.{0}} (a : Z ⟶ G) (c : Z ⟶ V) (_ : a ≫ q = c ≫ v) k, ⊤ ≤ a ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)` using `fun a c h k => by`. Rewrite using `[← Scheme.Hom.comp_preimage, h]`. Conclude with `lands c k`.

Take `⟨p, hp, hpu⟩` from `exists_hom hN hU (T.hom ≫ v) j (lands T.hom) fun k => (isUnit_val (𝟙 T) (Finsupp.single k 1)).unit`. Establish `key : ∀ {Z : Over V} (m : Z ⟶ T) k (h : ⊤ ≤ (m.left ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)), (pb (m.left ≫ p) (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k))).val = val m (Finsupp.single k 1)`. Introduce `Z m k h`. Rewrite using `[← pb_pb m.left p _ ⊤ ⊤ (lands' p T.hom hp k) le_rfl, hpu, pb_top_val]`. Conclude with `(val_eq m _).symm`.

Establish `ex : ∀ s : PullbackCone q v, ∃ l : s.pt ⟶ T.left, l ≫ p = s.fst ∧ l ≫ T.hom = s.snd`. Introduce `s`. Take `⟨l, hl⟩` from `exists_torus_hom (T := Over.mk s.snd) fun k => pb s.fst (q ⁻¹ᵁ (N k).U (j k)) ⊤ (lands' _ _ s.condition k) (u k (j k))`. Establish `w : l.left ≫ T.hom = s.snd` using `Over.w l`. Establish `w' : (l.left ≫ p) ≫ q = s.snd ≫ v`.

Rewrite using `[Category.assoc, hp, ← Category.assoc, w]`. Use `⟨l.left, hom_ext hu hU j _ _ (w'.trans s.condition.symm) (lands' _ _ s.condition) (lands' _ _ w') fun k => Units.ext ?_, w⟩` and prove the remaining obligations. Conclude with `(key l k _).trans (hl k)`. Use `⟨p, ⟨hp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex s).choose) (fun s => (ex s).choose_spec.1) (fun s => (ex s).choose_spec.2) fun s m h₁ h₂ => ?_⟩⟩` and prove the remaining obligations. Take `⟨h₃, h₄⟩` from `(ex s).choose_spec`.

Generalize the expression as in `(ex s).choose = l at h₃ h₄`. Establish `: (Over.homMk m h₂ : Over.mk s.snd ⟶ T) = Over.homMk l h₄`. Use `torus_hom_ext fun k => ?_` and prove the remaining obligations. Establish `hm : ⊤ ≤ (m ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)` using `by rw [h₁]; exact lands' _ _ s.condition k`. Establish `hl : ⊤ ≤ (l ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)` using `by rw [h₃]; exact lands' _ _ s.condition k`.

Rewrite using `[← key (Over.homMk m h₂ : Over.mk s.snd ⟶ T) k hm, ← key (Over.homMk l h₄ : Over.mk s.snd ⟶ T) k hl]`. Establish `aux : ∀ (a a' : s.pt ⟶ G) (_ : a = a') h h', pb a (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k)) = pb a' (q ⁻¹ᵁ (N k).U (j k)) ⊤ h' (u k (j k))`. Introduce and unpack `a _ rfl _ _`. Both sides reduce to the same expression. Conclude with `congrArg Units.val (aux _ _ (h₁.trans h₃.symm) _ _)`.

Conclude with `congrArg (·.left) this`.
-/
theorem exists_isPullback (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u)
    {V : Scheme.{0}} (v : V ⟶ B) (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ v ⁻¹ᵁ (N k).U (j k)) :
    ∃ p : (splitTorus V (κ →₀ ℤ)).left ⟶ G, IsPullback p (splitTorus V (κ →₀ ℤ)).hom q v := by
  let T := splitTorus V (κ →₀ ℤ)
  have lands : ∀ {Z : Scheme.{0}} (c : Z ⟶ V) k, ⊤ ≤ (c ≫ v) ⁻¹ᵁ (N k).U (j k) :=
    fun c k => c.preimage_mono (hj k)
  have lands' : ∀ {Z : Scheme.{0}} (a : Z ⟶ G) (c : Z ⟶ V) (_ : a ≫ q = c ≫ v) k,
      ⊤ ≤ a ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := fun a c h k => by
    rw [← Scheme.Hom.comp_preimage, h]; exact lands c k
  obtain ⟨p, hp, hpu⟩ := exists_hom hN hU (T.hom ≫ v) j (lands T.hom)
    fun k => (isUnit_val (𝟙 T) (Finsupp.single k 1)).unit
  have key : ∀ {Z : Over V} (m : Z ⟶ T) k (h : ⊤ ≤ (m.left ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)),
      (pb (m.left ≫ p) (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k))).val = val m (Finsupp.single k 1) := by
    intro Z m k h
    rw [← pb_pb m.left p _ ⊤ ⊤ (lands' p T.hom hp k) le_rfl, hpu, pb_top_val]
    exact (val_eq m _).symm
  have ex : ∀ s : PullbackCone q v, ∃ l : s.pt ⟶ T.left, l ≫ p = s.fst ∧ l ≫ T.hom = s.snd := by
    intro s
    obtain ⟨l, hl⟩ := exists_torus_hom (T := Over.mk s.snd)
      fun k => pb s.fst (q ⁻¹ᵁ (N k).U (j k)) ⊤ (lands' _ _ s.condition k) (u k (j k))
    have w : l.left ≫ T.hom = s.snd := Over.w l
    have w' : (l.left ≫ p) ≫ q = s.snd ≫ v := by
      rw [Category.assoc, hp, ← Category.assoc, w]
    refine ⟨l.left, hom_ext hu hU j _ _ (w'.trans s.condition.symm) (lands' _ _ s.condition)
      (lands' _ _ w') fun k => Units.ext ?_, w⟩
    exact (key l k _).trans (hl k)
  refine ⟨p, ⟨hp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex s).choose)
    (fun s => (ex s).choose_spec.1) (fun s => (ex s).choose_spec.2) fun s m h₁ h₂ => ?_⟩⟩
  obtain ⟨h₃, h₄⟩ := (ex s).choose_spec
  generalize (ex s).choose = l at h₃ h₄
  have : (Over.homMk m h₂ : Over.mk s.snd ⟶ T) = Over.homMk l h₄ := by
    refine torus_hom_ext fun k => ?_
    have hm : ⊤ ≤ (m ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₁]; exact lands' _ _ s.condition k
    have hl : ⊤ ≤ (l ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₃]; exact lands' _ _ s.condition k
    rw [← key (Over.homMk m h₂ : Over.mk s.snd ⟶ T) k hm, ← key (Over.homMk l h₄ : Over.mk s.snd ⟶ T) k hl]
    have aux : ∀ (a a' : s.pt ⟶ G) (_ : a = a') h h',
        pb a (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k)) = pb a' (q ⁻¹ᵁ (N k).U (j k)) ⊤ h' (u k (j k)) := by
      rintro a _ rfl _ _; rfl
    exact congrArg Units.val (aux _ _ (h₁.trans h₃.symm) _ _)
  exact congrArg (·.left) this

/- English proof (translation)
Set `W : (∀ k, (N k).ι) → B.Opens` to `fun j => ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩`. Establish `hW : iSup W = ⊤`. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations. Establish `: ∀ k, ∃ i, x ∈ (N k).U i` using `fun k => TopologicalSpace.Opens.mem_iSup.1 ((hN k).cover.ge trivial)`. Use `choose j hj using this`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩`. Use `IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun j => ?_` and prove the remaining obligations. Take `⟨p, hp⟩` from `exists_isPullback hN hu hU (W j).ι j fun k x _ => Set.mem_iInter.1 x.2 k`. Establish `h` using `(isPullback_morphismRestrict q (W j)).flip`. Rewrite using `[← h.isoIsPullback_hom_snd _ _ hp, MorphismProperty.cancel_left_of_respectsIso P]`.

Conclude with `hP _`.
-/
theorem prop_of_torus [Fintype κ] (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V : Scheme.{0}, P (splitTorus V (κ →₀ ℤ)).hom)
    (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) : P q := by
  let W : (∀ k, (N k).ι) → B.Opens := fun j =>
    ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have : ∀ k, ∃ i, x ∈ (N k).U i := fun k =>
      TopologicalSpace.Opens.mem_iSup.1 ((hN k).cover.ge trivial)
    choose j hj using this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun j => ?_
  obtain ⟨p, hp⟩ := exists_isPullback hN hu hU (W j).ι j
    fun k x _ => Set.mem_iInter.1 x.2 k
  have h := (isPullback_morphismRestrict q (W j)).flip
  rw [← h.isoIsPullback_hom_snd _ _ hp, MorphismProperty.cancel_left_of_respectsIso P]
  exact hP _

end Many

end GenScheme

/- English proof (translation)
Introduce `B κ _ N hN G q u ⟨hu, hU⟩`. Establish `hc : GeometricallyConnected q`. Establish `: IsZariskiLocalAtTarget @GeometricallyConnected`. Rewrite using `[GeometricallyConnected.eq_geometrically]`. Use `infer_instance`.

Conclude with `GenScheme.prop_of_torus @GeometricallyConnected (fun V => inferInstance) hN hu hU`. Establish `: IsZariskiLocalAtTarget @IsAffineHom` using `HasAffineProperty.instIsZariskiLocalAtTarget (P := @IsAffineHom)`. Establish `: IsZariskiLocalAtTarget @Smooth` using `HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)`. Establish `ha : IsAffineHom q` using `GenScheme.prop_of_torus @IsAffineHom (fun V => inferInstance) hN hu hU`. Use `⟨ha, GenScheme.prop_of_torus @Smooth (fun V => ?_) hN hu hU, inferInstance, inferInstance, hc⟩` and prove the remaining obligations.

Use `H1.torus_dim V (κ →₀ ℤ)` as an intermediate fact. Conclude with `SmoothOfRelativeDimension.smooth (Module.finrank ℤ (κ →₀ ℤ)) _`.
-/
theorem generatorScheme_properties :
    ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∀ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q ∧ Smooth q ∧ Surjective q ∧ IsSeparated q ∧ GeometricallyConnected q := by
  intro B κ _ N hN G q u ⟨hu, hU⟩
  have hc : GeometricallyConnected q := by
    have : IsZariskiLocalAtTarget @GeometricallyConnected := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    exact GenScheme.prop_of_torus @GeometricallyConnected (fun V => inferInstance) hN hu hU
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    HasAffineProperty.instIsZariskiLocalAtTarget (P := @IsAffineHom)
  have : IsZariskiLocalAtTarget @Smooth := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have ha : IsAffineHom q := GenScheme.prop_of_torus @IsAffineHom (fun V => inferInstance) hN hu hU
  refine ⟨ha, GenScheme.prop_of_torus @Smooth (fun V => ?_) hN hu hU, inferInstance, inferInstance, hc⟩
  have := H1.torus_dim V (κ →₀ ℤ)
  exact SmoothOfRelativeDimension.smooth (Module.finrank ℤ (κ →₀ ℤ)) _

end GlobalTheory
