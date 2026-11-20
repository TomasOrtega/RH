import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LinDescent

variable {X Y Z : Scheme.{0}}

def gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

/- English proof (translation)
The claim follows from `gs_eq r z U h a`.
-/
theorem gs_eq_gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gs r z U a = gsHom r z U h a := gs_eq r z U h a

/- English proof (translation)
Simplify using `only [gs_eq_gsHom r z U h, map_pow]`.
-/
theorem gs_pow (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq_gsHom r z U h, map_pow]

/- English proof (translation)
Simplify using `only [gs_eq_gsHom r z U h, map_sub]`.
-/
theorem gs_sub (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq_gsHom r z U h, map_sub]

/- English proof (translation)
Simplify using `only [gs_eq_gsHom r z U h, map_zero]`.
-/
theorem gs_zero (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) :
    gs r z U 0 = 0 := by simp only [gs_eq_gsHom r z U h, map_zero]

/- English proof (translation)
Simplify using `only [gs_eq_gsHom r z U h, map_sum]`.
-/
theorem gs_sum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {κ : Type} [Fintype κ]
    (a : κ → Γ(X, U)) : gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by
  simp only [gs_eq_gsHom r z U h, map_sum]

/- English proof (translation)
The claim follows from `(gs_res r z e h ((g.app U).hom a)).trans (gs_pull r g z U (e h) a)`.
-/
theorem gs_appLE (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ g ⁻¹ᵁ U)
    (h : r z ∈ V) (a : Γ(X, U)) : gs r z V ((g.appLE U V e).hom a) = gs (r ≫ g) z U a :=
  (gs_res r z e h ((g.app U).hom a)).trans (gs_pull r g z U (e h) a)

/- English proof (translation)
Rewrite using `[← gs_pull r g z U h, gs_eq r z (g ⁻¹ᵁ U) h, gs_eq g (r z) U h]`. Conclude with `(Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm`.
-/
theorem gs_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_eq r z (g ⁻¹ᵁ U) h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

/- English proof (translation)
Rewrite using `[gs_eq r z U h, ← Scheme.Hom.germ_stalkMap_apply, isUnit_map_iff, X.mem_basicOpen a _ h]`.
-/
theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.Hom.germ_stalkMap_apply, isUnit_map_iff, X.mem_basicOpen a _ h]

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

/- English proof (translation)
Take `⟨b, hb, -⟩` from `X.sheaf.existsUnique_gluing' O V (fun k => homOfLE (hO k)) (fun x hx => Opens.mem_iSup.2 (hc x hx)) a (fun k l => fn_ext (V := O k ⊓ O l) fun x hx => (gs_res (𝟙 X) x inf_le_left hx _).trans ((h k l x hx.1 hx.2).trans (gs_res (𝟙 X) x inf_le_right hx _).symm))`. Conclude with `⟨b, fun Z r z k hz => (gs_res r z (hO k) hz b).symm.trans (congrArg (gs r z (O k)) (hb k))⟩`.
-/
theorem glue_fn {κ : Type} (V : X.Opens) (O : κ → X.Opens) (hO : ∀ k, O k ≤ V)
    (hc : ∀ x ∈ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l → gs (𝟙 X) x (O k) (a k) = gs (𝟙 X) x (O l) (a l)) :
    ∃ b : Γ(X, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ O k →
      gs r z V b = gs r z (O k) (a k) := by
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' O V (fun k => homOfLE (hO k))
    (fun x hx => Opens.mem_iSup.2 (hc x hx)) a
    (fun k l => fn_ext (V := O k ⊓ O l) fun x hx =>
      (gs_res (𝟙 X) x inf_le_left hx _).trans ((h k l x hx.1 hx.2).trans
        (gs_res (𝟙 X) x inf_le_right hx _).symm))
  exact ⟨b, fun Z r z k hz => (gs_res r z (hO k) hz b).symm.trans (congrArg (gs r z (O k)) (hb k))⟩

abbrev gg (L : LB X) (r : Z ⟶ X) (z : Z) (i j : L.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z (L.U i ⊓ L.U j) (L.g i j)

/- English proof (translation)
The claim follows from `gs_unit r z (L.U i ⊓ L.U j) ⟨hi, hj⟩ _`.
-/
theorem gs_g (L : LB X) (r : Z ⟶ X) (z : Z) {i j : L.ι} (hi : r z ∈ L.U i) (hj : r z ∈ L.U j) :
    gs r z (L.U i ⊓ L.U j) (L.g i j).val = (gg L r z i j).val := gs_unit r z (L.U i ⊓ L.U j) ⟨hi, hj⟩ _

def IsLocSec (L : LB X) (W : X.Opens) (m : ∀ i, Γ(X, W ⊓ L.U i)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i j, r z ∈ W → r z ∈ L.U i → r z ∈ L.U j →
    gs r z _ (m i) = (gg L r z i j).val * gs r z _ (m j)

/- English proof (translation)
Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ O k ⊓ L.U i → gs r z (O k ⊓ L.U i) (rs (le_inf inf_le_right (inf_le_left.trans (ha k))) (L.g i (a k)).val * rs inf_le_left (b k)) = (gg L r z i (a k)).val * gs r z (O k) (b k)` using `fun Z r z i k hz => by`. Rewrite using `[gs_mul r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_g L r z hz.2 (ha k hz.1)]`. Establish `: ∀ i, ∃ m : Γ(X, W ⊓ L.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ L.U i → r z ∈ O k → gs r z _ m = (gg L r z i (a k)).val * gs r z (O k) (b k)` using `fun i => by`. Take `⟨m, hm⟩` from `glue_fn (W ⊓ L.U i) (fun k => O k ⊓ L.U i) (fun k => inf_le_inf_right _ (hO k)) (fun x hx => (hc x hx.1).imp fun k hk => ⟨hk, hx.2⟩) (fun k => rs (le_inf inf_le_right (inf_le_left.trans (ha k))) (L.g i (a k)).val * rs inf_le_left (b k)) (fun k l x hk hl => by`. Rewrite using `[v _ _ x i k hk, v _ _ x i l hl, h k l x hk.1 hl.1, ← mul_assoc, ← Units.val_mul, gm_cocycle hL (𝟙 X) x hk.2 (ha k hk.1) (ha l hl.1)])`.

Conclude with `⟨m, fun Z r z k hi hk => (hm Z r z k ⟨hk, hi⟩).trans (v Z r z i k ⟨hk, hi⟩)⟩`. Use `choose m hm using this`. Use `⟨m, fun Z r z i j hW hi hj => ?_, fun Z r z i k => hm i Z r z k⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hc _ hW`. Rewrite using `[hm i Z r z k hi hk, hm j Z r z k hj hk, ← mul_assoc, ← Units.val_mul, gm_cocycle hL r z hi hj (ha k hk)]`.
-/
theorem glue_sec {L : LB X} (hL : L.IsLB) {κ : Type} (W : X.Opens) (O : κ → X.Opens)
    (a : κ → L.ι) (hO : ∀ k, O k ≤ W) (ha : ∀ k, O k ≤ L.U (a k))
    (hc : ∀ x ∈ W, ∃ k, x ∈ O k) (b : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l →
      gs (𝟙 X) x (O k) (b k) = (gg L (𝟙 X) x (a k) (a l)).val * gs (𝟙 X) x (O l) (b l)) :
    ∃ m : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W m ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ L.U i → r z ∈ O k →
        gs r z _ (m i) = (gg L r z i (a k)).val * gs r z (O k) (b k) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ O k ⊓ L.U i →
      gs r z (O k ⊓ L.U i) (rs (le_inf inf_le_right (inf_le_left.trans (ha k))) (L.g i (a k)).val *
        rs inf_le_left (b k)) = (gg L r z i (a k)).val * gs r z (O k) (b k) := fun Z r z i k hz => by
    rw [gs_mul r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_g L r z hz.2 (ha k hz.1)]
  have : ∀ i, ∃ m : Γ(X, W ⊓ L.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k,
      r z ∈ L.U i → r z ∈ O k →
        gs r z _ m = (gg L r z i (a k)).val * gs r z (O k) (b k) := fun i => by
    obtain ⟨m, hm⟩ := glue_fn (W ⊓ L.U i) (fun k => O k ⊓ L.U i)
      (fun k => inf_le_inf_right _ (hO k))
      (fun x hx => (hc x hx.1).imp fun k hk => ⟨hk, hx.2⟩)
      (fun k => rs (le_inf inf_le_right (inf_le_left.trans (ha k))) (L.g i (a k)).val *
        rs inf_le_left (b k)) (fun k l x hk hl => by
        rw [v _ _ x i k hk, v _ _ x i l hl, h k l x hk.1 hl.1, ← mul_assoc, ← Units.val_mul,
          gm_cocycle hL (𝟙 X) x hk.2 (ha k hk.1) (ha l hl.1)])
    exact ⟨m, fun Z r z k hi hk => (hm Z r z k ⟨hk, hi⟩).trans (v Z r z i k ⟨hk, hi⟩)⟩
  choose m hm using this
  refine ⟨m, fun Z r z i j hW hi hj => ?_, fun Z r z i k => hm i Z r z k⟩
  obtain ⟨k, hk⟩ := hc _ hW
  rw [hm i Z r z k hi hk, hm j Z r z k hj hk, ← mul_assoc, ← Units.val_mul,
    gm_cocycle hL r z hi hj (ha k hk)]

/- English proof (translation)
Take `⟨n, b, hb⟩` from `exists_eq_pow_mul_of_isAffineOpen X D hD f (rs hV y)`. Use `filter_upwards [Filter.eventually_ge_atTop n] with m hm`. Use `⟨f ^ (m - n) * b, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxD : x ∈ D` using `X.basicOpen_le f hx`. Establish `e : gs (𝟙 X) x _ (rs (X.basicOpen_le f) b) = gs (𝟙 X) x _ (rs (X.basicOpen_le f) f ^ n * rs hV y)` using `congrArg _ hb`.

Rewrite `e` using `[gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx]`. Rewrite using `[gs_mul _ x _ hxD, gs_pow _ x _ hxD, e, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]`.
-/
theorem eventually_extend {D V : X.Opens} (hD : IsAffineOpen D) (f : Γ(X, D))
    (hV : X.basicOpen f ≤ V) (y : Γ(X, V)) :
    ∀ᶠ n in Filter.atTop, ∃ b : Γ(X, D), ∀ x ∈ X.basicOpen f,
      gs (𝟙 X) x D b = gs (𝟙 X) x D f ^ n * gs (𝟙 X) x V y := by
  obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X D hD f (rs hV y)
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  refine ⟨f ^ (m - n) * b, fun x hx => ?_⟩
  have hxD : x ∈ D := X.basicOpen_le f hx
  have e : gs (𝟙 X) x _ (rs (X.basicOpen_le f) b) =
      gs (𝟙 X) x _ (rs (X.basicOpen_le f) f ^ n * rs hV y) := congrArg _ hb
  rw [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx] at e
  rw [gs_mul _ x _ hxD, gs_pow _ x _ hxD, e, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hD b f (fn_ext fun x hx => (gs_res _ x (X.basicOpen_le f) hx b).trans ((h x hx).trans (gs_zero _ x _ hx).symm))`. Use `filter_upwards [Filter.eventually_ge_atTop n] with m hm`. Rewrite using `[← Nat.sub_add_cancel hm, pow_add, mul_assoc, hn, mul_zero]`.
-/
theorem eventually_kill {D : X.Opens} (hD : IsAffineOpen D) (f b : Γ(X, D))
    (h : ∀ x ∈ X.basicOpen f, gs (𝟙 X) x D b = 0) : ∀ᶠ n in Filter.atTop, f ^ n * b = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hD b f
    (fn_ext fun x hx => (gs_res _ x (X.basicOpen_le f) hx b).trans
      ((h x hx).trans (gs_zero _ x _ hx).symm))
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  rw [← Nat.sub_add_cancel hm, pow_add, mul_assoc, hn, mul_zero]

/- English proof (translation)
Establish `H : ∀ w : W, ∃ (a : L.ι) (h : Γ(X, W)), X.basicOpen h ≤ L.U a ∧ w.1 ∈ X.basicOpen h` using `fun w => by`. Take `⟨a, ha⟩` from `exists_chart hL w.1`. Take `⟨h, h1, h2⟩` from `hW.exists_basicOpen_le (V := L.U a) ⟨w.1, ha⟩ w.2`. Conclude with `⟨a, h, h1, h2⟩`. Use `choose a h ha hh using H`.

Take `⟨s, hs⟩` from `hW.isCompact.elim_finite_subcover (fun w : W => (X.basicOpen (h w) : Set X)) (fun w => (X.basicOpen (h w)).isOpen) fun w hw => Set.mem_iUnion.2 ⟨⟨w, hw⟩, hh _⟩`. Establish `hc : ∀ y ∈ W, ∃ k : s, y ∈ X.basicOpen (h k)` using `fun y hy => by`. Take `⟨k, hk, hk'⟩` from `Set.mem_iUnion₂.1 (hs hy)`. Conclude with `⟨⟨k, hk⟩, hk'⟩`. Set `D : s → X.Opens` to `fun k => X.basicOpen (h k)`.

Establish `hDW : ∀ k, D k ≤ W` using `fun k => X.basicOpen_le _`. Establish `hD : ∀ k, IsAffineOpen (D k)` using `fun k => hW.basicOpen _`. Establish `hDD : ∀ k l, IsAffineOpen (D k ⊓ D l)` using `fun k l => by`. Rewrite using `[← Scheme.basicOpen_mul]`. Conclude with `hW.basicOpen _`.

Set `x₀ : W` to `⟨x, hx⟩`. Set `f` to `h x₀`. Establish `hb : ∀ {V : X.Opens} (e : V ≤ W), X.basicOpen (rs e f) = V ⊓ X.basicOpen f` using `fun e => X.basicOpen_res f (homOfLE e).op`. Take `⟨N, hN⟩` from `(Filter.eventually_all.2 fun k : s => eventually_extend (hD k) (rs (hDW k) f) (V := L.U (a k) ⊓ L.U (a x₀)) ((hb _).le.trans (inf_le_inf (ha k) (ha x₀))) (L.g (a k) (a x₀)).val).exists`. Use `choose b hb' using hN`.

Establish `hb'' : ∀ k y, y ∈ D k → y ∈ X.basicOpen f → gs (𝟙 X) y (D k) (b k) = gs (𝟙 X) y W f ^ N * (gg L (𝟙 X) y (a k) (a x₀)).val` using `fun k y h1 h2 => by`. Rewrite using `[hb' k y ((hb _).ge ⟨h1, h2⟩), gs_res _ y _ h1, gs_g L (𝟙 X) y (ha k h1) (ha x₀ h2)]`. Establish `v : ∀ k l y, y ∈ D k ⊓ D l → gs (𝟙 X) y (D k ⊓ D l) (rs inf_le_left (b k) - rs (inf_le_inf (ha k) (ha l)) (L.g (a k) (a l)).val * rs inf_le_right (b l)) = gs (𝟙 X) y (D k) (b k) - (gg L (𝟙 X) y (a k) (a l)).val * gs (𝟙 X) y (D l) (b l)` using `fun k l y hy => by`. Rewrite using `[gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_g L (𝟙 X) y (ha k hy.1) (ha l hy.2)]`. Take `⟨N', hN'⟩` from `(Filter.eventually_all.2 fun p : s × s => eventually_kill (hDD p.1 p.2) (rs (inf_le_left.trans (hDW _)) f) (rs inf_le_left (b p.1) - rs (inf_le_inf (ha p.1) (ha p.2)) (L.g (a p.1) (a p.2)).val * rs inf_le_right (b p.2)) (fun y hy => by`.

Establish `hy'` using `(hb _).le hy`. Rewrite using `[v _ _ y hy'.1, hb'' _ y hy'.1.1 hy'.2, hb'' _ y hy'.1.2 hy'.2, mul_left_comm, ← Units.val_mul, gm_cocycle hL (𝟙 X) y (ha _ hy'.1.1) (ha _ hy'.1.2) (ha _ hy'.2), sub_self])).exists`. Establish `v' : ∀ k y, y ∈ D k → gs (𝟙 X) y (D k) (rs (hDW k) f ^ N' * b k) = gs (𝟙 X) y W f ^ N' * gs (𝟙 X) y (D k) (b k)` using `fun k y hy => by`. Rewrite using `[gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]`. Take `⟨m, hm, hm'⟩` from `glue_sec hL W D (fun k => a k) hDW (fun k => ha k) hc (fun k => rs (hDW k) f ^ N' * b k) (fun k l y hk hl => by`.

Establish `hy : y ∈ D k ⊓ D l` using `⟨hk, hl⟩`. Establish `e` using `congrArg (gs (𝟙 X) y (D k ⊓ D l)) (hN' (k, l))`. Rewrite `e` using `[gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, v k l y hy, gs_zero _ y _ hy, mul_sub, sub_eq_zero]`. Rewrite using `[v' k y hk, v' l y hl, e, mul_left_comm])`. Use `⟨m, hm, fun i hi => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hc x hx`. Establish `hf : IsUnit (gs (𝟙 X) x W f)` using `(isUnit_gs_iff _ x W hx f).2 (hh x₀)`. Use `(isUnit_gs_iff (𝟙 X) x (W ⊓ L.U i) ⟨hx, hi⟩ _).1 ?_` and prove the remaining obligations. Rewrite using `[hm' _ _ x i k hi hk, v' k x hk, hb'' k x hk (hh x₀)]`. Conclude with `(Units.isUnit _).mul ((hf.pow _).mul ((hf.pow _).mul (Units.isUnit _)))`.
-/
theorem exists_locSec {L : LB X} (hL : L.IsLB) {W : X.Opens} (hW : IsAffineOpen W) (x : X)
    (hx : x ∈ W) : ∃ m : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W m ∧
      ∀ i, x ∈ L.U i → x ∈ X.basicOpen (m i) := by
  classical
  have H : ∀ w : W, ∃ (a : L.ι) (h : Γ(X, W)), X.basicOpen h ≤ L.U a ∧ w.1 ∈ X.basicOpen h :=
    fun w => by
      obtain ⟨a, ha⟩ := exists_chart hL w.1
      obtain ⟨h, h1, h2⟩ := hW.exists_basicOpen_le (V := L.U a) ⟨w.1, ha⟩ w.2
      exact ⟨a, h, h1, h2⟩
  choose a h ha hh using H
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun w : W => (X.basicOpen (h w) : Set X))
    (fun w => (X.basicOpen (h w)).isOpen) fun w hw => Set.mem_iUnion.2 ⟨⟨w, hw⟩, hh _⟩
  have hc : ∀ y ∈ W, ∃ k : s, y ∈ X.basicOpen (h k) := fun y hy => by
    obtain ⟨k, hk, hk'⟩ := Set.mem_iUnion₂.1 (hs hy)
    exact ⟨⟨k, hk⟩, hk'⟩
  let D : s → X.Opens := fun k => X.basicOpen (h k)
  have hDW : ∀ k, D k ≤ W := fun k => X.basicOpen_le _
  have hD : ∀ k, IsAffineOpen (D k) := fun k => hW.basicOpen _
  have hDD : ∀ k l, IsAffineOpen (D k ⊓ D l) := fun k l => by
    rw [← Scheme.basicOpen_mul]; exact hW.basicOpen _
  let x₀ : W := ⟨x, hx⟩
  let f := h x₀
  have hb : ∀ {V : X.Opens} (e : V ≤ W), X.basicOpen (rs e f) = V ⊓ X.basicOpen f :=
    fun e => X.basicOpen_res f (homOfLE e).op
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 fun k : s => eventually_extend (hD k) (rs (hDW k) f)
    (V := L.U (a k) ⊓ L.U (a x₀)) ((hb _).le.trans (inf_le_inf (ha k) (ha x₀)))
    (L.g (a k) (a x₀)).val).exists
  choose b hb' using hN
  have hb'' : ∀ k y, y ∈ D k → y ∈ X.basicOpen f → gs (𝟙 X) y (D k) (b k) =
      gs (𝟙 X) y W f ^ N * (gg L (𝟙 X) y (a k) (a x₀)).val := fun k y h1 h2 => by
    rw [hb' k y ((hb _).ge ⟨h1, h2⟩), gs_res _ y _ h1, gs_g L (𝟙 X) y (ha k h1) (ha x₀ h2)]
  have v : ∀ k l y, y ∈ D k ⊓ D l → gs (𝟙 X) y (D k ⊓ D l) (rs inf_le_left (b k) -
      rs (inf_le_inf (ha k) (ha l)) (L.g (a k) (a l)).val * rs inf_le_right (b l)) =
      gs (𝟙 X) y (D k) (b k) - (gg L (𝟙 X) y (a k) (a l)).val * gs (𝟙 X) y (D l) (b l) :=
    fun k l y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_g L (𝟙 X) y (ha k hy.1) (ha l hy.2)]
  obtain ⟨N', hN'⟩ := (Filter.eventually_all.2 fun p : s × s => eventually_kill (hDD p.1 p.2)
    (rs (inf_le_left.trans (hDW _)) f) (rs inf_le_left (b p.1) -
      rs (inf_le_inf (ha p.1) (ha p.2)) (L.g (a p.1) (a p.2)).val * rs inf_le_right (b p.2))
    (fun y hy => by
      have hy' := (hb _).le hy
      rw [v _ _ y hy'.1, hb'' _ y hy'.1.1 hy'.2, hb'' _ y hy'.1.2 hy'.2, mul_left_comm,
        ← Units.val_mul, gm_cocycle hL (𝟙 X) y (ha _ hy'.1.1) (ha _ hy'.1.2) (ha _ hy'.2),
        sub_self])).exists
  have v' : ∀ k y, y ∈ D k → gs (𝟙 X) y (D k) (rs (hDW k) f ^ N' * b k) =
      gs (𝟙 X) y W f ^ N' * gs (𝟙 X) y (D k) (b k) := fun k y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨m, hm, hm'⟩ := glue_sec hL W D (fun k => a k) hDW (fun k => ha k) hc
    (fun k => rs (hDW k) f ^ N' * b k) (fun k l y hk hl => by
      have hy : y ∈ D k ⊓ D l := ⟨hk, hl⟩
      have e := congrArg (gs (𝟙 X) y (D k ⊓ D l)) (hN' (k, l))
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, v k l y hy, gs_zero _ y _ hy,
        mul_sub, sub_eq_zero] at e
      rw [v' k y hk, v' l y hl, e, mul_left_comm])
  refine ⟨m, hm, fun i hi => ?_⟩
  obtain ⟨k, hk⟩ := hc x hx
  have hf : IsUnit (gs (𝟙 X) x W f) := (isUnit_gs_iff _ x W hx f).2 (hh x₀)
  refine (isUnit_gs_iff (𝟙 X) x (W ⊓ L.U i) ⟨hx, hi⟩ _).1 ?_
  rw [hm' _ _ x i k hi hk, v' k x hk, hb'' k x hk (hh x₀)]
  exact (Units.isUnit _).mul ((hf.pow _).mul ((hf.pow _).mul (Units.isUnit _)))

/- English proof (translation)
The claim follows from `X.toRingedSpace.isUnit_of_isUnit_germ U a fun x hx => (X.mem_basicOpen a x hx).1 (h x hx)`.
-/
theorem isUnit_of_mem_basicOpen {U : X.Opens} (a : Γ(X, U)) (h : ∀ x ∈ U, x ∈ X.basicOpen a) :
    IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ U a fun x hx => (X.mem_basicOpen a x hx).1 (h x hx)

section Lin

variable {L : LB X}

abbrev twist (L : LB X) (t : X ⟶ X) : LB X := LB.LinComb L (K := Fin 2) ![𝟙 X, t] ![1, -1]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h 1⟩, fun h => Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨h.1, h.2⟩)⟩`.
-/
theorem mem_twist {t : X ⟶ X} {i j : L.ι} {x : X} :
    x ∈ LB.wchart L (K := Fin 2) ![𝟙 X, t] ![i, j] ↔ x ∈ L.U i ∧ t x ∈ L.U j :=
  ⟨fun h => ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h 1⟩,
    fun h => Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨h.1, h.2⟩)⟩

def uv {t : X ⟶ X} (u : LB.Gen (twist L t)) (r : Z ⟶ X) (z : Z) (i j : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z (LB.wchart L (K := Fin 2) ![𝟙 X, t] ![i, j]) (u.s ![i, j])

/- English proof (translation)
Use `(gen_trans hu r z (mem_twist.2 ⟨hi, hj⟩) (mem_twist.2 ⟨hi', hj'⟩)).trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[trF, Fin.prod_univ_two]`. Express the relevant statement in the definitionally equal form `gm (r ≫ 𝟙 X) z _ (L.g i i') ^ (1 : ℤ) * gm (r ≫ t) z _ (L.g j j') ^ (-1 : ℤ) = _`. Rewrite using `[Category.comp_id, zpow_one, zpow_neg_one]`.
-/
theorem uv_trans {t : X ⟶ X} {u : LB.Gen (twist L t)} (hu : u.IsGen) (r : Z ⟶ X) (z : Z)
    {i j i' j' : L.ι} (hi : r z ∈ L.U i) (hj : (r ≫ t) z ∈ L.U j) (hi' : r z ∈ L.U i')
    (hj' : (r ≫ t) z ∈ L.U j') :
    uv u r z i j = gg L r z i i' * (gg L (r ≫ t) z j j')⁻¹ * uv u r z i' j' := by
  refine (gen_trans hu r z (mem_twist.2 ⟨hi, hj⟩) (mem_twist.2 ⟨hi', hj'⟩)).trans ?_
  congr 1
  rw [trF, Fin.prod_univ_two]
  change gm (r ≫ 𝟙 X) z _ (L.g i i') ^ (1 : ℤ) * gm (r ≫ t) z _ (L.g j j') ^ (-1 : ℤ) = _
  rw [Category.comp_id, zpow_one, zpow_neg_one]

/- English proof (translation)
The claim follows from `val_of u r z J ![J r, J (r ≫ t)] (Fin.forall_fin_two.2 ⟨congrArg J (Category.comp_id r), rfl⟩)`.
-/
theorem val_eq_uv {t : X ⟶ X} (u : LB.Gen (twist L t)) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι) : val u r z J = uv u r z (J r) (J (r ≫ t)) :=
  val_of u r z J ![J r, J (r ≫ t)]
    (Fin.forall_fin_two.2 ⟨congrArg J (Category.comp_id r), rfl⟩)

/- English proof (translation)
Use `choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)`. Establish `hJ' : Good L z J` using `hJ`. Establish `e' : (r ≫ t₁) ≫ t₂ = r ≫ t₃` using `by rw [Category.assoc, e]`. Use `val_corr hJ' h r` as an intermediate fact. Rewrite `this` using `[val_mul hJ', val_pull hJ', val_eq_uv, val_eq_uv, val_eq_uv, e']`.

Rewrite using `[uv_trans h₃ r z hi hk (hJ r) (hJ _), uv_trans h₁ r z hi hj (hJ r) (hJ _), uv_trans h₂ (r ≫ t₁) z hj (e' ▸ hk) (hJ _) (e' ▸ hJ (r ≫ t₃)), this, e']`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem uv_cocycle (hL : L.IsLB) {t₁ t₂ t₃ : X ⟶ X} (e : t₁ ≫ t₂ = t₃)
    {u₁ : LB.Gen (twist L t₁)} {u₂ : LB.Gen (twist L t₂)} {u₃ : LB.Gen (twist L t₃)}
    (h₁ : u₁.IsGen) (h₂ : u₂.IsGen) (h₃ : u₃.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ u₃ (LB.mulGen L _ _ _ _ u₁ (LB.pullGen L _ _ u₂ t₁)))
    (r : Z ⟶ X) (z : Z) {i j k : L.ι} (hi : r z ∈ L.U i) (hj : (r ≫ t₁) z ∈ L.U j)
    (hk : (r ≫ t₃) z ∈ L.U k) :
    uv u₃ r z i k = uv u₁ r z i j * uv u₂ (r ≫ t₁) z j k := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have e' : (r ≫ t₁) ≫ t₂ = r ≫ t₃ := by rw [Category.assoc, e]
  have := val_corr hJ' h r
  rw [val_mul hJ', val_pull hJ', val_eq_uv, val_eq_uv, val_eq_uv, e'] at this
  rw [uv_trans h₃ r z hi hk (hJ r) (hJ _), uv_trans h₁ r z hi hj (hJ r) (hJ _),
    uv_trans h₂ (r ≫ t₁) z hj (e' ▸ hk) (hJ _) (e' ▸ hJ (r ≫ t₃)), this, e']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Set `O : L.ι × L.ι → X.Opens` to `fun p => W ⊓ LB.wchart L (K := Fin 2) ![𝟙 X, t] ![p.1, p.2]`. Establish `hle : ∀ p, O p ≤ t ⁻¹ᵁ (W ⊓ L.U p.2)` using `fun p x hx => ⟨hW hx.1, (mem_twist.1 hx.2).2⟩`. Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) p, r z ∈ O p → gs r z (O p) (rs inf_le_right (u.s ![p.1, p.2]).val * (t.appLE _ _ (hle p)).hom (m p.2)) = (uv u r z p.1 p.2).val * gs (r ≫ t) z _ (m p.2)` using `fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ hz.2 _)) (gs_appLE r t z _ _ _ hz _))`. Take `⟨m', h1, h2⟩` from `glue_sec hL W O Prod.fst (fun _ => inf_le_left) (fun p x hx => (mem_twist.1 hx.2).1) (fun x hx => by`. Take `⟨i, hi⟩` from `exists_chart hL x`.

Take `⟨j, hj⟩` from `exists_chart hL (t x)`. Conclude with `⟨(i, j), hx, mem_twist.2 ⟨hi, hj⟩⟩)`. Use the proof step `(fun p => rs inf_le_right (u.s ![p.1, p.2]).val * (t.appLE _ _ (hle p)).hom (m p.2))`. Use the proof step `(fun p q x hp hq => by`. Establish `hp'` using `mem_twist.1 hp.2`.

Establish `hq'` using `mem_twist.1 hq.2`. Rewrite using `[v _ (𝟙 X) x p hp, v _ (𝟙 X) x q hq, uv_trans hu (𝟙 X) x hp'.1 hp'.2 hq'.1 hq'.2, hm _ (𝟙 X ≫ t) x p.2 q.2 (hW hp.1) hp'.2 hq'.2, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right])`. Use `⟨m', h1, fun Z r z i j hz hi hj => ?_⟩` and prove the remaining obligations. Establish `hp : r z ∈ O (i, j)` using `⟨hz, mem_twist.2 ⟨hi, hj⟩⟩`. Rewrite using `[h2 Z r z i (i, j) hi hp, v Z r z _ hp, gg, gm_self hL r z hi, Units.val_one, one_mul]`.
-/
theorem exists_translate (hL : L.IsLB) {t : X ⟶ X} {u : LB.Gen (twist L t)} (hu : u.IsGen)
    {W : X.Opens} (hW : W ≤ t ⁻¹ᵁ W) {m : ∀ i, Γ(X, W ⊓ L.U i)} (hm : IsLocSec L W m) :
    ∃ m' : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W m' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i j, r z ∈ W → r z ∈ L.U i → (r ≫ t) z ∈ L.U j →
        gs r z _ (m' i) = (uv u r z i j).val * gs (r ≫ t) z _ (m j) := by
  let O : L.ι × L.ι → X.Opens := fun p => W ⊓ LB.wchart L (K := Fin 2) ![𝟙 X, t] ![p.1, p.2]
  have hle : ∀ p, O p ≤ t ⁻¹ᵁ (W ⊓ L.U p.2) := fun p x hx => ⟨hW hx.1, (mem_twist.1 hx.2).2⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) p, r z ∈ O p →
      gs r z (O p) (rs inf_le_right (u.s ![p.1, p.2]).val * (t.appLE _ _ (hle p)).hom (m p.2)) =
        (uv u r z p.1 p.2).val * gs (r ≫ t) z _ (m p.2) := fun Z r z p hz =>
    (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z _ hz _).trans (gs_unit r z _ hz.2 _)) (gs_appLE r t z _ _ _ hz _))
  obtain ⟨m', h1, h2⟩ := glue_sec hL W O Prod.fst (fun _ => inf_le_left)
    (fun p x hx => (mem_twist.1 hx.2).1) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      obtain ⟨j, hj⟩ := exists_chart hL (t x)
      exact ⟨(i, j), hx, mem_twist.2 ⟨hi, hj⟩⟩)
    (fun p => rs inf_le_right (u.s ![p.1, p.2]).val * (t.appLE _ _ (hle p)).hom (m p.2))
    (fun p q x hp hq => by
      have hp' := mem_twist.1 hp.2
      have hq' := mem_twist.1 hq.2
      rw [v _ (𝟙 X) x p hp, v _ (𝟙 X) x q hq, uv_trans hu (𝟙 X) x hp'.1 hp'.2 hq'.1 hq'.2,
        hm _ (𝟙 X ≫ t) x p.2 q.2 (hW hp.1) hp'.2 hq'.2, ← mul_assoc, ← mul_assoc,
        ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right])
  refine ⟨m', h1, fun Z r z i j hz hi hj => ?_⟩
  have hp : r z ∈ O (i, j) := ⟨hz, mem_twist.2 ⟨hi, hj⟩⟩
  rw [h2 Z r z i (i, j) hi hp, v Z r z _ hp, gg, gm_self hL r z hi, Units.val_one, one_mul]

variable {C : Type} {t : C → (X ⟶ X)}

def IsInv (u : ∀ c, LB.Gen (twist L (t c))) (W : X.Opens) (s : ∀ i, Γ(X, W ⊓ L.U i)) : Prop :=
  ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ W → r z ∈ L.U i → (r ≫ t c) z ∈ L.U k →
    gs r z _ (s i) = (uv (u c) r z i k).val * gs (r ≫ t c) z _ (s k)

variable [Group C] [Finite C]

/- English proof (translation)
Use `choose T hT hT' using fun c => exists_translate hL (hu c) (hW c) hm`. Set `s : ∀ i, Γ(X, W ⊓ L.U i)` to `fun i => ∑ c, T c i * ((t c).appLE W _ (inf_le_left.trans (hW c))).hom f`. Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ W → r z ∈ L.U i → gs r z _ (s i) = ∑ c, gs r z _ (T c i) * gs (r ≫ t c) z W f` using `fun Z r z i hz hi => by`. Establish `h : r z ∈ W ⊓ L.U i` using `⟨hz, hi⟩`. Rewrite using `[gs_sum r z _ h]`.

Conclude with `Finset.sum_congr rfl fun c _ => by rw [gs_mul r z _ h, gs_appLE r _ z _ _ _ h]`. Establish `v' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i (j : C → L.ι), r z ∈ W → r z ∈ L.U i → (∀ c, (r ≫ t c) z ∈ L.U (j c)) → gs r z _ (s i) = ∑ c, (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) * gs (r ≫ t c) z W f` using `fun Z r z i j hz hi hj => by`. Rewrite using `[v Z r z i hz hi]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [hT' c Z r z i (j c) hz hi (hj c)]`. Use `⟨s, fun Z r z i j hz hi hj => ?_, fun d Z r z i k hz hi hk => ?_, v'⟩` and prove the remaining obligations.

Rewrite using `[v Z r z i hz hi, v Z r z j hz hj, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [hT c Z r z i j hz hi hj, mul_assoc]`. Use `choose j hj using fun c => exists_chart hL ((r ≫ t c) z)`. Establish `e : ∀ c, (r ≫ t d) ≫ t c = r ≫ t (d * c)` using `fun c => by rw [Category.assoc, ht]`. Rewrite using `[v' Z r z i j hz hi hj, v' Z (r ≫ t d) z k (fun c => j (d * c)) (hW d hz) hk (fun c => by rw [e]; exact hj _), Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft d)]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, e, uv_cocycle hL (ht d c) (hu d) (hu c) (hu _) (hc d c) r z hi hk (hj _), Units.val_mul]`. Simplify using `only [mul_assoc]`.
-/
theorem exists_average [Fintype C] (hL : L.IsLB) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    {W : X.Opens} (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) {m : ∀ i, Γ(X, W ⊓ L.U i)} (hm : IsLocSec L W m)
    (f : Γ(X, W)) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i (j : C → L.ι), r z ∈ W → r z ∈ L.U i →
        (∀ c, (r ≫ t c) z ∈ L.U (j c)) → gs r z _ (s i) = ∑ c,
          (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) * gs (r ≫ t c) z W f := by
  choose T hT hT' using fun c => exists_translate hL (hu c) (hW c) hm
  let s : ∀ i, Γ(X, W ⊓ L.U i) := fun i =>
    ∑ c, T c i * ((t c).appLE W _ (inf_le_left.trans (hW c))).hom f
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ W → r z ∈ L.U i →
      gs r z _ (s i) = ∑ c, gs r z _ (T c i) * gs (r ≫ t c) z W f := fun Z r z i hz hi => by
    have h : r z ∈ W ⊓ L.U i := ⟨hz, hi⟩
    rw [gs_sum r z _ h]
    exact Finset.sum_congr rfl fun c _ => by rw [gs_mul r z _ h, gs_appLE r _ z _ _ _ h]
  have v' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i (j : C → L.ι), r z ∈ W → r z ∈ L.U i →
      (∀ c, (r ≫ t c) z ∈ L.U (j c)) → gs r z _ (s i) = ∑ c,
        (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) * gs (r ≫ t c) z W f :=
    fun Z r z i j hz hi hj => by
      rw [v Z r z i hz hi]
      exact Finset.sum_congr rfl fun c _ => by rw [hT' c Z r z i (j c) hz hi (hj c)]
  refine ⟨s, fun Z r z i j hz hi hj => ?_, fun d Z r z i k hz hi hk => ?_, v'⟩
  · rw [v Z r z i hz hi, v Z r z j hz hj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [hT c Z r z i j hz hi hj, mul_assoc]
  · choose j hj using fun c => exists_chart hL ((r ≫ t c) z)
    have e : ∀ c, (r ≫ t d) ≫ t c = r ≫ t (d * c) := fun c => by rw [Category.assoc, ht]
    rw [v' Z r z i j hz hi hj, v' Z (r ≫ t d) z k (fun c => j (d * c)) (hW d hz) hk
      (fun c => by rw [e]; exact hj _), Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft d)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Equiv.coe_mulLeft, e, uv_cocycle hL (ht d c) (hu d) (hu c) (hu _) (hc d c) r z hi hk (hj _),
      Units.val_mul]
    simp only [mul_assoc]

/- English proof (translation)
Establish `l : ⊤ ≤ r ⁻¹ᵁ W` using `fun z _ => h z`. Establish `l' : ⊤ ≤ r' ⁻¹ᵁ W` using `fun z _ => h' z`. Establish `e' : r.appLE W ⊤ l = r'.appLE W ⊤ l'`. Use extensionality with `f`. Use `fn_ext fun z hz => ?_` and prove the remaining obligations.

Rewrite using `[gs_appLE (𝟙 Z) r z _ _ _ hz, gs_appLE (𝟙 Z) r' z _ _ _ hz, Category.id_comp, Category.id_comp, e]`. Establish `: Epi (isAffineOpen_top Z).fromSpec`. Rewrite using `[IsAffineOpen.fromSpec_top]`. Use `infer_instance`. Rewrite using `[← cancel_epi (isAffineOpen_top Z).fromSpec, ← hW.SpecMap_appLE_fromSpec r (isAffineOpen_top Z) l, e', hW.SpecMap_appLE_fromSpec r' (isAffineOpen_top Z)]`.
-/
theorem hom_ext_of_gs [IsAffine Z] {W : X.Opens} (hW : IsAffineOpen W) {r r' : Z ⟶ X}
    (h : ∀ z, r z ∈ W) (h' : ∀ z, r' z ∈ W) (e : ∀ z f, gs r z W f = gs r' z W f) : r = r' := by
  have l : ⊤ ≤ r ⁻¹ᵁ W := fun z _ => h z
  have l' : ⊤ ≤ r' ⁻¹ᵁ W := fun z _ => h' z
  have e' : r.appLE W ⊤ l = r'.appLE W ⊤ l' := by
    ext f
    refine fn_ext fun z hz => ?_
    rw [gs_appLE (𝟙 Z) r z _ _ _ hz, gs_appLE (𝟙 Z) r' z _ _ _ hz, Category.id_comp,
      Category.id_comp, e]
  have : Epi (isAffineOpen_top Z).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top Z).fromSpec,
    ← hW.SpecMap_appLE_fromSpec r (isAffineOpen_top Z) l, e',
    hW.SpecMap_appLE_fromSpec r' (isAffineOpen_top Z)]

/- English proof (translation)
Consider the cases of `nonempty_fintype C`. Take `⟨m, hm, hm'⟩` from `exists_locSec hL hWa x hx`. Take `⟨k, _, _, r, hr⟩` from `FinEt.exists_algClosed_point X x`. Set `z : Sp k` to `IsLocalRing.closedPoint k`. Take `rfl : r z = x` from `hr.le ⟨z, rfl⟩`.

Establish `hF : IsField ((Sp k).presheaf.stalk z)` using `(stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)`. Establish `hz : ∀ c, (r ≫ t c) z ∈ W` using `fun c => hW c hx`. Establish `hinj : Function.Injective fun c => (gsHom (r ≫ t c) z W (hz c)).toMonoidHom` using `fun c c' e => hfree k r (hom_ext_of_gs hWa (fun z' => Subsingleton.elim z z' ▸ hz c) (fun z' => Subsingleton.elim z z' ▸ hz c') fun z' f => by`. Take `rfl : z = z'` from `Subsingleton.elim _ _`. Rewrite using `[gs_eq_gsHom _ _ _ (hz c), gs_eq_gsHom _ _ _ (hz c')]`.

Conclude with `DFunLike.congr_fun e f)`. Establish `hli` using `(linearIndependent_monoidHom Γ(X, W) ((Sp k).presheaf.stalk z)).comp _ hinj`. Take `⟨i, hi⟩` from `exists_chart hL (r z)`. Use `choose j hj using fun c => exists_chart hL ((r ≫ t c) z)`. Establish `: ∃ f : Γ(X, W), ∑ c, (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) * gs (r ≫ t c) z W f ≠ 0` using `by by_contra! H`.

Establish `h1` using `Fintype.linearIndependent_iff.1 hli (fun c => (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c))) (funext fun f => by`. Rewrite using `[Finset.sum_apply]`. Use `Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (H f)` and prove the remaining obligations. Rewrite using `[gs_eq_gsHom _ _ _ (hz c) f]`. Use the proof step `rfl) 1`.

Establish `h2` using `hj 1`. Rewrite `h2` using `[ht1, Category.comp_id]`. Establish `h3 : IsUnit (gs (r ≫ t 1) z _ (m (j 1)))`. Rewrite using `[ht1, Category.comp_id]`. Conclude with `(isUnit_gs_iff r z (W ⊓ L.U (j 1)) ⟨hx, h2⟩ _).2 (hm' _ h2)`.

Conclude with `((Units.isUnit _).mul h3).ne_zero h1`. Take `⟨f, hf⟩` from `this`. Take `⟨s, h1, h2, h3⟩` from `exists_average hL ht hu hc hW hm f`. Use `⟨s, h1, h2, i, (isUnit_gs_iff r z (W ⊓ L.U i) ⟨hx, hi⟩ _).1 ?_⟩` and prove the remaining obligations. Rewrite using `[h3 _ r z i j hx hi hj]`.

Take `⟨b, hb⟩` from `hF.mul_inv_cancel hf`. Conclude with `IsUnit.of_mul_eq_one _ hb`.
-/
theorem exists_inv_sec (hL : L.IsLB) (ht1 : t 1 = 𝟙 X) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ t c)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    {W : X.Opens} (hWa : IsAffineOpen W) (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) (x : X) (hx : x ∈ W) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∃ i, x ∈ X.basicOpen (s i) := by
  cases nonempty_fintype C
  obtain ⟨m, hm, hm'⟩ := exists_locSec hL hWa x hx
  obtain ⟨k, _, _, r, hr⟩ := FinEt.exists_algClosed_point X x
  let z : Sp k := IsLocalRing.closedPoint k
  obtain rfl : r z = x := hr.le ⟨z, rfl⟩
  have hF : IsField ((Sp k).presheaf.stalk z) :=
    (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hz : ∀ c, (r ≫ t c) z ∈ W := fun c => hW c hx
  have hinj : Function.Injective fun c => (gsHom (r ≫ t c) z W (hz c)).toMonoidHom :=
    fun c c' e => hfree k r (hom_ext_of_gs hWa
      (fun z' => Subsingleton.elim z z' ▸ hz c) (fun z' => Subsingleton.elim z z' ▸ hz c')
      fun z' f => by
        obtain rfl : z = z' := Subsingleton.elim _ _
        rw [gs_eq_gsHom _ _ _ (hz c), gs_eq_gsHom _ _ _ (hz c')]
        exact DFunLike.congr_fun e f)
  have hli := (linearIndependent_monoidHom Γ(X, W) ((Sp k).presheaf.stalk z)).comp _ hinj
  obtain ⟨i, hi⟩ := exists_chart hL (r z)
  choose j hj using fun c => exists_chart hL ((r ≫ t c) z)
  have : ∃ f : Γ(X, W), ∑ c, (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) *
      gs (r ≫ t c) z W f ≠ 0 := by
    by_contra! H
    have h1 := Fintype.linearIndependent_iff.1 hli
      (fun c => (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c))) (funext fun f => by
        rw [Finset.sum_apply]
        refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (H f)
        rw [gs_eq_gsHom _ _ _ (hz c) f]
        rfl) 1
    have h2 := hj 1
    rw [ht1, Category.comp_id] at h2
    have h3 : IsUnit (gs (r ≫ t 1) z _ (m (j 1))) := by
      rw [ht1, Category.comp_id]
      exact (isUnit_gs_iff r z (W ⊓ L.U (j 1)) ⟨hx, h2⟩ _).2 (hm' _ h2)
    exact ((Units.isUnit _).mul h3).ne_zero h1
  obtain ⟨f, hf⟩ := this
  obtain ⟨s, h1, h2, h3⟩ := exists_average hL ht hu hc hW hm f
  refine ⟨s, h1, h2, i, (isUnit_gs_iff r z (W ⊓ L.U i) ⟨hx, hi⟩ _).1 ?_⟩
  rw [h3 _ r z i j hx hi hj]
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hf
  exact IsUnit.of_mul_eq_one _ hb

end Lin

section Desc

variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}

def LocTransitive (t : C → (X ⟶ X)) (π : X ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π → ∀ z : Z,
    ∃ (c : C) (Z' : Scheme.{0}) (a : Z' ⟶ Z) (_ : IsOpenImmersion a) (z' : Z'),
      a z' = z ∧ a ≫ g₁ = (a ≫ g₂) ≫ t c

/- English proof (translation)
Take `⟨z, rfl, rfl⟩` from `Scheme.Pullback.exists_preimage_pullback (f := π) (g := π) x x' e`. Take `⟨c, Z', a, _, z', rfl, h'⟩` from `h _ _ _ (pullback.condition (f := π) (g := π)) z`. Conclude with `⟨c, congrArg (fun q : Z' ⟶ X => q z') h'⟩`.
-/
theorem LocTransitive.exists_apply_eq (h : LocTransitive t π) {x x' : X} (e : π x = π x') :
    ∃ c, x = t c x' := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := π) x x' e
  obtain ⟨c, Z', a, _, z', rfl, h'⟩ := h _ _ _ (pullback.condition (f := π) (g := π)) z
  exact ⟨c, congrArg (fun q : Z' ⟶ X => q z') h'⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `FunDescent.exists_app_eq π V f fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z hz => by`. Rewrite using `[gs_appLE (𝟙 Z) g₁ z _ _ _ hz, gs_appLE (𝟙 Z) g₂ z _ _ _ hz, Category.id_comp, Category.id_comp]`. Take `⟨c, Z', a, _, z', rfl, h'⟩` from `h Z g₁ g₂ e z`. Apply `(ConcreteCategory.bijective_of_isIso (a.stalkMap z')).1` to reduce the goal to its premises. Use `(gs_comp a g₁ z' _ (h₁ hz) f).symm.trans (Eq.trans ?_ (gs_comp a g₂ z' _ (h₂ hz) f))` and prove the remaining obligations.

Rewrite using `[h']`. Conclude with `hf c Z' (a ≫ g₂) z' (h₂ hz)`. Conclude with `⟨a, fun Z r z hz => (gs_pull r π z V hz a).symm⟩`.
-/
theorem LocTransitive.exists_descend [Flat π] [Surjective π] [QuasiCompact π]
    (h : LocTransitive t π) (V : Y.Opens) (f : Γ(X, π ⁻¹ᵁ V))
    (hf : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ t c) z _ f = gs r z _ f) :
    ∃ a : Γ(Y, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ π) z V a = gs r z _ f := by
  obtain ⟨a, rfl⟩ := FunDescent.exists_app_eq π V f fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z hz => by
    rw [gs_appLE (𝟙 Z) g₁ z _ _ _ hz, gs_appLE (𝟙 Z) g₂ z _ _ _ hz, Category.id_comp,
      Category.id_comp]
    obtain ⟨c, Z', a, _, z', rfl, h'⟩ := h Z g₁ g₂ e z
    apply (ConcreteCategory.bijective_of_isIso (a.stalkMap z')).1
    refine (gs_comp a g₁ z' _ (h₁ hz) f).symm.trans (Eq.trans ?_ (gs_comp a g₂ z' _ (h₂ hz) f))
    rw [h']
    exact hf c Z' (a ≫ g₂) z' (h₂ hz)
  exact ⟨a, fun Z r z hz => (gs_pull r π z V hz a).symm⟩

/- English proof (translation)
Use `Units.ext (FunDescent.app_injective π V (fn_ext fun x hx => ?_))` and prove the remaining obligations. Rewrite using `[gs_pull (𝟙 X) π x V hx, gs_pull (𝟙 X) π x V hx, gs_unit (𝟙 X ≫ π) x V hx, gs_unit (𝟙 X ≫ π) x V hx, h x hx]`.
-/
theorem unit_ext_of_flat [Flat π] [Surjective π] {V : Y.Opens} {a b : Γ(Y, V)ˣ}
    (h : ∀ x, π x ∈ V → gm (𝟙 X ≫ π) x V a = gm (𝟙 X ≫ π) x V b) : a = b := by
  refine Units.ext (FunDescent.app_injective π V (fn_ext fun x hx => ?_))
  rw [gs_pull (𝟙 X) π x V hx, gs_pull (𝟙 X) π x V hx, gs_unit (𝟙 X ≫ π) x V hx,
    gs_unit (𝟙 X ≫ π) x V hx, h x hx]

def IsInvGen (u : ∀ c, LB.Gen (twist L (t c))) (W : X.Opens) (e : ∀ i, Γ(X, W ⊓ L.U i)ˣ) : Prop :=
  (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i j, r z ∈ W → r z ∈ L.U i → r z ∈ L.U j →
    gm r z _ (e i) = gg L r z i j * gm r z _ (e j)) ∧
  ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ W → r z ∈ L.U i →
    (r ≫ t c) z ∈ L.U k → gm r z _ (e i) = uv (u c) r z i k * gm (r ≫ t c) z _ (e k)

/- English proof (translation)
Establish `hmem : ∀ (U : Y.Opens) c {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ U → (r ≫ t c) z ∈ π ⁻¹ᵁ U` using `fun U c Z r z hz => by`. Express the relevant statement in the definitionally equal form `((r ≫ t c) ≫ π) z ∈ U`. Rewrite using `[Category.assoc, hπ]`. Conclude with `hz`. Establish `H : ∀ y y', ∃ g : Γ(Y, V y ⊓ V y')ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V y → r z ∈ π ⁻¹ᵁ V y' → r z ∈ L.U i → gm (r ≫ π) z _ g = gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹` using `fun y y' => by`.

Set `O : L.ι → X.Opens` to `fun i => π ⁻¹ᵁ (V y ⊓ V y') ⊓ L.U i`. Establish `l : ∀ i, O i ≤ π ⁻¹ᵁ V y ⊓ L.U i` using `fun i x hx => ⟨hx.1.1, hx.2⟩`. Establish `l' : ∀ i, O i ≤ π ⁻¹ᵁ V y' ⊓ L.U i` using `fun i x hx => ⟨hx.1.2, hx.2⟩`. Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ O i → gs r z (O i) (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val` using `fun Z r z i hz => by`. Rewrite using `[gs_unit r z _ hz, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]`.

Take `⟨ρ, hρ⟩` from `glue_fn (π ⁻¹ᵁ (V y ⊓ V y')) O (fun _ => inf_le_left) (fun x hx => (exists_chart hL x).imp fun i hi => ⟨hx, hi⟩) (fun i => (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val) (fun i j x hi hj => by`. Rewrite using `[v _ (𝟙 X) x i hi, v _ (𝟙 X) x j hj, (he y).1 _ (𝟙 X) x i j hi.1.1 hi.2 hj.2, (he y').1 _ (𝟙 X) x i j hi.1.2 hi.2 hj.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])`. Establish `hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ (V y ⊓ V y') → r z ∈ L.U i → gs r z _ ρ = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val` using `fun Z r z i h1 h2 => (hρ Z r z i ⟨h1, h2⟩).trans (v Z r z i ⟨h1, h2⟩)`. Take `⟨a, ha⟩` from `h.exists_descend (V y ⊓ V y') ρ fun c Z r z hz => by`. Take `⟨i, hi⟩` from `exists_chart hL (r z)`.

Take `⟨k, hk⟩` from `exists_chart hL ((r ≫ t c) z)`. Rewrite using `[hρ' Z r z i hz hi, hρ' Z (r ≫ t c) z k (hmem _ c r z hz) hk, (he y).2 c Z r z i k hz.1 hi hk, (he y').2 c Z r z i k hz.2 hi hk, ← div_eq_mul_inv (_ * _), mul_div_mul_left_eq_div, div_eq_mul_inv]`. Establish `hu : IsUnit a` using `isUnit_of_mem_basicOpen a fun b hb => by`. Take `⟨x, rfl⟩` from `π.surjective b`. Take `⟨i, hi⟩` from `exists_chart hL x`.

Use `(isUnit_gs_iff (𝟙 X ≫ π) x (V y ⊓ V y') hb a).1 ?_` and prove the remaining obligations. Rewrite using `[ha _ (𝟙 X) x hb, hρ' _ (𝟙 X) x i hb hi]`. Conclude with `Units.isUnit _`. Use `⟨hu.unit, fun Z r z i h1 h2 hi => Units.ext ?_⟩` and prove the remaining obligations. Conclude with `(gs_unit (r ≫ π) z (V y ⊓ V y') ⟨h1, h2⟩ hu.unit).symm.trans ((ha Z r z ⟨h1, h2⟩).trans (hρ' Z r z i ⟨h1, h2⟩ hi))`.

Use `choose g hg using H`. Set `M : LB Y` to `⟨Y, V, g⟩`. Use `⟨M, ⟨eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩, fun y => ?_, fun y₁ y₂ y₃ => ?_⟩, ?_⟩` and prove the remaining obligations. Use `unit_ext_of_flat (π := π) fun x hx => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hL x`.

Use `(gm_res (𝟙 X ≫ π) x _ hx _).trans ((hg y y _ (𝟙 X) x i hx hx hi).trans ?_)` and prove the remaining obligations. Rewrite using `[mul_inv_cancel, map_one]`. Use `unit_ext_of_flat (π := π) fun x hx => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hL x`. Use `((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₂ _ (𝟙 X) x i hx.1.1 hx.1.2 hi)) ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₂ y₃ _ (𝟙 X) x i hx.1.2 hx.2 hi)))).trans (Eq.trans ?_ ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₃ _ (𝟙 X) x i hx.1.1 hx. …` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel_left]`. Establish `l : ∀ p : (PUnit → Y) × L.ι, (M.pull π).U p.1 ⊓ L.U p.2 ≤ π ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2` using `fun p x hx => ⟨mem_pull.1 hx.1, hx.2⟩`. Set `w : LB.Iso L (M.pull π)` to `⟨fun p => (res (l p) (e (p.1 PUnit.unit) p.2))⁻¹⟩`. Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (y : Y) i, π (r z) ∈ V y → r z ∈ L.U i → gw w r z y i = (gm r z _ (e y i))⁻¹` using `fun Z r z y i h1 h2 => (map_inv _ _).trans (congrArg _ (gm_res r z (l (fun _ => y, i)) ⟨(mem_pull (L := M)).2 h1, h2⟩ _))`. Use `⟨w, (isGen_iff w).2 fun Z r z y y' i i' h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations.

Rewrite using `[v Z r z y i h1 h3, v Z r z y' i' h2 h4]`. Use `Eq.trans ?_ (congrArg (· * _ * _) (hg y y' Z r z i' h1 h2 h4)).symm` and prove the remaining obligations. Rewrite using `[(he y).1 Z r z i i' h1 h3 h4]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`.

Normalize the expressions using the abelian group laws.
-/
theorem exists_descent_of_invGen [Flat π] [Surjective π] [QuasiCompact π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : LocTransitive t π) {u : ∀ c, LB.Gen (twist L (t c))}
    (V : Y → Y.Opens) (hV : ∀ y, y ∈ V y) (e : ∀ y i, Γ(X, π ⁻¹ᵁ V y ⊓ L.U i)ˣ)
    (he : ∀ y, IsInvGen u (π ⁻¹ᵁ V y) (e y)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have hmem : ∀ (U : Y.Opens) c {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ U →
      (r ≫ t c) z ∈ π ⁻¹ᵁ U := fun U c Z r z hz => by
    change ((r ≫ t c) ≫ π) z ∈ U
    rw [Category.assoc, hπ]
    exact hz
  have H : ∀ y y', ∃ g : Γ(Y, V y ⊓ V y')ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i,
      r z ∈ π ⁻¹ᵁ V y → r z ∈ π ⁻¹ᵁ V y' → r z ∈ L.U i →
      gm (r ≫ π) z _ g = gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹ := fun y y' => by
    let O : L.ι → X.Opens := fun i => π ⁻¹ᵁ (V y ⊓ V y') ⊓ L.U i
    have l : ∀ i, O i ≤ π ⁻¹ᵁ V y ⊓ L.U i := fun i x hx => ⟨hx.1.1, hx.2⟩
    have l' : ∀ i, O i ≤ π ⁻¹ᵁ V y' ⊓ L.U i := fun i x hx => ⟨hx.1.2, hx.2⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ O i →
        gs r z (O i) (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val =
        (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val := fun Z r z i hz => by
      rw [gs_unit r z _ hz, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
    obtain ⟨ρ, hρ⟩ := glue_fn (π ⁻¹ᵁ (V y ⊓ V y')) O (fun _ => inf_le_left)
      (fun x hx => (exists_chart hL x).imp fun i hi => ⟨hx, hi⟩)
      (fun i => (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val) (fun i j x hi hj => by
        rw [v _ (𝟙 X) x i hi, v _ (𝟙 X) x j hj, (he y).1 _ (𝟙 X) x i j hi.1.1 hi.2 hj.2,
          (he y').1 _ (𝟙 X) x i j hi.1.2 hi.2 hj.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div,
          div_eq_mul_inv])
    have hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ (V y ⊓ V y') →
        r z ∈ L.U i → gs r z _ ρ = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val :=
      fun Z r z i h1 h2 => (hρ Z r z i ⟨h1, h2⟩).trans (v Z r z i ⟨h1, h2⟩)
    obtain ⟨a, ha⟩ := h.exists_descend (V y ⊓ V y') ρ fun c Z r z hz => by
      obtain ⟨i, hi⟩ := exists_chart hL (r z)
      obtain ⟨k, hk⟩ := exists_chart hL ((r ≫ t c) z)
      rw [hρ' Z r z i hz hi, hρ' Z (r ≫ t c) z k (hmem _ c r z hz) hk,
        (he y).2 c Z r z i k hz.1 hi hk, (he y').2 c Z r z i k hz.2 hi hk,
        ← div_eq_mul_inv (_ * _), mul_div_mul_left_eq_div, div_eq_mul_inv]
    have hu : IsUnit a := isUnit_of_mem_basicOpen a fun b hb => by
      obtain ⟨x, rfl⟩ := π.surjective b
      obtain ⟨i, hi⟩ := exists_chart hL x
      refine (isUnit_gs_iff (𝟙 X ≫ π) x (V y ⊓ V y') hb a).1 ?_
      rw [ha _ (𝟙 X) x hb, hρ' _ (𝟙 X) x i hb hi]
      exact Units.isUnit _
    refine ⟨hu.unit, fun Z r z i h1 h2 hi => Units.ext ?_⟩
    exact (gs_unit (r ≫ π) z (V y ⊓ V y') ⟨h1, h2⟩ hu.unit).symm.trans
      ((ha Z r z ⟨h1, h2⟩).trans (hρ' Z r z i ⟨h1, h2⟩ hi))
  choose g hg using H
  let M : LB Y := ⟨Y, V, g⟩
  refine ⟨M, ⟨eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩, fun y => ?_,
    fun y₁ y₂ y₃ => ?_⟩, ?_⟩
  · refine unit_ext_of_flat (π := π) fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine (gm_res (𝟙 X ≫ π) x _ hx _).trans ((hg y y _ (𝟙 X) x i hx hx hi).trans ?_)
    rw [mul_inv_cancel, map_one]
  · refine unit_ext_of_flat (π := π) fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₂ _ (𝟙 X) x i hx.1.1 hx.1.2 hi))
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₂ y₃ _ (𝟙 X) x i hx.1.2 hx.2 hi)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 X ≫ π) x _ hx _).trans
        (hg y₁ y₃ _ (𝟙 X) x i hx.1.1 hx.2 hi)).symm)
    rw [mul_comm, mul_assoc, inv_mul_cancel_left]
  · have l : ∀ p : (PUnit → Y) × L.ι, (M.pull π).U p.1 ⊓ L.U p.2 ≤
        π ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.1 hx.1, hx.2⟩
    let w : LB.Iso L (M.pull π) := ⟨fun p => (res (l p) (e (p.1 PUnit.unit) p.2))⁻¹⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (y : Y) i, π (r z) ∈ V y → r z ∈ L.U i →
        gw w r z y i = (gm r z _ (e y i))⁻¹ := fun Z r z y i h1 h2 =>
      (map_inv _ _).trans (congrArg _ (gm_res r z (l (fun _ => y, i))
        ⟨(mem_pull (L := M)).2 h1, h2⟩ _))
    refine ⟨w, (isGen_iff w).2 fun Z r z y y' i i' h1 h2 h3 h4 => ?_⟩
    rw [v Z r z y i h1 h3, v Z r z y' i' h2 h4]
    refine Eq.trans ?_ (congrArg (· * _ * _) (hg y y' Z r z i' h1 h2 h4)).symm
    rw [(he y).1 Z r z i i' h1 h3 h4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/- English proof (translation)
Establish `H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e, IsInvGen u (π ⁻¹ᵁ V) e` using `fun y => by`. Take `⟨x, rfl⟩` from `π.surjective y`. Take `⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π x)) isOpen_univ`. Establish `hinv : ∀ (V : Y.Opens) c, π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ π ⁻¹ᵁ V` using `fun V c => by`. Rewrite using `[← Scheme.Hom.comp_preimage, hπ]`.

Take `⟨s, h1, h2, i₀, h3⟩` from `exists_inv_sec hL ht1 ht hfree hu hc (IsAffineOpen.preimage hV₀ π) (hinv V₀) x hx`. Set `N : X.Opens` to `⨆ i, X.basicOpen (s i)`. Set `V : Y.Opens` to `⟨(π '' (N : Set X)ᶜ)ᶜ, (π.isClosedMap _ N.isOpen.isClosed_compl).isOpen_compl⟩`. Establish `hN : ∀ x', x' ∈ π ⁻¹ᵁ V → ∃ i, x' ∈ X.basicOpen (s i)` using `fun x' hx' => by`. Assume the negation of the conclusion as `hh`.

Conclude with `hx' ⟨x', fun hh' => hh (Opens.mem_iSup.1 hh'), rfl⟩`. Establish `hN' : ∀ x', x' ∈ π ⁻¹ᵁ V → x' ∈ π ⁻¹ᵁ V₀` using `fun x' hx' => by`. Take `⟨i, hi⟩` from `hN x' hx'`. Conclude with `(X.basicOpen_le _ hi).1`. Establish `l : ∀ i, π ⁻¹ᵁ V ⊓ L.U i ≤ π ⁻¹ᵁ V₀ ⊓ L.U i` using `fun i x' hx' => ⟨hN' x' hx'.1, hx'.2⟩`.

Establish `hu' : ∀ i, IsUnit (rs (l i) (s i))` using `fun i => isUnit_of_mem_basicOpen _ fun x' hx' => by`. Take `⟨j, hj⟩` from `hN x' hx'.1`. Establish `hj'` using `X.basicOpen_le _ hj`. Use `(isUnit_gs_iff (𝟙 X) x' _ hx' _).1 ?_` and prove the remaining obligations. Rewrite using `[gs_res (𝟙 X) x' _ hx', h1 _ (𝟙 X) x' i j hj'.1 hx'.2 hj'.2]`.

Conclude with `(Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X) x' _ hj' _).2 hj)`. Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V → r z ∈ L.U i → (gm r z _ (hu' i).unit).val = gs r z _ (s i)` using `fun Z r z i a b => (gs_unit r z (π ⁻¹ᵁ V ⊓ L.U i) ⟨a, b⟩ _).symm.trans (gs_res r z (l i) ⟨a, b⟩ _)`. Use `⟨V, ?_, fun i => (hu' i).unit, fun Z r z i j a b c => Units.ext ?_, fun c Z r z i k a b d => Units.ext ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x', hx', e⟩`. Take `⟨c, rfl⟩` from `h.exists_apply_eq e`.

Take `⟨k, hk⟩` from `exists_chart hL (t c x)`. Establish `h4` using `X.basicOpen_le _ h3`. Establish `h5` using `(isUnit_gs_iff (𝟙 X) x _ h4 _).2 h3`. Rewrite `h5` using `[h2 c _ (𝟙 X) x i₀ k hx h4.2 hk]`. Conclude with `hx' (Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff (𝟙 X ≫ t c) x (π ⁻¹ᵁ V₀ ⊓ L.U k) ⟨hinv V₀ c hx, hk⟩ _).1 (isUnit_of_mul_isUnit_right h5)⟩)`.

Rewrite using `[Units.val_mul, v Z r z i a b, v Z r z j a c]`. Conclude with `h1 Z r z i j (hN' _ a) b c`. Rewrite using `[Units.val_mul, v Z r z i a b, v Z (r ≫ t c) z k (hinv V c a) d]`. Conclude with `h2 c Z r z i k (hN' _ a) b d`. Use `choose V hV e he using H`.

Conclude with `exists_descent_of_invGen hL hπ h V hV e he`.
-/
theorem exists_descent_of_galois [Group C] [Finite C] [IsFinite π] [Flat π] [Surjective π]
    (hL : L.IsLB) (ht1 : t 1 = 𝟙 X) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hπ : ∀ c, t c ≫ π = π) (h : LocTransitive t π)
    (hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ t c)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c)))) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e, IsInvGen u (π ⁻¹ᵁ V) e := fun y => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (π x)) isOpen_univ
    have hinv : ∀ (V : Y.Opens) c, π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ π ⁻¹ᵁ V := fun V c => by
      rw [← Scheme.Hom.comp_preimage, hπ]
    obtain ⟨s, h1, h2, i₀, h3⟩ := exists_inv_sec hL ht1 ht hfree hu hc
      (IsAffineOpen.preimage hV₀ π) (hinv V₀) x hx
    let N : X.Opens := ⨆ i, X.basicOpen (s i)
    let V : Y.Opens := ⟨(π '' (N : Set X)ᶜ)ᶜ, (π.isClosedMap _ N.isOpen.isClosed_compl).isOpen_compl⟩
    have hN : ∀ x', x' ∈ π ⁻¹ᵁ V → ∃ i, x' ∈ X.basicOpen (s i) := fun x' hx' => by
      by_contra hh
      exact hx' ⟨x', fun hh' => hh (Opens.mem_iSup.1 hh'), rfl⟩
    have hN' : ∀ x', x' ∈ π ⁻¹ᵁ V → x' ∈ π ⁻¹ᵁ V₀ := fun x' hx' => by
      obtain ⟨i, hi⟩ := hN x' hx'
      exact (X.basicOpen_le _ hi).1
    have l : ∀ i, π ⁻¹ᵁ V ⊓ L.U i ≤ π ⁻¹ᵁ V₀ ⊓ L.U i := fun i x' hx' => ⟨hN' x' hx'.1, hx'.2⟩
    have hu' : ∀ i, IsUnit (rs (l i) (s i)) := fun i => isUnit_of_mem_basicOpen _ fun x' hx' => by
      obtain ⟨j, hj⟩ := hN x' hx'.1
      have hj' := X.basicOpen_le _ hj
      refine (isUnit_gs_iff (𝟙 X) x' _ hx' _).1 ?_
      rw [gs_res (𝟙 X) x' _ hx', h1 _ (𝟙 X) x' i j hj'.1 hx'.2 hj'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X) x' _ hj' _).2 hj)
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V → r z ∈ L.U i →
        (gm r z _ (hu' i).unit).val = gs r z _ (s i) := fun Z r z i a b =>
      (gs_unit r z (π ⁻¹ᵁ V ⊓ L.U i) ⟨a, b⟩ _).symm.trans (gs_res r z (l i) ⟨a, b⟩ _)
    refine ⟨V, ?_, fun i => (hu' i).unit, fun Z r z i j a b c => Units.ext ?_,
      fun c Z r z i k a b d => Units.ext ?_⟩
    · rintro ⟨x', hx', e⟩
      obtain ⟨c, rfl⟩ := h.exists_apply_eq e
      obtain ⟨k, hk⟩ := exists_chart hL (t c x)
      have h4 := X.basicOpen_le _ h3
      have h5 := (isUnit_gs_iff (𝟙 X) x _ h4 _).2 h3
      rw [h2 c _ (𝟙 X) x i₀ k hx h4.2 hk] at h5
      exact hx' (Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff (𝟙 X ≫ t c) x (π ⁻¹ᵁ V₀ ⊓ L.U k)
        ⟨hinv V₀ c hx, hk⟩ _).1 (isUnit_of_mul_isUnit_right h5)⟩)
    · rw [Units.val_mul, v Z r z i a b, v Z r z j a c]
      exact h1 Z r z i j (hN' _ a) b c
    · rw [Units.val_mul, v Z r z i a b, v Z (r ≫ t c) z k (hinv V c a) d]
      exact h2 c Z r z i k (hN' _ a) b d
  choose V hV e he using H
  exact exists_descent_of_invGen hL hπ h V hV e he

end Desc

section Grp

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

/- English proof (translation)
Rewrite using `[MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]`.
-/
theorem comp_transl {T : Over S} (x : T ⟶ A) (y : 𝟙_ (Over S) ⟶ A) :
    x ≫ ((toUnit A ≫ y) * 𝟙 A) = (toUnit T ≫ y) * x := by
  rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

/- English proof (translation)
Establish `hone : ∀ {Z : Over S}, (1 : Z ⟶ B).left = Z.hom ≫ η[B].left` using `fun {Z} => by`. Rewrite using `[Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression. Establish `hη : η[B].left ≫ B.hom = 𝟙 _` using `Over.w η[B]`. Establish `hker : ∀ {Z : Over S} (d : Z ⟶ A), d ≫ ψ = 1 → d.left ≫ ψ.left = Z.hom ≫ η[B].left` using `fun d hd => by rw [← Over.comp_left, hd, hone]`.

Set `l : Z.left ⟶ pullback ψ.left η[B].left` to `pullback.lift _ _ (hker d hd)`. Take `⟨k, _, _, q, hq⟩` from `FinEt.exists_algClosed_point _ (l p)`. Establish `hw : (q ≫ pullback.fst ψ.left η[B].left) ≫ A.hom = q ≫ pullback.snd ψ.left η[B].left`. Rewrite using `[← Over.w ψ, Category.assoc, pullback.condition_assoc]`. Use `erw [hη]`.

Conclude with `congrArg (q ≫ ·) (Category.comp_id _)`. Take `⟨c, hc⟩` from `hk k (q ≫ pullback.snd ψ.left η[B].left) (Over.homMk _ hw) (by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hone]`. Express the relevant statement in the definitionally equal form `(q ≫ pullback.fst ψ.left η[B].left) ≫ ψ.left = (q ≫ pullback.snd ψ.left η[B].left) ≫ η[B].left`.

Rewrite using `[Category.assoc, pullback.condition, Category.assoc])`. Establish `hc' : q ≫ pullback.fst ψ.left η[B].left = (q ≫ pullback.snd ψ.left η[B].left) ≫ (i c).left` using `congrArg (·.left) hc`. Set `s : (𝟙_ (Over S)).left ⟶ pullback ψ.left η[B].left` to `pullback.lift (i c).left (𝟙 _) (hker (i c) (hi c))`. Establish `hs : s ≫ pullback.snd ψ.left η[B].left = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `hs' : s ≫ pullback.fst ψ.left η[B].left = (i c).left` using `pullback.lift_fst _ _ _`.

Establish `hqs : (q ≫ pullback.snd ψ.left η[B].left) ≫ s = q`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hs', hc']`. Rewrite using `[Category.assoc, hs, Category.comp_id]`. Use `isOpenImmersion_of_section_of_etale (pullback.snd ψ.left η[B].left) s hs` as an intermediate fact.

Take `⟨z, hz⟩ : l p ∈ Set.range q` from `hq.ge rfl`. Establish `ht : l p = s ((q ≫ pullback.snd ψ.left η[B].left) z)`. Rewrite using `[← Scheme.Hom.comp_apply, hqs, hz]`. Use `⟨c, Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl, inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p _ ht`.

Conclude with `⟨w, hw⟩`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pullback.fst l s ≫ d.left = (pullback.fst l s ≫ Z.hom) ≫ (i c).left`. Establish `h1 : d.left = l ≫ pullback.fst ψ.left η[B].left` using `(pullback.lift_fst _ _ _).symm`. Establish `h2 : Z.hom = l ≫ pullback.snd ψ.left η[B].left` using `(pullback.lift_snd _ _ _).symm`.

Establish `h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s`. Rewrite using `[h2, pullback.condition_assoc]`. Conclude with `(congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)`. Rewrite using `[h3, h1, pullback.condition_assoc, hs']`.
-/
theorem exists_local_section (ψ : A ⟶ B) [Etale ψ.left] {C : Type} (i : C → (𝟙_ (Over S) ⟶ A))
    (hi : ∀ c, i c ≫ ψ = 1)
    (hk : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A),
      x ≫ ψ = 1 → ∃ c, x = toUnit _ ≫ i c)
    {Z : Over S} (d : Z ⟶ A) (hd : d ≫ ψ = 1) (p : Z.left) :
    ∃ (c : C) (W : Over S) (a : W ⟶ Z) (_ : IsOpenImmersion a.left),
      p ∈ Set.range a.left ∧ a ≫ d = toUnit W ≫ i c := by
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ B).left = Z.hom ≫ η[B].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  have hη : η[B].left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hker : ∀ {Z : Over S} (d : Z ⟶ A), d ≫ ψ = 1 → d.left ≫ ψ.left = Z.hom ≫ η[B].left :=
    fun d hd => by rw [← Over.comp_left, hd, hone]
  let l : Z.left ⟶ pullback ψ.left η[B].left := pullback.lift _ _ (hker d hd)
  obtain ⟨k, _, _, q, hq⟩ := FinEt.exists_algClosed_point _ (l p)
  have hw : (q ≫ pullback.fst ψ.left η[B].left) ≫ A.hom = q ≫ pullback.snd ψ.left η[B].left := by
    rw [← Over.w ψ, Category.assoc, pullback.condition_assoc]
    erw [hη]
    exact congrArg (q ≫ ·) (Category.comp_id _)
  obtain ⟨c, hc⟩ := hk k (q ≫ pullback.snd ψ.left η[B].left) (Over.homMk _ hw) (by
    apply Over.OverMorphism.ext
    rw [hone]
    change (q ≫ pullback.fst ψ.left η[B].left) ≫ ψ.left =
      (q ≫ pullback.snd ψ.left η[B].left) ≫ η[B].left
    rw [Category.assoc, pullback.condition, Category.assoc])
  have hc' : q ≫ pullback.fst ψ.left η[B].left =
      (q ≫ pullback.snd ψ.left η[B].left) ≫ (i c).left := congrArg (·.left) hc
  let s : (𝟙_ (Over S)).left ⟶ pullback ψ.left η[B].left :=
    pullback.lift (i c).left (𝟙 _) (hker (i c) (hi c))
  have hs : s ≫ pullback.snd ψ.left η[B].left = 𝟙 _ := pullback.lift_snd _ _ _
  have hs' : s ≫ pullback.fst ψ.left η[B].left = (i c).left := pullback.lift_fst _ _ _
  have hqs : (q ≫ pullback.snd ψ.left η[B].left) ≫ s = q := by
    apply pullback.hom_ext
    · rw [Category.assoc, hs', hc']
    · rw [Category.assoc, hs, Category.comp_id]
  have := isOpenImmersion_of_section_of_etale (pullback.snd ψ.left η[B].left) s hs
  obtain ⟨z, hz⟩ : l p ∈ Set.range q := hq.ge rfl
  have ht : l p = s ((q ≫ pullback.snd ψ.left η[B].left) z) := by
    rw [← Scheme.Hom.comp_apply, hqs, hz]
  refine ⟨c, Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, ?_⟩
  · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p _ ht
    exact ⟨w, hw⟩
  · apply Over.OverMorphism.ext
    change pullback.fst l s ≫ d.left = (pullback.fst l s ≫ Z.hom) ≫ (i c).left
    have h1 : d.left = l ≫ pullback.fst ψ.left η[B].left := (pullback.lift_fst _ _ _).symm
    have h2 : Z.hom = l ≫ pullback.snd ψ.left η[B].left := (pullback.lift_snd _ _ _).symm
    have h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s := by
      rw [h2, pullback.condition_assoc]
      exact (congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)
    rw [h3, h1, pullback.condition_assoc, hs']

end Grp

end GlobalTheory.LinDescent

namespace GlobalTheory.LinDescent

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

/- English proof (translation)
Introduce `S A B _ _ ψ C _ _ i L hL hψ _ _ _ hi hk u hu hc`. Use `exists_descent_of_galois (t := fun c => ((toUnit A ≫ i c) * 𝟙 A).left) hL ?_ (fun c c' => ?_) (fun c => ?_) (fun Z g₁ g₂ e z => ?_) (fun k _ _ r c c' e => ?_) hu hc` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[map_one, MonObj.comp_one, _root_.one_mul, Over.id_left]`. Rewrite using `[← Over.comp_left, comp_transl, ← _root_.mul_assoc, ← MonObj.comp_mul, ← map_mul, mul_comm c']`.

Rewrite using `[← Over.comp_left, MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul, Category.id_comp]`. Set `Z' : Over S` to `Over.mk (g₂ ≫ A.hom)`. Set `k₂ : Z' ⟶ A` to `Over.homMk g₂ rfl`. Set `k₁ : Z' ⟶ A` to `Over.homMk g₁ (by`. Express the relevant statement in the definitionally equal form `g₁ ≫ A.hom = g₂ ≫ A.hom`.

Rewrite using `[← Over.w ψ, reassoc_of% e])`. Establish `e' : k₁ ≫ ψ = k₂ ≫ ψ` using `Over.OverMorphism.ext e`. Take `⟨c, W, a, ha, ⟨w, hw⟩, h⟩` from `exists_local_section ψ i hi (fun k _ _ t x hx => ((hk k t).1 x).1 hx) (k₁ * k₂⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]) z`. Rewrite `h` using `[MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul, ← comp_transl]`. Conclude with `⟨c, W.left, a.left, ha, w, hw, congrArg (·.left) h⟩`.

Set `x : Over.mk (r ≫ A.hom) ⟶ A` to `Over.homMk r rfl`. Establish `e' : x ≫ ((toUnit A ≫ i c) * 𝟙 A) = x ≫ ((toUnit A ≫ i c') * 𝟙 A)` using `Over.OverMorphism.ext e`. Rewrite `e'` using `[comp_transl, comp_transl, mul_left_inj, ← mul_inv_eq_one, ← GrpObj.comp_inv, ← MonObj.comp_mul, ← map_inv, ← map_mul]`. Conclude with `mul_inv_eq_one.1 ((hk k _).2 _ e')`.
-/
theorem exists_descent :
    ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ c, i c ≫ ψ = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])), (∀ c, (u c).IsGen) → (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) := by
  intro S A B _ _ ψ C _ _ i L hL hψ _ _ _ hi hk u hu hc
  refine exists_descent_of_galois (t := fun c => ((toUnit A ≫ i c) * 𝟙 A).left) hL ?_
    (fun c c' => ?_) (fun c => ?_) (fun Z g₁ g₂ e z => ?_) (fun k _ _ r c c' e => ?_) hu hc
  · beta_reduce
    rw [map_one, MonObj.comp_one, _root_.one_mul, Over.id_left]
  · rw [← Over.comp_left, comp_transl, ← _root_.mul_assoc, ← MonObj.comp_mul, ← map_mul, mul_comm c']
  · rw [← Over.comp_left, MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul,
      Category.id_comp]
  · let Z' : Over S := Over.mk (g₂ ≫ A.hom)
    let k₂ : Z' ⟶ A := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ A := Over.homMk g₁ (by
      change g₁ ≫ A.hom = g₂ ≫ A.hom
      rw [← Over.w ψ, reassoc_of% e])
    have e' : k₁ ≫ ψ = k₂ ≫ ψ := Over.OverMorphism.ext e
    obtain ⟨c, W, a, ha, ⟨w, hw⟩, h⟩ := exists_local_section ψ i hi
      (fun k _ _ t x hx => ((hk k t).1 x).1 hx) (k₁ * k₂⁻¹)
      (by rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]) z
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul, ← comp_transl] at h
    exact ⟨c, W.left, a.left, ha, w, hw, congrArg (·.left) h⟩
  · let x : Over.mk (r ≫ A.hom) ⟶ A := Over.homMk r rfl
    have e' : x ≫ ((toUnit A ≫ i c) * 𝟙 A) = x ≫ ((toUnit A ≫ i c') * 𝟙 A) :=
      Over.OverMorphism.ext e
    rw [comp_transl, comp_transl, mul_left_inj, ← mul_inv_eq_one, ← GrpObj.comp_inv,
      ← MonObj.comp_mul, ← map_inv, ← map_mul] at e'
    exact mul_inv_eq_one.1 ((hk k _).2 _ e')

/- English proof (translation)
Establish `hη : η[B].left ≫ B.hom = 𝟙 S` using `Over.w η[B]`. Establish `hy : y.left ≫ B.hom = 𝟙 S` using `Over.w y`. Establish `: IsImmersion (η[B].left ≫ B.hom)` using `hη ▸ (inferInstance : IsImmersion (𝟙 S))`. Establish `: IsImmersion η[B].left` using `IsImmersion.of_comp _ B.hom`. Set `p : pullback y.left η[B].left ⟶ S` to `pullback.fst y.left η[B].left`.

Establish `: IsImmersion p` using `inferInstanceAs (IsImmersion (pullback.fst y.left η[B].left))`. Establish `: Surjective p` using `⟨fun s => by`. Take `⟨k, _, _, t, ht⟩` from `FinEt.exists_algClosed_point S s`. Establish `e : t ≫ y.left = t ≫ η[B].left` using `congrArg (·.left) ((h k t).trans Hom.one_def)`. Take `⟨z, hz⟩ : s ∈ Set.range t` from `ht.ge rfl`.

Use `⟨pullback.lift t t e z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← hz]`. Conclude with `congrArg (fun q : Spec (CommRingCat.of k) ⟶ S => q z) (pullback.lift_fst _ _ _)⟩`. Establish `: IsClosedImmersion p` using `.of_isPreimmersion _ (by`. Rewrite using `[p.surjective.range_eq]`.

Conclude with `isClosed_univ)`. Establish `: IsIso p` using `isIso_of_isClosedImmersion_of_surjective p`. Establish `e : p ≫ y.left = pullback.snd y.left η[B].left ≫ η[B].left` using `pullback.condition`. Establish `e' : p = pullback.snd y.left η[B].left`. Use `e =≫ B.hom` as an intermediate fact.

Rewrite `this` using `[Category.assoc, Category.assoc, hy, hη]`. Conclude with `(Category.comp_id _).symm.trans (this.trans (Category.comp_id _))`. Rewrite `e` using `[← e', cancel_epi]`. Rewrite using `[Hom.one_def, toUnit_unit, Category.id_comp]`. Conclude with `Over.OverMorphism.ext e`.
-/
theorem section_eq_one_of_isReduced {S : Scheme.{0}} [IsReduced S] {B : Over S} [GrpObj B]
    (y : 𝟙_ (Over S) ⟶ B)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), toUnit (Over.mk t) ≫ y = 1) :
    y = 1 := by
  have hη : η[B].left ≫ B.hom = 𝟙 S := Over.w η[B]
  have hy : y.left ≫ B.hom = 𝟙 S := Over.w y
  have : IsImmersion (η[B].left ≫ B.hom) := hη ▸ (inferInstance : IsImmersion (𝟙 S))
  have : IsImmersion η[B].left := IsImmersion.of_comp _ B.hom
  let p : pullback y.left η[B].left ⟶ S := pullback.fst y.left η[B].left
  have : IsImmersion p := inferInstanceAs (IsImmersion (pullback.fst y.left η[B].left))
  have : Surjective p := ⟨fun s => by
    obtain ⟨k, _, _, t, ht⟩ := FinEt.exists_algClosed_point S s
    have e : t ≫ y.left = t ≫ η[B].left := congrArg (·.left) ((h k t).trans Hom.one_def)
    obtain ⟨z, hz⟩ : s ∈ Set.range t := ht.ge rfl
    refine ⟨pullback.lift t t e z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hz]
    exact congrArg (fun q : Spec (CommRingCat.of k) ⟶ S => q z) (pullback.lift_fst _ _ _)⟩
  have : IsClosedImmersion p := .of_isPreimmersion _ (by
    rw [p.surjective.range_eq]; exact isClosed_univ)
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  have e : p ≫ y.left = pullback.snd y.left η[B].left ≫ η[B].left := pullback.condition
  have e' : p = pullback.snd y.left η[B].left := by
    have := e =≫ B.hom
    rw [Category.assoc, Category.assoc, hy, hη] at this
    exact (Category.comp_id _).symm.trans (this.trans (Category.comp_id _))
  rw [← e', cancel_epi] at e
  rw [Hom.one_def, toUnit_unit, Category.id_comp]
  exact Over.OverMorphism.ext e

/- English proof (translation)
Introduce `S _ A B _ _ ψ C _ _ i L hL hψ h₁ h₂ h₃ hk` and use `exists_descent S A B ψ C i L hL hψ h₁ h₂ h₃ (fun c => section_eq_one_of_isReduced _ fun k _ _ t => (Category.assoc _ _ _).symm.trans (((hk k t).1 _).2 ⟨c, rfl⟩)) hk`.
-/
theorem exists_descent_of_isReduced :
    ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])), (∀ c, (u c).IsGen) → (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) :=
  fun S _ A B _ _ ψ C _ _ i L hL hψ h₁ h₂ h₃ hk =>
    exists_descent S A B ψ C i L hL hψ h₁ h₂ h₃ (fun c => section_eq_one_of_isReduced _
      fun k _ _ t => (Category.assoc _ _ _).symm.trans (((hk k t).1 _).2 ⟨c, rfl⟩)) hk

end GlobalTheory.LinDescent
