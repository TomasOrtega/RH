import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.WeilBound.CoreStatements.AmpleLineBundles.TopLePreimageOfEpsFibreSndComp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace CoverDenseAlt

/- English proof (translation)
Substitute `e` using the available equality. Establish `h : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ (1 : Over.mk a ⟶ G) = 1`. Simplify using `only [Hom.one_def, comp_toUnit_assoc]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {Y Y' : Scheme.{0}} (k : Y' ⟶ Y) (a : Y ⟶ S)
    {a' : Y' ⟶ S} (e : k ≫ a = a') : (1 : Over.mk a' ⟶ G).left = k ≫ (1 : Over.mk a ⟶ G).left := by
  subst e
  have h : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ (1 : Over.mk a ⟶ G) = 1 := by
    simp only [Hom.one_def, comp_toUnit_assoc]
  rw [← h]
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Establish `hx' : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ x = x'`. Use `ext`. Conclude with `hx`. Establish `hy' : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ y = y'`.

Use `ext`. Conclude with `hy`. Establish `h : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ (x * y) = x' * y'`. Rewrite using `[← hx', ← hy', Hom.mul_def, Hom.mul_def, comp_lift_assoc]`. Rewrite using `[← h]`.

Both sides reduce to the same expression.
-/
theorem mul_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {Y Y' : Scheme.{0}} (k : Y' ⟶ Y) (a : Y ⟶ S)
    {a' : Y' ⟶ S} (e : k ≫ a = a') (x y : Over.mk a ⟶ G) (x' y' : Over.mk a' ⟶ G)
    (hx : k ≫ x.left = x'.left) (hy : k ≫ y.left = y'.left) : k ≫ (x * y).left = (x' * y').left := by
  subst e
  have hx' : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ x = x' := by
    ext
    exact hx
  have hy' : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ y = y' := by
    ext
    exact hy
  have h : (Over.homMk k rfl : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ (x * y) = x' * y' := by
    rw [← hx', ← hy', Hom.mul_def, Hom.mul_def, comp_lift_assoc]
  rw [← h]
  rfl

/- English proof (translation)
Establish `e1 : Scheme.Hom.appLE (spMap g ≫ z) V ⊤ h' = z.appLE V ⊤ h ≫ (spMap g).appTop`. Rewrite using `[Scheme.Hom.comp_appLE]`. Use `show _ = (z.app V ≫ (Sp A).presheaf.map (homOfLE h).op) ≫ _`. Rewrite using `[Category.assoc]`. Use `congr 1`.

Establish `e2` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)`. Simplify using `only [val]`. Rewrite using `[e1, Category.assoc]`. Use `erw [e2]`. Both sides reduce to the same expression.
-/
private theorem val_spMap_comp_eq {Z : Scheme} {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ (spMap g ≫ z) ⁻¹ᵁ V) (f : Γ(Z, V)) :
    val (spMap g ≫ z) V h' f = g (val z V h f) := by
  have e1 : Scheme.Hom.appLE (spMap g ≫ z) V ⊤ h' = z.appLE V ⊤ h ≫ (spMap g).appTop := by
    rw [Scheme.Hom.comp_appLE]
    show _ = (z.app V ≫ (Sp A).presheaf.map (homOfLE h).op) ≫ _
    rw [Category.assoc]
    congr 1
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  simp only [val]
  rw [e1, Category.assoc]
  erw [e2]
  rfl

/- English proof (translation)
Simplify using `only [val, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec z hW (isAffineOpen_top _) h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]`. Simplify using `[← Spec.map_comp]`.
-/
private theorem spec_map_val_comp_fromSpec_eq {X : Scheme} {B : Type} [CommRing B] (z : Sp B ⟶ X) {W : X.Opens}
    (hW : IsAffineOpen W) (h : ⊤ ≤ z ⁻¹ᵁ W) :
    Spec.map (CommRingCat.ofHom (val z W h)) ≫ hW.fromSpec = z := by
  simp only [val, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec z hW (isAffineOpen_top _) h, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec]
  simp [← Spec.map_comp]

/- English proof (translation)
Introduce `p _`. Establish `hp : p ∈ Set.range (PrimeSpectrum.comap g)`. Rewrite using `[range_comap_of_surjective _ g hg]`. Introduce `r hr`. Conclude with `p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hk r hr]; exact Ideal.zero_mem _)`.

Take `⟨q, rfl⟩` from `hp`. Conclude with `h (Set.mem_univ q)`.
-/
private theorem cover_of_spMap_comp_cover_of_square_zero_kernel {X : Scheme} {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    (hg : Function.Surjective g) (hk : ∀ r, g r = 0 → r * r = 0) (z : Sp R ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ (spMap g ≫ z) ⁻¹ᵁ V) : ⊤ ≤ z ⁻¹ᵁ V := by
  intro p _
  have hp : p ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [range_comap_of_surjective _ g hg]
    intro r hr
    exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hk r hr]; exact Ideal.zero_mem _)
  obtain ⟨q, rfl⟩ := hp
  exact h (Set.mem_univ q)

/- English proof (translation)
Use `⟨{ carrier := {v | (∀ i, v i - v 0 ∈ J) ∧ v 0 + v 1 = v 2 + v 3} mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun v => Iff.rfl⟩` and prove the remaining obligations. Introduce and unpack `v w ⟨hv, hs⟩ ⟨hw, ht⟩`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (v * w) i - (v * w) 0 = (v i - v 0) * w i + v 0 * (w i - w 0)`. Simplify using `only [Pi.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.add_mem (J.mul_mem_right _ (hv i)) (J.mul_mem_left _ (hw i))`. Establish `z1` using `hJ _ (hv 2) _ (hw 3)`. Establish `z2` using `hJ _ (hv 3) _ (hw 2)`.

Simplify using `only [Pi.mul_apply]`. Take the linear combination `w 1 * hs + (v 2 + v 3 - v 0) * ht + z1 + z2`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Introduce and unpack `v w ⟨hv, hs⟩ ⟨hw, ht⟩`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (v + w) i - (v + w) 0 = (v i - v 0) + (w i - w 0)`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `J.add_mem (hv i) (hw i)`. Simplify using `only [Pi.add_apply]`. Take the linear combination `hs + ht`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce and unpack `v ⟨hv, hs⟩`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (-v) i - (-v) 0 = -(v i - v 0)`.

Simplify using `only [Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.neg_mem (hv i)`. Simplify using `only [Pi.neg_apply]`.

Take the linear combination `-hs`.
-/
private theorem exists_subring_fin_four_of_square_zero_ideal {A : Type} [CommRing A] (J : Ideal A) (hJ : ∀ j ∈ J, ∀ k ∈ J, j * k = 0) :
    ∃ Q : Subring (Fin 4 → A), ∀ v, v ∈ Q ↔ (∀ i, v i - v 0 ∈ J) ∧ v 0 + v 1 = v 2 + v 3 := by
  refine ⟨{ carrier := {v | (∀ i, v i - v 0 ∈ J) ∧ v 0 + v 1 = v 2 + v 3}
            mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ },
    fun v => Iff.rfl⟩
  · rintro v w ⟨hv, hs⟩ ⟨hw, ht⟩
    refine ⟨fun i => ?_, ?_⟩
    · have e : (v * w) i - (v * w) 0 = (v i - v 0) * w i + v 0 * (w i - w 0) := by
        simp only [Pi.mul_apply]
        ring
      rw [e]
      exact J.add_mem (J.mul_mem_right _ (hv i)) (J.mul_mem_left _ (hw i))
    · have z1 := hJ _ (hv 2) _ (hw 3)
      have z2 := hJ _ (hv 3) _ (hw 2)
      simp only [Pi.mul_apply]
      linear_combination w 1 * hs + (v 2 + v 3 - v 0) * ht + z1 + z2
  · refine ⟨fun i => ?_, ?_⟩
    · simp
    · simp
  · rintro v w ⟨hv, hs⟩ ⟨hw, ht⟩
    refine ⟨fun i => ?_, ?_⟩
    · have e : (v + w) i - (v + w) 0 = (v i - v 0) + (w i - w 0) := by
        simp only [Pi.add_apply]
        ring
      rw [e]
      exact J.add_mem (hv i) (hw i)
    · simp only [Pi.add_apply]
      linear_combination hs + ht
  · refine ⟨fun i => ?_, ?_⟩
    · simp
    · simp
  · rintro v ⟨hv, hs⟩
    refine ⟨fun i => ?_, ?_⟩
    · have e : (-v) i - (-v) 0 = -(v i - v 0) := by
        simp only [Pi.neg_apply]
        ring
      rw [e]
      exact J.neg_mem (hv i)
    · simp only [Pi.neg_apply]
      linear_combination -hs

/- English proof (translation)
Establish `hJz : ∀ j ∈ J, ∀ k ∈ J, j * k = 0`. Introduce `j hj k hk`. Establish `hm : j * k ∈ J ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hj hk`.

Rewrite `hm` using `[hJ]`. Conclude with `Ideal.mem_bot.mp hm`. Establish `hnilJ : ∀ r, Ideal.Quotient.mk J r = 0 → r * r = 0` using `fun r hr => hJz r (Ideal.Quotient.eq_zero_iff_mem.mp hr) r (Ideal.Quotient.eq_zero_iff_mem.mp hr)`. Establish `hvcongr : ∀ {B : Type} [CommRing B] {X' : Scheme} {z z' : Sp B ⟶ X'} (_ : z = z') (V' : X'.Opens) (h h') (g : Γ(X', V')), val z V' h g = val z' V' h' g`. Introduce and unpack `B _ X' z _ rfl V' h h' g`.

Both sides reduce to the same expression. Use `set e := (1 : Over.mk a ⟶ G).left with he`. Establish `hxW : ⊤ ≤ x.left ⁻¹ᵁ W` using `cover_of_spMap_comp_cover_of_square_zero_kernel (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hnilJ x.left W (by rw [ex]; exact fun p _ => ho (Set.mem_univ _))`. Establish `hyW : ⊤ ≤ y.left ⁻¹ᵁ W` using `cover_of_spMap_comp_cover_of_square_zero_kernel (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hnilJ y.left W (by rw [ey]; exact fun p _ => ho (Set.mem_univ _))`. Establish `hmod : ∀ (z : Sp A ⟶ G.left) (hz : ⊤ ≤ z ⁻¹ᵁ W), spMap (Ideal.Quotient.mk J) ≫ z = spMap (Ideal.Quotient.mk J) ≫ e → ∀ r, val z W hz r - val e W ho r ∈ J`.

Introduce `z hz hze r`. Rewrite using `[← Ideal.Quotient.eq, ← val_spMap_comp_eq (Ideal.Quotient.mk J) z W hz (fun p _ => hz (Set.mem_univ _)) r, ← val_spMap_comp_eq (Ideal.Quotient.mk J) e W ho (fun p _ => ho (Set.mem_univ _)) r]`. Conclude with `hvcongr hze W _ _ r`. Take `⟨Q, hQ⟩` from `exists_subring_fin_four_of_square_zero_ideal J hJz`. Use `set φx := val (A := A) x.left W hxW with hφx`.

Use `set φy := val (A := A) y.left W hyW with hφy`. Use `set φ1 := val (A := A) e W ho with hφ1`. Establish `dx : ∀ r, φx r - φ1 r ∈ J` using `hmod x.left hxW ex`. Establish `dy : ∀ r, φy r - φ1 r ∈ J` using `hmod y.left hyW ey`. Establish `hαmem : ∀ r, (Pi.ringHom ![φx, φ1, φx, φ1]) r ∈ Q`.

Introduce `r`. Rewrite using `[hQ]`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Use `fin_cases i`. Use `show φx r - φx r ∈ J`.

Simplify using the standard rewrite rules. Use `show φ1 r - φx r ∈ J`. Rewrite using `[← neg_sub]`. Conclude with `J.neg_mem (dx r)`. Use `show φx r - φx r ∈ J`.

Simplify using the standard rewrite rules. Use `show φ1 r - φx r ∈ J`. Rewrite using `[← neg_sub]`. Conclude with `J.neg_mem (dx r)`. Both sides reduce to the same expression.

Establish `hβmem : ∀ r, (Pi.ringHom ![φy, φ1, φ1, φy]) r ∈ Q`. Introduce `r`. Rewrite using `[hQ]`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Use `fin_cases i`.

Use `show φy r - φy r ∈ J`. Simplify using the standard rewrite rules. Use `show φ1 r - φy r ∈ J`. Rewrite using `[← neg_sub]`. Conclude with `J.neg_mem (dy r)`.

Use `show φ1 r - φy r ∈ J`. Rewrite using `[← neg_sub]`. Conclude with `J.neg_mem (dy r)`. Use `show φy r - φy r ∈ J`. Simplify using the standard rewrite rules.

Use `show φy r + φ1 r = φ1 r + φy r`. Expand and normalize the polynomial expressions, which then agree. Set `α : Γ(G.left, W) →+* Q` to `(Pi.ringHom ![φx, φ1, φx, φ1]).codRestrict Q hαmem`. Set `β : Γ(G.left, W) →+* Q` to `(Pi.ringHom ![φy, φ1, φ1, φy]).codRestrict Q hβmem`. Set `pr : Fin 4 → (Q →+* A)` to `fun i => (Pi.evalRingHom (fun _ => A) i).comp Q.subtype`.

Establish `hπ : ∀ (ψ : Γ(G.left, W) →+* Q) (i : Fin 4), spMap (pr i) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec = Spec.map (CommRingCat.ofHom ((pr i).comp ψ)) ≫ hW.fromSpec`. Introduce `ψ i`. Rewrite using `[← Category.assoc]`. Use `congr 1`. Simplify using `only [spMap, ← Spec.map_comp]`.

Both sides reduce to the same expression. Set `Xα : Sp Q ⟶ G.left` to `Spec.map (CommRingCat.ofHom α) ≫ hW.fromSpec`. Set `Xβ : Sp Q ⟶ G.left` to `Spec.map (CommRingCat.ofHom β) ≫ hW.fromSpec`. Establish `hXα : ∀ i, spMap (pr i) ≫ Xα = ![x.left, e, x.left, e] i`. Introduce `i`.

Rewrite using `[hπ]`. Use `fin_cases i`. Conclude with `spec_map_val_comp_fromSpec_eq x.left hW hxW`. Conclude with `spec_map_val_comp_fromSpec_eq e hW ho`. Conclude with `spec_map_val_comp_fromSpec_eq x.left hW hxW`.

Conclude with `spec_map_val_comp_fromSpec_eq e hW ho`. Establish `hXβ : ∀ i, spMap (pr i) ≫ Xβ = ![y.left, e, e, y.left] i`. Introduce `i`. Rewrite using `[hπ]`. Use `fin_cases i`.

Conclude with `spec_map_val_comp_fromSpec_eq y.left hW hyW`. Conclude with `spec_map_val_comp_fromSpec_eq e hW ho`. Conclude with `spec_map_val_comp_fromSpec_eq e hW ho`. Conclude with `spec_map_val_comp_fromSpec_eq y.left hW hyW`. Establish `hpr0 : Function.Surjective (pr 0)` using `fun c => ⟨⟨fun _ => c, (hQ _).2 ⟨fun i => by simp, rfl⟩⟩, rfl⟩`.

Establish `hnil0 : ∀ v, pr 0 v = 0 → v * v = 0`. Introduce `v hv`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `hvi : (v : Fin 4 → A) i ∈ J`.

Establish `h'` using `((hQ v).1 v.2).1 i`. Establish `h0 : (v : Fin 4 → A) 0 = 0` using `hv`. Rewrite `h'` using `[h0, sub_zero]`. Then use the resulting hypothesis. Conclude with `hJz _ hvi _ hvi`. Establish `hU' : ∀ T : Sp Q ⟶ S, spMap (pr 0) ≫ T = a → ⊤ ≤ T ⁻¹ᵁ U` using `fun T hT => cover_of_spMap_comp_cover_of_square_zero_kernel (pr 0) hpr0 hnil0 T U (by rw [hT]; exact ha)`.

Establish `hsame : ∀ T1 T2 : Sp Q ⟶ S, (∀ i, spMap (pr i) ≫ T1 = a) → (∀ i, spMap (pr i) ≫ T2 = a) → T1 = T2`. Introduce `T1 T2 h1' h2'`. Rewrite using `[← spec_map_val_comp_fromSpec_eq T1 hU (hU' T1 (h1' 0)), ← spec_map_val_comp_fromSpec_eq T2 hU (hU' T2 (h2' 0))]`. Establish `hv : val T1 U (hU' T1 (h1' 0)) = val T2 U (hU' T2 (h2' 0))`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `k1` using `val_spMap_comp_eq (pr i) T1 U (hU' T1 (h1' 0)) (by rw [h1' i]; exact ha) r`. Establish `k2` using `val_spMap_comp_eq (pr i) T2 U (hU' T2 (h2' 0)) (by rw [h2' i]; exact ha) r`. Express the relevant statement in the definitionally equal form `pr i (val T1 U _ r) = pr i (val T2 U _ r)`.

Rewrite using `[← k1, ← k2]`. Conclude with `(hvcongr (h1' i) U _ ha r).trans (hvcongr (h2' i) U _ ha r).symm`. Rewrite using `[hv]`. Establish `hS : Xα ≫ G.hom = Xβ ≫ G.hom`. Apply `hsame` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[← Category.assoc, hXα i]`. Use `fin_cases i`. Conclude with `Over.w x`. Conclude with `Over.w (1 : Over.mk a ⟶ G)`.

Conclude with `Over.w x`. Conclude with `Over.w (1 : Over.mk a ⟶ G)`. Introduce `i`. Rewrite using `[← Category.assoc, hXβ i]`. Use `fin_cases i`.

Conclude with `Over.w y`. Conclude with `Over.w (1 : Over.mk a ⟶ G)`. Conclude with `Over.w (1 : Over.mk a ⟶ G)`. Conclude with `Over.w y`. Set `Ψ : Sp Q ⟶ G.left` to `pullback.lift Xα Xβ hS ≫ (MonObj.mul (X := G)).left`.

Establish `hΨgen : ∀ (i : Fin 4) (z w : Over.mk a ⟶ G), spMap (pr i) ≫ Xα = z.left → spMap (pr i) ≫ Xβ = w.left → spMap (pr i) ≫ Ψ = (z * w).left`. Introduce `i z w hz hw`. Establish `hzw : (z * w).left = pullback.lift z.left w.left (z.w.trans w.w.symm) ≫ (MonObj.mul (X` using `G)).left := rfl`. Rewrite using `[hzw]`. Use `show spMap (pr i) ≫ pullback.lift Xα Xβ hS ≫ _ = _`.

Rewrite using `[← Category.assoc]`. Use `congr 1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, pullback.lift_fst]`. Conclude with `hz`.

Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd]`. Conclude with `hw`. Establish `h0 : spMap (pr 0) ≫ Ψ = (x * y).left` using `hΨgen 0 x y (hXα 0) (hXβ 0)`. Establish `h1' : spMap (pr 1) ≫ Ψ = e`. Rewrite using `[hΨgen 1 1 1 (hXα 1) (hXβ 1), _root_.mul_one]`.

Establish `h2' : spMap (pr 2) ≫ Ψ = x.left`. Rewrite using `[hΨgen 2 x 1 (hXα 2) (hXβ 2), _root_.mul_one]`. Establish `h3' : spMap (pr 3) ≫ Ψ = y.left`. Rewrite using `[hΨgen 3 1 y (hXα 3) (hXβ 3), _root_.one_mul]`. Establish `hΨV : ⊤ ≤ Ψ ⁻¹ᵁ V` using `cover_of_spMap_comp_cover_of_square_zero_kernel (pr 0) hpr0 hnil0 Ψ V (by rw [h0]; exact hxy)`.

Establish `k : ∀ (i : Fin 4) (z : Sp A ⟶ G.left) (hz : spMap (pr i) ≫ Ψ = z) (hzV : ⊤ ≤ z ⁻¹ᵁ V), ((val Ψ V hΨV f : Q) : Fin 4 → A) i = val z V hzV f`. Introduce `i z hz hzV`. Establish `k'` using `val_spMap_comp_eq (pr i) Ψ V hΨV (by rw [hz]; exact hzV) f`. Rewrite `k'` using `[hvcongr hz V _ hzV f]`. Conclude with `k'.symm`.

Establish `hc` using `((hQ _).1 (val Ψ V hΨV f).2).2`. Rewrite `hc` using `[k 0 _ h0 hxy, k 1 _ h1' h1, k 2 _ h2' hx, k 3 _ h3' hy]`. Conclude with `hc`.
-/
theorem val_add {S : Scheme.{0}} {G : Over S} [GrpObj G] {A : Type} [CommRing A] (a : Sp A ⟶ S) {J : Ideal A}
    (hJ : J ^ 2 = ⊥) {U : S.Opens} (hU : IsAffineOpen U) (ha : ⊤ ≤ a ⁻¹ᵁ U) {W : G.left.Opens}
    (hW : IsAffineOpen W) (ho : ⊤ ≤ (1 : Over.mk a ⟶ G).left ⁻¹ᵁ W) (x y : Over.mk a ⟶ G)
    (ex : spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk a ⟶ G).left)
    (ey : spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk a ⟶ G).left)
    (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V)
    (h1 : ⊤ ≤ (1 : Over.mk a ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    val (A := A) (x * y).left V hxy f + val (A := A) (1 : Over.mk a ⟶ G).left V h1 f =
      val (A := A) x.left V hx f + val (A := A) y.left V hy f := by
  have hJz : ∀ j ∈ J, ∀ k ∈ J, j * k = 0 := by
    intro j hj k hk
    have hm : j * k ∈ J ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hj hk
    rw [hJ] at hm
    exact Ideal.mem_bot.mp hm
  have hnilJ : ∀ r, Ideal.Quotient.mk J r = 0 → r * r = 0 := fun r hr =>
    hJz r (Ideal.Quotient.eq_zero_iff_mem.mp hr) r (Ideal.Quotient.eq_zero_iff_mem.mp hr)
  have hvcongr : ∀ {B : Type} [CommRing B] {X' : Scheme} {z z' : Sp B ⟶ X'} (_ : z = z')
      (V' : X'.Opens) (h h') (g : Γ(X', V')), val z V' h g = val z' V' h' g := by
    rintro B _ X' z _ rfl V' h h' g
    rfl
  set e := (1 : Over.mk a ⟶ G).left with he
  have hxW : ⊤ ≤ x.left ⁻¹ᵁ W := cover_of_spMap_comp_cover_of_square_zero_kernel (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    hnilJ x.left W (by rw [ex]; exact fun p _ => ho (Set.mem_univ _))
  have hyW : ⊤ ≤ y.left ⁻¹ᵁ W := cover_of_spMap_comp_cover_of_square_zero_kernel (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    hnilJ y.left W (by rw [ey]; exact fun p _ => ho (Set.mem_univ _))
  have hmod : ∀ (z : Sp A ⟶ G.left) (hz : ⊤ ≤ z ⁻¹ᵁ W),
      spMap (Ideal.Quotient.mk J) ≫ z = spMap (Ideal.Quotient.mk J) ≫ e →
        ∀ r, val z W hz r - val e W ho r ∈ J := by
    intro z hz hze r
    rw [← Ideal.Quotient.eq,
      ← val_spMap_comp_eq (Ideal.Quotient.mk J) z W hz (fun p _ => hz (Set.mem_univ _)) r,
      ← val_spMap_comp_eq (Ideal.Quotient.mk J) e W ho (fun p _ => ho (Set.mem_univ _)) r]
    exact hvcongr hze W _ _ r
  obtain ⟨Q, hQ⟩ := exists_subring_fin_four_of_square_zero_ideal J hJz
  set φx := val (A := A) x.left W hxW with hφx
  set φy := val (A := A) y.left W hyW with hφy
  set φ1 := val (A := A) e W ho with hφ1
  have dx : ∀ r, φx r - φ1 r ∈ J := hmod x.left hxW ex
  have dy : ∀ r, φy r - φ1 r ∈ J := hmod y.left hyW ey
  have hαmem : ∀ r, (Pi.ringHom ![φx, φ1, φx, φ1]) r ∈ Q := by
    intro r
    rw [hQ]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · show φx r - φx r ∈ J
        simp
      · show φ1 r - φx r ∈ J
        rw [← neg_sub]
        exact J.neg_mem (dx r)
      · show φx r - φx r ∈ J
        simp
      · show φ1 r - φx r ∈ J
        rw [← neg_sub]
        exact J.neg_mem (dx r)
    · rfl
  have hβmem : ∀ r, (Pi.ringHom ![φy, φ1, φ1, φy]) r ∈ Q := by
    intro r
    rw [hQ]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · show φy r - φy r ∈ J
        simp
      · show φ1 r - φy r ∈ J
        rw [← neg_sub]
        exact J.neg_mem (dy r)
      · show φ1 r - φy r ∈ J
        rw [← neg_sub]
        exact J.neg_mem (dy r)
      · show φy r - φy r ∈ J
        simp
    · show φy r + φ1 r = φ1 r + φy r
      ring
  let α : Γ(G.left, W) →+* Q := (Pi.ringHom ![φx, φ1, φx, φ1]).codRestrict Q hαmem
  let β : Γ(G.left, W) →+* Q := (Pi.ringHom ![φy, φ1, φ1, φy]).codRestrict Q hβmem
  let pr : Fin 4 → (Q →+* A) := fun i => (Pi.evalRingHom (fun _ => A) i).comp Q.subtype
  have hπ : ∀ (ψ : Γ(G.left, W) →+* Q) (i : Fin 4),
      spMap (pr i) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec =
        Spec.map (CommRingCat.ofHom ((pr i).comp ψ)) ≫ hW.fromSpec := by
    intro ψ i
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  let Xα : Sp Q ⟶ G.left := Spec.map (CommRingCat.ofHom α) ≫ hW.fromSpec
  let Xβ : Sp Q ⟶ G.left := Spec.map (CommRingCat.ofHom β) ≫ hW.fromSpec
  have hXα : ∀ i, spMap (pr i) ≫ Xα = ![x.left, e, x.left, e] i := by
    intro i
    rw [hπ]
    fin_cases i
    · exact spec_map_val_comp_fromSpec_eq x.left hW hxW
    · exact spec_map_val_comp_fromSpec_eq e hW ho
    · exact spec_map_val_comp_fromSpec_eq x.left hW hxW
    · exact spec_map_val_comp_fromSpec_eq e hW ho
  have hXβ : ∀ i, spMap (pr i) ≫ Xβ = ![y.left, e, e, y.left] i := by
    intro i
    rw [hπ]
    fin_cases i
    · exact spec_map_val_comp_fromSpec_eq y.left hW hyW
    · exact spec_map_val_comp_fromSpec_eq e hW ho
    · exact spec_map_val_comp_fromSpec_eq e hW ho
    · exact spec_map_val_comp_fromSpec_eq y.left hW hyW
  have hpr0 : Function.Surjective (pr 0) := fun c =>
    ⟨⟨fun _ => c, (hQ _).2 ⟨fun i => by simp, rfl⟩⟩, rfl⟩
  have hnil0 : ∀ v, pr 0 v = 0 → v * v = 0 := by
    intro v hv
    apply Subtype.ext
    funext i
    have hvi : (v : Fin 4 → A) i ∈ J := by
      have h' := ((hQ v).1 v.2).1 i
      have h0 : (v : Fin 4 → A) 0 = 0 := hv
      rwa [h0, sub_zero] at h'
    exact hJz _ hvi _ hvi
  have hU' : ∀ T : Sp Q ⟶ S, spMap (pr 0) ≫ T = a → ⊤ ≤ T ⁻¹ᵁ U := fun T hT =>
    cover_of_spMap_comp_cover_of_square_zero_kernel (pr 0) hpr0 hnil0 T U (by rw [hT]; exact ha)
  have hsame : ∀ T1 T2 : Sp Q ⟶ S, (∀ i, spMap (pr i) ≫ T1 = a) →
      (∀ i, spMap (pr i) ≫ T2 = a) → T1 = T2 := by
    intro T1 T2 h1' h2'
    rw [← spec_map_val_comp_fromSpec_eq T1 hU (hU' T1 (h1' 0)), ← spec_map_val_comp_fromSpec_eq T2 hU (hU' T2 (h2' 0))]
    have hv : val T1 U (hU' T1 (h1' 0)) = val T2 U (hU' T2 (h2' 0)) := by
      refine RingHom.ext fun r => ?_
      apply Subtype.ext
      funext i
      have k1 := val_spMap_comp_eq (pr i) T1 U (hU' T1 (h1' 0)) (by rw [h1' i]; exact ha) r
      have k2 := val_spMap_comp_eq (pr i) T2 U (hU' T2 (h2' 0)) (by rw [h2' i]; exact ha) r
      change pr i (val T1 U _ r) = pr i (val T2 U _ r)
      rw [← k1, ← k2]
      exact (hvcongr (h1' i) U _ ha r).trans (hvcongr (h2' i) U _ ha r).symm
    rw [hv]
  have hS : Xα ≫ G.hom = Xβ ≫ G.hom := by
    apply hsame
    · intro i
      rw [← Category.assoc, hXα i]
      fin_cases i
      · exact Over.w x
      · exact Over.w (1 : Over.mk a ⟶ G)
      · exact Over.w x
      · exact Over.w (1 : Over.mk a ⟶ G)
    · intro i
      rw [← Category.assoc, hXβ i]
      fin_cases i
      · exact Over.w y
      · exact Over.w (1 : Over.mk a ⟶ G)
      · exact Over.w (1 : Over.mk a ⟶ G)
      · exact Over.w y
  let Ψ : Sp Q ⟶ G.left := pullback.lift Xα Xβ hS ≫ (MonObj.mul (X := G)).left
  have hΨgen : ∀ (i : Fin 4) (z w : Over.mk a ⟶ G), spMap (pr i) ≫ Xα = z.left →
      spMap (pr i) ≫ Xβ = w.left → spMap (pr i) ≫ Ψ = (z * w).left := by
    intro i z w hz hw
    have hzw : (z * w).left =
        pullback.lift z.left w.left (z.w.trans w.w.symm) ≫ (MonObj.mul (X := G)).left := rfl
    rw [hzw]
    show spMap (pr i) ≫ pullback.lift Xα Xβ hS ≫ _ = _
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hz
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact hw
  have h0 : spMap (pr 0) ≫ Ψ = (x * y).left := hΨgen 0 x y (hXα 0) (hXβ 0)
  have h1' : spMap (pr 1) ≫ Ψ = e := by
    rw [hΨgen 1 1 1 (hXα 1) (hXβ 1), _root_.mul_one]
  have h2' : spMap (pr 2) ≫ Ψ = x.left := by
    rw [hΨgen 2 x 1 (hXα 2) (hXβ 2), _root_.mul_one]
  have h3' : spMap (pr 3) ≫ Ψ = y.left := by
    rw [hΨgen 3 1 y (hXα 3) (hXβ 3), _root_.one_mul]
  have hΨV : ⊤ ≤ Ψ ⁻¹ᵁ V := cover_of_spMap_comp_cover_of_square_zero_kernel (pr 0) hpr0 hnil0 Ψ V (by rw [h0]; exact hxy)
  have k : ∀ (i : Fin 4) (z : Sp A ⟶ G.left) (hz : spMap (pr i) ≫ Ψ = z) (hzV : ⊤ ≤ z ⁻¹ᵁ V),
      ((val Ψ V hΨV f : Q) : Fin 4 → A) i = val z V hzV f := by
    intro i z hz hzV
    have k' := val_spMap_comp_eq (pr i) Ψ V hΨV (by rw [hz]; exact hzV) f
    rw [hvcongr hz V _ hzV f] at k'
    exact k'.symm
  have hc := ((hQ _).1 (val Ψ V hΨV f).2).2
  rw [k 0 _ h0 hxy, k 1 _ h1' h1, k 2 _ h2' hx, k 3 _ h3' hy] at hc
  exact hc

end CoverDenseAlt
