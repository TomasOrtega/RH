import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMatricesValueMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisEquationDataPrimePower
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.IsoSecond

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Use `⟨(Z.presheaf.stalkSpecializes hs).hom a, ?_⟩` and prove the remaining obligations. Take `⟨U, hx, s, rfl⟩` from `TopCat.Presheaf.exists_germ_eq _ a`. Establish `hb : x' ∈ U` using `hs.mem_open U.isOpen hx`. Rewrite using `[algebraMap_germ hx]`.

Establish `e3` using `TopCat.Presheaf.germ_stalkSpecializes Z.presheaf (U := U) hx hs`. Rewrite using `[← CommRingCat.comp_apply, e3, algebraMap_germ hb]`.
-/
theorem regAt_of_specializes {Z : Scheme.{0}} [IsIntegral Z] {x x' : Z} (hs : x' ⤳ x) {f : Z.functionField}
    (h : RegAt x f) : RegAt x' f := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨(Z.presheaf.stalkSpecializes hs).hom a, ?_⟩
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  have hb : x' ∈ U := hs.mem_open U.isOpen hx
  rw [algebraMap_germ hx]
  have e3 := TopCat.Presheaf.germ_stalkSpecializes Z.presheaf (U := U) hx hs
  rw [← CommRingCat.comp_apply, e3, algebraMap_germ hb]

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (κ ((n : F) * f))` using `map_isIntegral_int κ h`. Establish `h2 : IsIntegral (Z.presheaf.stalk (below y)) (κ ((n : F) * f))` using `h1.tower_top`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Establish `hu : IsUnit ((n : ℕ) : Z.presheaf.stalk (below y))`. Use `IsUnit.of_map (Scheme.stalkClosedPointTo y).hom _ ?_` and prove the remaining obligations.

Rewrite using `[map_natCast]`. Conclude with `(isUnit_iff_ne_zero (G₀ := K)).2 (Nat.cast_ne_zero.2 hn)`. Take `⟨b, hb⟩` from `hu.exists_left_inv`. Use `⟨b * a, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (algebraMap (Z.presheaf.stalk (below y)) Z.functionField) hb`.

Rewrite `h3` using `[map_mul, map_natCast, map_one]`. Rewrite using `[map_mul, ha, map_mul, map_natCast, ← mul_assoc, h3, one_mul]`.
-/
theorem regAt_const {F K : Type} [Field F] [Field K] [CharZero K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    [IsIntegrallyClosed (Z.presheaf.stalk (below y))] (κ : F →+* Z.functionField) {n : ℕ} (hn : n ≠ 0) {f : F}
    (h : IsIntegral ℤ ((n : F) * f)) : RegAt (below y) (κ f) := by
  have h1 : IsIntegral ℤ (κ ((n : F) * f)) := map_isIntegral_int κ h
  have h2 : IsIntegral (Z.presheaf.stalk (below y)) (κ ((n : F) * f)) := h1.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have hu : IsUnit ((n : ℕ) : Z.presheaf.stalk (below y)) := by
    refine IsUnit.of_map (Scheme.stalkClosedPointTo y).hom _ ?_
    rw [map_natCast]
    exact (isUnit_iff_ne_zero (G₀ := K)).2 (Nat.cast_ne_zero.2 hn)
  obtain ⟨b, hb⟩ := hu.exists_left_inv
  refine ⟨b * a, ?_⟩
  have h3 := congrArg (algebraMap (Z.presheaf.stalk (below y)) Z.functionField) hb
  rw [map_mul, map_natCast, map_one] at h3
  rw [map_mul, ha, map_mul, map_natCast, ← mul_assoc, h3, one_mul]

/- English proof (translation)
Establish `hQP : Q * P = 1` using `mul_eq_one_comm.1 hPQ`. Establish `e1 : Q * (P * H * B) = H * B`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]`. Establish `e2 : (P * H * B).transpose * (Q.transpose * J * Q) * (P * H * B) = (H * B).transpose * J * (H * B)`. Rewrite using `[← e1]`.

Generalize the expression as in `P * H * B = M`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Establish `e3 : ∀ l : Fin g, H.mulVec (fun m => n * B m l) = fun r => n * (H * B) r l`. Introduce `l`. Use extensionality with `r`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Establish `hb : ∀ l : Fin g, supN w (H.mulVec fun m => n * B m l) ≤ 1`. Introduce `l`. Rewrite using `[e3]`.

Use `supN_le w zero_le_one fun r => ?_` and prove the remaining obligations. Rewrite using `[← e1, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_induction _ (fun x => w x ≤ 1) (fun a b ha hb => (hw a b).trans (max_le ha hb)) (by simp) ?_` and prove the remaining obligations. Introduce `m _`. Rewrite using `[← mul_assoc, map_mul]`.

Conclude with `mul_le_one₀ (hQ r m) (w.nonneg _) (hU m l)`. Establish `h` using `hiso _ _ (hb i) (hb j)`. Establish `e4 : dotProduct (H.mulVec fun m => n * B m i) (J.mulVec (H.mulVec fun m => n * B m j)) = n ^ 2 * ((H * B).transpose * J * (H * B)) i j`. Rewrite using `[e3, e3, Matrix.mul_assoc]`. Generalize the expression as in `H * B = M`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum, Matrix.transpose_apply]`. Conclude with `Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring`. Rewrite `h` using `[e4, map_mul, map_pow]`. Rewrite using `[e2, le_div_iff₀ (pow_pos (w.pos hn) 2), mul_comm]`. Conclude with `h`.
-/
theorem form_le {K : Type} [Field K] (w : AbsoluteValue K ℝ) (hw : IsNonarchimedean w) {N g : ℕ}
    (P Q J : Matrix (Fin N) (Fin N) K) (H : Matrix (Fin N) (Fin g) K) (B : Matrix (Fin g) (Fin g) K) (n : K) (hn : n ≠ 0)
    (ε : ℝ) (hPQ : P * Q = 1) (hQ : ∀ i j, w (n * Q i j) ≤ 1) (hU : ∀ i j, w ((P * H * B) i j) ≤ 1)
    (hiso : ∀ u u' : Fin g → K, supN w (H.mulVec u) ≤ 1 → supN w (H.mulVec u') ≤ 1 →
      w (dotProduct (H.mulVec u) (J.mulVec (H.mulVec u'))) ≤ ε) (i j : Fin g) :
    w (((P * H * B).transpose * (Q.transpose * J * Q) * (P * H * B)) i j) ≤ ε / w n ^ 2 := by
  have hQP : Q * P = 1 := mul_eq_one_comm.1 hPQ
  have e1 : Q * (P * H * B) = H * B := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have e2 : (P * H * B).transpose * (Q.transpose * J * Q) * (P * H * B) = (H * B).transpose * J * (H * B) := by
    rw [← e1]
    generalize P * H * B = M
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have e3 : ∀ l : Fin g, H.mulVec (fun m => n * B m l) = fun r => n * (H * B) r l := by
    intro l
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hb : ∀ l : Fin g, supN w (H.mulVec fun m => n * B m l) ≤ 1 := by
    intro l
    rw [e3]
    refine supN_le w zero_le_one fun r => ?_
    rw [← e1, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_induction _ (fun x => w x ≤ 1) (fun a b ha hb => (hw a b).trans (max_le ha hb)) (by simp) ?_
    intro m _
    rw [← mul_assoc, map_mul]
    exact mul_le_one₀ (hQ r m) (w.nonneg _) (hU m l)
  have h := hiso _ _ (hb i) (hb j)
  have e4 : dotProduct (H.mulVec fun m => n * B m i) (J.mulVec (H.mulVec fun m => n * B m j)) =
      n ^ 2 * ((H * B).transpose * J * (H * B)) i j := by
    rw [e3, e3, Matrix.mul_assoc]
    generalize H * B = M
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  rw [e4, map_mul, map_pow] at h
  rw [e2, le_div_iff₀ (pow_pos (w.pos hn) 2), mul_comm]
  exact h

/- English proof (translation)
Introduce `F _ _ Y C g A' p n k hp hn V W ι U0 H0 d T J P Q κ hκ hSL a U Um Lf c hU hreg hfr hiso`. Introduce `v hv e y hy z yt hz hyt hin i j`. Establish `hin0 : ⊤ ≤ yt ⁻¹ᵁ U0 a` using `fun x hx => hU (hin hx)`. Establish `hwp : e.w (p : AlgebraicClosure F) < 1` using `ConstLatRel.w_lt_one e hv`. Establish `hpO : ¬ IsUnit ((p : ℕ) : e.O)`.

Establish `h1` using `(HalfGlue.lt_one_iff e.w e.O e.mem_O (p : e.O)).1 (by simpa using hwp)`. Rewrite `h1` using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Then use the resulting hypothesis. Establish `hpx : ¬ IsUnit ((p : ℕ) : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O)))`. Introduce `h`. Apply `hpO` to reduce the goal to its premises.

Use `h.map (Scheme.stalkClosedPointTo yt).hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F)))`. Express the relevant statement in the definitionally equal form `(z ≫ V.j) _ = _`. Rewrite using `[← hyt]`.

Both sides reduce to the same expression. Establish `hPin : V.j (below z) ∈ U0 a`. Rewrite using `[e2]`. Conclude with `hin0 trivial`. Establish `hs : below (z ≫ V.j) ⤳ yt (IsLocalRing.closedPoint e.O)`.

Express the relevant statement in the definitionally equal form `V.j (below z) ⤳ _`. Rewrite using `[e2]`. Conclude with `(IsLocalRing.specializes_closedPoint _).map yt.continuous`. Establish `hπ : V.π (below z) = below y.1` using `by rw [← hz]; rfl`. Establish `hr : ∀ k l, RegAt (below z) ((H0 a * ((T (below y.1)).map V.φ)⁻¹) k l)`.

Introduce `k l`. Establish `h` using `hreg (below z) hPin k l`. Rewrite `h` using `[hπ]`. Then use the resulting hypothesis. Establish `hz' : (z ≫ V.π) ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))` using `by rw [hz]; exact y.2`. Establish `hc : ∀ f : F, valAt (z ≫ V.j) (κ f) = algebraMap F (AlgebraicClosure F) f` using `fun f => by`.

Rewrite using `[hκ, V.valAt_φ z (Var.regAt_algebraMap Y _ f)]`. Conclude with `OfLattice.valAt_const (z ≫ V.π) hz' f`. Establish `hκr : ∀ r s, RegAt (below (z ≫ V.j)) (κ (Q r s))` using `fun r s => haveI := (V.normal (below (z ≫ V.j))).2 regAt_const (z ≫ V.j) κ hn (hSL.2.1 r s).2`. Establish `hU0` using `fun k l => (hfr.2.1 _ (hin trivial) hpx k l).1`. Establish `hUr : ∀ k l, RegAt (below (z ≫ V.j)) (Um k l)` using `fun k l => regAt_of_specializes hs (hU0 k l)`.

Establish `hUb : ∀ k l, e.w (Um.map (valAt (z ≫ V.j)) k l) ≤ 1`. Introduce `k l`. Take `⟨s, hs⟩` from `hU0 k l`. Rewrite using `[Matrix.map_apply, ← hs, ← hyt, HalfGlue.val_stalk]`. Conclude with `(e.mem_O _).1 (Subtype.property _)`.

Take `⟨-, B, -, -, hB⟩` from `hfr.2.2.2 v hv e y hy z yt hz hyt hin`. Rewrite `hB` using `[ConstLatRel.valMat_const_mul V (H0 a) (T (below y.1)) P z hz' hr]`. Establish `eJ : (Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ = (Q.transpose * J.map (Int.castRingHom F) * Q).map κ`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`.

Use extensionality with `r s`. Simplify using the standard rewrite rules. Establish `eV : ((Q.transpose * J.map (Int.castRingHom F) * Q).map κ).map (valAt (z ≫ V.j)) = (Q.map (algebraMap F (AlgebraicClosure F))).transpose * J.map (Int.castRingHom (AlgebraicClosure F)) * Q.map (algebraMap F (AlgebraicClosure F))`. Establish `e1 : ((Q.transpose * J.map (Int.castRingHom F) * Q).map κ).map (valAt (z ≫ V.j)) = (Q.transpose * J.map (Int.castRingHom F) * Q).map (algebraMap F (AlgebraicClosure F))`. Use extensionality with `r s`.

Conclude with `hc _`. Rewrite using `[e1, Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Take `⟨hm, -⟩` from `CramerValues.values_regular (z ≫ V.j)`. Establish `h1` using `hm Um.transpose ((Q.transpose * J.map (Int.castRingHom F) * Q).map κ) (fun r s => hUr s r) (by`.

Rewrite using `[← eJ]`. Conclude with `(hm _ _ (hm (Q.map κ).transpose _ (fun r s => hκr s r) fun r s => ⟨J r s, by simp⟩).1 hκr).1)`. Establish `h2` using `(hm _ Um h1.1 hUr).2`. Rewrite `h2` using `[h1.2, eV, Matrix.transpose_map, hB]`. Rewrite using `[eJ]`.

Express the relevant statement in the definitionally equal form `e.w ((Um.transpose * (Q.transpose * J.map (Int.castRingHom F) * Q).map κ * Um).map (valAt (z ≫ V.j)) i j) ≤ _`. Rewrite using `[h2]`. Rewrite `hUb` using `[hB]`. Use `form_le e.w (isNonarchimedean_w e) _ _ _ _ B _ (Nat.cast_ne_zero.2 hn) _ ?_ (fun r s => ?_) hUb (hiso v hv e y hy z yt hz hyt a hin0).1 i j` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, hSL.1, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `h` using `ConstLatRel.w_le_one_of_isIntegral e (hSL.2.1 r s).2`. Rewrite `h` using `[map_mul, map_natCast]`. Then use the resulting hypothesis.
-/
theorem form_frame_second_le : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A' : Fin g → Adl C Y) (p n k : ℕ), p.Prime →
    n ≠ 0 → ∀ (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U0 : ι → V.X.Opens)
    (H0 : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F) (κ : F →+* V.X.functionField),
    (∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (f : F), valAt (z ≫ V.j) (κ f) = valAt z (V.φ (algebraMap F Y.Fn f))) →
    SecondLat J p n P Q → ∀ (a : ι) (U : V.X.Opens)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ), U ≤ U0 a → ChartReg V (U0 a) (H0 a) T →
    FrameOn V W U (P.map (V.φ.comp (algebraMap F Y.Fn)) * H0 a) d T A' p Um Lf c → IsoAgree V W U0 H0 T J p k →
    AtTest V W p (fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → ∀ i j,
      e.w (valAt (z ≫ V.j) ((Um.transpose * ((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) *
        Um) i j)) ≤ e.w (p : AlgebraicClosure F) ^ k / e.w (n : AlgebraicClosure F) ^ 2) := by
  intro F _ _ Y C g A' p n k hp hn V W ι U0 H0 d T J P Q κ hκ hSL a U Um Lf c hU hreg hfr hiso
  intro v hv e y hy z yt hz hyt hin i j
  have hin0 : ⊤ ≤ yt ⁻¹ᵁ U0 a := fun x hx => hU (hin hx)
  have hwp : e.w (p : AlgebraicClosure F) < 1 := ConstLatRel.w_lt_one e hv
  have hpO : ¬ IsUnit ((p : ℕ) : e.O) := by
    have h1 := (HalfGlue.lt_one_iff e.w e.O e.mem_O (p : e.O)).1 (by simpa using hwp)
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
  have hpx : ¬ IsUnit ((p : ℕ) : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O))) := by
    intro h
    apply hpO
    have := h.map (Scheme.stalkClosedPointTo yt).hom
    rwa [map_natCast] at this
  have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
    change (z ≫ V.j) _ = _
    rw [← hyt]; rfl
  have hPin : V.j (below z) ∈ U0 a := by
    rw [e2]; exact hin0 trivial
  have hs : below (z ≫ V.j) ⤳ yt (IsLocalRing.closedPoint e.O) := by
    change V.j (below z) ⤳ _
    rw [e2]
    exact (IsLocalRing.specializes_closedPoint _).map yt.continuous
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hr : ∀ k l, RegAt (below z) ((H0 a * ((T (below y.1)).map V.φ)⁻¹) k l) := by
    intro k l
    have h := hreg (below z) hPin k l
    rwa [hπ] at h
  have hz' : (z ≫ V.π) ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) := by rw [hz]; exact y.2
  have hc : ∀ f : F, valAt (z ≫ V.j) (κ f) = algebraMap F (AlgebraicClosure F) f := fun f => by
    rw [hκ, V.valAt_φ z (Var.regAt_algebraMap Y _ f)]
    exact OfLattice.valAt_const (z ≫ V.π) hz' f
  have hκr : ∀ r s, RegAt (below (z ≫ V.j)) (κ (Q r s)) := fun r s =>
    haveI := (V.normal (below (z ≫ V.j))).2
    regAt_const (z ≫ V.j) κ hn (hSL.2.1 r s).2
  have hU0 := fun k l => (hfr.2.1 _ (hin trivial) hpx k l).1
  have hUr : ∀ k l, RegAt (below (z ≫ V.j)) (Um k l) := fun k l => regAt_of_specializes hs (hU0 k l)
  have hUb : ∀ k l, e.w (Um.map (valAt (z ≫ V.j)) k l) ≤ 1 := by
    intro k l
    obtain ⟨s, hs⟩ := hU0 k l
    rw [Matrix.map_apply, ← hs, ← hyt, HalfGlue.val_stalk]
    exact (e.mem_O _).1 (Subtype.property _)
  obtain ⟨-, B, -, -, hB⟩ := hfr.2.2.2 v hv e y hy z yt hz hyt hin
  rw [ConstLatRel.valMat_const_mul V (H0 a) (T (below y.1)) P z hz' hr] at hB
  have eJ : (Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ =
      (Q.transpose * J.map (Int.castRingHom F) * Q).map κ := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext r s
    simp
  have eV : ((Q.transpose * J.map (Int.castRingHom F) * Q).map κ).map (valAt (z ≫ V.j)) =
      (Q.map (algebraMap F (AlgebraicClosure F))).transpose * J.map (Int.castRingHom (AlgebraicClosure F)) *
        Q.map (algebraMap F (AlgebraicClosure F)) := by
    have e1 : ((Q.transpose * J.map (Int.castRingHom F) * Q).map κ).map (valAt (z ≫ V.j)) =
        (Q.transpose * J.map (Int.castRingHom F) * Q).map (algebraMap F (AlgebraicClosure F)) := by
      ext r s
      exact hc _
    rw [e1, Matrix.map_mul, Matrix.map_mul]
    congr 2
  obtain ⟨hm, -⟩ := CramerValues.values_regular (z ≫ V.j)
  have h1 := hm Um.transpose ((Q.transpose * J.map (Int.castRingHom F) * Q).map κ) (fun r s => hUr s r)
    (by
      rw [← eJ]
      exact (hm _ _ (hm (Q.map κ).transpose _ (fun r s => hκr s r) fun r s => ⟨J r s, by simp⟩).1 hκr).1)
  have h2 := (hm _ Um h1.1 hUr).2
  rw [h1.2, eV, Matrix.transpose_map, hB] at h2
  rw [eJ]
  change e.w ((Um.transpose * (Q.transpose * J.map (Int.castRingHom F) * Q).map κ * Um).map (valAt (z ≫ V.j)) i j) ≤ _
  rw [h2]
  rw [hB] at hUb
  refine form_le e.w (isNonarchimedean_w e) _ _ _ _ B _ (Nat.cast_ne_zero.2 hn) _ ?_ (fun r s => ?_) hUb
    (hiso v hv e y hy z yt hz hyt a hin0).1 i j
  · rw [← Matrix.map_mul, hSL.1, Matrix.map_one _ (map_zero _) (map_one _)]
  · have h := ConstLatRel.w_le_one_of_isIntegral e (hSL.2.1 r s).2
    rwa [map_mul, map_natCast] at h

end GlobalTheory.ConstLat.IsoSecond

end
