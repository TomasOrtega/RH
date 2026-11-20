import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToToStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocal
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsRingHomComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

section Field

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L : Type} [Field L]

/- English proof (translation)
Use `(Scheme.Hom.comp_apply (spMap e) zL _).trans ?_` and prove the remaining obligations. Conclude with `congrArg zL (Subsingleton.elim _ _)`.
-/
theorem centre_map (zL : Sp L ⟶ X) (e : L →+* ℂ) : centre (spMap e ≫ zL) = centre zL := by
  refine (Scheme.Hom.comp_apply (spMap e) zL _).trans ?_
  exact congrArg zL (Subsingleton.elim _ _)

/- English proof (translation)
Establish `hc : centre zL = centre (spMap e ≫ zL)` using `(centre_map zL e).symm`. Establish `h0` using `h`. Take `⟨h', s, hs, -⟩` from `h`. Establish `h'' : genPt ξ ⤳ centre zL` using `hc ▸ h'`. Establish `hv : ValAt ξ zL a (Scheme.stalkClosedPointTo zL |>.hom (X.presheaf.stalkSpecializes (specializes_of_eq hc) s))` using `⟨h'', _, (genMap_stalkSpecializes ξ hc h' h'' s).trans hs, rfl⟩`.

Conclude with `⟨_, hv, ValAt.unique hξ (valAt_of_field_map ξ zL _ e rfl hv) h0⟩`.
-/
theorem descend {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (zL : Sp L ⟶ X) (e : L →+* ℂ) {a : Ω} {r : ℂ}
    (h : ValAt ξ (spMap e ≫ zL) a r) : ∃ t : L, ValAt ξ zL a t ∧ e t = r := by
  have hc : centre zL = centre (spMap e ≫ zL) := (centre_map zL e).symm
  have h0 := h
  obtain ⟨h', s, hs, -⟩ := h
  have h'' : genPt ξ ⤳ centre zL := hc ▸ h'
  have hv : ValAt ξ zL a (Scheme.stalkClosedPointTo zL |>.hom (X.presheaf.stalkSpecializes (specializes_of_eq hc) s)) :=
    ⟨h'', _, (genMap_stalkSpecializes ξ hc h' h'' s).trans hs, rfl⟩
  exact ⟨_, hv, ValAt.unique hξ (valAt_of_field_map ξ zL _ e rfl hv) h0⟩

/- English proof (translation)
Use `⟨fun k => (hw.1 k).imp fun c hc => hc.map e, fun k c hc => ?_⟩` and prove the remaining obligations. Establish `hne : w ⟨k, c⟩ ≠ 0` using `fun h0 => by simp [h0] at hc`. Take `⟨hy, hi⟩` from `hw.2 k c (isUnit_iff_ne_zero.2 hne)`. Use `⟨hy, fun i => ?_⟩` and prove the remaining obligations. Take `⟨ρ, hρ, hr⟩` from `hi i`.

Conclude with `⟨e ρ, valAt_of_field_map ξ zL _ e rfl hρ, by simp only [hr, map_mul]⟩`.
-/
theorem coords_map (ξ : Sp Ω ⟶ X) {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {zL : Sp L ⟶ X}
    {w : (Σ k, J k) → L} (hw : CoordsAt ξ y zL w) (e : L →+* ℂ) :
    CoordsAt ξ y (spMap e ≫ zL) (fun p => e (w p)) := by
  refine ⟨fun k => (hw.1 k).imp fun c hc => hc.map e, fun k c hc => ?_⟩
  have hne : w ⟨k, c⟩ ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨hy, hi⟩ := hw.2 k c (isUnit_iff_ne_zero.2 hne)
  refine ⟨hy, fun i => ?_⟩
  obtain ⟨ρ, hρ, hr⟩ := hi i
  exact ⟨e ρ, valAt_of_field_map ξ zL _ e rfl hρ, by simp only [hr, map_mul]⟩

variable {ξ : Sp Ω ⟶ X} {z : Sp L ⟶ X}

/- English proof (translation)
Take `⟨h1, s, rfl, rfl⟩` from `h`. Take `⟨u, rfl⟩ : IsUnit s` from `(Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.2 hr)`. Use `⟨h1, (u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_, eq_inv_of_mul_eq_one_left ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Use `((Scheme.stalkClosedPointTo z).hom.map_mul _ _).symm.trans ?_` and prove the remaining obligations.

Conclude with `(congrArg (Scheme.stalkClosedPointTo z).hom (Units.inv_mul u)).trans (Scheme.stalkClosedPointTo z).hom.map_one`.
-/
theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.2 hr)
  refine ⟨h1, (u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_, eq_inv_of_mul_eq_one_left ?_⟩
  · rw [← map_mul, Units.inv_mul, map_one]
  · refine ((Scheme.stalkClosedPointTo z).hom.map_mul _ _).symm.trans ?_
    exact (congrArg (Scheme.stalkClosedPointTo z).hom (Units.inv_mul u)).trans (Scheme.stalkClosedPointTo z).hom.map_one

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using RootHt.valAt_one h₀`. Consider the case `succ n ih => simpa [pow_succ] using RootHt.valAt_mul ih h`.
-/
theorem val_pow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using RootHt.valAt_one h₀
  | succ n ih => simpa [pow_succ] using RootHt.valAt_mul ih h

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using val_pow h₀ h n`. Consider the case `negSucc n`. Simplify `val_inv (val_pow h₀ h (n + 1)) (pow_ne_zero _ hr)` using `[zpow_negSucc]`.
-/
theorem val_zpow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using val_pow h₀ h n
  | negSucc n =>
    simpa [zpow_negSucc] using val_inv (val_pow h₀ h (n + 1)) (pow_ne_zero _ hr)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using RootHt.valAt_one h₀`. Consider the case `insert k s hk ih`. Rewrite using `[Finset.prod_insert hk, Finset.prod_insert hk]`. Conclude with `RootHt.valAt_mul (val_zpow h₀ (h k) (hr k) _) ih`.
-/
theorem val_prod_zpow (h₀ : genPt ξ ⤳ centre z) {K : Type} (s : Finset K) {A : K → Ω} {r : K → L} (b : K → ℤ)
    (h : ∀ k, ValAt ξ z (A k) (r k)) (hr : ∀ k, r k ≠ 0) :
    ValAt ξ z (∏ k ∈ s, A k ^ b k) (∏ k ∈ s, r k ^ b k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.valAt_one h₀
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact RootHt.valAt_mul (val_zpow h₀ (h k) (hr k) _) ih

end Field

/- English proof (translation)
Introduce `E _ _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or L _ _ z w cc p hw hcc hp`. Take `⟨e₀⟩ : Nonempty (L →+* ℂ)` from `inferInstance`. Establish `hT` using `Or.𝔐.tie`. Establish `hξ` using `hT.gen`. Establish `hwe` using `fun e : L →+* ℂ => coords_map Or.𝔐.ξ hw e`.

Establish `hm : ∀ e : L →+* ℂ, (fun q => e (w q)) ∈ mcPts (mCoordIdeal Dc.y)` using `fun e => (GlobalTheory.T.complex_points_iff_centres _ _ _ K J _ hT _).2 ⟨_, Or.𝔐.all _, hwe e⟩`. Establish `tv : ∀ (e : L →+* ℂ) (a : Ω) (r : ℂ), ValAt Or.𝔐.ξ (spMap e ≫ z) a r ↔ IsValueAt Dc.y a (fun q => e (w q)) r` using `fun e a r => GlobalTheory.T.valAt_iff_value_at _ _ _ K J _ hT _ _ (Or.𝔐.all _) (hwe e) a r`. Establish `hne` using `GlobalTheory.CompanionTheory.Ar.ProvConj.valAt_ne_zero (Dc.S_prime p hp).ne_zero (Dc.vertical p hp) (hm e₀) cc (fun k => (map_ne_zero e₀).2 (hcc k)) Dc.arith.2.1.2.1`. Establish `hex : ∃ v, IsValueAt Dc.y (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) (fun q => e₀ (w q)) v`. Assume the negation of the conclusion as `h`.

Conclude with `hne (by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_neg h])`. Take `⟨v, hv⟩` from `hex`. Rewrite `hne` using `[valAt_eq (hm e₀) hv]`. Take `⟨t, ht, het⟩` from `descend hξ z e₀ ((tv e₀ _ _).2 hv)`. Use `⟨t, fun h0 => hne (by rw [← het, h0, map_zero]), ht, fun e => ?_⟩` and prove the remaining obligations.

Establish `hve` using `valAt_of_field_map Or.𝔐.ξ z _ e rfl ht`. Establish `hccz : ∀ k, e (w ⟨k, cc k⟩) ≠ 0` using `fun k => (map_ne_zero e).2 (hcc k)`. Establish `hc : ∃ c : (k : K) → J k, ∀ k, (fun q => e (w q)) ⟨k, c k⟩ ≠ 0` using `⟨cc, hccz⟩`. Unfold `ComponentData.vertFactor`. Rewrite using `[dif_pos hc]`.

Establish `hcs` using `hc.choose_spec`. Generalize the expression as in `hc.choose = c at hcs ⊢`. Establish `hcs' : ∀ k, e (w ⟨k, c k⟩) ≠ 0` using `hcs`. Establish `hy : ∀ k, Dc.y ⟨k, c k⟩ ≠ 0` using `fun k => ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).1`. Establish `hy' : ∀ k, Dc.y ⟨k, cc k⟩ ≠ 0` using `fun k => ((hwe e).2 k (cc k) (isUnit_iff_ne_zero.2 (hccz k))).1`.

Establish `hr : ∀ k, ValAt Or.𝔐.ξ (spMap e ≫ z) (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩) (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩))` using `fun k => by`. Take `⟨ρ, h1, h2⟩` from `((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).2 (cc k)`. Establish `h3 : e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩) = ρ`. Rewrite using `[div_eq_iff (hcs' k)]`. Conclude with `h2`.

Rewrite using `[h3]`. Conclude with `h1`. Establish `hall` using `RootHt.valAt_mul hve (val_prod_zpow (Or.𝔐.all _) Finset.univ (Dc.vdeg p) hr (fun k => div_ne_zero (hccz k) (hcs' k)))`. Establish `ha : MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p) * ∏ k, (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩) ^ Dc.vdeg p k = MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y c (-Dc.vdeg p)`. Rewrite using `[_root_.mul_assoc]`.

Use `congr 1`. Unfold `chartMono`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.neg_apply, _root_.zpow_neg, _root_.zpow_neg, div_zpow, div_eq_mul_inv, ← _root_.mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ (hy' k)), _root_.one_mul]`.

Rewrite `hall` using `[ha]`. Rewrite using `[valAt_eq (hm e) ((tv e _ _).1 hall), ← norm_mul]`. Establish `hid : e t * (∏ k, (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) ^ Dc.vdeg p k) * zMono (fun q => e (w q)) c (Dc.vdeg p) = e t * ∏ k, e (w ⟨k, cc k⟩) ^ Dc.vdeg p k`. Rewrite using `[_root_.mul_assoc]`. Use `congr 1`.

Unfold `zMono`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, div_mul_cancel₀ _ (hcs' k)]`. Rewrite using `[hid, norm_mul, norm_prod]`.

Simplify using `only [norm_zpow]`.
-/
theorem vertical_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  intro E _ _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or L _ _ z w cc p hw hcc hp
  classical
  obtain ⟨e₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have hT := Or.𝔐.tie
  have hξ := hT.gen
  have hwe := fun e : L →+* ℂ => coords_map Or.𝔐.ξ hw e
  have hm : ∀ e : L →+* ℂ, (fun q => e (w q)) ∈ mcPts (mCoordIdeal Dc.y) := fun e =>
    (GlobalTheory.T.complex_points_iff_centres _ _ _ K J _ hT _).2 ⟨_, Or.𝔐.all _, hwe e⟩
  have tv : ∀ (e : L →+* ℂ) (a : Ω) (r : ℂ),
      ValAt Or.𝔐.ξ (spMap e ≫ z) a r ↔ IsValueAt Dc.y a (fun q => e (w q)) r :=
    fun e a r => GlobalTheory.T.valAt_iff_value_at _ _ _ K J _ hT _ _ (Or.𝔐.all _) (hwe e) a r
  have hne := GlobalTheory.CompanionTheory.Ar.ProvConj.valAt_ne_zero (Dc.S_prime p hp).ne_zero (Dc.vertical p hp) (hm e₀) cc
    (fun k => (map_ne_zero e₀).2 (hcc k)) Dc.arith.2.1.2.1
  have hex : ∃ v, IsValueAt Dc.y (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p)) (fun q => e₀ (w q)) v := by
    by_contra h
    exact hne (by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_neg h])
  obtain ⟨v, hv⟩ := hex
  rw [valAt_eq (hm e₀) hv] at hne
  obtain ⟨t, ht, het⟩ := descend hξ z e₀ ((tv e₀ _ _).2 hv)
  refine ⟨t, fun h0 => hne (by rw [← het, h0, map_zero]), ht, fun e => ?_⟩
  have hve := valAt_of_field_map Or.𝔐.ξ z _ e rfl ht
  have hccz : ∀ k, e (w ⟨k, cc k⟩) ≠ 0 := fun k => (map_ne_zero e).2 (hcc k)
  have hc : ∃ c : (k : K) → J k, ∀ k, (fun q => e (w q)) ⟨k, c k⟩ ≠ 0 := ⟨cc, hccz⟩
  unfold ComponentData.vertFactor
  rw [dif_pos hc]
  have hcs := hc.choose_spec
  generalize hc.choose = c at hcs ⊢
  have hcs' : ∀ k, e (w ⟨k, c k⟩) ≠ 0 := hcs
  have hy : ∀ k, Dc.y ⟨k, c k⟩ ≠ 0 := fun k => ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).1
  have hy' : ∀ k, Dc.y ⟨k, cc k⟩ ≠ 0 := fun k => ((hwe e).2 k (cc k) (isUnit_iff_ne_zero.2 (hccz k))).1
  have hr : ∀ k, ValAt Or.𝔐.ξ (spMap e ≫ z) (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩)
      (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) := fun k => by
    obtain ⟨ρ, h1, h2⟩ := ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).2 (cc k)
    have h3 : e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩) = ρ := by
      rw [div_eq_iff (hcs' k)]
      exact h2
    rw [h3]
    exact h1
  have hall := RootHt.valAt_mul hve (val_prod_zpow (Or.𝔐.all _) Finset.univ (Dc.vdeg p) hr
    (fun k => div_ne_zero (hccz k) (hcs' k)))
  have ha : MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p) * ∏ k, (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩) ^ Dc.vdeg p k =
      MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
        chartMono Dc.y c (-Dc.vdeg p) := by
    rw [_root_.mul_assoc]
    congr 1
    unfold chartMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, _root_.zpow_neg, _root_.zpow_neg, div_zpow, div_eq_mul_inv, ← _root_.mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero _ (hy' k)), _root_.one_mul]
  rw [ha] at hall
  rw [valAt_eq (hm e) ((tv e _ _).1 hall), ← norm_mul]
  have hid : e t * (∏ k, (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) ^ Dc.vdeg p k) *
      zMono (fun q => e (w q)) c (Dc.vdeg p) = e t * ∏ k, e (w ⟨k, cc k⟩) ^ Dc.vdeg p k := by
    rw [_root_.mul_assoc]
    congr 1
    unfold zMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hcs' k)]
  rw [hid, norm_mul, norm_prod]
  simp only [norm_zpow]

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert
