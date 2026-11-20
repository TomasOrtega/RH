import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermuteStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductionsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoordsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsCrd

/- English proof (translation)
Establish `h1 : φ (m⁻¹.mulVec u i) = lam * φ (w i)`. Establish `e : m⁻¹.mulVec (m.mulVec w) = w`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec]`. Use `conv_rhs => rw [← e]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h ⊢`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h j]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨v, hv⟩` from `hi.exists_right_inv`.

Establish `h2 : φ (m⁻¹.mulVec u i * v) = lam`. Rewrite using `[map_mul, h1, _root_.mul_assoc, ← map_mul, hv, map_one, _root_.mul_one]`. Establish `h3 : ∀ j, u j = (m⁻¹.mulVec u i * v) * m.mulVec w j` using `fun j => hφ (by rw [map_mul, h2, h])`. Establish `h4 : IsUnit (m⁻¹.mulVec u i * v)` using `isUnit_of_mul_isUnit_left (h3 k ▸ hk)`. Use `⟨h4.unit, funext fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[h3 j, IsUnit.unit_spec]`. Conclude with `congrFun (Matrix.mulVec_smul m (m⁻¹.mulVec u i * v) w) j`.
-/
theorem exists_unit_smul {O C J : Type} [CommRing O] [Field C] [Fintype J] [DecidableEq J] (φ : O →+* C)
    (hφ : Function.Injective φ) (m : Matrix J J O) (hm : IsUnit m.det) (w u : J → O) (lam : C)
    (h : ∀ i, φ (u i) = lam * φ (m.mulVec w i)) {i k : J} (hi : IsUnit (w i)) (hk : IsUnit (u k)) :
    ∃ mu : Oˣ, m.mulVec (fun j => (mu : O) * w j) = u := by
  have h1 : φ (m⁻¹.mulVec u i) = lam * φ (w i) := by
    have e : m⁻¹.mulVec (m.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec]
    conv_rhs => rw [← e]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h ⊢
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h j]; ring
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h2 : φ (m⁻¹.mulVec u i * v) = lam := by
    rw [map_mul, h1, _root_.mul_assoc, ← map_mul, hv, map_one, _root_.mul_one]
  have h3 : ∀ j, u j = (m⁻¹.mulVec u i * v) * m.mulVec w j := fun j => hφ (by rw [map_mul, h2, h])
  have h4 : IsUnit (m⁻¹.mulVec u i * v) := isUnit_of_mul_isUnit_left (h3 k ▸ hk)
  refine ⟨h4.unit, funext fun j => ?_⟩
  rw [h3 j, IsUnit.unit_spec]
  exact congrFun (Matrix.mulVec_smul m (m⁻¹.mulVec u i * v) w) j

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

/- English proof (translation)
Use `(hB.sec z x₀ hx h hh).1 _ ?_` and prove the remaining obligations. Rewrite using `[Q.basis l z hz]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
theorem sec_mem (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) (i : S.J) :
    (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
  refine (hB.sec z x₀ hx h hh).1 _ ?_
  rw [Q.basis l z hz]
  exact Submodule.subset_span ⟨i, rfl⟩

/- English proof (translation)
Take `⟨h1, i, h2, h3⟩` from `hB.sec z x₀ hx h hh`. Use `set v : S.J → Ω := fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i) with hv`. Establish `hvE : v ∈ EE.E z`. Establish `e : v = ∑ j, (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) • (Pi.single j (1 : Ω) : S.J → Ω)`. Use extensionality with `j`.

Simplify using `[hv, Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB.mem z j)`. Establish `hu : IsUnit (⟨_, h1 v hvE⟩ : M.O z)` using `(RatModel.isUnit_O_iff _).2 ⟨div_ne_zero h2 hx.1, by simpa using h3⟩`. Establish `hvE'` using `hvE`.

Rewrite `hvE'` using `[Q.basis l z hz]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun k j => Q.B l k j)).1 hvE'`. Establish `e : (⟨_, h1 v hvE⟩ : M.O z) = ∑ k, c k * ⟨_, sec_mem hB Q hz hx hh k⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Use `show v ⬝ᵥ S.ev h / S.th x₀ = _`.

Rewrite using `[← hc, sum_dotProduct, Finset.sum_div]`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_dotProduct, Subalgebra.smul_def, smul_eq_mul, mul_div_assoc]`. Rewrite `hu` using `[e]`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Use `(IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) hu` and prove the remaining obligations. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 (hn k)`.
-/
theorem sec_unit (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) :
    ∃ i, IsUnit (⟨_, sec_mem hB Q hz hx hh i⟩ : M.O z) := by
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z x₀ hx h hh
  set v : S.J → Ω := fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i) with hv
  have hvE : v ∈ EE.E z := by
    have e : v = ∑ j, (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) • (Pi.single j (1 : Ω) : S.J → Ω) := by
      ext j
      simp [hv, Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB.mem z j)
  have hu : IsUnit (⟨_, h1 v hvE⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero h2 hx.1, by simpa using h3⟩
  have hvE' := hvE
  rw [Q.basis l z hz] at hvE'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun k j => Q.B l k j)).1 hvE'
  have e : (⟨_, h1 v hvE⟩ : M.O z) = ∑ k, c k * ⟨_, sec_mem hB Q hz hx hh k⟩ := by
    refine Subtype.ext ?_
    show v ⬝ᵥ S.ev h / S.th x₀ = _
    rw [← hc, sum_dotProduct, Finset.sum_div]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_dotProduct, Subalgebra.smul_def, smul_eq_mul, mul_div_assoc]
  rw [e] at hu
  by_contra hn
  push_neg at hn
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) hu
  exact (IsLocalRing.mem_maximalIdeal _).2 (hn k)

variable {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

/- English proof (translation)
Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `e : gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `e2 : gPt p ≫ y = (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι`.

Rewrite using `[Category.assoc, c.yK_fac, ← Category.assoc, ← e, Category.assoc, c.fac]`. Rewrite using `[e2]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `((spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) w).2`.
-/
theorem cen {Q : Clos ρ M U₀ EE} {u : ρ.UTest p y₀} (c : Q.Fac y u) : M.Cen U₀ (y (cPt p)) y := by
  refine ⟨rfl, ?_⟩
  have e : gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e2 : gPt p ≫ y = (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← e, Category.assoc, c.fac]
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) w).2

/- English proof (translation)
Set `s : Sp (PadicAlgCl p)` to `IsLocalRing.closedPoint _`. Use `set ξ := (gPt p ≫ y) s with hξ`. Establish `hr : Set.range (gPt p ≫ y) = {ξ}` using `RatModel.range_eq_singleton _ s`. Establish `hU : ξ ∈ U₀` using `hc.2 ⟨s, rfl⟩`. Establish `hW : ξ ∈ Q.W l` using `(RatModel.gPt_specializes rfl s).mem_open (Q.W l).isOpen hz`.

Establish `hBm : ∀ j, Q.B l i j ∈ M.O ξ`. Establish `: Q.B l i ∈ EE.E ξ`. Rewrite using `[Q.basis l ξ hW]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite `this` using `[hB.ee.1 ξ hU]`.

Conclude with `(RatModel.Lat.mem_const_iff M).1 this`. Establish `hev : ∀ j, S.ev h j ∈ M.O ξ` using `fun j => RatModel.mem_ringOn.1 (hB.ov.le (S.ev_mem h j)) ξ hU`. Establish `hth : (S.th x₀)⁻¹ ∈ M.O ξ` using `RatModel.mem_ringOn.1 (hB.ov.th_unit x₀ hx) ξ hU`. Set `e : M.O ξ` to `⟨_, hth⟩ * ∑ j, ⟨_, hBm j⟩ * ⟨_, hev j⟩`. Establish `he : (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ = (e : Ω)`.

Simplify using `only [e]`. Use `push_cast`. Rewrite using `[div_eq_inv_mul]`. Both sides reduce to the same expression. Rewrite using `[he, ← RatModel.valHom_apply _ _ hr]`.

Simplify using `only [e, map_mul, map_sum, RatModel.valHom_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `congrArg (_ * ·) (ha ⟨_, S.ev_mem h j⟩).symm`.
-/
theorem val_gen (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} (hz : y (cPt p) ∈ Q.W l)
    (hc : M.Cen U₀ (y (cPt p)) y) (ha : S.At M y y₀) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) (h : S.Gam) (i : S.J) :
    M.val (gPt p ≫ y) ((Q.B l i ⬝ᵥ S.ev h) / S.th x₀) = M.val (gPt p ≫ y) (S.th x₀)⁻¹ *
      ((Q.B l).map (M.val (gPt p ≫ y))).mulVec (fun j => y₀ ⟨S.ev h j, S.ev_mem h j⟩) i := by
  let s : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  set ξ := (gPt p ≫ y) s with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ s
  have hU : ξ ∈ U₀ := hc.2 ⟨s, rfl⟩
  have hW : ξ ∈ Q.W l := (RatModel.gPt_specializes rfl s).mem_open (Q.W l).isOpen hz
  have hBm : ∀ j, Q.B l i j ∈ M.O ξ := by
    have : Q.B l i ∈ EE.E ξ := by
      rw [Q.basis l ξ hW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hU] at this
    exact (RatModel.Lat.mem_const_iff M).1 this
  have hev : ∀ j, S.ev h j ∈ M.O ξ := fun j => RatModel.mem_ringOn.1 (hB.ov.le (S.ev_mem h j)) ξ hU
  have hth : (S.th x₀)⁻¹ ∈ M.O ξ := RatModel.mem_ringOn.1 (hB.ov.th_unit x₀ hx) ξ hU
  let e : M.O ξ := ⟨_, hth⟩ * ∑ j, ⟨_, hBm j⟩ * ⟨_, hev j⟩
  have he : (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ = (e : Ω) := by
    simp only [e]
    push_cast
    rw [div_eq_inv_mul]
    rfl
  rw [he, ← RatModel.valHom_apply _ _ hr]
  simp only [e, map_mul, map_sum, RatModel.valHom_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (_ * ·) (ha ⟨_, S.ev_mem h j⟩).symm

/- English proof (translation)
Take `⟨e, -, he⟩` from `t.mt`. Use extensionality with `a`. Use `he a 0` as an intermediate fact. Rewrite `this` using `[map_zero]`. Conclude with `this`.
-/
theorem ker_eq (t : ρ.GeoTest p y₀) : t.τ.yy.ker = t.l.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  ext a
  have := he a 0
  rw [map_zero] at this
  exact this

/- English proof (translation)
Use `⟨?_, h.1, h.2.1⟩` and prove the remaining obligations. Establish `h1 : 2 ≤ ρ.n ^ ρ.k` using `ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)`. Rewrite using `[ρ.N_eq]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

/- English proof (translation)
Establish `hv` using `(GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 _ y₀ a`. Rewrite `hv` using `[← h₃]`. Establish `hb` using `t.link a' _ hv`. Take `⟨wc, hwc⟩` from `CrdCalc.crd_exists t.mod.isLB t.σ cc`. Establish `hg` using `CrdCalc.crd_map (OO p).subtype hwc`.

Rewrite `hb` using `[← h₂]`. Take `⟨κ, hκ⟩` from `CrdCalc.crd_unique hg hb`. Take `⟨⟨i, -, hi⟩, -⟩` from `GlobalTheory.T.exists_unit_weightZero_integral_coords hL.1 hL.2.1 p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls t.mod (big ρ hS) cc wc h₁ hwc`. Take `⟨k, hk⟩` from `sec_unit hB Q tm.mem hx ha`. Set `u : S.J → OO p` to `fun i => RatModel.valLoc y (y (cPt p)) specializes_rfl ⟨_, sec_mem hB Q tm.mem hx ha i⟩`.

Establish `hm : IsUnit (tm.m.map t.u.j).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `tm.unit.map _`. Take `⟨mu, hmu⟩` from `exists_unit_smul (OO p).subtype Subtype.val_injective (tm.m.map t.u.j) hm wc u (M.val (gPt p ≫ y) (S.th x₀)⁻¹ * κ) (fun i => by`. Use `(RatModel.val_spMap_comp (OO p).subtype y specializes_rfl _).symm.trans ?_` and prove the remaining obligations.

Use `(val_gen hB Q tm.mem (cen c) c.at_ hx.1 a i).trans ?_` and prove the remaining obligations. Rewrite using `[tm.m_eq, ← Matrix.mulVec_mulVec, funext hκ, _root_.mul_assoc]`. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Conclude with `mul_left_comm _ _ _) hi (hk.map _)`. Establish `hr` using `CrdCalc.crd_map (IsLocalRing.residue (OO p)) (CrdCalc.crd_smul mu hwc)`. Take `⟨w', hw'⟩` from `CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F (R := kb p) x.left`. Establish `hw''` using `t.mod.red x w' hw'`. Rewrite `hw''` using `[← h₄]`.

Take `⟨ν, hν⟩` from `CrdCalc.crd_unique hw'' hr`. Use `⟨fun j => IsLocalRing.residue (OO p) (mu * wc j), ?_, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[funext hν]`. Conclude with `CrdCalc.crd_smul ν hw'`. Use `Eq.trans ?_ (RatModel.val_spMap_comp (IsLocalRing.residue (OO p)) y specializes_rfl ⟨_, sec_mem hB Q tm.mem hx ha i⟩).symm` and prove the remaining obligations.

Use `Eq.trans ?_ (congrArg (IsLocalRing.residue (OO p)) (congrFun hmu i))` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`.
-/
theorem crd_red (hL : GlobalTheory.UT.LL) [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) {Q : Clos ρ M U₀ EE}
    {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) (hS : S.Big) {x₀ a : S.Gam}
    (hx : x₀ ∈ S.supI M (y (cPt p))) (ha : a ∈ S.HH M (y (cPt p))) (cc : Sp (OO p) ⟶ t.u.G.left) (a' : t.u.PtC)
    (x : t.mod.Φ.Pt) (h₁ : cc ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ cc = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) (h₄ : rPt p ≫ cc = x.left ≫ t.mod.r) :
    ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w =
        fun i => M.val (rPt p ≫ y) ((Q.B tm.l i ⬝ᵥ S.ev a) / S.th x₀) := by
  have hv := (GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 _ y₀ a
  rw [← h₃] at hv
  have hb := t.link a' _ hv
  obtain ⟨wc, hwc⟩ := CrdCalc.crd_exists t.mod.isLB t.σ cc
  have hg := CrdCalc.crd_map (OO p).subtype hwc
  rw [← h₂] at hb
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique hg hb
  obtain ⟨⟨i, -, hi⟩, -⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords hL.1 hL.2.1 p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls
    t.mod (big ρ hS) cc wc h₁ hwc
  obtain ⟨k, hk⟩ := sec_unit hB Q tm.mem hx ha
  let u : S.J → OO p := fun i => RatModel.valLoc y (y (cPt p)) specializes_rfl ⟨_, sec_mem hB Q tm.mem hx ha i⟩
  have hm : IsUnit (tm.m.map t.u.j).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map _
  obtain ⟨mu, hmu⟩ := exists_unit_smul (OO p).subtype Subtype.val_injective (tm.m.map t.u.j) hm wc u
    (M.val (gPt p ≫ y) (S.th x₀)⁻¹ * κ) (fun i => by
      refine (RatModel.val_spMap_comp (OO p).subtype y specializes_rfl _).symm.trans ?_
      refine (val_gen hB Q tm.mem (cen c) c.at_ hx.1 a i).trans ?_
      rw [tm.m_eq, ← Matrix.mulVec_mulVec, funext hκ, _root_.mul_assoc]
      congr 1
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact mul_left_comm _ _ _) hi (hk.map _)
  have hr := CrdCalc.crd_map (IsLocalRing.residue (OO p)) (CrdCalc.crd_smul mu hwc)
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F (R := kb p) x.left
  have hw'' := t.mod.red x w' hw'
  rw [← h₄] at hw''
  obtain ⟨ν, hν⟩ := CrdCalc.crd_unique hw'' hr
  refine ⟨fun j => IsLocalRing.residue (OO p) (mu * wc j), ?_, funext fun i => ?_⟩
  · rw [funext hν]
    exact CrdCalc.crd_smul ν hw'
  · refine Eq.trans ?_ (RatModel.val_spMap_comp (IsLocalRing.residue (OO p)) y specializes_rfl
      ⟨_, sec_mem hB Q tm.mem hx ha i⟩).symm
    refine Eq.trans ?_ (congrArg (IsLocalRing.residue (OO p)) (congrFun hmu i))
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS`. Establish `hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1` using `fun a => by`. Rewrite using `[c.at_]`. Conclude with `RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)`. Establish `hH : S.HH M (y (cPt p)) = t.l.yy.ker` using `(hB.atTest _ p y y₀ t.τ (cen c) c.at_).trans (ker_eq t)`.

Take `⟨-, g₁, g₂⟩` from `GlobalTheory.T.specialFibre_torsion_eq_reductions hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint`. Establish `hr : Set.range (rPt p ≫ y) = {y (cPt p)}`. Rewrite using `[RatModel.range_eq_singleton (K := kb p) _ (IsLocalRing.closedPoint (kb p))]`. Conclude with `congrArg (fun s => ({y s} : Set M.Z)) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Take `⟨a, ha, cc, a', h₁, h₂, h₃, h₄⟩` from `g₁ x hx`. Take `⟨x₀, hx₀⟩` from `hB.ov.div (y (cPt p))`. Rewrite `ha` using `[← hH]`. Take `⟨w, hw, e⟩` from `crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄`.

Conclude with `⟨w, hw, y (cPt p), by rw [hr]; rfl, x₀, hx₀, a, ha, e⟩`. Introduce and unpack `v ⟨z, hz, x₀, hx₀, a, ha, rfl⟩`. Rewrite `hz` using `[hr]`. Take `rfl : z = y (cPt p)` from `hz`. Take `⟨cc, a', x, h₁, h₂, h₃, h₄, h₅⟩` from `g₂ a (hH ▸ ha)`.

Take `⟨w, hw, e⟩` from `crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄`. Conclude with `⟨x, w, h₅, hw, e⟩`.
-/
theorem tors_crd : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → (∀ x : t.mod.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w ∈ Q.Tors (rPt p ≫ y) tm.l) ∧ ∀ v ∈ Q.Tors (rPt p ≫ y) tm.l, ∃ (x : t.mod.Φ.Pt) (w : S.J → kb p), x ^ (S.r * S.N) = 1 ∧ Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w = v := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [c.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hH : S.HH M (y (cPt p)) = t.l.yy.ker := (hB.atTest _ p y y₀ t.τ (cen c) c.at_).trans (ker_eq t)
  obtain ⟨-, g₁, g₂⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint
  have hr : Set.range (rPt p ≫ y) = {y (cPt p)} := by
    rw [RatModel.range_eq_singleton (K := kb p) _ (IsLocalRing.closedPoint (kb p))]
    exact congrArg (fun s => ({y s} : Set M.Z)) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  constructor
  · intro x hx
    obtain ⟨a, ha, cc, a', h₁, h₂, h₃, h₄⟩ := g₁ x hx
    obtain ⟨x₀, hx₀⟩ := hB.ov.div (y (cPt p))
    rw [← hH] at ha
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨w, hw, y (cPt p), by rw [hr]; rfl, x₀, hx₀, a, ha, e⟩
  · rintro v ⟨z, hz, x₀, hx₀, a, ha, rfl⟩
    rw [hr] at hz
    obtain rfl : z = y (cPt p) := hz
    obtain ⟨cc, a', x, h₁, h₂, h₃, h₄, h₅⟩ := g₂ a (hH ▸ ha)
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨x, w, h₅, hw, e⟩

end GlobalTheory.ZH.TorsCrd
end
