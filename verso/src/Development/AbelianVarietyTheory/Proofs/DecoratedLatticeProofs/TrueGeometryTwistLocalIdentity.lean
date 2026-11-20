import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartQuot

open GlobalTheory.FinPl GlobalTheory.FinPlLoc ValuativeRel

variable {D : D7}

/- English proof (translation)
Use `⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]`. Use `show ((a x * (c x)⁻¹ : Circle) : ℂ) = ((α.locK P k * (γ.locK P k)⁻¹ : ℂˣ) : ℂ)`. Rewrite using `[Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx, Units.val_mul, Units.val_inv_eq_inv_val]`.
-/
theorem chrEq_div {a c : (AE D)ˣ →* Circle} {α γ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a α) (hc : ChrEq c γ) :
    ChrEq (a * c⁻¹) (α * γ⁻¹) := by
  refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
  · show ((a x * (c x)⁻¹ : Circle) : ℂ) = ((α.locK P k * (γ.locK P k)⁻¹ : ℂˣ) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx,
      Units.val_mul, Units.val_inv_eq_inv_val]

/- English proof (translation)
Establish `h` using `chrEq_div ha hc`. Rewrite `h` using `[_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]`. Conclude with `GlobalTheory.GridWeil.triv_base h (hα.mul hγ.inv) b`.
-/
theorem quot_triv {a c : (AE D)ˣ →* Circle} {α γ ξ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a (α * ξ)) (hc : ChrEq c (γ * ξ))
    (hα : α.TrivOn D.host.F) (hγ : γ.TrivOn D.host.F) (b : (AF D.host.F)ˣ) : (a * c⁻¹) (idF D b) = 1 := by
  have h := chrEq_div ha hc
  rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right] at h
  exact GlobalTheory.GridWeil.triv_base h (hα.mul hγ.inv) b

/- English proof (translation)
Substitute `hn` using the available equality. Establish `e0 : ∀ g : GA D V, finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D)` using `fun g => by simp [finM]`. Rewrite `h` using `[e0, e0]`. Apply `mt_inj` to reduce the goal to its premises. Use extensionality with `i j`.

Establish `h1 : infPart D (Formalism.L2.Theta.mt V g i j) = infPart D (Formalism.L2.Theta.mt V g' i j)`. Establish `a : infHom V g = infHom V g'` using `(show infHom V g = 1 from hg).trans (show infHom V g' = 1 from hg').symm`. Conclude with `congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => z.1 i j) a`. Establish `h2 : finPart D (Formalism.L2.Theta.mt V g i j) = finPart D (Formalism.L2.Theta.mt V g' i j)` using `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (congrFun (congrFun h i) j)`. Rewrite using `[← sub_eq_zero]`.

Apply `eq_zero_of_comp` to reduce the goal to its premises. Rewrite using `[RingHom.map_sub, h1, sub_self]`. Introduce `w`. Rewrite using `[RingHom.map_sub]`. Unfold `GlobalTheory.FinPl.compAt`.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, h2, sub_self]`.
-/
theorem eq_of_finM {V : HSp D} {n : ℕ} (hn : V.rank = n) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : finM V hn g = finM V hn g') : g = g' := by
  subst hn
  have e0 : ∀ g : GA D V, finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := fun g => by simp [finM]
  rw [e0, e0] at h
  apply mt_inj
  ext i j
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = infPart D (Formalism.L2.Theta.mt V g' i j) := by
    have a : infHom V g = infHom V g' := (show infHom V g = 1 from hg).trans (show infHom V g' = 1 from hg').symm
    exact congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => z.1 i j) a
  have h2 : finPart D (Formalism.L2.Theta.mt V g i j) = finPart D (Formalism.L2.Theta.mt V g' i j) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (congrFun (congrFun h i) j)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, h1, sub_self]
  · intro w
    rw [RingHom.map_sub]
    unfold GlobalTheory.FinPl.compAt
    rw [RingHom.comp_apply, RingHom.comp_apply, h2, sub_self]

section Pt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

/- English proof (translation)
Take `⟨ε, ⟨α, rfl, h1, h0⟩, he⟩` from `p.above`. Rewrite using `[he]`. Express the relevant statement in the definitionally equal form `infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧ ∀ w, compAt D w (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _`. Use `⟨infPart_pair _ _, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[compAt_pair]`.

Use `split_ifs with hw`. Rewrite using `[hw, h1]`. Both sides reduce to the same expression. Rewrite using `[h0 w hw, TensorProduct.zero_tmul]`.
-/
theorem sum_parts : infPart D (p.e + cA D p.e) = 0 ∧
    ∀ w, compAt D w (p.e + cA D p.e) = if w = p.v then 1 else 0 := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, he⟩ := p.above
  rw [he]
  change infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧
    ∀ w, compAt D w (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
  refine ⟨infPart_pair _ _, fun w => ?_⟩
  rw [compAt_pair]
  split_ifs with hw
  · rw [hw, h1]; rfl
  · rw [h0 w hw, TensorProduct.zero_tmul]

/- English proof (translation)
Establish `e1` using `p.split.1`. Establish `e2` using `p.split.2.1`. Establish `e3 : cA D p.e * cA D p.e = cA D p.e` using `by rw [← map_mul, e1]`. Establish `f1 : φ p.e = 0`. Establish `: p.e = p.e * (p.e + cA D p.e)` using `by rw [mul_add, e1, e2, add_zero]`.

Rewrite using `[this, map_mul, h, mul_zero]`. Establish `f2 : φ (cA D p.e) = 0`. Rewrite `h` using `[map_add, f1, zero_add]`. Conclude with `h`. Establish `s : p.sec a = p.e * p.sec a` using `by rw [← p.sec_pr, p.pr_sec]`.

Rewrite using `[p.idele_val, s]`. Simplify using `only [map_add, map_sub, map_mul, map_one, f1, f2]`. Simplify using the standard rewrite rules.
-/
theorem idele_off {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 0) (a : kˣ) :
    φ (p.idele a : AE D) = 1 ∧ φ (cA D (p.idele a : AE D)) = 1 := by
  have e1 := p.split.1
  have e2 := p.split.2.1
  have e3 : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, e1]
  have f1 : φ p.e = 0 := by
    have : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, e1, e2, add_zero]
    rw [this, map_mul, h, mul_zero]
  have f2 : φ (cA D p.e) = 0 := by
    rw [map_add, f1, zero_add] at h; exact h
  have s : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
  rw [p.idele_val, s]
  simp only [map_add, map_sub, map_mul, map_one, f1, f2]
  simp

/- English proof (translation)
Establish `s : p.sec a = p.e * δ` using `by rw [← ha, p.sec_pr]`. Rewrite using `[p.idele_val, s]`. Establish `h2` using `congrArg φ hδ`. Simplify using `only [map_add, map_sub, map_mul, map_one] at h h2 ⊢`. Take the linear combination `(φ δ - 1) * h - φ (cA D p.e) * h2`.
-/
theorem idele_on {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 1) (a : kˣ) (δ : AE D)
    (hδ : cA D δ * δ = 1) (ha : p.pr δ = a) :
    φ (p.idele a : AE D) = φ δ * φ (cA D (p.idele a : AE D)) := by
  have s : p.sec a = p.e * δ := by rw [← ha, p.sec_pr]
  rw [p.idele_val, s]
  have h2 := congrArg φ hδ
  simp only [map_add, map_sub, map_mul, map_one] at h h2 ⊢
  linear_combination (φ δ - 1) * h - φ (cA D p.e) * h2

end Pt

/- English proof (translation)
Rewrite `hh` using `[mem_congGrp]`. Rewrite using `[← Ideal.Quotient.eq, map_one, RingHom.map_det]`. Establish `: (Ideal.Quotient.mk I).mapMatrix (Formalism.L2.Theta.mt V h) = (Ideal.Quotient.mk I).mapMatrix 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply]`.

Rewrite using `[Ideal.Quotient.eq]`. Conclude with `hh i j`. Rewrite using `[this, map_one, Matrix.det_one]`.
-/
theorem det_sub_one_mem {V : HSp D} {I : Ideal (AE D)} {h : GA D V} (hh : h ∈ congGrp V I) :
    (Formalism.L2.Theta.mt V h).det - 1 ∈ I := by
  rw [mem_congGrp] at hh
  rw [← Ideal.Quotient.eq, map_one, RingHom.map_det]
  have : (Ideal.Quotient.mk I).mapMatrix (Formalism.L2.Theta.mt V h) = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact hh i j
  rw [this, map_one, Matrix.det_one]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hδ` using `det_sub_one_mem hh`. Establish `hn` using `Formalism.L2.Theta.det_conj_mul V h`. Use `show _ = (Formalism.L2.Theta.mt V h).det * cA D _`. Establish `off : ∀ {R : Type} [CommRing R] (φ : AE D →+* R), (∀ i, φ ((p i).e + cA D (p i).e) = 0) → φ ((Formalism.L2.Theta.mt V h).det - 1) = 0 → φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0`. Introduce `R _ φ h1 h2`.

Rewrite `h2` using `[map_sub, map_one, sub_eq_zero]`. Rewrite using `[Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod, h2, Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).1, Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).2, mul_one, sub_self]`. Establish `on : ∀ {R : Type} [CommRing R] (φ : AE D →+* R) (i : ι), (∀ j, j ≠ i → φ ((p j).e + cA D (p j).e) = 0) → φ ((p i).e + cA D (p i).e) = 1 → φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0`. Introduce `R _ φ i o h1`. Rewrite using `[Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod, Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).1) (fun h => absurd (Finset.mem_univ i) h), Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).2) (fun h => absurd (Fi …`.

Conclude with `idele_on (p i) _ h1 _ _ hn (hd i)`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_comp` to reduce the goal to its premises. Conclude with `off (infPart D) (fun i => (sum_parts (p i)).1) (infPart_of_idAt hδ)`. Introduce `w`.

Distinguish the cases in `hw : ∃ i, (p i).v = w`. Take `⟨i, rfl⟩` from `hw`. Use `on (compAt D (p i).v) i (fun j hj => ?_) ?_` and prove the remaining obligations. Rewrite using `[(sum_parts (p j)).2, if_neg fun e => hj (hp e).symm]`. Rewrite using `[(sum_parts (p i)).2, if_pos rfl]`.

Use `off (compAt D w) (fun i => ?_) (compAt_of_idAt hδ hw)` and prove the remaining obligations. Rewrite using `[(sum_parts (p i)).2, if_neg fun e => hw ⟨i, e.symm⟩]`.
-/
theorem isDetRoot_prod {ι : Type} [Fintype ι] {k : ι → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (p : ∀ i, SplitPt D (k i))
    (hp : Function.Injective fun i => (p i).v) {V : HSp D} {h : GA D V} (hh : h ∈ grpAt V fun w => ∃ i, (p i).v = w)
    (d : ∀ i, (k i)ˣ) (hd : ∀ i, (p i).pr (Formalism.L2.Theta.mt V h).det = d i) :
    IsDetRoot V h (∏ i, (p i).idele (d i)) := by
  have hδ := det_sub_one_mem hh
  have hn := Formalism.L2.Theta.det_conj_mul V h
  show _ = (Formalism.L2.Theta.mt V h).det * cA D _
  have off : ∀ {R : Type} [CommRing R] (φ : AE D →+* R), (∀ i, φ ((p i).e + cA D (p i).e) = 0) →
      φ ((Formalism.L2.Theta.mt V h).det - 1) = 0 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ h1 h2
    rw [map_sub, map_one, sub_eq_zero] at h2
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod, h2,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).1,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).2, mul_one, sub_self]
  have on : ∀ {R : Type} [CommRing R] (φ : AE D →+* R) (i : ι), (∀ j, j ≠ i → φ ((p j).e + cA D (p j).e) = 0) →
      φ ((p i).e + cA D (p i).e) = 1 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ i o h1
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod,
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).1) (fun h => absurd (Finset.mem_univ i) h),
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).2) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
    exact idele_on (p i) _ h1 _ _ hn (hd i)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · exact off (infPart D) (fun i => (sum_parts (p i)).1) (infPart_of_idAt hδ)
  · intro w
    by_cases hw : ∃ i, (p i).v = w
    · obtain ⟨i, rfl⟩ := hw
      refine on (compAt D (p i).v) i (fun j hj => ?_) ?_
      · rw [(sum_parts (p j)).2, if_neg fun e => hj (hp e).symm]
      · rw [(sum_parts (p i)).2, if_pos rfl]
    · refine off (compAt D w) (fun i => ?_) (compAt_of_idAt hδ hw)
      rw [(sum_parts (p i)).2, if_neg fun e => hw ⟨i, e.symm⟩]

/- English proof (translation)
Use `⟨Matrix.GeneralLinearGroup.det g, ?_, ?_⟩` and prove the remaining obligations. Take `⟨g₀, rfl⟩` from `hg`. Establish `e : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀) : kˣ) : k) = algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g₀ : 𝒪[k]ˣ)`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)`. Rewrite using `[Matrix.det_conj_of_mul_eq_one F.βγ F.γβ, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_submatrix_equiv_self (Equiv.sumEmpty Y (Fin 0)).symm]`. Both sides reduce to the same expression.
-/
theorem exists_unit_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (g : GL (Y ⊕ Fin 0) k)
    (hg : g ∈ GlobalTheory.SplitWeil.KO k (Y ⊕ Fin 0)) :
    ∃ d : kˣ, valuation k (d : k) = 1 ∧ (F.β * g.val.toBlocks₁₁ * F.γ).det = d := by
  refine ⟨Matrix.GeneralLinearGroup.det g, ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hg
    have e : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀) : kˣ) : k) =
        algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g₀ : 𝒪[k]ˣ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
      rfl
    rw [e]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  · rw [Matrix.det_conj_of_mul_eq_one F.βγ F.γβ, Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.det_submatrix_equiv_self (Equiv.sumEmpty Y (Fin 0)).symm]
    rfl

/- English proof (translation)
Take `⟨a, ha⟩` from `(GlobalTheory.Member.isDetRoot_laws D V).2.1 g _ _ h h'`. Rewrite using `[ha, map_mul, hF, mul_one]`.
-/
theorem chr_eq_of_root {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g : GA D V} {x x' : (AE D)ˣ}
    (h : IsDetRoot V g x) (h' : IsDetRoot V g x') : χ x = χ x' := by
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g _ _ h h'
  rw [ha, map_mul, hF, mul_one]

/- English proof (translation)
Rewrite using `[chr_eq_of_root hF hz ((GlobalTheory.Member.isDetRoot_laws D V).2.2.2 _ _ _ _ hx hy), map_mul, h1, mul_one]`.
-/
theorem chr_eq_of_root_mul {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g h : GA D V} {x y z : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot V h y) (h1 : χ y = 1) (hz : IsDetRoot V (g * h) z) : χ z = χ x := by
  rw [chr_eq_of_root hF hz ((GlobalTheory.Member.isDetRoot_laws D V).2.2.2 _ _ _ _ hx hy), map_mul, h1, mul_one]

/- English proof (translation)
Establish `e : (p.idele d : AE D) = (ofSplit p).ι d + (1 - (ofSplit p).e)`. Rewrite using `[p.idele_val, add_comm]`. Both sides reduce to the same expression. Establish `a` using `h d _ e`. Establish `a'` using `h' d _ e`.

Rewrite `a` using `[MonoidHom.mul_apply, hη d hd]`. Rewrite `a'` using `[MonoidHom.mul_apply, hη' d hd, a]`. Use `Circle.ext a'` as an intermediate fact. Rewrite `this` using `[MonoidHom.inv_apply, MonoidHom.inv_apply]`. Conclude with `inv_injective this`.
-/
theorem eq_on_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {c c' : (AE D)ˣ →* Circle} {η η' δ : kˣ →* ℂˣ} (h : (ofSplit p).IsComp c⁻¹ (η * δ)) (h' : (ofSplit p).IsComp c'⁻¹ (η' * δ))
    (hη : GlobalTheory.SplitWeil.IsUnram η) (hη' : GlobalTheory.SplitWeil.IsUnram η') (d : kˣ) (hd : valuation k (d : k) = 1) :
    c (p.idele d) = c' (p.idele d) := by
  have e : (p.idele d : AE D) = (ofSplit p).ι d + (1 - (ofSplit p).e) := by
    rw [p.idele_val, add_comm]; rfl
  have a := h d _ e
  have a' := h' d _ e
  rw [MonoidHom.mul_apply, hη d hd] at a
  rw [MonoidHom.mul_apply, hη' d hd, a] at a'
  have := Circle.ext a'
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply] at this
  exact inv_injective this

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem det_cast (n n' : ℕ) (e : n = n') (h : GA D (D.sp.X n')) :
    (Formalism.L2.Theta.mt _ (e ▸ h : GA D (D.sp.X n))).det = (Formalism.L2.Theta.mt _ h).det := by
  subst e; rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' t J hJ j hj β β'`. Establish `hA` using `hJ.is`. Establish `hj0 : j < B.R.m` using `by omega`. Establish `hle : j + 1 ≤ B.R.m` using `hj.le`. Establish `c1 : ChrEq (J.A.chr (j + 1)) (I.C.mu0 ⟨j, hj0⟩ * I.xi (W.P.I.tup t))` using `hA.chr ⟨j, hj0⟩`.

Establish `c2 : ChrEq (J.A.chr (j + 1 + 1)) (I.C.mu0 ⟨j + 1, hj⟩ * I.xi (W.P.I.tup t))` using `hA.chr ⟨j + 1, hj⟩`. Establish `hF : ∀ b, (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (idF (I.rec7 l Z) b) = 1` using `quot_triv (D := I.rec7 l Z) c2 c1 (I.C.isMu0 ⟨j + 1, hj⟩).triv (I.C.isMu0 ⟨j, hj0⟩).triv`. Use `show (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _ = (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _`. Establish `key : ∀ γ, ∃ k₀ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)), k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) (j + 1) hle) k₀ = (TC.kStd X u (B.R.N (j + 1))).1 ∧ ∀ x, IsDetRoot _ k₀ x → (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (J.A.xr (j + 1) γ) = (J.A.chr (j + 1 + 1) * (J.A.chr (j + …`. Introduce `γ`.

Take `⟨hG, hM, hR⟩` from `hA.kA (j + 1) hle γ`. Break down `Nat.lt_or_ge (j + 1 + 1) B.R.m with h | h` into its components or cases. Use `⟨_, hG, ?_, fun x hx => chr_eq_of_root hF hR hx⟩` and prove the remaining obligations. Rewrite using `[hM, hJ.std (j + 1) h γ]`. Establish `hm : j + 1 + 1 = B.R.m` using `by omega`.

Take `⟨k₀, h₀, hG₀, hM₀, hk, hsupp, hloc⟩` from `hJ.pen (j + 1) hm γ`. Use `⟨k₀, hG₀, hM₀, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hs : ∀ i, (J.G i).s = j` using `fun i => by`. Establish `: (J.G i).s + 1 + 1 = B.R.m` using `(J.G i).hs`. Use linear arithmetic over natural numbers and integers.

Establish `hd : ∀ i, ∃ d : (J.G i).kˣ, valuation (J.G i).k (d : (J.G i).k) = 1 ∧ (J.G i).q.pr (Formalism.L2.Theta.mt _ h₀).det = d` using `fun i => by`. Establish `e : (J.G i).s + 1 = j + 1` using `by rw [hs i]`. Take `⟨g, hg, hmat⟩` from `hloc i e`. Take `⟨d, hd1, hd2⟩` from `exists_unit_det ((J.G i).FX ((J.G i).s + 1) le_rfl) g ((J.E i).le _ _ _ hg)`. Use `⟨d, hd1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← det_cast _ _ e h₀, RingHom.map_det]`. Conclude with `(congrArg Matrix.det hmat).trans hd2`. Use `choose d hd1 hd2 using hd`. Establish `hroot` using `isDetRoot_prod (fun i => (J.G i).q) (GlobalTheory.TopVol.TwistPlaces.places_injective W hW u a ha ha' t J hJ) hsupp d hd2`. Rewrite `hR` using `[hk]`.

Use `chr_eq_of_root_mul hF hx hroot ?_ hR` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, hJ.chr (j + 1) hj, hJ.chr j hj0, eq_on_unit (J.G i).q ((J.E i).mu (j + 1) (by rw [hs i])).1 ((J.E i).mu j (by rw [hs i]; omega)).1 ((J.E i).unr _) ((J.E i).unr _) (d i) (hd1 i), mul_inv_cancel]`. Take `⟨k₁, g1, m1, h1⟩` from `key β`.

Take `⟨k₂, g2, m2, h2⟩` from `key β'`. Take `rfl : k₁ = k₂` from `eq_of_finM _ g1 g2 (m1.trans m2.symm)`. Take `⟨x, hx⟩` from `(GlobalTheory.Member.isDetRoot_laws _ _).1 k₁`. Rewrite using `[h1 x hx, h2 x hx]`.
-/
theorem chr_quot_chart_free : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ j, j + 1 < B.R.m → ∀ β β' : J.Ch₀ (j + 1), J.A.chr (j + 1 + 1) (J.A.xr (j + 1) β) * (J.A.chr (j + 1) (J.A.xr (j + 1) β))⁻¹ = J.A.chr (j + 1 + 1) (J.A.xr (j + 1) β') * (J.A.chr (j + 1) (J.A.xr (j + 1) β'))⁻¹ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' t J hJ j hj β β'
  have hA := hJ.is
  have hj0 : j < B.R.m := by omega
  have hle : j + 1 ≤ B.R.m := hj.le
  have c1 : ChrEq (J.A.chr (j + 1)) (I.C.mu0 ⟨j, hj0⟩ * I.xi (W.P.I.tup t)) := hA.chr ⟨j, hj0⟩
  have c2 : ChrEq (J.A.chr (j + 1 + 1)) (I.C.mu0 ⟨j + 1, hj⟩ * I.xi (W.P.I.tup t)) := hA.chr ⟨j + 1, hj⟩
  have hF : ∀ b, (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (idF (I.rec7 l Z) b) = 1 :=
    quot_triv (D := I.rec7 l Z) c2 c1 (I.C.isMu0 ⟨j + 1, hj⟩).triv (I.C.isMu0 ⟨j, hj0⟩).triv
  show (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _ = (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _
  have key : ∀ γ, ∃ k₀ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)), k₀ ∈ GfC _ ∧
      finM _ (rankN (I.rec7 l Z) (j + 1) hle) k₀ = (TC.kStd X u (B.R.N (j + 1))).1 ∧
      ∀ x, IsDetRoot _ k₀ x → (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (J.A.xr (j + 1) γ) =
        (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) x := by
    intro γ
    obtain ⟨hG, hM, hR⟩ := hA.kA (j + 1) hle γ
    rcases Nat.lt_or_ge (j + 1 + 1) B.R.m with h | h
    · refine ⟨_, hG, ?_, fun x hx => chr_eq_of_root hF hR hx⟩
      rw [hM, hJ.std (j + 1) h γ]
    · have hm : j + 1 + 1 = B.R.m := by omega
      obtain ⟨k₀, h₀, hG₀, hM₀, hk, hsupp, hloc⟩ := hJ.pen (j + 1) hm γ
      refine ⟨k₀, hG₀, hM₀, fun x hx => ?_⟩
      have hs : ∀ i, (J.G i).s = j := fun i => by
        have : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
        omega
      have hd : ∀ i, ∃ d : (J.G i).kˣ, valuation (J.G i).k (d : (J.G i).k) = 1 ∧
          (J.G i).q.pr (Formalism.L2.Theta.mt _ h₀).det = d := fun i => by
        have e : (J.G i).s + 1 = j + 1 := by rw [hs i]
        obtain ⟨g, hg, hmat⟩ := hloc i e
        obtain ⟨d, hd1, hd2⟩ := exists_unit_det ((J.G i).FX ((J.G i).s + 1) le_rfl) g ((J.E i).le _ _ _ hg)
        refine ⟨d, hd1, ?_⟩
        rw [← det_cast _ _ e h₀, RingHom.map_det]
        exact (congrArg Matrix.det hmat).trans hd2
      choose d hd1 hd2 using hd
      have hroot := isDetRoot_prod (fun i => (J.G i).q)
        (GlobalTheory.TopVol.TwistPlaces.places_injective W hW u a ha ha' t J hJ) hsupp d hd2
      rw [hk] at hR
      refine chr_eq_of_root_mul hF hx hroot ?_ hR
      rw [map_prod]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hJ.chr (j + 1) hj, hJ.chr j hj0,
        eq_on_unit (J.G i).q ((J.E i).mu (j + 1) (by rw [hs i])).1 ((J.E i).mu j (by rw [hs i]; omega)).1
          ((J.E i).unr _) ((J.E i).unr _) (d i) (hd1 i), mul_inv_cancel]
  obtain ⟨k₁, g1, m1, h1⟩ := key β
  obtain ⟨k₂, g2, m2, h2⟩ := key β'
  obtain rfl : k₁ = k₂ := eq_of_finM _ g1 g2 (m1.trans m2.symm)
  obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 k₁
  rw [h1 x hx, h2 x hx]

end GlobalTheory.ChartQuot
