import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MiddleLatticeSelfDualAnisotropicPairingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalHyperbolicFrameAnisotropicMemSpanTransStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDualVectorNormInvNotMemLocalStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

/- English proof (translation)
Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]`. Establish `h` using `Algebra.norm_algebraMap (S := 𝓞 E) (T : ℤ)`. Simplify using `only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at h`. Rewrite using `[h, Int.natAbs_pow, Int.natAbs_natCast, NumberField.RingOfIntegers.rank]`.
-/
theorem mlat_card (E : Type) [Field E] [NumberField E] (T : ℕ) :
    Nat.card (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}) = T ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have h := Algebra.norm_algebraMap (S := 𝓞 E) (T : ℤ)
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at h
  rw [h, Int.natAbs_pow, Int.natAbs_natCast, NumberField.RingOfIntegers.rank]

end GlobalTheory.St.G

namespace GlobalTheory.St.G

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero`.
-/
theorem mlat_T_ne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

/- English proof (translation)
Establish `h` using `(VS D).baseLattice_isUnimodular`. Unfold `Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at h`. Establish `hy' : y ∈ Formalism.E.hdual (VS D).hT (VS D).L0` using `by rw [h]; exact hy`. Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'`. Take `⟨a, ha⟩` from `Submodule.mem_one.1 (hy' x hx)`.

Conclude with `⟨a, by simpa using ha⟩`.
-/
theorem selfDual_lattice_hermitian_form_integral {x y : (VS D).V} (hx : x ∈ (VS D).L0) (hy : y ∈ (VS D).L0) :
    (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h := (VS D).baseLattice_isUnimodular
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at h
  have hy' : y ∈ Formalism.E.hdual (VS D).hT (VS D).L0 := by rw [h]; exact hy
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hy' x hx)
  exact ⟨a, by simpa using ha⟩

/- English proof (translation)
Rewrite using `[X.Lam_split]`. Conclude with `le_sup_left.trans' le_sup_right`.
-/
theorem mlat_Lb_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]; exact le_sup_left.trans' le_sup_right

/- English proof (translation)
The claim follows from `((VS D).herm.eq x y).symm`.
-/
theorem mlat_symm (x y : (VS D).V) : (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
  ((VS D).herm.eq x y).symm

/- English proof (translation)
Rewrite using `[← hW.1]`. Simplify using `only [qFr, LinearEquiv.apply_symm_apply, xFr]`. Rewrite using `[D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]`. Both sides reduce to the same expression.
-/
theorem mlat_gram (hW : WittX X u wt) (i j : Fin (D.R.N 0)) :
    (VS D).hT (qFr wt i) (qFr wt j) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j := by
  rw [← hW.1]
  simp only [qFr, LinearEquiv.apply_symm_apply, xFr]
  rw [D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

/- English proof (translation)
Use `⟨fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hW.1, hW.2.1, mlat_symm]`. Simplify using `[qFr, xFr, (D.sp.hyp_orthX a _).1]`. Rewrite using `[← hW.1, hW.2.2.1, mlat_symm]`. Simplify using `[qFr, xFr, (D.sp.hyp_orthX a _).2]`.

Rewrite using `[← hW.1, hW.2.2.2, mlat_symm]`. Simplify using `only [qFr, LinearEquiv.apply_symm_apply, xFr, D7.zmOf, map_smul, map_smulₛₗ]`. Simplify using `[D.sp.zm_orth]`.
-/
theorem mlat_perp (hW : WittX X u wt) (j : Fin (D.R.N 0)) :
    (∀ a, (VS D).hT (X.eX a) (qFr wt j) = 0 ∧ (VS D).hT (X.fY a) (qFr wt j) = 0) ∧
      (VS D).hT (X.zu u) (qFr wt j) = 0 := by
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← hW.1, hW.2.1, mlat_symm]; simp [qFr, xFr, (D.sp.hyp_orthX a _).1]
  · rw [← hW.1, hW.2.2.1, mlat_symm]; simp [qFr, xFr, (D.sp.hyp_orthX a _).2]
  · rw [← hW.1, hW.2.2.2, mlat_symm]
    simp only [qFr, LinearEquiv.apply_symm_apply, xFr, D7.zmOf, map_smul, map_smulₛₗ]
    simp [D.sp.zm_orth]

end GlobalTheory.St.G

namespace GlobalTheory.St.G

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}

/- English proof (translation)
Simplify using `only [Fintype.linearCombination_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mlat_gram hW, Formalism.UG.hform, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply]`. Establish `: ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)) (d i) = starRingEnd D.host.E (d i)` using `rfl`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mlat_hT_lc (hW : WittX X u wt) (d d' : Fin (D.R.N 0) → D.host.E) :
    (VS D).hT (Fintype.linearCombination D.host.E (qFr wt) d) (Fintype.linearCombination D.host.E (qFr wt) d') =
      Formalism.UG.hform (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) d d' := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, mlat_gram hW, Formalism.UG.hform, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  have : ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)) (d i) = starRingEnd D.host.E (d i) := rfl
  rw [this]; ring

/- English proof (translation)
Simplify using `only [Fintype.linearCombination_apply, map_sum, map_smul, (mlat_perp hW _).2, ((mlat_perp hW _).1 _).1, ((mlat_perp hW _).1 _).2, smul_zero, Finset.sum_const_zero, and_self, implies_true]`.
-/
theorem mlat_lc_perp (hW : WittX X u wt) (d : Fin (D.R.N 0) → D.host.E) :
    (∀ a, (VS D).hT (X.eX a) (Fintype.linearCombination D.host.E (qFr wt) d) = 0 ∧
      (VS D).hT (X.fY a) (Fintype.linearCombination D.host.E (qFr wt) d) = 0) ∧
      (VS D).hT (X.zu u) (Fintype.linearCombination D.host.E (qFr wt) d) = 0 := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, (mlat_perp hW _).2, ((mlat_perp hW _).1 _).1,
    ((mlat_perp hW _).1 _).2, smul_zero, Finset.sum_const_zero, and_self, implies_true]

/- English proof (translation)
Use `⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩` and prove the remaining obligations. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => intro x _; exact ⟨0, by simp [Formalism.UG.hform]⟩`. Consider the case `add a b _ _ ha hb`.

Introduce `x hx`. Take `⟨p, hp⟩` from `ha x hx`. Take `⟨q, hq⟩` from `hb x hx`. Use `⟨p + q, ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hp hq ⊢`.

Rewrite using `[map_add, hp, hq]`. Consider the case `smul c a _ ha`. Introduce `x hx`. Take `⟨p, hp⟩` from `ha x hx`. Use `⟨c * p, ?_⟩` and prove the remaining obligations.

Simplify using `only [Formalism.UG.hform, Pi.smul_apply] at hp ⊢`. Rewrite using `[map_mul, hp, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mlat_mem_dualL {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → D.host.E) :
    y ∈ dualL (Formalism.L2.Forms.sigD D) J L ↔ y ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J L := by
  refine ⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro x _; exact ⟨0, by simp [Formalism.UG.hform]⟩
  | add a b _ _ ha hb =>
    intro x hx
    obtain ⟨p, hp⟩ := ha x hx
    obtain ⟨q, hq⟩ := hb x hx
    refine ⟨p + q, ?_⟩
    simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hp hq ⊢
    rw [map_add, hp, hq]
  | smul c a _ ha =>
    intro x hx
    obtain ⟨p, hp⟩ := ha x hx
    refine ⟨c * p, ?_⟩
    simp only [Formalism.UG.hform, Pi.smul_apply] at hp ⊢
    rw [map_mul, hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]; ring

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `d hd`. Establish `hdet` using `(GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts D u).2.2.2.2.2.2`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdet ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `h` using `mlat_hT_lc hW (Pi.single i 1) d`. Rewrite `h` using `[hd, map_zero]`. Simplify `h.symm` using `[Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct]`.
-/
theorem mlat_inj (hW : WittX X u wt) : Function.Injective (Fintype.linearCombination D.host.E (qFr wt)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro d hd
  have hdet := (GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts D u).2.2.2.2.2.2
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
  funext i
  have h := mlat_hT_lc hW (Pi.single i 1) d
  rw [hd, map_zero] at h
  simpa [Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using h.symm

end GlobalTheory.St.G

namespace GlobalTheory.St.G

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨hLb, ⟨x₀, hx₀Lb, hx₀z⟩, -⟩` from `GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing D X u`. Establish `hWc` using `GlobalTheory.T.orthogonal_hyperbolicFrame_anisotropic_mem_span_transported D X u wt hW`. Use `set T : ℕ := (D.mem u).A.T with hTdef`. Use `set φ := Fintype.linearCombination D.host.E (qFr wt) with hφ`. Use `set h := (VS D).hT with hh`.

Use `set z := X.zu u with hz`. Establish `hT0 : (T : D.host.E) ≠ 0` using `mlat_T_ne`. Establish `hzz : h z z = -(T : D.host.E)` using `X.zu_norm u`. Establish `hzLb : z ∈ X.Lb` using `X.zu_Lb u`. Establish `hx0L0` using `mlat_Lb_le hx₀Lb`.

Establish `hzL0` using `mlat_Lb_le hzLb`. Establish `hx₀z' : h x₀ z = 1` using `by rw [hh, mlat_symm, ← hh, hx₀z, map_one]`. Establish `hTstar : starRingEnd D.host.E ((T : D.host.E)⁻¹) = (T : D.host.E)⁻¹` using `by simp`. Use `set w₀ := x₀ + (T : D.host.E)⁻¹ • z with hw₀`. Establish `hw0e : ∀ a, h (X.eX a) w₀ = 0 ∧ h (X.fY a) w₀ = 0`.

Introduce `a`. Simplify using `[w₀, (X.Lb_perp _ hx₀Lb a).1, (X.Lb_perp _ hx₀Lb a).2, (X.zu_orth u a).1, (X.zu_orth u a).2, h, z]`. Establish `hw0z : h z w₀ = 0`. Simplify using `only [w₀, map_add, map_smul, hx₀z, hzz, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨d, hd⟩` from `hWc w₀ hw0e hw0z`. Establish `hmem : ∀ x, x ∈ Mq wt ↔ φ x ∈ (VS D).L0` using `fun x => Iff.rfl`. Establish `hmemLb : ∀ x, x ∈ Mq wt ↔ φ x ∈ X.Lb` using `fun x => (hmem x).trans ((hLb (φ x) (mlat_lc_perp hW x).1).1)`. Establish `hdual : ∀ y, y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) ↔ ∀ x ∈ Mq wt, h (φ x) (φ y) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`.

Introduce `y`. Rewrite using `[mlat_mem_dualL]`. Simplify using `only [dualSet, Set.mem_setOf_eq, hh, hφ, mlat_hT_lc hW]`. Establish `hperp0 : ∀ x, h (φ x) z = 0` using `fun x => by rw [hh, mlat_symm, ← hh, (mlat_lc_perp hW x).2, map_zero]`. Establish `hsmulLb : ∀ (c : D.host.E), c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range → ∀ v ∈ X.Lb, c • v ∈ X.Lb`.

Introduce and unpack `c ⟨c', rfl⟩ v hv`. Rewrite using `[algebraMap_smul]`. Conclude with `X.Lb.smul_mem c' hv`. Establish `hsmulM : ∀ (c : D.host.E), c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range → ∀ v ∈ Mq wt, c • v ∈ Mq wt`. Introduce and unpack `c ⟨c', rfl⟩ v hv`.

Rewrite using `[algebraMap_smul]`. Conclude with `(Mq wt).smul_mem c' hv`. Establish `hC : ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), (T : D.host.E) * h x₀ (φ y) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧ y - ((T : D.host.E) * h x₀ (φ y)) • d ∈ Mq wt`. Introduce `y hy`. Establish `hYp` using `mlat_lc_perp hW y`.

Use `set Y := φ y with hY`. Use `set Y' := Y - h x₀ Y • z with hY'`. Establish `hY'perp : ∀ a, h (X.eX a) Y' = 0 ∧ h (X.fY a) Y' = 0`. Introduce `a`. Simplify using `[Y', (hYp.1 a).1, (hYp.1 a).2, (X.zu_orth u a).1, (X.zu_orth u a).2, h, z]`.

Establish `hY'Lb : Y' ∈ X.Lb`. Use `(hLb Y' hY'perp).2 fun x hx => ?_` and prove the remaining obligations. Use `set c := h z x with hc`. Establish `hcint : c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range` using `selfDual_lattice_hermitian_form_integral hzL0 (mlat_Lb_le hx)`. Use `set m := x - c • x₀ with hm`.

Establish `hmLb : m ∈ X.Lb` using `X.Lb.sub_mem hx (hsmulLb c hcint x₀ hx₀Lb)`. Establish `hmz : h z m = 0` using `by simp [m, map_sub, map_smul, hx₀z, c]`. Take `⟨xm, hxm⟩` from `hWc m (X.Lb_perp m hmLb) hmz`. Establish `hxmM : xm ∈ Mq wt` using `(hmemLb xm).2 (hxm ▸ hmLb)`. Establish `h1 : h m Y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`.

Rewrite using `[← hxm]`. Conclude with `(hdual y).1 hy xm hxmM`. Establish `hmz' : h m z = 0` using `by rw [hh, mlat_symm, ← hh, hmz, map_zero]`. Establish `hx' : x = m + c • x₀` using `by simp [m]`. Rewrite using `[hx']`.

Establish `e : h (m + c • x₀) Y' = h m Y`. Simplify using `only [Y', map_add, map_smulₛₗ, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hmz', hx₀z', smul_eq_mul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1`.

Establish `hYz : h z Y = 0` using `hYp.2`. Establish `hb : h z Y' = (T : D.host.E) * h x₀ Y`. Simplify using `only [Y', map_sub, map_smul, hYz, hzz, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbint : (T : D.host.E) * h x₀ Y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range` using `hb ▸ selfDual_lattice_hermitian_form_integral hzL0 (mlat_Lb_le hY'Lb)`.

Use `⟨hbint, (hmemLb _).2 ?_⟩` and prove the remaining obligations. Establish `hbT : (T : D.host.E) * h x₀ Y * (T : D.host.E)⁻¹ = h x₀ Y` using `by field_simp`. Establish `e : φ (y - ((T : D.host.E) * h x₀ Y) • d) = Y' - ((T : D.host.E) * h x₀ Y) • x₀`. Rewrite using `[map_sub, map_smul, hd, ← hY]`. Simplify using `only [Y', w₀, smul_add, smul_smul, hbT]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `X.Lb.sub_mem hY'Lb (hsmulLb _ hbint x₀ hx₀Lb)`. Establish `hdD : d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)`. Use `(hdual d).2 fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[hd]`. Simplify using `only [w₀, map_add, map_smul, hperp0, smul_zero, add_zero]`. Conclude with `selfDual_lattice_hermitian_form_integral ((hmem x).1 hx) hx0L0`. Establish `hTd : (T : D.host.E) • d ∈ Mq wt`. Use `(hmem _).2 ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hd]`. Simplify using `only [w₀, smul_add, smul_smul, mul_inv_cancel₀ hT0, one_smul]`. Use `(VS D).L0.add_mem ?_ hzL0` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hx0L0 T`.

Establish `hw0w0 : h w₀ w₀ = h x₀ x₀ + (T : D.host.E)⁻¹`. Simplify using `only [w₀, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, hx₀z, hx₀z', hzz, hTstar, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∀ x ∈ Mq wt, x ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)`.

Introduce `x hx x' hx'`. Rewrite using `[← mlat_hT_lc hW]`. Conclude with `selfDual_lattice_hermitian_form_integral ((hmem _).1 hx') ((hmem _).1 hx)`. Establish `hnorm : Formalism.UG.hform (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) d d - ((T : D.host.E))⁻¹ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`. Rewrite using `[← mlat_hT_lc hW, hd, ← hh, hw0w0, add_sub_cancel_right]`.

Conclude with `selfDual_lattice_hermitian_form_integral hx0L0 hx0L0`. Establish `hLat : IsLat (Mq wt)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg`. Set `f : Mq wt →ₗ[𝓞 D.host.E] (VS D).L0` to `LinearMap.codRestrict (VS D).L0 ((φ.restrictScalars (𝓞 D.host.E)).comp (Mq wt).subtype) (fun x => x.2)`.

Use `Module.Finite.of_injective f ?_` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `mlat_inj hW` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hab`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `hspan` using `(VS D).standardTuple_isLattice.span_eq_top`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E ((VS D).L0 : Set (VS D).V) (φ y) (by rw [hspan]; trivial)`. Rewrite `ht` using `[Submodule.span_eq, Submonoid.smul_def]`.

Establish `htM : ((t : 𝓞 D.host.E)) • y ∈ Mq wt`. Use `(hmem _).2 ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul D.host.E (t : 𝓞 D.host.E) y, map_smul, algebraMap_smul]`. Conclude with `ht`. Establish `ht0 : algebraMap (𝓞 D.host.E) D.host.E t ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero t.2)`.

Establish `e : y = (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ • ((t : 𝓞 D.host.E) • y)`. Rewrite using `[← algebraMap_smul D.host.E (t : 𝓞 D.host.E) y, smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span htM)`. Establish `hkill : ∀ y ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), (T : D.host.E) • y ∈ Mq wt`.

Introduce `y hy`. Take `⟨hb, hyM⟩` from `hC y (Submodule.subset_span hy)`. Establish `e : (T : D.host.E) • y = (T : D.host.E) • (y - ((T : D.host.E) * h x₀ (φ y)) • d) + ((T : D.host.E) * h x₀ (φ y)) • ((T : D.host.E) • d)`. Rewrite using `[smul_sub, smul_smul, smul_smul, mul_comm]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Use `(Mq wt).add_mem ?_ (hsmulM _ hb _ hTd)` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hyM T`. Establish `hidx : (Mq wt).toAddSubgroup.relIndex (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup = T ^ (2 * D.R.f)`.

Establish `key : ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = (T : D.host.E) * h x₀ (φ y)` using `fun y hy => (hC y hy).1`. Use `choose B hB using key`. Establish `hinjO` using `IsFractionRing.injective (𝓞 D.host.E) D.host.E`. Set `ψ : (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup →+ (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)})` to `AddMonoidHom.mk' (fun y => Ideal.Quotient.mk _ (B y.1 y.2)) (by`. Introduce `a b`.

Rewrite using `[← map_add]`. Use `congr 1`. Apply `hinjO` to reduce the goal to its premises. Simplify using `only [hB, map_add, AddSubgroup.coe_add, mul_add])`. Establish `hψ : ∀ y, ψ y = Ideal.Quotient.mk _ (B y.1 y.2)` using `fun y => rfl`.

Establish `hsurj : Function.Surjective ψ`. Introduce `q`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `had` using `Submodule.smul_mem (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)) a hdD`. Take `⟨e, he⟩ : h x₀ x₀ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range` from `selfDual_lattice_hermitian_form_integral hx0L0 hx0L0`.

Use `⟨⟨_, had⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Use `⟨a * e, hinjO ?_⟩` and prove the remaining obligations. Establish `hBa` using `hB (a • d) had`. Establish `hφa : φ (a • d) = algebraMap (𝓞 D.host.E) D.host.E a • w₀`.

Rewrite using `[← algebraMap_smul D.host.E a d, map_smul, hd]`. Rewrite `hBa` using `[hφa]`. Use `show algebraMap (𝓞 D.host.E) D.host.E (a * e * ((T : ℕ) : 𝓞 D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E (B (a • d) had - a)`. Rewrite using `[map_sub, hBa, map_mul, map_mul, map_natCast]`. Simplify using `only [hw₀, map_add, map_smul, smul_eq_mul, hx₀z', ← he]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hker : ψ.ker = (Mq wt).toAddSubgroup.addSubgroupOf (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup`. Use extensionality with `⟨y, hy⟩`. Rewrite using `[AddMonoidHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton', AddSubgroup.mem_addSubgroupOf]`.

Simplify using `only [Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `hc' : (T : D.host.E) * h x₀ (φ y) = algebraMap (𝓞 D.host.E) D.host.E c * (T : D.host.E)`. Rewrite using `[← hB y hy, ← hc, map_mul, map_natCast]`.

Establish `e : y = (y - ((T : D.host.E) * h x₀ (φ y)) • d) + algebraMap (𝓞 D.host.E) D.host.E c • ((T : D.host.E) • d)`. Rewrite using `[smul_smul, ← hc']`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `(Mq wt).add_mem (hC y hy).2 (hsmulM _ ⟨c, rfl⟩ _ hTd)`.

Introduce `hyM`. Take `⟨c, hc⟩` from `selfDual_lattice_hermitian_form_integral hx0L0 ((hmem y).1 hyM)`. Use `⟨c, hinjO ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc, hB y hy, map_natCast, mul_comm]`. Rewrite using `[AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top, mlat_card, (GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts D u).2.2.2.1]`.

Use `⟨⟨hLat, hint, hkill, hidx, fun v hv => ?_⟩, x₀, hx₀Lb, hx₀z, d, hdD, hd, fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.hermitian_dual_vector_norm_inv_not_mem_local D.host.F D.host.E D.sp.cm (D.R.N 0) _ (Mq wt) hint d T (D.mem u).A.T_prime.pos hdD hnorm v hv`. Take `⟨⟨b, hb⟩, hyM⟩` from `hC y hy`. Use `⟨b, ?_⟩` and prove the remaining obligations. Establish `: ((b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b` using `rfl`.

Rewrite using `[this, hb]`. Conclude with `hyM`.
-/
theorem mlat_main (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) : TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt) ∧ ∃ x₀ ∈ X.Lb, (VS D).hT (X.zu u) x₀ = 1 ∧ ∃ d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), Fintype.linearCombination D.host.E (qFr wt) d = x₀ + (((D.mem u).A.T : D.host.E))⁻¹ • X.zu u ∧ ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ a : 𝓞 D.host.E, y - (a : D.host.E) • d ∈ Mq wt := by
  obtain ⟨hLb, ⟨x₀, hx₀Lb, hx₀z⟩, -⟩ := GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing D X u
  have hWc := GlobalTheory.T.orthogonal_hyperbolicFrame_anisotropic_mem_span_transported D X u wt hW
  set T : ℕ := (D.mem u).A.T with hTdef
  set φ := Fintype.linearCombination D.host.E (qFr wt) with hφ
  set h := (VS D).hT with hh
  set z := X.zu u with hz
  have hT0 : (T : D.host.E) ≠ 0 := mlat_T_ne
  have hzz : h z z = -(T : D.host.E) := X.zu_norm u
  have hzLb : z ∈ X.Lb := X.zu_Lb u
  have hx0L0 := mlat_Lb_le hx₀Lb
  have hzL0 := mlat_Lb_le hzLb
  have hx₀z' : h x₀ z = 1 := by rw [hh, mlat_symm, ← hh, hx₀z, map_one]
  have hTstar : starRingEnd D.host.E ((T : D.host.E)⁻¹) = (T : D.host.E)⁻¹ := by simp
  set w₀ := x₀ + (T : D.host.E)⁻¹ • z with hw₀
  have hw0e : ∀ a, h (X.eX a) w₀ = 0 ∧ h (X.fY a) w₀ = 0 := by
    intro a
    simp [w₀, (X.Lb_perp _ hx₀Lb a).1, (X.Lb_perp _ hx₀Lb a).2, (X.zu_orth u a).1, (X.zu_orth u a).2, h, z]
  have hw0z : h z w₀ = 0 := by
    simp only [w₀, map_add, map_smul, hx₀z, hzz, smul_eq_mul]
    field_simp; ring
  obtain ⟨d, hd⟩ := hWc w₀ hw0e hw0z
  have hmem : ∀ x, x ∈ Mq wt ↔ φ x ∈ (VS D).L0 := fun x => Iff.rfl
  have hmemLb : ∀ x, x ∈ Mq wt ↔ φ x ∈ X.Lb := fun x => (hmem x).trans ((hLb (φ x) (mlat_lc_perp hW x).1).1)
  have hdual : ∀ y, y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) ↔
      ∀ x ∈ Mq wt, h (φ x) (φ y) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [mlat_mem_dualL]
    simp only [dualSet, Set.mem_setOf_eq, hh, hφ, mlat_hT_lc hW]

  have hperp0 : ∀ x, h (φ x) z = 0 := fun x => by rw [hh, mlat_symm, ← hh, (mlat_lc_perp hW x).2, map_zero]
  have hsmulLb : ∀ (c : D.host.E), c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range → ∀ v ∈ X.Lb, c • v ∈ X.Lb := by
    rintro c ⟨c', rfl⟩ v hv
    rw [algebraMap_smul]; exact X.Lb.smul_mem c' hv
  have hsmulM : ∀ (c : D.host.E), c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range → ∀ v ∈ Mq wt, c • v ∈ Mq wt := by
    rintro c ⟨c', rfl⟩ v hv
    rw [algebraMap_smul]; exact (Mq wt).smul_mem c' hv

  have hC : ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt),
      (T : D.host.E) * h x₀ (φ y) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        y - ((T : D.host.E) * h x₀ (φ y)) • d ∈ Mq wt := by
    intro y hy
    have hYp := mlat_lc_perp hW y
    set Y := φ y with hY
    set Y' := Y - h x₀ Y • z with hY'
    have hY'perp : ∀ a, h (X.eX a) Y' = 0 ∧ h (X.fY a) Y' = 0 := by
      intro a
      simp [Y', (hYp.1 a).1, (hYp.1 a).2, (X.zu_orth u a).1, (X.zu_orth u a).2, h, z]
    have hY'Lb : Y' ∈ X.Lb := by
      refine (hLb Y' hY'perp).2 fun x hx => ?_
      set c := h z x with hc
      have hcint : c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := selfDual_lattice_hermitian_form_integral hzL0 (mlat_Lb_le hx)
      set m := x - c • x₀ with hm
      have hmLb : m ∈ X.Lb := X.Lb.sub_mem hx (hsmulLb c hcint x₀ hx₀Lb)
      have hmz : h z m = 0 := by simp [m, map_sub, map_smul, hx₀z, c]
      obtain ⟨xm, hxm⟩ := hWc m (X.Lb_perp m hmLb) hmz
      have hxmM : xm ∈ Mq wt := (hmemLb xm).2 (hxm ▸ hmLb)
      have h1 : h m Y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        rw [← hxm]; exact (hdual y).1 hy xm hxmM
      have hmz' : h m z = 0 := by rw [hh, mlat_symm, ← hh, hmz, map_zero]
      have hx' : x = m + c • x₀ := by simp [m]
      rw [hx']
      have e : h (m + c • x₀) Y' = h m Y := by
        simp only [Y', map_add, map_smulₛₗ, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hmz', hx₀z', smul_eq_mul, RingHom.id_apply]
        ring
      rw [e]; exact h1
    have hYz : h z Y = 0 := hYp.2
    have hb : h z Y' = (T : D.host.E) * h x₀ Y := by
      simp only [Y', map_sub, map_smul, hYz, hzz, smul_eq_mul]; ring
    have hbint : (T : D.host.E) * h x₀ Y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
      hb ▸ selfDual_lattice_hermitian_form_integral hzL0 (mlat_Lb_le hY'Lb)
    refine ⟨hbint, (hmemLb _).2 ?_⟩
    have hbT : (T : D.host.E) * h x₀ Y * (T : D.host.E)⁻¹ = h x₀ Y := by field_simp
    have e : φ (y - ((T : D.host.E) * h x₀ Y) • d) = Y' - ((T : D.host.E) * h x₀ Y) • x₀ := by
      rw [map_sub, map_smul, hd, ← hY]
      simp only [Y', w₀, smul_add, smul_smul, hbT]
      abel
    rw [e]
    exact X.Lb.sub_mem hY'Lb (hsmulLb _ hbint x₀ hx₀Lb)
  have hdD : d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) := by
    refine (hdual d).2 fun x hx => ?_
    rw [hd]
    simp only [w₀, map_add, map_smul, hperp0, smul_zero, add_zero]
    exact selfDual_lattice_hermitian_form_integral ((hmem x).1 hx) hx0L0
  have hTd : (T : D.host.E) • d ∈ Mq wt := by
    refine (hmem _).2 ?_
    rw [map_smul, hd]
    simp only [w₀, smul_add, smul_smul, mul_inv_cancel₀ hT0, one_smul]
    refine (VS D).L0.add_mem ?_ hzL0
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx0L0 T
  have hw0w0 : h w₀ w₀ = h x₀ x₀ + (T : D.host.E)⁻¹ := by
    simp only [w₀, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, hx₀z, hx₀z', hzz,
      hTstar, smul_eq_mul]
    field_simp; ring

  have hint : ∀ x ∈ Mq wt, x ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) := by
    intro x hx x' hx'
    rw [← mlat_hT_lc hW]
    exact selfDual_lattice_hermitian_form_integral ((hmem _).1 hx') ((hmem _).1 hx)
  have hnorm : Formalism.UG.hform (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) d d -
      ((T : D.host.E))⁻¹ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    rw [← mlat_hT_lc hW, hd, ← hh, hw0w0, add_sub_cancel_right]
    exact selfDual_lattice_hermitian_form_integral hx0L0 hx0L0
  have hLat : IsLat (Mq wt) := by
    refine ⟨?_, ?_⟩
    · haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg
      let f : Mq wt →ₗ[𝓞 D.host.E] (VS D).L0 :=
        LinearMap.codRestrict (VS D).L0 ((φ.restrictScalars (𝓞 D.host.E)).comp (Mq wt).subtype) (fun x => x.2)
      refine Module.Finite.of_injective f ?_
      intro a b hab
      apply Subtype.ext
      apply mlat_inj hW
      exact congrArg Subtype.val hab
    · rw [eq_top_iff]
      intro y _
      have hspan := (VS D).standardTuple_isLattice.span_eq_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E
        ((VS D).L0 : Set (VS D).V) (φ y) (by rw [hspan]; trivial)
      rw [Submodule.span_eq, Submonoid.smul_def] at ht
      have htM : ((t : 𝓞 D.host.E)) • y ∈ Mq wt := by
        refine (hmem _).2 ?_
        rw [← algebraMap_smul D.host.E (t : 𝓞 D.host.E) y, map_smul, algebraMap_smul]
        exact ht
      have ht0 : algebraMap (𝓞 D.host.E) D.host.E t ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero t.2)
      have e : y = (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ • ((t : 𝓞 D.host.E) • y) := by
        rw [← algebraMap_smul D.host.E (t : 𝓞 D.host.E) y, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span htM)
  have hkill : ∀ y ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), (T : D.host.E) • y ∈ Mq wt := by
    intro y hy
    obtain ⟨hb, hyM⟩ := hC y (Submodule.subset_span hy)
    have e : (T : D.host.E) • y = (T : D.host.E) • (y - ((T : D.host.E) * h x₀ (φ y)) • d) +
        ((T : D.host.E) * h x₀ (φ y)) • ((T : D.host.E) • d) := by
      rw [smul_sub, smul_smul, smul_smul, mul_comm]; abel
    rw [e]
    refine (Mq wt).add_mem ?_ (hsmulM _ hb _ hTd)
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hyM T

  have hidx : (Mq wt).toAddSubgroup.relIndex
      (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup = T ^ (2 * D.R.f) := by
    have key : ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt),
        ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = (T : D.host.E) * h x₀ (φ y) :=
      fun y hy => (hC y hy).1
    choose B hB using key
    have hinjO := IsFractionRing.injective (𝓞 D.host.E) D.host.E
    let ψ : (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup →+
        (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)}) :=
      AddMonoidHom.mk' (fun y => Ideal.Quotient.mk _ (B y.1 y.2)) (by
        intro a b
        rw [← map_add]
        congr 1
        apply hinjO
        simp only [hB, map_add, AddSubgroup.coe_add, mul_add])
    have hψ : ∀ y, ψ y = Ideal.Quotient.mk _ (B y.1 y.2) := fun y => rfl
    have hsurj : Function.Surjective ψ := by
      intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      have had := Submodule.smul_mem (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)) a hdD
      obtain ⟨e, he⟩ : h x₀ x₀ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := selfDual_lattice_hermitian_form_integral hx0L0 hx0L0
      refine ⟨⟨_, had⟩, ?_⟩
      rw [hψ, Ideal.Quotient.eq, Ideal.mem_span_singleton']
      refine ⟨a * e, hinjO ?_⟩
      have hBa := hB (a • d) had
      have hφa : φ (a • d) = algebraMap (𝓞 D.host.E) D.host.E a • w₀ := by
        rw [← algebraMap_smul D.host.E a d, map_smul, hd]
      rw [hφa] at hBa
      show algebraMap (𝓞 D.host.E) D.host.E (a * e * ((T : ℕ) : 𝓞 D.host.E)) =
        algebraMap (𝓞 D.host.E) D.host.E (B (a • d) had - a)
      rw [map_sub, hBa, map_mul, map_mul, map_natCast]
      simp only [hw₀, map_add, map_smul, smul_eq_mul, hx₀z', ← he]
      field_simp
      ring
    have hker : ψ.ker = (Mq wt).toAddSubgroup.addSubgroupOf
        (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup := by
      ext ⟨y, hy⟩
      rw [AddMonoidHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton',
        AddSubgroup.mem_addSubgroupOf]
      simp only [Submodule.mem_toAddSubgroup]
      constructor
      · rintro ⟨c, hc⟩
        have hc' : (T : D.host.E) * h x₀ (φ y) = algebraMap (𝓞 D.host.E) D.host.E c * (T : D.host.E) := by
          rw [← hB y hy, ← hc, map_mul, map_natCast]
        have e : y = (y - ((T : D.host.E) * h x₀ (φ y)) • d) + algebraMap (𝓞 D.host.E) D.host.E c • ((T : D.host.E) • d) := by
          rw [smul_smul, ← hc']; abel
        rw [e]
        exact (Mq wt).add_mem (hC y hy).2 (hsmulM _ ⟨c, rfl⟩ _ hTd)
      · intro hyM
        obtain ⟨c, hc⟩ := selfDual_lattice_hermitian_form_integral hx0L0 ((hmem y).1 hyM)
        refine ⟨c, hinjO ?_⟩
        rw [map_mul, hc, hB y hy, map_natCast, mul_comm]
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top, mlat_card,
      (GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts D u).2.2.2.1]
  refine ⟨⟨hLat, hint, hkill, hidx, fun v hv => ?_⟩, x₀, hx₀Lb, hx₀z, d, hdD, hd, fun y hy => ?_⟩
  · exact GlobalTheory.T.hermitian_dual_vector_norm_inv_not_mem_local D.host.F D.host.E D.sp.cm (D.R.N 0) _ (Mq wt) hint d T (D.mem u).A.T_prime.pos hdD hnorm v hv
  · obtain ⟨⟨b, hb⟩, hyM⟩ := hC y hy
    refine ⟨b, ?_⟩
    have : ((b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b := rfl
    rw [this, hb]
    exact hyM

end GlobalTheory.St.G
