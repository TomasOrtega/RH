import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Conclude with `Formalism.MainNotions.LiftingTheory.constantCoeff_gamma W g a`.
-/
theorem gradNPf_cc_γ₀ (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  exact Formalism.MainNotions.LiftingTheory.constantCoeff_gamma W g a

/- English proof (translation)
Conclude with `Formalism.MainNotions.LiftingTheory.frame_γA_comm W g h a`.
-/
theorem gradNPf_γA_comm (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  exact Formalism.MainNotions.LiftingTheory.frame_γA_comm W g h a

/- English proof (translation)
Establish `hi` using `congrFun hf i`. Establish `hγi : (W.γA W.gam π') i = W.γ₀ W.gam (π' i)` using `rfl`. Establish `hπi : π' i = (w : LetA O n) i * PowerSeries.X ^ s'` using `by rw [hw]; rfl`. Establish `hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X * PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))` using `by conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]`. Rewrite using `[(W.γ₀_X W.gam).1, map_zero, add_zero]`.

Establish `hh : PowerSeries.constantCoeff (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) = ((W.χΓ W.gam : Oˣ) : O)`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]`. Conclude with `(W.γ₀_X W.gam).2`. Rewrite `hi` using `[hγi, Pi.mul_apply, hπi, map_mul, map_pow, hX, mul_pow]`. Establish `h2 : PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) * (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) ^ s') = PowerSeries.X ^ s' * ((w : LetA O n) i * f i)`.

Take the linear combination `hi`. Establish `h3` using `congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel h2)`. Rewrite `h3` using `[map_mul, map_mul, map_pow, hh, gradNPf_cc_γ₀]`. Establish `hwu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i))` using `(w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map PowerSeries.constantCoeff`. Conclude with `(hwu.mul_left_cancel h3).symm`.
-/
theorem gradNPf_cc_f (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hf : W.γA W.gam π' = π' * f) (i : ZMod n) :
    PowerSeries.constantCoeff (f i) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  have hi := congrFun hf i
  have hγi : (W.γA W.gam π') i = W.γ₀ W.gam (π' i) := rfl
  have hπi : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  have hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X *
      PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X)) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]
    rw [(W.γ₀_X W.gam).1, map_zero, add_zero]
  have hh : PowerSeries.constantCoeff (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1)
      (W.γ₀ W.gam PowerSeries.X))) = ((W.χΓ W.gam : Oˣ) : O) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (W.γ₀_X W.gam).2
  rw [hγi, Pi.mul_apply, hπi, map_mul, map_pow, hX, mul_pow] at hi
  have h2 : PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) *
      (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) ^ s') =
      PowerSeries.X ^ s' * ((w : LetA O n) i * f i) := by
    linear_combination hi
  have h3 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel h2)
  rw [map_mul, map_mul, map_pow, hh, gradNPf_cc_γ₀] at h3
  have hwu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) :=
    (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map PowerSeries.constantCoeff
  exact (hwu.mul_left_cancel h3).symm

/- English proof (translation)
Introduce `δ hδ`. Establish `hu : IsUnit (algebraMap (LetA O n) W.EE π')`. Rewrite using `[hw, map_mul, map_pow]`. Establish `hl : IsUnit (algebraMap (LetA O n) W.EE letπ)` using `by simpa using Formalism.MainNotions.LiftingTheory.wmap_unit W 0`. Conclude with `(w.isUnit.map _).mul (hl.pow _)`.

Apply `Formalism.MainNotions.LiftingTheory.lifta_reg W π' _ _ hu` to reduce the goal to its premises. Establish `h1 : W.γA δ (W.γA W.gam π') = W.γA W.gam π'`. Rewrite using `[Formalism.MainNotions.LiftingTheory.frame_γA_comm, hπΔ δ hδ]`. Rewrite `h1` using `[hf, map_mul, hπΔ δ hδ]`. Conclude with `h1`.
-/
theorem gradNPf_fΔ (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hf : W.γA W.gam π' = π' * f) : ∀ δ ∈ W.DelF, W.γA δ f = f := by
  intro δ hδ
  have hu : IsUnit (algebraMap (LetA O n) W.EE π') := by
    rw [hw, map_mul, map_pow]
    have hl : IsUnit (algebraMap (LetA O n) W.EE letπ) := by simpa using Formalism.MainNotions.LiftingTheory.wmap_unit W 0
    exact (w.isUnit.map _).mul (hl.pow _)
  apply Formalism.MainNotions.LiftingTheory.lifta_reg W π' _ _ hu
  have h1 : W.γA δ (W.γA W.gam π') = W.γA W.gam π' := by
    rw [Formalism.MainNotions.LiftingTheory.frame_γA_comm, hπΔ δ hδ]
  rw [hf, map_mul, hπΔ δ hδ] at h1
  exact h1

/- English proof (translation)
Establish `hS : ∀ i, PowerSeries.HasSubst (π' i)` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)`. Use `⟨fun i => PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e1 : a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)) + PowerSeries.C (PowerSeries.constantCoeff (F i))` using `by conv_lhs => rw [hF i, PowerSeries.eq_X_mul_shift_add_const (F i)]`. Rewrite using `[PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i), PowerSeries.subst_C]`.

Both sides reduce to the same expression. Establish `e3 : PowerSeries.constantCoeff (F i) = c₀`. Use `congrArg PowerSeries.constantCoeff e1` as an intermediate fact. Rewrite `this` using `[hc i, map_add, map_mul, hπ0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C]`. Conclude with `this.symm`.

Rewrite `e1` using `[e3]`. Establish `hC : algebraMap O (PowerSeries O) c₀ = PowerSeries.C c₀`. Rewrite using `[PowerSeries.algebraMap_apply]`. Both sides reduce to the same expression. Use `show a i - algebraMap O (PowerSeries O) c₀ = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i))`.

Rewrite using `[hC, e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gradNPf_expand (π' a : LetA O n) (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (F : ZMod n → PowerSeries O) (hF : ∀ i, a i = PowerSeries.subst (π' i) (F i))
    (c₀ : O) (hc : ∀ i, PowerSeries.constantCoeff (a i) = c₀) :
    ∃ t : LetA O n, a - algebraMap O (LetA O n) c₀ = π' * t := by
  have hS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  refine ⟨fun i => PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)), ?_⟩
  funext i
  have e1 : a i = π' i * PowerSeries.subst (π' i)
      (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)) +
      PowerSeries.C (PowerSeries.constantCoeff (F i)) := by
    conv_lhs => rw [hF i, PowerSeries.eq_X_mul_shift_add_const (F i)]
    rw [PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i),
      PowerSeries.subst_C]
    rfl
  have e3 : PowerSeries.constantCoeff (F i) = c₀ := by
    have := congrArg PowerSeries.constantCoeff e1
    rw [hc i, map_add, map_mul, hπ0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at this
    exact this.symm
  rw [e3] at e1
  have hC : algebraMap O (PowerSeries O) c₀ = PowerSeries.C c₀ := by
    rw [PowerSeries.algebraMap_apply]
    rfl
  show a i - algebraMap O (PowerSeries O) c₀ = π' i * PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i))
  rw [hC, e1]
  ring

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.1`. Establish `hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π'` using `fun δ hδ => hR.1 δ hδ`. Take `⟨w', hw'⟩` from `hR.2.2.2.2.2.2.1`. Take `⟨f, hfdef⟩ : ∃ f : LetA O n, f = 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π'` from `⟨_, rfl⟩`. Establish `hf : W.γA W.gam π' = π' * f`.

Rewrite using `[hfdef]`. Take the linear combination `hw'`. Establish `hfΔ` using `gradNPf_fΔ W s' w π' f hw hπΔ hf`. Take `⟨Fs, hFs, -⟩` from `hR.2.1 f hfΔ`. Establish `hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0`.

Introduce `i`. Establish `: π' i = (w : LetA O n) i * PowerSeries.X ^ s'` using `by rw [hw]; rfl`. Rewrite using `[this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]`. Take `⟨t, ht⟩` from `gradNPf_expand π' f hπ0 Fs hFs _ (gradNPf_cc_f W s' w π' f hw hf)`. Use `⟨f, t, hf, ht, ?_, hπΔ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw, map_mul, map_pow]`. Conclude with `(w.isUnit.map _).mul (W.EE_π.pow _)`. Introduce `y hy`. Take `⟨x', hx', hxe⟩` from `hm y hy`. Use `⟨((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) • x', (W.N T).smul_mem _ hx'.1, ?_⟩` and prove the remaining obligations.

Establish `hπ₀ : π'₀ = ((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π'`. Rewrite using `[hw₀, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]`. Rewrite using `[smul_smul, mul_comm π', ← hπ₀]`. Conclude with `hxe`.
-/
theorem exists_gam_pi_factor (T : LocLat G Qp LL O) (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n)
    (E : ZMod n → Polynomial O) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n)
    (w₀ : (LetA O n)ˣ) (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s')
    (hm : ∀ y ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T y - y = π'₀ • x') :
    ∃ f t : LetA O n, W.γA W.gam π' = π' * f ∧
      f - algebraMap O (LetA O n) (((W.χΓ W.gam : Oˣ) : O) ^ s') = π' * t ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π' := fun δ hδ => hR.1 δ hδ
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.2.1
  obtain ⟨f, hfdef⟩ : ∃ f : LetA O n, f = 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := ⟨_, rfl⟩
  have hf : W.γA W.gam π' = π' * f := by
    rw [hfdef]
    linear_combination hw'
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Fs hFs _ (gradNPf_cc_f W s' w π' f hw hf)
  refine ⟨f, t, hf, ht, ?_, hπΔ, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · intro y hy
    obtain ⟨x', hx', hxe⟩ := hm y hy
    refine ⟨((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) • x', (W.N T).smul_mem _ hx'.1, ?_⟩
    have hπ₀ : π'₀ = ((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π' := by
      rw [hw₀, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]
    rw [smul_smul, mul_comm π', ← hπ₀]
    exact hxe

end Local

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, h9W, -⟩` from `h1 l K 1 LL hG`. Establish `hpl : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Establish `hp : ((D.loc l).PD K).p ≠ 2` using `by rw [hpl]; exact hl`. Establish `hs1 : ((HW l).W K 1 LL hG).s = 1` using `(HW l).W_s K 1 LL hG`. Take `⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩` from `h9W T hT hs1 hp`.

Rewrite `hr₀` using `[hpl]`. Take `⟨w₀, hw₀⟩` from `hr₀.2.2.1`. Take `⟨f, t, hf, ht, hEE, hπΔ, hγN⟩` from `exists_gam_pi_factor _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀.2`. Establish `hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1)` using `Subtype.val_injective`. Establish `hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y`.

Introduce `y`. Rewrite using `[(D.loc l).v_O LL y]`. Conclude with `⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩`. Establish `hlv : (D.loc l).v LL (l : ↥LL.1) = 1` using `(D.loc l).v_l LL`. Establish `hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1`.

Rewrite using `[map_natCast]`. Conclude with `hlv`. Establish `hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1`. Use `((HW l).W K 1 LL hG).gam_gen` as an intermediate fact. Rewrite `this` using `[hs1, Nat.cast_one]`.

Conclude with `this`. Take `⟨u, hu, hxu⟩` from `gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv (l : ↥(OL LL)) _ hlO hxv`. Establish `hsl : ¬ l ∣ sK l K`. Apply `Nat.not_dvd_of_pos_of_lt hs` to reduce the goal to its premises. Establish `h2` using `hpf.out.two_le`.

Conclude with `lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)`. Conclude with `⟨f, t, (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ), u, hu, hxu, hf, ht, hEE, hπΔ, hγN, ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp, fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _ u hu hxu (sK l K) (by omega) hsl N⟩`.
-/
theorem gradNPf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hs : 1 ≤ sK l K) :
    ∃ (f t : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x u : ↥(OL LL)),
      IsUnit u ∧ x - 1 = (l : ↥(OL LL)) * u ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * f ∧
      f - algebraMap ↥(OL LL) (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x ^ sK l K) = π' * t ∧
      IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
      (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
      (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
        ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
      ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
      ∀ N : ℕ, ∃ a : ↥(OL LL), (l : ↥(OL LL)) ^ (N + padicValNat l N.factorial) =
        a * ∏ y ∈ Finset.Ico 1 (N + 1), ((x ^ sK l K) ^ y - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  obtain ⟨f, t, hf, ht, hEE, hπΔ, hγN⟩ :=
    exists_gam_pi_factor _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀.2
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact ⟨f, t, (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ), u, hu, hxu, hf, ht, hEE, hπΔ, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp,
    fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _ u hu hxu
      (sK l K) (by omega) hsl N⟩

end Formalism.MainNotions.N.Ln34

end
