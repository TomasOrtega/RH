import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardAddMonoidHomZmodLe

open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift ReciprocityTheory.Gal

namespace GlobalTheory.Cyc.CocycleCount

/- English proof (translation)
Establish `hker : LinearMap.ker (d0 rho) = H0 rho`. Use extensionality with `m`. Rewrite using `[LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]`. Prove the components needed by the constructor for the conclusion. Introduce `h g`.

Establish `hg` using `congrFun h g`. Rewrite `hg` using `[amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]`. Conclude with `hg`. Introduce `h`. Use function extensionality and compare the values at `g`.

Rewrite using `[amitsur_d0_apply, Pi.zero_apply, h g, sub_self]`. Establish `hM : Nat.card M = Nat.card (H0 rho) * Nat.card (B1 rho)`. Rewrite using `[(LinearMap.ker (d0 rho)).card_eq_card_quotient_mul_card, Nat.card_congr (LinearMap.quotKerEquivRange (d0 rho)).toEquiv, hker]`. Both sides reduce to the same expression. Establish `hZ : Nat.card (Z1 rho) = Nat.card (B1 rho) * Nat.card (H1 rho)`.

Rewrite using `[((B1 rho).comap (Z1 rho).subtype).card_eq_card_quotient_mul_card, Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles rho h)).toEquiv]`. Rewrite using `[hZ, hM]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_Z1_mul_card_H0 {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (h : ContAction rho) :
    Nat.card (Z1 rho) * Nat.card (H0 rho) = Nat.card M * Nat.card (H1 rho) := by
  have hker : LinearMap.ker (d0 rho) = H0 rho := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have hg := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at hg
      exact hg
    · intro h
      funext g
      rw [amitsur_d0_apply, Pi.zero_apply, h g, sub_self]
  have hM : Nat.card M = Nat.card (H0 rho) * Nat.card (B1 rho) := by
    rw [(LinearMap.ker (d0 rho)).card_eq_card_quotient_mul_card,
      Nat.card_congr (LinearMap.quotKerEquivRange (d0 rho)).toEquiv, hker]
    rfl
  have hZ : Nat.card (Z1 rho) = Nat.card (B1 rho) * Nat.card (H1 rho) := by
    rw [((B1 rho).comap (Z1 rho).subtype).card_eq_card_quotient_mul_card,
      Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles rho h)).toEquiv]
  rw [hZ, hM]
  ring

/- English proof (translation)
Break down `le_or_gt r N with h | h` into its components or cases. Rewrite using `[Nat.sub_eq_zero_of_le h, pow_zero]`. Conclude with `one_dvd _`. Establish `h1 : ((l ^ N * a.val : ℕ) : ZMod (l ^ r)) = 0`. Use `push_cast`.

Rewrite using `[ZMod.natCast_zmod_val]`. Conclude with `ha`. Rewrite `h1` using `[CharP.cast_eq_zero_iff (ZMod (l ^ r)) (l ^ r)]`. Establish `h2 : l ^ r = l ^ N * l ^ (r - N)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' h.le]`.

Establish `h3 : l ^ N * l ^ (r - N) ∣ l ^ N * a.val`. Rewrite using `[← h2]`. Conclude with `h1`. Conclude with `Nat.dvd_of_mul_dvd_mul_left (pow_pos hl N) h3`.
-/
private theorem pow_sub_dvd_val_of_pow_mul_eq_zero {l : ℕ} (hl : 0 < l) (N r : ℕ) [NeZero (l ^ r)] (a : ZMod (l ^ r))
    (ha : (l : ZMod (l ^ r)) ^ N * a = 0) : l ^ (r - N) ∣ a.val := by
  rcases le_or_gt r N with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    exact one_dvd _
  · have h1 : ((l ^ N * a.val : ℕ) : ZMod (l ^ r)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact ha
    rw [CharP.cast_eq_zero_iff (ZMod (l ^ r)) (l ^ r)] at h1
    have h2 : l ^ r = l ^ N * l ^ (r - N) := by
      rw [← pow_add, Nat.add_sub_cancel' h.le]
    have h3 : l ^ N * l ^ (r - N) ∣ l ^ N * a.val := by
      rw [← h2]
      exact h1
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hl N) h3

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `: NeZero (l ^ r)` using `⟨(pow_pos hl r).ne'⟩`. Set `g : X → Fin (l ^ N)` to `fun x => ⟨(f x).val / l ^ (r - N), by`. Rewrite using `[Nat.div_lt_iff_lt_mul (pow_pos hl _), ← pow_add]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hg : Function.Injective g`. Introduce `x y hxy`. Apply `hf` to reduce the goal to its premises. Apply `ZMod.val_injective` to reduce the goal to its premises. Establish `hx` using `pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f x) (hann x)`.

Establish `hy` using `pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f y) (hann y)`. Establish `e : (f x).val / l ^ (r - N) = (f y).val / l ^ (r - N)` using `congrArg Fin.val hxy`. Rewrite using `[← Nat.div_mul_cancel hx, ← Nat.div_mul_cancel hy, e]`. Establish `hc` using `Nat.card_le_card_of_injective g hg`. Simplify using `using hc`.
-/
private theorem card_le_pow_of_injective_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (N r : ℕ) {X : Type*} (f : X → ZMod (l ^ r))
    (hf : Function.Injective f) (hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0) :
    Nat.card X ≤ l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  let g : X → Fin (l ^ N) := fun x => ⟨(f x).val / l ^ (r - N), by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hl _), ← pow_add]
    calc (f x).val < l ^ r := ZMod.val_lt _
      _ ≤ l ^ (N + (r - N)) := Nat.pow_le_pow_right hl (by omega)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    apply ZMod.val_injective
    have hx := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f x) (hann x)
    have hy := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f y) (hann y)
    have e : (f x).val / l ^ (r - N) = (f y).val / l ^ (r - N) := congrArg Fin.val hxy
    rw [← Nat.div_mul_cancel hx, ← Nat.div_mul_cancel hy, e]
  have hc := Nat.card_le_card_of_injective g hg
  simpa using hc

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G]

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `: NeZero (l ^ r)` using `⟨(pow_pos hl r).ne'⟩`. Establish `key : ∀ (φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r))) (m : ZMod (l ^ r)), φ m = m * φ 1`. Introduce `φ m`. Establish `h` using `LinearMap.map_smul (show Module.Dual (ZMod (l ^ r)) (ZMod (l ^ r)) from φ) m 1`.

Rewrite `h` using `[smul_eq_mul, smul_eq_mul, mul_one]`. Conclude with `h`. Set `f : H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) → ZMod (l ^ r)` to `fun x => x.1 1`. Establish `hf : Function.Injective f`. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `TDual.ext` to reduce the goal to its premises. Introduce `m`. Rewrite using `[key x.1 m, key y.1 m]`. Conclude with `congrArg (m * ·) hxy`.

Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 hg.le)`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ))` using `zpow_pos (by exact_mod_cast hl) _`. Establish `hvn : ‖v‖ = 1`. Establish `hn` using `congrArg norm hv`. Rewrite `hn` using `[norm_mul, PadicInt.norm_p_pow, hg]`.

Conclude with `mul_right_cancel₀ hpos.ne' (hn.trans (one_mul _).symm)`. Establish `hvu : IsUnit (PadicInt.toZModPow r v)` using `(PadicInt.isUnit_iff.2 hvn).map _`. Establish `hred : (redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1 = PadicInt.toZModPow r v * (l : ZMod (l ^ r)) ^ N`. Establish `e` using `congrArg (PadicInt.toZModPow r) hv`. Simplify using `only [map_mul, map_pow, map_natCast, map_sub, map_one] at e`.

Rewrite using `[redChar_apply, redChar_apply, e]`. Establish `hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0`. Introduce `x`. Establish `h0 : ∀ g, twDual (redChar χ r) (charRep (redChar ψ r)) g x.1 = x.1`. Establish `hx` using `x.2`.

Conclude with `hx`. Establish `h1` using `congrArg (fun φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) => φ 1) (h0 g₀)`. Simplify using `only [twDual_apply, charRep_apply, mul_one] at h1`. Rewrite `h1` using `[key x.1]`. Establish `h2 : ((redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1) * f x = 0` using `by show _ * x.1 1 = 0`.

Take the linear combination `h1`. Rewrite `h2` using `[hred, mul_assoc]`. Conclude with `hvu.mul_right_eq_zero.1 h2`. Conclude with `⟨Finite.of_injective f hf, card_le_pow_of_injective_of_pow_mul_eq_zero N r f hf hann⟩`.
-/
theorem card_invariants_twistedDual_charRep_le_pow (χ ψ : G →* ℤ_[l]ˣ) (N r : ℕ)
    (g₀ : G) (hg : ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ))) :
    Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ∧
    Nat.card (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ≤
      l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have key : ∀ (φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r))) (m : ZMod (l ^ r)), φ m = m * φ 1 := by
    intro φ m
    have h := LinearMap.map_smul (show Module.Dual (ZMod (l ^ r)) (ZMod (l ^ r)) from φ) m 1
    rw [smul_eq_mul, smul_eq_mul, mul_one] at h
    exact h
  let f : H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →
      ZMod (l ^ r) := fun x => x.1 1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply TDual.ext
    intro m
    rw [key x.1 m, key y.1 m]
    exact congrArg (m * ·) hxy
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 hg.le)
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ)) := zpow_pos (by exact_mod_cast hl) _
  have hvn : ‖v‖ = 1 := by
    have hn := congrArg norm hv
    rw [norm_mul, PadicInt.norm_p_pow, hg] at hn
    exact mul_right_cancel₀ hpos.ne' (hn.trans (one_mul _).symm)
  have hvu : IsUnit (PadicInt.toZModPow r v) := (PadicInt.isUnit_iff.2 hvn).map _
  have hred : (redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1 =
      PadicInt.toZModPow r v * (l : ZMod (l ^ r)) ^ N := by
    have e := congrArg (PadicInt.toZModPow r) hv
    simp only [map_mul, map_pow, map_natCast, map_sub, map_one] at e
    rw [redChar_apply, redChar_apply, e]
  have hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0 := by
    intro x
    have h0 : ∀ g, twDual (redChar χ r) (charRep (redChar ψ r)) g x.1 = x.1 := by
      have hx := x.2
      exact hx
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) => φ 1) (h0 g₀)
    simp only [twDual_apply, charRep_apply, mul_one] at h1
    rw [key x.1] at h1
    have h2 : ((redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1) * f x = 0 := by
      show _ * x.1 1 = 0
      linear_combination h1
    rw [hred, mul_assoc] at h2
    exact hvu.mul_right_eq_zero.1 h2
  exact ⟨Finite.of_injective f hf, card_le_pow_of_injective_of_pow_mul_eq_zero N r f hf hann⟩

/- English proof (translation)
Introduce `l _ G _ _ _ χ ψ hψ N r d g₀ hg hH2 hinj hH1`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `: NeZero (l ^ r)` using `⟨(pow_pos hl r).ne'⟩`. Establish `hcont : ContAction (charRep (redChar ψ r))`. Apply `contAction_charRep` to reduce the goal to its premises.

Establish `e : (fun g => ((redChar ψ r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) = fun g => PadicInt.toZModPow r (ψ g : ℤ_[l])` using `funext fun g => redChar_apply ψ r g`. Rewrite using `[e]`. Conclude with `(continuous_toZModPow r).comp hψ`. Establish `h1` using `card_Z1_mul_card_H0 (charRep (redChar ψ r)) hcont`. Take `⟨hfin0, hle0⟩` from `card_invariants_twistedDual_charRep_le_pow χ ψ N r g₀ hg`.

Take `⟨e⟩` from `hH2`. Set `F : H2 (charRep (redChar ψ r)) → (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+ ZMod (l ^ r))` to `fun c => (e.toLinearMap ∘ₗ (cup20 (redChar χ r) (charRep (redChar ψ r)) (MonoidHom.id G) c)).toAddMonoidHom`. Establish `hF : Function.Injective F`. Introduce `c c' hcc`. Apply `hinj` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Apply `e.injective` to reduce the goal to its premises. Conclude with `DFunLike.congr_fun hcc y`. Establish `: Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+ ZMod (l ^ r))` using `Finite.of_injective _ DFunLike.coe_injective`.

Establish `: Finite (H2 (charRep (redChar ψ r)))` using `Finite.of_injective F hF`. Establish `hc2 : Nat.card (H2 (charRep (redChar ψ r))) ≤ l ^ N` using `((Nat.card_le_card_of_injective F hF).trans (GlobalTheory.natCard_addMonoidHom_zmod_le (l ^ r) _)).trans hle0`. Establish `hc2pos : 0 < Nat.card (H2 (charRep (redChar ψ r)))` using `Nat.card_pos`. Establish `h0pos : 0 < Nat.card (H0 (charRep (redChar ψ r)))` using `Nat.card_pos`. Establish `hZ : Nat.card (Z1 (charRep (redChar ψ r))) = l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d)`.

Apply `Nat.eq_of_mul_eq_mul_right h0pos` to reduce the goal to its premises. Rewrite using `[h1, hH1, Nat.card_zmod]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Nat.finite_of_card_ne_zero (by rw [hZ]; positivity), ?_⟩` and prove the remaining obligations. Rewrite using `[hZ]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_cocycles_charRep_modPow_le_of_duality : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ ψ : G →* ℤ_[l]ˣ), (Continuous fun g => (ψ g : ℤ_[l])) → ∀ (N r d : ℕ) (g₀ : G), ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ)) → Nonempty (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar χ r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) → Function.Injective (ReciprocityTheory.Gal.cup20 (redChar χ r) (ReciprocityTheory.Gal.charRep (redChar ψ r)) (MonoidHom.id G)) → Nat.card (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ZMod (l ^ r)) ^ d → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ l ^ N * l ^ (r * (d + 1)) := by
  intro l _ G _ _ _ χ ψ hψ N r d g₀ hg hH2 hinj hH1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have hcont : ContAction (charRep (redChar ψ r)) := by
    apply contAction_charRep
    have e : (fun g => ((redChar ψ r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) =
        fun g => PadicInt.toZModPow r (ψ g : ℤ_[l]) := funext fun g => redChar_apply ψ r g
    rw [e]
    exact (continuous_toZModPow r).comp hψ
  have h1 := card_Z1_mul_card_H0 (charRep (redChar ψ r)) hcont
  obtain ⟨hfin0, hle0⟩ := card_invariants_twistedDual_charRep_le_pow χ ψ N r g₀ hg
  obtain ⟨e⟩ := hH2
  let F : H2 (charRep (redChar ψ r)) →
      (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+ ZMod (l ^ r)) :=
    fun c => (e.toLinearMap ∘ₗ
      (cup20 (redChar χ r) (charRep (redChar ψ r)) (MonoidHom.id G) c)).toAddMonoidHom
  have hF : Function.Injective F := by
    intro c c' hcc
    apply hinj
    apply LinearMap.ext
    intro y
    apply e.injective
    exact DFunLike.congr_fun hcc y
  have : Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+
      ZMod (l ^ r)) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (H2 (charRep (redChar ψ r))) := Finite.of_injective F hF
  have hc2 : Nat.card (H2 (charRep (redChar ψ r))) ≤ l ^ N :=
    ((Nat.card_le_card_of_injective F hF).trans
      (GlobalTheory.natCard_addMonoidHom_zmod_le (l ^ r) _)).trans hle0
  have hc2pos : 0 < Nat.card (H2 (charRep (redChar ψ r))) := Nat.card_pos
  have h0pos : 0 < Nat.card (H0 (charRep (redChar ψ r))) := Nat.card_pos
  have hZ : Nat.card (Z1 (charRep (redChar ψ r))) =
      l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d) := by
    apply Nat.eq_of_mul_eq_mul_right h0pos
    rw [h1, hH1, Nat.card_zmod]
    ring
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hZ]; positivity), ?_⟩
  rw [hZ]
  calc l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d)
      ≤ l ^ r * (l ^ N * (l ^ r) ^ d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc2)
    _ = l ^ N * l ^ (r * (d + 1)) := by ring

end GlobalTheory.Cyc.CocycleCount
