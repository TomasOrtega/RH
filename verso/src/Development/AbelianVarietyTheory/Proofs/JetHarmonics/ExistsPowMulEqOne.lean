import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFinOrd

/- English proof (translation)
Establish `h₁ : ∀ i : ℕ, U ^ i * W = e ^ i • (W * U ^ i)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`.

Rewrite using `[pow_succ', _root_.mul_assoc, ih, mul_smul_comm, ← _root_.mul_assoc, h, smul_mul_assoc, smul_smul, _root_.mul_assoc, pow_succ e]`. Establish `h₂ : ∀ n : ℕ, ∃ t : ℕ, (U * W) ^ n = e ^ t • (W ^ n * U ^ n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `succ n ih`. Take `⟨t, ht⟩` from `ih`. Use `⟨t + (n + 1), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, ht, smul_mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (U ^ n), ← pow_succ, h₁, mul_smul_comm, smul_smul, ← pow_add, ← _root_.mul_assoc, ← pow_succ]`. Establish `h₃ : e ^ M • (1 : A) = 1`.

Establish `a` using `h₁ M`. Rewrite `a` using `[hU, _root_.one_mul, _root_.mul_one]`. Take `⟨m, rfl⟩ : ∃ m, M' = m + 1` from `⟨M' - 1, by omega⟩`. Establish `b : W ^ m * W = W ^ m * (e ^ M • W)` using `congrArg _ a`. Rewrite `b` using `[mul_smul_comm, ← pow_succ, hW]`.

Conclude with `b.symm`. Take `⟨t, ht⟩` from `h₂ (M * M')`. Use `⟨M * M' * M, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[pow_mul U, hU, one_pow, mul_comm M M', pow_mul W, hW, one_pow, _root_.mul_one]`. Rewrite using `[mul_comm M M', pow_mul, ht, smul_pow, one_pow, ← pow_mul, mul_comm t M, pow_mul]`.

Use `congrArg (· ^ t) h₃` as an intermediate fact. Simplify `this` using `only [smul_pow, one_pow]`.
-/
theorem exists_pow_mul_eq_one {F A : Type} [Field F] [Ring A] [Algebra F A] (U W : A) (e : F)
    (h : U * W = e • (W * U)) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hU : U ^ M = 1) (hW : W ^ M' = 1) :
    ∃ n, 1 ≤ n ∧ (U * W) ^ n = 1 := by
  have h₁ : ∀ i : ℕ, U ^ i * W = e ^ i • (W * U ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', _root_.mul_assoc, ih, mul_smul_comm, ← _root_.mul_assoc, h, smul_mul_assoc, smul_smul,
        _root_.mul_assoc, pow_succ e]
  have h₂ : ∀ n : ℕ, ∃ t : ℕ, (U * W) ^ n = e ^ t • (W ^ n * U ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (n + 1), ?_⟩
      rw [pow_succ, ht, smul_mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (U ^ n), ← pow_succ, h₁,
        mul_smul_comm, smul_smul, ← pow_add, ← _root_.mul_assoc, ← pow_succ]
  have h₃ : e ^ M • (1 : A) = 1 := by
    have a := h₁ M
    rw [hU, _root_.one_mul, _root_.mul_one] at a
    obtain ⟨m, rfl⟩ : ∃ m, M' = m + 1 := ⟨M' - 1, by omega⟩
    have b : W ^ m * W = W ^ m * (e ^ M • W) := congrArg _ a
    rw [mul_smul_comm, ← pow_succ, hW] at b
    exact b.symm
  obtain ⟨t, ht⟩ := h₂ (M * M')
  refine ⟨M * M' * M, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
  rw [pow_mul U, hU, one_pow, mul_comm M M', pow_mul W, hW, one_pow, _root_.mul_one] at ht
  rw [mul_comm M M', pow_mul, ht, smul_pow, one_pow, ← pow_mul, mul_comm t M, pow_mul]
  have := congrArg (· ^ t) h₃
  simpa only [smul_pow, one_pow] using this

/- English proof (translation)
Rewrite `h`, the goal using `[isAdd_iff]`. Use `⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩` and prove the remaining obligations. Establish `C : IsCub (th D (T` using `TF (R := R) F) y J) := isCub_cubV D.cub hJ`. Rewrite using `[C.s12, h.2 χ y J hJ, mul_comm]`.
-/
theorem isAdd_symm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

/- English proof (translation)
Take `⟨c, -, hc⟩` from `TWM.exists_ratio (F := F) D.toPre.P.isLB w hw w' hw' (fun _ _ _ => rfl)`. Use `⟨c, LinearMap.ext fun s => ?_⟩` and prove the remaining obligations. Use `phi_unique p w ((phiRel_iff hG p w hw _ _).1 (hΦ s)) ?_` and prove the remaining obligations. Introduce `a β hβ T ρ z J hJ`. Establish `h1` using `(phiRel_iff hG p w' hw' s (Φ' s)).1 (hΦ' s) a β hβ T ρ z J hJ`.

Establish `h2` using `hc _ (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z J hJ`. Rewrite using `[LinearMap.smul_apply, sval_smul c (Φ' s) β ρ.left z hJ, h1, val_mul hJ, val_mul hJ]`. Simplify using `only [Units.val_mul]`. Establish `alg : ∀ {S : Type} [CommRing S] (g a u x y y' : S), y = g * y' → g * (a * (u * (x * y'))) = a * (u * (x * y))` using `fun g a u x y y' h => by rw [h]; ring`. Conclude with `alg _ _ _ _ _ _ h2`.
-/
theorem exists_scalar (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (hw : w.IsGen) (hw' : w'.IsGen) (Φ Φ' : Fam D.toPre F k →ₗ[F] Fam D.toPre F k)
    (hΦ : ∀ s, PhiRel D.toPre F k p w s (Φ s)) (hΦ' : ∀ s, PhiRel D.toPre F k p w' s (Φ' s)) :
    ∃ c : F, Φ = c • Φ' := by
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio (F := F) D.toPre.P.isLB w hw w' hw' (fun _ _ _ => rfl)
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  refine phi_unique p w ((phiRel_iff hG p w hw _ _).1 (hΦ s)) ?_
  intro a β hβ T ρ z J hJ
  have h1 := (phiRel_iff hG p w' hw' s (Φ' s)).1 (hΦ' s) a β hβ T ρ z J hJ
  have h2 := hc _ (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z J hJ
  rw [LinearMap.smul_apply, sval_smul c (Φ' s) β ρ.left z hJ, h1, val_mul hJ, val_mul hJ]
  simp only [Units.val_mul]
  have alg : ∀ {S : Type} [CommRing S] (g a u x y y' : S), y = g * y' →
      g * (a * (u * (x * y'))) = a * (u * (x * y)) := fun g a u x y y' h => by rw [h]; ring
  exact alg _ _ _ _ _ _ h2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨M, hM, H⟩`. Use `⟨M, hM, LinearMap.ext fun s => ?_⟩` and prove the remaining obligations. Use `H (fun i => ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s) (fun i => Φ (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)) (fun i => ⟨(hΦ _ _).2 rfl, by` as an intermediate fact. Rewrite using `[DVR.isSmul_iff, Fin.val_succ, pow_succ', Module.End.mul_apply, LinearMap.smul_apply]⟩)`.

Conclude with `fam_ext this`. Introduce and unpack `⟨M, hM, hpow⟩`. Use `⟨M, hM, fun ss ts H α j => ?_⟩` and prove the remaining obligations. Establish `hstep : ∀ i : Fin M, ss i.succ = (ζ • Φ) (ss i.castSucc)`. Introduce `i`.

Take `⟨h1, h2⟩` from `H i`. Rewrite `h1` using `[hΦ]`. Rewrite `h2` using `[DVR.isSmul_iff]`. Rewrite using `[h2, h1, LinearMap.smul_apply]`. Establish `hall : ∀ i : ℕ, ∀ hi : i < M + 1, ss ⟨i, hi⟩ = ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ i) (ss 0)`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Both sides reduce to the same expression. Consider the case `succ i ih`.

Introduce `hi`. Rewrite using `[pow_succ', Module.End.mul_apply, ← ih (by omega)]`. Conclude with `hstep ⟨i, by omega⟩`. Establish `hlast : ss (Fin.last M) = ss 0`. Rewrite using `[show Fin.last M = ⟨M, Nat.lt_succ_self M⟩ from rfl, hall M (Nat.lt_succ_self M), hpow]`.

Both sides reduce to the same expression. Rewrite using `[hlast]`.
-/
theorem finOrd_iff {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    FinOrd D F k p w ζ ↔ ∃ M : ℕ, 1 ≤ M ∧ ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) = 1 := by
  constructor
  · rintro ⟨M, hM, H⟩
    refine ⟨M, hM, LinearMap.ext fun s => ?_⟩
    have := H (fun i => ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)
      (fun i => Φ (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)) (fun i => ⟨(hΦ _ _).2 rfl, by
        rw [DVR.isSmul_iff, Fin.val_succ, pow_succ', Module.End.mul_apply, LinearMap.smul_apply]⟩)
    exact fam_ext this
  · rintro ⟨M, hM, hpow⟩
    refine ⟨M, hM, fun ss ts H α j => ?_⟩
    have hstep : ∀ i : Fin M, ss i.succ = (ζ • Φ) (ss i.castSucc) := by
      intro i
      obtain ⟨h1, h2⟩ := H i
      rw [hΦ] at h1
      rw [DVR.isSmul_iff] at h2
      rw [h2, h1, LinearMap.smul_apply]
    have hall : ∀ i : ℕ, ∀ hi : i < M + 1,
        ss ⟨i, hi⟩ = ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ i) (ss 0) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
        exact hstep ⟨i, by omega⟩
    have hlast : ss (Fin.last M) = ss 0 := by
      rw [show Fin.last M = ⟨M, Nat.lt_succ_self M⟩ from rfl, hall M (Nat.lt_succ_self M), hpow]
      rfl
    rw [hlast]

/- English proof (translation)
Take `⟨c, -, hc⟩` from `phiPow_of_globalFns hG V _ D F k hk p w hw`. Use `⟨c, LinearMap.ext fun s => ?_⟩` and prove the remaining obligations. Use `hc (fun i => (Φ ^ (i : ℕ)) s) (fun i => (hΦ _ _).2 (by` as an intermediate fact. Rewrite using `[Fin.val_succ, pow_succ', Module.End.mul_apply]`. Use the proof step `rfl))`.

Rewrite `this` using `[DVR.isSmul_iff]`. Conclude with `this`.
-/
theorem exists_pow_scalar (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Module.End F (Fam D.toPre F k)) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    ∃ c : F, Φ ^ k = c • 1 := by
  obtain ⟨c, -, hc⟩ := phiPow_of_globalFns hG V _ D F k hk p w hw
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  have := hc (fun i => (Φ ^ (i : ℕ)) s) (fun i => (hΦ _ _).2 (by
    rw [Fin.val_succ, pow_succ', Module.End.mul_apply]; rfl))
  rw [DVR.isSmul_iff] at this
  exact this

end GlobalTheory.ThetaFinOrd

namespace GlobalTheory

open ThetaFinOrd in

/- English proof (translation)
Introduce `hL V _ _ _ D F _ _ k hk`. Establish `hG` using `hL.globalFns`. Use `⟨fun p w hw ζ Φ hΦ s M hs hM hfix => ?_, fun p p₁ p₂ hy hg w w₁ w₂ hw hw₁ hw₂ hc ζ ζ₁ h h₁ => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_pow_scalar hG hk p w hw Φ hΦ`. Establish `e : ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ k = ((ζ ^ k * c) ^ M) • 1`.

Rewrite using `[← pow_mul, mul_comm M k, pow_mul, smul_pow, hc, smul_smul, smul_pow, one_pow]`. Establish `f : ∀ n : ℕ, (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ n) s = s`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rfl`.

Consider the case `succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]`. Establish `g` using `f k`. Rewrite `g` using `[e, LinearMap.smul_apply, Module.End.one_apply]`. Establish `g' : (ζ ^ k * c) ^ M = 1`. Establish `: ((ζ ^ k * c) ^ M - 1) • s = 0` using `by rw [sub_smul, g, one_smul, sub_self]`.

Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)`. Use `(finOrd_iff p w ζ Φ hΦ).2 ⟨M * k, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul, e, g', one_smul]`. Take `⟨Φ, hΦ⟩` from `phiFun_of_globalFns hG V _ D F k hk p w hw`. Take `⟨Φ₁, hΦ₁⟩` from `phiFun_of_globalFns hG V _ D F k hk p₁ w₁ hw₁`.

Take `⟨Φ₂, hΦ₂⟩` from `phiFun_of_globalFns hG V _ D F k hk p₂ w₂ hw₂`. Take `⟨w', hw', hc'⟩` from `ThetaMul.phi_mul_core hG p₁ p p₂ (hy.trans (add_comm _ _)) (isAdd_symm hg) w₁ w hw₁ hw`. Establish `e₂ : Φ₂ = (Φ * Φ₁ : Module.End F (Fam D.toPre F k))` using `LinearMap.ext fun s => ((hΦ₂ _ _).1 (hc s _ _ ((hΦ₁ _ _).2 rfl) ((hΦ _ _).2 rfl))).symm`. Take `⟨e, he⟩` from `exists_scalar hG p₂ w₂ w' hw₂ hw' Φ₂ (Φ₁ * Φ : Module.End F (Fam D.toPre F k)) (fun s => (hΦ₂ _ _).2 rfl) (fun s => hc' s _ _ ((hΦ _ _).2 rfl) ((hΦ₁ _ _).2 rfl))`. Take `⟨M, hM, hU⟩` from `(finOrd_iff p w ζ Φ hΦ).1 h`.

Take `⟨M', hM', hW⟩` from `(finOrd_iff p₁ w₁ ζ₁ Φ₁ hΦ₁).1 h₁`. Establish `m : (ζ • Φ : Module.End F (Fam D.toPre F k)) * (ζ₁ • Φ₁ : Module.End F (Fam D.toPre F k)) = (ζ * ζ₁) • Φ₂`. Rewrite using `[e₂, smul_mul_smul_comm]`. Take `⟨n, hn, hp⟩` from `exists_pow_mul_eq_one (F := F) (A := Module.End F (Fam D.toPre F k)) (ζ • Φ) (ζ₁ • Φ₁) e (by rw [m, he, smul_mul_smul_comm, smul_comm, mul_comm ζ₁ ζ]) hM hM' hU hW`. Rewrite `hp` using `[m]`.

Conclude with `(finOrd_iff p₂ w₂ _ Φ₂ hΦ₂).2 ⟨n, hn, hp⟩`.
-/
theorem finOrd_criteria : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ (p : QkPt D.toPre F k) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), w.IsGen → ∀ (ζ : F) (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) → ∀ (s : Fam D.toPre F k) (M : ℕ), s ≠ 0 → 1 ≤ M → ((ζ • Φ) ^ M) s = s → FinOrd D F k p w ζ) ∧ ∀ (p p₁ p₂ : QkPt D.toPre F k), p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))) (w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → w₂.IsGen → (∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t') → ∀ ζ ζ₁ : F, FinOrd D F k p w ζ → FinOrd D F k p₁ w₁ ζ₁ → FinOrd D F k p₂ w₂ (ζ * ζ₁) := by
  intro hL V _ _ _ D F _ _ k hk
  have hG := hL.globalFns
  refine ⟨fun p w hw ζ Φ hΦ s M hs hM hfix => ?_, fun p p₁ p₂ hy hg w w₁ w₂ hw hw₁ hw₂ hc ζ ζ₁ h h₁ => ?_⟩
  · obtain ⟨c, hc⟩ := exists_pow_scalar hG hk p w hw Φ hΦ
    have e : ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ k = ((ζ ^ k * c) ^ M) • 1 := by
      rw [← pow_mul, mul_comm M k, pow_mul, smul_pow, hc, smul_smul, smul_pow, one_pow]
    have f : ∀ n : ℕ, (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ n) s = s := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
    have g := f k
    rw [e, LinearMap.smul_apply, Module.End.one_apply] at g
    have g' : (ζ ^ k * c) ^ M = 1 := by
      have : ((ζ ^ k * c) ^ M - 1) • s = 0 := by rw [sub_smul, g, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    refine (finOrd_iff p w ζ Φ hΦ).2 ⟨M * k, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    rw [pow_mul, e, g', one_smul]
  · obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
    obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of_globalFns hG V _ D F k hk p₁ w₁ hw₁
    obtain ⟨Φ₂, hΦ₂⟩ := phiFun_of_globalFns hG V _ D F k hk p₂ w₂ hw₂
    obtain ⟨w', hw', hc'⟩ := ThetaMul.phi_mul_core hG p₁ p p₂ (hy.trans (add_comm _ _)) (isAdd_symm hg)
      w₁ w hw₁ hw
    have e₂ : Φ₂ = (Φ * Φ₁ : Module.End F (Fam D.toPre F k)) := LinearMap.ext fun s =>
      ((hΦ₂ _ _).1 (hc s _ _ ((hΦ₁ _ _).2 rfl) ((hΦ _ _).2 rfl))).symm
    obtain ⟨e, he⟩ := exists_scalar hG p₂ w₂ w' hw₂ hw' Φ₂ (Φ₁ * Φ : Module.End F (Fam D.toPre F k))
      (fun s => (hΦ₂ _ _).2 rfl) (fun s => hc' s _ _ ((hΦ _ _).2 rfl) ((hΦ₁ _ _).2 rfl))
    obtain ⟨M, hM, hU⟩ := (finOrd_iff p w ζ Φ hΦ).1 h
    obtain ⟨M', hM', hW⟩ := (finOrd_iff p₁ w₁ ζ₁ Φ₁ hΦ₁).1 h₁
    have m : (ζ • Φ : Module.End F (Fam D.toPre F k)) * (ζ₁ • Φ₁ : Module.End F (Fam D.toPre F k)) =
        (ζ * ζ₁) • Φ₂ := by
      rw [e₂, smul_mul_smul_comm]
    obtain ⟨n, hn, hp⟩ := exists_pow_mul_eq_one (F := F) (A := Module.End F (Fam D.toPre F k)) (ζ • Φ) (ζ₁ • Φ₁) e
      (by rw [m, he, smul_mul_smul_comm, smul_comm, mul_comm ζ₁ ζ]) hM hM' hU hW
    rw [m] at hp
    exact (finOrd_iff p₂ w₂ _ Φ₂ hΦ₂).2 ⟨n, hn, hp⟩

end GlobalTheory
