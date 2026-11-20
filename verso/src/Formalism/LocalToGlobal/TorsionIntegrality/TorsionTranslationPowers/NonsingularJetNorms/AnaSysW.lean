import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftPtsInt

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace AnaSysW

open Formalism.L2.Th1

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])

/- English proof (translation)
Use `first`. Consider the case `(rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [A.logSer, A.integ, PowerSeries.coeff_mk])`. Consider the case `(simp only [A.logSer, A.integ]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; simp)`.
-/
theorem lg0 : constantCoeff (A.logSer W) = 0 := by
  first
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [A.logSer, A.integ, PowerSeries.coeff_mk])
  | (simp only [A.logSer, A.integ]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; simp)

/- English proof (translation)
Use `first`. Consider the case `(simp only [A.logSer, A.integ, PowerSeries.coeff_mk]; simp [A.om, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit])`. Consider the case `(simp [A.logSer, A.integ, A.om, PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply])`.
-/
theorem lg1 : coeff 1 (A.logSer W) = 1 := by
  first
  | (simp only [A.logSer, A.integ, PowerSeries.coeff_mk]; simp [A.om, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit])
  | (simp [A.logSer, A.integ, A.om, PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply])

/- English proof (translation)
Introduce `h`. Establish `h1` using `lg1 (W := W)`. Rewrite `h1` using `[h]`. Simplify using `at h1`.
-/
theorem lg_ne : A.logSer W ≠ 0 := by
  intro h
  have h1 := lg1 (W := W)
  rw [h] at h1
  simp at h1

/- English proof (translation)
Use `first`. Consider the case `exact HasSubst.of_constantCoeff_zero' (lg0 (W := W))`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero' (lg0 (W := W))`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero (lg0 (W := W))`.
-/
theorem lgS : HasSubst (A.logSer W) := by
  first
  | exact HasSubst.of_constantCoeff_zero' (lg0 (W := W))
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' (lg0 (W := W))
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (lg0 (W := W))

/- English proof (translation)
Establish `h` using `(F.taylorRing.1 f g hf hg).2`. Unfold `inW`. Rewrite using `[h, map_mul]`. Use `first`. Consider the case `exact PowerSeries.subst_mul (lgS (W := W)) _ _`.

Consider the case `exact PowerSeries.subst_mul (ha := lgS (W := W)) _ _`. Consider the case `(rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact map_mul _ _ _)`. Consider the case `simp [PowerSeries.subst_mul, lgS]`.
-/
theorem inW_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    inW l ι W (fun z => f z * g z) = inW l ι W f * inW l ι W g := by
  have h := (F.taylorRing.1 f g hf hg).2
  unfold inW
  rw [h, map_mul]
  first
  | exact PowerSeries.subst_mul (lgS (W := W)) _ _
  | exact PowerSeries.subst_mul (ha := lgS (W := W)) _ _
  | (rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact map_mul _ _ _)
  | simp [PowerSeries.subst_mul, lgS]

/- English proof (translation)
Establish `h` using `(F.taylorRing.1 f g hf hg).1`. Unfold `inW`. Rewrite using `[h, map_add]`. Use `first`. Consider the case `exact PowerSeries.subst_add (lgS (W := W)) _ _`.

Consider the case `exact PowerSeries.subst_add (ha := lgS (W := W)) _ _`. Consider the case `(rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact map_add _ _ _)`. Consider the case `simp [PowerSeries.subst_add, lgS]`.
-/
theorem inW_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    inW l ι W (fun z => f z + g z) = inW l ι W f + inW l ι W g := by
  have h := (F.taylorRing.1 f g hf hg).1
  unfold inW
  rw [h, map_add]
  first
  | exact PowerSeries.subst_add (lgS (W := W)) _ _
  | exact PowerSeries.subst_add (ha := lgS (W := W)) _ _
  | (rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact map_add _ _ _)
  | simp [PowerSeries.subst_add, lgS]

/- English proof (translation)
Unfold `inW`. Rewrite using `[F.taylorRing.2.1 c, PowerSeries.map_C]`. Use `first`. Consider the case `exact PowerSeries.subst_C (lgS (W := W)) _`. Consider the case `exact PowerSeries.subst_C (ha := lgS (W := W)) _`.

Consider the case `(rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact (PowerSeries.substAlgHom _).commutes _)`. Consider the case `simp [PowerSeries.subst_C, lgS]`.
-/
theorem inW_const (c : ℂ) : inW l ι W (fun _ => c) = C (ι c) := by
  unfold inW
  rw [F.taylorRing.2.1 c, PowerSeries.map_C]
  first
  | exact PowerSeries.subst_C (lgS (W := W)) _
  | exact PowerSeries.subst_C (ha := lgS (W := W)) _
  | (rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact (PowerSeries.substAlgHom _).commutes _)
  | simp [PowerSeries.subst_C, lgS]

/- English proof (translation)
Unfold `inW`. Rewrite using `[F.taylorRing.2.2.1, PowerSeries.map_X]`. Use `first`. Consider the case `exact PowerSeries.subst_X (lgS (W := W))`. Consider the case `exact PowerSeries.subst_X (ha := lgS (W := W))`.

Consider the case `simp [PowerSeries.subst_X, lgS]`.
-/
theorem inW_id : inW l ι W (fun z => z) = A.logSer W := by
  unfold inW
  rw [F.taylorRing.2.2.1, PowerSeries.map_X]
  first
  | exact PowerSeries.subst_X (lgS (W := W))
  | exact PowerSeries.subst_X (ha := lgS (W := W))
  | simp [PowerSeries.subst_X, lgS]

/- English proof (translation)
Unfold `inW`. Rewrite using `[F.taylorRing.2.2.2 f g h]`.
-/
theorem inW_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : inW l ι W f = inW l ι W g := by
  unfold inW
  rw [F.taylorRing.2.2.2 f g h]

/- English proof (translation)
Unfold `inW`. Establish `hS : constantCoeff (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 f)) = ι (f 0)`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]`. Simplify using `[F.taylor0, PowerSeries.coeff_mk]`. Establish `ha` using `lgS (W := W)`.

Establish `h0` using `lg0 (W := W)`. Establish `hX : PowerSeries.subst (A.logSer W) (X : PowerSeries ℂ_[l]) = A.logSer W` using `by first`. Consider the case `exact PowerSeries.subst_X ha`. Consider the case `exact PowerSeries.subst_X (ha := ha)`. Consider the case `simp [PowerSeries.subst_X, ha]`.

Establish `hC : ∀ c : ℂ_[l], PowerSeries.subst (A.logSer W) (C c : PowerSeries ℂ_[l]) = C c`. Introduce `c`. Use `first`. Consider the case `exact PowerSeries.subst_C ha c`. Consider the case `exact PowerSeries.subst_C (ha := ha) c`.

Consider the case `(rw [← PowerSeries.coe_substAlgHom ha]; exact (PowerSeries.substAlgHom ha).commutes c)`. Consider the case `simp [PowerSeries.subst_C, ha]`. Rewrite using `[PowerSeries.eq_shift_mul_X_add_const (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 f)), ← PowerSeries.coe_substAlgHom ha, map_add, map_mul, PowerSeries.coe_substAlgHom, hX, hC]`. Simplify using `[h0, hS]`.
-/
theorem cc_inW (f : ℂ → ℂ) : constantCoeff (inW l ι W f) = ι (f 0) := by
  unfold inW
  have hS : constantCoeff (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 f)) = ι (f 0) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp [F.taylor0, PowerSeries.coeff_mk]
  have ha := lgS (W := W)
  have h0 := lg0 (W := W)
  have hX : PowerSeries.subst (A.logSer W) (X : PowerSeries ℂ_[l]) = A.logSer W := by
    first
    | exact PowerSeries.subst_X ha
    | exact PowerSeries.subst_X (ha := ha)
    | simp [PowerSeries.subst_X, ha]
  have hC : ∀ c : ℂ_[l], PowerSeries.subst (A.logSer W) (C c : PowerSeries ℂ_[l]) = C c := by
    intro c
    first
    | exact PowerSeries.subst_C ha c
    | exact PowerSeries.subst_C (ha := ha) c
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact (PowerSeries.substAlgHom ha).commutes c)
    | simp [PowerSeries.subst_C, ha]
  rw [PowerSeries.eq_shift_mul_X_add_const (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 f)),
    ← PowerSeries.coe_substAlgHom ha, map_add, map_mul, PowerSeries.coe_substAlgHom, hX, hC]
  simp [h0, hS]

def Rd (f : ℂ → ℂ) (S : PowerSeries ℂ_[l]) : Prop := AnalyticAt ℂ f 0 ∧ inW l ι W f = S

variable {l ι W}

/- English proof (translation)
Use `⟨hf.1.mul hg.1, ?_⟩` and prove the remaining obligations. Rewrite using `[inW_mul (l := l) (ι := ι) (W := W) hf.1 hg.1, hf.2, hg.2]`.
-/
theorem Rd.mul {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l ι W f S) (hg : Rd l ι W g T) :
    Rd l ι W (fun z => f z * g z) (S * T) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  rw [inW_mul (l := l) (ι := ι) (W := W) hf.1 hg.1, hf.2, hg.2]

/- English proof (translation)
Use `⟨hf.1.add hg.1, ?_⟩` and prove the remaining obligations. Rewrite using `[inW_add (l := l) (ι := ι) (W := W) hf.1 hg.1, hf.2, hg.2]`.
-/
theorem Rd.add {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l ι W f S) (hg : Rd l ι W g T) :
    Rd l ι W (fun z => f z + g z) (S + T) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  rw [inW_add (l := l) (ι := ι) (W := W) hf.1 hg.1, hf.2, hg.2]

variable (l ι W)

/- English proof (translation)
Conclude with `⟨analyticAt_const, inW_const (l := l) (ι := ι) (W := W) c⟩`.
-/
theorem Rd.const (c : ℂ) : Rd l ι W (fun _ => c) (C (ι c)) := by
  exact ⟨analyticAt_const, inW_const (l := l) (ι := ι) (W := W) c⟩

/- English proof (translation)
Use `⟨?_, inW_id (l := l) (ι := ι) (W := W)⟩` and prove the remaining obligations. Apply the tactic sequence `first | exact analyticAt_id | fun_prop`.
-/
theorem Rd.id : Rd l ι W (fun z => z) (A.logSer W) := by
  refine ⟨?_, inW_id (l := l) (ι := ι) (W := W)⟩
  first | exact analyticAt_id | fun_prop

/- English proof (translation)
Establish `hs : Differentiable ℂ (F.wSigma L)` using `F.sigmaEntire L`. Establish `hd : Differentiable ℂ (F.opU L x (F.sgStar L))`. Unfold `F.opU F.sgStar F.herm`. Use `fun_prop`. Use `⟨?_, rfl⟩` and prove the remaining obligations.

Use `first`. Consider the case `exact hd.analyticAt 0`. Consider the case `exact Differentiable.analyticAt hd 0`.
-/
theorem Rd.opU (x : ℂ) :
    Rd l ι W (F.opU L x (F.sgStar L)) (inW l ι W (F.opU L x (F.sgStar L))) := by
  have hs : Differentiable ℂ (F.wSigma L) := F.sigmaEntire L
  have hd : Differentiable ℂ (F.opU L x (F.sgStar L)) := by
    unfold F.opU F.sgStar F.herm
    fun_prop
  refine ⟨?_, rfl⟩
  first
  | exact hd.analyticAt 0
  | exact Differentiable.analyticAt hd 0

/- English proof (translation)
Unfold `phW`. Conclude with `B.Ph.constantCoeff_phO _ _ (lg0 (W := W)) (lg1 (W := W))`.
-/
theorem cc_phW : constantCoeff (phW l L ι W) = 0 := by
  unfold phW
  exact B.Ph.constantCoeff_phO _ _ (lg0 (W := W)) (lg1 (W := W))

/- English proof (translation)
Establish `hT : F.taylor0 (F.sgStar L) = B.sgStar (F.s2 L) (F.pSeries L)` using `AnaSys.taylorSgStar L`. Establish `hM` using `(B.Map.baseChangeCompatible ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (F.s2 L) 0 0 (F.pSeries L) 0 PowerSeries.X 0 (by simp) (by simp) (by simp)).2.1`. Establish `hD` using `(B.Ph.logSigmaPullbackSpec ℂ_[l] (ι (F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L)) (A.logSer W) (lg0 (W := W)) (lg1 (W := W))).2`. Unfold `inW phW`. Rewrite using `[hT, hM]`.

Conclude with `hD`.
-/
theorem inW_sgStar : inW l ι W (F.sgStar L) = X * B.fExp (-(phW l L ι W)) := by
  have hT : F.taylor0 (F.sgStar L) = B.sgStar (F.s2 L) (F.pSeries L) := AnaSys.taylorSgStar L
  have hM := (B.Map.baseChangeCompatible ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (F.s2 L) 0 0 (F.pSeries L) 0
    PowerSeries.X 0 (by simp) (by simp) (by simp)).2.1
  have hD := (B.Ph.logSigmaPullbackSpec ℂ_[l] (ι (F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L))
    (A.logSer W) (lg0 (W := W)) (lg1 (W := W))).2
  unfold inW phW
  rw [hT, hM]
  exact hD

/- English proof (translation)
Establish `h1 : MvPowerSeries.constantCoeff (phW l L ι W) = 0` using `cc_phW (l := l) (L := L) (ι := ι) (W := W)`. Establish `h2 : MvPowerSeries.constantCoeff (-(phW l L ι W)) = 0` using `by rw [map_neg, h1, neg_zero]`. Rewrite using `[← B.fExp_add h1 h2, add_neg_cancel]`. Establish `h0 : MvPowerSeries.constantCoeff (0 : PowerSeries ℂ_[l]) = 0` using `map_zero _`. Establish `e : (B.fExp (0 : PowerSeries ℂ_[l]) : PowerSeries ℂ_[l]) = B.fExp (0 : PowerSeries ℂ_[l]) * B.fExp (0 : PowerSeries ℂ_[l])`.

Establish `e'` using `B.fExp_add h0 h0`. Rewrite `e'` using `[add_zero]`. Conclude with `e'`. Establish `c` using `B.constantCoeff_fExp h0`. Establish `hne : (B.fExp (0 : PowerSeries ℂ_[l]) : PowerSeries ℂ_[l]) ≠ 0`.

Introduce `hz`. Rewrite `c` using `[hz, map_zero]`. Conclude with `zero_ne_one c`. Conclude with `mul_left_cancel₀ hne (e.symm.trans (mul_one _).symm)`.
-/
theorem fExp_cancel : B.fExp (phW l L ι W) * B.fExp (-(phW l L ι W)) = 1 := by
  have h1 : MvPowerSeries.constantCoeff (phW l L ι W) = 0 := cc_phW (l := l) (L := L) (ι := ι) (W := W)
  have h2 : MvPowerSeries.constantCoeff (-(phW l L ι W)) = 0 := by rw [map_neg, h1, neg_zero]
  rw [← B.fExp_add h1 h2, add_neg_cancel]
  have h0 : MvPowerSeries.constantCoeff (0 : PowerSeries ℂ_[l]) = 0 := map_zero _
  have e : (B.fExp (0 : PowerSeries ℂ_[l]) : PowerSeries ℂ_[l]) = B.fExp (0 : PowerSeries ℂ_[l]) * B.fExp (0 : PowerSeries ℂ_[l]) := by
    have e' := B.fExp_add h0 h0
    rw [add_zero] at e'
    exact e'
  have c := B.constantCoeff_fExp h0
  have hne : (B.fExp (0 : PowerSeries ℂ_[l]) : PowerSeries ℂ_[l]) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at c
    exact zero_ne_one c
  exact mul_left_cancel₀ hne (e.symm.trans (mul_one _).symm)

/- English proof (translation)
Establish `h1 : MvPowerSeries.constantCoeff (phW l L ι W) = 0` using `cc_phW (l := l) (L := L) (ι := ι) (W := W)`. Establish `hc : constantCoeff (B.fExp (phW l L ι W)) = 1` using `B.constantCoeff_fExp h1`. Unfold `gW`. Rewrite using `[map_mul, hc, one_mul, cc_inW]`.
-/
theorem cc_gW (t : ℂ) : constantCoeff (gW l L ι W t) = ι (F.opU L t (F.sgStar L) 0) := by
  have h1 : MvPowerSeries.constantCoeff (phW l L ι W) = 0 := cc_phW (l := l) (L := L) (ι := ι) (W := W)
  have hc : constantCoeff (B.fExp (phW l L ι W)) = 1 := B.constantCoeff_fExp h1
  unfold gW
  rw [map_mul, hc, one_mul, cc_inW]

/- English proof (translation)
Establish `hs : F.semiChar L t = 1 ∨ F.semiChar L t = -1`. Unfold `F.semiChar`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.

Establish `hss : F.semiChar L t * F.semiChar L t = 1`. Apply the tactic sequence `rcases hs with h | h <;> rw [h] <;> norm_num`. Establish `hfun : F.opU L t (F.sgStar L) = fun z => F.semiChar L t * F.sgStar L z`. Use function extensionality and compare the values at `z`. Rewrite using `[← F.sgStarFixed L t z ht, ← mul_assoc, hss, one_mul]`.

Use `⟨ι (F.semiChar L t), ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases hs with h | h <;> rw [h] <;> simp`. Establish `hσ : Rd l ι W (F.sgStar L) (X * B.fExp (-(phW l L ι W)))` using `⟨(F.sgStarBasic L).1.analyticAt 0, inW_sgStar l L ι W⟩`. Establish `h` using `((Rd.const l ι W (F.semiChar L t)).mul hσ).2`. Unfold `gW`.

Rewrite using `[hfun, h]`. Take the linear combination `(C (ι (F.semiChar L t)) * X) * fExp_cancel l L ι W`.
-/
theorem gW_mem (t : ℂ) (ht : t ∈ L.lattice) : ∃ ε : ℂ_[l], ‖ε‖ = 1 ∧ gW l L ι W t = C ε * X := by
  have hs : F.semiChar L t = 1 ∨ F.semiChar L t = -1 := by
    unfold F.semiChar
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hss : F.semiChar L t * F.semiChar L t = 1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  have hfun : F.opU L t (F.sgStar L) = fun z => F.semiChar L t * F.sgStar L z := by
    funext z
    rw [← F.sgStarFixed L t z ht, ← mul_assoc, hss, one_mul]
  refine ⟨ι (F.semiChar L t), ?_, ?_⟩
  · rcases hs with h | h <;> rw [h] <;> simp
  · have hσ : Rd l ι W (F.sgStar L) (X * B.fExp (-(phW l L ι W))) :=
      ⟨(F.sgStarBasic L).1.analyticAt 0, inW_sgStar l L ι W⟩
    have h := ((Rd.const l ι W (F.semiChar L t)).mul hσ).2
    unfold gW
    rw [hfun, h]
    linear_combination (C (ι (F.semiChar L t)) * X) * fExp_cancel l L ι W

abbrev xc (t : ℂ) : ℂ_[l] := ι (L.weierstrassP t) - W.b₂ / 12

abbrev yc (t : ℂ) : ℂ_[l] :=
  (ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2

variable {l L ι W}

/- English proof (translation)
Introduce `hΔ`. Establish `h1` using `hU.1`. Establish `h2` using `hU.2`. Simplify using `only [A.g₂, A.g₃] at h1 h2`. Establish `hc` using `WeierstrassCurve.c_relation W`.

Rewrite `hc` using `[hΔ]`. Apply `F.discNeZero L` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Simplify using `only [map_sub, map_mul, map_pow, map_ofNat, map_zero]`. Rewrite using `[← h1, ← h2]`.

Take the linear combination `(-1 / 1728) * hc`.
-/
theorem disc_ne (hU : Unif l L ι W) : W.Δ ≠ 0 := by
  intro hΔ
  have h1 := hU.1
  have h2 := hU.2
  simp only [A.g₂, A.g₃] at h1 h2
  have hc := WeierstrassCurve.c_relation W
  rw [hΔ] at hc
  apply F.discNeZero L
  apply ι.injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
  rw [← h1, ← h2]
  linear_combination (-1 / 1728) * hc

/- English proof (translation)
Establish `hΔ` using `disc_ne hU`. Establish `h1` using `hU.1`. Establish `h2` using `hU.2`. Simplify using `only [A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h1 h2`. Establish `hn : (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2)` using `by first`.

Consider the case `exact AnaSys.nonsing (l := l) (L := L) (ι := ι) t ht`. Consider the case `exact AddThm.nonsing (l := l) (L := L) (ι := ι) t ht`. Establish `he : (curveL l L ι).toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2)` using `by first`. Consider the case `exact hn.1`. Consider the case `exact hn.left`.

Consider the case `exact (WeierstrassCurve.Affine.nonsingular_iff' _ _).1 hn |>.1`. Rewrite `he` using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [curveL, A.shortW] at he`. Establish `heq : W.toAffine.Equation (xc l L ι W t) (yc l L ι W t)`. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`.

Simplify using `only [xc, yc, WeierstrassCurve.b₂]`. Take the linear combination `he + (ι (L.weierstrassP t) / 4) * h1 + (1 / 4) * h2`. Use `first`. Consider the case `exact WeierstrassCurve.Affine.nonsingular_of_Δ_ne_zero heq hΔ`. Consider the case `(haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩`.

Conclude with `(WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq)`. Consider the case `(haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩`. Conclude with `(WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp heq)`.
-/
theorem nonsing (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    W.toAffine.Nonsingular (xc l L ι W t) (yc l L ι W t) := by
  have hΔ := disc_ne hU
  have h1 := hU.1
  have h2 := hU.2
  simp only [A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h1 h2
  have hn : (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    first
    | exact AnaSys.nonsing (l := l) (L := L) (ι := ι) t ht
    | exact AddThm.nonsing (l := l) (L := L) (ι := ι) t ht
  have he : (curveL l L ι).toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    first
    | exact hn.1
    | exact hn.left
    | exact (WeierstrassCurve.Affine.nonsingular_iff' _ _).1 hn |>.1
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [curveL, A.shortW] at he
  have heq : W.toAffine.Equation (xc l L ι W t) (yc l L ι W t) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [xc, yc, WeierstrassCurve.b₂]
    linear_combination he + (ι (L.weierstrassP t) / 4) * h1 + (1 / 4) * h2
  first
  | exact WeierstrassCurve.Affine.nonsingular_of_Δ_ne_zero heq hΔ
  | (haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
     exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq)
  | (haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
     exact (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp heq)

/- English proof (translation)
Unfold `ptW`. Conclude with `dif_pos ⟨ht, nonsing hU t ht⟩`.
-/
theorem ptW_notMem (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    ptW l L ι W t = .some _ _ (nonsing hU t ht) := by
  unfold ptW
  exact dif_pos ⟨ht, nonsing hU t ht⟩

variable (l L ι W)

/- English proof (translation)
Unfold `ptW`. Conclude with `dif_neg (fun h => h.1 ht)`.
-/
theorem ptW_mem (t : ℂ) (ht : t ∈ L.lattice) : ptW l L ι W t = 0 := by
  unfold ptW
  exact dif_neg (fun h => h.1 ht)

variable {l L ι W}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `ht`. Rewrite `h` using `[ptW_notMem hU t ht]`. Apply the tactic sequence `first | exact WeierstrassCurve.Affine.Point.some_ne_zero _ h | simp at h | cases h | exact nomatch h`.

Introduce `ht`. Conclude with `ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht`.
-/
theorem ptW_zero_iff (hU : Unif l L ι W) (t : ℂ) : ptW l L ι W t = 0 ↔ t ∈ L.lattice := by
  constructor
  · intro h
    by_contra ht
    rw [ptW_notMem hU t ht] at h
    first | exact WeierstrassCurve.Affine.Point.some_ne_zero _ h | simp at h | cases h | exact nomatch h
  · intro ht
    exact ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht

/- English proof (translation)
Rewrite using `[ptW_notMem hU t ht]`. Apply the tactic sequence `first | rfl | simp [px]`.
-/
theorem px_ptW (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    px W (ptW l L ι W t) = xc l L ι W t := by
  rw [ptW_notMem hU t ht]
  first | rfl | simp [px]

/- English proof (translation)
Rewrite using `[ptW_notMem hU t ht]`. Apply the tactic sequence `first | rfl | simp [x2, xT, px, py]`.
-/
theorem scaled_x_model_point (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    x2 W (ptW l L ι W t) = X ^ 2 * xT W (ptW l L ι W t) := by
  rw [ptW_notMem hU t ht]
  first | rfl | simp [x2, xT, px, py]

variable (l L ι W)

/- English proof (translation)
Rewrite using `[ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht]`. Apply the tactic sequence `first | rfl | simp [x2]`.
-/
theorem scaled_x_model_point_lattice (t : ℂ) (ht : t ∈ L.lattice) : x2 W (ptW l L ι W t) = A.xS W := by
  rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht]
  first | rfl | simp [x2]

def W0 : WeierstrassCurve ℂ := W.map (ι.symm : ℂ_[l] →+* ℂ)

/- English proof (translation)
Use `first`. Consider the case `(ext <;> simp [W0])`. Consider the case `(simp only [W0, WeierstrassCurve.map_map]; simp)`.
-/
theorem lattice_model_map : (W0 l ι W).map (ι : ℂ →+* ℂ_[l]) = W := by
  first
  | (ext <;> simp [W0])
  | (simp only [W0, WeierstrassCurve.map_map]; simp)

variable {l L ι W}

/- English proof (translation)
Apply `ι.injective` to reduce the goal to its premises. Establish `h` using `hU.1`. Use `first`. Consider the case `(simp only [A.g₂] at h ⊢; simp only [W0, WeierstrassCurve.map_c₄, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)`. Consider the case `(simp [A.g₂, W0, map_div₀] at h ⊢; exact h)`.
-/
theorem lattice_model_g2 (hU : Unif l L ι W) : A.g₂ (W0 l ι W) = L.g₂ := by
  apply ι.injective
  have h := hU.1
  first
  | (simp only [A.g₂] at h ⊢; simp only [W0, WeierstrassCurve.map_c₄, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)
  | (simp [A.g₂, W0, map_div₀] at h ⊢; exact h)

/- English proof (translation)
Apply `ι.injective` to reduce the goal to its premises. Establish `h` using `hU.2`. Use `first`. Consider the case `(simp only [A.g₃] at h ⊢; simp only [W0, WeierstrassCurve.map_c₆, map_div₀, map_neg, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)`. Consider the case `(simp [A.g₃, W0, map_div₀] at h ⊢; exact h)`.
-/
theorem lattice_model_g3 (hU : Unif l L ι W) : A.g₃ (W0 l ι W) = L.g₃ := by
  apply ι.injective
  have h := hU.2
  first
  | (simp only [A.g₃] at h ⊢; simp only [W0, WeierstrassCurve.map_c₆, map_div₀, map_neg, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)
  | (simp [A.g₃, W0, map_div₀] at h ⊢; exact h)

/- English proof (translation)
Establish `h1` using `F.curve_weierstrass_series_eq (W0 l ι W) L (lattice_model_g2 hU) (lattice_model_g3 hU)`. Establish `h2` using `(A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)).2.2.1`. Rewrite using `[← h1, h2, lattice_model_map]`.
-/
theorem wpBridge (hU : Unif l L ι W) :
    A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curve_weierstrass_series_eq (W0 l ι W) L (lattice_model_g2 hU) (lattice_model_g3 hU)
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)).2.2.1
  rw [← h1, h2, lattice_model_map]

/- English proof (translation)
Establish `h` using `A.wpInU ℂ_[l] W`. Rewrite `h` using `[wpBridge hU]`. Conclude with `h`.
-/
theorem wpInW (hU : Unif l L ι W) :
    X ^ 2 * (1 + A.logSer W ^ 2 * inW l ι W (L.weierstrassPExcept 0)) =
      A.logSer W ^ 2 * (A.xS W + C (W.b₂ / 12) * X ^ 2) := by
  have h := A.wpInU ℂ_[l] W
  rw [wpBridge hU] at h
  exact h

section Trans

open F.TaylorWp

variable (L : PeriodPair) (V : WeierstrassCurve ℂ) (t : ℂ)

def xf : ℂ → ℂ := fun z => L.weierstrassP (z + t) + -(V.b₂ / 12)

def yf : ℂ → ℂ := fun z => (1 / 2) * (L.derivWeierstrassP (z + t) + (-V.a₁ * xf L V t z + -V.a₃))

/- English proof (translation)
Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `h : AnalyticAt ℂ (fun z => L.weierstrassP (z + t)) 0` using `by first`. Consider the case `exact (AnaSys.T_wp ht).1`. Consider the case `exact (AnaSys.T_wp (L := L) (t := t) ht).1`. Consider the case `exact (AnaSys.T_wp L t ht).1`.

Conclude with `h.add analyticAt_const`.
-/
theorem T_xf (ht : t ∉ L.lattice) : T (xf L V t) (F.taylor0 (xf L V t)) := by
  refine ⟨?_, rfl⟩
  have h : AnalyticAt ℂ (fun z => L.weierstrassP (z + t)) 0 := by
    first
    | exact (AnaSys.T_wp ht).1
    | exact (AnaSys.T_wp (L := L) (t := t) ht).1
    | exact (AnaSys.T_wp L t ht).1
  exact h.add analyticAt_const

/- English proof (translation)
Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `h : AnalyticAt ℂ (fun z => L.derivWeierstrassP (z + t)) 0` using `by first`. Consider the case `exact (AnaSys.T_dwp ht).1`. Consider the case `exact (AnaSys.T_dwp (L := L) (t := t) ht).1`. Consider the case `exact (AnaSys.T_dwp L t ht).1`.

Establish `hx` using `(T_xf L V t ht).1`. Conclude with `analyticAt_const.mul (h.add ((analyticAt_const.mul hx).add analyticAt_const))`.
-/
theorem T_yf (ht : t ∉ L.lattice) : T (yf L V t) (F.taylor0 (yf L V t)) := by
  refine ⟨?_, rfl⟩
  have h : AnalyticAt ℂ (fun z => L.derivWeierstrassP (z + t)) 0 := by
    first
    | exact (AnaSys.T_dwp ht).1
    | exact (AnaSys.T_dwp (L := L) (t := t) ht).1
    | exact (AnaSys.T_dwp L t ht).1
  have hx := (T_xf L V t ht).1
  exact analyticAt_const.mul (h.add ((analyticAt_const.mul hx).add analyticAt_const))

/- English proof (translation)
Establish `h` using `F.PDeriv.hasDerivAt_P L hz`. Use `first`. Consider the case `exact (h.comp_add_const z t).add_const _`. Consider the case `exact (HasDerivAt.comp_add_const z t h).add_const _`.
-/
theorem hasDeriv_xf (z : ℂ) (hz : z + t ∉ L.lattice) :
    HasDerivAt (xf L V t) (L.derivWeierstrassP (z + t)) z := by
  have h := F.PDeriv.hasDerivAt_P L hz
  first
  | exact (h.comp_add_const z t).add_const _
  | exact (HasDerivAt.comp_add_const z t h).add_const _

/- English proof (translation)
Establish `h2 : HasDerivAt (fun w => L.derivWeierstrassP (w + t)) (6 * L.weierstrassP (z + t) ^ 2 - L.g₂ / 2) z` using `by first`. Consider the case `exact (F.pSecond L (z + t) hz).comp_add_const z t`. Consider the case `exact HasDerivAt.comp_add_const z t (F.pSecond L (z + t) hz)`. Establish `hx` using `hasDeriv_xf L V t z hz`. Conclude with `(h2.add ((hx.const_mul (-V.a₁)).add_const (-V.a₃))).const_mul (1 / 2)`.
-/
theorem hasDeriv_yf (z : ℂ) (hz : z + t ∉ L.lattice) :
    HasDerivAt (yf L V t) ((1 / 2) * ((6 * L.weierstrassP (z + t) ^ 2 - L.g₂ / 2) +
      -V.a₁ * L.derivWeierstrassP (z + t))) z := by
  have h2 : HasDerivAt (fun w => L.derivWeierstrassP (w + t)) (6 * L.weierstrassP (z + t) ^ 2 - L.g₂ / 2) z := by
    first
    | exact (F.pSecond L (z + t) hz).comp_add_const z t
    | exact HasDerivAt.comp_add_const z t (F.pSecond L (z + t) hz)
  have hx := hasDeriv_xf L V t z hz
  exact (h2.add ((hx.const_mul (-V.a₁)).add_const (-V.a₃))).const_mul (1 / 2)

variable {L V}

/- English proof (translation)
Establish `hr` using `F.taylorRing`. Establish `hx` using `T_xf L V t ht`. Establish `hy` using `T_yf L V t ht`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`.

Establish `hl` using `(T.add hr (T.add hr (T.pow hr hy 2) (T.mul hr (T.mul hr (T.const hr V.a₁) hx) hy)) (T.mul hr (T.const hr V.a₃) hy)).2`. Establish `hq` using `(T.add hr (T.add hr (T.add hr (T.pow hr hx 3) (T.mul hr (T.const hr V.a₂) (T.pow hr hx 2))) (T.mul hr (T.const hr V.a₄) hx)) (T.const hr V.a₆)).2`. Use `hl.symm.trans (Eq.trans ?_ hq)` and prove the remaining obligations. Apply `F.Taylor.taylor0_congr` to reduce the goal to its premises. Use `filter_upwards [AnaSys.ev_notMem L t ht] with z hz`.

Establish `h` using `L.derivWeierstrassP_sq (z + t) hz`. Rewrite `h` using `[← h2, ← h3]`. Simplify using `only [xf, yf, A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢`. Take the linear combination `h / 4`. Establish `hq` using `(T.add hr (T.add hr (T.mul hr (T.const hr 2) hy) (T.mul hr (T.const hr V.a₁) hx)) (T.const hr V.a₃)).2`.

Establish `c2 : (C (2 : ℂ) : PowerSeries ℂ) = 2` using `map_ofNat C 2`. Rewrite `hq` using `[c2]`. Rewrite using `[← F.Taylor.taylor0_deriv]`. Use `Eq.trans ?_ hq` and prove the remaining obligations. Apply `F.Taylor.taylor0_congr` to reduce the goal to its premises.

Use `filter_upwards [AnaSys.ev_notMem L t ht] with z hz`. Rewrite using `[(hasDeriv_xf L V t z hz).deriv]`. Simplify using `only [yf]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq` using `(T.add hr (T.add hr (T.add hr (T.mul hr (T.const hr 3) (T.pow hr hx 2)) (T.mul hr (T.mul hr (T.const hr 2) (T.const hr V.a₂)) hx)) (T.const hr V.a₄)) (T.mul hr (T.const hr (-V.a₁)) hy)).2`.

Establish `c2 : (C (2 : ℂ) : PowerSeries ℂ) = 2` using `map_ofNat C 2`. Establish `c3 : (C (3 : ℂ) : PowerSeries ℂ) = 3` using `map_ofNat C 3`. Rewrite `hq` using `[c2, c3, map_neg, neg_mul, ← sub_eq_add_neg]`. Rewrite using `[← F.Taylor.taylor0_deriv]`. Use `Eq.trans ?_ hq` and prove the remaining obligations.

Apply `F.Taylor.taylor0_congr` to reduce the goal to its premises. Use `filter_upwards [AnaSys.ev_notMem L t ht] with z hz`. Rewrite using `[(hasDeriv_yf L V t z hz).deriv, ← h2]`. Simplify using `only [xf, yf, A.g₂, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flowC (h2 : A.g₂ V = L.g₂) (h3 : A.g₃ V = L.g₃) (ht : t ∉ L.lattice) :
    A.IsFlow (A.curveS V) (derivative ℂ) (F.taylor0 (xf L V t)) (F.taylor0 (yf L V t)) := by
  have hr := F.taylorRing
  have hx := T_xf L V t ht
  have hy := T_yf L V t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    have hl := (T.add hr (T.add hr (T.pow hr hy 2) (T.mul hr (T.mul hr (T.const hr V.a₁) hx) hy))
      (T.mul hr (T.const hr V.a₃) hy)).2
    have hq := (T.add hr (T.add hr (T.add hr (T.pow hr hx 3) (T.mul hr (T.const hr V.a₂) (T.pow hr hx 2)))
      (T.mul hr (T.const hr V.a₄) hx)) (T.const hr V.a₆)).2
    refine hl.symm.trans (Eq.trans ?_ hq)
    apply F.Taylor.taylor0_congr
    filter_upwards [AnaSys.ev_notMem L t ht] with z hz
    have h := L.derivWeierstrassP_sq (z + t) hz
    rw [← h2, ← h3] at h
    simp only [xf, yf, A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢
    linear_combination h / 4
  · have hq := (T.add hr (T.add hr (T.mul hr (T.const hr 2) hy) (T.mul hr (T.const hr V.a₁) hx))
      (T.const hr V.a₃)).2
    have c2 : (C (2 : ℂ) : PowerSeries ℂ) = 2 := map_ofNat C 2
    rw [c2] at hq
    rw [← F.Taylor.taylor0_deriv]
    refine Eq.trans ?_ hq
    apply F.Taylor.taylor0_congr
    filter_upwards [AnaSys.ev_notMem L t ht] with z hz
    rw [(hasDeriv_xf L V t z hz).deriv]
    simp only [yf]
    ring
  · have hq := (T.add hr (T.add hr (T.add hr (T.mul hr (T.const hr 3) (T.pow hr hx 2))
      (T.mul hr (T.mul hr (T.const hr 2) (T.const hr V.a₂)) hx)) (T.const hr V.a₄))
      (T.mul hr (T.const hr (-V.a₁)) hy)).2
    have c2 : (C (2 : ℂ) : PowerSeries ℂ) = 2 := map_ofNat C 2
    have c3 : (C (3 : ℂ) : PowerSeries ℂ) = 3 := map_ofNat C 3
    rw [c2, c3, map_neg, neg_mul, ← sub_eq_add_neg] at hq
    rw [← F.Taylor.taylor0_deriv]
    refine Eq.trans ?_ hq
    apply F.Taylor.taylor0_congr
    filter_upwards [AnaSys.ev_notMem L t ht] with z hz
    rw [(hasDeriv_yf L V t z hz).deriv, ← h2]
    simp only [xf, yf, A.g₂, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring

/- English proof (translation)
Establish `hfl` using `flowC t h2 h3 ht`. Establish `heq : V.toAffine.Equation (xf L V t 0) (yf L V t 0)`. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Establish `h` using `L.derivWeierstrassP_sq (0 + t) (by simpa using ht)`. Rewrite `h` using `[← h2, ← h3]`.

Simplify using `only [xf, yf, A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢`. Take the linear combination `h / 4`. Establish `he0 : constantCoeff (A.expSer V) = 0` using `(A.expSpec ℂ _).1`. Establish `hf` using `(A.plusFlow ℂ V _ _ heq)`. Use `(A.flowUniqueZ ℂ V _ _ _ _ (A.plusZ ℂ _ _ _ heq).1 hfl ?_ ?_).1` and prove the remaining obligations.

Rewrite using `[B.Ph.constantCoeff_psubst he0, hf.2.1, F.TaylorSigmaUniqueness.constantCoeff_taylor0]`. Rewrite using `[B.Ph.constantCoeff_psubst he0, hf.2.2, F.TaylorSigmaUniqueness.constantCoeff_taylor0]`.
-/
theorem transC (h2 : A.g₂ V = L.g₂) (h3 : A.g₃ V = L.g₃) (ht : t ∉ L.lattice) :
    (A.xPlus V (xf L V t 0) (yf L V t 0)).subst (A.expSer V) = F.taylor0 (xf L V t) := by
  have hfl := flowC t h2 h3 ht
  have heq : V.toAffine.Equation (xf L V t 0) (yf L V t 0) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have h := L.derivWeierstrassP_sq (0 + t) (by simpa using ht)
    rw [← h2, ← h3] at h
    simp only [xf, yf, A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢
    linear_combination h / 4
  have he0 : constantCoeff (A.expSer V) = 0 := (A.expSpec ℂ _).1
  have hf := (A.plusFlow ℂ V _ _ heq)
  refine (A.flowUniqueZ ℂ V _ _ _ _ (A.plusZ ℂ _ _ _ heq).1 hfl ?_ ?_).1
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.1, F.TaylorSigmaUniqueness.constantCoeff_taylor0]
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.2, F.TaylorSigmaUniqueness.constantCoeff_taylor0]

end Trans

/- English proof (translation)
Use `first`. Consider the case `(simp only [xf, xc, W0, WeierstrassCurve.map_b₂, zero_add, map_add, map_neg, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; ring)`. Consider the case `(simp [xf, xc, W0, map_div₀, sub_eq_add_neg])`.
-/
theorem map_analytic_x_at_zero (t : ℂ) : ι (xf L (W0 l ι W) t 0) = xc l L ι W t := by
  first
  | (simp only [xf, xc, W0, WeierstrassCurve.map_b₂, zero_add, map_add, map_neg, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; ring)
  | (simp [xf, xc, W0, map_div₀, sub_eq_add_neg])

/- English proof (translation)
Use `first`. Consider the case `(simp only [yf, yc, xf, W0, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, WeierstrassCurve.map_b₂, zero_add, map_add, map_neg, map_mul, map_div₀, map_one, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; ring)`. Consider the case `(simp [yf, yc, xf, W0, map_div₀]; ring)`.
-/
theorem map_analytic_y_at_zero (t : ℂ) : ι (yf L (W0 l ι W) t 0) = yc l L ι W t := by
  first
  | (simp only [yf, yc, xf, W0, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, WeierstrassCurve.map_b₂, zero_add, map_add, map_neg, map_mul, map_div₀, map_one, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; ring)
  | (simp [yf, yc, xf, W0, map_div₀]; ring)

/- English proof (translation)
Establish `hz` using `A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)`. Establish `hp` using `(A.plusMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W) (xf L (W0 l ι W) t 0) (yf L (W0 l ι W) t 0)).2.1`. Establish `he` using `A.expSpec ℂ_[l] W`. Unfold `inW`. Rewrite using `[← transC t (lattice_model_g2 hU) (lattice_model_g3 hU) ht, B.Map.map_psubst' _ (A.expSpec ℂ _).1, hz.2.1, hp, lattice_model_map, subst_comp_subst_apply (B.Ph.hs he.1) (lgS l W), he.2.2.2.1, X_subst, ptW_notMem hU t ht]`.

Simplify using `only [xT, px, py, RingEquiv.coe_toRingHom, map_analytic_x_at_zero, map_analytic_y_at_zero]`.
-/
theorem transW (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    inW l ι W (xf L (W0 l ι W) t) = xT W (ptW l L ι W t) := by
  have hz := A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)
  have hp := (A.plusMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W) (xf L (W0 l ι W) t 0)
    (yf L (W0 l ι W) t 0)).2.1
  have he := A.expSpec ℂ_[l] W
  unfold inW
  rw [← transC t (lattice_model_g2 hU) (lattice_model_g3 hU) ht, B.Map.map_psubst' _ (A.expSpec ℂ _).1, hz.2.1, hp, lattice_model_map,
    subst_comp_subst_apply (B.Ph.hs he.1) (lgS l W), he.2.2.2.1, X_subst, ptW_notMem hU t ht]
  simp only [xT, px, py, RingEquiv.coe_toRingHom, map_analytic_x_at_zero, map_analytic_y_at_zero]

/- English proof (translation)
Establish `hev : (fun z => F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z) =ᶠ[nhds 0] fun z => F.opU L Q (F.sgStar L) 0 ^ 2 * (xf L (W0 l ι W) Q 0 + (-1) * xf L (W0 l ι W) P z) * (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z)` using `by filter_upwards [AnaSys.ev_notMem L P hP] with z hz`. Rewrite using `[F.translateProduct L P Q z hQ hz]`. Simplify using `only [xf, zero_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwp : Rd l ι W (xf L (W0 l ι W) P) (xT W (ptW l L ι W P))` using `⟨(T_xf L (W0 l ι W) P hP).1, transW hU P hP⟩`.

Establish `hl` using `((Rd.opU l L ι W (P + Q)).mul (Rd.opU l L ι W (P - Q))).2`. Establish `hr` using `(((Rd.const l ι W (F.opU L Q (F.sgStar L) 0 ^ 2)).mul ((Rd.const l ι W (xf L (W0 l ι W) Q 0)).add ((Rd.const l ι W (-1)).mul hwp))).mul ((Rd.opU l L ι W P).mul (Rd.opU l L ι W P))).2`. Establish `key` using `hl.symm.trans ((inW_congr l ι W hev).trans hr)`. Simplify using `only [map_pow, map_neg, map_one, map_analytic_x_at_zero] at key`. Rewrite using `[cc_gW, px_ptW hU Q hQ, scaled_x_model_point hU P hP]`.

Unfold `gW`. Simplify using `only [map_pow]`. Take the linear combination `(X ^ 2 * B.fExp (phW l L ι W) ^ 2) * key`.
-/
theorem prod_notMem (hU : Unif l L ι W) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    X ^ 2 * (gW l L ι W (P + Q) * gW l L ι W (P - Q)) =
      C (constantCoeff (gW l L ι W Q) ^ 2) *
        (C (px W (ptW l L ι W Q)) * X ^ 2 - x2 W (ptW l L ι W P)) * gW l L ι W P ^ 2 := by
  have hev : (fun z => F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 * (xf L (W0 l ι W) Q 0 + (-1) * xf L (W0 l ι W) P z) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [AnaSys.ev_notMem L P hP] with z hz
    rw [F.translateProduct L P Q z hQ hz]
    simp only [xf, zero_add]
    ring
  have hwp : Rd l ι W (xf L (W0 l ι W) P) (xT W (ptW l L ι W P)) :=
    ⟨(T_xf L (W0 l ι W) P hP).1, transW hU P hP⟩
  have hl := ((Rd.opU l L ι W (P + Q)).mul (Rd.opU l L ι W (P - Q))).2
  have hr := (((Rd.const l ι W (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    ((Rd.const l ι W (xf L (W0 l ι W) Q 0)).add ((Rd.const l ι W (-1)).mul hwp))).mul
    ((Rd.opU l L ι W P).mul (Rd.opU l L ι W P))).2
  have key := hl.symm.trans ((inW_congr l ι W hev).trans hr)
  simp only [map_pow, map_neg, map_one, map_analytic_x_at_zero] at key
  rw [cc_gW, px_ptW hU Q hQ, scaled_x_model_point hU P hP]
  unfold gW
  simp only [map_pow]
  linear_combination (X ^ 2 * B.fExp (phW l L ι W) ^ 2) * key

/- English proof (translation)
Establish `hev : (fun z => (z * z) * (F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z)) =ᶠ[nhds 0] fun z => F.opU L Q (F.sgStar L) 0 ^ 2 * (L.weierstrassP Q * (z * z) + (-1) * (1 + (z * z) * L.weierstrassPExcept 0 z)) * (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z)` using `by filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz`. Distinguish the cases in `h0 : z = 0`. Substitute `h0` using the available equality. Rewrite using `[AnaSys.opU_zero_eq L P hP]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hzL : z ∉ L.lattice` using `fun h => hz ⟨h, h0⟩`. Establish `hzP : z + P ∉ L.lattice` using `fun h => hzL (by simpa using L.lattice.sub_mem h hP)`. Rewrite using `[F.translateProduct L P Q z hQ hzP, L.weierstrassP_add_coe z ⟨P, hP⟩, ← L.weierstrassPExcept_add (0 : L.lattice) z]`. Simplify using `only [ZeroMemClass.coe_zero, sub_zero]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hz2 : Rd l ι W (fun z => z * z) _` using `(Rd.id l ι W).mul (Rd.id l ι W)`. Establish `hex : Rd l ι W (L.weierstrassPExcept 0) (inW l ι W (L.weierstrassPExcept 0))` using `⟨L.analyticAt_weierstrassPExcept 0, rfl⟩`. Establish `hl` using `(hz2.mul ((Rd.opU l L ι W (P + Q)).mul (Rd.opU l L ι W (P - Q)))).2`. Establish `hr` using `(((Rd.const l ι W (F.opU L Q (F.sgStar L) 0 ^ 2)).mul (((Rd.const l ι W (L.weierstrassP Q)).mul hz2).add ((Rd.const l ι W (-1)).mul ((Rd.const l ι W 1).add (hz2.mul hex))))).mul ((Rd.opU l L ι W P).mul (Rd.opU l L ι W P))).2`.

Establish `key` using `hl.symm.trans ((inW_congr l ι W hev).trans hr)`. Simplify using `only [map_pow, map_neg, map_one] at key`. Establish `hw` using `wpInW hU`. Rewrite using `[cc_gW, px_ptW hU Q hQ, scaled_x_model_point_lattice l L ι W P hP]`. Unfold `gW`.

Simplify using `only [map_pow, xc, map_sub]`. Apply `mul_left_cancel₀ (pow_ne_zero 2 (lg_ne l W))` to reduce the goal to its premises. Take the linear combination `(X ^ 2 * B.fExp (phW l L ι W) ^ 2) * key - (C (ι (F.opU L Q (F.sgStar L) 0)) ^ 2 * B.fExp (phW l L ι W) ^ 2 * inW l ι W (F.opU L P (F.sgStar L)) ^ 2) * hw`.
-/
theorem prod_mem (hU : Unif l L ι W) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∈ L.lattice) :
    X ^ 2 * (gW l L ι W (P + Q) * gW l L ι W (P - Q)) =
      C (constantCoeff (gW l L ι W Q) ^ 2) *
        (C (px W (ptW l L ι W Q)) * X ^ 2 - x2 W (ptW l L ι W P)) * gW l L ι W P ^ 2 := by
  have hev : (fun z => (z * z) *
        (F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z)) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 *
          (L.weierstrassP Q * (z * z) + (-1) * (1 + (z * z) * L.weierstrassPExcept 0 z)) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
    by_cases h0 : z = 0
    · subst h0
      rw [AnaSys.opU_zero_eq L P hP]
      ring
    · have hzL : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
      have hzP : z + P ∉ L.lattice := fun h => hzL (by simpa using L.lattice.sub_mem h hP)
      rw [F.translateProduct L P Q z hQ hzP, L.weierstrassP_add_coe z ⟨P, hP⟩,
        ← L.weierstrassPExcept_add (0 : L.lattice) z]
      simp only [ZeroMemClass.coe_zero, sub_zero]
      field_simp
      ring
  have hz2 : Rd l ι W (fun z => z * z) _ := (Rd.id l ι W).mul (Rd.id l ι W)
  have hex : Rd l ι W (L.weierstrassPExcept 0) (inW l ι W (L.weierstrassPExcept 0)) :=
    ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
  have hl := (hz2.mul ((Rd.opU l L ι W (P + Q)).mul (Rd.opU l L ι W (P - Q)))).2
  have hr := (((Rd.const l ι W (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    (((Rd.const l ι W (L.weierstrassP Q)).mul hz2).add
      ((Rd.const l ι W (-1)).mul ((Rd.const l ι W 1).add (hz2.mul hex))))).mul
    ((Rd.opU l L ι W P).mul (Rd.opU l L ι W P))).2
  have key := hl.symm.trans ((inW_congr l ι W hev).trans hr)
  simp only [map_pow, map_neg, map_one] at key
  have hw := wpInW hU
  rw [cc_gW, px_ptW hU Q hQ, scaled_x_model_point_lattice l L ι W P hP]
  unfold gW
  simp only [map_pow, xc, map_sub]
  apply mul_left_cancel₀ (pow_ne_zero 2 (lg_ne l W))
  linear_combination (X ^ 2 * B.fExp (phW l L ι W) ^ 2) * key -
    (C (ι (F.opU L Q (F.sgStar L) 0)) ^ 2 * B.fExp (phW l L ι W) ^ 2 *
      inW l ι W (F.opU L P (F.sgStar L)) ^ 2) * hw

/- English proof (translation)
Distinguish the cases in `ht : t ∈ L.lattice`. Establish `h' : t + ω ∈ L.lattice` using `add_mem ht hω`. Rewrite using `[ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ h', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]`. Establish `h' : t + ω ∉ L.lattice` using `fun h => ht (by simpa using sub_mem h hω)`. Establish `e1 : L.weierstrassP (t + ω) = L.weierstrassP t` using `by first`.

Consider the case `exact L.weierstrassP_add_coe t ⟨ω, hω⟩`. Consider the case `exact L.weierstrassP_add_coe ⟨ω, hω⟩ t`. Consider the case `simpa using L.weierstrassP_add_coe t ⟨ω, hω⟩`. Establish `e2 : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t` using `by first`. Consider the case `exact L.derivWeierstrassP_add_coe t ⟨ω, hω⟩`.

Consider the case `exact L.derivWeierstrassP_add_coe ⟨ω, hω⟩ t`. Consider the case `simpa using L.derivWeierstrassP_add_coe t ⟨ω, hω⟩`. Rewrite using `[ptW_notMem hU _ h', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.some.injEq]`. Conclude with `⟨by simp only [xc, e1], by simp only [yc, e1, e2]⟩`.
-/
theorem ptW_add_lattice (hU : Unif l L ι W) (t ω : ℂ) (hω : ω ∈ L.lattice) :
    ptW l L ι W (t + ω) = ptW l L ι W t := by
  by_cases ht : t ∈ L.lattice
  · have h' : t + ω ∈ L.lattice := add_mem ht hω
    rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ h', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]
  · have h' : t + ω ∉ L.lattice := fun h => ht (by simpa using sub_mem h hω)
    have e1 : L.weierstrassP (t + ω) = L.weierstrassP t := by
      first
      | exact L.weierstrassP_add_coe t ⟨ω, hω⟩
      | exact L.weierstrassP_add_coe ⟨ω, hω⟩ t
      | simpa using L.weierstrassP_add_coe t ⟨ω, hω⟩
    have e2 : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := by
      first
      | exact L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
      | exact L.derivWeierstrassP_add_coe ⟨ω, hω⟩ t
      | simpa using L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
    rw [ptW_notMem hU _ h', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨by simp only [xc, e1], by simp only [yc, e1, e2]⟩

/- English proof (translation)
Distinguish the cases in `ht : t ∈ L.lattice`. Establish `ht' : -t ∈ L.lattice` using `neg_mem ht`. Rewrite using `[ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]`. Apply the tactic sequence `first | simp | rfl | exact neg_zero.symm`. Establish `ht' : -t ∉ L.lattice` using `fun h => ht (by simpa using neg_mem h)`.

Rewrite using `[ptW_notMem hU _ ht', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]`. Use `first`. Consider the case `(refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg] <;> ring)`. Consider the case `(refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, L.weierstrassP_neg, L.derivWeierstrassP_neg] <;> ring)`.
-/
theorem ptW_neg (hU : Unif l L ι W) (t : ℂ) : ptW l L ι W (-t) = -ptW l L ι W t := by
  by_cases ht : t ∈ L.lattice
  · have ht' : -t ∈ L.lattice := neg_mem ht
    rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]
    first | simp | rfl | exact neg_zero.symm
  · have ht' : -t ∉ L.lattice := fun h => ht (by simpa using neg_mem h)
    rw [ptW_notMem hU _ ht', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    first
    | (refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg] <;> ring)
    | (refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, L.weierstrassP_neg, L.derivWeierstrassP_neg] <;> ring)

section Law

variable [DecidableEq ℂ_[l]]

/- English proof (translation)
Establish `hne` using `AddThm.P_sub_ne L s t hs ht hp hm`. Establish `hne' : ι (L.weierstrassP s) - ι (L.weierstrassP t) ≠ 0`. Rewrite using `[← map_sub]`. Conclude with `fun h => hne (ι.injective (h.trans (map_zero ι).symm))`. Establish `hd : xc l L ι W s - xc l L ι W t = ι (L.weierstrassP s) - ι (L.weierstrassP t)`.

Simplify using `only [xc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx : xc l L ι W s ≠ xc l L ι W t` using `sub_ne_zero.1 (by rw [hd]; exact hne')`. Establish `hX` using `congrArg ι (AddThm.P_add L s t hs ht hp hm)`. Establish `hY` using `congrArg ι (AddThm.collinear L s t hs ht hp)`.

Simplify using `only [map_pow, map_sub, map_mul, map_add, map_neg, map_div₀, map_ofNat] at hX hY`. Rewrite using `[ptW_notMem hU s hs, ptW_notMem hU t ht, ptW_notMem hU _ hp, WeierstrassCurve.Affine.Point.add_of_X_ne hx]`. Establish `e1 : xc l L ι W (s + t) = W.toAffine.addX (xc l L ι W s) (xc l L ι W t) (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t))`. Rewrite using `[WeierstrassCurve.Affine.slope_of_X_ne hx, hd]`. Simplify using `only [WeierstrassCurve.Affine.addX, xc, yc, WeierstrassCurve.b₂]`.

Rewrite using `[hX]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : yc l L ι W (s + t) = W.toAffine.addY (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t))`. Rewrite using `[WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← e1, WeierstrassCurve.Affine.slope_of_X_ne hx, hd]`.

Simplify using `only [WeierstrassCurve.Affine.negY, xc, yc]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `144 * hY`. Simplify using `only [WeierstrassCurve.Affine.Point.some.injEq]`. Conclude with `⟨e1, e2⟩`.
-/
theorem ptW_add_generic (hU : Unif l L ι W) (s t : ℂ) (hs : s ∉ L.lattice) (ht : t ∉ L.lattice)
    (hp : s + t ∉ L.lattice) (hm : s - t ∉ L.lattice) :
    ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t := by
  have hne := AddThm.P_sub_ne L s t hs ht hp hm
  have hne' : ι (L.weierstrassP s) - ι (L.weierstrassP t) ≠ 0 := by
    rw [← map_sub]
    exact fun h => hne (ι.injective (h.trans (map_zero ι).symm))
  have hd : xc l L ι W s - xc l L ι W t = ι (L.weierstrassP s) - ι (L.weierstrassP t) := by
    simp only [xc]
    ring
  have hx : xc l L ι W s ≠ xc l L ι W t := sub_ne_zero.1 (by rw [hd]; exact hne')
  have hX := congrArg ι (AddThm.P_add L s t hs ht hp hm)
  have hY := congrArg ι (AddThm.collinear L s t hs ht hp)
  simp only [map_pow, map_sub, map_mul, map_add, map_neg, map_div₀, map_ofNat] at hX hY
  rw [ptW_notMem hU s hs, ptW_notMem hU t ht, ptW_notMem hU _ hp,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have e1 : xc l L ι W (s + t) =
      W.toAffine.addX (xc l L ι W s) (xc l L ι W t)
        (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t)) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hd]
    simp only [WeierstrassCurve.Affine.addX, xc, yc, WeierstrassCurve.b₂]
    rw [hX]
    field_simp
    ring
  have e2 : yc l L ι W (s + t) =
      W.toAffine.addY (xc l L ι W s) (xc l L ι W t) (yc l L ι W s)
        (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t)) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← e1,
      WeierstrassCurve.Affine.slope_of_X_ne hx, hd]
    simp only [WeierstrassCurve.Affine.negY, xc, yc]
    field_simp
    linear_combination 144 * hY
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨e1, e2⟩

/- English proof (translation)
Distinguish the cases in `hs : s ∈ L.lattice`. Rewrite using `[add_comm s t, ptW_add_lattice hU t s hs, ptW_mem l L ι W s hs, zero_add]`. Distinguish the cases in `ht : t ∈ L.lattice`. Rewrite using `[ptW_add_lattice hU s t ht, ptW_mem l L ι W t ht, add_zero]`. Distinguish the cases in `hp : s + t ∈ L.lattice`.

Establish `h : ptW l L ι W t = -ptW l L ι W s`. Rewrite using `[← ptW_neg hU, ← ptW_add_lattice hU (-s) (s + t) hp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ptW_mem l L ι W _ hp, h, add_neg_cancel]`.

Distinguish the cases in `hm : s - t ∈ L.lattice`. Establish `h1 : ptW l L ι W s = ptW l L ι W t`. Rewrite using `[← ptW_add_lattice hU t (s - t) hm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ptW l L ι W (s + t) = ptW l L ι W (t + t)`. Rewrite using `[← ptW_add_lattice hU (t + t) (s - t) hm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `htt : t + t ∉ L.lattice` using `fun h => hp (by`.

Use `L.lattice.add_mem h hm` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Take `⟨u, hu2, hup, hum⟩` from `AddThm.exists_finite_part_one_idele_split_congruence_quotient L t`. Establish `hu : u ∉ L.lattice` using `fun h => hu2 (by`.

Rewrite using `[two_mul]`. Conclude with `L.lattice.add_mem h h)`. Establish `hu' : -u ∉ L.lattice` using `fun h => hu (by simpa using L.lattice.neg_mem h)`. Establish `a1 : ptW l L ι W ((t + u) + (t - u)) = ptW l L ι W (t + u) + ptW l L ι W (t - u)` using `ptW_add_generic hU _ _ hup hum (by convert htt using 2; ring) (by convert hu2 using 2; ring)`. Establish `a2 : ptW l L ι W (t + u) = ptW l L ι W t + ptW l L ι W u` using `ptW_add_generic hU _ _ ht hu hup hum`.

Establish `a3 : ptW l L ι W (t + -u) = ptW l L ι W t + ptW l L ι W (-u)` using `ptW_add_generic hU _ _ ht hu' (by rwa [← sub_eq_add_neg]) (by rwa [sub_neg_eq_add])`. Rewrite using `[h2, h1]`. Establish `e : t + t = (t + u) + (t - u)` using `by ring`. Rewrite using `[e, a1, a2, sub_eq_add_neg, a3, ptW_neg hU]`. Normalize the expressions using the abelian group laws.

Conclude with `ptW_add_generic hU s t hs ht hp hm`.
-/
theorem ptW_add (hU : Unif l L ι W) (s t : ℂ) :
    ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t := by
  by_cases hs : s ∈ L.lattice
  · rw [add_comm s t, ptW_add_lattice hU t s hs, ptW_mem l L ι W s hs, zero_add]
  by_cases ht : t ∈ L.lattice
  · rw [ptW_add_lattice hU s t ht, ptW_mem l L ι W t ht, add_zero]
  by_cases hp : s + t ∈ L.lattice
  · have h : ptW l L ι W t = -ptW l L ι W s := by
      rw [← ptW_neg hU, ← ptW_add_lattice hU (-s) (s + t) hp]
      congr 1
      ring
    rw [ptW_mem l L ι W _ hp, h, add_neg_cancel]
  by_cases hm : s - t ∈ L.lattice
  · have h1 : ptW l L ι W s = ptW l L ι W t := by
      rw [← ptW_add_lattice hU t (s - t) hm]
      congr 1
      ring
    have h2 : ptW l L ι W (s + t) = ptW l L ι W (t + t) := by
      rw [← ptW_add_lattice hU (t + t) (s - t) hm]
      congr 1
      ring
    have htt : t + t ∉ L.lattice := fun h => hp (by
      have := L.lattice.add_mem h hm
      convert this using 1
      ring)
    obtain ⟨u, hu2, hup, hum⟩ := AddThm.exists_finite_part_one_idele_split_congruence_quotient L t
    have hu : u ∉ L.lattice := fun h => hu2 (by
      rw [two_mul]
      exact L.lattice.add_mem h h)
    have hu' : -u ∉ L.lattice := fun h => hu (by simpa using L.lattice.neg_mem h)
    have a1 : ptW l L ι W ((t + u) + (t - u)) = ptW l L ι W (t + u) + ptW l L ι W (t - u) :=
      ptW_add_generic hU _ _ hup hum (by convert htt using 2; ring) (by convert hu2 using 2; ring)
    have a2 : ptW l L ι W (t + u) = ptW l L ι W t + ptW l L ι W u :=
      ptW_add_generic hU _ _ ht hu hup hum
    have a3 : ptW l L ι W (t + -u) = ptW l L ι W t + ptW l L ι W (-u) :=
      ptW_add_generic hU _ _ ht hu' (by rwa [← sub_eq_add_neg]) (by rwa [sub_neg_eq_add])
    rw [h2, h1]
    have e : t + t = (t + u) + (t - u) := by ring
    rw [e, a1, a2, sub_eq_add_neg, a3, ptW_neg hU]
    abel
  exact ptW_add_generic hU s t hs ht hp hm

end Law

end AnaSysW

/- English proof (translation)
Introduce `l _ L ι W hU t`. Conclude with `AnaSysW.ptW_zero_iff hU t`.
-/
theorem analytic_point_eq_zero_iff : PtWZero := by
  intro l _ L ι W hU t
  exact AnaSysW.ptW_zero_iff hU t

open Classical in

/- English proof (translation)
Introduce `l _ L ι W hU s t`. Conclude with `AnaSysW.ptW_add hU s t`.
-/
theorem analytic_point_map_add : PtWAdd := by
  intro l _ L ι W hU s t
  exact AnaSysW.ptW_add hU s t

/- English proof (translation)
Conclude with `AnaSysW.wpBridge hU`.
-/
theorem weierstrass_series_eq_transported (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (W : WeierstrassCurve ℂ_[l]) (hU : Unif l L ι W) :
    Formalism.L2.Th1.A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L) := by
  exact AnaSysW.wpBridge hU

open Classical in

/- English proof (translation)
Unfold `AnalyticSysW`. Introduce `l _ L ι W hU π hπ`. Unfold `IsTransSys`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Simplify using `only [hπ] at ht`. Conclude with `AnaSysW.gW_mem (l := l) (L := L) (ι := ι) (W := W) t ((AnaSysW.ptW_zero_iff hU t).1 ht)`. Introduce `t ht`. Simplify using `only [hπ] at ht`. Establish `htl : t ∉ L.lattice` using `fun h => ht ((AnaSysW.ptW_zero_iff hU t).2 h)`.

Rewrite using `[AnaSysW.cc_gW (l := l) (L := L) (ι := ι) (W := W) t]`. Use `(map_ne_zero ι).mpr ?_` and prove the remaining obligations. Simplify using `only [F.opU, F.sgStar, zero_add]`. Use `mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)` and prove the remaining obligations. Conclude with `fun h => htl ((F.sigmaZero L t).1 h)`.

Introduce `P Q hQ`. Simplify using `only [hπ] at hQ ⊢`. Establish `hQl : Q ∉ L.lattice` using `fun h => hQ ((AnaSysW.ptW_zero_iff hU Q).2 h)`. Distinguish the cases in `hP : P ∈ L.lattice`. Conclude with `AnaSysW.prod_mem hU P Q hQl hP`.

Conclude with `AnaSysW.prod_notMem hU P Q hQl hP`.
-/
theorem analytic_translate_system_model : AnalyticSysW := by
  unfold AnalyticSysW
  intro l _ L ι W hU π hπ
  unfold IsTransSys
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [hπ] at ht
    exact AnaSysW.gW_mem (l := l) (L := L) (ι := ι) (W := W) t ((AnaSysW.ptW_zero_iff hU t).1 ht)
  · intro t ht
    simp only [hπ] at ht
    have htl : t ∉ L.lattice := fun h => ht ((AnaSysW.ptW_zero_iff hU t).2 h)
    rw [AnaSysW.cc_gW (l := l) (L := L) (ι := ι) (W := W) t]
    refine (map_ne_zero ι).mpr ?_
    simp only [F.opU, F.sgStar, zero_add]
    refine mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
    exact fun h => htl ((F.sigmaZero L t).1 h)
  · intro P Q hQ
    simp only [hπ] at hQ ⊢
    have hQl : Q ∉ L.lattice := fun h => hQ ((AnaSysW.ptW_zero_iff hU Q).2 h)
    by_cases hP : P ∈ L.lattice
    · exact AnaSysW.prod_mem hU P Q hQl hP
    · exact AnaSysW.prod_notMem hU P Q hQl hP

end Formalism.L2.Th1.E
