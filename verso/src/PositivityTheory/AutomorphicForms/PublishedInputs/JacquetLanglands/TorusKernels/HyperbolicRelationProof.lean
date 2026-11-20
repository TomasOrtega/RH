import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.IdeleSplittingLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def zg (g : GL (Fin 2) (TR.Rinf F)) : InfinitePlace F → P := fun v => gv v g • iP

def Jg (k : InfinitePlace F → ℕ) (g : GL (Fin 2) (TR.Rinf F)) : ℂ := ∏ v, j1 (k v) (gv v g) iP

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _`.
-/
theorem Jg_ne (hB : B1b) (k : InfinitePlace F → ℕ) (g : GL (Fin 2) (TR.Rinf F)) : Jg k g ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _

/- English proof (translation)
Establish `h : algebraMap F (InfiniteAdeleRing F) x = TR.infEq F (fun w => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x)`. Use function extensionality and compare the values at `w`. Apply `(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).injective` to reduce the goal to its premises. Use `show _ = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)) ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x))`. Rewrite using `[RingEquiv.apply_symm_apply]`.

Conclude with `InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) _`. Express the relevant statement in the definitionally equal form `(TR.infEq F).symm (algebraMap F (InfiniteAdeleRing F) x) v = _`. Rewrite using `[h, RingEquiv.symm_apply_apply]`.
-/
theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have h : algebraMap F (InfiniteAdeleRing F) x = TR.infEq F (fun w => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) := by
    funext w
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).injective
    show _ = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
        (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x))
    rw [RingEquiv.apply_symm_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) _
  change (TR.infEq F).symm (algebraMap F (InfiniteAdeleRing F) x) v = _
  rw [h, RingEquiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun i j => pInf_alg (γ i j) v)`.
-/
theorem gv_rat (γ : GL (Fin 2) F) (v : InfinitePlace F) :
    gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ)) =
      Matrix.GeneralLinearGroup.map (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)) γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg (γ i j) v)

omit [IsTotallyReal F] in
/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => rfl)`.
-/
theorem pFin_rat (γ : GL (Fin 2) F) : Matrix.GeneralLinearGroup.map (pFin F) (ratGL F 2 γ) = jF F γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
Rewrite using `[eq_div_iff (Jg_ne hB k _)]`. Use `hr (Matrix.GeneralLinearGroup.map (TR.pInf F) h) (Matrix.GeneralLinearGroup.map (pFin F) h)` as an intermediate fact. Rewrite `this` using `[TR.infGL_mul_finGL]`. Then use the resulting hypothesis.
-/
theorem val_eq (hB : B1b) {k : InfinitePlace F → ℕ} {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ}
    (hr : Rel k f φ) (h : GA F 2) :
    φ h = f (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) h), Matrix.GeneralLinearGroup.map (pFin F) h) /
      Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) h) := by
  rw [eq_div_iff (Jg_ne hB k _)]
  have := hr (Matrix.GeneralLinearGroup.map (TR.pInf F) h) (Matrix.GeneralLinearGroup.map (pFin F) h)
  rwa [TR.infGL_mul_finGL] at this

/- English proof (translation)
Rewrite using `[val_eq hB hr, val_eq hB hr, map_mul, map_mul, pFin_rat]`. Use `set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g`. Use `set x := Matrix.GeneralLinearGroup.map (pFin F) g`. Establish `hz : zg (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).act γ (zg a)`. Use function extensionality and compare the values at `v`.

Simplify using `only [zg, map_mul, gv_rat, mul_smul]`. Both sides reduce to the same expression. Establish `hJ : Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).J k γ (zg a) * Jg k a`. Simplify using `only [Jg, Dat.J, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hB.1, gv_rat]`. Both sides reduce to the same expression. Establish `hne : (mkDat c χ).J k γ (zg a) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _`. Rewrite using `[hz, hJ, show jF F γ * x = (mkDat c χ).j γ * x from rfl, hf.aut, mul_div_mul_left _ _ hne]`.
-/
theorem part1 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {χ : Hc c →* ℂˣ} {f : (InfinitePlace F → P) × GF F → ℂ}
    {φ : GA F 2 → ℂ} (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) (γ : GL (Fin 2) F) (g : GA F 2) :
    φ (ratGL F 2 γ * g) = φ g := by
  rw [val_eq hB hr, val_eq hB hr, map_mul, map_mul, pFin_rat]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set x := Matrix.GeneralLinearGroup.map (pFin F) g
  have hz : zg (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).act γ (zg a) := by
    funext v
    simp only [zg, map_mul, gv_rat, mul_smul]
    rfl
  have hJ : Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).J k γ (zg a) * Jg k a := by
    simp only [Jg, Dat.J, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, hB.1, gv_rat]
    rfl
  have hne : (mkDat c χ).J k γ (zg a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _
  rw [hz, hJ, show jF F γ * x = (mkDat c χ).j γ * x from rfl, hf.aut, mul_div_mul_left _ _ hne]

/- English proof (translation)
Rewrite using `[val_eq hB hr, val_eq hB hr, map_mul, map_mul, TR.pInf_finGL, mul_one, pFin_finGL]`. Establish `hH : u ∈ Hc c` using `Subgroup.mem_sup_left hu`. Establish `h1` using `hf.lev (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) g)) (Matrix.GeneralLinearGroup.map (pFin F) g) (⟨u, hH⟩ : (mkDat c χ).H)`. Establish `h2 : χ ⟨u, hH⟩ = 1`. Rewrite using `[(hχ ⟨u, hH⟩).2 u hu 1 (by simp [zc]), map_one, map_one]`.

Express the relevant statement in the definitionally equal form `f (_, _ * u) = (χ ⟨u, hH⟩ : ℂ) * _ at h1`. Rewrite using `[h1, h2, Units.val_one, one_mul]`.
-/
theorem part2 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hχ : IsChi c ω χ) (hf : (mkDat c χ).IsForm k f)
    (hr : Rel k f φ) (u : GF F) (hu : u ∈ Kc c) (g : GA F 2) : φ (g * finGL F 2 u) = φ g := by
  rw [val_eq hB hr, val_eq hB hr, map_mul, map_mul, TR.pInf_finGL, mul_one, pFin_finGL]
  have hH : u ∈ Hc c := Subgroup.mem_sup_left hu
  have h1 := hf.lev (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) g)) (Matrix.GeneralLinearGroup.map (pFin F) g)
    (⟨u, hH⟩ : (mkDat c χ).H)
  have h2 : χ ⟨u, hH⟩ = 1 := by
    rw [(hχ ⟨u, hH⟩).2 u hu 1 (by simp [zc]), map_one, map_one]
  change f (_, _ * u) = (χ ⟨u, hH⟩ : ℂ) * _ at h1
  rw [h1, h2, Units.val_one, one_mul]

/- English proof (translation)
Establish `h : ∀ x, TR.pInf F (TR.sInf F x) = x` using `fun x => (TR.infEq F).symm_apply_apply x`. Establish `h2 : ∀ x, TR.pInf F (sFin F x) = 0` using `fun x => map_zero (TR.infEq F).symm`. Establish `h3 : ∀ x, pFin F (TR.sInf F x) = 0` using `fun x => rfl`. Establish `h4 : ∀ x, pFin F (sFin F x) = x` using `fun x => rfl`. Use `Units.ext (TR.ad_ext ?_ ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _`. Simplify using `[h, h2]`. Express the relevant statement in the definitionally equal form `pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _`. Simplify using `[h3, h4]`.
-/
theorem idele_split (z : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom z) * finId F (Units.map (pFin F).toMonoidHom z) = z := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _
    simp [h3, h4]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]`.
-/
theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map p.toMonoidHom z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Establish `ha : 0 < |s|` using `abs_pos.2 hs`. Establish `e1 : |s * s| ^ (-(k : ℝ) / 2) = (|s| ^ k)⁻¹`. Rewrite using `[abs_mul, ← sq, ← Real.rpow_natCast |s| 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast, ← Real.rpow_neg ha.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sign_pow (k : ℕ) {s : ℝ} (hs : s ≠ 0) :
    s ^ k * |s * s| ^ (-(k : ℝ) / 2) = (SignType.sign s : ℝ) ^ k := by
  have ha : 0 < |s| := abs_pos.2 hs
  have e1 : |s * s| ^ (-(k : ℝ) / 2) = (|s| ^ k)⁻¹ := by
    rw [abs_mul, ← sq, ← Real.rpow_natCast |s| 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast, ← Real.rpow_neg ha.le]
    congr 1
    push_cast
    ring
  rw [e1]
  calc s ^ k * (|s| ^ k)⁻¹ = ((SignType.sign s : ℝ) * |s|) ^ k * (|s| ^ k)⁻¹ := by rw [sign_mul_abs]
    _ = _ := by rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), mul_one]

/- English proof (translation)
Rewrite using `[j1, den, det_eq, h10, h01, h00, h11, ← Complex.ofReal_pow, ← sign_pow k hs]`. Simplify using `[Complex.ofReal_mul]`.
-/
theorem automorphy_factor_scalar_matrix (k : ℕ) (g : GL (Fin 2) ℝ) (s : ℝ) (hs : s ≠ 0) (h10 : g 1 0 = 0) (h01 : g 0 1 = 0) (h00 : g 0 0 = s)
    (h11 : g 1 1 = s) (w : P) : j1 k g w = ((SignType.sign s : ℝ) : ℂ) ^ k := by
  rw [j1, den, det_eq, h10, h01, h00, h11, ← Complex.ofReal_pow, ← sign_pow k hs]
  simp [Complex.ofReal_mul]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gv, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]`.
-/
theorem gv_scalar (t : (TR.Rinf F)ˣ) (v : InfinitePlace F) :
    (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 1 0 = 0 ∧ (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 0 1 = 0 ∧
      (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 0 0 = t.val v ∧
      (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 1 1 = t.val v := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gv, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Use `set zi := Units.map (TR.pInf F).toMonoidHom z`. Use `set zf := Units.map (pFin F).toMonoidHom z`. Establish `hω' : ((ω.1 z : ℂˣ) : ℂ) = ((ω.1 (TR.infId F zi) : ℂˣ) : ℂ) * ((ω.1 (finId F zf) : ℂˣ) : ℂ)`. Rewrite using `[← Units.val_mul, ← map_mul, idele_split]`. Establish `hS` using `((h0 F k c ω χ hω hχ).2 hs).2 zi`.

Rewrite using `[val_eq hB hr, val_eq hB hr g, map_mul, map_mul, map_scalar, map_scalar]`. Use `set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g`. Use `set x := Matrix.GeneralLinearGroup.map (pFin F) g`. Use `set S : ℂ := ∏ v, ((SignType.sign (zi.val v) : ℝ) : ℂ) ^ k v`. Establish `hz : zg (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = zg a`.

Use function extensionality and compare the values at `v`. Take `⟨e1, e2, e3, e4⟩` from `gv_scalar zi v`. Simplify using `only [zg, map_mul, mul_smul]`. Conclude with `center_smul _ e2 e1 (e3.trans e4.symm) _`. Establish `hJ : Jg k (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = S * Jg k a`.

Simplify using `only [Jg, S, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Take `⟨e1, e2, e3, e4⟩` from `gv_scalar zi v`. Rewrite using `[map_mul, hB.1, automorphy_factor_scalar_matrix _ _ (zi.val v) (TR.unit_ne_zero zi v) e1 e2 e3 e4]`. Establish `hH : zc F zf ∈ Hc c` using `Subgroup.mem_sup_right ⟨zf, rfl⟩`.

Establish `hc : χ ⟨zc F zf, hH⟩ = ω.1 (finId F zf)` using `(hχ ⟨zc F zf, hH⟩).2 1 (one_mem _) zf (one_mul _).symm`. Establish `hl` using `hf.lev (zg a) x (⟨zc F zf, hH⟩ : (mkDat c χ).H)`. Express the relevant statement in the definitionally equal form `f (_, x * zc F zf) = (χ ⟨zc F zf, hH⟩ : ℂ) * _ at hl`. Establish `hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) zf * x = x * zc F zf` using `(Subgroup.mem_center_iff.1 (zc_center zf) x).symm`. Establish `hSS : S * S = 1`.

Simplify using `only [S, ← Finset.prod_mul_distrib, ← mul_pow]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (TR.unit_ne_zero zi v) with h | h` into its components or cases. Simplify using `[h]`. Simplify using `[h]`.

Establish `hSne : S ≠ 0` using `left_ne_zero_of_mul_eq_one hSS`. Rewrite using `[hz, hJ, hcomm, hl, hc, hω', hS, div_eq_iff (mul_ne_zero hSne (Jg_ne hB k a))]`. Rewrite using `[show S * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * (f (zg a, x) / Jg k a) * (S * Jg k a) = (S * S) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * f (zg a, x) * ((Jg k a)⁻¹ * Jg k a) by ring, hSS, inv_mul_cancel₀ (Jg_ne hB k a)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem part3 (hB : B1b) (h0 : H0b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hω : IsOfFinOrder ω) (hχ : IsChi c ω χ) (hs : Sgn k ω)
    (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) (z : Ideles F) (g : GA F 2) :
    φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g := by
  set zi := Units.map (TR.pInf F).toMonoidHom z
  set zf := Units.map (pFin F).toMonoidHom z
  have hω' : ((ω.1 z : ℂˣ) : ℂ) = ((ω.1 (TR.infId F zi) : ℂˣ) : ℂ) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, idele_split]
  have hS := ((h0 F k c ω χ hω hχ).2 hs).2 zi
  rw [val_eq hB hr, val_eq hB hr g, map_mul, map_mul, map_scalar, map_scalar]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set x := Matrix.GeneralLinearGroup.map (pFin F) g
  set S : ℂ := ∏ v, ((SignType.sign (zi.val v) : ℝ) : ℂ) ^ k v
  have hz : zg (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = zg a := by
    funext v
    obtain ⟨e1, e2, e3, e4⟩ := gv_scalar zi v
    simp only [zg, map_mul, mul_smul]
    exact center_smul _ e2 e1 (e3.trans e4.symm) _
  have hJ : Jg k (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = S * Jg k a := by
    simp only [Jg, S, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨e1, e2, e3, e4⟩ := gv_scalar zi v
    rw [map_mul, hB.1, automorphy_factor_scalar_matrix _ _ (zi.val v) (TR.unit_ne_zero zi v) e1 e2 e3 e4]
  have hH : zc F zf ∈ Hc c := Subgroup.mem_sup_right ⟨zf, rfl⟩
  have hc : χ ⟨zc F zf, hH⟩ = ω.1 (finId F zf) := (hχ ⟨zc F zf, hH⟩).2 1 (one_mem _) zf (one_mul _).symm
  have hl := hf.lev (zg a) x (⟨zc F zf, hH⟩ : (mkDat c χ).H)
  change f (_, x * zc F zf) = (χ ⟨zc F zf, hH⟩ : ℂ) * _ at hl
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) zf * x = x * zc F zf :=
    (Subgroup.mem_center_iff.1 (zc_center zf) x).symm
  have hSS : S * S = 1 := by
    simp only [S, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_eq_one fun v _ => ?_
    rcases lt_or_gt_of_ne (TR.unit_ne_zero zi v) with h | h
    · simp [h]
    · simp [h]
  have hSne : S ≠ 0 := left_ne_zero_of_mul_eq_one hSS
  rw [hz, hJ, hcomm, hl, hc, hω', hS, div_eq_iff (mul_ne_zero hSne (Jg_ne hB k a))]
  rw [show S * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * (f (zg a, x) / Jg k a) * (S * Jg k a) =
    (S * S) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * f (zg a, x) * ((Jg k a)⁻¹ * Jg k a) by ring, hSS,
    inv_mul_cancel₀ (Jg_ne hB k a)]
  ring

/- English proof (translation)
Take `⟨C, hC⟩` from `hf.bdd`. Use `⟨C, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[val_eq hB hr h, norm_div]`. Use `set a := Matrix.GeneralLinearGroup.map (TR.pInf F) h`. Establish `hn : ‖Jg k a‖ * nrm k (zg a) = 1`.

Rewrite using `[Jg, nrm, norm_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Rewrite using `[zg, hB.2.2.2.2.1]`. Simplify using `[iP]`. Establish `hpos : 0 < ‖Jg k a‖` using `norm_pos_iff.2 (Jg_ne hB k a)`.

Rewrite using `[div_le_iff₀ hpos]`. Use `hC (zg a) (Matrix.GeneralLinearGroup.map (pFin F) h)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_comm (nrm k _), hn, mul_one]`. Use `_ ≤ C * ‖Jg k a‖ := mul_le_mul_of_nonneg_right this hpos.le`.
-/
theorem part4 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) :
    ∃ C, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨C, fun h => ?_⟩
  rw [val_eq hB hr h, norm_div]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) h
  have hn : ‖Jg k a‖ * nrm k (zg a) = 1 := by
    rw [Jg, nrm, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [zg, hB.2.2.2.2.1]
    simp [iP]
  have hpos : 0 < ‖Jg k a‖ := norm_pos_iff.2 (Jg_ne hB k a)
  rw [div_le_iff₀ hpos]
  have := hC (zg a) (Matrix.GeneralLinearGroup.map (pFin F) h)
  calc _ = ‖f (zg a, Matrix.GeneralLinearGroup.map (pFin F) h)‖ * nrm k (zg a) * ‖Jg k a‖ := by
        rw [mul_assoc, mul_comm (nrm k _), hn, mul_one]
    _ ≤ C * ‖Jg k a‖ := mul_le_mul_of_nonneg_right this hpos.le

end UpperTheory.Esk.IdeleSplittingLemmas

/- English proof (translation)
Introduce `hB h0 F _ _ _ k c _ ω χ hω hχ hs _ f φ hf hr`. Conclude with `⟨UpperTheory.Esk.IdeleSplittingLemmas.part1 hB hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part2 hB hχ hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part3 hB h0 hω hχ hs hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part4 hB hf hr⟩`.
-/
theorem UpperTheory.Esk.hyperbolic_relation_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.H0b → UpperTheory.Esk.H2a := by
  intro hB h0 F _ _ _ k c _ ω χ hω hχ hs _ f φ hf hr
  exact ⟨UpperTheory.Esk.IdeleSplittingLemmas.part1 hB hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part2 hB hχ hf hr,
    UpperTheory.Esk.IdeleSplittingLemmas.part3 hB h0 hω hχ hs hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part4 hB hf hr⟩
