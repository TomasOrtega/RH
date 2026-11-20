import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

omit [IsTotallyReal F] in
/- English proof (translation)
Take `⟨n, hn, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `e2 : ω.1 ^ n = 1` using `congrArg Subtype.val e`. Conclude with `⟨n, hn, fun x => by rw [← MonoidHom.pow_apply, e2, MonoidHom.one_apply]⟩`.
-/
theorem pow_char {ω : HChar F} (h : IsOfFinOrder ω) : ∃ n, 0 < n ∧ ∀ x, ω.1 x ^ n = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact ⟨n, hn, fun x => by rw [← MonoidHom.pow_apply, e2, MonoidHom.one_apply]⟩

/- English proof (translation)
Take `⟨n, hn, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n`. Use `Units.ext (funext fun i => ?_)` and prove the remaining obligations. Establish `: (n : ℝ) ≠ 0` using `by positivity`. Simplify using `only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, map_pow, map_pow]`. Establish `e2 : ω.1 ^ n = 1` using `congrArg Subtype.val e`. Conclude with `DFunLike.congr_fun e2 _`.
-/
theorem exp_triv {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

def pU : (TR.Rinf F)ˣ ≃* (InfinitePlace F → ℝˣ) := MulEquiv.piUnits

omit [NumberField F] [IsTotallyReal F] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pU_symm_val (f : InfinitePlace F → ℝˣ) (w : InfinitePlace F) :
    (((pU.symm f : (TR.Rinf F)ˣ) : TR.Rinf F) w) = (f w : ℝ) := rfl

omit [NumberField F] [IsTotallyReal F] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pU_val (s : (TR.Rinf F)ˣ) (w : InfinitePlace F) : ((pU s w : ℝˣ) : ℝ) = (s : TR.Rinf F) w := rfl

open Classical in

def atV (v : InfinitePlace F) (x : ℝˣ) : (TR.Rinf F)ˣ := pU.symm (Pi.mulSingle v x : InfinitePlace F → ℝˣ)

open Classical in
omit [NumberField F] [IsTotallyReal F] in
/- English proof (translation)
The claim follows from `pU_symm_val _ w`.
-/
theorem atV_val (v w : InfinitePlace F) (x : ℝˣ) :
    ((atV v x : (TR.Rinf F)ˣ) : TR.Rinf F) w = (((Pi.mulSingle v x : InfinitePlace F → ℝˣ) w : ℝˣ) : ℝ) := pU_symm_val _ w

/- English proof (translation)
Use `Units.ext (Prod.ext (funext fun w => ?_) ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 - TR.infEq F 1 + TR.infEq F ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w`. Rewrite using `[map_one, sub_self, zero_add]`. Express the relevant statement in the definitionally equal form `(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w) = _`. Distinguish the cases in `h : w = v`.

Substitute `h` using the available equality. Establish `: ((atV w (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = -1` using `by rw [atV_val]; simp`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `: ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = 1` using `by rw [atV_val, Pi.mulSingle_eq_of_ne h]; simp`.

Rewrite using `[this]`. Simplify using `[h]`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules.
-/
theorem atV_neg (v : InfinitePlace F) :
    TR.infId F (atV v (-1)) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
  classical
  refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
  · change (1 - TR.infEq F 1 + TR.infEq F ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F)) w =
      Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
    rw [map_one, sub_self, zero_add]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      (((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w) = _
    by_cases h : w = v
    · subst h
      have : ((atV w (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = -1 := by rw [atV_val]; simp
      rw [this]
      simp
    · have : ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = 1 := by rw [atV_val, Pi.mulSingle_eq_of_ne h]; simp
      rw [this]
      simp [h]
  · change (1 : Af F) - 0 + 0 = 1
    simp

open Classical in
omit [IsTotallyReal F] in
/- English proof (translation)
Simplify using `only [atV]`. Rewrite using `[← map_prod, Finset.univ_prod_mulSingle, MulEquiv.symm_apply_apply]`.
-/
theorem prod_atV (s : (TR.Rinf F)ˣ) : s = ∏ v, atV v (pU s v) := by
  simp only [atV]
  rw [← map_prod, Finset.univ_prod_mulSingle, MulEquiv.symm_apply_apply]

/- English proof (translation)
Take `⟨s, hss, e⟩` from `TR.exists_sign_mul_expU u`. Establish `hsv : ∀ v, (s : TR.Rinf F) v = 1 ∨ (s : TR.Rinf F) v = -1` using `fun v => by`. Use `congrArg (fun x : (TR.Rinf F)ˣ => (x : TR.Rinf F) v) hss` as an intermediate fact. Simplify using `only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at this`. Conclude with `mul_self_eq_one_iff.1 this`.

Establish `hsign : ∀ v, ((SignType.sign (u.val v) : ℝ)) = (s : TR.Rinf F) v` using `fun v => by`. Establish `hu : u.val v = (s : TR.Rinf F) v * Real.exp (Real.log |u.val v|)` using `by conv_lhs => rw [e]`. Simplify using `[TR.expU_val]`. Rewrite using `[hu, sign_mul, sign_pos (Real.exp_pos _), mul_one]`. Apply the tactic sequence `rcases hsv v with h | h <;> rw [h] <;> simp`.

Establish `hL : ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((ω.1 (TR.infId F (atV v (pU s v))) : ℂˣ) : ℂ)`. Establish `h1 : ω.1 (TR.infId F u) = ω.1 (TR.infId F s)`. Rewrite using `[e, map_mul, map_mul, exp_triv hω, mul_one]`. Rewrite using `[h1]`. Use `conv_lhs => rw [prod_atV s]`.

Rewrite using `[map_prod, map_prod, Units.coe_prod]`. Rewrite using `[hL]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hsign v]`. Establish `hpv : ((pU s v : ℝˣ) : ℝ) = (s : TR.Rinf F) v` using `pU_val s v`.

Break down `hsv v with h | h` into its components or cases. Establish `: pU s v = 1` using `Units.ext (hpv.trans h)`. Rewrite using `[this, h]`. Simplify using `[atV]`. Establish `: pU s v = -1` using `Units.ext (by rw [hpv, h]; simp)`.

Rewrite using `[this, h, atV_neg]`. Use `hs v` as an intermediate fact. Rewrite `this` using `[HChar.locInf]`. Simplify using `using this`.
-/
theorem inf_sign {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (u : (TR.Rinf F)ˣ) :
    ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (u.val v) : ℝ) : ℂ) ^ k v := by
  obtain ⟨s, hss, e⟩ := TR.exists_sign_mul_expU u
  have hsv : ∀ v, (s : TR.Rinf F) v = 1 ∨ (s : TR.Rinf F) v = -1 := fun v => by
    have := congrArg (fun x : (TR.Rinf F)ˣ => (x : TR.Rinf F) v) hss
    simp only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at this
    exact mul_self_eq_one_iff.1 this
  have hsign : ∀ v, ((SignType.sign (u.val v) : ℝ)) = (s : TR.Rinf F) v := fun v => by
    have hu : u.val v = (s : TR.Rinf F) v * Real.exp (Real.log |u.val v|) := by
      conv_lhs => rw [e]
      simp [TR.expU_val]
    rw [hu, sign_mul, sign_pos (Real.exp_pos _), mul_one]
    rcases hsv v with h | h <;> rw [h] <;> simp
  have hL : ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((ω.1 (TR.infId F (atV v (pU s v))) : ℂˣ) : ℂ) := by
    have h1 : ω.1 (TR.infId F u) = ω.1 (TR.infId F s) := by
      rw [e, map_mul, map_mul, exp_triv hω, mul_one]
    rw [h1]
    conv_lhs => rw [prod_atV s]
    rw [map_prod, map_prod, Units.coe_prod]
  rw [hL]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hsign v]
  have hpv : ((pU s v : ℝˣ) : ℝ) = (s : TR.Rinf F) v := pU_val s v
  rcases hsv v with h | h
  · have : pU s v = 1 := Units.ext (hpv.trans h)
    rw [this, h]
    simp [atV]
  · have : pU s v = -1 := Units.ext (by rw [hpv, h]; simp)
    rw [this, h, atV_neg]
    have := hs v
    rw [HChar.locInf] at this
    simpa using this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _`. Simplify using the standard rewrite rules.
-/
theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

/- English proof (translation)
Set `φ : F →+* TR.Rinf F` to `(TR.pInf F).comp (algebraMap F (AdeleRing (𝓞 F) F))`. Establish `e : TR.infId F (Units.map φ.toMonoidHom a) * finId F (ratU F a) = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a`. Use `Units.ext (TR.ad_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul]`. Express the relevant statement in the definitionally equal form `TR.pInf F (1 - TR.sInf F 1 + TR.sInf F (φ a)) * TR.pInf F (1 - GlobalTheory.CuspRep.sFin F 1 + GlobalTheory.CuspRep.sFin F _) = φ a`.

Establish `h1 : ∀ x, TR.pInf F (TR.sInf F x) = x` using `fun x => (TR.infEq F).symm_apply_apply x`. Establish `h2 : ∀ x, TR.pInf F (GlobalTheory.CuspRep.sFin F x) = 0` using `fun x => map_zero (TR.infEq F).symm`. Simplify using `only [map_add, map_sub, map_one, h1, h2, sub_self, zero_add, sub_zero, add_zero, mul_one]`. Rewrite using `[Units.val_mul, map_mul]`. Express the relevant statement in the definitionally equal form `((1 : Af F) - 0 + 0) * ((1 : Af F) - 1 + algebraMap F (Af F) a) = algebraMap F (Af F) a`.

Simplify using `only [sub_self, zero_add, sub_zero, add_zero, one_mul]`. Establish `h1 : ω.1 (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1` using `ω.2.2 a`. Rewrite `h1` using `[← e, map_mul]`. Establish `h2` using `congrArg Units.val h1`. Rewrite `h2` using `[Units.val_mul, Units.val_one, inf_sign hω hs]`.

Establish `h3 : ∀ v, ((Units.map φ.toMonoidHom a : (TR.Rinf F)ˣ) : TR.Rinf F) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)` using `fun v => pInf_alg (a : F) v`. Simplify using `only [h3] at h2`. Establish `hP : (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) * ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_pow]`. Establish `: ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) * ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) = 1`. Establish `ha : InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) ≠ 0` using `(map_ne_zero _).2 a.ne_zero`. Break down `lt_or_gt_of_ne ha with h | h` into its components or cases. Rewrite using `[sign_neg h]`.

Simplify using the standard rewrite rules. Rewrite using `[sign_pos h]`. Simplify using the standard rewrite rules. Rewrite using `[this, one_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fin_rat {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (a : Fˣ) :
    ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ) =
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v := by
  let φ : F →+* TR.Rinf F := (TR.pInf F).comp (algebraMap F (AdeleRing (𝓞 F) F))
  have e : TR.infId F (Units.map φ.toMonoidHom a) * finId F (ratU F a) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a := by
    refine Units.ext (TR.ad_ext ?_ ?_)
    · rw [Units.val_mul, map_mul]
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F (φ a)) *
        TR.pInf F (1 - GlobalTheory.CuspRep.sFin F 1 + GlobalTheory.CuspRep.sFin F _) = φ a
      have h1 : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
      have h2 : ∀ x, TR.pInf F (GlobalTheory.CuspRep.sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
      simp only [map_add, map_sub, map_one, h1, h2, sub_self, zero_add, sub_zero, add_zero, mul_one]
    · rw [Units.val_mul, map_mul]
      change ((1 : Af F) - 0 + 0) * ((1 : Af F) - 1 + algebraMap F (Af F) a) = algebraMap F (Af F) a
      simp only [sub_self, zero_add, sub_zero, add_zero, one_mul]
  have h1 : ω.1 (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := ω.2.2 a
  rw [← e, map_mul] at h1
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_one, inf_sign hω hs] at h2
  have h3 : ∀ v, ((Units.map φ.toMonoidHom a : (TR.Rinf F)ˣ) : TR.Rinf F) v =
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) := fun v => pInf_alg (a : F) v
  simp only [h3] at h2
  have hP : (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [← mul_pow]
    have : ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) *
        ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) = 1 := by
      have ha : InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) ≠ 0 :=
        (map_ne_zero _).2 a.ne_zero
      rcases lt_or_gt_of_ne ha with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
    rw [this, one_pow]
  calc _ = (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
        ((∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
          ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ)) := by rw [← mul_assoc, hP, one_mul]
    _ = _ := by rw [h2, mul_one]

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
/- English proof (translation)
Introduce `F _ _ _ k c ω χ hω hχ`. Use `⟨?_, fun hs => ⟨?_, inf_sign hω hs⟩⟩` and prove the remaining obligations. Take `⟨n, hn, hp⟩` from `pow_char hω`. Use `⟨n, hn, fun h => ?_⟩` and prove the remaining obligations. Take `⟨⟨k', hk', z, hz⟩, h2⟩` from `hχ h`.

Rewrite using `[h2 k' hk' z hz]`. Conclude with `hp _`. Introduce `γ h`. Take `⟨h1, h2, h3⟩` from `center_entries h`. Establish `h0 : γ 0 0 ≠ 0` using `fun e => γ.det_ne_zero (by rw [Matrix.det_fin_two, e, h1]; simp)`.

Use `set a : Fˣ := Units.mk0 _ h0 with ha`. Establish `hz : jF F γ = zc F (ratU F a)`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap F (Af F) (γ i j) = Matrix.scalar (Fin 2) (algebraMap F (Af F) (γ 0 0)) i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3]`.

Take `⟨-, hχ2⟩` from `hχ ⟨jF F γ, (mkDat c χ).cenH γ h⟩`. Establish `e` using `hχ2 1 (one_mem _) (ratU F a) (by rw [one_mul]; exact hz)`. Express the relevant statement in the definitionally equal form `((χ ⟨jF F γ, _⟩ : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (γ 0 0)) : ℝ) : ℂ) ^ k v`. Rewrite using `[e, fin_rat hω hs a]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Esk.hyperbolic_orbit_integral_proof : UpperTheory.Esk.H0b := by
  intro F _ _ _ k c ω χ hω hχ
  refine ⟨?_, fun hs => ⟨?_, inf_sign hω hs⟩⟩
  · obtain ⟨n, hn, hp⟩ := pow_char hω
    refine ⟨n, hn, fun h => ?_⟩
    obtain ⟨⟨k', hk', z, hz⟩, h2⟩ := hχ h
    rw [h2 k' hk' z hz]
    exact hp _
  · intro γ h
    obtain ⟨h1, h2, h3⟩ := center_entries h
    have h0 : γ 0 0 ≠ 0 := fun e => γ.det_ne_zero (by rw [Matrix.det_fin_two, e, h1]; simp)
    set a : Fˣ := Units.mk0 _ h0 with ha
    have hz : jF F γ = zc F (ratU F a) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change algebraMap F (Af F) (γ i j) = Matrix.scalar (Fin 2) (algebraMap F (Af F) (γ 0 0)) i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3]
    obtain ⟨-, hχ2⟩ := hχ ⟨jF F γ, (mkDat c χ).cenH γ h⟩
    have e := hχ2 1 (one_mem _) (ratU F a) (by rw [one_mul]; exact hz)
    change ((χ ⟨jF F γ, _⟩ : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (γ 0 0)) : ℝ) : ℂ) ^ k v
    rw [e, fin_rat hω hs a]
    rfl
