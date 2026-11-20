import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Natural

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Rewrite using `[inclL_apply, inclL_apply, ← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[map_mul]`.
-/
theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

/- English proof (translation)
Rewrite using `[homW_apply, inclL_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, inclL_apply]`. Establish `hM : ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) = ((homMat t ϖ F).map (frobOA l O)).map (inclO l O)`. Use extensionality with `i j`. Simplify using `[frobOW_inclO]`. Rewrite using `[hM]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (inclO l O).toRingHom _ _ i).symm`.
-/
theorem homW_inclL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (c : ι → OA l O) :
    homW t ϖ F (inclL t ϖ P c) = inclL t ϖ Q (((homMat t ϖ F).map (frobOA l O)) *ᵥ c) := by
  rw [homW_apply, inclL_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, inclL_apply]
  have hM : ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) =
      ((homMat t ϖ F).map (frobOA l O)).map (inclO l O) := by
    ext i j; simp [frobOW_inclO]
  rw [hM]
  congr 1
  funext i
  exact (RingHom.map_mulVec (inclO l O).toRingHom _ _ i).symm

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b y => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem map_id_smul {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}
    (g : ↥T.L.T →ₗ[O] ↥T'.L.T) (r : OB l O) (x : TW (OB l O) T) :
    TensorProduct.map LinearMap.id g (r • x) = r • TensorProduct.map LinearMap.id g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Establish `hmat : ∀ τ, Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ` using `fun τ => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[P.mx_mul_mxInv, Matrix.mul_one]`. Use `_ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by simp only [Matrix.mul_assoc]`. Use `_ = Q.mxInv τ * Q.mx τ * (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by`.

Rewrite using `[F.comm]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [Q.mxInv_mul_mx, Matrix.one_mul]`. Establish `hA : ∀ (g : ZMod a → A O K) (h : ∀ τ, (g τ : K⟦X⟧) ∈ invL l (S O K e)), ϖ.iB t K (fun τ => ⟨(g τ : K⟦X⟧), h τ⟩) = toB l O (ϖ.iTot t K g)` using `fun g h => (ϖ.iB_of_mem t K (fun τ => ⟨g τ, A_le_S l e (g τ).2⟩)).trans (congrArg (toOB l O) (ϖ.iC_of_mem t K g))`. Use function extensionality and compare the values at `i`.

Rewrite using `[toBcris_apply, Matrix.mulVec, dotProduct]`. Simplify using `only [Matrix.map_apply, toBcris_apply, homMat, Matrix.of_apply, ← PiSys.iTot_frob]`. Use `trans ∑ j, ϖ.iB t K (fun τ => ⟨(frobAc l (fun τ => ⟨F.mat τ i j, F.mem τ i j⟩) τ : K⟦X⟧), le_away _ _ (A_le_S l e (Subtype.prop _))⟩) * ϖ.iB t K (coordL P _ m j)`. Use `swap`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hA]`.

Simplify using `only [← map_mul, ← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `congrFun (congrArg (· *ᵥ (m.1 τ)) (hmat τ)) i`.

Simplify using `only [← Matrix.mulVec_mulVec] at h1`. Simplify using `only [Finset.sum_apply, Pi.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]`. Express the relevant statement in the definitionally equal form `(Q.mxInv τ *ᵥ m'.1 τ) i = ∑ j, frob K l (F.mat (τ - 1) i j) * (P.mxInv τ *ᵥ m.1 τ) j`. Rewrite using `[hm, BK.Hom.app_apply, h1]`. Both sides reduce to the same expression.
-/
theorem toBcris_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (m : P.MMl)
    (m' : Q.MMl) (hm : m'.1 = F.app m.1) :
    toBcris t ϖ Q m' = (((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ toBcris t ϖ P m := by
  have hmat : ∀ τ, Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := fun τ => by
    calc Q.mxInv τ * F.mat τ = Q.mxInv τ * F.mat τ * (P.mx τ * P.mxInv τ) := by
          rw [P.mx_mul_mxInv, Matrix.mul_one]
      _ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by simp only [Matrix.mul_assoc]
      _ = Q.mxInv τ * Q.mx τ * (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
          rw [F.comm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Q.mxInv_mul_mx, Matrix.one_mul]
  have hA : ∀ (g : ZMod a → A O K) (h : ∀ τ, (g τ : K⟦X⟧) ∈ invL l (S O K e)),
      ϖ.iB t K (fun τ => ⟨(g τ : K⟦X⟧), h τ⟩) = toB l O (ϖ.iTot t K g) := fun g h =>
    (ϖ.iB_of_mem t K (fun τ => ⟨g τ, A_le_S l e (g τ).2⟩)).trans
      (congrArg (toOB l O) (ϖ.iC_of_mem t K g))
  funext i
  rw [toBcris_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.map_apply, toBcris_apply, homMat, Matrix.of_apply, ← PiSys.iTot_frob]
  trans ∑ j, ϖ.iB t K (fun τ => ⟨(frobAc l (fun τ => ⟨F.mat τ i j, F.mem τ i j⟩) τ : K⟦X⟧),
      le_away _ _ (A_le_S l e (Subtype.prop _))⟩) * ϖ.iB t K (coordL P _ m j)
  swap
  · exact Finset.sum_congr rfl fun j _ => by rw [hA]
  simp only [← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  have h1 := congrFun (congrArg (· *ᵥ (m.1 τ)) (hmat τ)) i
  simp only [← Matrix.mulVec_mulVec] at h1
  simp only [Finset.sum_apply, Pi.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
  change (Q.mxInv τ *ᵥ m'.1 τ) i = ∑ j, frob K l (F.mat (τ - 1) i j) * (P.mxInv τ *ᵥ m.1 τ) j
  rw [hm, BK.Hom.app_apply, h1]
  rfl

variable [TameDescentExponentData K l e a]

/- English proof (translation)
Use `set Φ := TensorProduct.map (LinearMap.id : OB l O →ₗ[O] OB l O) ((f.f.restrictScalars O).restrict f.T_le) with hΦ`. Use `set H := (homMat t ϖ F).map (frobOA l O) with hH`. Set `Pr : (ι → OB l O) → Prop` to `fun v => jB' (H.map (toB l O) *ᵥ v) = Φ (jB v)`. Establish `hsm : ∀ (r : OB l O) v, Pr (r • v) ↔ r • jB' (H.map (toB l O) *ᵥ v) = r • Φ (jB v)`. Introduce `r v`.

Express the relevant statement in the definitionally equal form `jB' (H.map (toB l O) *ᵥ (r • v)) = Φ (jB (r • v)) ↔ _`. Rewrite using `[Matrix.mulVec_smul, map_smul, map_smul, hΦ, map_id_smul]`. Establish `hcancel : ∀ (r : OB l O) v, IsUnit r → Pr (r • v) → Pr v` using `fun r v hr h => (hr.smul_left_cancel).1 ((hsm r v).1 h)`. Establish `hofT : ∀ x : ↥T.L.T, Pr (jB.symm ((1 : OB l O) ⊗ₜ[O] x))`. Introduce `x`.

Take `⟨m, c, hu, hc, hb⟩` from `((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I).2 jB hB).2.2.2.1 x`. Take `⟨m', c', hu', hc', hb'⟩` from `((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Q T' I').2 jB' hB').2.2.2.1 ⟨f.f x, f.T_le _ x.2⟩`. Use `hcancel (toB l O m) _ hu ?_` and prove the remaining obligations. Establish `e1 : toB l O m • jB.symm ((1 : OB l O) ⊗ₜ[O] x) = fun i => toB l O (c i)`. Rewrite using `[← map_smul, hb, LinearEquiv.symm_apply_apply]`.

Express the relevant statement in the definitionally equal form `jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)`. Rewrite using `[e1]`. Establish `e2 : (H.map (toB l O) *ᵥ fun i => toB l O (c i)) = fun i => toB l O ((H *ᵥ c) i)`. Use function extensionality and compare the values at `fun i => (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm`. Establish `hc2 : inclO l O m • I'.ofT ⟨f.f x, f.T_le _ x.2⟩ = inclL t ϖ Q (H *ᵥ c)`.

Rewrite using `[← hF.homW_ofT x, ← (homW t ϖ F).map_smul, hc, homW_inclL]`. Establish `heq : m' • (H *ᵥ c) = m • c'`. Apply `inclL_injective t ϖ Q` to reduce the goal to its premises. Rewrite using `[inclL_smul, inclL_smul, ← hc2, ← hc', smul_comm]`. Establish `heqB : toB l O m' • (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • fun i => toB l O (c' i)`.

Use function extensionality and compare the values at `i`. Use `congrArg (toB l O) (congrFun heq i)` as an intermediate fact. Simplify `this` using `[map_mul]`. Establish `e3 : jB' (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • ((1 : OB l O) ⊗ₜ[O] (⟨f.f x, f.T_le _ x.2⟩ : ↥T'.L.T))`. Use `(hu'.smul_left_cancel).1 ?_` and prove the remaining obligations.

Rewrite using `[← map_smul, heqB, map_smul, ← hb', smul_comm]`. Rewrite using `[e2, e3, ← hb, hΦ, map_id_smul]`. Both sides reduce to the same expression. Take `⟨y, rfl⟩` from `jB.symm.surjective v`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul b x`. Establish `: b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul]`. Conclude with `(hsm b _).2 (by rw [hofT x])`.

Consider the case `add x y hx hy`. Express the relevant statement in the definitionally equal form `jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)`. Rewrite using `[map_add, Matrix.mulVec_add, map_add, map_add, map_add]`. Conclude with `congrArg₂ (· + ·) hx hy`.
-/
theorem jB_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) (v : ι → OB l O) :
    jB' ((((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ v) =
      TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB v) := by
  set Φ := TensorProduct.map (LinearMap.id : OB l O →ₗ[O] OB l O) ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  set H := (homMat t ϖ F).map (frobOA l O) with hH
  let Pr : (ι → OB l O) → Prop := fun v => jB' (H.map (toB l O) *ᵥ v) = Φ (jB v)
  have hsm : ∀ (r : OB l O) v, Pr (r • v) ↔ r • jB' (H.map (toB l O) *ᵥ v) = r • Φ (jB v) := by
    intro r v
    change jB' (H.map (toB l O) *ᵥ (r • v)) = Φ (jB (r • v)) ↔ _
    rw [Matrix.mulVec_smul, map_smul, map_smul, hΦ, map_id_smul]
  have hcancel : ∀ (r : OB l O) v, IsUnit r → Pr (r • v) → Pr v := fun r v hr h =>
    (hr.smul_left_cancel).1 ((hsm r v).1 h)
  have hofT : ∀ x : ↥T.L.T, Pr (jB.symm ((1 : OB l O) ⊗ₜ[O] x)) := by
    intro x
    obtain ⟨m, c, hu, hc, hb⟩ := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I).2 jB hB).2.2.2.1 x
    obtain ⟨m', c', hu', hc', hb'⟩ :=
      ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Q T' I').2 jB' hB').2.2.2.1 ⟨f.f x, f.T_le _ x.2⟩
    refine hcancel (toB l O m) _ hu ?_
    have e1 : toB l O m • jB.symm ((1 : OB l O) ⊗ₜ[O] x) = fun i => toB l O (c i) := by
      rw [← map_smul, hb, LinearEquiv.symm_apply_apply]
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [e1]
    have e2 : (H.map (toB l O) *ᵥ fun i => toB l O (c i)) = fun i => toB l O ((H *ᵥ c) i) :=
      funext fun i => (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm
    have hc2 : inclO l O m • I'.ofT ⟨f.f x, f.T_le _ x.2⟩ = inclL t ϖ Q (H *ᵥ c) := by
      rw [← hF.homW_ofT x, ← (homW t ϖ F).map_smul, hc, homW_inclL]
    have heq : m' • (H *ᵥ c) = m • c' := by
      apply inclL_injective t ϖ Q
      rw [inclL_smul, inclL_smul, ← hc2, ← hc', smul_comm]
    have heqB : toB l O m' • (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • fun i => toB l O (c' i) := by
      funext i
      have := congrArg (toB l O) (congrFun heq i)
      simpa [map_mul] using this
    have e3 : jB' (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • ((1 : OB l O) ⊗ₜ[O] (⟨f.f x, f.T_le _ x.2⟩ : ↥T'.L.T)) := by
      refine (hu'.smul_left_cancel).1 ?_
      rw [← map_smul, heqB, map_smul, ← hb', smul_comm]
    rw [e2, e3, ← hb, hΦ, map_id_smul]
    rfl
  obtain ⟨y, rfl⟩ := jB.symm.surjective v
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    have : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact (hsm b _).2 (by rw [hofT x])
  | add x y hx hy =>
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [map_add, Matrix.mulVec_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

/- English proof (translation)
Take `⟨m, c, hu, hc, hb⟩` from `h`. Use `⟨m, ((homMat t ϖ F).map (frobOA l O)) *ᵥ c, hu, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← (homW t ϖ F).map_smul, hc, homW_inclL]`. Rewrite using `[← map_id_smul ((f.f.restrictScalars O).restrict f.T_le), hb, ← jB_hom t ϖ hB hB' hF]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm`.
-/
theorem isCrisVal_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) :
    IsCrisVal t ϖ Q jB' (homW t ϖ F w)
      (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  refine ⟨m, ((homMat t ϖ F).map (frobOA l O)) *ᵥ c, hu, ?_, ?_⟩
  · rw [← (homW t ϖ F).map_smul, hc, homW_inclL]
  · rw [← map_id_smul ((f.f.restrictScalars O).restrict f.T_le), hb, ← jB_hom t ϖ hB hB' hF]
    congr 1
    funext i
    exact (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm

end GlobalTheory.BKGal.Natural

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hB κ _ _ Q T' I' jB' f F hB' hF`. Use `⟨fun m m' hm => ?_, fun w b hw => GlobalTheory.BKGal.Natural.isCrisVal_hom t ϖ hB hB' hF hw⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.BKGal.Natural.toBcris_hom t ϖ F m m' hm]`. Conclude with `GlobalTheory.BKGal.Natural.jB_hom t ϖ hB hB' hF _`.
-/
theorem GlobalTheory.BKGal.cris_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hB κ _ _ Q T' I' jB' f F hB' hF
  refine ⟨fun m m' hm => ?_, fun w b hw => GlobalTheory.BKGal.Natural.isCrisVal_hom t ϖ hB hB' hF hw⟩
  rw [GlobalTheory.BKGal.Natural.toBcris_hom t ϖ F m m' hm]
  exact GlobalTheory.BKGal.Natural.jB_hom t ϖ hB hB' hF _
