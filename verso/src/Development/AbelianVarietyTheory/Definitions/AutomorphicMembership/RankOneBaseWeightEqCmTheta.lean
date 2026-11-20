import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUnitOfNorm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Formalism.FrobeniusOrbits.HostCorollaries

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Dim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

/- English proof (translation)
Use `A.t.semi.smooth` as an intermediate fact. Use `A.t.semi.geomConnected` as an intermediate fact. Establish `d₀ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (Out.jK A.R))`. Use `A.U.A.smoothDim` as an intermediate fact. Establish `: IsIso A.U.U.gen.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map A.U.U.gen.hom))`.

Rewrite using `[show pullback.snd A.t.G.hom (Out.jK A.R) = A.U.U.gen.hom.left ≫ A.U.A.A.hom from (Over.w A.U.U.gen.hom).symm]`. Use `infer_instance`. Establish `d₁` using `GenericDim.smoothOfRelativeDimension_of_generic A.R A.t.G _ d₀`. Establish `e : spMap (DatAtCheck.fC A) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _`. Use `Eq.trans ?_ P.ext` and prove the remaining obligations.

Rewrite using `[← A.fac, ← Category.assoc]`. Conclude with `congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))`. Establish `p₁` using `(IsPullback.of_hasPullback A.t.G.hom (spMap (DatAtCheck.fC A))).paste_horiz A.m.cart.1`. Establish `p₂` using `(IsPullback.of_hasPullback Y.oF.t.G.hom P.y).paste_horiz Y.m.cart.1`. Rewrite `p₁` using `[e]`.

Establish `d₂ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A)))` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) d₁`. Establish `d₃ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd Y.oF.t.G.hom P.y)` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) (ObjDim.smoothOfRelativeDimension Y.oF)`. Establish `d₄ : SmoothOfRelativeDimension (0 + Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A)))`. Rewrite using `[← p₁.isoIsPullback_hom_snd _ _ p₂]`. Use `infer_instance`.

Establish `: Surjective A.t.G.hom` using `inferInstance`. Take `⟨x, -⟩` from `(pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))).surjective (Per.gen ↥C.S)`. Simplify using `using H1.dim_unique _ d₂ d₄ x`.
-/
theorem generic_dim (A : DatAt Y P) : A.U.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have := A.t.semi.smooth
  have := A.t.semi.geomConnected
  have d₀ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (Out.jK A.R)) := by
    have := A.U.A.smoothDim
    have : IsIso A.U.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map A.U.U.gen.hom))
    rw [show pullback.snd A.t.G.hom (Out.jK A.R) = A.U.U.gen.hom.left ≫ A.U.A.A.hom from (Over.w A.U.U.gen.hom).symm]
    infer_instance
  have d₁ := GenericDim.smoothOfRelativeDimension_of_generic A.R A.t.G _ d₀
  have e : spMap (DatAtCheck.fC A) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ P.ext
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have p₁ := (IsPullback.of_hasPullback A.t.G.hom (spMap (DatAtCheck.fC A))).paste_horiz A.m.cart.1
  have p₂ := (IsPullback.of_hasPullback Y.oF.t.G.hom P.y).paste_horiz Y.m.cart.1
  rw [e] at p₁
  have d₂ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) d₁
  have d₃ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd Y.oF.t.G.hom P.y) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ObjDim.smoothOfRelativeDimension Y.oF)
  have d₄ : SmoothOfRelativeDimension (0 + Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) := by
    rw [← p₁.isoIsPullback_hom_snd _ _ p₂]
    infer_instance
  have : Surjective A.t.G.hom := inferInstance
  obtain ⟨x, -⟩ := (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))).surjective (Per.gen ↥C.S)
  simpa using H1.dim_unique _ d₂ d₄ x

/- English proof (translation)
Establish `h` using `UT.dim_eq_rank_add_dim firstFiveLaws A.R _ ⟨A.noeth, inferInstance, A.normal, A.complete⟩ A.U.D A.U.A A.t.G A.t.semi A.U.U`. Rewrite using `[← generic_dim A, add_comm]`. Conclude with `h.symm`.
-/
theorem dim_add_rank (A : DatAt Y P) :
    A.U.D.toPre.P.g + Module.finrank ℤ A.Ylat = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := UT.dim_eq_rank_add_dim firstFiveLaws A.R _ ⟨A.noeth, inferInstance, A.normal, A.complete⟩ A.U.D A.U.A A.t.G
    A.t.semi A.U.U
  rw [← generic_dim A, add_comm]
  exact h.symm

end Dim

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

/- English proof (translation)
Rewrite using `[D.host.finrank_cmField]`. Unfold `Ranks.f Ranks.n`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_host_eq (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]`.
-/
theorem complexConj_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `h` using `congrArg (algebraMap (𝓞 D.host.E) D.host.E) A.H.two_weight_eq_one_add_root`. Rewrite `h` using `[map_mul, map_add, map_one, map_ofNat]`. Establish `h₂ : algebraMap (𝓞 D.host.E) D.host.E A.H.rt = D.host.sqrtMinusD` using `A.rt_eq`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.E) D.host.E A.H.w0 = (1 + D.host.sqrtMinusD) / 2`.

Rewrite using `[← h₂, ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rankOne_base_weight_eq_cmTheta (A : Amb D) : A.H.w0 = w0 D := by
  apply RingOfIntegers.ext
  have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) A.H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, map_ofNat] at h
  have h₂ : algebraMap (𝓞 D.host.E) D.host.E A.H.rt = D.host.sqrtMinusD := A.rt_eq
  change algebraMap (𝓞 D.host.E) D.host.E A.H.w0 = (1 + D.host.sqrtMinusD) / 2
  rw [← h₂, ← h]
  ring

namespace At

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

def beLin : ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ := (ct.dat y).beLin (PointLawsEdge.betaAdd _ p)

def evidence : Per.Reading (ct.dat y) := (Per.nonempty_reading ct.hp.one_lt (ct.dat y)).some

def tauVal (a : ct.Ylat y) (χ : ct.chX y) : ((ct.fld y).C)ˣ := (ct.evidence y).t a ((ct.phi y).symm χ)

def lineShift (a : ct.Ylat y) : ct.chX y := ct.phi y a

def mulFst (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y a

def mulSnd (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y b

def mulConst (a b : ct.Ylat y) : ((ct.fld y).C)ˣ :=
  Exists.choose (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S))
    ⟨(ct.evidence y).t a b, (ct.evidence y).isVal a b⟩

def abDim : ℕ := (ct.dat y).U.D.toPre.P.g

/- English proof (translation)
The claim follows from `(ct.dat y).U.D.toPre.P.smoothDim`.
-/
theorem smooth_abDim : SmoothOfRelativeDimension (ct.abDim y) (ct.dat y).U.D.toPre.P.A.hom :=
  (ct.dat y).U.D.toPre.P.smoothDim

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem beLin_apply (a b : ct.Ylat y) : ct.beLin y a b = (ct.dat y).beta a b := rfl

/- English proof (translation)
The claim follows from `(ct.evidence y).isVal a b`.
-/
theorem isTauVal_tauVal (a b : ct.Ylat y) :
    Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) ((ct.tauVal y a (ct.phi y b) : ((ct.fld y).C)ˣ) : (ct.fld y).C) :=
  (ct.evidence y).isVal a b

/- English proof (translation)
The claim follows from `Exists.choose_spec (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S)) _`.
-/
theorem isTauVal_mulConst (a b : ct.Ylat y) :
    Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) ((ct.mulConst y a b : ((ct.fld y).C)ˣ) : (ct.fld y).C) :=
  Exists.choose_spec (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S)) _

/- English proof (translation)
Rewrite using `[mulFst, lineShift, lineShift, map_add, add_sub_cancel_left]`.
-/
theorem mulFst_eq (a b : ct.Ylat y) : ct.mulFst y a b = ct.phi y b := by
  rw [mulFst, lineShift, lineShift, map_add, add_sub_cancel_left]

/- English proof (translation)
Rewrite using `[mulSnd, lineShift, lineShift, map_add, add_sub_cancel_right]`.
-/
theorem mulSnd_eq (a b : ct.Ylat y) : ct.mulSnd y a b = ct.phi y a := by
  rw [mulSnd, lineShift, lineShift, map_add, add_sub_cancel_right]

/- English proof (translation)
The claim follows from `Units.ext ((ct.evidence y).eq_of_isTauVal (ct.isTauVal_mulConst y a b))`.
-/
theorem mulConst_eq (a b : ct.Ylat y) : ct.mulConst y a b = ct.tauVal y a (ct.phi y b) :=
  Units.ext ((ct.evidence y).eq_of_isTauVal (ct.isTauVal_mulConst y a b))

/- English proof (translation)
Establish `h` using `dim_add_rank (ct.dat y)`. Rewrite `h` using `[finrank_host_eq, S.rank_eq, Nat.mul_div_cancel_left _ two_pos]`. Conclude with `h`.
-/
theorem abDim_add : ct.abDim y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N := by
  have h := dim_add_rank (ct.dat y)
  rw [finrank_host_eq, S.rank_eq, Nat.mul_div_cancel_left _ two_pos] at h
  exact h

end At

def motTrue (ct : At S κ p) : MotSt ct where
  be y := ct.beLin y
  be_symm y a b := (ct.dat y).beta_symm a b
  be_bal y c c' h a b := PointLawsEdge.betaBal _ p _ _ (ct.dat y) c c' (h.trans (complexConj_eq_conj D _).symm) a b
  be_posDef y := PointLawsEdge.betaPosDef _ ct.hp.one_lt _ _ (ct.dat y)
  yl_rank y := by
    obtain ⟨ρ, h₁, h₂, h₃⟩ := PointLawsEdge.rank_le (ct.dat y)
    rw [finrank_host_eq, Nat.mul_div_cancel_left _ two_pos] at h₁
    have := S.p_eq
    have := S.rank_eq
    exact ⟨ρ, h₁, fun _ _ => by omega⟩
  psiV y a := vU p (ct.mulConst y a (w0 D • a))
  tau y := ct.tauVal y
  tau_add_left y a a' χ := (ct.evidence y).add_left a a' _
  tau_add_right y a χ χ' := (ct.evidence y).add_right a χ χ'
  tau_symm y a b := (ct.evidence y).symm a b
  tau_smul y c a χ := (ct.evidence y).bal c a χ
  be_tau y a b := (ct.evidence y).beta_eq a b
  multiplicationLatticeFirst y := ct.mulFst y
  multiplicationLatticeSecond y := ct.mulSnd y
  mulC y := ct.mulConst y
  psiV_def _ _ := rfl
  dimB y := ct.abDim y
  dimB_add y := ct.abDim_add y
  be_eq _ _ _ := rfl

section Api

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

/- English proof (translation)
Assemble the required witnesses or components as `⟨ct.mulFst_eq y a b, ct.mulSnd_eq y a b, ct.mulConst_eq y a b⟩`.
-/
theorem motTrue_mul (a b : ct.Ylat y) : (motTrue ct).multiplicationLatticeFirst y a b = ct.phi y b ∧ (motTrue ct).multiplicationLatticeSecond y a b = ct.phi y a ∧
    (motTrue ct).mulC y a b = (motTrue ct).tau y a (ct.phi y b) :=
  ⟨ct.mulFst_eq y a b, ct.mulSnd_eq y a b, ct.mulConst_eq y a b⟩

/- English proof (translation)
Rewrite using `[(motTrue ct).psiV_def, (motTrue_mul ct y _ _).2.2, (motTrue ct).be_tau]`.
-/
theorem motTrue_psiV_eq_be (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a (w0 D • a) := by
  rw [(motTrue ct).psiV_def, (motTrue_mul ct y _ _).2.2, (motTrue ct).be_tau]

/- English proof (translation)
Establish `h` using `(motTrue ct).be_bal y (w0 D) (1 - w0 D) (one_sub_halfSqrt_eq_conj D) a a`. Rewrite `h` using `[sub_smul, one_smul, map_sub, (motTrue ct).be_symm y (w0 D • a)]`. Rewrite using `[motTrue_psiV_eq_be]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem motTrue_psiV_half (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a a / 2 := by
  have h := (motTrue ct).be_bal y (w0 D) (1 - w0 D) (one_sub_halfSqrt_eq_conj D) a a
  rw [sub_smul, one_smul, map_sub, (motTrue ct).be_symm y (w0 D • a)] at h
  rw [motTrue_psiV_eq_be]
  linarith

/- English proof (translation)
Establish `h` using `(BetaAdd.main _ (ct.dat y).U.D _ (DatAtCheck.fC (ct.dat y)) p (ct.dat y).normal (DatAtCheck.norm_le _) (DatAtCheck.coord_ne_zero _)).2 a`. Rewrite using `[motTrue_psiV_half]`. Conclude with `(congrArg (· / 2) h).trans (mul_div_cancel_left₀ _ two_ne_zero)`.
-/
theorem motTrue_psiV_eq_vPsiAt (a : ct.Ylat y) :
    (motTrue ct).psiV y a = vPsiAt (ct.dat y).U.D.toPre (DatAtCheck.fC (ct.dat y)) p a := by
  have h := (BetaAdd.main _ (ct.dat y).U.D _ (DatAtCheck.fC (ct.dat y)) p (ct.dat y).normal (DatAtCheck.norm_le _)
    (DatAtCheck.coord_ne_zero _)).2 a
  rw [motTrue_psiV_half]
  exact (congrArg (· / 2) h).trans (mul_div_cancel_left₀ _ two_ne_zero)

/- English proof (translation)
Establish `h` using `(motTrue ct).tau_add_left y 0 0 χ`. Rewrite `h` using `[add_zero]`. Conclude with `left_eq_mul.1 h`.
-/
example (χ : ct.chX y) : (motTrue ct).tau y 0 χ = 1 := by
  have h := (motTrue ct).tau_add_left y 0 0 χ
  rw [add_zero] at h
  exact left_eq_mul.1 h

/- English proof (translation)
Rewrite using `[motTrue_psiV_half]`. Conclude with `half_pos (DatAtCheck.beta_self_pos ct.hp.one_lt (ct.dat y) a ha)`.
-/
example (a : ct.Ylat y) (ha : a ≠ 0) : 0 < (motTrue ct).psiV y a := by
  rw [motTrue_psiV_half]
  exact half_pos (DatAtCheck.beta_self_pos ct.hp.one_lt (ct.dat y) a ha)

/- English proof (translation)
Establish `h` using `(motTrue ct).dimB_add y`. Rewrite `h` using `[Module.finrank_zero_of_subsingleton, add_zero]`. Then use the resulting hypothesis.
-/
example (y : ct.Pt ct.Xm) [Subsingleton (ct.Ylat y)] : (motTrue ct).dimB y = D.R.f * N := by
  have h := (motTrue ct).dimB_add y
  rwa [Module.finrank_zero_of_subsingleton, add_zero] at h

end Api

end GlobalTheory.LocM
