import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientIdeleScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalUnitLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeALocalPartHypothesisStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LamSupp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {n n₁ d d₁ : ℕ}

variable (σ : E →ₐ[F] E) in

def uStar (H : Plane E n n₁) (H' : Plane E d d₁) (z : AE F E) : Matrix (Fin n) (Fin d) (AE F E) :=
  cA σ z • Matrix.vecMulVec (incV F H.y) (incV F H'.x)

/- English proof (translation)
The claim follows from `Or.inl ⟨cA σ z • incV F H.y, by ext i j simp only [uStar, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]⟩`.
-/
theorem uStar_mem_isoA (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (z : AE F E) :
    uStar σ H H' z ∈ isoA H H' :=
  Or.inl ⟨cA σ z • incV F H.y, by
    ext i j
    simp only [uStar, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]⟩

/- English proof (translation)
Introduce `u hu`. Rewrite using `[uStar, ← smul_assoc, ← map_smul, GlobalTheory.VanishLoc.at_liftT v t u hu, map_zero, zero_smul]`.
-/
theorem at_uStar (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t : Fv F v ⊗[F] E) :
    At (evFin F v) (uStar σ H H' (GlobalTheory.VanishLoc.liftT v t)) := by
  intro u hu
  rw [uStar, ← smul_assoc, ← map_smul, GlobalTheory.VanishLoc.at_liftT v t u hu, map_zero, zero_smul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [GlobalTheory.VanishLoc.uAt, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem uAt_eq_smul (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t : Fv F v ⊗[F] E) :
    GlobalTheory.VanishLoc.uAt H H' v t = GlobalTheory.VanishLoc.liftT v t • Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by
  ext i j
  simp only [GlobalTheory.VanishLoc.uAt, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[partFin, smul_shiftA, GlobalTheory.VacShift.liftV_one_smul_eq, uAt_eq_smul]`. Both sides reduce to the same expression.
-/
theorem partFin_shiftA (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (l : (AE F E)ˣ) :
    partFin v (shiftA H H' l) = GlobalTheory.VanishLoc.uAt H H' v (compFin F E v l.1) := by
  rw [partFin, smul_shiftA, GlobalTheory.VacShift.liftV_one_smul_eq, uAt_eq_smul]
  rfl

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>`. Simplify using `[GlobalTheory.LatVac.locCo, partFin, GlobalTheory.LatVac.evFin_liftV]`.
-/
theorem locCo_partFin {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F}
    (co : Darboux Bf κ) (v : Pl F) (u : V) : GlobalTheory.LatVac.locCo co v (partFin v u) = GlobalTheory.LatVac.locCo co v u := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp [GlobalTheory.LatVac.locCo, partFin, GlobalTheory.LatVac.evFin_liftV]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]`. Rewrite using `[add_assoc x a.1 b.1]`. Establish `h : ψ (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) * ψ ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : R) * (b.1 ⬝ᵥ b.2)) = ψ (⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)) * ψ (x ⬝ᵥ (a.2 + b.2) + ⅟(2 : R) * ((a.1 + b.1) ⬝ᵥ (a.2 + b.2)))`. Simplify using `only [← AddChar.map_add_eq_mul]`.

Use `congr 1`. Establish `h2 : ⅟(2 : R) * 2 = 1` using `invOf_mul_self 2`. Simplify using `only [dotProduct_add, add_dotProduct]`. Take the linear combination `(-(a.1 ⬝ᵥ b.2)) * h2`. Take the linear combination `(φ (x + (a.1 + b.1))) * h`.
-/
theorem schr_schr_eq {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ a (schr ψ b φ) = ψ (⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)) • schr ψ (a + b) φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [add_assoc x a.1 b.1]
  have h : ψ (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) * ψ ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : R) * (b.1 ⬝ᵥ b.2)) =
      ψ (⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)) *
        ψ (x ⬝ᵥ (a.2 + b.2) + ⅟(2 : R) * ((a.1 + b.1) ⬝ᵥ (a.2 + b.2))) := by
    simp only [← AddChar.map_add_eq_mul]
    congr 1
    have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    simp only [dotProduct_add, add_dotProduct]
    linear_combination (-(a.1 ⬝ᵥ b.2)) * h2
  linear_combination (φ (x + (a.1 + b.1))) * h

/- English proof (translation)
Simplify using `only [uStar, map_add, add_smul]`.
-/
theorem uStar_add (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (s t : Fv F v ⊗[F] E) :
    uStar σ H H' (GlobalTheory.VanishLoc.liftT v (s + t)) =
      uStar σ H H' (GlobalTheory.VanishLoc.liftT v s) + uStar σ H H' (GlobalTheory.VanishLoc.liftT v t) := by
  simp only [uStar, map_add, add_smul]

/- English proof (translation)
Simplify using `only [uStar, GlobalTheory.VanishLocCont.liftT_smul, map_smul, smul_assoc]`.
-/
theorem uStar_smul (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (a : Fv F v)
    (t : Fv F v ⊗[F] E) :
    uStar σ H H' (GlobalTheory.VanishLoc.liftT v (a • t)) = GlobalTheory.LatVac.liftV v a • uStar σ H H' (GlobalTheory.VanishLoc.liftT v t) := by
  simp only [uStar, GlobalTheory.VanishLocCont.liftT_smul, map_smul, smul_assoc]

def locUStar {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁) (v : Pl F) :
    (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun t := GlobalTheory.LatVac.locCo M.co v (uStar σ H H' (GlobalTheory.VanishLoc.liftT v t))
  map_add' s t := by rw [uStar_add, map_add]
  map_smul' a t := by rw [uStar_smul, GlobalTheory.VanishLocCont.locCo_smul, RingHom.id_apply]

end GlobalTheory.LamSupp

end

noncomputable section

namespace GlobalTheory.LamSupp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {n n₁ d d₁ : ℕ}

open GlobalTheory.LocPair in

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.hTens, GlobalTheory.VanishLoc.uAt, uStar, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, incV, incM, Matrix.map_apply, smul_eq_mul, map_mul, cA_inclR, cA_cA hσ, form, dotProduct, Matrix.mulVec, map_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Use `(Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_` and prove the remaining obligations. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_uStar {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (JA : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin d) (Fin d) E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (x : Fv F v ⊗[F] E)
    (z : AE F E) :
    GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) (GlobalTheory.VanishLoc.uAt H H' v x) (uStar σ H H' z) =
      GlobalTheory.VanishLoc.liftT v x * z * inclR (F := F) (AF F) (form σ JA H.x H.y) *
        inclR (F := F) (AF F) (form σ JB H'.y H'.x) := by
  simp only [GlobalTheory.WeilM.hTens, GlobalTheory.VanishLoc.uAt, uStar, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
    incV, incM, Matrix.map_apply, smul_eq_mul, map_mul, cA_inclR, cA_cA hσ, form, dotProduct, Matrix.mulVec,
    map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => ?_)
  ring

open GlobalTheory.ConeSoB in

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hT.base.cm.2.2.1]; norm_num)`. Establish `hσ` using `cm_conj_conj hT.base.cm`. Establish `hxy : form σ G.V.J H.x H.y = 1` using `hC.hH.xy`. Establish `hyx : form σ G.W.J H'.y H'.x = -1`. Rewrite using `[GlobalTheory.LocPair.form_swap_skew hσ _ hT.geo.hW.skew, hC.hH'.xy, map_one]`.

Rewrite using `[GlobalTheory.LocPair.locCo_pair, GlobalTheory.WeilM.symp, hTens_uStar hσ, GlobalTheory.LocPair.evFin_trace, hxy, hyx, map_one, map_neg, map_one]`. Establish `e : (-1 : AE F E) * (GlobalTheory.VanishLoc.liftT v x * GlobalTheory.VanishLoc.liftT v t * 1 * -1) = GlobalTheory.VanishLoc.liftT v x * GlobalTheory.VanishLoc.liftT v t` using `by ring`. Rewrite using `[e, map_mul, GlobalTheory.LocPair.compFin_liftT, GlobalTheory.LocPair.compFin_liftT]`.
-/
theorem pair_uStar {σ : E →ₐ[F] E} (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (hC : CfgA B G G₁ H H') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (hT : IsTriple B G X om om') (v : Pl F) (x t : Fv F v ⊗[F] E) :
    (GlobalTheory.LatVac.locCo G.M.co v (GlobalTheory.VanishLoc.uAt H H' v x)).1 ⬝ᵥ
                 (GlobalTheory.LatVac.locCo G.M.co v (uStar σ H H' (GlobalTheory.VanishLoc.liftT v t))).2 -
      (GlobalTheory.LatVac.locCo G.M.co v (uStar σ H H' (GlobalTheory.VanishLoc.liftT v t))).1 ⬝ᵥ
        (GlobalTheory.LatVac.locCo G.M.co v (GlobalTheory.VanishLoc.uAt H H' v x)).2 =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hT.base.cm.2.2.1]; norm_num)
  have hσ := cm_conj_conj hT.base.cm
  have hxy : form σ G.V.J H.x H.y = 1 := hC.hH.xy
  have hyx : form σ G.W.J H'.y H'.x = -1 := by
    rw [GlobalTheory.LocPair.form_swap_skew hσ _ hT.geo.hW.skew, hC.hH'.xy, map_one]
  rw [GlobalTheory.LocPair.locCo_pair, GlobalTheory.WeilM.symp, hTens_uStar hσ, GlobalTheory.LocPair.evFin_trace, hxy, hyx, map_one, map_neg,
    map_one]
  have e : (-1 : AE F E) * (GlobalTheory.VanishLoc.liftT v x * GlobalTheory.VanishLoc.liftT v t * 1 * -1) =
      GlobalTheory.VanishLoc.liftT v x * GlobalTheory.VanishLoc.liftT v t := by ring
  rw [e, map_mul, GlobalTheory.LocPair.compFin_liftT, GlobalTheory.LocPair.compFin_liftT]

end GlobalTheory.LamSupp

end

open GlobalTheory.LamSupp in

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e hE ei ev hloc X om om' om₁ om₁' hT hT₁ v ψ hψ`. Establish `hψc : Continuous B.ψ` using `hT.base.std.1`. Establish `hψv : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.continuous_psiAt B.ψ hψc v`. Establish `hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1` using `GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`.

Use `set L := GlobalTheory.VanishLocCont.locUAt G.M H H' v with hLdef`. Use `set L' := locUStar G.M H H' v with hL'def`. Use `⟨fun x => ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hL : Continuous L` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hψl : IsLocallyConstant (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.isLocallyConstant_addChar _ hψv`.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `ht : Tendsto (fun y => L (y - x)) (𝓝 x) (𝓝 0)`. Establish `hc0 : Continuous fun y : Fv F v ⊗[F] E => L (y - x)` using `hL.comp (continuous_id.sub continuous_const)`. Establish `h` using `hc0.tendsto x`.

Simplify using `using h`. Establish `h1` using `ht.eventually (GlobalTheory.SchrSmall.schr_eventually_eq v (GlobalTheory.LatVac.psiAt B.ψ v) hψv ψ hψ)`. Establish `hc : Continuous fun w : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) × (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) => ⅟(2 : Fv F v) * ((L x).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (L x).2)` using `continuous_const.mul ((continuous_const.dotProduct continuous_snd).sub (continuous_fst.dotProduct continuous_const))`. Establish `h2` using `ht.eventually ((hψl.comp_continuous hc).eventually_eq (x := 0))`. Use `filter_upwards [h1, h2] with y hy1 hy2`.

Simplify using `only [Function.comp_apply, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, zero_dotProduct, sub_self, mul_zero, AddChar.map_zero_eq_one] at hy2`. Establish `e1 : L y = L x + L (y - x)` using `by rw [← map_add]; congr 1; abel`. Establish `h3` using `schr_schr_eq (GlobalTheory.LatVac.psiAt B.ψ v) (L x) (L (y - x)) ψ`. Rewrite `h3` using `[hy1, hy2, one_smul]`. Use `show ev v (schr _ (L y) ψ) = ev v (schr _ (L x) ψ)`.

Rewrite using `[e1, ← h3]`. Establish `hL' : Tendsto L' (𝓝 0) (𝓝 0)`. Establish `h` using `(IsModuleTopology.continuous_of_linearMap L').tendsto 0`. Rewrite `h` using `[map_zero]`. Then use the resulting hypothesis. Use `set U : Set (Fv F v ⊗[F] E) := {t | schr (GlobalTheory.LatVac.psiAt B.ψ v) (L' t) ψ = ψ} with hUdef`.

Establish `hU : U ∈ 𝓝 0` using `hL'.eventually (GlobalTheory.SchrSmall.schr_eventually_eq v (GlobalTheory.LatVac.psiAt B.ψ v) hψv ψ hψ)`. Use `⟨_, GlobalTheory.TraceAnnCompact.isCompact_trace_ann v (GlobalTheory.LatVac.psiAt B.ψ v) hψv hne U hU, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_forall] at hx`. Take `⟨t, ht, hne1⟩` from `hx`. Establish `ht' : schr (GlobalTheory.LatVac.psiAt B.ψ v) (L' t) ψ = ψ` using `ht`.

Establish `hS : schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ ∈ SB _` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ ψ hψ`. Establish `h1` using `GlobalTheory.T.seesaw_type_a_local_part_hypothesis B G G₁ H H' e hE ei ev hloc X om om' om₁ om₁' hT hT₁ v (uStar σ H H' (GlobalTheory.VanishLoc.liftT v t)) (uStar_mem_isoA σ H H' _) (at_uStar σ H H' v t) _ hS`. Establish `hcomm` using `GlobalTheory.VanishLoc.schr_comm (GlobalTheory.LatVac.psiAt B.ψ v) (L x) (L' t) ψ`. Rewrite `hcomm` using `[ht']`. Establish `hp : (L x).1 ⬝ᵥ (L' t).2 - (L' t).1 ⬝ᵥ (L x).2 = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t)` using `pair_uStar B G G₁ H H' hC X om om' hT v x t`.

Rewrite `hcomm` using `[hp]`. Establish `h2 : ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ) = GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t)) • ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ)` using `by conv_lhs => rw [hcomm]`. Rewrite using `[map_smul]`. Conclude with `congrArg _ h1`. Establish `h3 : (GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t)) - 1) • ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ) = 0`.

Rewrite using `[sub_smul, ← h2, one_smul, sub_self]`. Conclude with `(smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (by rwa [mul_comm]))`. Introduce `l _`. Rewrite using `[(locOp_rho G.M.co hψc v (shiftA H H' l) hψ).2, ← locCo_partFin, partFin_shiftA]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.LamSupp.lam_supp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F), ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ Gh : (Fv F v ⊗[F] E) → ((Fin b × Fin (b + a') → Fv F v) → ℂ), IsLocallyConstant Gh ∧
        (∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ x ∉ C, Gh x = 0) ∧
        ∀ l ∈ idelesAt E (evFin F v), ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) ψ) =
          Gh ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e hE ei ev hloc X om om' om₁ om₁' hT hT₁ v ψ hψ
  have hψc : Continuous B.ψ := hT.base.std.1
  have hψv : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψc v
  have hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  set L := GlobalTheory.VanishLocCont.locUAt G.M H H' v with hLdef
  set L' := locUStar G.M H H' v with hL'def
  refine ⟨fun x => ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ), ?_, ?_, ?_⟩
  · have hL : Continuous L := IsModuleTopology.continuous_of_linearMap _
    have hψl : IsLocallyConstant (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.isLocallyConstant_addChar _ hψv
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have ht : Tendsto (fun y => L (y - x)) (𝓝 x) (𝓝 0) := by
      have hc0 : Continuous fun y : Fv F v ⊗[F] E => L (y - x) := hL.comp (continuous_id.sub continuous_const)
      have h := hc0.tendsto x
      simpa using h
    have h1 := ht.eventually (GlobalTheory.SchrSmall.schr_eventually_eq v (GlobalTheory.LatVac.psiAt B.ψ v) hψv ψ hψ)
    have hc : Continuous fun w : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) × (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) =>
        ⅟(2 : Fv F v) * ((L x).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (L x).2) :=
      continuous_const.mul ((continuous_const.dotProduct continuous_snd).sub (continuous_fst.dotProduct continuous_const))
    have h2 := ht.eventually ((hψl.comp_continuous hc).eventually_eq (x := 0))
    filter_upwards [h1, h2] with y hy1 hy2
    simp only [Function.comp_apply, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, zero_dotProduct,
      sub_self, mul_zero, AddChar.map_zero_eq_one] at hy2
    have e1 : L y = L x + L (y - x) := by rw [← map_add]; congr 1; abel
    have h3 := schr_schr_eq (GlobalTheory.LatVac.psiAt B.ψ v) (L x) (L (y - x)) ψ
    rw [hy1, hy2, one_smul] at h3
    show ev v (schr _ (L y) ψ) = ev v (schr _ (L x) ψ)
    rw [e1, ← h3]
  · have hL' : Tendsto L' (𝓝 0) (𝓝 0) := by
      have h := (IsModuleTopology.continuous_of_linearMap L').tendsto 0
      rwa [map_zero] at h
    set U : Set (Fv F v ⊗[F] E) := {t | schr (GlobalTheory.LatVac.psiAt B.ψ v) (L' t) ψ = ψ} with hUdef
    have hU : U ∈ 𝓝 0 := hL'.eventually (GlobalTheory.SchrSmall.schr_eventually_eq v (GlobalTheory.LatVac.psiAt B.ψ v) hψv ψ hψ)
    refine ⟨_, GlobalTheory.TraceAnnCompact.isCompact_trace_ann v (GlobalTheory.LatVac.psiAt B.ψ v) hψv hne U hU, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨t, ht, hne1⟩ := hx
    have ht' : schr (GlobalTheory.LatVac.psiAt B.ψ v) (L' t) ψ = ψ := ht
    have hS : schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ ∈ SB _ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ ψ hψ
    have h1 := GlobalTheory.T.seesaw_type_a_local_part_hypothesis B G G₁ H H' e hE ei ev hloc X om om' om₁ om₁' hT hT₁ v
      (uStar σ H H' (GlobalTheory.VanishLoc.liftT v t)) (uStar_mem_isoA σ H H' _) (at_uStar σ H H' v t) _ hS
    have hcomm := GlobalTheory.VanishLoc.schr_comm (GlobalTheory.LatVac.psiAt B.ψ v) (L x) (L' t) ψ
    rw [ht'] at hcomm
    have hp : (L x).1 ⬝ᵥ (L' t).2 - (L' t).1 ⬝ᵥ (L x).2 = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t) :=
      pair_uStar B G G₁ H H' hC X om om' hT v x t
    rw [hp] at hcomm
    have h2 : ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ) =
        GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t)) •
          ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ) := by
      conv_lhs => rw [hcomm]
      rw [map_smul]
      exact congrArg _ h1
    have h3 : (GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * t)) - 1) •
        ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ) = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (by rwa [mul_comm]))
  · intro l _
    rw [(locOp_rho G.M.co hψc v (shiftA H H' l) hψ).2, ← locCo_partFin, partFin_shiftA]
    rfl
