import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMem
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CosetTheta

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA`. Use `Submodule.subset_span fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec]`. Conclude with `hM _ (hA x hx)`.

Consider the case `zero => simp`. Consider the case `add A B _ _ hA hB => rw [smul_add]`. Conclude with `add_mem hA hB`. Consider the case `smul c A _ hA => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ c hA`.
-/
theorem homL_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L₁) : M • A ∈ homL D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    rw [Matrix.smul_mulVec]
    exact hM _ (hA x hx)
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

/- English proof (translation)
Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem B hB`. Take `⟨a, ha, A, hA, rfl⟩` from `hB`. Conclude with `Submodule.subset_span ⟨a, ha, M • A, homL_nsmul_mem M hM hA, smul_comm _ _ _⟩`. Consider the case `zero => simp`.

Consider the case `add A B _ _ hA hB => rw [smul_add]`. Conclude with `add_mem hA hB`. Consider the case `smul c A _ hA => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ c hA`.
-/
theorem YYl_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L₁) : M • A ∈ YYl D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M • A, homL_nsmul_mem M hM hA, smul_comm _ _ _⟩
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨w, hw, A, hA, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨w, hw, M • A, YYl_nsmul_mem M hM hA, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i j`.

Simplify using `only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem La_nsmul_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L₁) : M • x ∈ La D (tor0 D cc δ) L L₂ := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨w, hw, M • A, YYl_nsmul_mem M hM hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Use `⟨Ideal.absNorm (D.host.conj • 𝔫), Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h), fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢`. Introduce `i`. Rewrite using `[Pi.smul_apply]`. Establish `hyi` using `hy i`.

Rewrite `hyi` using `[FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using h)]`. Establish `hmem` using `hyi (algebraMap (𝓞 D.host.E) D.host.E (Ideal.absNorm (D.host.conj • 𝔫) : 𝓞 D.host.E)) ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem _, rfl⟩)`. Take `⟨x', -, hx'⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hmem`. Rewrite using `[Submodule.mem_one]`. Use `⟨x', ?_⟩` and prove the remaining obligations.

Rewrite using `[hx', nsmul_eq_mul, mul_comm, map_natCast]`.
-/
theorem skewLat_nsmul_le (𝔫 : Ideal (𝓞 D.host.E)) (h : D.host.conj • 𝔫 ≠ ⊥) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ skewLat D 𝔫 N, M • y ∈ stdL D N := by
  refine ⟨Ideal.absNorm (D.host.conj • 𝔫), Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h),
    fun y hy => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  rw [Pi.smul_apply]
  have hyi := hy i
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero
    (by simpa using h)] at hyi
  have hmem := hyi (algebraMap (𝓞 D.host.E) D.host.E (Ideal.absNorm (D.host.conj • 𝔫) : 𝓞 D.host.E))
    ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem _, rfl⟩)
  obtain ⟨x', -, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  rw [Submodule.mem_one]
  refine ⟨x', ?_⟩
  rw [hx', nsmul_eq_mul, mul_comm, map_natCast]

end GlobalTheory.BotPairSmall.CosetTheta

namespace GlobalTheory.BotPairSmall.CosetTheta

/- English proof (translation)
Establish `hlc` using `GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d`. Use `set T := tor0 D ⊤ δ`. Use `set A := La0 D T a d`. Establish `h0 : (0 : VC D a d → ℂ) ∈ TT D T a d`. Use `hlc.2.2.2 0 e0 heT` as an intermediate fact.

Rewrite `this` using `[zero_smul]`. Then use the resulting hypothesis. Distinguish the cases in `hfin : Finite (B ⧸ A.addSubgroupOf B)`. Use `haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)`. Establish `e : Iop D T A B e0 = ∑ q : B ⧸ A.addSubgroupOf B, ((((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * al D T ((Quotient.out q : B) : VC D a d) * (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) e0)`. Use function extensionality and compare the values at `z`.

Simplify using `only [Iop, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Wd]`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `: wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0` using `by simp [wdPh, ee, Complex.exp_ne_zero]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Use `Finset.sum_induction _ (· ∈ TT D T a d) (fun F G hF hG => hlc.2.2.1 F hF G hG) h0 fun q _ => ?_` and prove the remaining obligations. Conclude with `hlc.2.2.2 _ _ (GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT hc hM (hB _ (Quotient.out q : B).2) heT)`. Establish `hi : (A.addSubgroupOf B).index = 0` using `AddSubgroup.index_eq_zero_iff_infinite.2 (not_finite_iff_infinite.1 hfin)`. Establish `e : Iop D T A B e0 = 0`.

Use function extensionality and compare the values at `z`. Simplify using `[Iop, hi]`. Rewrite using `[e]`. Conclude with `h0`.
-/
theorem iop_mem_TT {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {B : AddSubgroup (VC D a d)} {M : ℕ} (hM : 0 < M)
    (hB : ∀ x ∈ B, M • x ∈ La0 D (tor0 D ⊤ δ) a d) {e0 : VC D a d → ℂ} (heT : e0 ∈ TT D (tor0 D ⊤ δ) a d) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) B e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  set T := tor0 D ⊤ δ
  set A := La0 D T a d
  have h0 : (0 : VC D a d → ℂ) ∈ TT D T a d := by
    have := hlc.2.2.2 0 e0 heT
    rwa [zero_smul] at this
  by_cases hfin : Finite (B ⧸ A.addSubgroupOf B)
  · haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    have e : Iop D T A B e0 = ∑ q : B ⧸ A.addSubgroupOf B,
        ((((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) e0) := by
      funext z
      simp only [Iop, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Wd]
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
      field_simp
    rw [e]
    refine Finset.sum_induction _ (· ∈ TT D T a d) (fun F G hF hG => hlc.2.2.1 F hF G hG) h0 fun q _ => ?_
    exact hlc.2.2.2 _ _ (GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT hc hM (hB _ (Quotient.out q : B).2) heT)
  · have hi : (A.addSubgroupOf B).index = 0 :=
      AddSubgroup.index_eq_zero_iff_infinite.2 (not_finite_iff_infinite.1 hfin)
    have e : Iop D T A B e0 = 0 := by
      funext z
      simp [Iop, hi]
    rw [e]; exact h0

end GlobalTheory.BotPairSmall.CosetTheta

/- English proof (translation)
Introduce `D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho`. Establish `hlc` using `GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d`. Establish `s0` using `VacMove.sd_of_moves (VacMove.moves_one D a)`. Establish `s0'` using `VacMove.sd_of_moves (VacMove.moves_one D d)`. Establish `heT : e0 ∈ TT D (tor0 D ⊤ δ) a d` using `hlc.1 _ _ s0 s0' e0 hv.1`.

Establish `hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥` using `GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)`. Take `⟨M, hM, hMs⟩` from `GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d`. Establish `hI` using `GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT`. Unfold `GlobalTheory.BotPairSmall.cvec`. Conclude with `hlc.2.2.2 _ _ (hlc.2.1 _ _ hI)`.
-/
theorem GlobalTheory.BotPairSmall.cvec_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  have hI := GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
  unfold GlobalTheory.BotPairSmall.cvec
  exact hlc.2.2.2 _ _ (hlc.2.1 _ _ hI)
