import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStagePeterssonValueRealLevelTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ZetaNeProof

variable {D : D7}

/- English proof (translation)
Establish `hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one]`. Establish `hv : p.ω (b * κ, 1) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.ω (b, 1) (p.pt φ)`. Rewrite using `[hmul, Module.End.mul_apply, hlaw κ hκ, map_smul]`. Unfold `coefW`.

Rewrite using `[hv, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    coefW p.ω m X (p.pt φ) (b * κ) = Lev.levChi s.V s.β s.L κ * coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ, map_smul]
  unfold coefW
  rw [hv, ← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs`. Establish `hκf : κ ∈ GfC s.V` using `(Subgroup.mem_inf.mp hκ).1`. Unfold `hgtS`. Establish `hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) = GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)`. Introduce `w`.

Rewrite using `[map_mul, h2 κ hκf w, mul_one]`. Establish `hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1`. Introduce `v _`. Rewrite using `[map_mul, h3 b b.2 v, one_mul]`. Conclude with `h1 v _ (hstab κ hκ v)`.

Simplify using `only [hA]`. Rewrite using `[Finset.prod_eq_one hF, mul_one]`.
-/
theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ)
    (hstab : ∀ k ∈ Lev.levG s.V s.β s.L, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

/- English proof (translation)
Introduce `D hMet hLev hLaw hSupp hRZ`. Introduce `hng c hc k hk s s' hs hs' p hp m X hcov`. Take `⟨φ, v, hvK, hR⟩` from `hRZ hng c hc k hk s s' hs hs' p hp m X hcov`. Establish `hkm : k ≤ D.R.m` using `hk.le`. Take `⟨ipD, ip, hip⟩` from `hMet c hc k hkm s hs`.

Take `⟨_, _, hLF3, _, _, hLF6⟩` from `hLev c hc k hkm s hs`. Take `⟨hmOff, _, hAsub, _, mR, hmR, hint⟩` from `GlobalTheory.T.pushforward_haar_realPoints_times_level D hLev c hc k hkm s hs`. Establish `hpet` using `GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate D c hc k hkm s hs ipD ip hip`. Establish `hlaw` using `(hLaw hng c hc k hk s s' hs hs' p hp φ).1`. Establish `hsupp` using `hSupp hng c hc k hk s s' hs hs' p hp m X hcov φ`.

Take `⟨hz, hzI⟩` from `hR mR hmR`. Use `⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Establish `hipu : ip u u ≠ 0`. Introduce `h0`.

Use `hip.pos u hu` as an intermediate fact. Rewrite `this` using `[h0, Complex.zero_re]`. Conclude with `lt_irrefl _ this`. Establish `hcipu : conj (ip u u) ≠ 0` using `(map_ne_zero _).mpr hipu`. Establish `hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) = conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) * conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : …`.

Introduce `b κ hκ`. Unfold `Step.zint`. Rewrite using `[coefW_mul_lev p m X φ hlaw _ κ hκ, hpet u v b κ hκ]`. Establish `hn : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hLF6 κ hκ]`.

Evaluate the numerical expressions. Simplify using `only [map_mul]`. Take the linear combination `(conj (ip u u) * coefW p.ω m X (p.pt φ) (b : GA D s.V) * conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn`. Establish `hoff : ∀ g ∈ intOff c s \ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0`. Introduce and unpack `g ⟨hg, hgA⟩`.

Unfold `Step.zint`. Rewrite using `[hsupp g hg hgA, zero_mul]`. Establish `hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) * conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR`. Assume the negation of the conclusion as `hni`. Conclude with `hz (integral_undef hni)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]`. Rewrite using `[(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]`. Conclude with `mul_ne_zero hcipu hz`. Introduce `a hmaj hcomp`.

Take `⟨s₁, hs₁, hI⟩` from `hzI a hmaj hcomp`. Use `⟨s₁, hs₁, ?_⟩` and prove the remaining obligations. Use `IntegrableOn.of_forall_diff_eq_zero (s := {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}) ?_ hmOff ?_` and prove the remaining obligations. Use `(hint _ _ (hI.const_mul (conj (ip u u))) ?_).1` and prove the remaining obligations. Introduce `b κ hκ`.

Rewrite using `[hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hLF3 a b κ hκ, mul_assoc]`. Introduce `g hg`. Rewrite using `[hoff g hg, zero_mul]`.
-/
theorem zetaNe_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  intro D hMet hLev hLaw hSupp hRZ
  intro hng c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ hng c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ D.R.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨_, _, hLF3, _, _, hLF6⟩ := hLev c hc k hkm s hs
  obtain ⟨hmOff, _, hAsub, _, mR, hmR, hint⟩ := GlobalTheory.T.pushforward_haar_realPoints_times_level D hLev c hc k hkm s hs
  have hpet := GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate D c hc k hkm s hs ipD ip hip
  have hlaw := (hLaw hng c hc k hk s s' hs hs' p hp φ).1
  have hsupp := hSupp hng c hc k hk s s' hs hs' p hp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet u v b κ hκ]
    have hn : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hLF6 κ hκ]
      norm_num
    simp only [map_mul]
    linear_combination (conj (ip u u) * coefW p.ω m X (p.pt φ) (b : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn

  have hoff : ∀ g ∈ intOff c s \ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L},
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    rw [hsupp g hg hgA, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hLF3 a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.ChainOnto.ZetaNeProof

/- English proof (translation)
The claim follows from `GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real`.
-/
example : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D :=
  GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real
