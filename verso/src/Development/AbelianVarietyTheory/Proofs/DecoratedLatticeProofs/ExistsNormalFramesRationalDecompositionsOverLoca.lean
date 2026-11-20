import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hi : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k]`. Take `⟨η, hη, h0, h⟩` from `exists_idem p`. Establish `hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v)`. Use `⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`.

Conclude with `TensorProduct.zero_tmul _ _`. Use `Ideal.mem_iInf.2 fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Rewrite using `[h0 w.1 w.2, TensorProduct.zero_tmul]`. Use `pr_int p (hU.1 _ hm).2.2` as an intermediate fact.

Rewrite `this` using `[map_mul, pr_pair_tmul p h, map_one, map_one, mul_one]`. Then use the resulting hypothesis. Establish `h0 : D.host.xi0 ≠ 0` using `fun h => by`. Use `GlobalTheory.MixModel.HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)` as an intermediate fact. Rewrite `this` using `[h, map_zero, zero_mul]`. Establish `h2` using `congrArg p.pr this`.

Rewrite `h2` using `[map_zero, map_one]`. Conclude with `zero_ne_one h2`. Establish `a` using `(Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral p hU)`. Establish `b` using `(Valuation.mem_integer_iff _ _).1 hi`. Establish `ab : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1`.

Rewrite using `[← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one, map_one]`. Conclude with `le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm _ ≤ valuation k (p.pr (incA D D.host.xi0)) * 1 := mul_le_mul_right b _ _ = _ := mul_one _)`.
-/
theorem val_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  have hi : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
    obtain ⟨η, hη, h0, h⟩ := exists_idem p
    have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
      refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
      · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        exact TensorProduct.zero_tmul _ _
      · refine Ideal.mem_iInf.2 fun w => ?_
        change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        rw [h0 w.1 w.2, TensorProduct.zero_tmul]
    have := pr_int p (hU.1 _ hm).2.2
    rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this
  have h0 : D.host.xi0 ≠ 0 := fun h => by
    have := GlobalTheory.MixModel.HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)
    rw [h, map_zero, zero_mul] at this
    have h2 := congrArg p.pr this
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have a := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral p hU)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D D.host.xi0)) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

/- English proof (translation)
Rewrite using `[Brg.star_purely_imaginary_eq_neg, map_neg, map_neg, Valuation.map_neg, val_xi p hU]`.
-/
theorem val_star_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D (star D.host.xi0))) = 1 := by
  rw [Brg.star_purely_imaginary_eq_neg, map_neg, map_neg, Valuation.map_neg, val_xi p hU]

/- English proof (translation)
Establish `hx : ((n : ℕ) : 𝓞 D.host.E) ≠ 0` using `fun h => hn (h ▸ PP.asIdeal.zero_mem)`. Establish `h1` using `(hI.2 _ hx).not.1 hn`. Rewrite `h1` using `[not_not]`. Establish `hcast : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = (n : D.host.E)` using `by simp`. Rewrite `h1` using `[hcast]`.

Establish `hi : p.pr (incA D (n : D.host.E)⁻¹) ∈ 𝒪[k]`. Rewrite using `[p.int_iff, p.sec_pr]`. Conclude with `h1`. Establish `hn0 : (n : D.host.E) ≠ 0`. Introduce `h; apply hx; exact_mod_cast (by rw [hcast]; exact h : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = 0)`.

Establish `a : valuation k (p.pr (incA D (n : D.host.E))) ≤ 1`. Rewrite using `[map_natCast, map_natCast]`. Conclude with `(Valuation.mem_integer_iff _ _).1 (natCast_mem _ n)`. Establish `b` using `(Valuation.mem_integer_iff _ _).1 hi`. Establish `ab : valuation k (p.pr (incA D (n : D.host.E))) * valuation k (p.pr (incA D (n : D.host.E)⁻¹)) = 1`.

Rewrite using `[← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hn0, map_one, map_one, map_one]`. Conclude with `le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm _ ≤ valuation k (p.pr (incA D (n : D.host.E))) * 1 := mul_le_mul_right b _ _ = _ := mul_one _)`.
-/
theorem val_nat (p : SplitPt D k) {PP : Pl D.host.E} (hI : Formalism.L2.NTheta.IsIdemAt p.e PP) (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : valuation k (p.pr (incA D (n : D.host.E))) = 1 := by
  have hx : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hn (h ▸ PP.asIdeal.zero_mem)
  have h1 := (hI.2 _ hx).not.1 hn
  rw [not_not] at h1
  have hcast : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := by simp
  rw [hcast] at h1
  have hi : p.pr (incA D (n : D.host.E)⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact h1
  have hn0 : (n : D.host.E) ≠ 0 := by
    intro h; apply hx; exact_mod_cast (by rw [hcast]; exact h : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = 0)
  have a : valuation k (p.pr (incA D (n : D.host.E))) ≤ 1 := by
    rw [map_natCast, map_natCast]
    exact (Valuation.mem_integer_iff _ _).1 (natCast_mem _ n)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D (n : D.host.E))) * valuation k (p.pr (incA D (n : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hn0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D (n : D.host.E))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hT j h`. Establish `h3` using `congrArg (fun A => star a.ζ₀ ⬝ᵥ A *ᵥ a.ζ₀) h1`. Simplify using `only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul] at h3`. Rewrite `h3` using `[Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h2, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul]`. Rewrite using `[← h3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tau_norm {a : XGeo D} (y : YRat a) {lam : D.host.E} (hT : y.Tau lam) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    star lam * (lam * (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ)) =
      -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
  obtain ⟨h1, h2⟩ := hT j h
  have h3 := congrArg (fun A => star a.ζ₀ ⬝ᵥ A *ᵥ a.ζ₀) h1
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul] at h3
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h2, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at h3
  rw [← h3]; ring

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hx` using `val_xi q hU`. Establish `hs` using `val_star_xi q hU`. Establish `hN` using `val_nat q hI n hnP`. Introduce `ρ`. Proceed by induction on `ρ with`.

Consider the case `zero`. Introduce `j h`. Express the relevant statement in the definitionally equal form `valuation k (q.pr (incA D (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ))) = 1`. Establish `h3` using `congrArg (fun x => valuation k (q.pr (incA D x))) (tau_norm y hT j h)`. Simplify using `only [hn, map_mul, map_neg, map_pow, Valuation.map_neg, Valuation.map_pow, star_neg, star_pow, hx, hs, hN, one_pow, one_mul, mul_one] at h3`.

Conclude with `h3`. Consider the case `succ σ ih`. Introduce `j h`. Establish `h1` using `(y.lnk j σ h).norm`. Express the relevant statement in the definitionally equal form `star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ = _ at h1`.

Express the relevant statement in the definitionally equal form `valuation k (q.pr (incA D (star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))) = 1`. Rewrite using `[h1, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hx, hs, one_mul, one_mul]`. Conclude with `ih _ _`.
-/
theorem val_hz {a : XGeo D} (y : YRat a) (q : SplitPt D k) (hU : q.UnitAA) {PP : Pl D.host.E}
    (hI : Formalism.L2.NTheta.IsIdemAt q.e PP) (n : ℕ) (hT : y.Tau (-D.host.xi0 ^ (D.R.m / 2)))
    (hn : star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E)) (hnP : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    ∀ ρ j (h : j + 2 * ρ + 2 = D.R.m), valuation k ((ofSplit q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1 := by
  have hx := val_xi q hU
  have hs := val_star_xi q hU
  have hN := val_nat q hI n hnP
  intro ρ
  induction ρ with
  | zero =>
    intro j h
    change valuation k (q.pr (incA D (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ))) = 1
    have h3 := congrArg (fun x => valuation k (q.pr (incA D x))) (tau_norm y hT j h)
    simp only [hn, map_mul, map_neg, map_pow, Valuation.map_neg, Valuation.map_pow, star_neg, star_pow, hx, hs, hN,
      one_pow, one_mul, mul_one] at h3
    exact h3
  | succ σ ih =>
    intro j h
    have h1 := (y.lnk j σ h).norm
    change star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ = _ at h1
    change valuation k (q.pr (incA D (star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))) = 1
    rw [h1, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hx, hs, one_mul, one_mul]
    exact ih _ _

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

/- English proof (translation)
Introduce `D a y βT PP l n hT hn hnP`. Establish `hxi : (ofSplit l.q).xi ≠ 0` using `GlobalTheory.LocMod.Witness.xi_ne (ofSplit l.q)`. Establish `hv : valuation l.k (ofSplit l.q).xi = 1` using `val_xi l.q l.unit`. Establish `hsc : ∀ j, (ofSplit l.q).xi ^ (j / 2) ≠ 0` using `fun j => pow_ne_zero _ hxi`. Establish `hz` using `val_hz y l.q l.unit l.idem n hT hn hnP`.

Establish `hm` using `l.hs`. Take `⟨r, hr⟩` from `D.R.m_even`. Establish `key : ∀ j c (hc : j + c = l.s + 1), ∃ F : Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c), (∀ ρ h, (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) ((ofSplit l.q).xi ^ (j / 2)) (l.FX j (by omega)) F) ∧ ∀ j' (hj : j = j' + 1) ρ h, (ofSplit l.q).IsJacFrame ( …`. Introduce `j c hc`. Distinguish the cases in `hE : ∃ ρ, j + 2 * ρ + 2 = D.R.m`.

Take `⟨ρ, h⟩` from `hE`. Take `⟨F, hF⟩` from `GlobalTheory.LocMod.Witness.exists_bes (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol) (hsc j) (l.FX j (by omega))`. Take `rfl : c = 2 * ρ + 1` from `by omega`. Use `⟨F, fun ρ' h' => ?_, fun j' hj ρ' h' => absurd h' (by omega)⟩` and prove the remaining obligations. Take `rfl : ρ' = ρ` from `by omega`.

Conclude with `hF`. Establish `hE' : ∀ ρ, j + 2 * ρ + 2 ≠ D.R.m` using `fun ρ h => hE ⟨ρ, h⟩`. Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by have := hE' (r - 1); omega⟩`. Take `⟨ρ, hρ⟩ : ∃ ρ, j' + 2 * ρ + 2 = D.R.m` from `⟨(D.R.m - j' - 2) / 2, by have := hE' ((D.R.m - j' - 3) / 2); omega⟩`. Take `⟨F, hF⟩` from `GlobalTheory.LocMod.Witness.exists_jac (ofSplit l.q) ((y.jac j' ρ hρ).lev (a.x (j' + 1)).vol) (hsc j') (GlobalTheory.LocMod.Witness.hz_ne (ofSplit l.q) ((y.bes j' ρ hρ).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))`.

Take `rfl : c = 2 * ρ` from `by omega`. Use `⟨F, fun ρ' h' => absurd h' (hE' ρ'), fun j'' hj ρ' h' => ?_⟩` and prove the remaining obligations. Take `rfl : j'' = j'` from `by omega`. Take `rfl : ρ' = ρ` from `by omega`. Conclude with `hF`.

Use `⟨fun j c hc => (key j c hc).choose, fun j => (ofSplit l.q).xi ^ (j / 2), fun j => ?_, fun j => ?_, fun j ρ h => hz ρ j h, fun j ρ h c hc => (key j c hc).choose_spec.1 ρ h, fun j ρ h c hc => (key (j + 1) c hc).choose_spec.2 j rfl ρ h, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hv, one_pow]`. Use `show (ofSplit l.q).xi ^ ((j + 1 + 1) / 2) = (ofSplit l.q).xi ^ (j / 2) * (ofSplit l.q).xi`. Rewrite using `[show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ]`. Establish `h2` using `(hT l.s h).2`.

Use function extensionality and compare the values at `i`. Establish `e1 : ((y.τ l.s h).map (ofSplit l.q).pr *ᵥ fun i => (ofSplit l.q).pr (a.ζ₀ i)) i = GlobalTheory.LocMod.Witness.prH (ofSplit l.q) ((y.τ l.s h *ᵥ a.ζ₀) i)` using `(RingHom.map_mulVec (GlobalTheory.LocMod.Witness.prH (ofSplit l.q)) _ _ i).symm`. Rewrite using `[e1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_neg, map_pow]`. Express the relevant statement in the definitionally equal form `-((ofSplit l.q).xi ^ (D.R.m / 2)) * (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i) = _`. Rewrite using `[show D.R.m / 2 = l.s / 2 + 1 by omega, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem normalFrames_exist : ∀ {D : D7} (a : XGeo D) (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (n : ℕ), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) →
    star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E) → ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
    ∃ (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc := by
  intro D a y βT PP l n hT hn hnP
  have hxi : (ofSplit l.q).xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne (ofSplit l.q)
  have hv : valuation l.k (ofSplit l.q).xi = 1 := val_xi l.q l.unit
  have hsc : ∀ j, (ofSplit l.q).xi ^ (j / 2) ≠ 0 := fun j => pow_ne_zero _ hxi
  have hz := val_hz y l.q l.unit l.idem n hT hn hnP
  have hm := l.hs
  obtain ⟨r, hr⟩ := D.R.m_even
  have key : ∀ j c (hc : j + c = l.s + 1), ∃ F : Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c),
      (∀ ρ h, (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) ((ofSplit l.q).xi ^ (j / 2))
        (l.FX j (by omega)) F) ∧
      ∀ j' (hj : j = j' + 1) ρ h, (ofSplit l.q).IsJacFrame ((y.jac j' ρ h).lev (a.x (j' + 1)).vol)
        ((ofSplit l.q).xi ^ (j' / 2)) ((ofSplit l.q).hz ((y.bes j' ρ h).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
        (hj ▸ F) := by
    intro j c hc
    by_cases hE : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hE
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_bes (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol) (hsc j)
        (l.FX j (by omega))
      obtain rfl : c = 2 * ρ + 1 := by omega
      refine ⟨F, fun ρ' h' => ?_, fun j' hj ρ' h' => absurd h' (by omega)⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
    · have hE' : ∀ ρ, j + 2 * ρ + 2 ≠ D.R.m := fun ρ h => hE ⟨ρ, h⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hE' (r - 1); omega⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ, j' + 2 * ρ + 2 = D.R.m := ⟨(D.R.m - j' - 2) / 2, by have := hE' ((D.R.m - j' - 3) / 2); omega⟩
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_jac (ofSplit l.q) ((y.jac j' ρ hρ).lev (a.x (j' + 1)).vol) (hsc j')
        (GlobalTheory.LocMod.Witness.hz_ne (ofSplit l.q) ((y.bes j' ρ hρ).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
      obtain rfl : c = 2 * ρ := by omega
      refine ⟨F, fun ρ' h' => absurd h' (hE' ρ'), fun j'' hj ρ' h' => ?_⟩
      obtain rfl : j'' = j' := by omega
      obtain rfl : ρ' = ρ := by omega
      exact hF
  refine ⟨fun j c hc => (key j c hc).choose, fun j => (ofSplit l.q).xi ^ (j / 2), fun j => ?_, fun j => ?_,
    fun j ρ h => hz ρ j h, fun j ρ h c hc => (key j c hc).choose_spec.1 ρ h,
    fun j ρ h c hc => (key (j + 1) c hc).choose_spec.2 j rfl ρ h, fun h => ?_⟩
  · rw [map_pow, hv, one_pow]
  · show (ofSplit l.q).xi ^ ((j + 1 + 1) / 2) = (ofSplit l.q).xi ^ (j / 2) * (ofSplit l.q).xi
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ]
  · have h2 := (hT l.s h).2
    funext i
    have e1 : ((y.τ l.s h).map (ofSplit l.q).pr *ᵥ fun i => (ofSplit l.q).pr (a.ζ₀ i)) i =
        GlobalTheory.LocMod.Witness.prH (ofSplit l.q) ((y.τ l.s h *ᵥ a.ζ₀) i) :=
      (RingHom.map_mulVec (GlobalTheory.LocMod.Witness.prH (ofSplit l.q)) _ _ i).symm
    rw [e1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_neg, map_pow]
    change -((ofSplit l.q).xi ^ (D.R.m / 2)) * (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i) = _
    rw [show D.R.m / 2 = l.s / 2 + 1 by omega, pow_succ]
    ring

end GlobalTheory.Fam.FramesY
