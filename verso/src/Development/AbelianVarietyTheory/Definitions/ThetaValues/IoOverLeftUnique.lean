import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecBCIffSecBCTest

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.FieldBCModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map evR_map hasBC_of)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l}

/- English proof (translation)
The claim follows from `Algebra.algebra_ext _ _ fun a => (h a).symm`.
-/
theorem alg_eq (hle : c.F ≤ c'.F) (S : Type) [CommRing S] [i : Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) : i = resAlg hle S :=
  Algebra.algebra_ext _ _ fun a => (h a).symm

/- English proof (translation)
Take `rfl` from `alg_eq hle S h`. Both sides reduce to the same expression.
-/
theorem nabBC_apply (hle : c.F ≤ c'.F) (nab : NabV Xo c) {S : Type} [CommRing S] [i : Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (k : ℤ) (F) (α) :
    nabBC hle nab y k F α = nab (y.res hle h) k F α := by
  obtain rfl := alg_eq hle S h
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `S _ i y k F α`. Conclude with `nabBC_apply (le_refl _) nab (i := i) (fun _ => rfl) y k F α`.
-/
theorem nabBC_self (nab : NabV Xo c) : (nabBC (le_refl c.F) nab : NabV Xo c) = (nab : NabV Xo c) := by
  funext S _ i y k F α
  exact nabBC_apply (le_refl _) nab (i := i) (fun _ => rfl) y k F α

/- English proof (translation)
Take `rfl` from `alg_eq hle p.R h`. Both sides reduce to the same expression.
-/
theorem rulBC_apply (hle : c.F ≤ c'.F) (f : Rul Xo c) (p : TRing c'.F) [i : Algebra c.F p.R]
    (h : AlgOver c c' hle p.R) (y : FrPt Xo c' p.R) : rulBC hle f p y = evR Xo c f (y.res hle h) := by
  obtain rfl := alg_eq hle p.R h
  rfl

/- English proof (translation)
The claim follows from `evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c))`.
-/
theorem wd (c : Coeff l) : ValueWD Xo c :=
  evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c))

/- English proof (translation)
Establish `: IsReduced p.R` using `(Ideal.isRadical_iff_quotient_reduced _).1 p.rad`. Conclude with `GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c p.R _`.
-/
theorem fromT_res (hle : c.F ≤ c'.F) (p : TRing c'.F) [Algebra c.F p.R]
    (h : AlgOver c c' hle p.R) (y : FrPt Xo c' p.R) : FromT (y.res hle h) := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  exact GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c p.R _

/- English proof (translation)
Use function extensionality and compare the values at `p y`. Use `letI := resAlg hle p.R`. Conclude with `evalAt_one _ _ _ (fromT_res hle p (fun _ => rfl) y)`.
-/
theorem rulBC_one (hle : c.F ≤ c'.F) : rulBC hle (1 : Rul Xo c) = 1 := by
  funext p y
  letI := resAlg hle p.R
  exact evalAt_one _ _ _ (fromT_res hle p (fun _ => rfl) y)

/- English proof (translation)
Use function extensionality and compare the values at `p y`. Rewrite using `[rulBC_apply (le_refl _) f p (fun _ => rfl) y]`. Conclude with `evR_test hf p y`.
-/
theorem rulBC_self {f : Rul Xo c} (hf : Natural c f) : rulBC (le_refl c.F) f = f := by
  funext p y
  rw [rulBC_apply (le_refl _) f p (fun _ => rfl) y]
  exact evR_test hf p y

/- English proof (translation)
Introduce `p q φ y z h`. Use `letI := resAlg hle p.R`. Use `letI := resAlg hle q.R`. Conclude with `evR_map (wd c) hf (fromT_res hle p (fun _ => rfl) y) ((GlobalTheory.SecFieldCompare.frMap_res_iff hle (fun _ => rfl) (fun _ => rfl) φ y z).2 h)`.
-/
theorem rulBC_natural (hle : c.F ≤ c'.F) {f : Rul Xo c} (hf : Natural c f) : Natural c' (rulBC hle f) := by
  intro p q φ y z h
  letI := resAlg hle p.R
  letI := resAlg hle q.R
  exact evR_map (wd c) hf (fromT_res hle p (fun _ => rfl) y)
    ((GlobalTheory.SecFieldCompare.frMap_res_iff hle (fun _ => rfl) (fun _ => rfl) φ y z).2 h)

/- English proof (translation)
Distinguish the cases in `hy : FromT y`. Take `⟨q, φ, y₀, h₀, e⟩` from `evR_spec hy`. Use `letI := resAlg hle q.R`. Rewrite using `[e, evR_map (wd c) hf (fromT_res hle q (fun _ => rfl) y₀) ((GlobalTheory.SecFieldCompare.frMap_res_iff hle (fun _ => rfl) h φ y₀ y).2 h₀)]`. Both sides reduce to the same expression.

Rewrite using `[evR_not hy, evR_not fun h' => hy (GlobalTheory.SecFieldCompare.fromT_of_res hle (hasBC_of GlobalTheory.abelianSchemeLaws_all.1.secBaseChange) h y h')]`.
-/
theorem evR_rulBC (hle : c.F ≤ c'.F) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) :
    evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h) := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, h₀, e⟩ := evR_spec hy
    letI := resAlg hle q.R
    rw [e, evR_map (wd c) hf (fromT_res hle q (fun _ => rfl) y₀)
      ((GlobalTheory.SecFieldCompare.frMap_res_iff hle (fun _ => rfl) h φ y₀ y).2 h₀)]
    rfl
  · rw [evR_not hy, evR_not fun h' => hy (GlobalTheory.SecFieldCompare.fromT_of_res hle
      (hasBC_of GlobalTheory.abelianSchemeLaws_all.1.secBaseChange) h y h')]

/- English proof (translation)
Introduce `S _ _ _ h y`. Simplify using `[evR_rulBC hle hf h y]`.
-/
theorem isBC_rulBC (hle : c.F ≤ c'.F) {f : Rul Xo c} (hf : Natural c f) : IsBC hle (rulBC hle f) ![1] ![f] := by
  intro S _ _ _ h y
  simp [evR_rulBC hle hf h y]

/- English proof (translation)
Use `⟨rulBC_natural hle hf.1, fun p t y y' h => ?_⟩` and prove the remaining obligations. Use `letI := resAlg hle p.R`. Conclude with `wtAll_of_borChart (borChartF_of_cover (GlobalTheory.Frames.chartCoverF_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c)) (ex Dw a n) hf.1 hf.2 _ _ _ _ (fromT_res hle p (fun _ => rfl) y) (fromT_res hle p (fun _ => rfl) y') h`.
-/
theorem rulBC_mem_sec (hle : c.F ≤ c'.F) {a} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    rulBC hle f ∈ sec Xo c' a n := by
  refine ⟨rulBC_natural hle hf.1, fun p t y y' h => ?_⟩
  letI := resAlg hle p.R
  exact wtAll_of_borChart (borChartF_of_cover (GlobalTheory.Frames.chartCoverF_of_secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c)) (ex Dw a n) hf.1 hf.2 _ _ _ _
    (fromT_res hle p (fun _ => rfl) y) (fromT_res hle p (fun _ => rfl) y') h

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem frOver_iff (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) {k : Type} [CommRing k]
    [Algebra c.F k] [Algebra d.c₂.F k] [Algebra c'.F k] [i₂ : Algebra (covCoeff hle d).F k]
    (h : AlgOver c c' hle k) (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k)
    (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (y : FrPt Xo c' k) :
    @FrOver E _ _ _ H Dw l Xo c' n (ddBC hle d) k _ _ i₂ y₂ y ↔
      FrOver d (y₂.res (le_covCoeff hle d) h₂) (y.res hle h) := Iff.rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((zetaM c' ^ pairL (l := l) x0 (fun b => levRep (q b)) * incF c c' hle (d.φδ q) : c'.F) : ℂ) = ((zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) * d.φδ q : c.F) : ℂ)`. Establish `: zetaM c' = incF c c' hle (zetaM c)` using `by unfold zetaM; rw [map_pow]; rfl`. Rewrite using `[this, ← map_zpow₀, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem w_ddBC (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂) :
    (ddBC hle d).w x0 q = incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (d.w x0 q) := by
  apply Subtype.ext
  show ((zetaM c' ^ pairL (l := l) x0 (fun b => levRep (q b)) * incF c c' hle (d.φδ q) : c'.F) : ℂ) =
    ((zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) * d.φδ q : c.F) : ℂ)
  have : zetaM c' = incF c c' hle (zetaM c) := by unfold zetaM; rw [map_pow]; rfl
  rw [this, ← map_zpow₀, ← map_mul]
  rfl

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩` from `hd`. Use `⟨h1, h2, h3, h4, h5, h6, ?_, rulBC_mem_sec (le_covCoeff hle d) h8, ?_⟩` and prove the remaining obligations. Introduce `k _ _ i i₂ hi y`. Use `letI i₂' : Algebra (covCoeff hle d).F k := i₂`. Use `letI := resAlg hle k`.

Use `letI := resAlg (le_covCoeff hle d) k`. Take `⟨y₂, hy₂⟩` from `h7 k (fun a => hi (incF c c' hle a)) (y.res hle fun _ => rfl)`. Conclude with `⟨y₂.ext (le_covCoeff hle d) (fun _ => rfl), hy₂⟩`. Introduce `k _ _ i₂ y₂`. Use `letI i₂' : Algebra (covCoeff hle d).F k := i₂`.

Use `letI := resAlg (le_covCoeff hle d) k`. Establish `e` using `evR_rulBC (le_covCoeff hle d) h8.1 (S := k) (fun _ => rfl) y₂`. Conclude with `fun h0 => h9 k _ (e.symm.trans h0)`.
-/
theorem isLev_ddBC (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) : (ddBC hle d).IsLev := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hd
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, rulBC_mem_sec (le_covCoeff hle d) h8, ?_⟩
  · intro k _ _ i i₂ hi y
    letI i₂' : Algebra (covCoeff hle d).F k := i₂
    letI := resAlg hle k
    letI := resAlg (le_covCoeff hle d) k
    obtain ⟨y₂, hy₂⟩ := h7 k (fun a => hi (incF c c' hle a)) (y.res hle fun _ => rfl)
    exact ⟨y₂.ext (le_covCoeff hle d) (fun _ => rfl), hy₂⟩
  · intro k _ _ i₂ y₂
    letI i₂' : Algebra (covCoeff hle d).F k := i₂
    letI := resAlg (le_covCoeff hle d) k
    have e := evR_rulBC (le_covCoeff hle d) h8.1 (S := k) (fun _ => rfl) y₂
    exact fun h0 => h9 k _ (e.symm.trans h0)

/- English proof (translation)
Introduce `v v' h`. Use `show MvPolynomial.rename g (v' : Formalism.L2.DIV.Pol c'.F Ix n) = MvPolynomial.map _ (MvPolynomial.rename g (v : Formalism.L2.DIV.Pol c.F Ix n))`. Rewrite using `[h, MvPolynomial.map_rename]`.
-/
theorem ioOver_rename (hle : c.F ≤ c'.F) {n : ℕ} {Ix : Type} [Fintype Ix] (lam : Ix → Formalism.BasicNotions.DomWeight n)
    (g : Ix × Fin n × Fin n → LtN Dw n) :
    IoOver hle lam ((MvPolynomial.rename g).toLinearMap ∘ₗ (Formalism.L2.DIV.VV c.F lam).subtype)
      ((MvPolynomial.rename g).toLinearMap ∘ₗ (Formalism.L2.DIV.VV c'.F lam).subtype) := by
  intro v v' h
  show MvPolynomial.rename g (v' : Formalism.L2.DIV.Pol c'.F Ix n) = MvPolynomial.map _ (MvPolynomial.rename g (v : Formalism.L2.DIV.Pol c.F Ix n))
  rw [h, MvPolynomial.map_rename]

/- English proof (translation)
Establish `e : incF c c (le_refl _) = RingHom.id _` using `RingHom.ext fun _ => rfl`. Unfold `IoOver`. Rewrite using `[e]`. Simplify using `only [MvPolynomial.map_id]`. Conclude with `⟨fun h => LinearMap.ext fun v => h v v rfl, fun h v v' hv => by rw [h, Subtype.ext hv]⟩`.
-/
theorem ioOver_self {n : ℕ} {Ix : Type} [Fintype Ix] (lam : Ix → Formalism.BasicNotions.DomWeight n)
    (io io' : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : IoOver (le_refl c.F) lam io io' ↔ io' = io := by
  have e : incF c c (le_refl _) = RingHom.id _ := RingHom.ext fun _ => rfl
  unfold IoOver
  rw [e]
  simp only [MvPolynomial.map_id]
  exact ⟨fun h => LinearMap.ext fun v => h v v rfl, fun h v v' hv => by rw [h, Subtype.ext hv]⟩

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢`. Use `⟨fun d hd => hf.1 fun h0 => hd (by rw [MvPolynomial.coeff_map, h0, map_zero]), fun a b hab => ?_⟩` and prove the remaining obligations. Establish `e : ∀ g : MvPolynomial (Fin r × Fin n) K, Formalism.GradedWeylDivisibility.colAddGen K' a b (MvPolynomial.map φ g) = MvPolynomial.map φ (Formalism.GradedWeylDivisibility.colAddGen K a b g)`. Introduce `g`.

Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C x => simp [Formalism.GradedWeylDivisibility.colAddGen]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, hp]`.

Use `congr 1`. Simplify using `only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.map_X, MvPolynomial.aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e, hf.2 a b hab, MvPolynomial.map_rename]`.
-/
theorem map_mem_dualWeyl {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {r n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin r × Fin n) K} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) :
    MvPolynomial.map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨fun d hd => hf.1 fun h0 => hd (by rw [MvPolynomial.coeff_map, h0, map_zero]), fun a b hab => ?_⟩
  have e : ∀ g : MvPolynomial (Fin r × Fin n) K, Formalism.GradedWeylDivisibility.colAddGen K' a b (MvPolynomial.map φ g) =
      MvPolynomial.map φ (Formalism.GradedWeylDivisibility.colAddGen K a b g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C x => simp [Formalism.GradedWeylDivisibility.colAddGen]
    | add p q hp hq => simp [hp, hq]
    | mul_X p v hp =>
      rw [map_mul, map_mul, map_mul, map_mul, hp]
      congr 1
      simp only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.map_X, MvPolynomial.aeval_X]
      split_ifs <;> simp
  rw [e, hf.2 a b hab, MvPolynomial.map_rename]

/- English proof (translation)
Take `⟨v, hv⟩` from `v`. Use `⟨⟨_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show MvPolynomial.map (incF c c' hle) v ∈ Formalism.L2.DIV.VV c'.F lam`. Unfold `Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hv ⊢`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨fun s => MvPolynomial.map (incF c c' hle) (F s), fun s => map_mem_dualWeyl _ _ (hF s), ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => MvPolynomial.map_rename _ _ _`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem exists_over (hle : c.F ≤ c'.F) {n : ℕ} {Ix : Type} [Fintype Ix] (lam : Ix → Formalism.BasicNotions.DomWeight n)
    (v : VVc c lam) : ∃ v' : VVc c' lam,
      (v' : Formalism.L2.DIV.Pol c'.F Ix n) = MvPolynomial.map (incF c c' hle) (v : Formalism.L2.DIV.Pol c.F Ix n) := by
  obtain ⟨v, hv⟩ := v
  refine ⟨⟨_, ?_⟩, rfl⟩
  show MvPolynomial.map (incF c c' hle) v ∈ Formalism.L2.DIV.VV c'.F lam
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map (incF c c' hle) (F s), fun s => map_mem_dualWeyl _ _ (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => MvPolynomial.map_rename _ _ _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨v', hv⟩` from `exists_over hle lam v`. Conclude with `MvPolynomial.map_injective _ (incF c c' hle).injective ((h₁ v v' hv).symm.trans (h₂ v v' hv))`.
-/
theorem ioOver_left_unique (hle : c.F ≤ c'.F) {n : ℕ} {Ix : Type} [Fintype Ix] (lam : Ix → Formalism.BasicNotions.DomWeight n)
    {io₁ io₂ : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F} {io' : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    (h₁ : IoOver hle lam io₁ io') (h₂ : IoOver hle lam io₂ io') : io₁ = io₂ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨v', hv⟩ := exists_over hle lam v
  exact MvPolynomial.map_injective _ (incF c c' hle).injective ((h₁ v v' hv).symm.trans (h₂ v v' hv))

/- English proof (translation)
Use `⟨h.1, fun S _ _ _ y => ?_⟩` and prove the remaining obligations. Use `letI := resAlg hle S`. Take `⟨C, h1, h2⟩` from `h.2 S (y.res hle fun _ => rfl)`. Conclude with `⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h, ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩, ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩`.
-/
theorem isNab_nabBC [StarRing (𝓞 E)] (hle : c.F ≤ c'.F) (nab : NabV Xo c) (h : IsNab Xo c nab) :
    IsNab Xo c' (nabBC hle nab) := by
  refine ⟨h.1, fun S _ _ _ y => ?_⟩
  letI := resAlg hle S
  obtain ⟨C, h1, h2⟩ := h.2 S (y.res hle fun _ => rfl)
  exact ⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩,
    ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩

end GlobalTheory.FieldBCModel
