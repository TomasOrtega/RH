import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal

namespace GlobalTheory.GenModel

/- English proof (translation)
Use `choose Mi Li mi hIi using h`. Take `⟨P, π, hπ⟩` from `GlobalTheory.Member.DomFin.exists_dominating_fintype F Y (Mi (Classical.arbitrary ι)) ι Mi`. Take `⟨Q, ρ, -, hQ, hρ, -, hρj, -⟩` from `GlobalTheory.ModelDom.exists_normal_dominating F Y P P`. Establish `hE : 0 < ∏ i, (mi i : ℕ)` using `Finset.prod_pos fun i _ => (mi i).pos`. Set `m : ℕ+` to `⟨∏ i, (mi i : ℕ), hE⟩`.

Establish `hdiv : ∀ i, (mi i : ℕ) ∣ ∏ i, (mi i : ℕ)` using `fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Set `e : ι → ℕ+` to `fun i => ⟨(∏ i, (mi i : ℕ)) / mi i, Nat.div_pos (Nat.le_of_dvd hE (hdiv i)) (mi i).pos⟩`. Establish `hme : ∀ i, mi i * e i = m` using `fun i => PNat.eq (by rw [PNat.mul_coe, PNat.mk_coe]; exact Nat.mul_div_cancel' (hdiv i))`. Use `⟨Q, hQ, fun i => (((Li i).pull (π i) (hπ i).1).pull ρ hρ).pow (e i), m, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.T.induced_metric_pow _ _ _ _ Q _ (mi i) (e i) 0 (GlobalTheory.T.induced_metric_pullback _ _ _ _ P Q ρ hρ hρj _ (mi i) 0 (GlobalTheory.T.induced_metric_pullback _ _ _ _ (Mi i) P (π i) (hπ i).1 (hπ i).2 (Li i) (mi i) 0 (hIi i)))`.

Rewrite `h1` using `[hme i]`. Then use the resulting hypothesis.
-/
theorem exists_normal_common {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {ι : Type} [Fintype ι]
    [Nonempty ι] (A : ι → Adl C Y)
    (h : ∀ i, ∃ (M : TrueGeo.Model Y) (L : HermLB M.p) (m : ℕ+), (A i).Induced M L m 0) :
    ∃ (M : TrueGeo.Model Y) (_ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (L : ι → HermLB M.p) (m : ℕ+),
      ∀ i, (A i).Induced M (L i) m 0 := by
  classical
  choose Mi Li mi hIi using h
  obtain ⟨P, π, hπ⟩ := GlobalTheory.Member.DomFin.exists_dominating_fintype F Y (Mi (Classical.arbitrary ι)) ι Mi
  obtain ⟨Q, ρ, -, hQ, hρ, -, hρj, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y P P
  have hE : 0 < ∏ i, (mi i : ℕ) := Finset.prod_pos fun i _ => (mi i).pos
  let m : ℕ+ := ⟨∏ i, (mi i : ℕ), hE⟩
  have hdiv : ∀ i, (mi i : ℕ) ∣ ∏ i, (mi i : ℕ) := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let e : ι → ℕ+ := fun i => ⟨(∏ i, (mi i : ℕ)) / mi i, Nat.div_pos (Nat.le_of_dvd hE (hdiv i)) (mi i).pos⟩
  have hme : ∀ i, mi i * e i = m := fun i =>
    PNat.eq (by rw [PNat.mul_coe, PNat.mk_coe]; exact Nat.mul_div_cancel' (hdiv i))
  refine ⟨Q, hQ, fun i => (((Li i).pull (π i) (hπ i).1).pull ρ hρ).pow (e i), m, fun i => ?_⟩
  have h1 := GlobalTheory.T.induced_metric_pow _ _ _ _ Q _ (mi i) (e i) 0
    (GlobalTheory.T.induced_metric_pullback _ _ _ _ P Q ρ hρ hρj _ (mi i) 0
      (GlobalTheory.T.induced_metric_pullback _ _ _ _ (Mi i) P (π i) (hπ i).1 (hπ i).2 (Li i) (mi i) 0 (hIi i)))
  rwa [hme i] at h1

/- English proof (translation)
Take `⟨M, L, m, r, hL, hP, hfin⟩` from `GlobalTheory.T.exists_model_presenting_divisor HTBound.htBound D A N j S κ s Φ (admEx S κ) k w hw`. Apply the tactic sequence `obtain ⟨L', hL'⟩ := GlobalTheory.TrueGeo.ModelMetric.exists_hermLB_induced D.what₂.LL (Φ.C k).Y (adlOf (Φ.C k) (fun _ => refMet x Φ k) w) M L hL m r hP rfl (fun σ => (GlobalTheory.T.family_metrics_smooth D A N j S κ s x Φ k σ (expo S.Dw w)).2.1) (fun σ σ' p p' a hp hpa => (Global …`. Conclude with `⟨M, L', m, hL'⟩`.
-/
theorem induced_refMet {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (Φ : s.Flag) (k : s.Comp) (w : Sym D.host.E →₀ ℤ) (hw : ∀ a ∈ w.support, {q | a.1 q = true}.Finite) :
    ∃ (M : TrueGeo.Model (Φ.C k).Y) (L : HermLB M.p) (m : ℕ+),
      (adlOf (Φ.C k) (fun _ => refMet x Φ k) w).Induced M L m 0 := by
  obtain ⟨M, L, m, r, hL, hP, hfin⟩ :=
    GlobalTheory.T.exists_model_presenting_divisor HTBound.htBound D A N j S κ s Φ (admEx S κ) k w hw
  obtain ⟨L', hL'⟩ := GlobalTheory.TrueGeo.ModelMetric.exists_hermLB_induced D.what₂.LL (Φ.C k).Y
    (adlOf (Φ.C k) (fun _ => refMet x Φ k) w) M L hL m r hP rfl
    (fun σ => (GlobalTheory.T.family_metrics_smooth D A N j S κ s x Φ k σ (expo S.Dw w)).2.1)
    (fun σ σ' p p' a hp hpa => (GlobalTheory.T.metric_conjugation_symmetry D A N j S κ s x Φ k σ σ' (expo S.Dw w) p p' a hp hpa).2.1)
    hfin
  exact ⟨M, L', m, hL'⟩

/- English proof (translation)
Introduce `D O hO B _ c`. Take `⟨x, P, h⟩` from `hO`. Use `exists_normal_common (fun o : Option (DV.Rt D.what₂.Tau O.N) => o.elim (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))) ?_` and prove the remaining obligations. Introduce and unpack `(_ | y)`. Take `⟨M, L, q, hi, -⟩` from `P.ab_model c`.

Conclude with `⟨M, L, q, h.ab_eq ▸ hi⟩`. Express the relevant statement in the definitionally equal form `∃ (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (m : ℕ+), (adlOf (O.Φ.C c) (fun _ => O.met.h0 c) _).Induced M L m 0`. Rewrite using `[h.h0_eq]`. Use `induced_refMet x O.Φ c _ fun a ha => ?_` and prove the remaining obligations. Establish `ha1 : a.1 = ArIn.ind (FlagAr.setB O.Y B)`.

Unfold `rootSym at ha`. Apply the tactic sequence `split_ifs at ha <;> rw [Finset.mem_singleton.1 (Finsupp.support_single_subset ha)]`. Rewrite using `[ha1]`. Use `(FlagAr.setB O.Y B).finite_toSet.subset fun q hq => ?_` and prove the remaining obligations. Simplify `hq` using `[ArIn.ind]`.
-/
theorem exists_normal_model : ∀ (D : D7) (O : Setup D), O.Core → ∀ (B : ℝ), 2 ≤ B → ∀ c : O.s.Comp, ∃ (M : TrueGeo.Model (O.var c)) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (L : Option (DV.Rt D.what₂.Tau O.N) → HermLB M.p) (m : ℕ+), ∀ o : Option (DV.Rt D.what₂.Tau O.N), (o.elim (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))).Induced M (L o) m 0 := by
  intro D O hO B _ c
  obtain ⟨x, P, h⟩ := hO
  classical
  refine exists_normal_common
    (fun o : Option (DV.Rt D.what₂.Tau O.N) => o.elim (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))) ?_
  rintro (_ | y)
  · obtain ⟨M, L, q, hi, -⟩ := P.ab_model c
    exact ⟨M, L, q, h.ab_eq ▸ hi⟩
  · change ∃ (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (m : ℕ+),
      (adlOf (O.Φ.C c) (fun _ => O.met.h0 c) _).Induced M L m 0
    rw [h.h0_eq]
    refine induced_refMet x O.Φ c _ fun a ha => ?_
    have ha1 : a.1 = ArIn.ind (FlagAr.setB O.Y B) := by
      unfold rootSym at ha
      split_ifs at ha <;> rw [Finset.mem_singleton.1 (Finsupp.support_single_subset ha)]
    rw [ha1]
    refine (FlagAr.setB O.Y B).finite_toSet.subset fun q hq => ?_
    simpa [ArIn.ind] using hq

end GlobalTheory.GenModel
