import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ _ hc G P hT F _ _ _ N hN M _ _ ev hadd hsm hpow hsurj`. Use `letI := H.starRing`. Take `⟨f, hto, hon, heq, hfa, hfs, -⟩` from `hT F N hN`. Establish `hB` using `P.D.tau_bimult`. Establish `hG : GlobalFnsSt` using `GlobalTheory.SemiRigid.globalFns`.

Use `choose pt hpt using fun a => hon (ev a) (hpow a)`. Use `⟨pt, fun a => (hto _ _).2 (hpt a).symm, fun n z hz y => ?_⟩` and prove the remaining obligations. Establish `yadd : ∀ a b, ∃ t : P.D.toPre.X, (pt (a + b)).y = (pt a).y + (pt b).y + N • t` using `fun a b => by`. Establish `e` using `hfa _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB (pt a) (pt b))`. Rewrite `e` using `[hpt, hpt, ← hadd, ← hpt]`.

Take `⟨t, ht, -⟩` from `(heq _ _).1 e`. Conclude with `⟨t, ht⟩`. Establish `ysm : ∀ (o : 𝓞 E) a, ∃ t : P.D.toPre.X, (pt (o • a)).y = o • (pt a).y + N • t` using `fun o a => by`. Establish `e` using `hfs _ _ _ (GlobalTheory.TorusExt.qkAct_qkSmul hB hG P.oD o (pt a))`. Rewrite `e` using `[hpt, ← hsm, ← hpt]`.

Take `⟨t, ht, -⟩` from `(heq _ _).1 e`. Conclude with `⟨t, ht⟩`. Establish `key : ∀ m ∈ Submodule.span (𝓞 E) (Set.range z), ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, (pt m).y = u + N • t`. Introduce `m hm`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Conclude with `⟨_, Submodule.subset_span ⟨b, rfl⟩, 0, by rw [smul_zero, add_zero]⟩`. Consider the case `zero`. Take `⟨t, ht⟩` from `ysm 0 0`.

Rewrite `ht` using `[zero_smul, zero_smul]`. Conclude with `⟨0, Submodule.zero_mem _, t, ht⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨u, hu, t, ht⟩` from `ha`. Take `⟨u', hu', t', ht'⟩` from `hb`.

Take `⟨s, hs⟩` from `yadd a b`. Conclude with `⟨u + u', Submodule.add_mem _ hu hu', t + t' + s, by`. Rewrite using `[hs, ht, ht', smul_add, smul_add]`. Use the proof step `abel⟩`. Consider the case `smul o a _ ha`.

Take `⟨u, hu, t, ht⟩` from `ha`. Take `⟨s, hs⟩` from `ysm o a`. Conclude with `⟨o • u, Submodule.smul_mem _ o hu, o • t + s, by`. Rewrite using `[hs, ht, smul_add, smul_add, smul_comm o N t, add_assoc]⟩`. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hc⟩`.

Use `letI := GlobalTheory.TorusExt.gtGroup P.D.toPre F`. Take `⟨g, hg⟩` from `(GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V _ hA P.D F).2.1 N hN (GlobalTheory.TorusExt.iota hB F y)`. Set `p : QkPt P.D.toPre F N` to `GlobalTheory.TorusExt.qkMk hB y g ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg).symm`. Establish `hp : f p ^ N = 1`. Take `⟨w, hw⟩` from `P.U.ext`.

Conclude with `((hto p _).2 rfl w hw).1`. Take `⟨m, hm⟩` from `hsurj _ hp`. Take `⟨s, hs, -⟩` from `(heq (pt m) p).1 ((hpt m).trans hm)`. Take `⟨u, hu, t, ht⟩` from `key m (hz ▸ Submodule.mem_top)`. Use `⟨u, hu, t + s, ?_⟩` and prove the remaining obligations.

Establish `hs' : y = (pt m).y + N • s` using `hs`. Rewrite using `[hs', ht, smul_add, add_assoc]`.
-/
theorem exists_qkPt_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  intro E _ _ _ H V _ _ _ _ hc G P hT F _ _ _ N hN M _ _ ev hadd hsm hpow hsurj
  letI := H.starRing
  obtain ⟨f, hto, hon, heq, hfa, hfs, -⟩ := hT F N hN
  have hB := P.D.tau_bimult
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  choose pt hpt using fun a => hon (ev a) (hpow a)
  refine ⟨pt, fun a => (hto _ _).2 (hpt a).symm, fun n z hz y => ?_⟩
  have yadd : ∀ a b, ∃ t : P.D.toPre.X, (pt (a + b)).y = (pt a).y + (pt b).y + N • t := fun a b => by
    have e := hfa _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB (pt a) (pt b))
    rw [hpt, hpt, ← hadd, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, ht⟩
  have ysm : ∀ (o : 𝓞 E) a, ∃ t : P.D.toPre.X, (pt (o • a)).y = o • (pt a).y + N • t := fun o a => by
    have e := hfs _ _ _ (GlobalTheory.TorusExt.qkAct_qkSmul hB hG P.oD o (pt a))
    rw [hpt, ← hsm, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, ht⟩
  have key : ∀ m ∈ Submodule.span (𝓞 E) (Set.range z),
      ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, (pt m).y = u + N • t := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨b, rfl⟩, 0, by rw [smul_zero, add_zero]⟩
    | zero =>
      obtain ⟨t, ht⟩ := ysm 0 0
      rw [zero_smul, zero_smul] at ht
      exact ⟨0, Submodule.zero_mem _, t, ht⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨u', hu', t', ht'⟩ := hb
      obtain ⟨s, hs⟩ := yadd a b
      exact ⟨u + u', Submodule.add_mem _ hu hu', t + t' + s, by
        rw [hs, ht, ht', smul_add, smul_add]; abel⟩
    | smul o a _ ha =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨s, hs⟩ := ysm o a
      exact ⟨o • u, Submodule.smul_mem _ o hu, o • t + s, by
        rw [hs, ht, smul_add, smul_add, smul_comm o N t, add_assoc]⟩
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  letI := GlobalTheory.TorusExt.gtGroup P.D.toPre F
  obtain ⟨g, hg⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V _ hA P.D F).2.1 N hN
    (GlobalTheory.TorusExt.iota hB F y)
  let p : QkPt P.D.toPre F N :=
    GlobalTheory.TorusExt.qkMk hB y g ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg).symm
  have hp : f p ^ N = 1 := by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((hto p _).2 rfl w hw).1
  obtain ⟨m, hm⟩ := hsurj _ hp
  obtain ⟨s, hs, -⟩ := (heq (pt m) p).1 ((hpt m).trans hm)
  obtain ⟨u, hu, t, ht⟩ := key m (hz ▸ Submodule.mem_top)
  refine ⟨u, hu, t + s, ?_⟩
  have hs' : y = (pt m).y + N • s := hs
  rw [hs', ht, smul_add, add_assoc]

end GlobalTheory.EtaVal
