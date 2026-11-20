import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.GalTwist

/- English proof (translation)
Introduce `_ D l Q χ ψ₀ _ hψ hG`. Take `⟨hker, art, ha, h⟩` from `hG`. Generalize the expression as in `hr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ₀ = r at h`. Establish `hinj : ∀ g, r g = 1 ↔ ψ₀ g = 1` using `fun g => by`. Rewrite using `[← hr, MonoidHom.comp_apply]`.

Conclude with `map_eq_one_iff _ (Units.map_injective (f := D.what₂.embLL.toMonoidHom) D.what₂.embLL.injective)`. Establish `hrker : IsOpen (r.ker : Set (G D.host.E D.nd.Om))`. Use `hker using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Conclude with `hinj g`.

Establish `hrc : Continuous r` using `GlobalTheory.HeckeGal.continuous_of_isOpen_ker' r hrker`. Establish `: Algebra.IsAlgebraic D.host.E D.nd.Om` using `IsAlgClosure.isAlgebraic`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc1, hcm, hrr, -⟩` from `GlobalTheory.Mem.HostCM.host_cm D.R D.host`. Take `⟨j, hj⟩` from `D.ntw.cc_cm.1`.

Establish `h1 : ∀ x : D.host.E, D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x)` using `fun x => by`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, hc1]`. Conclude with `(D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm`. Establish `h2 : ∀ x, D.ntw.cc (D.ntw.cc x) = x` using `fun x => j.injective (by rw [hj, hj, Complex.conj_conj])`.

Establish `hinv : ∀ x, c (c x) = x` using `fun x => (algebraMap D.host.E D.nd.Om).injective (by rw [← h1, ← h1, h2])`. Establish `hc : ∀ x : D.host.E, ∃ y : D.host.E, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y` using `fun x => ⟨c x, by rw [RingEquiv.symm_apply_eq, h1, hinv]⟩`. Use `choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv v).exists`. Establish `hbb : ∀ v, bar (bar v) = v` using `fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv (bar v)).unique (hbar _) (GlobalTheory.AntiLAdic.conjPl_symm hinv (hbar v))`. Set `T` to `(GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset`.

Establish `key : r * r.comp (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc) = 1`. Use `GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha ℂˣ _ (hrc.mul (hrc.comp (GlobalTheory.AntiLAdic.continuous_conjHom D.ntw.cc hc))) (T ∪ T.image bar) fun v hv A hA σ hσ => ?_` and prove the remaining obligations. Rewrite `hv` using `[Finset.mem_union, not_or]`. Establish `a2 : χ.UnrAt v` using `by simpa [T] using hv.1`. Establish `b2 : χ.UnrAt (bar v)`.

Assume the negation of the conclusion as `hn`. Conclude with `hv.2 (Finset.mem_image.2 ⟨bar v, by simpa [T] using hn, hbb v⟩)`. Establish `hA'` using `GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) h1 (hbar v) hA`. Establish `hσ'` using `GlobalTheory.AntiLAdic.isFrob_conjHom D.ntw.cc hc hσ`. Rewrite `hσ'` using `[← GlobalTheory.AntiLAdic.normV_conjPl (hbar v)]`.

Establish `e3` using `GlobalTheory.AntiLAdic.val_mul_val_conj c hcm.rank hcm.ne hrr χ hψ.triv (hbar v) a2 b2`. Rewrite `e3` using `[h.val_eq ha a2 hA hσ, h.val_eq ha b2 hA' hσ', ← mul_inv, inv_eq_one]`. Use `show r σ * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc σ) = 1`. Conclude with `e3`. Introduce `g g' hg`.

Establish `e : g' = GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g` using `AlgEquiv.ext hg`. Establish `k : r g * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g) = 1` using `DFunLike.congr_fun key g`. Rewrite `k` using `[← map_mul, hinj, map_mul, ← e]`. Conclude with `eq_inv_of_mul_eq_one_right k`. Introduce `v A hA`.

Rewrite using `[← not_iff_not, not_exists]`. Simplify using `only [not_and, not_not]`. Rewrite using `[Finset.mem_coe, ← hψ.ram v, h.unr_iff ha hA]`. Conclude with `forall₂_congr fun σ _ => (hinj σ).symm`. Introduce `v hv A hA σ hσ`.

Rewrite using `[← hinj]`. Establish `hcl : IsClosed ((GlobalTheory.HeckeGal.liftAb r hrc).ker : Set (Gab D.host.E D.nd.Om))` using `isClosed_singleton.preimage (GlobalTheory.HeckeGal.continuous_liftAb r hrc)`. Establish `hle : (art.comp (Neutral.B1.localIdele D.host.E v)).range ≤ (GlobalTheory.HeckeGal.liftAb r hrc).ker`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨τ, hτ⟩` from `GlobalTheory.HeckeGal.toAb_surjective (art (Neutral.B1.localIdele D.host.E v x))`.

Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, GlobalTheory.HeckeGal.liftAb_toAb, ← h _ τ hτ.symm]`. Conclude with `hψ.atl v hv x`. Establish `hm : GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ ∈ (GlobalTheory.HeckeGal.liftAb r hrc).ker`. Use `Subgroup.topologicalClosure_minimal _ hle hcl ?_` and prove the remaining obligations. Rewrite using `[ha.dec v A hA]`.

Conclude with `⟨σ, hσ, rfl⟩`. Rewrite `hm` using `[MonoidHom.mem_ker, GlobalTheory.HeckeGal.liftAb_toAb]`. Then use the resulting hypothesis.
-/
theorem galOf_twist_props : PrN → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  intro _ D l Q χ ψ₀ _ hψ hG
  classical
  obtain ⟨hker, art, ha, h⟩ := hG
  generalize hr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ₀ = r at h
  have hinj : ∀ g, r g = 1 ↔ ψ₀ g = 1 := fun g => by
    rw [← hr, MonoidHom.comp_apply]
    exact map_eq_one_iff _ (Units.map_injective (f := D.what₂.embLL.toMonoidHom) D.what₂.embLL.injective)
  have hrker : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := by
    convert hker using 1
    ext g
    exact hinj g
  have hrc : Continuous r := GlobalTheory.HeckeGal.continuous_of_isOpen_ker' r hrker
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc1, hcm, hrr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
    obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
    have h1 : ∀ x : D.host.E, D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
      apply j.injective
      rw [hj, hc1]
      exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
    have h2 : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => j.injective (by rw [hj, hj, Complex.conj_conj])
    have hinv : ∀ x, c (c x) = x := fun x => (algebraMap D.host.E D.nd.Om).injective (by rw [← h1, ← h1, h2])
    have hc : ∀ x : D.host.E, ∃ y : D.host.E, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
      fun x => ⟨c x, by rw [RingEquiv.symm_apply_eq, h1, hinv]⟩
    choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv v).exists
    have hbb : ∀ v, bar (bar v) = v := fun v =>
      (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv (bar v)).unique (hbar _) (GlobalTheory.AntiLAdic.conjPl_symm hinv (hbar v))
    let T := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
    have key : r * r.comp (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc) = 1 := by
      refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha ℂˣ _
        (hrc.mul (hrc.comp (GlobalTheory.AntiLAdic.continuous_conjHom D.ntw.cc hc))) (T ∪ T.image bar) fun v hv A hA σ hσ => ?_
      rw [Finset.mem_union, not_or] at hv
      have a2 : χ.UnrAt v := by simpa [T] using hv.1
      have b2 : χ.UnrAt (bar v) := by
        by_contra hn
        exact hv.2 (Finset.mem_image.2 ⟨bar v, by simpa [T] using hn, hbb v⟩)
      have hA' := GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) h1 (hbar v) hA
      have hσ' := GlobalTheory.AntiLAdic.isFrob_conjHom D.ntw.cc hc hσ
      rw [← GlobalTheory.AntiLAdic.normV_conjPl (hbar v)] at hσ'
      have e3 := GlobalTheory.AntiLAdic.val_mul_val_conj c hcm.rank hcm.ne hrr χ hψ.triv (hbar v) a2 b2
      rw [h.val_eq ha a2 hA hσ, h.val_eq ha b2 hA' hσ', ← mul_inv, inv_eq_one] at e3
      show r σ * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc σ) = 1
      exact e3
    intro g g' hg
    have e : g' = GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g := AlgEquiv.ext hg
    have k : r g * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g) = 1 := DFunLike.congr_fun key g
    rw [← map_mul, hinj, map_mul, ← e] at k
    exact eq_inv_of_mul_eq_one_right k
  · intro v A hA
    rw [← not_iff_not, not_exists]
    simp only [not_and, not_not]
    rw [Finset.mem_coe, ← hψ.ram v, h.unr_iff ha hA]
    exact forall₂_congr fun σ _ => (hinj σ).symm
  · intro v hv A hA σ hσ
    rw [← hinj]
    have hcl : IsClosed ((GlobalTheory.HeckeGal.liftAb r hrc).ker : Set (Gab D.host.E D.nd.Om)) :=
      isClosed_singleton.preimage (GlobalTheory.HeckeGal.continuous_liftAb r hrc)
    have hle : (art.comp (Neutral.B1.localIdele D.host.E v)).range ≤ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (art (Neutral.B1.localIdele D.host.E v x))
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, GlobalTheory.HeckeGal.liftAb_toAb, ← h _ τ hτ.symm]
      exact hψ.atl v hv x
    have hm : GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ ∈ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      refine Subgroup.topologicalClosure_minimal _ hle hcl ?_
      rw [ha.dec v A hA]
      exact ⟨σ, hσ, rfl⟩
    rwa [MonoidHom.mem_ker, GlobalTheory.HeckeGal.liftAb_toAb] at hm

end GlobalTheory.GalTwist

end
