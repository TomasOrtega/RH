import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Unfold `GlobalTheory.MemLoc.rootT`. Rewrite using `[← map_mul]`. Use `congr 1`. Proceed by induction on `n with`. Consider the case `zero => rfl`.

Consider the case `succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]`.
-/
theorem rootT_mul' {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (n : ℕ) :
    GlobalTheory.MemLoc.rootT (a * b) n = GlobalTheory.MemLoc.rootT a n * GlobalTheory.MemLoc.rootT b n := by
  unfold GlobalTheory.MemLoc.rootT
  rw [← map_mul]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

/- English proof (translation)
Unfold `GlobalTheory.MemLoc.rootT`. Rewrite using `[Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]`.
-/
theorem rootT_succ_pow' {l : ℕ} [Fact l.Prime] (a : Per.Fl l) (n : ℕ) :
    GlobalTheory.MemLoc.rootT a (n + 1) ^ l = GlobalTheory.MemLoc.rootT a n := by
  unfold GlobalTheory.MemLoc.rootT
  rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Introduce `l _ hroots K bk e he`. Take `⟨hπ, hπu⟩` from `GlobalTheory.BSP.BK.prime_unif l K bk`. Take `⟨halg, hfix⟩` from `GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk`. Use `choose y hy using halg`. Establish `hc : ∀ n : ℕ, ∃ c : Om l, (c : ℂ_[l]) = ((GlobalTheory.MemLoc.rootT e n : OC l) : ℂ_[l])`.

Introduce `n`. Use `hroots _ (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun x : OC l => (x : ℂ_[l])) (GlobalTheory.MemLoc.rootT_pow_eq_untilt e n)`. Simplify `h` using `[he]`. Use `choose c hc using hc`.

Establish `hcoe : ∀ x : Om l, (x : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x` using `fun _ => rfl`. Establish `hinj : Function.Injective (fun x : Om l => (x : ℂ_[l]))` using `(algebraMap (Om l) ℂ_[l]).injective`. Establish `hy0 : y 0 = (((bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) : ↥(OL K)) : ↥K.1) : Om l)`. Apply `hinj` to reduce the goal to its premises. Use `beta_reduce`.

Rewrite using `[← hy 0, ← coe_intToOC, hπu]`. Both sides reduce to the same expression. Establish `hc0 : c 0 = 1`. Apply `hinj` to reduce the goal to its premises. Use `beta_reduce`.

Rewrite using `[hc 0, hcoe, map_one]`. Use `show ((PreTilt.untilt e : OC l) : ℂ_[l]) = 1`. Rewrite using `[he]`. Both sides reduce to the same expression. Establish `hys : ∀ n, y (n + 1) ^ l = y n`.

Introduce `n`. Apply `hinj` to reduce the goal to its premises. Use `show ((y (n + 1) ^ l : Om l) : ℂ_[l]) = (y n : ℂ_[l])`. Rewrite using `[hcoe, map_pow, ← hcoe, ← hy, ← hy, ← SubmonoidClass.coe_pow, rootT_succ_pow']`. Establish `hcs : ∀ n, c (n + 1) ^ l = c n`.

Introduce `n`. Apply `hinj` to reduce the goal to its premises. Use `show ((c (n + 1) ^ l : Om l) : ℂ_[l]) = (c n : ℂ_[l])`. Rewrite using `[hcoe, map_pow, ← hcoe, hc, hc, ← SubmonoidClass.coe_pow, rootT_succ_pow']`. Take `⟨g, hg⟩` from `GlobalTheory.galois_transitive_on_root_systems_of_prime l K _ hπ y (fun n => c n * y n) hy0 (by rw [hc0, one_mul, hy0]) hys (fun n => by rw [mul_pow, hcs, hys])`.

Use `⟨g, hfix _ _ fun n => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `(GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_` and prove the remaining obligations. Rewrite using `[hy n, GlobalTheory.RingBasics.σC_coe, hg n, rootT_mul']`. Rewrite using `[MulMemClass.coe_mul, hcoe, map_mul, ← hcoe, ← hcoe, hc n, hy n]`.
-/
theorem galois_moves_flat_by_unit_root : ∀ (l : ℕ) [Fact l.Prime], (∀ (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x) → ∀ (K : FinExt l) (bk : BK K) (e : OCb l), e.untilt = 1 → ∃ g : ↥(GK K), Per.σF (g : GQ l) bk.flat = e * bk.flat := by
  intro l _ hroots K bk e he
  obtain ⟨hπ, hπu⟩ := GlobalTheory.BSP.BK.prime_unif l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose y hy using halg
  have hc : ∀ n : ℕ, ∃ c : Om l, (c : ℂ_[l]) = ((GlobalTheory.MemLoc.rootT e n : OC l) : ℂ_[l]) := by
    intro n
    refine hroots _ (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) ?_
    have h := congrArg (fun x : OC l => (x : ℂ_[l])) (GlobalTheory.MemLoc.rootT_pow_eq_untilt e n)
    simpa [he] using h
  choose c hc using hc
  have hcoe : ∀ x : Om l, (x : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x := fun _ => rfl
  have hinj : Function.Injective (fun x : Om l => (x : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hy0 : y 0 = (((bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) : ↥(OL K)) : ↥K.1) : Om l) := by
    apply hinj
    beta_reduce
    rw [← hy 0, ← coe_intToOC, hπu]
    rfl
  have hc0 : c 0 = 1 := by
    apply hinj
    beta_reduce
    rw [hc 0, hcoe, map_one]
    show ((PreTilt.untilt e : OC l) : ℂ_[l]) = 1
    rw [he]
    rfl
  have hys : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    apply hinj
    show ((y (n + 1) ^ l : Om l) : ℂ_[l]) = (y n : ℂ_[l])
    rw [hcoe, map_pow, ← hcoe, ← hy, ← hy, ← SubmonoidClass.coe_pow, rootT_succ_pow']
  have hcs : ∀ n, c (n + 1) ^ l = c n := by
    intro n
    apply hinj
    show ((c (n + 1) ^ l : Om l) : ℂ_[l]) = (c n : ℂ_[l])
    rw [hcoe, map_pow, ← hcoe, hc, hc, ← SubmonoidClass.coe_pow, rootT_succ_pow']
  obtain ⟨g, hg⟩ := GlobalTheory.galois_transitive_on_root_systems_of_prime l K _ hπ y (fun n => c n * y n) hy0
    (by rw [hc0, one_mul, hy0]) hys (fun n => by rw [mul_pow, hcs, hys])
  refine ⟨g, hfix _ _ fun n => ?_⟩
  apply Subtype.ext
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
  rw [hy n, GlobalTheory.RingBasics.σC_coe, hg n, rootT_mul']
  rw [MulMemClass.coe_mul, hcoe, map_mul, ← hcoe, ← hcoe, hc n, hy n]

end GlobalTheory.BSP
