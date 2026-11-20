import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
open ComplexConjugate

namespace GlobalTheory.CurvConstVec

/- English proof (translation)
Establish `hc1 : MContDiffAt 1 (fun x => conn K x ξ) z` using `hK.conn hu (j := 1) (by rw [one_add_one_eq_two]) ξ`. Establish `hcov : ∀ x, covDel K (fun _ => v) x ξ = conn K x ξ *ᵥ v` using `fun x => by`. Use extensionality with `a`. Simplify using `[covDel]`. Establish `hdel : ∀ x, MContDiffAt 1 K x → IsUnit (K x).det → GlobalTheory.del (fun y => form (K y) v v) x ξ = form (K x) (conn K x ξ *ᵥ v) v`.

Introduce `x h1 h2`. Rewrite using `[del_form (s := fun _ => v) (t := fun _ => v) h1 h2 (fun _ => contDiffAt_const) (fun _ => contDiffAt_const) ξ, hcov]`. Simplify using `only [GlobalTheory.dbar_const, ContinuousLinearMap.zero_apply]`. Rewrite using `[show (fun _ : n => (0 : ℂ)) = 0 from rfl]`. Simplify using `[form]`.

Establish `hev : (fun x => GlobalTheory.del (fun y => form (K y) v v) x ξ) =ᶠ[𝓝 z] fun x => conj (form (K x) v (conn K x ξ *ᵥ v))` using `by filter_upwards [hK.eventually_two, hK.eventually_isUnit hu, hh] with x h1 h2 h3`. Rewrite using `[hdel x (h1.of_le one_le_two) h2, conj_form h3]`. Establish `hφ : ContDiffAt ℝ 2 (fun x => form (K x) v v) z`. Simplify using `only [form_eq_sum]`. Conclude with `ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (contDiffAt_const.mul (hK a b)).mul contDiffAt_const`.

Establish `ht : ∀ a, ContDiffAt ℝ 1 (fun x => (conn K x ξ *ᵥ v) a) z` using `fun a => by`. Simplify using `only [mulVec, dotProduct]`. Conclude with `ContDiffAt.sum fun b _ => (hc1 a b).mul contDiffAt_const`. Establish `hmv : (fun a => GlobalTheory.dbar (fun x => (conn K x ξ *ᵥ v) a) z ξ) = mdbar (fun x => conn K x ξ) z ξ *ᵥ v`. Use extensionality with `a`.

Simplify using `only [mulVec, dotProduct]`. Rewrite using `[GlobalTheory.dbar_sum (t := Finset.univ) (A := fun b x => conn K x ξ a b * v b) fun b _ => (hc1.diff a b).mul_const (v b), ContinuousLinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.dbar_mul (b := fun _ => v b) (hc1.diff a b) (differentiableAt_const (v b))]`. Simplify using the standard rewrite rules.

Establish `hg` using `del_form (s := fun _ => v) (hK.of_le one_le_two) hu (fun _ => contDiffAt_const) ht ξ`. Rewrite `hg` using `[hcov, hmv]`. Establish `hF : mdbar (fun x => conn K x ξ) z ξ = -curv K z ξ ξ` using `by rw [curv, neg_neg]`. Rewrite using `[GlobalTheory.ddbar_eq_dbar_del hφ, GlobalTheory.dbar_congr hev, GlobalTheory.dbar_conj, hg, hF, map_add, conj_form hh.self_of_nhds, conj_form hh.self_of_nhds]`. Simplify using `only [form, neg_mulVec, neg_dotProduct]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_curv_const_vec {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {K : (ι → ℂ) → Matrix n n ℂ} {z : ι → ℂ} (hK : MContDiffAt 2 K z)
    (hh : ∀ᶠ x in 𝓝 z, (K x).IsHermitian) (hu : IsUnit (K z).det) (ξ : ι → ℂ) (v : n → ℂ) :
    form (K z) (curv K z ξ ξ *ᵥ v) v = form (K z) (conn K z ξ *ᵥ v) (conn K z ξ *ᵥ v) -
      GlobalTheory.ddbar (fun x => form (K x) v v) z ξ ξ := by
  have hc1 : MContDiffAt 1 (fun x => conn K x ξ) z :=
    hK.conn hu (j := 1) (by rw [one_add_one_eq_two]) ξ
  have hcov : ∀ x, covDel K (fun _ => v) x ξ = conn K x ξ *ᵥ v := fun x => by
    ext a; simp [covDel]
  have hdel : ∀ x, MContDiffAt 1 K x → IsUnit (K x).det →
      GlobalTheory.del (fun y => form (K y) v v) x ξ = form (K x) (conn K x ξ *ᵥ v) v := by
    intro x h1 h2
    rw [del_form (s := fun _ => v) (t := fun _ => v) h1 h2 (fun _ => contDiffAt_const)
      (fun _ => contDiffAt_const) ξ, hcov]
    simp only [GlobalTheory.dbar_const, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : n => (0 : ℂ)) = 0 from rfl]
    simp [form]
  have hev : (fun x => GlobalTheory.del (fun y => form (K y) v v) x ξ) =ᶠ[𝓝 z]
      fun x => conj (form (K x) v (conn K x ξ *ᵥ v)) := by
    filter_upwards [hK.eventually_two, hK.eventually_isUnit hu, hh] with x h1 h2 h3
    rw [hdel x (h1.of_le one_le_two) h2, conj_form h3]
  have hφ : ContDiffAt ℝ 2 (fun x => form (K x) v v) z := by
    simp only [form_eq_sum]
    exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
      (contDiffAt_const.mul (hK a b)).mul contDiffAt_const
  have ht : ∀ a, ContDiffAt ℝ 1 (fun x => (conn K x ξ *ᵥ v) a) z := fun a => by
    simp only [mulVec, dotProduct]
    exact ContDiffAt.sum fun b _ => (hc1 a b).mul contDiffAt_const
  have hmv : (fun a => GlobalTheory.dbar (fun x => (conn K x ξ *ᵥ v) a) z ξ) =
      mdbar (fun x => conn K x ξ) z ξ *ᵥ v := by
    ext a
    simp only [mulVec, dotProduct]
    rw [GlobalTheory.dbar_sum (t := Finset.univ) (A := fun b x => conn K x ξ a b * v b)
      fun b _ => (hc1.diff a b).mul_const (v b), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.dbar_mul (b := fun _ => v b) (hc1.diff a b) (differentiableAt_const (v b))]
    simp
  have hg := del_form (s := fun _ => v) (hK.of_le one_le_two) hu (fun _ => contDiffAt_const) ht ξ
  rw [hcov, hmv] at hg
  have hF : mdbar (fun x => conn K x ξ) z ξ = -curv K z ξ ξ := by rw [curv, neg_neg]
  rw [GlobalTheory.ddbar_eq_dbar_del hφ, GlobalTheory.dbar_congr hev, GlobalTheory.dbar_conj, hg, hF, map_add,
    conj_form hh.self_of_nhds, conj_form hh.self_of_nhds]
  simp only [form, neg_mulVec, neg_dotProduct]
  ring

end GlobalTheory.CurvConstVec
