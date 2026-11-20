import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingNonzeroLocus

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory

/- English proof (translation)
Use `⟨powSecMk (m + n) (fun i => powSecFn s i * powSecFn s' i) ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[map_mul, map_mul, powSecFn_compat s i j, powSecFn_compat s' i j, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[nonzeroLocus_powSecMk]`.

Repeatedly rewrite using `[Scheme.basicOpen_mul, ← nonzeroLocus_inf_powSecFn]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `iSup_le fun i => le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)`. Introduce `x hx`. Establish `hx' : x ∈ ⨆ i, L.U i` using `by rw [hL.cover]; trivial`.

Rewrite `hx'`, the goal using `[TopologicalSpace.Opens.mem_iSup]`. Take `⟨i, hi⟩` from `hx'`. Conclude with `⟨i, ⟨hx.1, hi⟩, ⟨hx.2, hi⟩⟩`.
-/
private theorem exists_sec_lbPow_add_nonzeroLocus_eq_inf {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {m n : ℕ} (s : (lbPow L m).Sec) (s' : (lbPow L n).Sec) :
    ∃ τ : (lbPow L (m + n)).Sec, nonzeroLocus τ = nonzeroLocus s ⊓ nonzeroLocus s' := by
  refine ⟨powSecMk (m + n) (fun i => powSecFn s i * powSecFn s' i) ?_, ?_⟩
  · intro i j
    rw [map_mul, map_mul, powSecFn_compat s i j, powSecFn_compat s' i j, pow_add]
    ring
  · rw [nonzeroLocus_powSecMk]
    simp_rw [Scheme.basicOpen_mul, ← nonzeroLocus_inf_powSecFn]
    apply le_antisymm
    · exact iSup_le fun i => le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro x hx
      have hx' : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
      obtain ⟨i, hi⟩ := hx'
      exact ⟨i, ⟨hx.1, hi⟩, ⟨hx.2, hi⟩⟩

/- English proof (translation)
Proceed by induction on `t using Finset.cons_induction with`. Consider the case `empty => exact absurd ht Finset.not_nonempty_empty`. Consider the case `cons a s ha ih`. Break down `s.eq_empty_or_nonempty with hs | hs` into its components or cases. Substitute `hs` using the available equality.

Use `⟨e a, he a, σ a, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Take `⟨N, hN, τ, hτ⟩` from `ih hs`. Take `⟨τ', hτ'⟩` from `exists_sec_lbPow_add_nonzeroLocus_eq_inf hH (σ a) τ`. Use `⟨e a + N, by omega, τ', ?_⟩` and prove the remaining obligations.

Rewrite using `[hτ', hτ, Finset.cons_eq_insert, Finset.iInf_insert]`.
-/
theorem exists_sec_lbPow_nonzeroLocus_eq_iInf {X : Scheme.{0}} {H : LB X} (hH : H.IsLB)
    {r : ℕ} (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec) (he : ∀ a, 0 < e a)
    (t : Finset (Fin r)) (ht : t.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : (lbPow H N).Sec, nonzeroLocus τ = ⨅ a ∈ t, nonzeroLocus (σ a) := by
  induction t using Finset.cons_induction with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨e a, he a, σ a, ?_⟩
      simp
    · obtain ⟨N, hN, τ, hτ⟩ := ih hs
      obtain ⟨τ', hτ'⟩ := exists_sec_lbPow_add_nonzeroLocus_eq_inf hH (σ a) τ
      refine ⟨e a + N, by omega, τ', ?_⟩
      rw [hτ', hτ, Finset.cons_eq_insert, Finset.iInf_insert]

/- English proof (translation)
Introduce `X Y _ _ s F _ H hH j hev r e σ he t ht`. Take `⟨N, hN, τ, hτ⟩` from `exists_sec_lbPow_nonzeroLocus_eq_iInf hH e σ he t ht`. Rewrite using `[← hτ, ← nonzeroLocus_secPowPull τ s]`. Establish `hM : (H.pull s).IsLB` using `LB.isLB_pull hH s`. Establish `hL : (lbPow (H.pull s) N).IsLB` using `isLB_lbPow hM N`.

Apply `subsingleton_cohOn_nonzeroLocus_of_eventually_twist Y F (lbPow (H.pull s) N) hL` to reduce the goal to its premises. Take `⟨c0, hc0⟩` from `eventually_atTop.1 hev`. Use `eventually_atTop.2 ⟨c0, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hcls : cls (lbPow (lbPow (H.pull s) N) c) (isLB_lbPow hL c) = cls (lbPow (H.pull s) (N * c)) (isLB_lbPow hM (N * c))`. Rewrite using `[CechPic.cls_lbPow hL, CechPic.cls_lbPow hM, CechPic.cls_lbPow hM, smul_smul, mul_comm]`.

Take `⟨iso⟩` from `nonempty_twist_iso_of_cls_eq F (isLB_lbPow hL c) (isLB_lbPow hM (N * c)) hcls`. Establish `hsub` using `hc0 (N * c) (le_trans hc (Nat.le_mul_of_pos_left c hN))`. Conclude with `(cohOn.mapIso (Γ(Y, ⊤)) ⊤ j iso).toEquiv.subsingleton`.
-/
theorem subsingleton_cohOn_preimage_iInf_nonzeroLocus : ∀ (X Y : Scheme.{0}) [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), H.IsLB → ∀ j : ℕ, (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → ∀ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec), (∀ a, 0 < e a) → ∀ t : Finset (Fin r), t.Nonempty → Subsingleton (cohOn F (s ⁻¹ᵁ (⨅ a ∈ t, nonzeroLocus (σ a))) j) := by
  intro X Y _ _ s F _ H hH j hev r e σ he t ht
  obtain ⟨N, hN, τ, hτ⟩ := exists_sec_lbPow_nonzeroLocus_eq_iInf hH e σ he t ht
  rw [← hτ, ← nonzeroLocus_secPowPull τ s]
  have hM : (H.pull s).IsLB := LB.isLB_pull hH s
  have hL : (lbPow (H.pull s) N).IsLB := isLB_lbPow hM N
  apply subsingleton_cohOn_nonzeroLocus_of_eventually_twist Y F (lbPow (H.pull s) N) hL
  obtain ⟨c0, hc0⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨c0, fun c hc => ?_⟩
  have hcls : cls (lbPow (lbPow (H.pull s) N) c) (isLB_lbPow hL c)
      = cls (lbPow (H.pull s) (N * c)) (isLB_lbPow hM (N * c)) := by
    rw [CechPic.cls_lbPow hL, CechPic.cls_lbPow hM, CechPic.cls_lbPow hM, smul_smul, mul_comm]
  obtain ⟨iso⟩ := nonempty_twist_iso_of_cls_eq F (isLB_lbPow hL c) (isLB_lbPow hM (N * c)) hcls
  have hsub := hc0 (N * c) (le_trans hc (Nat.le_mul_of_pos_left c hN))
  exact (cohOn.mapIso (Γ(Y, ⊤)) ⊤ j iso).toEquiv.subsingleton

end GlobalTheory
