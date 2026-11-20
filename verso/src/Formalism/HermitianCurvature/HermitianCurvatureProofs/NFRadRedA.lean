import Formalism.HermitianCurvature.StatementNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hg.1, fun a _ => hg.2 a⟩`.
-/
theorem uwb_glev {g : Q.Mx k r} (hg : g ∈ B2.UWb k r) : g ∈ Glev k r (Fin.last r) := ⟨hg.1, fun a _ => hg.2 a⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hg.1, fun a => hg.2 a a.isLt⟩`.
-/
theorem glev_uwb {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := ⟨hg.1, fun a => hg.2 a a.isLt⟩

/- English proof (translation)
The claim follows from `TwoByOneBlock.emb_mem_UWb (hsec.2 ζ hζ).1`.
-/
theorem muZ_uwb (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    muZ k r μsec ζ ∈ B2.UWb k r := TwoByOneBlock.emb_mem_UWb (hsec.2 ζ hζ).1

/- English proof (translation)
Simplify using `[Q.zetaL, Formalism.QuantumDeterminants.fvec]`.
-/
theorem zeta_eq (g : Q.Mx k r) : zetaL k r z z' (Fin.last r) g = herm (Hpk k r) (g *ᵥ z') z := by
  simp [Q.zetaL, Formalism.QuantumDeterminants.fvec]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [UH]`.
-/
private theorem one_mem_uwset (w : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r w := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [UH]

/- English proof (translation)
Establish `h1` using `one_mem_uwset (k := k) (r := r) z`. Establish `h1'` using `one_mem_uwset (k := k) (r := r) z'`. Establish `h2` using `(TwoByOneBlock.rankOneMem k r z z' μsec hz hz' hsec ζ hζ 1 h1 1 h1').2`. Rewrite using `[zeta_eq]`. Simplify `h2` using `[NF.muZ]`.
-/
theorem zeta_muZ (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec) {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : zetaL k r z z' (Fin.last r) (muZ k r μsec ζ) = ζ := by
  have h1 := one_mem_uwset (k := k) (r := r) z
  have h1' := one_mem_uwset (k := k) (r := r) z'
  have h2 := (TwoByOneBlock.rankOneMem k r z z' μsec hz hz' hsec ζ hζ 1 h1 1 h1').2
  rw [zeta_eq]
  simpa [NF.muZ] using h2

/- English proof (translation)
Establish `hO : IsOpen (OmX r)`. Establish `he : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0}` using `by ext x; simp [OmX]`. Rewrite using `[he]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Conclude with `(hO.preimage continuous_fst).inter (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))`.
-/
theorem qr_open : IsOpen (QR k r z z') := by
  have hO : IsOpen (OmX r) := by
    have he : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [he]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  exact (hO.preimage continuous_fst).inter
    (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))

/- English proof (translation)
Use `⟨hq.1, uwb_glev (muZ_uwb hsec hq.2), ?_⟩` and prove the remaining obligations. Use `show 0 < GGl k r z z' (muZ k r μsec q.2)`. Unfold `GGl`. Rewrite using `[zeta_muZ hz hz' hsec hq.2]`. Conclude with `sub_pos.2 hq.2`.
-/
theorem mem_domR (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec)
    {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QR k r z z') : (q.1, muZ k r μsec q.2) ∈ DomR k r z z' := by
  refine ⟨hq.1, uwb_glev (muZ_uwb hsec hq.2), ?_⟩
  show 0 < GGl k r z z' (muZ k r μsec q.2)
  unfold GGl
  rw [zeta_muZ hz hz' hsec hq.2]
  exact sub_pos.2 hq.2

/- English proof (translation)
Use `contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [NF.muZ, B2.embWb]`. Distinguish the cases in `h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)`. Simplify using `only [dif_pos h]`. Conclude with `hsec.1 _ _`.

Simplify using `only [dif_neg h]`. Conclude with `contDiffOn_const`.
-/
theorem muZ_contDiffOn (hsec : IsSection k r z z' μsec) :
    ContDiffOn ℝ ∞ (fun ζ => muZ k r μsec ζ) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  simp only [NF.muZ, B2.embWb]
  by_cases h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [dif_pos h]
    exact hsec.1 _ _
  · simp only [dif_neg h]
    exact contDiffOn_const

/- English proof (translation)
Establish `hU : g ∈ B2.UWb k r` using `glev_uwb hg`. Establish `hζ : Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (g *ᵥ z') z)`. Establish `h2` using `hG`. Unfold `GGl at h2`. Rewrite `h2` using `[zeta_eq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h, hh, h', hh', he⟩` from `TwoByOneBlock.rankOneCoord k r z z' μsec hk hz hz' hT hT' hsec g hU hζ`. Use `⟨h⁻¹, BigCellInversePair.uw_inv hh, h', hh', ?_⟩` and prove the remaining obligations. Rewrite using `[zeta_eq]`. Conclude with `he`.
-/
theorem decomp (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z', g = h * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * h' := by
  have hU : g ∈ B2.UWb k r := glev_uwb hg
  have hζ : Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) := by
    have h2 := hG
    unfold GGl at h2
    rw [zeta_eq] at h2
    linarith
  obtain ⟨h, hh, h', hh', he⟩ := TwoByOneBlock.rankOneCoord k r z z' μsec hk hz hz' hT hT' hsec g hU hζ
  refine ⟨h⁻¹, BigCellInversePair.uw_inv hh, h', hh', ?_⟩
  rw [zeta_eq]
  exact he

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ`. Take `⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩` from `hB`. Take `⟨h0, hs, he⟩` from `hΦ`. Use `⟨?_, fun q hq => ?_, fun q hq => Set.indicator_of_notMem hq _⟩` and prove the remaining obligations. Apply `contDiffOn_of_locally_contDiffOn` to reduce the goal to its premises.

Introduce `q0 hq0`. Take `⟨V, F, hV, hxV, hF, hΦF⟩` from `hs _ (mem_domR hz hz' hsec hq0)`. Establish `hψ : ContDiffOn ℝ ∞ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) (QR k r z z')` using `contDiffOn_fst.prodMk ((muZ_contDiffOn hsec).comp contDiffOn_snd (fun q hq => hq.2))`. Use `⟨QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V, hψ.continuousOn.isOpen_inter_preimage qr_open hV, ⟨hq0, hxV⟩, ?_⟩` and prove the remaining obligations. Establish `hc : ContDiffOn ℝ ∞ (F ∘ fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) (QR k r z z' ∩ (QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V))` using `hF.comp (hψ.mono fun q hq => hq.1) fun q hq => hq.2.2`.

Use `hc.congr fun q hq => ?_` and prove the remaining obligations. Simplify using `only [radR, Set.indicator_of_mem hq.1, Function.comp_apply]`. Conclude with `hΦF _ hq.2.2 (uwb_glev (muZ_uwb hsec hq.1.2))`. Simplify using `only [radR, Set.indicator_of_mem hq, Fib, Set.mem_setOf_eq]`. Introduce `p hp`.

Take `⟨hp1, hp2, hpe⟩` from `hp`. Establish `h3` using `he _ (mem_domR hz hz' hsec hq) p.1 hp1 p.2 hp2`. Simplify using `only at h3`. Rewrite `h3` using `[hpe]`. Conclude with `h3.symm`.
-/
theorem radRedMem : NF.RadRedMem := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨?_, fun q hq => ?_, fun q hq => Set.indicator_of_notMem hq _⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro q0 hq0
    obtain ⟨V, F, hV, hxV, hF, hΦF⟩ := hs _ (mem_domR hz hz' hsec hq0)
    have hψ : ContDiffOn ℝ ∞ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) (QR k r z z') :=
      contDiffOn_fst.prodMk ((muZ_contDiffOn hsec).comp contDiffOn_snd (fun q hq => hq.2))
    refine ⟨QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V,
      hψ.continuousOn.isOpen_inter_preimage qr_open hV, ⟨hq0, hxV⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (F ∘ fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2))
        (QR k r z z' ∩ (QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V)) :=
      hF.comp (hψ.mono fun q hq => hq.1) fun q hq => hq.2.2
    refine hc.congr fun q hq => ?_
    simp only [radR, Set.indicator_of_mem hq.1, Function.comp_apply]
    exact hΦF _ hq.2.2 (uwb_glev (muZ_uwb hsec hq.1.2))
  · simp only [radR, Set.indicator_of_mem hq, Fib, Set.mem_setOf_eq]
    intro p hp
    obtain ⟨hp1, hp2, hpe⟩ := hp
    have h3 := he _ (mem_domR hz hz' hsec hq) p.1 hp1 p.2 hp2
    simp only at h3
    rw [hpe] at h3
    exact h3.symm

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ Ψ hΨ hR`. Take `⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩` from `hB`. Take `⟨h0, -, he⟩` from `hΦ`. Take `⟨h0', -, he'⟩` from `hΨ`. Use function extensionality and compare the values at `x g`.

Distinguish the cases in `hx : (x, g) ∈ DomR k r z z'`. Take `⟨hxO, hg, hG⟩` from `hx`. Take `⟨h, hh, h', hh', hd⟩` from `decomp hk hz hz' hT hT' hsec hg hG`. Establish `hq : (x, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z'`. Use `⟨hxO, ?_⟩` and prove the remaining obligations.

Establish `h2` using `hG`. Unfold `GGl at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD` using `mem_domR hz hz' hsec hq`. Establish `e1` using `he _ hD h hh h' hh'`.

Establish `e2` using `he' _ hD h hh h' hh'`. Establish `hr` using `congrFun hR (x, zetaL k r z z' (Fin.last r) g)`. Simplify using `only [radR, Set.indicator_of_mem hq] at hr`. Simplify using `only at e1 e2 hd`. Rewrite using `[hd, e1, e2, hr]`.

Conclude with `(h0 (x, g) hx).trans (h0' (x, g) hx).symm`.
-/
theorem radRedInj : NF.RadRedInj := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ Ψ hΨ hR
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := hΦ
  obtain ⟨h0', -, he'⟩ := hΨ
  funext x g
  by_cases hx : (x, g) ∈ DomR k r z z'
  · obtain ⟨hxO, hg, hG⟩ := hx
    obtain ⟨h, hh, h', hh', hd⟩ := decomp hk hz hz' hT hT' hsec hg hG
    have hq : (x, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by
      refine ⟨hxO, ?_⟩
      have h2 := hG
      unfold GGl at h2
      linarith
    have hD := mem_domR hz hz' hsec hq
    have e1 := he _ hD h hh h' hh'
    have e2 := he' _ hD h hh h' hh'
    have hr := congrFun hR (x, zetaL k r z z' (Fin.last r) g)
    simp only [radR, Set.indicator_of_mem hq] at hr
    simp only at e1 e2 hd
    rw [hd, e1, e2, hr]
  · exact (h0 (x, g) hx).trans (h0' (x, g) hx).symm

end Formalism.FourierDecayAlt.P.NFRadRedA

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `NFRadRedA.radRedMem`.
-/
theorem radical_reduction_mem : Formalism.FourierDecayAlt.NF.RadRedMem := NFRadRedA.radRedMem

/- English proof (translation)
The claim follows from `NFRadRedA.radRedInj`.
-/
theorem radical_reduction_injective : Formalism.FourierDecayAlt.NF.RadRedInj := NFRadRedA.radRedInj

end Formalism.FourierDecayAlt.P
