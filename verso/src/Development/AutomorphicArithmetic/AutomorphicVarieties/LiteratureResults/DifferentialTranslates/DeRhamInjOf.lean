import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Take `⟨W, hW⟩` from `h6 Γ V S d G hp`. Take `⟨u, hu⟩` from `h7 Γ V S d G W hW`. Take `⟨a1, a2, a3⟩` from `h3 Γ V S d G hc hn`. Conclude with `h1 q Γ _ (fun q => G.Om q) G.lev G.act G.incl G.dOm a1 (h2 Γ V S d G) a2 a3 (h4 Γ V S d G hc) (h5 Γ V S d G u hu) n w hi hd hx`.
-/
theorem geo_main (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (G : Geo Γ V S d)
    (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hp : G.Proper) (q n : ℕ) (w : Fin n → G.Om q)
    (hi : ∀ i γ, G.act q γ (w i) = w i) (hd : ∀ i, G.dOm q (w i) = 0)
    (hx : ∀ c : Fin n → ℂ, InvExact (Ω := fun q => G.Om q) G.act G.dOm (∑ i, c i • w i) → c = 0) :
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of G.lev) q) := by
  obtain ⟨W, hW⟩ := h6 Γ V S d G hp
  obtain ⟨u, hu⟩ := h7 Γ V S d G W hW
  obtain ⟨a1, a2, a3⟩ := h3 Γ V S d G hc hn
  exact h1 q Γ _ (fun q => G.Om q) G.lev G.act G.incl G.dOm a1 (h2 Γ V S d G) a2 a3 (h4 Γ V S d G hc) (h5 Γ V S d G u hu)
    n w hi hd hx

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ}

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (fun g : V [⋀^Fin q]→ₗ[ℝ] M => g X) fun _ _ => rfl) f _`.
-/
private theorem alt_sum {V M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (f : Fin n → V [⋀^Fin q]→ₗ[ℝ] M) (X : Fin q → V) : (∑ i, f i) X = ∑ i, f i X :=
  map_sum (AddMonoidHom.mk' (fun g : V [⋀^Fin q]→ₗ[ℝ] M => g X) fun _ _ => rfl) f _

/- English proof (translation)
Introduce `g x X` and use `by simp`.
-/
theorem corr_zero : Corr (q := q) U Ξ 0 0 := fun g x X => by simp

/- English proof (translation)
Introduce `g x X` and use `by rw [alt_sum, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ContinuousAlternatingMap.sum_apply, Matrix.mulVec_sum] refine Finset.sum_congr rfl fun i _ => ?_ rw [AlternatingMap.smul_apply, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_smul …`.
-/
theorem corr_sum {n : ℕ} (c : Fin n → ℂ) {α : Fin n → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))}
    {w : Fin n → (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)} (h : ∀ i, Corr U Ξ (α i) (w i)) :
    Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i) := fun g x X => by
  rw [alt_sum, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlternatingMap.smul_apply, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_smul, ← h i g x X]
  rfl

end

/- English proof (translation)
Introduce `E _ _ _ a ha U _ hU Ξ q n α hα hind`. Establish `ho : IsOpen (cone E a)` using `isOpen_iff_mem_nhds.2 fun p hp => by`. Take `⟨τ, -, hτ⟩` from `k1 E a p hp`. Conclude with `hτ.mono fun x hx => ⟨τ x, hx⟩`. Establish `hv : ∀ i X, LeftInv (α i X) ∧ RightInv U (α i X)` using `fun i X => (k5 E a U Ξ _).1 ((hα i).1.val X)`.

Establish `hw : ∀ i, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (α i) w.1` using `fun i => by`. Take `⟨w, hw, h0⟩` from `k7 E a U Ξ q (α i) (hα i).1.equiv fun X => (hv i X).2`. Conclude with `⟨⟨w, fun s => ⟨k8 E a U Ξ q _ w hw s, h0 s⟩⟩, hw⟩`. Use `choose w hw using hw`. Rewrite using `[← geo_lev ho U Ξ]`.

Use `geo_main h1 h2 h3 h4 h5 h6 h7 (geo ho U Ξ) (k2 E a).1 ⟨_, hOne_mem_cone⟩ (k3 E a ho U Ξ hU) q n w (fun i => (k12 E a ho U Ξ q _ _ (hw i)).1 fun X => (hv i X).1) (fun i => ?_) fun c hc => hind c ?_` and prove the remaining obligations. Establish `h` using `k14 E a ho U Ξ q _ _ (hw i)`. Rewrite `h` using `[(hα i).2]`. Conclude with `(k11 E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)`. Establish `hs : Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i).1`.

Rewrite using `[Submodule.coe_sum]`. Conclude with `corr_sum U Ξ c hw`. Establish `hb : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → (∑ i, c i • α i) X = 0` using `fun X i hX => by`. Rewrite using `[alt_sum]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [AlternatingMap.smul_apply, (hα j).1.basic X i hX, smul_zero]`.

Generalize the expression as in `∑ i, c i • α i = β at hs hb`. Generalize the expression as in `∑ i, c i • w i = z at hs hc`. Consider the cases of `q with`. Consider the case `zero`. Take `rfl : z = 0` from `hc`.

Conclude with `(k11 E a ho U Ξ 0).1 _ 0 _ hs (corr_zero U Ξ)`. Consider the case `succ q`. Take `⟨y, hy, rfl⟩` from `hc`. Take `⟨l, hl⟩` from `k4 E a ha ho U Ξ hU`. Take `⟨y', i1, i2, i3⟩` from `h8 _ _ _ _ (geo ho U Ξ) (k2 E a).2 l hl q y hy ((k13 E a U Ξ _ _ _ hs).1 hb)`.

Take `⟨η, hη⟩` from `k9 E a ho U Ξ q y'`. Establish `e : dCo (smLie Ξ) η = β` using `(k11 E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ k14 E a ho U Ξ q _ _ hη) hs`. Establish `b` using `(k13 E a U Ξ _ _ _ hη).2 i2`. Take `⟨c1, c2⟩` from `k10 E a U Ξ q _ _ hη`. Conclude with `⟨η, ⟨c1, b, fun X => (k5 E a U Ξ _).2 ((k12 E a ho U Ξ q _ _ hη).2 i1 X) (c2 X) (k6 E a _ (smLie Ξ) q η b (e ▸ hb) X)⟩, e⟩`.
-/
theorem deRhamInj_of (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    (h8 : Retract) (k1 : LocSec) (k2 : ConeConvex) (k3 : GeoProper) (k4 : Gauge) (k5 : LevelVal) (k6 : CentralOf)
    (k7 : CorrFwd) (k8 : CorrSmooth) (k9 : CorrBwd) (k10 : CorrCochain) (k11 : CorrUniq) (k12 : CorrInv) (k13 : CorrBasic)
    (k14 : CorrD) : DeRhamInj := by
  intro E _ _ _ a ha U _ hU Ξ q n α hα hind
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := k1 E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have hv : ∀ i X, LeftInv (α i X) ∧ RightInv U (α i X) := fun i X => (k5 E a U Ξ _).1 ((hα i).1.val X)
  have hw : ∀ i, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (α i) w.1 := fun i => by
    obtain ⟨w, hw, h0⟩ := k7 E a U Ξ q (α i) (hα i).1.equiv fun X => (hv i X).2
    exact ⟨⟨w, fun s => ⟨k8 E a U Ξ q _ w hw s, h0 s⟩⟩, hw⟩
  choose w hw using hw
  rw [← geo_lev ho U Ξ]
  refine geo_main h1 h2 h3 h4 h5 h6 h7 (geo ho U Ξ) (k2 E a).1 ⟨_, hOne_mem_cone⟩ (k3 E a ho U Ξ hU) q n w
    (fun i => (k12 E a ho U Ξ q _ _ (hw i)).1 fun X => (hv i X).1) (fun i => ?_) fun c hc => hind c ?_
  · have h := k14 E a ho U Ξ q _ _ (hw i)
    rw [(hα i).2] at h
    exact (k11 E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · have hs : Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i).1 := by
      rw [Submodule.coe_sum]
      exact corr_sum U Ξ c hw
    have hb : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → (∑ i, c i • α i) X = 0 := fun X i hX => by
      rw [alt_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [AlternatingMap.smul_apply, (hα j).1.basic X i hX, smul_zero]
    generalize ∑ i, c i • α i = β at hs hb
    generalize ∑ i, c i • w i = z at hs hc
    cases q with
    | zero =>
      obtain rfl : z = 0 := hc
      exact (k11 E a ho U Ξ 0).1 _ 0 _ hs (corr_zero U Ξ)
    | succ q =>
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨l, hl⟩ := k4 E a ha ho U Ξ hU
      obtain ⟨y', i1, i2, i3⟩ := h8 _ _ _ _ (geo ho U Ξ) (k2 E a).2 l hl q y hy ((k13 E a U Ξ _ _ _ hs).1 hb)
      obtain ⟨η, hη⟩ := k9 E a ho U Ξ q y'
      have e : dCo (smLie Ξ) η = β := (k11 E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ k14 E a ho U Ξ q _ _ hη) hs
      have b := (k13 E a U Ξ _ _ _ hη).2 i2
      obtain ⟨c1, c2⟩ := k10 E a U Ξ q _ _ hη
      exact ⟨η, ⟨c1, b, fun X => (k5 E a U Ξ _).2 ((k12 E a ho U Ξ q _ _ hη).2 i1 X) (c2 X)
        (k6 E a _ (smLie Ξ) q η b (e ▸ hb) X)⟩, e⟩

end UpperTheory.V.Lit.Dr
