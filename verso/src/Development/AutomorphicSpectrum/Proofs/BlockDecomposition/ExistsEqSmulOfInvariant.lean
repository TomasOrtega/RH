import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbUniq

/- English proof (translation)
Distinguish the cases in `hlam : lam = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Substitute `hlam` using the available equality. Simplify using `using Measure.absolutelyContinuous_zero_iff.1 hνl`. Establish `hTg : ∀ g, Measurable (T g)` using `fun g => hT.comp measurable_prodMk_left`.

Use `set ρ := ν.rnDeriv lam with hρdef`. Establish `hρ : Measurable ρ` using `Measure.measurable_rnDeriv ν lam`. Establish `hden : lam.withDensity ρ = ν` using `Measure.withDensity_rnDeriv_eq ν lam hνl`. Establish `h1 : ∀ g, ∀ᵐ y ∂lam, ρ (T g y) = ρ y`. Introduce `g`.

Take `⟨g', hg'⟩` from `hinv g`. Set `eq : Y ≃ᵐ Y` to `{ toFun := T g, invFun := T g', left_inv := fun y => (hg' y).1, right_inv := fun y => (hg' y).2, measurable_toFun := hTg g, measurable_invFun := hTg g' }`. Establish `hmp : MeasurePreserving (T g) lam lam` using `⟨hTg g, hl g⟩`. Establish `hw : lam.withDensity (ρ ∘ T g) = lam.withDensity ρ`. Use `Measure.ext fun A hA => ?_` and prove the remaining obligations.

Rewrite using `[withDensity_apply _ hA, hden]`. Establish `hAB : A = T g ⁻¹' (T g' ⁻¹' A)`. Use extensionality with `y`. Simplify using `[(hg' y).1]`. Establish `hB : MeasurableSet (T g' ⁻¹' A)` using `hTg g' hA`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hAB]`. Both sides reduce to the same expression. Use `_ = ∫⁻ y in T g' ⁻¹' A, ρ y ∂lam := hmp.setLIntegral_comp_preimage_emb eq.measurableEmbedding ρ _`. Use `_ = lam.withDensity ρ (T g' ⁻¹' A) := (withDensity_apply _ hB).symm`.

Use `_ = ν (T g' ⁻¹' A) := by rw [hden]`. Use `_ = ν.map (T g') A := (Measure.map_apply (hTg g') hA).symm`. Use `_ = ν A := by rw [hn g']`. Conclude with `(withDensity_eq_iff_of_sigmaFinite (hρ.comp (hTg g)).aemeasurable hρ.aemeasurable).1 hw`. Establish `hE : ∀ c : Y → ℝ≥0∞, Measurable c → MeasurableSet {p : Γ × Y | ρ (T p.1 p.2) = c p.2}` using `fun c hc => measurableSet_eq_fun (hρ.comp hT) (hc.comp measurable_snd)`.

Establish `hm' : (ae m).NeBot` using `ae_neBot.2 hm`. Establish `hl' : (ae lam).NeBot` using `ae_neBot.2 hlam`. Establish `h2 : ∀ᵐ y ∂lam, ∀ᵐ g ∂m, ρ (T g y) = ρ y` using `(Measure.ae_ae_comm (p := fun g y => ρ (T g y) = ρ y) (hE ρ hρ)).1 (Eventually.of_forall h1)`. Establish `hOae : ∀ᵐ y ∂lam, y ∈ O`. Rewrite using `[ae_iff]`.

Conclude with `hO`. Take `⟨y₀, hy₀, hy₀O⟩` from `(h2.and hOae).exists`. Establish `h3 : ∀ᵐ y ∂lam, ∀ᵐ g ∂m, ρ (T g y) = ρ y₀` using `by filter_upwards [hOae] with y hy`. Take `⟨φ, hφ, hyφ⟩` from `htr y₀ hy₀O y hy`. Use `filter_upwards [hφ.ae hy₀] with g hg`.

Rewrite using `[hyφ g, hg]`. Establish `h4 : ∀ᵐ g ∂m, ∀ᵐ y ∂lam, ρ (T g y) = ρ y₀` using `(Measure.ae_ae_comm (p := fun g y => ρ (T g y) = ρ y₀) (hE _ measurable_const)).2 h3`. Take `⟨g, hg⟩` from `h4.exists`. Establish `h5 : ρ =ᵐ[lam] fun _ => ρ y₀` using `by filter_upwards [hg, h1 g] with y hy hy'`. Rewrite using `[← hy', hy]`.

Establish `hfin : ρ y₀ ≠ ⊤`. Take `⟨y, hy, hy'⟩` from `(h5.and (Measure.rnDeriv_lt_top ν lam)).exists`. Establish `hy2 : ρ y₀ = ρ y` using `hy.symm`. Rewrite using `[hy2]`. Conclude with `hy'.ne`.

Use `⟨(ρ y₀).toNNReal, ?_⟩` and prove the remaining obligations. Rewrite using `[← hden, withDensity_congr_ae h5, withDensity_const]`. Use extensionality with `A hA`. Simplify using `[ENNReal.smul_def, ENNReal.coe_toNNReal hfin]`.
-/
theorem exists_eq_smul_of_invariant {Γ Y : Type*} [MeasurableSpace Γ] [MeasurableSpace Y]
    (m : Measure Γ) [SFinite m] (hm : m ≠ 0) (lam ν : Measure Y) [SigmaFinite lam] [SigmaFinite ν]
    (hνl : ν ≪ lam) (T : Γ → Y → Y) (hT : Measurable fun p : Γ × Y => T p.1 p.2)
    (hl : ∀ g, lam.map (T g) = lam) (hn : ∀ g, ν.map (T g) = ν)
    (hinv : ∀ g, ∃ g', ∀ y, T g' (T g y) = y ∧ T g (T g' y) = y)
    (O : Set Y) (hO : lam Oᶜ = 0)
    (htr : ∀ y₀ ∈ O, ∀ y ∈ O, ∃ φ : Γ → Γ, Measure.QuasiMeasurePreserving φ m m ∧
      ∀ g, T g y = T (φ g) y₀) :
    ∃ c : ℝ≥0, ν = c • lam := by
  by_cases hlam : lam = 0
  · refine ⟨0, ?_⟩
    subst hlam
    simpa using Measure.absolutelyContinuous_zero_iff.1 hνl
  have hTg : ∀ g, Measurable (T g) := fun g => hT.comp measurable_prodMk_left
  set ρ := ν.rnDeriv lam with hρdef
  have hρ : Measurable ρ := Measure.measurable_rnDeriv ν lam
  have hden : lam.withDensity ρ = ν := Measure.withDensity_rnDeriv_eq ν lam hνl

  have h1 : ∀ g, ∀ᵐ y ∂lam, ρ (T g y) = ρ y := by
    intro g
    obtain ⟨g', hg'⟩ := hinv g
    let eq : Y ≃ᵐ Y :=
      { toFun := T g, invFun := T g', left_inv := fun y => (hg' y).1, right_inv := fun y => (hg' y).2,
        measurable_toFun := hTg g, measurable_invFun := hTg g' }
    have hmp : MeasurePreserving (T g) lam lam := ⟨hTg g, hl g⟩
    have hw : lam.withDensity (ρ ∘ T g) = lam.withDensity ρ := by
      refine Measure.ext fun A hA => ?_
      rw [withDensity_apply _ hA, hden]
      have hAB : A = T g ⁻¹' (T g' ⁻¹' A) := by
        ext y
        simp [(hg' y).1]
      have hB : MeasurableSet (T g' ⁻¹' A) := hTg g' hA
      calc ∫⁻ y in A, (ρ ∘ T g) y ∂lam = ∫⁻ y in T g ⁻¹' (T g' ⁻¹' A), ρ (T g y) ∂lam := by
            rw [← hAB]; rfl
        _ = ∫⁻ y in T g' ⁻¹' A, ρ y ∂lam :=
            hmp.setLIntegral_comp_preimage_emb eq.measurableEmbedding ρ _
        _ = lam.withDensity ρ (T g' ⁻¹' A) := (withDensity_apply _ hB).symm
        _ = ν (T g' ⁻¹' A) := by rw [hden]
        _ = ν.map (T g') A := (Measure.map_apply (hTg g') hA).symm
        _ = ν A := by rw [hn g']
    exact (withDensity_eq_iff_of_sigmaFinite (hρ.comp (hTg g)).aemeasurable hρ.aemeasurable).1 hw
  have hE : ∀ c : Y → ℝ≥0∞, Measurable c → MeasurableSet {p : Γ × Y | ρ (T p.1 p.2) = c p.2} := fun c hc =>
    measurableSet_eq_fun (hρ.comp hT) (hc.comp measurable_snd)
  have hm' : (ae m).NeBot := ae_neBot.2 hm
  have hl' : (ae lam).NeBot := ae_neBot.2 hlam

  have h2 : ∀ᵐ y ∂lam, ∀ᵐ g ∂m, ρ (T g y) = ρ y :=
    (Measure.ae_ae_comm (p := fun g y => ρ (T g y) = ρ y) (hE ρ hρ)).1 (Eventually.of_forall h1)
  have hOae : ∀ᵐ y ∂lam, y ∈ O := by
    rw [ae_iff]; exact hO
  obtain ⟨y₀, hy₀, hy₀O⟩ := (h2.and hOae).exists

  have h3 : ∀ᵐ y ∂lam, ∀ᵐ g ∂m, ρ (T g y) = ρ y₀ := by
    filter_upwards [hOae] with y hy
    obtain ⟨φ, hφ, hyφ⟩ := htr y₀ hy₀O y hy
    filter_upwards [hφ.ae hy₀] with g hg
    rw [hyφ g, hg]
  have h4 : ∀ᵐ g ∂m, ∀ᵐ y ∂lam, ρ (T g y) = ρ y₀ :=
    (Measure.ae_ae_comm (p := fun g y => ρ (T g y) = ρ y₀) (hE _ measurable_const)).2 h3
  obtain ⟨g, hg⟩ := h4.exists
  have h5 : ρ =ᵐ[lam] fun _ => ρ y₀ := by
    filter_upwards [hg, h1 g] with y hy hy'
    rw [← hy', hy]
  have hfin : ρ y₀ ≠ ⊤ := by
    obtain ⟨y, hy, hy'⟩ := (h5.and (Measure.rnDeriv_lt_top ν lam)).exists
    have hy2 : ρ y₀ = ρ y := hy.symm
    rw [hy2]; exact hy'.ne
  refine ⟨(ρ y₀).toNNReal, ?_⟩
  rw [← hden, withDensity_congr_ae h5, withDensity_const]
  ext A hA
  simp [ENNReal.smul_def, ENNReal.coe_toNNReal hfin]

end GlobalTheory.CompanionTheory.OrbUniq

namespace GlobalTheory.CompanionTheory.OrbUniq

variable {D : D7} {r t : ℕ}

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F`. Use `haveI : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele D.host.F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)`. Conclude with `⟨e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩`.
-/
theorem ae_facts (D : D7) : LocallyCompactSpace (AE D) ∧ SecondCountableTopology (AE D) ∧ T2Space (AE D) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  haveI : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  exact ⟨e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `ae_facts D`. Conclude with `⟨inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → AE D)), inferInstanceAs (SecondCountableTopology (Fin a → Fin b → AE D)), inferInstanceAs (T2Space (Fin a → Fin b → AE D)), inferInstanceAs (IsTopologicalAddGroup (Fin a → Fin b → AE D)), ⟨rfl⟩⟩`.
-/
theorem mx_facts (D : D7) (a b : ℕ) : LocallyCompactSpace (Mx D a b) ∧ SecondCountableTopology (Mx D a b) ∧
    T2Space (Mx D a b) ∧ IsTopologicalAddGroup (Mx D a b) ∧ BorelSpace (Mx D a b) := by
  obtain ⟨h1, h2, h3⟩ := ae_facts D
  exact ⟨inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → AE D)),
    inferInstanceAs (SecondCountableTopology (Fin a → Fin b → AE D)),
    inferInstanceAs (T2Space (Fin a → Fin b → AE D)),
    inferInstanceAs (IsTopologicalAddGroup (Fin a → Fin b → AE D)), ⟨rfl⟩⟩

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt, map_mul]`.
-/
theorem mt_mul (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul]

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt, map_one]`.
-/
theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt, map_one]

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mt (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Establish `h : A * B - 1 = (A - 1) * B + (B - 1)`. Rewrite using `[sub_mul, one_mul, sub_add_sub_cancel]`. Rewrite using `[h, smul_add, ← Matrix.smul_mul, hA, hB]`.
-/
theorem smul_sub_one_mul {R : Type*} [CommRing R] {n : ℕ} (e : R) (A B : Matrix (Fin n) (Fin n) R)
    (hA : e • (A - 1) = A - 1) (hB : e • (B - 1) = B - 1) : e • (A * B - 1) = A * B - 1 := by
  have h : A * B - 1 = (A - 1) * B + (B - 1) := by
    rw [sub_mul, one_mul, sub_add_sub_cancel]
  rw [h, smul_add, ← Matrix.smul_mul, hA, hB]

/- English proof (translation)
Establish `h : B - 1 = -(B * (A - 1))`. Rewrite using `[mul_sub, hBA, mul_one, neg_sub]`. Rewrite using `[h, smul_neg, ← Matrix.mul_smul, hA]`.
-/
theorem smul_sub_one_inv {R : Type*} [CommRing R] {n : ℕ} (e : R) (A B : Matrix (Fin n) (Fin n) R)
    (hBA : B * A = 1) (hA : e • (A - 1) = A - 1) : e • (B - 1) = B - 1 := by
  have h : B - 1 = -(B * (A - 1)) := by
    rw [mul_sub, hBA, mul_one, neg_sub]
  rw [h, smul_neg, ← Matrix.mul_smul, hA]

def gS (V : HSp D) (e : AE D) : Subgroup (GA D V) where
  carrier := {h | e • (Formalism.L2.Theta.mt V h - 1) = Formalism.L2.Theta.mt V h - 1}
  mul_mem' := by
    intro g h hg hh
    change e • (Formalism.L2.Theta.mt V (g * h) - 1) = Formalism.L2.Theta.mt V (g * h) - 1
    rw [mt_mul]
    exact smul_sub_one_mul e _ _ hg hh
  one_mem' := by
    change e • (Formalism.L2.Theta.mt V 1 - 1) = Formalism.L2.Theta.mt V 1 - 1
    rw [mt_one, sub_self, smul_zero]
  inv_mem' := by
    intro h hh
    change e • (Formalism.L2.Theta.mt V h⁻¹ - 1) = Formalism.L2.Theta.mt V h⁻¹ - 1
    exact smul_sub_one_inv e (Formalism.L2.Theta.mt V h) _ (by rw [← mt_mul, inv_mul_cancel, mt_one]) hh

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `mx_facts D V.rank V.rank`. Use `haveI : ContinuousSub (Matrix (Fin V.rank) (Fin V.rank) (AE D)) := @IsTopologicalAddGroup.to_continuousSub _ _ _ h4`. Establish `hc : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h - 1` using `(continuous_mt V).sub continuous_const`. Conclude with `isClosed_eq (hc.const_smul e) hc`.
-/
theorem isClosed_gS (V : HSp D) (e : AE D) : IsClosed (gS V e : Set (GA D V)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mx_facts D V.rank V.rank
  haveI : ContinuousSub (Matrix (Fin V.rank) (Fin V.rank) (AE D)) := @IsTopologicalAddGroup.to_continuousSub _ _ _ h4
  have hc : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h - 1 := (continuous_mt V).sub continuous_const
  exact isClosed_eq (hc.const_smul e) hc

/- English proof (translation)
Rewrite using `[smul_add, Matrix.mul_add x, Matrix.mul_assoc A B, Matrix.mul_assoc B x, ← Matrix.mul_add B]`. Use `congr 2`. Rewrite using `[add_assoc, add_comm (x * (e • b))]`.
-/
theorem act_alg {R : Type*} [CommRing R] {n r t : ℕ} (e : R) (A B : Matrix (Fin n) (Fin n) R)
    (a b : Matrix (Fin r) (Fin t) R) (x : Matrix (Fin n) (Fin r) R) (v : Matrix (Fin n) (Fin t) R) :
    A * (B * (v + x * (e • b)) + (B * x) * (e • a)) = (A * B) * (v + x * (e • (a + b))) := by
  rw [smul_add, Matrix.mul_add x, Matrix.mul_assoc A B, Matrix.mul_assoc B x, ← Matrix.mul_add B]
  congr 2
  rw [add_assoc, add_comm (x * (e • b))]

def act (V : HSp D) (e : AE D) (g : GA D V) (a : Mx D r t) (z : Mx D V.rank r × Mx D V.rank t) :
    Mx D V.rank r × Mx D V.rank t :=
  (mm (Formalism.L2.Theta.mt V g) z.1, mm (Formalism.L2.Theta.mt V g) (z.2 + mm z.1 (e • a)))

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mm (Formalism.L2.Theta.mt V g) (mm (Formalism.L2.Theta.mt V h) z.1) = mm (Formalism.L2.Theta.mt V (g * h)) z.1`. Rewrite using `[mt_mul]`. Conclude with `(Matrix.mul_assoc _ _ _).symm`. Express the relevant statement in the definitionally equal form `mm (Formalism.L2.Theta.mt V g) (mm (Formalism.L2.Theta.mt V h) (z.2 + mm z.1 (e • b)) + mm (mm (Formalism.L2.Theta.mt V h) z.1) (e • a)) = mm (Formalism.L2.Theta.mt V (g * h)) (z.2 + mm z.1 (e • (a + b)))`.

Rewrite using `[mt_mul]`. Conclude with `act_alg e _ _ a b z.1 z.2`.
-/
theorem act_act (V : HSp D) (e : AE D) (g h : GA D V) (a b : Mx D r t) (z : Mx D V.rank r × Mx D V.rank t) :
    act V e g a (act V e h b z) = act V e (g * h) (a + b) z := by
  refine Prod.ext ?_ ?_
  · change mm (Formalism.L2.Theta.mt V g) (mm (Formalism.L2.Theta.mt V h) z.1) = mm (Formalism.L2.Theta.mt V (g * h)) z.1
    rw [mt_mul]
    exact (Matrix.mul_assoc _ _ _).symm
  · change mm (Formalism.L2.Theta.mt V g) (mm (Formalism.L2.Theta.mt V h) (z.2 + mm z.1 (e • b)) +
        mm (mm (Formalism.L2.Theta.mt V h) z.1) (e • a)) = mm (Formalism.L2.Theta.mt V (g * h)) (z.2 + mm z.1 (e • (a + b)))
    rw [mt_mul]
    exact act_alg e _ _ a b z.1 z.2

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mm (Formalism.L2.Theta.mt V 1) z.1 = z.1`. Rewrite using `[mt_one]`. Conclude with `Matrix.one_mul _`. Express the relevant statement in the definitionally equal form `mm (Formalism.L2.Theta.mt V 1) (z.2 + mm z.1 (e • (0 : Mx D r t))) = z.2`.

Rewrite using `[mt_one, smul_zero]`. Use `(Matrix.one_mul _).trans ?_` and prove the remaining obligations. Rewrite using `[show mm z.1 (0 : Mx D r t) = 0 from Matrix.mul_zero _, add_zero]`.
-/
theorem act_one (V : HSp D) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) :
    act V e 1 (0 : Mx D r t) z = z := by
  refine Prod.ext ?_ ?_
  · change mm (Formalism.L2.Theta.mt V 1) z.1 = z.1
    rw [mt_one]
    exact Matrix.one_mul _
  · change mm (Formalism.L2.Theta.mt V 1) (z.2 + mm z.1 (e • (0 : Mx D r t))) = z.2
    rw [mt_one, smul_zero]
    refine (Matrix.one_mul _).trans ?_
    rw [show mm z.1 (0 : Mx D r t) = 0 from Matrix.mul_zero _, add_zero]

/- English proof (translation)
Take `⟨-, -, -, h4, -⟩` from `mx_facts D r t`. Establish `hm : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => Formalism.L2.Theta.mt V p.1.1` using `(continuous_mt V).comp (continuous_fst.comp continuous_fst)`. Establish `ha : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => e • p.1.2` using `(continuous_snd.comp continuous_fst).const_smul e`. Establish `h1 : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => p.2.1` using `continuous_fst.comp continuous_snd`. Establish `h2 : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => p.2.2` using `continuous_snd.comp continuous_snd`.

Conclude with `(hm.matrix_mul h1).prodMk (hm.matrix_mul (h2.add (h1.matrix_mul ha)))`.
-/
theorem continuous_act (V : HSp D) (e : AE D) :
    Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => act V e p.1.1 p.1.2 p.2 := by
  obtain ⟨-, -, -, h4, -⟩ := mx_facts D r t
  have hm : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => Formalism.L2.Theta.mt V p.1.1 :=
    (continuous_mt V).comp (continuous_fst.comp continuous_fst)
  have ha : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => e • p.1.2 :=
    (continuous_snd.comp continuous_fst).const_smul e
  have h1 : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => p.2.1 :=
    continuous_fst.comp continuous_snd
  have h2 : Continuous fun p : (GA D V × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => p.2.2 :=
    continuous_snd.comp continuous_snd
  exact (hm.matrix_mul h1).prodMk (hm.matrix_mul (h2.add (h1.matrix_mul ha)))

/- English proof (translation)
Take `⟨p1, p2, p3, p4, p5⟩` from `mx_facts D V.rank r`. Take `⟨q1, q2, q3, q4, q5⟩` from `mx_facts D V.rank t`. Establish `hU : Continuous fun z : Mx D V.rank r × Mx D V.rank t => (mm (Formalism.L2.Theta.mt V g) z.1, mm (Formalism.L2.Theta.mt V g) z.2)` using `(continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)`. Establish `hS : Continuous fun z : Mx D V.rank r × Mx D V.rank t => (z.1, z.2 + mm z.1 (e • a))` using `continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))`. Establish `hc : act V e g a = (fun z : Mx D V.rank r × Mx D V.rank t => (mm (Formalism.L2.Theta.mt V g) z.1, mm (Formalism.L2.Theta.mt V g) z.2)) ∘ (fun z : Mx D V.rank r × Mx D V.rank t => (z.1, z.2 + mm z.1 (e • a)))` using `rfl`.

Rewrite using `[hc, ← Measure.map_map hU.measurable hS.measurable, hν.invS (e • a) (by rw [smul_smul, he]), hν.invU g hg]`.
-/
theorem map_act {V : HSp D} {b₀ : HermE D r} {e : AE D} (he : e * e = e)
    {ν : Measure (Mx D V.rank r × Mx D V.rank t)} (hν : IsOrb (t := t) V b₀ e ν) (g : GA D V) (hg : g ∈ gS V e)
    (a : Mx D r t) : ν.map (act V e g a) = ν := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := mx_facts D V.rank r
  obtain ⟨q1, q2, q3, q4, q5⟩ := mx_facts D V.rank t
  have hU : Continuous fun z : Mx D V.rank r × Mx D V.rank t =>
      (mm (Formalism.L2.Theta.mt V g) z.1, mm (Formalism.L2.Theta.mt V g) z.2) :=
    (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)
  have hS : Continuous fun z : Mx D V.rank r × Mx D V.rank t => (z.1, z.2 + mm z.1 (e • a)) :=
    continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  have hc : act V e g a = (fun z : Mx D V.rank r × Mx D V.rank t =>
      (mm (Formalism.L2.Theta.mt V g) z.1, mm (Formalism.L2.Theta.mt V g) z.2)) ∘
      (fun z : Mx D V.rank r × Mx D V.rank t => (z.1, z.2 + mm z.1 (e • a))) := rfl
  rw [hc, ← Measure.map_map hU.measurable hS.measurable, hν.invS (e • a) (by rw [smul_smul, he]),
    hν.invU g hg]

/- English proof (translation)
Use `⟨hf.measurable.prodMap hg.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[← Measure.map_prod_map μ ν hf.measurable hg.measurable]`. Conclude with `hf.absolutelyContinuous.prod hg.absolutelyContinuous`.
-/
theorem qmp_prodMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f : X → X} {g : Y → Y} (hf : Measure.QuasiMeasurePreserving f μ μ)
    (hg : Measure.QuasiMeasurePreserving g ν ν) :
    Measure.QuasiMeasurePreserving (Prod.map f g) (μ.prod ν) (μ.prod ν) := by
  refine ⟨hf.measurable.prodMap hg.measurable, ?_⟩
  rw [← Measure.map_prod_map μ ν hf.measurable hg.measurable]
  exact hf.absolutelyContinuous.prod hg.absolutelyContinuous

end GlobalTheory.CompanionTheory.OrbUniq

namespace GlobalTheory.CompanionTheory.OrbUniq

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `hI hN hT D r t V b₀ hb S e he ν ν' hν hν' hne`. Take `⟨hee, -⟩` from `(hI D S).2 e he`. Take `⟨p1, p2, p3, p4, p5⟩` from `mx_facts D V.rank r`. Take `⟨q1, q2, q3, q4, q5⟩` from `mx_facts D V.rank t`. Take `⟨s1, s2, s3, s4, s5⟩` from `mx_facts D r t`.

Use `haveI hGB : BorelSpace (GA D V) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (gS V e) := (isClosed_gS V e).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Set `m₁ : Measure (gS V e)` to `Measure.haar`. Set `m₂ : Measure (Mx D r t)` to `Measure.addHaar`. Set `T : (gS V e × Mx D r t) → (Mx D V.rank r × Mx D V.rank t) → (Mx D V.rank r × Mx D V.rank t)` to `fun g => act V e (g.1 : GA D V) g.2`.

Establish `hTc : Continuous fun p : (gS V e × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => T p.1 p.2` using `(continuous_act (r := r) (t := t) V e).comp (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk (continuous_snd.comp continuous_fst)).prodMk continuous_snd)`. Establish `hTm : Measurable fun p : (gS V e × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => T p.1 p.2` using `hTc.measurable`. Establish `hTg : ∀ g, Measurable (T g)` using `fun g => hTm.comp measurable_prodMk_left`. Establish `hm : m₁.prod m₂ ≠ 0`. Introduce `h0`.

Establish `h1 : m₁ Set.univ ≠ 0` using `(isOpen_univ.measure_pos m₁ Set.univ_nonempty).ne'`. Establish `h2 : m₂ Set.univ ≠ 0` using `(isOpen_univ.measure_pos m₂ Set.univ_nonempty).ne'`. Establish `h3` using `congrArg (fun μ : Measure (gS V e × Mx D r t) => μ (Set.univ ×ˢ Set.univ)) h0`. Simplify using `only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply] at h3`. Conclude with `mul_ne_zero h1 h2 h3`.

Use `haveI := hν.fin`. Use `haveI := hν'.fin`. Use `haveI : SigmaFinite ν := inferInstance`. Use `haveI : SigmaFinite ν' := inferInstance`. Establish `hinv : ∀ g : gS V e × Mx D r t, ∃ g', ∀ y, T g' (T g y) = y ∧ T g (T g' y) = y`.

Introduce `g`. Use `⟨(g.1⁻¹, -g.2), fun y => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act V e ((g.1⁻¹ : gS V e) : GA D V) (-g.2) (act V e (g.1 : GA D V) g.2 y) = y`. Rewrite using `[act_act, Subgroup.coe_inv, inv_mul_cancel, neg_add_cancel, act_one]`. Express the relevant statement in the definitionally equal form `act V e (g.1 : GA D V) g.2 (act V e ((g.1⁻¹ : gS V e) : GA D V) (-g.2) y) = y`.

Rewrite using `[act_act, Subgroup.coe_inv, mul_inv_cancel, add_neg_cancel, act_one]`. Establish `hpres : ∀ {μ : Measure (Mx D V.rank r × Mx D V.rank t)}, IsOrb (t` using `t) V b₀ e μ → ∀ g, μ.map (T g) = μ := fun hμ g => map_act hee hμ _ g.1.2 g.2`. Set `O : Set (Mx D V.rank r × Mx D V.rank t)` to `{z | Free e z ∧ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)}`. Establish `hOz : ∀ {μ : Measure (Mx D V.rank r × Mx D V.rank t)}, IsOrb (t` using `t) V b₀ e μ → μ Oᶜ = 0 := by`. Introduce `μ hμ`.

Use `measure_mono_null (t := {z | ¬ Free e z} ∪ {z | ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)}) ?_ (measure_union_null (hN D r t V b₀ hb S e he μ hμ) hμ.supp)` and prove the remaining obligations. Introduce `z hz`. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc`. Conclude with `hz hc`.

Establish `htr : ∀ y₀ ∈ O, ∀ y ∈ O, ∃ φ : (gS V e × Mx D r t) → (gS V e × Mx D r t), Measure.QuasiMeasurePreserving φ (m₁.prod m₂) (m₁.prod m₂) ∧ ∀ g, T g y = T (φ g) y₀`. Introduce `y₀ hy₀ y hy`. Take `⟨h, b, hh, hb', hyz⟩` from `(hT D r t V b₀ hb S e he).2 y₀ y hy₀.1 hy.1 hy₀.2 hy.2`. Establish `hyact : y = act V e h b y₀`. Rewrite using `[hyz]`.

Simplify using `only [act, hb']`. Use `⟨Prod.map (fun g => g * (⟨h, hh⟩ : gS V e)) (fun a => a + b), qmp_prodMap (quasiMeasurePreserving_mul_right m₁ _) (measurePreserving_add_right m₂ b).quasiMeasurePreserving, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act V e (g.1 : GA D V) g.2 y = act V e (g.1 * h) (g.2 + b) y₀`. Rewrite using `[hyact, act_act]`. Establish `key : ∀ {μ : Measure (Mx D V.rank r × Mx D V.rank t)} [SigmaFinite μ], IsOrb (t` using `t) V b₀ e μ → μ ≪ ν + ν' → ∃ c : ℝ≥0, μ = c • (ν + ν') := by`.

Introduce `μ _ hμ hac`. Use `exists_eq_smul_of_invariant (m₁.prod m₂) hm (ν + ν') μ hac T hTm ?_ (hpres hμ) hinv O ?_ htr` and prove the remaining obligations. Introduce `g`. Rewrite using `[Measure.map_add _ _ (hTg g), hpres hν, hpres hν']`. Simplify using `[hOz hν, hOz hν']`.

Take `⟨c, hc⟩` from `key hν (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))`. Take `⟨c', hc'⟩` from `key hν' (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))`. Establish `hc0 : c' ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (by simpa using hc')`.

Use `⟨c / c', ?_⟩` and prove the remaining obligations. Rewrite using `[hc']`. Use `conv_lhs => rw [hc]`. Rewrite using `[smul_smul, div_mul_cancel₀ _ hc0]`.
-/
theorem uniq_of_trans : IdemEx → NullSing → Trans → Uniq := by
  intro hI hN hT D r t V b₀ hb S e he ν ν' hν hν' hne
  obtain ⟨hee, -⟩ := (hI D S).2 e he
  obtain ⟨p1, p2, p3, p4, p5⟩ := mx_facts D V.rank r
  obtain ⟨q1, q2, q3, q4, q5⟩ := mx_facts D V.rank t
  obtain ⟨s1, s2, s3, s4, s5⟩ := mx_facts D r t
  haveI hGB : BorelSpace (GA D V) := ⟨rfl⟩

  haveI : LocallyCompactSpace (gS V e) := (isClosed_gS V e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let m₁ : Measure (gS V e) := Measure.haar
  let m₂ : Measure (Mx D r t) := Measure.addHaar
  let T : (gS V e × Mx D r t) → (Mx D V.rank r × Mx D V.rank t) → (Mx D V.rank r × Mx D V.rank t) :=
    fun g => act V e (g.1 : GA D V) g.2
  have hTc : Continuous fun p : (gS V e × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => T p.1 p.2 :=
    (continuous_act (r := r) (t := t) V e).comp
      (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hTm : Measurable fun p : (gS V e × Mx D r t) × (Mx D V.rank r × Mx D V.rank t) => T p.1 p.2 :=
    hTc.measurable
  have hTg : ∀ g, Measurable (T g) := fun g => hTm.comp measurable_prodMk_left
  have hm : m₁.prod m₂ ≠ 0 := by
    intro h0
    have h1 : m₁ Set.univ ≠ 0 := (isOpen_univ.measure_pos m₁ Set.univ_nonempty).ne'
    have h2 : m₂ Set.univ ≠ 0 := (isOpen_univ.measure_pos m₂ Set.univ_nonempty).ne'
    have h3 := congrArg (fun μ : Measure (gS V e × Mx D r t) => μ (Set.univ ×ˢ Set.univ)) h0
    simp only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply] at h3
    exact mul_ne_zero h1 h2 h3

  haveI := hν.fin
  haveI := hν'.fin
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite ν' := inferInstance
  have hinv : ∀ g : gS V e × Mx D r t, ∃ g', ∀ y, T g' (T g y) = y ∧ T g (T g' y) = y := by
    intro g
    refine ⟨(g.1⁻¹, -g.2), fun y => ⟨?_, ?_⟩⟩
    · change act V e ((g.1⁻¹ : gS V e) : GA D V) (-g.2) (act V e (g.1 : GA D V) g.2 y) = y
      rw [act_act, Subgroup.coe_inv, inv_mul_cancel, neg_add_cancel, act_one]
    · change act V e (g.1 : GA D V) g.2 (act V e ((g.1⁻¹ : gS V e) : GA D V) (-g.2) y) = y
      rw [act_act, Subgroup.coe_inv, mul_inv_cancel, add_neg_cancel, act_one]
  have hpres : ∀ {μ : Measure (Mx D V.rank r × Mx D V.rank t)}, IsOrb (t := t) V b₀ e μ →
      ∀ g, μ.map (T g) = μ := fun hμ g => map_act hee hμ _ g.1.2 g.2
  let O : Set (Mx D V.rank r × Mx D V.rank t) := {z | Free e z ∧
    (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)}
  have hOz : ∀ {μ : Measure (Mx D V.rank r × Mx D V.rank t)}, IsOrb (t := t) V b₀ e μ → μ Oᶜ = 0 := by
    intro μ hμ
    refine measure_mono_null (t := {z | ¬ Free e z} ∪
      {z | ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)}) ?_
      (measure_union_null (hN D r t V b₀ hb S e he μ hμ) hμ.supp)
    intro z hz
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hz hc
  have htr : ∀ y₀ ∈ O, ∀ y ∈ O, ∃ φ : (gS V e × Mx D r t) → (gS V e × Mx D r t),
      Measure.QuasiMeasurePreserving φ (m₁.prod m₂) (m₁.prod m₂) ∧ ∀ g, T g y = T (φ g) y₀ := by
    intro y₀ hy₀ y hy
    obtain ⟨h, b, hh, hb', hyz⟩ := (hT D r t V b₀ hb S e he).2 y₀ y hy₀.1 hy.1 hy₀.2 hy.2
    have hyact : y = act V e h b y₀ := by
      rw [hyz]
      simp only [act, hb']
    refine ⟨Prod.map (fun g => g * (⟨h, hh⟩ : gS V e)) (fun a => a + b),
      qmp_prodMap (quasiMeasurePreserving_mul_right m₁ _)
        (measurePreserving_add_right m₂ b).quasiMeasurePreserving, fun g => ?_⟩
    change act V e (g.1 : GA D V) g.2 y = act V e (g.1 * h) (g.2 + b) y₀
    rw [hyact, act_act]
  have key : ∀ {μ : Measure (Mx D V.rank r × Mx D V.rank t)} [SigmaFinite μ], IsOrb (t := t) V b₀ e μ → μ ≪ ν + ν' →
      ∃ c : ℝ≥0, μ = c • (ν + ν') := by
    intro μ _ hμ hac
    refine exists_eq_smul_of_invariant (m₁.prod m₂) hm (ν + ν') μ hac T hTm ?_ (hpres hμ) hinv O ?_ htr
    · intro g
      rw [Measure.map_add _ _ (hTg g), hpres hν, hpres hν']
    · simp [hOz hν, hOz hν']
  obtain ⟨c, hc⟩ := key hν (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
  obtain ⟨c', hc'⟩ := key hν' (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hc0 : c' ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hc')
  refine ⟨c / c', ?_⟩
  rw [hc']
  conv_lhs => rw [hc]
  rw [smul_smul, div_mul_cancel₀ _ hc0]

end GlobalTheory.CompanionTheory.OrbUniq
