import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ZSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HeckeSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Take `⟨⟨ι, hι⟩, hemb⟩` from `embEx (2 + 2) w hw`. Take `⟨-, hc1, hc2, -, -, hlev⟩` from `hemb ι hι`. Establish `hcf1 : ∀ v : Pl K, GM.cf v (1 : FA K (2 + 2)) = 1`. Introduce `v`. Distinguish the cases in `hv : v ∈ im w`.

Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`. Establish `h` using `hc1 1 i`. Rewrite `h` using `[map_one]`. Then use the resulting hypothesis. Establish `h` using `hc2 1 v hv`. Rewrite `h` using `[map_one]`. Then use the resulting hypothesis.

Establish `hinU : ∀ u ∈ Subgroup.pi Set.univ (fun i => U (w i)), ι u ∈ levOn (im w) U` using `fun u hu => (hlev U _).2 ⟨u, 1, (mul_one _).symm, fun i => hu i trivial, fun i => hcf1 _, fun v => by rw [hcf1]; exact one_mem _⟩`. Take `⟨-, hfl, hinj, -⟩` from `secTr μ₂ τ₁ τ₂ κ e hA.idem`. Take `⟨hZ, hZ'⟩` from `zMem μ₂ τ₁ τ₂ κ e hA.idem`. Establish `hle` using `(levLaws (2 + 2) (im w)).1`. Establish `hsimple` using `zSimple μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι hw hι`.

Establish `hex` using `(heckeEx K μ μ₂ τ₁ τ₂ hP κ e hA.idem (im w) U hU D hD d A).1`. Set `Φ : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)` to `{ toFun := fun v => flat 0 (A.sec v) map_add' := fun a b => by funext x; simp [flat, mul_add] map_smul' := fun c a => by funext x; simp [flat, mul_left_comm] }`. Establish `hΦ : ∀ v, Φ v = flat 0 (A.sec v)` using `fun _ => rfl`. Establish `hΦinj : Function.Injective Φ` using `fun a b h => A.inj (hinj _ _ h)`. Establish `hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ FixA κ e (A.sec v) ∧ FixF (levOn (im w) U) (A.sec v)` using `fun v => by`.

Take `⟨h1, h2⟩` from `(A.onto _).1 (LinearMap.mem_range_self A.sec v)`. Conclude with `⟨h1, (hD.fix _ h1.cont).1 h2⟩`. Establish `hfixΦ : ∀ v, FixF (levOn (im w) U) (Φ v)` using `fun v => ((hfl _ (hsec v).1.cont).2 _ (hle U hU).2).2 (hsec v).2.2`. Establish `hmem : ∀ v, Φ v ∈ Zs τ₁ τ₂ κ e (im w)` using `fun v => (hZ _ _).2 ⟨_, (hsec v).1, (hsec v).2.1, ⟨U, hU, (hsec v).2.2⟩, rfl⟩`. Establish `hCO : ∀ i, CO (U (w i))` using `fun i => (hU (w i)).1`.

Establish `hCOpi : CO (Subgroup.pi Set.univ fun i => U (w i))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_pi]`. Conclude with `isCompact_univ_pi fun i => (hCO i).1`. Rewrite using `[Subgroup.coe_pi]`.

Conclude with `isOpen_set_pi Set.finite_univ fun i _ => (hCO i).2`. Establish `hrS : ∀ g (φ : G1 K (2 + 2) → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g))` using `fun _ _ _ => rfl`. Establish `hQfix : ∀ φ ∈ P.map Φ, ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u φ = φ`. Introduce and unpack `_ ⟨v, -, rfl⟩ u hu`. Use function extensionality and compare the values at `x`.

Rewrite using `[hrS]`. Conclude with `hfixΦ v _ (hinU u hu) x`. Establish `hQhop : ∀ g, ∀ φ ∈ P.map Φ, hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ ∈ P.map Φ`. Use `hopProd (rS ι) (fun i => U (w i)) (P.map Φ) hCO hQfix ?_` and prove the remaining obligations. Introduce and unpack `i g _ ⟨v, hv, rfl⟩`.

Take `⟨M, hM, -⟩` from `hex (AdelicGLn.localEmbedding (w i) g)`. Use `⟨M v, hst (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) g M hM v hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← hopEmb (2 + 2) w ι hw hι U hU _ (hfixΦ v), hι i g]`. Conclude with `hM v`. Break down `heckeSimple (rS ι) (Zs τ₁ τ₂ κ e (im w)) _ hCOpi hsimple (fun φ hφ => (hZ' w ι hw hι φ hφ).1) (P.map Φ) (by rintro _ ⟨v, -, rfl⟩; exact hmem v) hQfix hQhop with h | h` into its components or cases.

Use `left`. Use `(Submodule.eq_bot_iff _).2 fun v hv => hΦinj ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `(Submodule.eq_bot_iff _).1 h _ ⟨v, hv, rfl⟩`. Use `right`.

Use `Submodule.eq_top_iff'.2 fun v => ?_` and prove the remaining obligations. Establish `hv : ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u (Φ v) = Φ v`. Introduce `u hu`. Use function extensionality and compare the values at `x`. Rewrite using `[hrS]`.

Conclude with `hfixΦ v _ (hinU u hu) x`. Take `⟨v', hv', he⟩` from `h _ (hmem v) hv`. Rewrite using `[← hΦinj he]` and apply the resulting hypothesis.
-/
private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irreducible_cuspidal_weight_component {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2)))
    [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hP : Pair μ₂ τ₁ τ₂)
    {κ e κ₂ p₁ p₂ k₀} (hA : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (hw : Function.Injective w)
    (U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)) (hU : Lev U) (D : TypeDat K (2 + 2)) (hD : IsTy D κ e (levOn (im w) U))
    (d : ℕ) (A : Line μ τ₁ τ₂ D d) (P : Submodule ℂ (Eu d))
    (hst : ∀ v ∈ im w, ∀ (g : Gw (2 + 2) v) M, HeckeAt A (levOn (im w) U) (AdelicGLn.localEmbedding v g) M → ∀ x ∈ P, M x ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (2 + 2) w hw
  obtain ⟨-, hc1, hc2, -, -, hlev⟩ := hemb ι hι
  have hcf1 : ∀ v : Pl K, GM.cf v (1 : FA K (2 + 2)) = 1 := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have h := hc1 1 i
      rwa [map_one] at h
    · have h := hc2 1 v hv
      rwa [map_one] at h
  have hinU : ∀ u ∈ Subgroup.pi Set.univ (fun i => U (w i)), ι u ∈ levOn (im w) U := fun u hu =>
    (hlev U _).2 ⟨u, 1, (mul_one _).symm, fun i => hu i trivial, fun i => hcf1 _, fun v => by rw [hcf1]; exact one_mem _⟩
  obtain ⟨-, hfl, hinj, -⟩ := secTr μ₂ τ₁ τ₂ κ e hA.idem
  obtain ⟨hZ, hZ'⟩ := zMem μ₂ τ₁ τ₂ κ e hA.idem
  have hle := (levLaws (2 + 2) (im w)).1
  have hsimple := zSimple μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι hw hι
  have hex := (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hA.idem (im w) U hU D hD d A).1
  let Φ : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ) :=
    { toFun := fun v => flat 0 (A.sec v)
      map_add' := fun a b => by funext x; simp [flat, mul_add]
      map_smul' := fun c a => by funext x; simp [flat, mul_left_comm] }
  have hΦ : ∀ v, Φ v = flat 0 (A.sec v) := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun a b h => A.inj (hinj _ _ h)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ FixA κ e (A.sec v) ∧ FixF (levOn (im w) U) (A.sec v) := fun v => by
    obtain ⟨h1, h2⟩ := (A.onto _).1 (LinearMap.mem_range_self A.sec v)
    exact ⟨h1, (hD.fix _ h1.cont).1 h2⟩
  have hfixΦ : ∀ v, FixF (levOn (im w) U) (Φ v) := fun v =>
    ((hfl _ (hsec v).1.cont).2 _ (hle U hU).2).2 (hsec v).2.2
  have hmem : ∀ v, Φ v ∈ Zs τ₁ τ₂ κ e (im w) := fun v =>
    (hZ _ _).2 ⟨_, (hsec v).1, (hsec v).2.1, ⟨U, hU, (hsec v).2.2⟩, rfl⟩
  have hCO : ∀ i, CO (U (w i)) := fun i => (hU (w i)).1
  have hCOpi : CO (Subgroup.pi Set.univ fun i => U (w i)) := by
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_pi]; exact isCompact_univ_pi fun i => (hCO i).1
    · rw [Subgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (hCO i).2
  have hrS : ∀ g (φ : G1 K (2 + 2) → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl
  have hQfix : ∀ φ ∈ P.map Φ, ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u φ = φ := by
    rintro _ ⟨v, -, rfl⟩ u hu
    funext x
    rw [hrS]
    exact hfixΦ v _ (hinU u hu) x
  have hQhop : ∀ g, ∀ φ ∈ P.map Φ, hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ ∈ P.map Φ := by
    refine hopProd (rS ι) (fun i => U (w i)) (P.map Φ) hCO hQfix ?_
    rintro i g _ ⟨v, hv, rfl⟩
    obtain ⟨M, hM, -⟩ := hex (AdelicGLn.localEmbedding (w i) g)
    refine ⟨M v, hst (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) g M hM v hv, ?_⟩
    rw [← hopEmb (2 + 2) w ι hw hι U hU _ (hfixΦ v), hι i g]
    exact hM v
  rcases heckeSimple (rS ι) (Zs τ₁ τ₂ κ e (im w)) _ hCOpi hsimple (fun φ hφ => (hZ' w ι hw hι φ hφ).1) (P.map Φ)
    (by rintro _ ⟨v, -, rfl⟩; exact hmem v) hQfix hQhop with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => hΦinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ ⟨v, hv, rfl⟩
  · right
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u (Φ v) = Φ v := by
      intro u hu
      funext x
      rw [hrS]
      exact hfixΦ v _ (hinU u hu) x
    obtain ⟨v', hv', he⟩ := h _ (hmem v) hv
    rwa [← hΦinj he]

/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hA S U hU D hD d A P hst`. Choose the witnesses or unpack the hypotheses as in `⟨r, w, hw, rfl⟩ : ∃ (r : ℕ) (w : Fin r → Pl K), Function.Injective w ∧ S = im w := by`. Use `⟨S.card, fun i => (S.equivFin.symm i : Pl K), fun a b h => S.equivFin.symm.injective (Subtype.ext h), ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`.

Conclude with `⟨fun hv => ⟨S.equivFin ⟨v, hv⟩, by simp⟩, fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2⟩`. Conclude with `irreducible_cuspidal_weight_component μ μ₂ τ₁ τ₂ hP hA w hw U hU D hD d A P hst`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irrW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IrrW := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hA S U hU D hD d A P hst
  obtain ⟨r, w, hw, rfl⟩ : ∃ (r : ℕ) (w : Fin r → Pl K), Function.Injective w ∧ S = im w := by
    refine ⟨S.card, fun i => (S.equivFin.symm i : Pl K), fun a b h => S.equivFin.symm.injective (Subtype.ext h), ?_⟩
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hv => ⟨S.equivFin ⟨v, hv⟩, by simp⟩, fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2⟩
  exact irreducible_cuspidal_weight_component μ μ₂ τ₁ τ₂ hP hA w hw U hU D hD d A P hst
