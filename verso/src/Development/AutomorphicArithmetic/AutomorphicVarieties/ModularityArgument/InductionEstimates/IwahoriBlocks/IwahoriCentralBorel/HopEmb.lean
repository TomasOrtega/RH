import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW.2`. Establish `hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ W)` using `QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)`. Use `((hW.1.image hc).finite_of_discrete).subset ?_` and prove the remaining obligations. Introduce and unpack `c ⟨u, hu, rfl⟩`. Conclude with `⟨u, hu, rfl⟩`.
-/
private theorem cosets_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W : Subgroup G}
    (hW : CO W) (g : G) : {c : G ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ W) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hW.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

/- English proof (translation)
Introduce `K _ _ n r w ι hw hι U hU φ hφ g`. Take `⟨hcf, hoff, -, hcomm, hmem⟩` from `((embEx n w hw).2 ι hι).2`. Establish `hcf' : ∀ (v : Pl K), GM.cf v (1 : FA K n) ∈ GLnLocal.integralGL (v.adicCompletion K) n`. Introduce `v`. Distinguish the cases in `hv : v ∈ im w`.

Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`. Use `hcf 1 i` as an intermediate fact. Rewrite `this` using `[map_one]`. Rewrite using `[this]`. Conclude with `Subgroup.one_mem _`.

Use `hoff 1 v hv` as an intermediate fact. Rewrite `this` using `[map_one]`. Rewrite using `[this]`. Conclude with `Subgroup.one_mem _`. Establish `hcf1 : ∀ i, GM.cf (w i) (1 : FA K n) = 1`.

Introduce `i`. Use `hcf 1 i` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Use `set L := levOn (im w) U with hL`. Use `set W : Subgroup (GS n w) := Subgroup.pi Set.univ fun i => U (w i) with hWdef`.

Establish `hWL : ∀ a ∈ W, ι a ∈ L` using `fun a ha => (hmem U _).2 ⟨a, 1, (mul_one _).symm, fun i => ha i trivial, hcf1, hcf'⟩`. Establish `hLW : ∀ x, ι x ∈ L → x ∈ W`. Introduce `x hx`. Take `⟨a, h', e, ha, h1, -⟩` from `(hmem U _).1 hx`. Establish `e' : h' = ι (a⁻¹ * x)` using `by rw [map_mul, map_inv, e, inv_mul_cancel_left]`.

Establish `e1 : a⁻¹ * x = 1` using `funext fun i => by`. Rewrite using `[← hcf (a⁻¹ * x) i, ← e', h1]`. Both sides reduce to the same expression. Rewrite using `[(inv_mul_eq_one.1 e1).symm]`. Conclude with `fun i _ => ha i`.

Establish `hW : CO W` using `⟨isCompact_univ_pi fun j => (hU (w j)).1.1, isOpen_set_pi Set.finite_univ fun j _ => (hU (w j)).1.2⟩`. Set `e : GS n w ⧸ W → FA K n ⧸ L` to `fun c => QuotientGroup.mk (ι c.out)`. Establish `he : ∀ y, e (QuotientGroup.mk y) = QuotientGroup.mk (ι y)`. Introduce `y`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations.

Use `hWL _ (QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk y : GS n w ⧸ W)))` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv]`. Then use the resulting hypothesis. Establish `hbij : Set.BijOn e {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)} {c : FA K n ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * ι g)}`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `c ⟨u, hu, rfl⟩`.

Conclude with `⟨ι u, hWL u hu, by rw [he, map_mul]⟩`. Introduce `c _ d _ hcd`. Establish `h1` using `QuotientGroup.eq.1 hcd`. Rewrite `h1` using `[← map_inv, ← map_mul]`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]`.

Conclude with `QuotientGroup.eq.2 (hLW _ h1)`. Introduce and unpack `c ⟨u, hu, rfl⟩`. Take `⟨a, h', e', ha, h1, h2⟩` from `(hmem U _).1 hu`. Establish `hh' : h' ∈ L` using `(hmem U _).2 ⟨1, h', by simp, fun i => Subgroup.one_mem _, h1, h2⟩`. Use `⟨QuotientGroup.mk (a * g), ⟨a, fun i _ => ha i, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, map_mul, e']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Establish `: (ι a * ι g)⁻¹ * (ι a * h' * ι g) = h'`. Rewrite using `[mul_assoc (ι a) h', (hcomm g h' h1).symm.eq]`. Use `group`.

Rewrite using `[this]` and apply the resulting hypothesis. Establish `hfin` using `cosets_finite hW g`. Use function extensionality and compare the values at `x`. Establish `hR : hopR (rS ι) W g φ x = ∑ᶠ c ∈ {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}, φ (x * fin1 (ι c.out))`. Unfold `hopR`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[hR]`. Unfold `hop`. Use `symm`.

Use `finsum_mem_eq_of_bijOn e hbij fun c _ => ?_` and prove the remaining obligations. Establish `hl : (ι c.out)⁻¹ * (e c).out ∈ L` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm`. Use `hφ _ hl (x * fin1 (ι c.out))` as an intermediate fact. Rewrite using `[← this, mul_assoc, ← map_mul, mul_inv_cancel_left]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopEmb :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n), Function.Injective w → IsEmb w ι → ∀ U, Lev U → ∀ φ : G1 K n → ℂ, FixF (levOn (im w) U) φ →
      ∀ g, hop (levOn (im w) U) (ι g) φ = hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ := by
  intro K _ _ n r w ι hw hι U hU φ hφ g
  obtain ⟨hcf, hoff, -, hcomm, hmem⟩ := ((embEx n w hw).2 ι hι).2
  have hcf' : ∀ (v : Pl K), GM.cf v (1 : FA K n) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have := hcf 1 i
      rw [map_one] at this
      rw [this]
      exact Subgroup.one_mem _
    · have := hoff 1 v hv
      rw [map_one] at this
      rw [this]
      exact Subgroup.one_mem _
  have hcf1 : ∀ i, GM.cf (w i) (1 : FA K n) = 1 := by
    intro i
    have := hcf 1 i
    rwa [map_one] at this
  set L := levOn (im w) U with hL
  set W : Subgroup (GS n w) := Subgroup.pi Set.univ fun i => U (w i) with hWdef
  have hWL : ∀ a ∈ W, ι a ∈ L := fun a ha =>
    (hmem U _).2 ⟨a, 1, (mul_one _).symm, fun i => ha i trivial, hcf1, hcf'⟩
  have hLW : ∀ x, ι x ∈ L → x ∈ W := by
    intro x hx
    obtain ⟨a, h', e, ha, h1, -⟩ := (hmem U _).1 hx
    have e' : h' = ι (a⁻¹ * x) := by rw [map_mul, map_inv, e, inv_mul_cancel_left]
    have e1 : a⁻¹ * x = 1 := funext fun i => by
      rw [← hcf (a⁻¹ * x) i, ← e', h1]
      rfl
    rw [(inv_mul_eq_one.1 e1).symm]
    exact fun i _ => ha i
  have hW : CO W :=
    ⟨isCompact_univ_pi fun j => (hU (w j)).1.1, isOpen_set_pi Set.finite_univ fun j _ => (hU (w j)).1.2⟩
  let e : GS n w ⧸ W → FA K n ⧸ L := fun c => QuotientGroup.mk (ι c.out)
  have he : ∀ y, e (QuotientGroup.mk y) = QuotientGroup.mk (ι y) := by
    intro y
    refine QuotientGroup.eq.2 ?_
    have := hWL _ (QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk y : GS n w ⧸ W)))
    rwa [map_mul, map_inv] at this
  have hbij : Set.BijOn e {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}
      {c : FA K n ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * ι g)} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro c ⟨u, hu, rfl⟩
      exact ⟨ι u, hWL u hu, by rw [he, map_mul]⟩
    · intro c _ d _ hcd
      have h1 := QuotientGroup.eq.1 hcd
      rw [← map_inv, ← map_mul] at h1
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
      exact QuotientGroup.eq.2 (hLW _ h1)
    · rintro c ⟨u, hu, rfl⟩
      obtain ⟨a, h', e', ha, h1, h2⟩ := (hmem U _).1 hu
      have hh' : h' ∈ L := (hmem U _).2 ⟨1, h', by simp, fun i => Subgroup.one_mem _, h1, h2⟩
      refine ⟨QuotientGroup.mk (a * g), ⟨a, fun i _ => ha i, rfl⟩, ?_⟩
      rw [he, map_mul, e']
      refine QuotientGroup.eq.2 ?_
      have : (ι a * ι g)⁻¹ * (ι a * h' * ι g) = h' := by
        rw [mul_assoc (ι a) h', (hcomm g h' h1).symm.eq]
        group
      rwa [this]
  have hfin := cosets_finite hW g
  funext x
  have hR : hopR (rS ι) W g φ x = ∑ᶠ c ∈ {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}, φ (x * fin1 (ι c.out)) := by
    unfold hopR
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]
    rfl
  rw [hR]
  unfold hop
  symm
  refine finsum_mem_eq_of_bijOn e hbij fun c _ => ?_
  have hl : (ι c.out)⁻¹ * (e c).out ∈ L := QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  have := hφ _ hl (x * fin1 (ι c.out))
  rw [← this, mul_assoc, ← map_mul, mul_inv_cancel_left]
