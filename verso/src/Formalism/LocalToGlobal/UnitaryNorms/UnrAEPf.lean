import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.UnrAe

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Establish `hz1 : z - 1 ≠ 0` using `sub_ne_zero.mpr hz`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr hz1`. Take `⟨N, hN⟩` from `exists_nat_gt (1 / ‖z - 1‖)`. Establish `hre : ∀ n : ℕ, 1 / 2 < (z ^ n).re` using `fun n => by`.

Establish `h1` using `h n`. Establish `h2 : |(z ^ n - 1).re| ≤ ‖z ^ n - 1‖` using `Complex.abs_re_le_norm _`. Rewrite `h2` using `[Complex.sub_re, Complex.one_re]`. Establish `h3` using `(abs_lt.mp (lt_of_le_of_lt h2 h1)).1`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsum_re : (N : ℝ) * (1 / 2) ≤ (∑ i ∈ Finset.range N, z ^ i).re`. Rewrite using `[Complex.re_sum]`. Establish `h4 : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ ∑ i ∈ Finset.range N, (z ^ i).re` using `Finset.sum_le_sum fun i _ => (hre i).le`. Rewrite `h4` using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Conclude with `h4`.

Establish `hsum_norm : ‖∑ i ∈ Finset.range N, z ^ i‖ < 1 / 2 / ‖z - 1‖`. Rewrite using `[geom_sum_eq hz, norm_div]`. Conclude with `div_lt_div_of_pos_right (h N) hpos`. Establish `h5` using `(hsum_re.trans (Complex.re_le_norm _)).trans_lt hsum_norm`. Establish `h6 : (1 : ℝ) / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) * (1 / 2)` using `by ring`.

Rewrite `h5` using `[h6]`. Establish `h7 : (1 / ‖z - 1‖) * (1 / 2) < (N : ℝ) * (1 / 2)` using `by linarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hre : ∀ n : ℕ, 1 / 2 < (z ^ n).re := fun n => by
    have h1 := h n
    have h2 : |(z ^ n - 1).re| ≤ ‖z ^ n - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    linarith
  have hsum_re : (N : ℝ) * (1 / 2) ≤ (∑ i ∈ Finset.range N, z ^ i).re := by
    rw [Complex.re_sum]
    have h4 : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ ∑ i ∈ Finset.range N, (z ^ i).re :=
      Finset.sum_le_sum fun i _ => (hre i).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    exact h4
  have hsum_norm : ‖∑ i ∈ Finset.range N, z ^ i‖ < 1 / 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz, norm_div]
    exact div_lt_div_of_pos_right (h N) hpos
  have h5 := (hsum_re.trans (Complex.re_le_norm _)).trans_lt hsum_norm
  have h6 : (1 : ℝ) / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) * (1 / 2) := by ring
  rw [h6] at h5
  have h7 : (1 / ‖z - 1‖) * (1 / 2) < (N : ℝ) * (1 / 2) := by linarith
  linarith

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
The claim follows from `Valued.isOpen_valuationSubring _`.
-/
theorem isOpen_integers (v : HeightOneSpectrum (𝓞 L)) : IsOpen ((v.adicCompletionIntegers L : Set (v.adicCompletion L))) :=
  Valued.isOpen_valuationSubring _

/- English proof (translation)
Establish `hσ` using `RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (A := fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) isOpen_integers`. Establish `h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite 1 = 1` using `RestrictedProduct.ext _ _ fun i => rfl`. Establish `h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite ⁻¹' Vf ∈ nhds 1`. Apply `hσ.continuous.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[h1]`.

Conclude with `hV`. Rewrite `h2` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hsub⟩` from `h2`. Use `⟨I, hI, fun v hv y hy => ?_⟩` and prove the remaining obligations. Establish `hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers L : Set (v.adicCompletion L)))) : (i : HeightOneSpectrum (𝓞 L)) → ((i.adicCompletionIntegers L : Set (i.adicCompletion L)))) ∈ I.pi t`.

Introduce `i hi`. Establish `hne : i ≠ v` using `fun e => hv (e ▸ hi)`. Rewrite using `[Pi.mulSingle_eq_of_ne hne]`. Conclude with `mem_of_mem_nhds (ht i)`. Establish `hg` using `hsub hmem`.

Establish `e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) = finiteSingle L v y`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[RestrictedProduct.structureMap_apply]`. Use `show _ = Pi.mulSingle v y i`.

Distinguish the cases in `hi : i = v`. Substitute `hi` using the available equality. Rewrite using `[Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]`. Rewrite using `[Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]`. Both sides reduce to the same expression.

Rewrite using `[← e]`. Conclude with `hg`.
-/
theorem finiteSingle_mem (Vf : Set (FiniteAdeleRing (𝓞 L) L)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 L) L)) :
    ∃ S : Set (HeightOneSpectrum (𝓞 L)), S.Finite ∧ ∀ v, v ∉ S → ∀ y : v.adicCompletion L,
      y ∈ v.adicCompletionIntegers L → finiteSingle L v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
    (A := fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) isOpen_integers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  refine ⟨I, hI, fun v hv y hy => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
      (i : HeightOneSpectrum (𝓞 L)) → ((i.adicCompletionIntegers L : Set (i.adicCompletion L)))) ∈ I.pi t := by
    intro i hi
    have hne : i ≠ v := fun e => hv (e ▸ hi)
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle L v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hx.le`.
-/
theorem mem_integers_of_isUnitAt {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) :
    (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact hx.le

/- English proof (translation)
Unfold `IsUnitAt at *`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]`.
-/
theorem isUnitAt_inv {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : IsUnitAt v x⁻¹ := by
  unfold IsUnitAt at *
  rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]

/- English proof (translation)
Unfold `IsUnitAt at *`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hx, one_pow]`.
-/
theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (n : ℕ) :
    IsUnitAt v (x ^ n) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

/- English proof (translation)
Introduce `χ hχ`. Use `set U : Set (Ideles L) := {a | ‖((χ a : ℂˣ) : ℂ) - 1‖ < 1 / 2} with hUdef`. Establish `hUo : IsOpen U` using `isOpen_lt ((Units.continuous_val.comp hχ).sub continuous_const).norm continuous_const`. Establish `hU1 : (1 : Ideles L) ∈ U` using `by show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1 / 2`. Rewrite using `[map_one, Units.val_one, sub_self, norm_zero]`.

Evaluate the numerical expressions. Take `⟨W, hWo, hWU⟩` from `Units.isInducing_embedProduct.isOpen_iff.mp hUo`. Establish `hW1 : Units.embedProduct _ (1 : Ideles L) ∈ W`. Rewrite using `[← Set.mem_preimage, hWU]`. Conclude with `hU1`.

Rewrite `hW1` using `[map_one]`. Take `⟨W1, hW1n, W2, hW2n, hprod⟩` from `mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)`. Establish `hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 L) L)` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n`. Establish `hV : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L))` using `Filter.inter_mem hW1n hW2'`. Take `⟨Vi, hVi, Vf, hVf, hVprod⟩` from `mem_nhds_prod_iff.mp hV`.

Take `⟨S, hS, hSV⟩` from `finiteSingle_mem Vf hVf`. Establish `key : ∀ v, v ∉ S → ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → localIdele L v x ∈ U`. Introduce `v hv x hx`. Establish `hin : ∀ y : (v.adicCompletion L)ˣ, IsUnitAt v y → ((localIdele L v y : Ideles L) : AdeleRing (𝓞 L) L) ∈ W1 ∩ MulOpposite.op ⁻¹' W2` using `fun y hy => hVprod ⟨mem_of_mem_nhds hVi, hSV v hv _ (mem_integers_of_isUnitAt hy)⟩`. Establish `h1` using `hin x hx`.

Establish `h2` using `hin x⁻¹ (isUnitAt_inv hx)`. Rewrite using `[← hWU, Set.mem_preimage, Units.embedProduct_apply]`. Use `hprod ⟨h1.1, ?_⟩` and prove the remaining obligations. Establish `h3` using `h2.2`. Rewrite `h3` using `[map_inv]`.

Conclude with `h3`. Use `(hS.subset ?_ : {v | ¬ _}.Finite)` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises.

Introduce `x hx`. Establish `hpow : ∀ n : ℕ, ‖((χ (localIdele L v x) : ℂˣ) : ℂ) ^ n - 1‖ < 1 / 2` using `fun n => by`. Establish `h' : ‖((χ (localIdele L v (x ^ n)) : ℂˣ) : ℂ) - 1‖ < 1 / 2` using `key v hvS (x ^ n) (isUnitAt_pow hx n)`. Rewrite `h'` using `[map_pow, map_pow, Units.val_pow_eq_pow_val]`. Then use the resulting hypothesis. Conclude with `Units.ext (eq_one_of_pow_near hpow)`.
-/
theorem unrAE (L : Type) [Field L] [NumberField L] : UnrAE L := by
  intro χ hχ
  set U : Set (Ideles L) := {a | ‖((χ a : ℂˣ) : ℂ) - 1‖ < 1 / 2} with hUdef
  have hUo : IsOpen U :=
    isOpen_lt ((Units.continuous_val.comp hχ).sub continuous_const).norm continuous_const
  have hU1 : (1 : Ideles L) ∈ U := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1 / 2
    rw [map_one, Units.val_one, sub_self, norm_zero]
    norm_num
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hUo
  have hW1 : Units.embedProduct _ (1 : Ideles L) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact hU1
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 L) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hV : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨S, hS, hSV⟩ := finiteSingle_mem Vf hVf
  have key : ∀ v, v ∉ S → ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → localIdele L v x ∈ U := by
    intro v hv x hx
    have hin : ∀ y : (v.adicCompletion L)ˣ, IsUnitAt v y →
        ((localIdele L v y : Ideles L) : AdeleRing (𝓞 L) L) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy =>
      hVprod ⟨mem_of_mem_nhds hVi, hSV v hv _ (mem_integers_of_isUnitAt hy)⟩
    have h1 := hin x hx
    have h2 := hin x⁻¹ (isUnitAt_inv hx)
    rw [← hWU, Set.mem_preimage, Units.embedProduct_apply]
    refine hprod ⟨h1.1, ?_⟩
    have h3 := h2.2
    rw [map_inv] at h3
    exact h3
  refine (hS.subset ?_ : {v | ¬ _}.Finite)
  intro v hv
  by_contra hvS
  apply hv
  intro x hx
  have hpow : ∀ n : ℕ, ‖((χ (localIdele L v x) : ℂˣ) : ℂ) ^ n - 1‖ < 1 / 2 := fun n => by
    have h' : ‖((χ (localIdele L v (x ^ n)) : ℂˣ) : ℂ) - 1‖ < 1 / 2 := key v hvS (x ^ n) (isUnitAt_pow hx n)
    rwa [map_pow, map_pow, Units.val_pow_eq_pow_val] at h'
  exact Units.ext (eq_one_of_pow_near hpow)

end Formalism.L2.Host
