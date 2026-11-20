import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.EisTestK

/- English proof (translation)
Establish `hcont : Tendsto (fun x : K₀ × K₀ => x.1 * x.2⁻¹) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)`. Establish `h : Continuous (fun x : K₀ × K₀ => x.1 * x.2⁻¹)` using `by fun_prop`. Use `h.tendsto ((1 : K₀), (1 : K₀))` as an intermediate fact. Simplify `this` using `[nhds_prod_eq]`. Take `⟨W, hW, hWN⟩` from `Filter.mem_prod_self_iff.1 (hcont hN)`.

Establish `hjW : j ⁻¹' W ∈ 𝓝 (1 : K)` using `hj.continuousAt.preimage_mem_nhds (by simpa using hW)`. Take `⟨V₀, hV₀sub, hV₀o, h1⟩` from `mem_nhds_iff.1 (Filter.inter_mem hV hjW)`. Set `Q : Subgroup K` to `S.comap j`. Set `A : Set K` to `(Q : Set K) * V₀`. Establish `hAo : IsOpen A` using `hV₀o.mul_left`.

Establish `hC : IsCompact (j '' Aᶜ)` using `(hAo.isClosed_compl.isCompact).image hj`. Establish `hScpt : IsCompact (S : Set K₀)` using `hS.isCompact`. Set `T : Set K₀` to `(S : Set K₀) * (j '' Aᶜ)`. Establish `hT : IsCompact T` using `hScpt.mul hC`. Establish `h1T : (1 : K₀) ∉ T`.

Introduce and unpack `⟨p, hp, c, ⟨x, hx, rfl⟩, hpc⟩`. Apply `hx` to reduce the goal to its premises. Establish `hjx : j x ∈ S`. Establish `: j x = p⁻¹` using `eq_inv_of_mul_eq_one_right hpc`. Rewrite using `[this]`.

Conclude with `S.inv_mem hp`. Conclude with `⟨x, hjx, 1, h1, by simp⟩`. Use `⟨W ∩ Tᶜ, Filter.inter_mem hW (hT.isClosed.isOpen_compl.mem_nhds h1T), ?_⟩` and prove the remaining obligations. Introduce `κ p u hp hu hκ`. Distinguish the cases in `hκA : κ ∈ A`.

Take `⟨r, hr, v, hv, rfl⟩` from `hκA`. Use `⟨r, v, hr, (hV₀sub hv).1, rfl, fun u' hu' => ?_⟩` and prove the remaining obligations. Conclude with `hWN (Set.mk_mem_prod (hV₀sub hv).2 hu'.1)`. It suffices to derive a contradiction. Apply `hu.2` to reduce the goal to its premises.

Use `⟨p⁻¹, S.inv_mem hp, j κ, ⟨κ, hκA, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[hκ]`.
-/
theorem nhd_choice {K K₀ : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [Group K₀] [TopologicalSpace K₀] [IsTopologicalGroup K₀] [CompactSpace K₀] [T2Space K₀]
    (j : K →* K₀) (hj : Continuous j) (S : Subgroup K₀) (hS : IsClosed (S : Set K₀))
    (N₁ : Set K₀) (hN : N₁ ∈ 𝓝 (1 : K₀)) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∃ U ∈ 𝓝 (1 : K₀), ∀ (κ : K) (p u : K₀), p ∈ S → u ∈ U → j κ = p * u →
      ∃ r v : K, j r ∈ S ∧ v ∈ V ∧ κ = r * v ∧ ∀ u' ∈ U, j v * u'⁻¹ ∈ N₁ := by
  have hcont : Tendsto (fun x : K₀ × K₀ => x.1 * x.2⁻¹) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1) := by
    have h : Continuous (fun x : K₀ × K₀ => x.1 * x.2⁻¹) := by fun_prop
    have := h.tendsto ((1 : K₀), (1 : K₀))
    simpa [nhds_prod_eq] using this
  obtain ⟨W, hW, hWN⟩ := Filter.mem_prod_self_iff.1 (hcont hN)
  have hjW : j ⁻¹' W ∈ 𝓝 (1 : K) := hj.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨V₀, hV₀sub, hV₀o, h1⟩ := mem_nhds_iff.1 (Filter.inter_mem hV hjW)
  let Q : Subgroup K := S.comap j
  let A : Set K := (Q : Set K) * V₀
  have hAo : IsOpen A := hV₀o.mul_left
  have hC : IsCompact (j '' Aᶜ) := (hAo.isClosed_compl.isCompact).image hj
  have hScpt : IsCompact (S : Set K₀) := hS.isCompact
  let T : Set K₀ := (S : Set K₀) * (j '' Aᶜ)
  have hT : IsCompact T := hScpt.mul hC
  have h1T : (1 : K₀) ∉ T := by
    rintro ⟨p, hp, c, ⟨x, hx, rfl⟩, hpc⟩
    apply hx
    have hjx : j x ∈ S := by
      have : j x = p⁻¹ := eq_inv_of_mul_eq_one_right hpc
      rw [this]; exact S.inv_mem hp
    exact ⟨x, hjx, 1, h1, by simp⟩
  refine ⟨W ∩ Tᶜ, Filter.inter_mem hW (hT.isClosed.isOpen_compl.mem_nhds h1T), ?_⟩
  intro κ p u hp hu hκ
  by_cases hκA : κ ∈ A
  · obtain ⟨r, hr, v, hv, rfl⟩ := hκA
    refine ⟨r, v, hr, (hV₀sub hv).1, rfl, fun u' hu' => ?_⟩
    exact hWN (Set.mk_mem_prod (hV₀sub hv).2 hu'.1)
  · exfalso
    apply hu.2
    refine ⟨p⁻¹, S.inv_mem hp, j κ, ⟨κ, hκA, rfl⟩, ?_⟩
    simp [hκ]

section Concrete

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

/- English proof (translation)
Introduce `r hr c hc`. Establish `hrc : r ≠ c` using `fun h => hr (h ▸ hc)`. Conclude with `⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩`.
-/
theorem dgl_mem_stab (d : ι → IdeleGroup k) (i : ι) : dgl d ∈ stab 𝔸[k] ({i} : Set ι) := by
  intro r hr c hc
  have hrc : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩

/- English proof (translation)
Establish `hD` using `dgl_mem_stab d i`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e : π g = dgl d * kap π d g * (dgl d)⁻¹` using `by simp [kap, mul_assoc]`. Rewrite using `[e]`.

Conclude with `mul_mem (mul_mem hD h) (inv_mem hD)`. Introduce `h`. Conclude with `mul_mem (mul_mem (inv_mem hD) h) hD`.
-/
theorem kap_mem_stab_iff (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    kap π d g ∈ stab 𝔸[k] ({i} : Set ι) ↔ π g ∈ stab 𝔸[k] ({i} : Set ι) := by
  have hD := dgl_mem_stab d i
  constructor
  · intro h
    have e : π g = dgl d * kap π d g * (dgl d)⁻¹ := by simp [kap, mul_assoc]
    rw [e]
    exact mul_mem (mul_mem hD h) (inv_mem hD)
  · intro h
    exact mul_mem (mul_mem (inv_mem hD) h) hD

/- English proof (translation)
Unfold `bdet`. Use `split_ifs with h1 h2 h2`. Conclude with `Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])`. Conclude with `absurd (by rwa [h] at h1) h2`. Conclude with `absurd (by rwa [← h] at h2) h1`.

Both sides reduce to the same expression.
-/
theorem bdet_congr {R : Type} [CommRing R] {s : Set ι} {g g' : GL ι R}
    (h : (g : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      (g' : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) : bdet s g = bdet s g' := by
  unfold bdet
  split_ifs with h1 h2 h2
  · exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])
  · exact absurd (by rwa [h] at h1) h2
  · exact absurd (by rwa [← h] at h2) h1
  · rfl

/- English proof (translation)
Apply `bdet_congr` to reduce the goal to its premises. Use extensionality with `⟨a, ha⟩ ⟨b, hb⟩`. Take `rfl : a = i` from `ha`. Take `rfl : b = a` from `hb`. Establish `e : (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])` using `rfl`.

Establish `e' : ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (d i : 𝔸[k])` using `rfl`. Simplify using `only [Matrix.submatrix_apply, kap, Units.val_mul, e, e', Matrix.mul_diagonal, Matrix.diagonal_mul]`. Rewrite using `[mul_right_comm, Units.inv_mul, one_mul]`.
-/
theorem bdet_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    bdet ({i} : Set ι) (kap π d g) = bdet ({i} : Set ι) (π g) := by
  apply bdet_congr
  ext ⟨a, ha⟩ ⟨b, hb⟩
  obtain rfl : a = i := ha
  obtain rfl : b = a := hb
  have e : (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) =
      Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) := rfl
  have e' : ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (d i : 𝔸[k]) := rfl
  simp only [Matrix.submatrix_apply, kap, Units.val_mul, e, e', Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, Units.inv_mul, one_mul]

end Concrete

/- English proof (translation)
Introduce `hStd hB hT G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hSide V hV`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Use `haveI : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.1 ((hStd k).kcpt ι)`. Take `⟨hcl, hmul, hcb, -, -, -⟩` from `hB k 𝔸[k] (adStd k) (hStd k) ι ({i} : Set ι)`. Set `j : K →* (adStd k).kGL ι` to `{ toFun := fun κ => ⟨kap π d κ, hSide.piK κ κ.2⟩ map_one' := by apply Subtype.ext; simp [kap] map_mul' := fun a b => by apply Subtype.ext; simp [kap, mul_assoc] }`.

Establish `hj : Continuous j`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Unfold `kap`. Conclude with `(continuous_const.mul (hSide.cont.comp continuous_subtype_val)).mul continuous_const`. Set `S : Subgroup ((adStd k).kGL ι)` to `(stab 𝔸[k] ({i} : Set ι)).comap ((adStd k).kGL ι).subtype`.

Establish `hS : IsClosed (S : Set ((adStd k).kGL ι))` using `hcl.preimage continuous_subtype_val`. Establish `hb1 : bdet ({i} : Set ι) (1 : GL ι 𝔸[k]) = 1`. Use `hmul 1 (one_mem _) 1 (one_mem _)` as an intermediate fact. Simplify using `using this`. Set `f : (adStd k).kGL ι → ℂ` to `fun p => (ω.toIdele (bdet ({i} : Set ι) p.1) : ℂ)`.

Establish `hf1 : f 1 = 1` using `by show (ω.toIdele (bdet ({i} : Set ι) (1 : GL ι 𝔸[k])) : ℂ) = 1`. Rewrite using `[hb1]`. Simplify using `[HeckeCharacter.toIdele_apply]`. Establish `hfc : ContinuousOn f (S : Set ((adStd k).kGL ι))`. Establish `h1 : ContinuousOn (fun p : (adStd k).kGL ι => bdet ({i} : Set ι) p.1) (S : Set ((adStd k).kGL ι))` using `hcb.comp continuous_subtype_val.continuousOn fun p hp => hp`.

Conclude with `continuous_subtype_val.comp_continuousOn (ω.continuous_toIdele.comp_continuousOn h1)`. Choose the witnesses or unpack the hypotheses as in `⟨N₁, hN₁, hNf⟩ : ∃ N₁ ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ p ∈ S, p ∈ N₁ → ‖f p - 1‖ ≤ 1 / 4 := by`. Establish `h` using `hfc 1 (one_mem S)`. Establish `hm : f ⁻¹' Metric.closedBall 1 (1 / 4) ∈ 𝓝[(S : Set ((adStd k).kGL ι))] (1 : (adStd k).kGL ι)` using `h (by rw [hf1]; exact Metric.closedBall_mem_nhds _ (by norm_num))`. Take `⟨u, huo, hu1, hus⟩` from `mem_nhdsWithin.1 hm`.

Use `⟨u, huo.mem_nhds hu1, fun p hp hpu => ?_⟩` and prove the remaining obligations. Use `hus ⟨hpu, hp⟩` as an intermediate fact. Simplify `this` using `[dist_eq_norm]`. Take `⟨U, hU, hUmain⟩` from `nhd_choice j hj S hS N₁ hN₁ V hV`. Take `⟨Ψ, Ψ₁, ψ, hΨ, hΨ₁, hψc, hψ1, hfac, hsupp, hlaw, hz, hone⟩` from `hT k ι i ω hSide.sq U hU`.

Use `⟨Ψ, Ψ₁, ψ ∘ j, hΨ, hΨ₁, hψc.comp hj, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hψ1`. Introduce `r κ hr`. Establish `hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι)` using `(kap_mem_stab_iff π d i r).2 ((hSide.mem _).1 hr)`. Use `show ψ (j (r * κ)) = c r * ψ (j κ)`.

Rewrite using `[map_mul, hlaw _ _ hrS, (hSide.val _ hr).1]`. Rewrite using `[show (j r).1 = kap π d r from rfl, bdet_kap]`. Introduce `κ hκ`. Take `⟨p, hp, u, hu, hκe, -⟩` from `hsupp (j κ) hκ`. Take `⟨r, v, hr, hv, rfl, hvN⟩` from `hUmain κ p u hp hu hκe`.

Establish `hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι)` using `hr`. Establish `hrP : (r : G) ∈ P` using `(hSide.mem _).2 ((kap_mem_stab_iff π d i r).1 hr)`. Use `⟨r, v, hrP, hv, rfl, ?_⟩` and prove the remaining obligations. Establish `hl` using `hlaw (j r) (j v) hrS`. Establish `hφv : ψ (j v) ≠ 0` using `fun h => hκ (by show ψ (j (r * v)) = 0`.

Rewrite using `[map_mul, hl, h, mul_zero])`. Take `⟨p', hp', u', hu', hve, hval⟩` from `hsupp (j v) hφv`. Establish `hpN : p' ∈ N₁`. Use `hvN u' hu'` as an intermediate fact. Rewrite `this` using `[hve, mul_inv_cancel_right]`. Then use the resulting hypothesis.

Establish `hb : ‖f p' - 1‖ ≤ 1 / 4` using `hNf p' hp' hpN`. Use `show ‖ψ (j v) - (‖ψ (j v)‖ : ℂ)‖ ≤ ‖ψ (j v)‖ / 4`. Generalize the expression as in `ψ (j v) = a at hval`. Establish `e : a - (‖a‖ : ℂ) = (f p' - 1) * (‖a‖ : ℂ)`. Rewrite using `[sub_mul, one_mul]`.

Conclude with `congrArg (· - (‖a‖ : ℂ)) hval`. Rewrite using `[e, norm_mul, Complex.norm_real, norm_norm]`. Use polynomial arithmetic with `[norm_nonneg a]`. Introduce `s κ show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) ω s = globalZeta (fun t => Ψ₁ fun _ => t) ω s * ψ (j κ)`. Establish `hfun : (fun t => Ψ (t • vec (kap π d κ) i)) = fun t => (Ψ₁ fun _ => t) * ψ (j κ)`.

Use function extensionality and compare the values at `fun t => hfac t (j κ)`. Rewrite using `[hfun]`. Unfold `globalZeta`. Rewrite using `[← integral_mul_const]`. Use `congr 1`.

Use extensionality with `x`. Expand and normalize the polynomial expressions, which then agree. Take `⟨z, hz1, hz2⟩` from `hz`. Conclude with `⟨z, by linarith, hz2⟩`. Conclude with `hone`.
-/
theorem testK : StdGood → BdetLaw → TestFun → TestK := by
  intro hStd hB hT G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hSide V hV
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.1 ((hStd k).kcpt ι)
  obtain ⟨hcl, hmul, hcb, -, -, -⟩ := hB k 𝔸[k] (adStd k) (hStd k) ι ({i} : Set ι)
  let j : K →* (adStd k).kGL ι :=
    { toFun := fun κ => ⟨kap π d κ, hSide.piK κ κ.2⟩
      map_one' := by apply Subtype.ext; simp [kap]
      map_mul' := fun a b => by apply Subtype.ext; simp [kap, mul_assoc] }
  have hj : Continuous j := by
    refine Continuous.subtype_mk ?_ _
    unfold kap
    exact (continuous_const.mul (hSide.cont.comp continuous_subtype_val)).mul continuous_const
  let S : Subgroup ((adStd k).kGL ι) := (stab 𝔸[k] ({i} : Set ι)).comap ((adStd k).kGL ι).subtype
  have hS : IsClosed (S : Set ((adStd k).kGL ι)) := hcl.preimage continuous_subtype_val
  have hb1 : bdet ({i} : Set ι) (1 : GL ι 𝔸[k]) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  let f : (adStd k).kGL ι → ℂ := fun p => (ω.toIdele (bdet ({i} : Set ι) p.1) : ℂ)
  have hf1 : f 1 = 1 := by
    show (ω.toIdele (bdet ({i} : Set ι) (1 : GL ι 𝔸[k])) : ℂ) = 1
    rw [hb1]
    simp [HeckeCharacter.toIdele_apply]
  have hfc : ContinuousOn f (S : Set ((adStd k).kGL ι)) := by
    have h1 : ContinuousOn (fun p : (adStd k).kGL ι => bdet ({i} : Set ι) p.1) (S : Set ((adStd k).kGL ι)) :=
      hcb.comp continuous_subtype_val.continuousOn fun p hp => hp
    exact continuous_subtype_val.comp_continuousOn (ω.continuous_toIdele.comp_continuousOn h1)
  obtain ⟨N₁, hN₁, hNf⟩ : ∃ N₁ ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ p ∈ S, p ∈ N₁ → ‖f p - 1‖ ≤ 1 / 4 := by
    have h := hfc 1 (one_mem S)
    have hm : f ⁻¹' Metric.closedBall 1 (1 / 4) ∈ 𝓝[(S : Set ((adStd k).kGL ι))] (1 : (adStd k).kGL ι) :=
      h (by rw [hf1]; exact Metric.closedBall_mem_nhds _ (by norm_num))
    obtain ⟨u, huo, hu1, hus⟩ := mem_nhdsWithin.1 hm
    refine ⟨u, huo.mem_nhds hu1, fun p hp hpu => ?_⟩
    have := hus ⟨hpu, hp⟩
    simpa [dist_eq_norm] using this
  obtain ⟨U, hU, hUmain⟩ := nhd_choice j hj S hS N₁ hN₁ V hV
  obtain ⟨Ψ, Ψ₁, ψ, hΨ, hΨ₁, hψc, hψ1, hfac, hsupp, hlaw, hz, hone⟩ := hT k ι i ω hSide.sq U hU
  refine ⟨Ψ, Ψ₁, ψ ∘ j, hΨ, hΨ₁, hψc.comp hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hψ1
  · intro r κ hr
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := (kap_mem_stab_iff π d i r).2 ((hSide.mem _).1 hr)
    show ψ (j (r * κ)) = c r * ψ (j κ)
    rw [map_mul, hlaw _ _ hrS, (hSide.val _ hr).1]
    rw [show (j r).1 = kap π d r from rfl, bdet_kap]
  · intro κ hκ
    obtain ⟨p, hp, u, hu, hκe, -⟩ := hsupp (j κ) hκ
    obtain ⟨r, v, hr, hv, rfl, hvN⟩ := hUmain κ p u hp hu hκe
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := hr
    have hrP : (r : G) ∈ P := (hSide.mem _).2 ((kap_mem_stab_iff π d i r).1 hr)
    refine ⟨r, v, hrP, hv, rfl, ?_⟩
    have hl := hlaw (j r) (j v) hrS
    have hφv : ψ (j v) ≠ 0 := fun h => hκ (by
      show ψ (j (r * v)) = 0
      rw [map_mul, hl, h, mul_zero])
    obtain ⟨p', hp', u', hu', hve, hval⟩ := hsupp (j v) hφv
    have hpN : p' ∈ N₁ := by
      have := hvN u' hu'
      rwa [hve, mul_inv_cancel_right] at this
    have hb : ‖f p' - 1‖ ≤ 1 / 4 := hNf p' hp' hpN
    show ‖ψ (j v) - (‖ψ (j v)‖ : ℂ)‖ ≤ ‖ψ (j v)‖ / 4
    generalize ψ (j v) = a at hval
    have e : a - (‖a‖ : ℂ) = (f p' - 1) * (‖a‖ : ℂ) := by
      rw [sub_mul, one_mul]
      exact congrArg (· - (‖a‖ : ℂ)) hval
    rw [e, norm_mul, Complex.norm_real, norm_norm]
    nlinarith [norm_nonneg a]
  · intro s κ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) ω s = globalZeta (fun t => Ψ₁ fun _ => t) ω s * ψ (j κ)
    have hfun : (fun t => Ψ (t • vec (kap π d κ) i)) = fun t => (Ψ₁ fun _ => t) * ψ (j κ) :=
      funext fun t => hfac t (j κ)
    rw [hfun]
    unfold globalZeta
    rw [← integral_mul_const]
    congr 1
    ext x
    ring
  · obtain ⟨z, hz1, hz2⟩ := hz
    exact ⟨z, by linarith, hz2⟩
  · exact hone

end GlobalTheory.CompanionTheory.EisTestK
