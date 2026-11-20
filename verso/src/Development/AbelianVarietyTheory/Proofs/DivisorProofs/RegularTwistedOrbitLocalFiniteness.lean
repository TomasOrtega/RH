import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.LocFin

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/- English proof (translation)
Introduce `g hg`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨hg.1, ?_⟩` and prove the remaining obligations. Establish `hzp : (Subgroup.zpowers g : Set G) ⊆ K` using `(Subgroup.zpowers_le (G := G) (H := K)).2 hg.2`. Conclude with `hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)`.
-/
theorem inf_le_cptPart (T K : Subgroup G) (hK : IsCompact (K : Set G)) : T ⊓ K ≤ cptPart T := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.1, ?_⟩
  have hzp : (Subgroup.zpowers g : Set G) ⊆ K := (Subgroup.zpowers_le (G := G) (H := K)).2 hg.2
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)

/- English proof (translation)
Rewrite using `[Subgroup.coe_map]`. Establish `hc : Continuous fun a : G => x * a * x⁻¹` using `by fun_prop`. Conclude with `hK.image hc`.
-/
theorem isCompact_map_conj (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  exact hK.image hc

/- English proof (translation)
Rewrite using `[Subgroup.coe_map]`. Conclude with `(Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK`.
-/
theorem isOpen_map_conj (K : Subgroup G) (hK : IsOpen (K : Set G)) (x : G) :
    IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK

/- English proof (translation)
Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH`. Establish `ho : IsOpen ((A.subgroupOf H : Subgroup H) : Set H)` using `hA.preimage continuous_subtype_val`. Use `haveI := Subgroup.quotient_finite_of_isOpen _ ho`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_isOpen (A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) :
    A.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have ho : IsOpen ((A.subgroupOf H : Subgroup H) : Set H) := hA.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Establish `hPT : cptPart T ≤ T`. Rewrite using `[cptPart, Subgroup.closure_le]`. Conclude with `fun t ht => ht.1`. Establish `e : (T ⊓ A) ⊓ cptPart T = A ⊓ cptPart T`. Use extensionality with `g`.

Simplify using `only [Subgroup.mem_inf]`. Conclude with `⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hPT h.2, h.1⟩, h.2⟩⟩`. Rewrite using `[← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]`. Establish `h1` using `relIndex_ne_zero_of_isOpen A H hA hH`. Establish `: (A.subgroupOf H).FiniteIndex` using `⟨h1⟩`.

Establish `: Finite (cptPart T ⧸ A.subgroupOf (cptPart T))` using `Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE A hTH).injective`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_cptPart_ne_zero (T A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G))
    (hTH : cptPart T ≤ H) : (T ⊓ A).relIndex (cptPart T) ≠ 0 := by
  have hPT : cptPart T ≤ T := by
    rw [cptPart, Subgroup.closure_le]; exact fun t ht => ht.1
  have e : (T ⊓ A) ⊓ cptPart T = A ⊓ cptPart T := by
    ext g; simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hPT h.2, h.1⟩, h.2⟩⟩
  rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
  have h1 := relIndex_ne_zero_of_isOpen A H hA hH
  have : (A.subgroupOf H).FiniteIndex := ⟨h1⟩
  have : Finite (cptPart T ⧸ A.subgroupOf (cptPart T)) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE A hTH).injective
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Take `⟨s, hs⟩` from `compact_covered_by_mul_left_translates hD (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)`. Use `(s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨t, ht, d, hd, hx⟩` from `hP _ hq`. Use `hs hd` as an intermediate fact.

Simplify using `only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this`. Take `⟨g, hg, hgd⟩` from `this`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]`. Conclude with `⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩`.
-/
theorem finite_of_subset_mul (T K' : Subgroup G) (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

end Generic

section Main

/- English proof (translation)
The claim follows from `GlobalTheory.T.continuous_involutive_local_transpose_inverse`.
-/
theorem hKT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := GlobalTheory.T.continuous_involutive_local_transpose_inverse

/- English proof (translation)
The claim follows from `GlobalTheory.T.orbit_compact_mod_centralizer_separable_local`.
-/
theorem hKPa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer`.
-/
theorem hKA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer

/- English proof (translation)
The claim follows from `GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul`.
-/
theorem hKPb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Distinguish the cases in `hs : IsSplitAt w`. Establish `h1 : thL n w = MonoidHom.id _` using `by rw [thL, if_pos hs]`. Simplify using `only [nrmL, if_pos hs, h1, MonoidHom.id_apply]`. Establish `h1 : thL n w = thetaGL n (cj w)` using `by rw [thL, if_neg hs]`. Establish `h2` using `(hKT E hU n w).2`.

Rewrite `h2` using `[h1]`. Simplify using `only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]`. Use `group`.
-/
theorem nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (hKT E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

/- English proof (translation)
Distinguish the cases in `hs : IsSplitAt w`. Establish `e : nrmL n w = fun u => u` using `funext fun u => by simp [nrmL, hs]`. Rewrite using `[e]`. Conclude with `continuous_id`. Establish `h1 : thL n w = thetaGL n (cj w)` using `by rw [thL, if_neg hs]`.

Establish `hc` using `(hKT E hU n w).1`. Rewrite `hc` using `[h1]`. Establish `e : nrmL n w = fun u => u * thetaGL n (cj w) u` using `funext fun u => by simp [nrmL, hs]`. Rewrite using `[e]`. Conclude with `continuous_id.mul hc`.
-/
theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (hKT E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

/- English proof (translation)
Establish `hθ` using `(hKT E hU n w).1`. Take `⟨D₁, hD₁, h₁⟩` from `hKPa E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL hU n w))`. Use `set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)`. Establish `hC₂ : IsCompact C₂` using `(hD₁.prod (hC.prod hD₁)).image (by fun_prop)`. Take `⟨D₂, hD₂, h₂⟩` from `hKPb E hU n w y hy C₂ hC₂`.

Use `⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨z, hz, d, hd, rfl⟩` from `h₁ x ⟨_, hx, by rw [nrmL_twConj hU]⟩`. Establish `hz2 : z⁻¹ * y * thL n w z ∈ C₂` using `⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by`. Simplify using `only [map_mul]`.

Use the proof step `group⟩`. Take `⟨t, ht, d₂, hd₂, rfl⟩` from `h₂ z hz hz2`. Conclude with `⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩`.
-/
theorem proper (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (hKT E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := hKPa E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := hKPb E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

/- English proof (translation)
Introduce `E _ _ _ hU n w y hy K' hK'`. Take `⟨hK'o, hK'K, -⟩` from `hK'`. Take `⟨hKo, hKc⟩` from `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n`. Take `⟨H, hH, hPH⟩` from `hKA E hU n w y hy`. Use `⟨fun x => ⟨inf_le_cptPart _ _ (isCompact_map_conj _ hKc x), relIndex_cptPart_ne_zero _ _ H (isOpen_map_conj _ hK'o x) hH hPH⟩, fun C hC => ?_⟩` and prove the remaining obligations.

Take `⟨D, hD, hP⟩` from `proper hU n w y hy C hC`. Conclude with `finite_of_subset_mul _ K' hK'o D hD _ hP`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ K' : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K' → (∀ x : GLw n w, twCent (thL n w) y ⊓ (GlobalTheory.LFun.KGL w n).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (thL n w) y) ∧ (twCent (thL n w) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL n w) y)) ≠ 0) ∧ ∀ C : Set (GLw n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (thL n w) y : Set (GLw n w)) (K' : Set (GLw n w)) | (Quotient.out q)⁻¹ * y * thL n w (Quotient.out q) ∈ C}.Finite := by
  intro E _ _ _ hU n w y hy K' hK'
  obtain ⟨hK'o, hK'K, -⟩ := hK'
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  obtain ⟨H, hH, hPH⟩ := hKA E hU n w y hy
  refine ⟨fun x => ⟨inf_le_cptPart _ _ (isCompact_map_conj _ hKc x),
    relIndex_cptPart_ne_zero _ _ H (isOpen_map_conj _ hK'o x) hH hPH⟩, fun C hC => ?_⟩
  obtain ⟨D, hD, hP⟩ := proper hU n w y hy C hC
  exact finite_of_subset_mul _ K' hK'o D hD _ hP

end Main

end GlobalTheory.LocFin
