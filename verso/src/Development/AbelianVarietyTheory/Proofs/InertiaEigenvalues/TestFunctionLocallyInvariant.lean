import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.RowSmooth

/- English proof (translation)
Introduce `R _ _ _ T hT`. Take `⟨V, hV, hVT⟩` from `GlobalTheory.TestFn.unif_const (R × R) T hT`. Establish `hC : IsCompact (tsupport T)` using `hT.2`. Set `φ : (R × R × R × R) → R × R → R × R` to `fun e v => (v.1 * e.1 + v.2 * e.2.2.1, v.1 * e.2.1 + v.2 * e.2.2.2)`. Establish `hφ : Continuous (fun z : (R × R × R × R) × (R × R) => φ z.1 z.2)`.

Simplify using `only [φ]`. Use `fun_prop`. Establish `hev : ∀ᶠ e in 𝓝 (0 : R × R × R × R), ∀ v ∈ tsupport T, φ e v ∈ V`. Use `hC.eventually_forall_of_forall_eventually (P := fun e v => φ e v ∈ V) ?_` and prove the remaining obligations. Introduce `v _`.

Establish `h0 : φ 0 v = 0` using `by simp [φ]`. Establish `: V ∈ 𝓝 (φ (0 : R × R × R × R) v)` using `by rw [h0]; exact hV`. Conclude with `hφ.continuousAt (x := ((0 : R × R × R × R), v)) this`. Take `⟨A₁, hA₁, S₁, hS₁, hsub₁⟩` from `mem_nhds_prod_iff.mp (show _ ∈ 𝓝 ((0 : R), ((0 : R), (0 : R), (0 : R))) from hev)`. Take `⟨A₂, hA₂, S₂, hS₂, hsub₂⟩` from `mem_nhds_prod_iff.mp hS₁`.

Take `⟨A₃, hA₃, A₄, hA₄, hsub₃⟩` from `mem_nhds_prod_iff.mp hS₂`. Use `set U₀ : Set R := A₁ ∩ A₂ ∩ A₃ ∩ A₄ with hU₀def`. Establish `hU₀ : U₀ ∈ 𝓝 (0 : R)` using `inter_mem (inter_mem (inter_mem hA₁ hA₂) hA₃) hA₄`. Establish `key : ∀ a b c d : R, a ∈ U₀ → b ∈ U₀ → c ∈ U₀ → d ∈ U₀ → ∀ v ∈ tsupport T, T (v + φ (a, b, c, d) v) = T v`. Introduce `a b c d ha hb hc hd v hv`.

Establish `hmem : ((a, b, c, d) : R × R × R × R) ∈ {e | ∀ v ∈ tsupport T, φ e v ∈ V}` using `hsub₁ ⟨ha.1.1.1, hsub₂ ⟨hb.1.1.2, hsub₃ ⟨hc.1.2, hd.2⟩⟩⟩`. Conclude with `hVT v _ (hmem v hv)`. Use `⟨U₀ ∩ (fun x => -x) ⁻¹' U₀, inter_mem hU₀ (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₀)), ?_⟩` and prove the remaining obligations. Introduce `k hk c u`. Establish `hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1`.

Use `k.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `this`. Establish `e00` using `hk 0 0`. Establish `e01` using `hk 0 1`.

Establish `e10` using `hk 1 0`. Establish `e11` using `hk 1 1`. Simplify using `only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at e00 e01 e10 e11`. Distinguish the cases in `hv : (c, u) ∈ tsupport T`. Use `key (k 0 0 - 1) (k 0 1) (k 1 0) (k 1 1 - 1) e00.1 e01.1 e10.1 e11.1 (c, u) hv` as an intermediate fact.

Rewrite using `[← this]`. Use `congr 1`. Simplify using `only [φ, Prod.mk_add_mk]`. Apply the tactic sequence `ext <;> simp <;> ring`. Distinguish the cases in `hw : (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) ∈ tsupport T`.

Use `key (k 1 1 - 1) (-k 0 1) (-k 1 0) (k 0 0 - 1) e11.1 e01.2 e10.2 e00.1 _ hw` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Simplify using `only [φ, Prod.mk_add_mk]`. Use `ext`.

Simplify using the standard rewrite rules. Take the linear combination `c * hdet`. Simplify using the standard rewrite rules. Take the linear combination `u * hdet`. Rewrite using `[image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]`.
-/
theorem row_smooth : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  intro R _ _ _ T hT
  classical
  obtain ⟨V, hV, hVT⟩ := GlobalTheory.TestFn.unif_const (R × R) T hT
  have hC : IsCompact (tsupport T) := hT.2
  let φ : (R × R × R × R) → R × R → R × R := fun e v =>
    (v.1 * e.1 + v.2 * e.2.2.1, v.1 * e.2.1 + v.2 * e.2.2.2)
  have hφ : Continuous (fun z : (R × R × R × R) × (R × R) => φ z.1 z.2) := by
    simp only [φ]; fun_prop
  have hev : ∀ᶠ e in 𝓝 (0 : R × R × R × R), ∀ v ∈ tsupport T, φ e v ∈ V := by
    refine hC.eventually_forall_of_forall_eventually (P := fun e v => φ e v ∈ V) ?_
    intro v _
    have h0 : φ 0 v = 0 := by simp [φ]
    have : V ∈ 𝓝 (φ (0 : R × R × R × R) v) := by rw [h0]; exact hV
    exact hφ.continuousAt (x := ((0 : R × R × R × R), v)) this
  obtain ⟨A₁, hA₁, S₁, hS₁, hsub₁⟩ := mem_nhds_prod_iff.mp (show _ ∈ 𝓝 ((0 : R), ((0 : R), (0 : R), (0 : R))) from hev)
  obtain ⟨A₂, hA₂, S₂, hS₂, hsub₂⟩ := mem_nhds_prod_iff.mp hS₁
  obtain ⟨A₃, hA₃, A₄, hA₄, hsub₃⟩ := mem_nhds_prod_iff.mp hS₂
  set U₀ : Set R := A₁ ∩ A₂ ∩ A₃ ∩ A₄ with hU₀def
  have hU₀ : U₀ ∈ 𝓝 (0 : R) := inter_mem (inter_mem (inter_mem hA₁ hA₂) hA₃) hA₄
  have key : ∀ a b c d : R, a ∈ U₀ → b ∈ U₀ → c ∈ U₀ → d ∈ U₀ → ∀ v ∈ tsupport T,
      T (v + φ (a, b, c, d) v) = T v := by
    intro a b c d ha hb hc hd v hv
    have hmem : ((a, b, c, d) : R × R × R × R) ∈ {e | ∀ v ∈ tsupport T, φ e v ∈ V} :=
      hsub₁ ⟨ha.1.1.1, hsub₂ ⟨hb.1.1.2, hsub₃ ⟨hc.1.2, hd.2⟩⟩⟩
    exact hVT v _ (hmem v hv)
  refine ⟨U₀ ∩ (fun x => -x) ⁻¹' U₀, inter_mem hU₀
    (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₀)), ?_⟩
  intro k hk c u
  have hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by
    have := k.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 := hk 0 0
  have e01 := hk 0 1
  have e10 := hk 1 0
  have e11 := hk 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at e00 e01 e10 e11
  by_cases hv : (c, u) ∈ tsupport T
  · have := key (k 0 0 - 1) (k 0 1) (k 1 0) (k 1 1 - 1) e00.1 e01.1 e10.1 e11.1 (c, u) hv
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext <;> simp <;> ring
  by_cases hw : (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) ∈ tsupport T
  · have := key (k 1 1 - 1) (-k 0 1) (-k 1 0) (k 0 0 - 1) e11.1 e01.2 e10.2 e00.1 _ hw
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext
    · simp; linear_combination c * hdet
    · simp; linear_combination u * hdet
  · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

end GlobalTheory.RowSmooth
