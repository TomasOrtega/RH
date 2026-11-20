import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.Mem.ColAd.Nbhd

/- English proof (translation)
Rewrite `hW` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, t, ht, hsub⟩` from `hW`. Conclude with `⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun X hX => hsub fun i _ => Set.mem_iInter.1 (hX i) i⟩`.
-/
theorem pi_small {ι T : Type} [Finite ι] [TopologicalSpace T] (x : T) (W : Set (ι → T))
    (hW : W ∈ nhds (fun _ : ι => x)) : ∃ O ∈ nhds x, ∀ X : ι → T, (∀ i, X i ∈ O) → X ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun X hX => hsub fun i _ => Set.mem_iInter.1 (hX i) i⟩

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- English proof (translation)
Use `letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)`. Introduce `O hO`. Use `haveI := rlt_isModTop F E`. Use `haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)`. Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`.

Establish `hc : Continuous (rlt_comb (F` using `F) b) := IsModuleTopology.continuous_of_linearMap _`. Establish `h1 : (rlt_comb (F` using `F) b) ⁻¹' O ∈ nhds (0 : Fin m → FiniteAdeleRing (𝓞 F) F) := hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hO)`. Take `⟨O', hO', hsub⟩` from `pi_small (0 : FiniteAdeleRing (𝓞 F) F) _ h1`. Take `⟨N, hN, hNO⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O' hO'`. Use `⟨N, hN, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨r, hr, rfl⟩` from `(Set.ext_iff.1 (rlt_image_comb (F := F) b hb) x).2 hx`. Rewrite using `[← map_nsmul]`. Conclude with `hsub _ fun j => hNO (r j) (hr j (Set.mem_univ _))`.
-/
theorem exists_nsmul_intAf : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ O ∈ nhds (0 : AfE F E), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Formalism.L2.Herm.intAf F E, N • x ∈ O := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro O hO
  haveI := rlt_isModTop F E
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  have hc : Continuous (rlt_comb (F := F) b) := IsModuleTopology.continuous_of_linearMap _
  have h1 : (rlt_comb (F := F) b) ⁻¹' O ∈ nhds (0 : Fin m → FiniteAdeleRing (𝓞 F) F) :=
    hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hO)
  obtain ⟨O', hO', hsub⟩ := pi_small (0 : FiniteAdeleRing (𝓞 F) F) _ h1
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O' hO'
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨r, hr, rfl⟩ := (Set.ext_iff.1 (rlt_image_comb (F := F) b hb) x).2 hx
  rw [← map_nsmul]
  exact hsub _ fun j => hNO (r j) (hr j (Set.mem_univ _))

end Tens

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- English proof (translation)
Take `⟨q, rfl⟩` from `hdvd`. Use `set s := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E))⁻¹ * x with hs`. Establish `hm' : (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) ≠ 0`. Rewrite using `[map_natCast]`. Conclude with `hm.ne'` after adjusting the coercions.

Establish `hx' : x = Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) * s := by`. Rewrite using `[hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hm', map_one, one_mul]`. Use `⟨(q : AfE F E) * s, mul_mem (natCast_mem _ q) hx, ?_⟩` and prove the remaining obligations. Establish `hc : Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) = ((m₀ * q : ℕ) : AfE F E) := by`. Rewrite using `[map_natCast, map_natCast]`.

Rewrite using `[hx', hc, nsmul_eq_mul, Nat.cast_mul, mul_assoc]`.
-/
theorem mem_of_congOne_entry {m₀ m : ℕ} (hdvd : m₀ ∣ m) (hm : 0 < m) (x : AfE F E)
    (hx : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m : ℕ) : 𝓞 E))⁻¹ * x ∈
      Formalism.L2.Herm.intAf F E) : ∃ y ∈ Formalism.L2.Herm.intAf F E, x = m₀ • y := by
  obtain ⟨q, rfl⟩ := hdvd
  set s := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E))⁻¹ * x with hs
  have hm' : (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hm.ne'
  have hx' : x = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) * s := by
    rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hm', map_one, one_mul]
  refine ⟨(q : AfE F E) * s, mul_mem (natCast_mem _ q) hx, ?_⟩
  have hc : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) =
      ((m₀ * q : ℕ) : AfE F E) := by
    rw [map_natCast, map_natCast]
  rw [hx', hc, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ n`. Use `letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)`. Use `haveI := rlt_isModTop F E`. Use `haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)`. Introduce `N hN`.

Rewrite `hN` using `[Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap]`. Take `⟨t, ht, hts⟩` from `Filter.mem_comap.1 hN`. Set `φ : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E) → Matrix (Fin n) (Fin n) (AfE F E) × (Matrix (Fin n) (Fin n) (AfE F E))ᵐᵒᵖ` to `fun p => ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.1, MulOpposite.op ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.2))`. Establish `hφ : Continuous φ` using `(continuous_const.add continuous_fst).prodMk (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))`. Establish `hφ0 : φ (0, 0) = Units.embedProduct _ 1`.

Rewrite using `[map_one]`. Simplify using `[φ]`. Establish `h1 : φ ⁻¹' t ∈ nhds ((0, 0) : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E))` using `hφ.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact ht)`. Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.1 h1`. Take `⟨u1, hu1, hu1s⟩` from `pi_small (0 : Fin n → AfE F E) u hu`.

Take `⟨u2, hu2, hu2s⟩` from `pi_small (0 : AfE F E) u1 hu1`. Take `⟨v1, hv1, hv1s⟩` from `pi_small (0 : Fin n → AfE F E) v hv`. Take `⟨v2, hv2, hv2s⟩` from `pi_small (0 : AfE F E) v1 hv1`. Take `⟨m₀, hm₀, hm⟩` from `exists_nsmul_intAf (F := F) (E := E) (u2 ∩ v2) (Filter.inter_mem hu2 hv2)`. Use `⟨m₀, hm₀, fun m hdvd hm0 k hk hk' => hts ?_⟩` and prove the remaining obligations.

Establish `ent : ∀ g : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) g → ∀ i j, (g : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ u2 ∩ v2`. Introduce `g hg i j`. Apply the tactic sequence `obtain ⟨y, hy, e⟩ := mem_of_congOne_entry hdvd hm0 _ (hg i j)`. Rewrite using `[e]`. Conclude with `hm y hy`.

Establish `e : Units.embedProduct _ k = φ (fun i j => (k : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j, fun i j => ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (k : Matrix (Fin n) (Fin n) (AfE F E)) = _`. Use extensionality with `i j`. Simplify using `[φ]`.

Use `show MulOpposite.op ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = _`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Use `show Units.embedProduct _ k ∈ t`.

Rewrite using `[e]`. Conclude with `huv ⟨hu1s _ fun i => hu2s _ fun j => (ent k hk i j).1, hv1s _ fun i => hv2s _ fun j => (ent _ hk' i j).2⟩`.
-/
theorem congOne_nhds : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  intro F E _ _ _ _ _ n
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := rlt_isModTop F E
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)
  intro N hN
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hN
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hN
  let φ : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E) →
      Matrix (Fin n) (Fin n) (AfE F E) × (Matrix (Fin n) (Fin n) (AfE F E))ᵐᵒᵖ :=
    fun p => ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.1,
      MulOpposite.op ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.2))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_fst).prodMk (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))
  have hφ0 : φ (0, 0) = Units.embedProduct _ 1 := by
    rw [map_one]
    simp [φ]
  have h1 : φ ⁻¹' t ∈ nhds ((0, 0) : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E)) :=
    hφ.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact ht)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨u1, hu1, hu1s⟩ := pi_small (0 : Fin n → AfE F E) u hu
  obtain ⟨u2, hu2, hu2s⟩ := pi_small (0 : AfE F E) u1 hu1
  obtain ⟨v1, hv1, hv1s⟩ := pi_small (0 : Fin n → AfE F E) v hv
  obtain ⟨v2, hv2, hv2s⟩ := pi_small (0 : AfE F E) v1 hv1
  obtain ⟨m₀, hm₀, hm⟩ := exists_nsmul_intAf (F := F) (E := E) (u2 ∩ v2) (Filter.inter_mem hu2 hv2)
  refine ⟨m₀, hm₀, fun m hdvd hm0 k hk hk' => hts ?_⟩
  have ent : ∀ g : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) g → ∀ i j,
      (g : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ u2 ∩ v2 := by
    intro g hg i j
    obtain ⟨y, hy, e⟩ := mem_of_congOne_entry hdvd hm0 _ (hg i j)
    rw [e]
    exact hm y hy
  have e : Units.embedProduct _ k = φ (fun i j => (k : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j,
      fun i j => ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
    refine Prod.ext ?_ ?_
    · show (k : Matrix (Fin n) (Fin n) (AfE F E)) = _
      ext i j
      simp [φ]
    · show MulOpposite.op ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = _
      congr 1
      ext i j
      simp
  show Units.embedProduct _ k ∈ t
  rw [e]
  exact huv ⟨hu1s _ fun i => hu2s _ fun j => (ent k hk i j).1, hv1s _ fun i => hv2s _ fun j => (ent _ hk' i j).2⟩

end Main

end GlobalTheory.Mem.ColAd.Nbhd
