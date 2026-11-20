import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFLeSpanK

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def phi {n : ℕ} (b : Fin n → V) (a : Fin n → 𝓞 F) : (Fin n → 𝓞 K) →ₗ[𝓞 K] V where
  toFun z := ∑ i, (jK (z i) / jK (ι (a i))) • b i
  map_add' z z' := by
    simp only [Pi.add_apply, map_add, add_div, add_smul, Finset.sum_add_distrib]
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_jK c, smul_smul, mul_div_assoc]

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}

/- English proof (translation)
Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]`.
-/
private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : jK (ι a) = algebraMap F K (a : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

/- English proof (translation)
Rewrite using `[coe_iota_eq_algebraMap_coe]`. Use `(map_ne_zero (algebraMap F K)).mpr ?_` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha`.
-/
private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  rw [coe_iota_eq_algebraMap_coe]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

/- English proof (translation)
Establish `hdiag' : ∀ i, h (b i) (b i) = jK (ι (a i))` using `fun i => by`. Rewrite using `[hdiag i]`. Conclude with `(coe_iota_eq_algebraMap_coe (a i)).symm`. Use `show h (b k) (∑ i, (jK (z i) / jK (ι (a i))) • b i) = jK (z k)`. Rewrite using `[h_sum horth hdiag' _ k, div_mul_cancel₀ _ (jK_iota_ne_zero (ha k))]`.
-/
theorem h_phi (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
    (z : Fin n → 𝓞 K) (k : Fin n) : h (b k) (phi b a z) = jK (z k) := by
  have hdiag' : ∀ i, h (b i) (b i) = jK (ι (a i)) := fun i => by
    rw [hdiag i]; exact (coe_iota_eq_algebraMap_coe (a i)).symm
  show h (b k) (∑ i, (jK (z i) / jK (ι (a i))) • b i) = jK (z k)
  rw [h_sum horth hdiag' _ k, div_mul_cancel₀ _ (jK_iota_ne_zero (ha k))]

/- English proof (translation)
Use `show (∑ i, (jK (z i) / jK (ι (a i))) • b i) ∈ X`. Conclude with `X.sum_mem fun i _ => X.smul_mem _ (hbX i)`.
-/
theorem phi_mem (hbX : ∀ i, b i ∈ X) (z : Fin n → 𝓞 K) : phi b a z ∈ X := by
  show (∑ i, (jK (z i) / jK (ι (a i))) • b i) ∈ X
  exact X.sum_mem fun i _ => X.smul_mem _ (hbX i)

/- English proof (translation)
Use `haveI := h𝔭.isPrime`. Establish `hA : ∀ z, phi b a z ∈ locF 𝔭 (dualIn h X L)` using `fun z => (mem_locF_dualIn_iff hbX hloc horth hdiag ha hF h𝔭 hL _).mpr ⟨phi_mem hbX z, fun i => by rw [h_phi horth hdiag ha]; exact HU.jK_mem_SP _⟩`. Set `ψ₀ : (Fin n → 𝓞 K) →ₗ[𝓞 K] locF 𝔭 (dualIn h X L)` to `LinearMap.codRestrict _ (phi b a) hA`. Set `ψ` to `((locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype).mkQ.comp ψ₀`. Establish `hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun i => extP K 𝔭 ^ vF 𝔭 (a i))`.

Use extensionality with `z`. Simplify using `only [ψ, ψ₀, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.codRestrict_apply, Submodule.mem_pi, Set.mem_univ, forall_const]`. Rewrite using `[mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL]`. Simplify using `only [h_phi horth hdiag ha, div_mem_SP_iff h𝔭 (ha _)]`. Conclude with `⟨fun hz => hz.2, fun hz => ⟨phi_mem hbX z, hz⟩⟩`.

Establish `hsurj : Function.Surjective ψ`. Introduce `q`. Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.Quotient.mk_surjective ((locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype) q`. Establish `hx'` using `(mem_locF_dualIn_iff hbX hloc horth hdiag ha hF h𝔭 hL x).mp hx`. Use `choose z hz using fun i => exists_sub_div_mem_SP h𝔭 (ha i) (hx'.2 i)`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify using `only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Simplify using `only [ψ₀, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub, LinearMap.codRestrict_apply]`. Rewrite using `[mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL]`.

Use `⟨X.sub_mem (phi_mem hbX z) hx'.1, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, h_phi horth hdiag ha]`. Use `Subring.neg_mem _ (hz i)` as an intermediate fact. Rewrite `this` using `[← neg_div, neg_sub]`. Then use the resulting hypothesis. Conclude with `⟨(LinearMap.quotKerEquivOfSurjective ψ hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ Submodule.quotientPi _⟩`.
-/
theorem disc_equiv (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn X L) (hbX : ∀ i, b i ∈ X)
    (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
    (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0) :
    Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] ∀ i : Fin n, 𝓞 K ⧸ extP K 𝔭 ^ vF 𝔭 (a i)) := by
  classical
  haveI := h𝔭.isPrime
  have hA : ∀ z, phi b a z ∈ locF 𝔭 (dualIn h X L) := fun z =>
    (mem_locF_dualIn_iff hbX hloc horth hdiag ha hF h𝔭 hL _).mpr
      ⟨phi_mem hbX z, fun i => by rw [h_phi horth hdiag ha]; exact HU.jK_mem_SP _⟩
  let ψ₀ : (Fin n → 𝓞 K) →ₗ[𝓞 K] locF 𝔭 (dualIn h X L) := LinearMap.codRestrict _ (phi b a) hA
  let ψ := ((locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype).mkQ.comp ψ₀
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun i => extP K 𝔭 ^ vF 𝔭 (a i)) := by
    ext z
    simp only [ψ, ψ₀, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      LinearMap.codRestrict_apply, Submodule.mem_pi, Set.mem_univ, forall_const]
    rw [mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL]
    simp only [h_phi horth hdiag ha, div_mem_SP_iff h𝔭 (ha _)]
    exact ⟨fun hz => hz.2, fun hz => ⟨phi_mem hbX z, hz⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ :=
      Submodule.Quotient.mk_surjective ((locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype) q
    have hx' := (mem_locF_dualIn_iff hbX hloc horth hdiag ha hF h𝔭 hL x).mp hx
    choose z hz using fun i => exists_sub_div_mem_SP h𝔭 (ha i) (hx'.2 i)
    refine ⟨z, ?_⟩
    simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [ψ₀, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub,
      LinearMap.codRestrict_apply]
    rw [mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL]
    refine ⟨X.sub_mem (phi_mem hbX z) hx'.1, fun i => ?_⟩
    rw [map_sub, h_phi horth hdiag ha]
    have := Subring.neg_mem _ (hz i)
    rwa [← neg_div, neg_sub] at this
  exact ⟨(LinearMap.quotKerEquivOfSurjective ψ hsurj).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ Submodule.quotientPi _⟩

end

end Formalism.L2.SG.Pf.G2
