import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCentralCharacter
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.AbC

section LinAlg

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Break down `hρ.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h` into its components or cases. Conclude with `absurd (congrArg Subrepresentation.toSubmodule h) h0`. Conclude with `congrArg Subrepresentation.toSubmodule h`.
-/
private theorem stable_eq_top {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (h0 : S ≠ ⊥) : S = ⊤ := by
  rcases hρ.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) h0
  · exact congrArg Subrepresentation.toSubmodule h

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Take `⟨x, y, hxy⟩` from `hρ.toNontrivial.exists_pair_ne`. Conclude with `hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))`.
-/
private theorem nontrivial_of_irr {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨x, y, hxy⟩ := hρ.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

/- English proof (translation)
Establish `hsq : Squarefree (minpoly ℂ f)` using `hf.minpoly_squarefree`. Establish `h1 : minpoly ℂ f ∣ (X - 1 : ℂ[X]) ^ (m + 1)` using `(LinearMap.minpoly_dvd_charpoly f).trans (hd.trans (pow_dvd_pow _ (Nat.le_succ m)))`. Take `⟨q, hq⟩` from `(hsq.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 h1`. Establish `h2 : aeval f (X - 1 : ℂ[X]) = 0` using `by rw [hq, map_mul, minpoly.aeval, zero_mul]`. Simplify `h2` using `[sub_eq_zero]`.
-/
private theorem eq_one_of_dvd [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hf : f.IsSemisimple) (m : ℕ)
    (hd : f.charpoly ∣ (X - 1 : ℂ[X]) ^ m) : f = 1 := by
  have hsq : Squarefree (minpoly ℂ f) := hf.minpoly_squarefree
  have h1 : minpoly ℂ f ∣ (X - 1 : ℂ[X]) ^ (m + 1) :=
    (LinearMap.minpoly_dvd_charpoly f).trans (hd.trans (pow_dvd_pow _ (Nat.le_succ m)))
  obtain ⟨q, hq⟩ := (hsq.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 h1
  have h2 : aeval f (X - 1 : ℂ[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h2

/- English proof (translation)
Use `haveI := nontrivial_of_irr hρ`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue f`. Establish `hS : f.eigenspace μ = ⊤` using `stable_eq_top hρ _ (fun g v hv => by`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Establish `h1 : f (ρ g v) = ρ g (f v)` using `LinearMap.congr_fun (hf g).eq.symm v`.

Rewrite using `[h1, hv, map_smul]) hμ`. Use `⟨μ, fun v => ?_⟩` and prove the remaining obligations. Establish `hv : v ∈ f.eigenspace μ` using `hS ▸ Submodule.mem_top`. Conclude with `Module.End.mem_eigenspace_iff.1 hv`.
-/
private theorem scalar_of_commute [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible)
    (f : Module.End ℂ V) (hf : ∀ g, Commute (ρ g) f) : ∃ c : ℂ, ∀ v, f v = c • v := by
  haveI := nontrivial_of_irr hρ
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  have hS : f.eigenspace μ = ⊤ := stable_eq_top hρ _ (fun g v hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h1 : f (ρ g v) = ρ g (f v) := LinearMap.congr_fun (hf g).eq.symm v
    rw [h1, hv, map_smul]) hμ
  refine ⟨μ, fun v => ?_⟩
  have hv : v ∈ f.eigenspace μ := hS ▸ Submodule.mem_top
  exact Module.End.mem_eigenspace_iff.1 hv

end LinAlg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Use `haveI := nontrivial_of_irr hb`. Establish `h1 : ∀ (σ : Weil h) (t : Ine (F` using `E) A), b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) = 1 := fun σ t => by`. Take `⟨m, hm⟩` from `hu σ t`. Conclude with `eq_one_of_dvd _ (b.semisimple _) m hm`. Establish `h2 : ∀ (σ : Weil h) (t : Ine (F` using `E) A), Commute (b.ρ σ) (b.ρ (ineIncl h t)) := fun σ t => by`.

Establish `e : σ * ineIncl h t = (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) * (ineIncl h t * σ)` using `by group`. Use `show b.ρ σ * b.ρ _ = b.ρ _ * b.ρ σ`. Rewrite using `[← map_mul, ← map_mul, e, map_mul, h1, one_mul]`. Establish `h3 : ∀ t : Ine (F` using `E) A, ∃ c : ℂ, ∀ v, b.ρ (ineIncl h t) v = c • v := fun t => scalar_of_commute hb _ fun g => h2 g t`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue (b.ρ (frob h))`.

Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Establish `hv0 : v ≠ 0` using `hv.2`. Establish `hφ : b.ρ (frob h) v = μ • v` using `Module.End.mem_eigenspace_iff.1 hv.1`. Set `K : Subgroup (Weil h)` to `{ carrier := {σ | ∃ c : ℂ, b.ρ σ v = c • v} one_mem' := ⟨1, by simp⟩ mul_mem' := by`. Introduce and unpack `σ τ ⟨c, hc⟩ ⟨c', hc'⟩`.

Conclude with `⟨c * c', by rw [map_mul, Module.End.mul_apply, hc', map_smul, hc, smul_smul, mul_comm]⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `σ ⟨c, hc⟩`. Establish `hinv : b.ρ σ⁻¹ (b.ρ σ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`.

Both sides reduce to the same expression. Rewrite `hinv` using `[hc, map_smul]`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hinv` using `[zero_smul]`.

Conclude with `hv0 hinv.symm`. Conclude with `⟨c⁻¹, by rw [eq_inv_smul_iff₀ hc0]; exact hinv⟩ }`. Establish `hK : ∀ σ, σ ∈ K` using `fun σ => by`. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) σ`. Rewrite using `[hτ]`.

Use `K.mul_mem (K.zpow_mem ⟨μ, hφ⟩ _) ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `h3 τ`. Conclude with `⟨c, hc v⟩`. Establish `hL : (ℂ ∙ v) = ⊤` using `stable_eq_top hb _ (fun g u hu => by`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hu`.

Take `⟨c, hc⟩` from `hK g`. Rewrite using `[map_smul, hc]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))`. Use the proof step `(by simpa using hv0)`. Establish `hf` using `finrank_span_singleton (K := ℂ) hv0`.

Rewrite `hf` using `[hL, finrank_top, Module.finrank_fin_fun]`. Conclude with `hf`.
-/
private theorem dim_one {d : ℕ} (b : WDRep h (Fin d → ℂ)) (hb : b.ρ.IsIrreducible)
    (hu : ∀ (σ : Weil h) (t : Ine (F := E) A), ∃ m : ℕ,
      (b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹)).charpoly ∣ (X - 1 : ℂ[X]) ^ m) : d = 1 := by
  haveI := nontrivial_of_irr hb
  have h1 : ∀ (σ : Weil h) (t : Ine (F := E) A), b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) = 1 := fun σ t => by
    obtain ⟨m, hm⟩ := hu σ t
    exact eq_one_of_dvd _ (b.semisimple _) m hm
  have h2 : ∀ (σ : Weil h) (t : Ine (F := E) A), Commute (b.ρ σ) (b.ρ (ineIncl h t)) := fun σ t => by
    have e : σ * ineIncl h t = (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) * (ineIncl h t * σ) := by group
    show b.ρ σ * b.ρ _ = b.ρ _ * b.ρ σ
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have h3 : ∀ t : Ine (F := E) A, ∃ c : ℂ, ∀ v, b.ρ (ineIncl h t) v = c • v :=
    fun t => scalar_of_commute hb _ fun g => h2 g t
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (b.ρ (frob h))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hφ : b.ρ (frob h) v = μ • v := Module.End.mem_eigenspace_iff.1 hv.1
  let K : Subgroup (Weil h) :=
    { carrier := {σ | ∃ c : ℂ, b.ρ σ v = c • v}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro σ τ ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', by rw [map_mul, Module.End.mul_apply, hc', map_smul, hc, smul_smul, mul_comm]⟩
      inv_mem' := by
        rintro σ ⟨c, hc⟩
        have hinv : b.ρ σ⁻¹ (b.ρ σ v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [hc, map_smul] at hinv
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hinv
          exact hv0 hinv.symm
        exact ⟨c⁻¹, by rw [eq_inv_smul_iff₀ hc0]; exact hinv⟩ }
  have hK : ∀ σ, σ ∈ K := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    rw [hτ]
    refine K.mul_mem (K.zpow_mem ⟨μ, hφ⟩ _) ?_
    obtain ⟨c, hc⟩ := h3 τ
    exact ⟨c, hc v⟩
  have hL : (ℂ ∙ v) = ⊤ := stable_eq_top hb _ (fun g u hu => by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨c, hc⟩ := hK g
    rw [map_smul, hc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
    (by simpa using hv0)
  have hf := finrank_span_singleton (K := ℂ) hv0
  rw [hL, finrank_top, Module.finrank_fin_fun] at hf
  exact hf

/- English proof (translation)
Rewrite using `[(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ]`. Establish `h0 : ((rc Δ.first).lpTw ((0 : ℕ) : ℝ)).charPol σ = (rc Δ.first).charPol σ`. Take `⟨n, b, hb⟩` from `(rc Δ.first).exists_rep`. Rewrite using `[← hb, WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ]`. Simplify using the standard rewrite rules.

Rewrite using `[← h0]`. Conclude with `Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 Δ.len_pos, rfl⟩)`.
-/
private theorem charPol_first_dvd (rc : IrrGL (w.adicCompletion E) → WD h) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (rc Δ.first).charPol σ ∣ (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).charPol σ := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ]
  have h0 : ((rc Δ.first).lpTw ((0 : ℕ) : ℝ)).charPol σ = (rc Δ.first).charPol σ := by
    obtain ⟨n, b, hb⟩ := (rc Δ.first).exists_rep
    rw [← hb, WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ]
    simp
  rw [← h0]
  exact Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 Δ.len_pos, rfl⟩)

end UpperTheory.Zero.LLC.AbC

open UpperTheory.Zero.LLC.AbC in
/- English proof (translation)
Introduce and unpack `E Ω _ _ _ _ _ A w h rc ⟨a, ha, H⟩ x ξ hξ`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨𝔪, hm⟩` from `Pr.exh (w.adicCompletion E) x`. Establish `hs : HasSupport x.rep (msupp 𝔪)` using `GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm`. Establish `hrc : rc x = segSum rc 𝔪.toList` using `H.langlands _ x (by rw [Multiset.coe_toList]; exact hm)`.

Use `⟨_, hs, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨Δ, hΔ, hy⟩` from `Multiset.mem_bind.1 hy`. Take `⟨j, -, rfl⟩` from `Segment.mem_carrier.1 (Segment.mem_ms.1 hy)`. Establish `hd : ∀ σ, (rc Δ.first).charPol σ ∣ (rc x).charPol σ` using `fun σ => by`. Rewrite using `[hrc, segSum, CuspExt.charPol_sumList, List.map_map]`.

Use `(charPol_first_dvd rc Δ σ).trans (List.dvd_prod (List.mem_map.2 ⟨Δ, Multiset.mem_toList.2 hΔ, rfl⟩))` and prove the remaining obligations. Take `⟨n, b, hb, hirr⟩` from `H.cusp _ Δ.isCusp_first`. Establish `hdim : n = Δ.first.1`. Use `H.dim Δ.first` as an intermediate fact. Rewrite `this` using `[← hb, WD.lpDim_mk]`.

Simplify using `using this`. Establish `hn : n = 1` using `dim_one b hirr fun σ t => ⟨x.1, by`. Establish `e : σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹ = ineIncl h (ineConj σ t * t⁻¹)`. Rewrite using `[map_mul, ineIncl_ineConj, map_inv]`. Establish `h1 : ∀ j, ξ j (ineIncl h (ineConj σ t * t⁻¹)) = 1` using `fun j => by`.

Rewrite using `[← e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (ξ j σ), mul_inv_cancel_right, mul_inv_cancel]`. Rewrite using `[← WD.charPol_mk, hb, e]`. Use `(hd _).trans ?_` and prove the remaining obligations. Rewrite using `[hξ]`. Simplify using `[h1]⟩`.

Conclude with `hdim.symm.trans hn`.
-/
theorem UpperTheory.Zero.LLC.abConv :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ x, UpperTheory.Zero.LLC.AbConverse (rc x) x := by
  rintro E Ω _ _ _ _ _ A w h rc ⟨a, ha, H⟩ x ξ hξ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  have hrc : rc x = segSum rc 𝔪.toList := H.langlands _ x (by rw [Multiset.coe_toList]; exact hm)
  refine ⟨_, hs, fun y hy => ?_⟩
  obtain ⟨Δ, hΔ, hy⟩ := Multiset.mem_bind.1 hy
  obtain ⟨j, -, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hy)
  have hd : ∀ σ, (rc Δ.first).charPol σ ∣ (rc x).charPol σ := fun σ => by
    rw [hrc, segSum, CuspExt.charPol_sumList, List.map_map]
    refine (charPol_first_dvd rc Δ σ).trans (List.dvd_prod (List.mem_map.2 ⟨Δ, Multiset.mem_toList.2 hΔ, rfl⟩))
  obtain ⟨n, b, hb, hirr⟩ := H.cusp _ Δ.isCusp_first
  have hdim : n = Δ.first.1 := by
    have := H.dim Δ.first
    rw [← hb, WD.lpDim_mk] at this
    simpa using this
  have hn : n = 1 := dim_one b hirr fun σ t => ⟨x.1, by
    have e : σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹ = ineIncl h (ineConj σ t * t⁻¹) := by
      rw [map_mul, ineIncl_ineConj, map_inv]
    have h1 : ∀ j, ξ j (ineIncl h (ineConj σ t * t⁻¹)) = 1 := fun j => by
      rw [← e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (ξ j σ), mul_inv_cancel_right, mul_inv_cancel]
    rw [← WD.charPol_mk, hb, e]
    refine (hd _).trans ?_
    rw [hξ]
    simp [h1]⟩
  exact hdim.symm.trans hn
