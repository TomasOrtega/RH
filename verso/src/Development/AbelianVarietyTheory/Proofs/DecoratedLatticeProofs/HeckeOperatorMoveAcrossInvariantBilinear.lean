import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag

noncomputable section

namespace GlobalTheory.ChainOnto

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

section Move

variable {G : Type} [Group G] {K : Subgroup G}

/- English proof (translation)
Simplify using `only [DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, k, hk, e⟩`. Use `⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩` and prove the remaining obligations. Establish `hg : g = (h * a * k)⁻¹` using `by rw [← e, inv_inv]`.

Rewrite using `[hg]`. Use `group`. Introduce and unpack `⟨h, hh, k, hk, e⟩`. Use `⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Use `group`.
-/
theorem mem_doubleCoset_inv_iff {a g : G} :
    g⁻¹ ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    have hg : g = (h * a * k)⁻¹ := by rw [← e, inv_inv]
    rw [hg]
    group
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    rw [e]
    group

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [dosetInd]`. Distinguish the cases in `h : g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem (mem_doubleCoset_inv_iff.mpr h)]`. Both sides reduce to the same expression.

Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (mem_doubleCoset_inv_iff.mp h'))]`.
-/
theorem dosetInd_comp_inv (a : G) : (fun g => dosetInd ℂ K a g⁻¹) = dosetInd ℂ K a⁻¹ := by
  funext g
  simp only [dosetInd]
  by_cases h : g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_doubleCoset_inv_iff.mpr h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (mem_doubleCoset_inv_iff.mp h'))]

/- English proof (translation)
Rewrite using `[DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, k, hk, e⟩`. Use `⟨h, hh, ?_⟩` and prove the remaining obligations. Establish `hc : ((c.out : G) : G ⧸ K) = c` using `QuotientGroup.out_eq' c`.

Rewrite using `[← hc, e, QuotientGroup.eq]`. Establish `hx : (h * a * k)⁻¹ * (h * a) = k⁻¹` using `by group`. Rewrite using `[hx]`. Conclude with `K.inv_mem hk`. Introduce and unpack `⟨k, hk, rfl⟩`.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul K (k * a)`. Conclude with `⟨k, hk, h, h.2, hh⟩`.
-/
theorem out_mem_doubleCoset_iff (a : G) (c : G ⧸ K) :
    c.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ ∃ k ∈ K, c = ((k * a : G) : G ⧸ K) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨h, hh, ?_⟩
    have hc : ((c.out : G) : G ⧸ K) = c := QuotientGroup.out_eq' c
    rw [← hc, e, QuotientGroup.eq]
    have hx : (h * a * k)⁻¹ * (h * a) = k⁻¹ := by group
    rw [hx]
    exact K.inv_mem hk
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (k * a)
    exact ⟨k, hk, h, h.2, hh⟩

/- English proof (translation)
Establish `h` using `hK a`. Use `set H := K.map (MulAut.conj a).toMonoidHom with hH`. Establish `hfin : Finite (K ⧸ H.subgroupOf K)`. Unfold `Subgroup.relIndex at h`. Conclude with `Subgroup.index_ne_zero_iff_finite.mp h`.

Apply `(Set.finite_range (fun q : K ⧸ H.subgroupOf K => ((((q.out : K) : G) * a : G) : G ⧸ K))).subset` to reduce the goal to its premises. Introduce and unpack `c ⟨k, hk, rfl⟩`. Take `⟨h', hh'⟩` from `QuotientGroup.mk_out_eq_mul (H.subgroupOf K) (⟨k, hk⟩ : K)`. Use `⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hh', QuotientGroup.eq]`. Establish `hm : ((h' : K) : G) ∈ H` using `Subgroup.mem_subgroupOf.mp h'.2`. Take `⟨y, hy, hyeq⟩` from `Subgroup.mem_map.mp hm`. Establish `hy' : ((h' : K) : G) = a * y * a⁻¹`. Rewrite using `[← hyeq]`.

Simplify using `[MulAut.conj_apply]`. Establish `hx : ((((⟨k, hk⟩ : K) * (h' : K) : K) : G) * a)⁻¹ * (k * a) = y⁻¹`. Rewrite using `[Subgroup.coe_mul, hy']`. Simplify using `only [Subgroup.coe_mk]`. Use `group`.

Rewrite using `[hx]`. Conclude with `K.inv_mem hy`.
-/
private theorem finite_left_cosets_of_isCommensurated (hK : IsCommensurated K) (a : G) :
    {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}.Finite := by
  have h := hK a
  set H := K.map (MulAut.conj a).toMonoidHom with hH
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    unfold Subgroup.relIndex at h
    exact Subgroup.index_ne_zero_iff_finite.mp h
  apply (Set.finite_range (fun q : K ⧸ H.subgroupOf K => ((((q.out : K) : G) * a : G) : G ⧸ K))).subset
  rintro c ⟨k, hk, rfl⟩
  obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K) (⟨k, hk⟩ : K)
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  simp only
  rw [hh', QuotientGroup.eq]
  have hm : ((h' : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp h'.2
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hm
  have hy' : ((h' : K) : G) = a * y * a⁻¹ := by
    rw [← hyeq]
    simp [MulAut.conj_apply]
  have hx : ((((⟨k, hk⟩ : K) * (h' : K) : K) : G) * a)⁻¹ * (k * a) = y⁻¹ := by
    rw [Subgroup.coe_mul, hy']
    simp only [Subgroup.coe_mk]
    group
  rw [hx]
  exact K.inv_mem hy

/- English proof (translation)
Use `set S := {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} with hSdef`. Establish `hS : S.Finite` using `finite_left_cosets_of_isCommensurated hK a`. Establish `hind : ∀ c : G ⧸ K, dosetInd ℂ K a c.out = S.indicator (fun _ => (1 : ℂ)) c`. Introduce `c`. Simplify using `only [dosetInd, Set.indicator_apply, out_mem_doubleCoset_iff, hSdef, Set.mem_setOf_eq, Pi.one_apply]`.

Rewrite using `[finsum_congr hind, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const, nsmul_eq_mul, mul_one]`. Establish `hcard : Nat.card S = hS.toFinset.card` using `Nat.card_eq_card_finite_toFinset hS`. Conclude with `hcard.symm` after adjusting the coercions.
-/
theorem finsum_dosetInd_out (hK : IsCommensurated K) (a : G) :
    ∑ᶠ c : G ⧸ K, dosetInd ℂ K a c.out = (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ) := by
  classical
  set S := {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} with hSdef
  have hS : S.Finite := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, dosetInd ℂ K a c.out = S.indicator (fun _ => (1 : ℂ)) c := by
    intro c
    simp only [dosetInd, Set.indicator_apply, out_mem_doubleCoset_iff, hSdef, Set.mem_setOf_eq, Pi.one_apply]
  rw [finsum_congr hind, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : Nat.card S = hS.toFinset.card := Nat.card_eq_card_finite_toFinset hS
  exact_mod_cast hcard.symm

/- English proof (translation)
Establish `h : ∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v` using `hv`. Simplify using `using h ⟨k, hk⟩`.
-/
private theorem apply_eq_of_mem_fixed {G V : Type} [Group G] {K : Subgroup G} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {v : V} (hv : v ∈ fixed ρ K) {k : G} (hk : k ∈ K) : ρ k v = v := by
  have h : ∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v := hv
  simpa using h ⟨k, hk⟩

/- English proof (translation)
Take `⟨k, hk, k', hk', rfl⟩` from `DoubleCoset.mem_doubleCoset.mp hw`. Establish `hu' : π k' u = u` using `apply_eq_of_mem_fixed π hu hk'`. Establish `hy' : ρ k⁻¹ y = y` using `apply_eq_of_mem_fixed ρ hy (K.inv_mem hk)`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu']`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem invariant_pairing_doubleCoset_eq {G U X X' : Type} [Group G] {K : Subgroup G} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    {a w : G} (hw : w ∈ DoubleCoset.doubleCoset a (K : Set G) K) : b (π w u) y = b (π a u) y := by
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
  have hu' : π k' u = u := apply_eq_of_mem_fixed π hu hk'
  have hy' : ρ k⁻¹ y = y := apply_eq_of_mem_fixed ρ hy (K.inv_mem hk)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu']
  calc b (π k (π a u)) y = b (π k (π a u)) (ρ k (ρ k⁻¹ y)) := by rw [Representation.self_inv_apply]
    _ = b (π a u) (ρ k⁻¹ y) := hb k _ _
    _ = b (π a u) y := by rw [hy']

/- English proof (translation)
Establish `hS` using `finite_left_cosets_of_isCommensurated hK a`. Establish `hind : ∀ c : G ⧸ K, c ∉ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} → dosetInd ℂ K a c.out = 0`. Introduce `c hc`. Simplify using `only [dosetInd]`. Conclude with `Set.indicator_of_notMem (fun h => hc ((out_mem_doubleCoset_iff a c).mp h)) _`.

Rewrite using `[← LinearMap.flip_apply b (heckeVec π K (r • dosetInd ℂ K a) u) y]`. Unfold `heckeVec`. Establish `hsupp : (Function.support fun c : G ⧸ K => (r • dosetInd ℂ K a) c.out • π c.out u).Finite`. Apply `hS.subset` to reduce the goal to its premises. Introduce `c hc`.

Assume the negation of the conclusion as `hcS`. Apply `hc` to reduce the goal to its premises. Simplify using `[hind c hcS]`. Rewrite using `[map_finsum _ hsupp]`. Establish `hterm : ∀ c : G ⧸ K, (b.flip y) ((r • dosetInd ℂ K a) c.out • π c.out u) = (r * dosetInd ℂ K a c.out) • b (π a u) y`.

Introduce `c`. Rewrite using `[map_smul, LinearMap.flip_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hc : c ∈ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}`. Rewrite using `[invariant_pairing_doubleCoset_eq π ρ b hb hu hy ((out_mem_doubleCoset_iff a c).mpr hc)]`. Simplify using `[hind c hc]`.

Rewrite using `[finsum_congr hterm, ← finsum_smul, ← mul_finsum, finsum_dosetInd_out hK a]`.
-/
private theorem pairing_heckeVec_dosetInd_eq_card_smul {G U X X' : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    (r : ℂ) (a : G) :
    b (heckeVec π K (r • dosetInd ℂ K a) u) y =
      (r * (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ)) • b (π a u) y := by
  classical
  have hS := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, c ∉ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} → dosetInd ℂ K a c.out = 0 := by
    intro c hc
    simp only [dosetInd]
    exact Set.indicator_of_notMem (fun h => hc ((out_mem_doubleCoset_iff a c).mp h)) _
  rw [← LinearMap.flip_apply b (heckeVec π K (r • dosetInd ℂ K a) u) y]
  unfold heckeVec
  have hsupp : (Function.support fun c : G ⧸ K => (r • dosetInd ℂ K a) c.out • π c.out u).Finite := by
    apply hS.subset
    intro c hc
    by_contra hcS
    apply hc
    simp [hind c hcS]
  rw [map_finsum _ hsupp]
  have hterm : ∀ c : G ⧸ K, (b.flip y) ((r • dosetInd ℂ K a) c.out • π c.out u) =
      (r * dosetInd ℂ K a c.out) • b (π a u) y := by
    intro c
    rw [map_smul, LinearMap.flip_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : c ∈ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}
    · rw [invariant_pairing_doubleCoset_eq π ρ b hb hu hy ((out_mem_doubleCoset_iff a c).mpr hc)]
    · simp [hind c hc]
  rw [finsum_congr hterm, ← finsum_smul, ← mul_finsum, finsum_dosetInd_out hK a]

/- English proof (translation)
Establish `h : IsBiInv K ψ ∧ FinDosetSupp K ψ` using `hψ`. Take `⟨hbi, S, hS⟩` from `h`. Use `show IsBiInv K (fun g => ψ g⁻¹) ∧ FinDosetSupp K (fun g => ψ g⁻¹)`. Use `⟨fun a b g => ?_, S.image (fun s => s⁻¹), fun g hg => ?_⟩` and prove the remaining obligations. Establish `e` using `hbi b⁻¹ a⁻¹ g⁻¹`.

Simplify using `only [Subgroup.coe_inv] at e`. Simplify using `only`. Rewrite using `[← e]`. Use `congr 1`. Use `group`.

Take `⟨s, hs, a, b, e⟩` from `hS g⁻¹ hg`. Use `⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩` and prove the remaining obligations. Establish `hg' : g = (↑a * s * ↑b)⁻¹` using `by rw [← e, inv_inv]`. Rewrite using `[hg', Subgroup.coe_inv, Subgroup.coe_inv]`. Use `group`.
-/
private theorem comp_inv_mem_hecke {G : Type} [Group G] {K : Subgroup G} {ψ : G → ℂ} (hψ : ψ ∈ Hecke ℂ K) :
    (fun g => ψ g⁻¹) ∈ Hecke ℂ K := by
  classical
  have h : IsBiInv K ψ ∧ FinDosetSupp K ψ := hψ
  obtain ⟨hbi, S, hS⟩ := h
  show IsBiInv K (fun g => ψ g⁻¹) ∧ FinDosetSupp K (fun g => ψ g⁻¹)
  refine ⟨fun a b g => ?_, S.image (fun s => s⁻¹), fun g hg => ?_⟩
  · have e := hbi b⁻¹ a⁻¹ g⁻¹
    simp only [Subgroup.coe_inv] at e
    simp only
    rw [← e]
    congr 1
    group
  · obtain ⟨s, hs, a, b, e⟩ := hS g⁻¹ hg
    refine ⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩
    have hg' : g = (↑a * s * ↑b)⁻¹ := by rw [← e, inv_inv]
    rw [hg', Subgroup.coe_inv, Subgroup.coe_inv]
    group

end Move

/- English proof (translation)
Introduce `G _ K hK hsym U X X' _ _ _ _ _ _ π ρ b hb f hf x hx φ hφ`. Use `⟨comp_inv_mem_hecke hφ, ?_⟩` and prove the remaining obligations. Use `hecke_induction (p := fun ψ => b (heckeVec π K ψ f) x = b f (heckeVec ρ K (fun g => ψ g⁻¹) x)) ?_ ?_ ?_ hφ` and prove the remaining obligations. Simplify using `[heckeVec]`. Introduce `ψ hψ ψ' hψ' e e'`.

Establish `hsum : (fun g => (ψ + ψ') g⁻¹) = (fun g => ψ g⁻¹) + (fun g => ψ' g⁻¹)` using `rfl`. Rewrite using `[heckeVec_add hK π hψ hψ' f, hsum, heckeVec_add hK ρ (comp_inv_mem_hecke hψ) (comp_inv_mem_hecke hψ') x, map_add, LinearMap.add_apply, map_add, e, e']`. Introduce `r a`. Establish `hc : (fun g => (r • dosetInd ℂ K a) g⁻¹) = r • dosetInd ℂ K a⁻¹`. Use function extensionality and compare the values at `g`.

Rewrite using `[Pi.smul_apply, Pi.smul_apply, ← dosetInd_comp_inv a]`. Establish `hb' : ∀ g y u, b.flip (ρ g y) (π g u) = b.flip y u` using `fun g y u => by`. Rewrite using `[LinearMap.flip_apply, LinearMap.flip_apply, hb]`. Rewrite using `[hc, pairing_heckeVec_dosetInd_eq_card_smul hK π ρ b hb hf hx r a, ← LinearMap.flip_apply b f (heckeVec ρ K (r • dosetInd ℂ K a⁻¹) x), pairing_heckeVec_dosetInd_eq_card_smul hK ρ π b.flip hb' hx hf r a⁻¹, LinearMap.flip_apply, hsym a]`. Use `congr 1`.

Rewrite using `[← hb a f (ρ a⁻¹ x), Representation.self_inv_apply]`.
-/
theorem heckeVec_move : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → CosetSym K →
    ∀ (U X X' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ g u y, b (π g u) (ρ g y) = b u y) → ∀ f ∈ fixed π K, ∀ x ∈ fixed ρ K, ∀ φ ∈ Hecke ℂ K,
    (fun g => φ g⁻¹) ∈ Hecke ℂ K ∧ b (heckeVec π K φ f) x = b f (heckeVec ρ K (fun g => φ g⁻¹) x) := by
  intro G _ K hK hsym U X X' _ _ _ _ _ _ π ρ b hb f hf x hx φ hφ
  refine ⟨comp_inv_mem_hecke hφ, ?_⟩
  refine hecke_induction (p := fun ψ => b (heckeVec π K ψ f) x = b f (heckeVec ρ K (fun g => ψ g⁻¹) x))
    ?_ ?_ ?_ hφ
  · simp [heckeVec]
  · intro ψ hψ ψ' hψ' e e'
    have hsum : (fun g => (ψ + ψ') g⁻¹) = (fun g => ψ g⁻¹) + (fun g => ψ' g⁻¹) := rfl
    rw [heckeVec_add hK π hψ hψ' f, hsum, heckeVec_add hK ρ (comp_inv_mem_hecke hψ) (comp_inv_mem_hecke hψ') x,
      map_add, LinearMap.add_apply, map_add, e, e']
  · intro r a
    have hc : (fun g => (r • dosetInd ℂ K a) g⁻¹) = r • dosetInd ℂ K a⁻¹ := by
      funext g
      rw [Pi.smul_apply, Pi.smul_apply, ← dosetInd_comp_inv a]
    have hb' : ∀ g y u, b.flip (ρ g y) (π g u) = b.flip y u := fun g y u => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, hb]
    rw [hc, pairing_heckeVec_dosetInd_eq_card_smul hK π ρ b hb hf hx r a, ← LinearMap.flip_apply b f (heckeVec ρ K (r • dosetInd ℂ K a⁻¹) x),
      pairing_heckeVec_dosetInd_eq_card_smul hK ρ π b.flip hb' hx hf r a⁻¹, LinearMap.flip_apply, hsym a]
    congr 1
    rw [← hb a f (ρ a⁻¹ x), Representation.self_inv_apply]

end GlobalTheory.ChainOnto

end
