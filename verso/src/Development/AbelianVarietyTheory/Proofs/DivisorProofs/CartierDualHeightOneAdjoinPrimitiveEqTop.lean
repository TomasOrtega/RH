import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HeightOneDual

variable {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H]

/- English proof (translation)
Rewrite using `[cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]`. Introduce `a b`. Rewrite using `[map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, CartierDual.one_apply]`. Express the relevant statement in the definitionally equal form `_ = δ (a * b)`. Rewrite using `[hδ a b]`.

Express the relevant statement in the definitionally equal form `δ a * counit b + counit a * δ b = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cobOne_toConv_eq_zero {δ : H →ₗ[K] K} (hδ : ReciprocityTheory.PGsh.IsPtDer δ) :
    cobOne K (CartierDual K H) (WithConv.toConv δ) = 0 := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]
  intro a b
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply]
  change _ = δ (a * b)
  rw [hδ a b]
  change δ a * counit b + counit a * δ b = _
  ring

/- English proof (translation)
Rewrite using `[CartierDual.mul_apply, CartierDual.pair_tmul]`. Simplify using `only [ReciprocityTheory.PGsh.convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]`. Generalize the expression as in `comul (R := K) y = t`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Consider the case `tmul a b => simp [mul_comm]`.
-/
theorem apply_convD (φ : CartierDual K H) (δ : H →ₗ[K] K) (y : H) :
    φ (ReciprocityTheory.PGsh.convD δ y) = (φ * WithConv.toConv δ) y := by
  rw [CartierDual.mul_apply, CartierDual.pair_tmul]
  simp only [ReciprocityTheory.PGsh.convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize comul (R := K) y = t
  induction t with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a b => simp [mul_comm]

/- English proof (translation)
Introduce `p hp K H _ _ _ _ _ _ hpow`. Use `set ε := counitAlgHom K H with hεdef`. Use `set S := Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} with hSdef`. Use `haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)`. Set `b` to `Module.finBasis K (AugCot ε)`.

Use `choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)`. Set `y : Fin (Module.finrank K (AugCot ε)) → H` to `fun i => (x i : H)`. Establish `hy : ∀ i, y i ∈ RingHom.ker ε` using `fun i => (x i).2`. Establish `hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, AugCot.d ε (∑ i, l i • y i) = ∑ i, l i • b i`. Introduce `l`.

Simplify using `[y, map_sum, hx]`. Establish `hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, (∑ i, l i • y i) ∈ RingHom.ker ε`. Introduce `l`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Conclude with `Ideal.mul_mem_left _ _ (hy i)`. Establish `hspan : ∀ z ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K, z - ∑ i, l i • y i ∈ RingHom.ker ε ^ 2`. Introduce `z hz`. Use `⟨b.repr (AugCot.d ε z), ?_⟩` and prove the remaining obligations. Establish `h1 : AugCot.d ε (z - ∑ i, b.repr (AugCot.d ε z) i • y i) = 0`.

Rewrite using `[map_sub, hsum, b.sum_repr, sub_self]`. Rewrite `h1` using `[AugCot.d_of_mem _ (sub_mem hz (hmem _)), Ideal.toCotangent_eq_zero]`. Then use the resulting hypothesis. Establish `hind : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 → l = 0`. Introduce `l hl`. Establish `h1 : AugCot.d ε (∑ i, l i • y i) = 0`.

Rewrite using `[AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]`. Conclude with `hl`. Rewrite `h1` using `[hsum]`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i`.

Establish `: IsNoetherianRing H` using `isNoetherian_of_tower K inferInstance`. Establish `hnil : IsNilpotent (RingHom.ker ε)`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `f hf`. Conclude with `⟨p, hpow f hf⟩`.

Establish `hsurj` using `GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil y hy hspan`. Take `⟨δ, hδ, hδx⟩` from `GlobalTheory.HeightOneHopf.exists_isPtDer_dual y hy hind`. Set `Z : Set H` to `{h | ∀ φ ∈ S, φ h = 0}`. Establish `hZε : ∀ h ∈ Z, ε h = 0` using `fun h hh => by`. Establish `h1` using `hh 1 S.one_mem`.

Rewrite `h1` using `[CartierDual.one_apply]`. Then use the resulting hypothesis. Establish `hZD : ∀ i, ∀ h ∈ Z, ReciprocityTheory.PGsh.convD (δ i) h ∈ Z` using `fun i h hh φ hφ => by`. Rewrite using `[apply_convD]`. Conclude with `hh _ (S.mul_mem hφ (Algebra.subset_adjoin (cobOne_toConv_eq_zero (hδ i))))`. Establish `hZ0 : ∀ h ∈ Z, h = 0`.

Introduce `h hh`. Take `⟨P, rfl⟩` from `hsurj h`. Establish `hc` using `ReciprocityTheory.PGsh.coeff_eq_zero_of_stable ε y hy (fun i => ReciprocityTheory.PGsh.convD (δ i)) (fun i => ReciprocityTheory.PGsh.convD_mul _ (hδ i)) (fun i j => (ReciprocityTheory.PGsh.counit_convD (δ i) (y j)).trans (hδx i j)) hsurj (CharP.cast_eq_zero K p) (fun n h0 hn => b …`. Rewrite using `[isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff K p]`. Conclude with `Nat.not_dvd_of_pos_of_lt h0 hn) Z hZε hZD P hh`.

Conclude with `ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span y (fun j => hpow _ (hy j)) (ReciprocityTheory.PGsh.mem_span_pow_of_coeff hc)`. Set `W : Submodule K (Module.Dual K H)` to `(Subalgebra.toSubmodule S).map (CartierDual.toDual K H).toLinearMap`. Establish `hW : W.dualCoannihilator = ⊥`. Use `eq_bot_iff.2 fun h hh => ?_` and prove the remaining obligations. Rewrite `hh` using `[Submodule.mem_dualCoannihilator]`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `hZ0 h fun φ hφ => hh _ ⟨φ, hφ, rfl⟩`. Establish `hWtop : W = ⊤`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW, Submodule.dualAnnihilator_bot]`. Rewrite using `[← Algebra.toSubmodule_eq_top, eq_top_iff]`.

Introduce `φ _`. Establish `h1 : CartierDual.toDual K H φ ∈ W` using `hWtop ▸ Submodule.mem_top`. Take `⟨ψ, hψ, e⟩` from `h1`. Rewrite `hψ` using `[(CartierDual.toDual K H).injective e]`. Then use the resulting hypothesis.
-/
theorem adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ a ∈ augIdeal K H, a ^ p = 0) →
    Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  intro p hp K H _ _ _ _ _ _ hpow
  classical
  set ε := counitAlgHom K H with hεdef
  set S := Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} with hSdef
  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  let y : Fin (Module.finrank K (AugCot ε)) → H := fun i => (x i : H)
  have hy : ∀ i, y i ∈ RingHom.ker ε := fun i => (x i).2
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • y i) = ∑ i, l i • b i := by
    intro l
    simp [y, map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, (∑ i, l i • y i) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hy i)
  have hspan : ∀ z ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      z - ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 := by
    intro z hz
    refine ⟨b.repr (AugCot.d ε z), ?_⟩
    have h1 : AugCot.d ε (z - ∑ i, b.repr (AugCot.d ε z) i • y i) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hz (hmem _)), Ideal.toCotangent_eq_zero] at h1
  have hind : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 → l = 0 := by
    intro l hl
    have h1 : AugCot.d ε (∑ i, l i • y i) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i
  have : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil y hy hspan
  obtain ⟨δ, hδ, hδx⟩ := GlobalTheory.HeightOneHopf.exists_isPtDer_dual y hy hind

  let Z : Set H := {h | ∀ φ ∈ S, φ h = 0}
  have hZε : ∀ h ∈ Z, ε h = 0 := fun h hh => by
    have h1 := hh 1 S.one_mem
    rwa [CartierDual.one_apply] at h1
  have hZD : ∀ i, ∀ h ∈ Z, ReciprocityTheory.PGsh.convD (δ i) h ∈ Z := fun i h hh φ hφ => by
    rw [apply_convD]
    exact hh _ (S.mul_mem hφ (Algebra.subset_adjoin (cobOne_toConv_eq_zero (hδ i))))
  have hZ0 : ∀ h ∈ Z, h = 0 := by
    intro h hh
    obtain ⟨P, rfl⟩ := hsurj h
    have hc := ReciprocityTheory.PGsh.coeff_eq_zero_of_stable ε y hy (fun i => ReciprocityTheory.PGsh.convD (δ i))
      (fun i => ReciprocityTheory.PGsh.convD_mul _ (hδ i)) (fun i j =>
        (ReciprocityTheory.PGsh.counit_convD (δ i) (y j)).trans (hδx i j)) hsurj
      (CharP.cast_eq_zero K p) (fun n h0 hn => by
        rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff K p]
        exact Nat.not_dvd_of_pos_of_lt h0 hn) Z hZε hZD P hh
    exact ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span y (fun j => hpow _ (hy j))
      (ReciprocityTheory.PGsh.mem_span_pow_of_coeff hc)

  let W : Submodule K (Module.Dual K H) :=
    (Subalgebra.toSubmodule S).map (CartierDual.toDual K H).toLinearMap
  have hW : W.dualCoannihilator = ⊥ := by
    refine eq_bot_iff.2 fun h hh => ?_
    rw [Submodule.mem_dualCoannihilator] at hh
    rw [Submodule.mem_bot]
    exact hZ0 h fun φ hφ => hh _ ⟨φ, hφ, rfl⟩
  have hWtop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW, Submodule.dualAnnihilator_bot]
  rw [← Algebra.toSubmodule_eq_top, eq_top_iff]
  intro φ _
  have h1 : CartierDual.toDual K H φ ∈ W := hWtop ▸ Submodule.mem_top
  obtain ⟨ψ, hψ, e⟩ := h1
  rwa [(CartierDual.toDual K H).injective e] at hψ

end GlobalTheory.HeightOneDual
