import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HfAlgSmulRight

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Establish `hm : b ∈ IsLocalRing.maximalIdeal O` using `hb`. Rewrite `hm` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]`. Conclude with `h hm`.
-/
theorem isUnit_of_not_dvd {ϖ b : O} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ b) : IsUnit b := by
  by_contra hb
  have hm : b ∈ IsLocalRing.maximalIdeal O := hb
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.mem_span_singleton] at hm
  exact h hm

/- English proof (translation)
Introduce `h`. Conclude with `hϖ.ne_zero (IsFractionRing.injective O K (by simpa using h))`.
-/
theorem alg_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : algebraMap O K ϖ ≠ 0 := by
  intro h
  exact hϖ.ne_zero (IsFractionRing.injective O K (by simpa using h))

/- English proof (translation)
Establish `h1 : Irreducible (c ϖ)` using `(MulEquiv.irreducible_iff c.toMulEquiv).2 hϖ`. Take `⟨u, hu⟩` from `IsDiscreteValuationRing.associated_of_irreducible O h1 hϖ`. Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations. Establish `e : c ϖ = ((u⁻¹ : Oˣ) : O) * ϖ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hcK, e, map_mul]`.
-/
theorem exists_unit_conj (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : Oˣ, cK (algebraMap O K ϖ) = algebraMap O K u * algebraMap O K ϖ := by
  have h1 : Irreducible (c ϖ) := (MulEquiv.irreducible_iff c.toMulEquiv).2 hϖ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible O h1 hϖ
  refine ⟨u⁻¹, ?_⟩
  have e : c ϖ = ((u⁻¹ : Oˣ) : O) * ϖ := by
    calc c ϖ = c ϖ * u * ((u⁻¹ : Oˣ) : O) := by simp [mul_assoc]
      _ = ϖ * ((u⁻¹ : Oˣ) : O) := by rw [hu]
      _ = _ := mul_comm _ _
  rw [hcK, e, map_mul]

/- English proof (translation)
Take `⟨b, hb⟩` from `hβ'`. Take `⟨g, hg⟩` from `hγ`. Establish `h0 : algebraMap O K ϖ ≠ 0` using `alg_ne_zero hϖ`. Establish `hbu : IsUnit b`. Apply `isUnit_of_not_dvd hϖ` to reduce the goal to its premises.

Introduce and unpack `⟨e, rfl⟩`. Apply `hβ` to reduce the goal to its premises. Use `⟨e, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[map_mul]`. Conclude with `(mul_left_cancel₀ h0 hb)`.

Take `⟨u, rfl⟩` from `hbu`. Use `⟨g * ((u⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Establish `e1 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1`. Rewrite using `[← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[← hg, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, mul_one]`. Use `_ = algebraMap O K g * ((algebraMap O K ϖ * β) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by rw [hb]`.

Use `_ = _ := by ring`.
-/
theorem exists_ratio {ϖ : O} (hϖ : Irreducible ϖ) {β γ : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (hγ : algebraMap O K ϖ * γ ∈ (algebraMap O K).range) :
    ∃ a : O, γ = algebraMap O K a * β := by
  obtain ⟨b, hb⟩ := hβ'
  obtain ⟨g, hg⟩ := hγ
  have h0 : algebraMap O K ϖ ≠ 0 := alg_ne_zero hϖ
  have hbu : IsUnit b := by
    apply isUnit_of_not_dvd hϖ
    rintro ⟨e, rfl⟩
    apply hβ
    refine ⟨e, ?_⟩
    rw [map_mul] at hb
    exact (mul_left_cancel₀ h0 hb)
  obtain ⟨u, rfl⟩ := hbu
  refine ⟨g * ((u⁻¹ : Oˣ) : O), ?_⟩
  apply mul_left_cancel₀ h0
  have e1 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul]; simp
  rw [← hg, map_mul]
  calc algebraMap O K g = algebraMap O K g * (algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by
        rw [e1, mul_one]
    _ = algebraMap O K g * ((algebraMap O K ϖ * β) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by rw [hb]
    _ = _ := by ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hd`. Take `⟨u, rfl⟩` from `isUnit_of_not_dvd hϖ hd`. Apply `hβ` to reduce the goal to its premises.

Establish `e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Establish `: β = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K (u : O) * β)`. Rewrite using `[← mul_assoc, e1, one_mul]`.

Rewrite using `[this]`. Conclude with `mul_mem ⟨_, rfl⟩ h`. Introduce and unpack `⟨e, rfl⟩`. Rewrite using `[map_mul, mul_comm (algebraMap O K ϖ), mul_assoc]`. Conclude with `mul_mem ⟨_, rfl⟩ hβ'`.
-/
theorem ratio_mem_iff {ϖ : O} (hϖ : Irreducible ϖ) {β : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (a : O) : algebraMap O K a * β ∈ (algebraMap O K).range ↔ ϖ ∣ a := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u, rfl⟩ := isUnit_of_not_dvd hϖ hd
    apply hβ
    have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul]; simp
    have : β = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K (u : O) * β) := by
      rw [← mul_assoc, e1, one_mul]
    rw [this]
    exact mul_mem ⟨_, rfl⟩ h
  · rintro ⟨e, rfl⟩
    rw [map_mul, mul_comm (algebraMap O K ϖ), mul_assoc]
    exact mul_mem ⟨_, rfl⟩ hβ'

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_unit_conj c cK hcK (K := K) hϖ`. Establish `h1` using `(hSD _).1 hw l hl`. Rewrite `h1` using `[hf_algSmul_left, hu]`. Establish `e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1`. Rewrite using `[← map_mul]`.

Simplify using the standard rewrite rules. Establish `: algebraMap O K ϖ * hf cK J v l = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K (u : O) * algebraMap O K ϖ * hf cK J v l)`. Rewrite using `[mul_assoc, ← mul_assoc (algebraMap O K ((u⁻¹ : Oˣ) : O)), e1, one_mul]`. Rewrite using `[this]`. Conclude with `mul_mem ⟨_, rfl⟩ h1`.
-/
theorem mul_pair_mem (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hw : ϖ • v ∈ L)
    {l : Fin r → K} (hl : l ∈ L) :
    algebraMap O K ϖ * hf cK J v l ∈ (algebraMap O K).range := by
  obtain ⟨u, hu⟩ := exists_unit_conj c cK hcK (K := K) hϖ
  have h1 := (hSD _).1 hw l hl
  rw [hf_algSmul_left, hu] at h1
  have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
    rw [← map_mul]; simp
  have : algebraMap O K ϖ * hf cK J v l = algebraMap O K ((u⁻¹ : Oˣ) : O) *
      (algebraMap O K (u : O) * algebraMap O K ϖ * hf cK J v l) := by
    rw [mul_assoc, ← mul_assoc (algebraMap O K ((u⁻¹ : Oˣ) : O)), e1, one_mul]
  rw [this]
  exact mul_mem ⟨_, rfl⟩ h1

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hv ((hSD v).2 hcon)`. Use `set β := hf cK J v l0 with hβdef`.

Establish `hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range` using `mul_pair_mem c cK hcK hϖ hSD hw hl0`. Establish `hβ0 : β ≠ 0`. Introduce `h0`. Conclude with `hβ (h0 ▸ zero_mem _)`. Establish `hex : ∀ l : L.toAddSubgroup, ∃ a : O, hf cK J v (l : Fin r → K) = algebraMap O K a * β` using `fun l => exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw l.2)`.

Use `choose a ha using hex`. Establish `hadd : ∀ x y : L.toAddSubgroup, a (x + y) = a x + a y`. Introduce `x y`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Apply `mul_right_cancel₀ hβ0` to reduce the goal to its premises.

Rewrite using `[← ha, map_add, add_mul, ← ha, ← ha]`. Simplify using `using hf_add_right cK J v (x : Fin r → K) y`. Set `ψ : L.toAddSubgroup →+ IsLocalRing.ResidueField O` to `AddMonoidHom.mk' (fun l => IsLocalRing.residue O (a l)) (by`. Introduce `x y`. Rewrite using `[hadd, map_add])`.

Establish `hker : (perp cK J L v).toAddSubgroup.addSubgroupOf L.toAddSubgroup = ψ.ker`. Use extensionality with `l`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `(l : Fin r → K) ∈ perp cK J L v ↔ IsLocalRing.residue O (a l) = 0`. Rewrite using `[mem_perp, IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton, ← ratio_mem_iff hϖ hβ hβ', ← ha]`.

Conclude with `⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩`. Establish `hsurj : Function.Surjective ψ`. Introduce `z`. Take `⟨b, rfl⟩` from `IsLocalRing.residue_surjective z`. Establish `hm : b • l0 ∈ L.toAddSubgroup` using `L.smul_mem b hl0`.

Use `⟨⟨b • l0, hm⟩, ?_⟩` and prove the remaining obligations. Establish `: a ⟨b • l0, hm⟩ = b`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Apply `mul_right_cancel₀ hβ0` to reduce the goal to its premises. Rewrite using `[← ha]`.

Conclude with `hf_algSmul_right cK J b v l0`. Express the relevant statement in the definitionally equal form `IsLocalRing.residue O (a ⟨b • l0, hm⟩) = _`. Rewrite using `[this]`. Rewrite using `[AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj]`. Conclude with `Nat.card_congr AddSubgroup.topEquiv.toEquiv`.
-/
theorem perp_relIndex (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hv : v ∉ L)
    (hw : ϖ • v ∈ L) :
    (perp cK J L v).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (IsLocalRing.ResidueField O) := by
  classical
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  set β := hf cK J v l0 with hβdef
  have hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hβ0 : β ≠ 0 := by
    intro h0
    exact hβ (h0 ▸ zero_mem _)
  have hex : ∀ l : L.toAddSubgroup, ∃ a : O, hf cK J v (l : Fin r → K) = algebraMap O K a * β :=
    fun l => exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw l.2)
  choose a ha using hex
  have hadd : ∀ x y : L.toAddSubgroup, a (x + y) = a x + a y := by
    intro x y
    apply IsFractionRing.injective O K
    apply mul_right_cancel₀ hβ0
    rw [← ha, map_add, add_mul, ← ha, ← ha]
    simpa using hf_add_right cK J v (x : Fin r → K) y
  let ψ : L.toAddSubgroup →+ IsLocalRing.ResidueField O :=
    AddMonoidHom.mk' (fun l => IsLocalRing.residue O (a l)) (by
      intro x y; rw [hadd, map_add])
  have hker : (perp cK J L v).toAddSubgroup.addSubgroupOf L.toAddSubgroup = ψ.ker := by
    ext l
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (l : Fin r → K) ∈ perp cK J L v ↔ IsLocalRing.residue O (a l) = 0
    rw [mem_perp, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton,
      ← ratio_mem_iff hϖ hβ hβ', ← ha]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    have hm : b • l0 ∈ L.toAddSubgroup := L.smul_mem b hl0
    refine ⟨⟨b • l0, hm⟩, ?_⟩
    have : a ⟨b • l0, hm⟩ = b := by
      apply IsFractionRing.injective O K
      apply mul_right_cancel₀ hβ0
      rw [← ha]
      exact hf_algSmul_right cK J b v l0
    change IsLocalRing.residue O (a ⟨b • l0, hm⟩) = _
    rw [this]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj]
  exact Nat.card_congr AddSubgroup.topEquiv.toEquiv

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Simplify using `only [Pi.smul_apply, Algebra.smul_def] at this`. Conclude with `mul_left_cancel₀ (alg_ne_zero hϖ) this`.
-/
theorem smul_injective {ϖ : O} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Fin r → K => ϖ • x) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  exact mul_left_cancel₀ (alg_ne_zero hϖ) this

/- English proof (translation)
Use `set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'`. Establish `hinj : Function.Injective f.toAddMonoidHom` using `smul_injective hϖ`. Establish `e : ∀ P : Submodule O (Fin r → K), (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom` using `fun P => by`. Use extensionality with `x`. Simplify using `[Submodule.mem_map]`.

Establish `hsub : ∀ P : Submodule O (Fin r → K), (P.map f).toAddSubgroup ≤ P.toAddSubgroup`. Introduce `P x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Conclude with `P.smul_mem ϖ hy`. Establish `hBA : (M.map f).toAddSubgroup ≤ (L.map f).toAddSubgroup` using `fun x hx => Submodule.map_mono h hx`.

Establish `hML : M.toAddSubgroup ≤ L.toAddSubgroup` using `h`. Establish `e1 : (M.map f).toAddSubgroup.relIndex (L.map f).toAddSubgroup = M.toAddSubgroup.relIndex L.toAddSubgroup`. Rewrite using `[e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`. Establish `h1` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hBA (hsub L)`. Establish `h2` using `AddSubgroup.relIndex_mul_relIndex _ _ _ (hsub M) hML`.

Rewrite `h1` using `[e1]`. Establish `h3 : M.toAddSubgroup.relIndex L.toAddSubgroup * idx ϖ L = idx ϖ M * M.toAddSubgroup.relIndex L.toAddSubgroup`. Simplify using `only [idx]`. Rewrite using `[h1, h2]`. Rewrite `h3` using `[mul_comm]`.

Conclude with `(Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h3).symm`.
-/
theorem idx_eq_of_le {ϖ : O} (hϖ : Irreducible ϖ) {M L : Submodule O (Fin r → K)} (h : M ≤ L)
    (hi : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) : idx ϖ M = idx ϖ L := by
  set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
  have hinj : Function.Injective f.toAddMonoidHom := smul_injective hϖ
  have e : ∀ P : Submodule O (Fin r → K),
      (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom := fun P => by
    ext x; simp [Submodule.mem_map]
  have hsub : ∀ P : Submodule O (Fin r → K), (P.map f).toAddSubgroup ≤ P.toAddSubgroup := by
    intro P x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact P.smul_mem ϖ hy
  have hBA : (M.map f).toAddSubgroup ≤ (L.map f).toAddSubgroup :=
    fun x hx => Submodule.map_mono h hx
  have hML : M.toAddSubgroup ≤ L.toAddSubgroup := h
  have e1 : (M.map f).toAddSubgroup.relIndex (L.map f).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have h1 := AddSubgroup.relIndex_mul_relIndex _ _ _ hBA (hsub L)
  have h2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (hsub M) hML
  rw [e1] at h1
  have h3 : M.toAddSubgroup.relIndex L.toAddSubgroup * idx ϖ L =
      idx ϖ M * M.toAddSubgroup.relIndex L.toAddSubgroup := by
    simp only [idx]; rw [h1, h2]
  rw [mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h3).symm

end GlobalTheory.HermNbr
