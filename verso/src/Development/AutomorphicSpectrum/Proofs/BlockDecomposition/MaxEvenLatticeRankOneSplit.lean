import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.RankOne

section

variable {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]

/- English proof (translation)
Rewrite using `[hh.smul_right, hh.symm w (r • w), hh.smul_right, map_mul]`.
-/
theorem h_smul_smul {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (r r' : R) (w : V) :
    h (r • w) (r' • w) = r' * (c r * c (h w w)) := by
  rw [hh.smul_right, hh.symm w (r • w), hh.smul_right, map_mul]

/- English proof (translation)
Rewrite using `[h_smul_smul hh, map_mul, map_mul, hc, hc, hd]`. Apply the tactic sequence `ext <;> simp [mul_assoc]`.
-/
theorem phi_h {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (φ : R ≃+* k × k)
    (hc : ∀ r, φ (c r) = (φ r).swap) (r r' : R) (w : V) (δ : k) (hd : φ (h w w) = (δ, δ)) :
    φ (h (r • w) (r' • w)) = ((φ r').1 * (φ r).2 * δ, (φ r').2 * (φ r).1 * δ) := by
  rw [h_smul_smul hh, map_mul, map_mul, hc, hc, hd]
  ext <;> simp [mul_assoc]

/- English proof (translation)
Establish `h1` using `hh.smul_right r w w`. Establish `h2` using `hh.smul_right 0 w w`. Rewrite `h1` using `[h0]`. Rewrite `h2` using `[zero_smul, zero_mul]`. Rewrite `h1` using `[h2]`.

Conclude with `hu.mul_left_eq_zero.1 h1.symm`.
-/
theorem smul_eq_zero_of_unit {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (w : V)
    (hu : IsUnit (h w w)) (r : R) (h0 : r • w = 0) : r = 0 := by
  have h1 := hh.smul_right r w w
  have h2 := hh.smul_right 0 w w
  rw [h0] at h1
  rw [zero_smul, zero_mul] at h2
  rw [h2] at h1
  exact hu.mul_left_eq_zero.1 h1.symm

/- English proof (translation)
Set `S : Submodule R V` to `{ carrier := {x | ∃ r : R, x = r • w ∧ p r = 0} add_mem' := by`. Introduce and unpack `_ _ ⟨r, rfl, hr⟩ ⟨s, rfl, hs⟩`. Conclude with `⟨r + s, (add_smul _ _ _).symm, by simp [hr, hs]⟩`. Use the proof step `zero_mem' := ⟨0, (zero_smul _ _).symm, map_zero p⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `a _ ⟨r, rfl, hr⟩`. Conclude with `⟨a * r, (mul_smul _ _ _).symm, by simp [hr]⟩ }`. Establish `hle : Submodule.span R (L : Set V) ≤ S` using `Submodule.span_le.2 fun x hx => hL x hx`. Rewrite `hle` using `[hspan]`. Take `⟨r, hr, h0⟩ : w ∈ S` from `hle Submodule.mem_top`.

Establish `h1 : (1 - r) • w = 0` using `by rw [sub_smul, one_smul, ← hr, sub_self]`. Establish `h2 : r = 1` using `(sub_eq_zero.1 (smul_eq_zero_of_unit hh w hu _ h1)).symm`. Rewrite `h0` using `[h2, map_one]`. Conclude with `one_ne_zero h0`.
-/
theorem span_comp_false (p : R →+* k) {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (w : V)
    (hu : IsUnit (h w w)) (𝔬 : Subring R) (L : Submodule 𝔬 V)
    (hspan : Submodule.span R (L : Set V) = ⊤) (hL : ∀ x ∈ L, ∃ r : R, x = r • w ∧ p r = 0) : False := by
  let S : Submodule R V :=
    { carrier := {x | ∃ r : R, x = r • w ∧ p r = 0}
      add_mem' := by
        rintro _ _ ⟨r, rfl, hr⟩ ⟨s, rfl, hs⟩
        exact ⟨r + s, (add_smul _ _ _).symm, by simp [hr, hs]⟩
      zero_mem' := ⟨0, (zero_smul _ _).symm, map_zero p⟩
      smul_mem' := by
        rintro a _ ⟨r, rfl, hr⟩
        exact ⟨a * r, (mul_smul _ _ _).symm, by simp [hr]⟩ }
  have hle : Submodule.span R (L : Set V) ≤ S := Submodule.span_le.2 fun x hx => hL x hx
  rw [hspan] at hle
  obtain ⟨r, hr, h0⟩ : w ∈ S := hle Submodule.mem_top
  have h1 : (1 - r) • w = 0 := by rw [sub_smul, one_smul, ← hr, sub_self]
  have h2 : r = 1 := (sub_eq_zero.1 (smul_eq_zero_of_unit hh w hu _ h1)).symm
  rw [h2, map_one] at h0
  exact one_ne_zero h0

def lat (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (w : V) (a b : k) : Submodule 𝔬 V where
  carrier := {v | ∃ r : R, v = r • w ∧ (∃ x ∈ O, (φ r).1 = a * x) ∧ ∃ y ∈ O, (φ r).2 = b * y}
  add_mem' := by
    rintro _ _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ ⟨s, rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩
    exact ⟨r + s, (add_smul _ _ _).symm, ⟨x + x', O.add_mem _ _ hx hx', by simp [h1, h1', mul_add]⟩,
      y + y', O.add_mem _ _ hy hy', by simp [h2, h2', mul_add]⟩
  zero_mem' := ⟨0, (zero_smul _ _).symm, ⟨0, O.zero_mem, by simp⟩, 0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro ⟨s, hs⟩ _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩
    obtain ⟨hs1, hs2⟩ := (h𝔬 s).1 hs
    refine ⟨s * r, ?_, ⟨(φ s).1 * x, O.mul_mem _ _ hs1 hx, ?_⟩, (φ s).2 * y, O.mul_mem _ _ hs2 hy, ?_⟩
    · rw [mul_smul]; rfl
    · simp only [map_mul, Prod.fst_mul, h1]; ring
    · simp only [map_mul, Prod.snd_mul, h2]; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `_ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ _ ⟨r', rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩`. Rewrite using `[h𝔬, phi_h hh φ hc r r' w δ hd, h1, h2, h1', h2']`. Prove the components needed by the constructor for the conclusion. Establish `: a * x' * (b * y) * δ = x' * y`.

Combine the equalities or inequalities in the displayed calculation. Simplify `O.mul_mem _ _ hx' hy` using `[this]`. Establish `: b * y' * (a * x) * δ = y' * x`. Combine the equalities or inequalities in the displayed calculation. Simplify `O.mul_mem _ _ hy' hx` using `[this]`.

Introduce and unpack `_ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩`. Establish `hxy : (φ r).1 * (φ r).2 * δ = x * y`. Rewrite using `[h1, h2]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨φ.symm (x * y, 0), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h𝔬]`. Simplify using `using O.mul_mem _ _ hx hy`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[phi_h hh φ hc r r w δ hd, map_add, hc]`. Simplify using `only [RingEquiv.apply_symm_apply]`.

Use `ext`. Simplify using `using hxy`. Simplify `(by rw [mul_comm (φ r).2 (φ r).1]; exact hxy : (φ r).2 * (φ r).1 * δ = x * y)` using `[mul_comm (φ r).1 (φ r).2]`.
-/
theorem lat_even {O : ValuationSubring k} {φ : R ≃+* k × k} {c : R →+* R} {𝔬 : Subring R}
    (hc : ∀ r, φ (c r) = (φ r).swap) (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O)
    {h : V → V → R} (hh : IsHerm c h) (w : V) (δ : k) (hd : φ (h w w) = (δ, δ)) (a b : k)
    (hab : a * b * δ = 1) : IsEvenInt c 𝔬 h (lat O φ 𝔬 h𝔬 w a b) := by
  constructor
  · rintro _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ _ ⟨r', rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩
    rw [h𝔬, phi_h hh φ hc r r' w δ hd, h1, h2, h1', h2']
    constructor
    · have : a * x' * (b * y) * δ = x' * y := by
        calc a * x' * (b * y) * δ = (a * b * δ) * (x' * y) := by ring
          _ = x' * y := by rw [hab, one_mul]
      simpa [this] using O.mul_mem _ _ hx' hy
    · have : b * y' * (a * x) * δ = y' * x := by
        calc b * y' * (a * x) * δ = (a * b * δ) * (y' * x) := by ring
          _ = y' * x := by rw [hab, one_mul]
      simpa [this] using O.mul_mem _ _ hy' hx
  · rintro _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩
    have hxy : (φ r).1 * (φ r).2 * δ = x * y := by
      rw [h1, h2]
      calc a * x * (b * y) * δ = (a * b * δ) * (x * y) := by ring
        _ = x * y := by rw [hab, one_mul]
    refine ⟨φ.symm (x * y, 0), ?_, ?_⟩
    · rw [h𝔬]
      simpa using O.mul_mem _ _ hx hy
    · apply φ.injective
      rw [phi_h hh φ hc r r w δ hd, map_add, hc]
      simp only [RingEquiv.apply_symm_apply]
      ext
      · simpa using hxy
      · simpa [mul_comm (φ r).1 (φ r).2] using (by rw [mul_comm (φ r).2 (φ r).1]; exact hxy : (φ r).2 * (φ r).1 * δ = x * y)

end

/- English proof (translation)
Introduce `k R V _ _ _ _ O φ c 𝔬 hc h𝔬 h hh w₀ hw hu L hL α β hmem`. Take `⟨⟨_, hspan⟩, ⟨hint, _⟩, hmax⟩` from `hL`. Establish `hcd : c (h w₀ w₀) = h w₀ w₀` using `(hh.symm w₀ w₀).symm`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hd⟩ : ∃ δ, φ (h w₀ w₀) = (δ, δ) := by`. Establish `h1` using `hc (h w₀ w₀)`.

Rewrite `h1` using `[hcd]`. Conclude with `⟨(φ (h w₀ w₀)).1, Prod.ext rfl (congrArg Prod.fst h1).symm⟩`. Establish `hδ : δ ≠ 0`. Establish `h1 : IsUnit (φ (h w₀ w₀))` using `hu.map φ`. Rewrite `h1` using `[hd, Prod.isUnit_iff]`.

Conclude with `h1.1.ne_zero`. Establish `hα : α ≠ 0`. Introduce and unpack `rfl`. Use `span_comp_false ((RingHom.fst k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_` and prove the remaining obligations. Take `⟨r, rfl⟩` from `hw x`.

Take `⟨⟨y, _, hy⟩, _⟩` from `(hmem r).1 hx`. Conclude with `⟨r, rfl, by simpa using hy⟩`. Establish `hβ : β ≠ 0`. Introduce and unpack `rfl`. Use `span_comp_false ((RingHom.snd k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_` and prove the remaining obligations.

Take `⟨r, rfl⟩` from `hw x`. Take `⟨_, ⟨y, _, hy⟩⟩` from `(hmem r).1 hx`. Conclude with `⟨r, rfl, by simpa using hy⟩`. Use `⟨hα, hβ, ?_⟩` and prove the remaining obligations. Establish `hγ0 : α * β * δ ≠ 0` using `mul_ne_zero (mul_ne_zero hα hβ) hδ`.

Establish `hγ : α * β * δ ∈ O`. Establish `h1 : φ.symm (α, 0) • w₀ ∈ L` using `(hmem _).2 ⟨⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩`. Establish `h2 : φ.symm (0, β) • w₀ ∈ L` using `(hmem _).2 ⟨⟨0, O.zero_mem, by simp⟩, 1, O.one_mem, by simp⟩`. Establish `h3` using `(h𝔬 _).1 (hint _ h1 _ h2)`. Rewrite `h3` using `[phi_h hh φ hc _ _ w₀ δ hd]`.

Establish `h4` using `h3.2`. Simplify using `only [RingEquiv.apply_symm_apply] at h4`. Rewrite `h4` using `[mul_comm β α]`. Then use the resulting hypothesis. Establish `hab : α / (α * β * δ) * β * δ = 1`. Clear the denominators using the available nonvanishing facts.

Establish `hle : L ≤ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β`. Introduce `v hv`. Take `⟨r, rfl⟩` from `hw v`. Take `⟨⟨x, hx, h1⟩, y, hy, h2⟩` from `(hmem r).1 hv`. Use `⟨r, rfl, ⟨α * β * δ * x, O.mul_mem _ _ hγ hx, ?_⟩, y, hy, h2⟩` and prove the remaining obligations.

Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Establish `hL₂` using `hmax _ (lat_even hc h𝔬 hh w₀ δ hd _ _ hab) hle`. Establish `hmem₂ : φ.symm (α / (α * β * δ), 0) • w₀ ∈ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β` using `⟨_, rfl, ⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩`. Take `⟨⟨x, hx, h1⟩, _⟩` from `(hmem _).1 (hL₂ hmem₂)`.

Simplify using `only [RingEquiv.apply_symm_apply] at h1`. Use `⟨α * β * δ, hγ, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : (α * β * δ)⁻¹ = x`. Apply `mul_left_cancel₀ hα` to reduce the goal to its premises. Rewrite using `[← h1, div_eq_mul_inv]`.

Rewrite using `[h2]` and apply the resulting hypothesis. Rewrite using `[hd]`.
-/
theorem unimodular_coords : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R) (𝔬 : Subring R), (∀ r, φ (c r) = (φ r).swap) → (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ h : V → V → R, IsHerm c h → ∀ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) → IsUnit (h w₀ w₀) → ∀ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → ∀ α β : k, (∀ r : R, r • w₀ ∈ L ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y)) → α ≠ 0 ∧ β ≠ 0 ∧ ∃ u : k, u ∈ O ∧ u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u := by
  intro k R V _ _ _ _ O φ c 𝔬 hc h𝔬 h hh w₀ hw hu L hL α β hmem
  obtain ⟨⟨_, hspan⟩, ⟨hint, _⟩, hmax⟩ := hL
  have hcd : c (h w₀ w₀) = h w₀ w₀ := (hh.symm w₀ w₀).symm
  obtain ⟨δ, hd⟩ : ∃ δ, φ (h w₀ w₀) = (δ, δ) := by
    have h1 := hc (h w₀ w₀)
    rw [hcd] at h1
    exact ⟨(φ (h w₀ w₀)).1, Prod.ext rfl (congrArg Prod.fst h1).symm⟩
  have hδ : δ ≠ 0 := by
    have h1 : IsUnit (φ (h w₀ w₀)) := hu.map φ
    rw [hd, Prod.isUnit_iff] at h1
    exact h1.1.ne_zero
  have hα : α ≠ 0 := by
    rintro rfl
    refine span_comp_false ((RingHom.fst k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_
    obtain ⟨r, rfl⟩ := hw x
    obtain ⟨⟨y, _, hy⟩, _⟩ := (hmem r).1 hx
    exact ⟨r, rfl, by simpa using hy⟩
  have hβ : β ≠ 0 := by
    rintro rfl
    refine span_comp_false ((RingHom.snd k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_
    obtain ⟨r, rfl⟩ := hw x
    obtain ⟨_, ⟨y, _, hy⟩⟩ := (hmem r).1 hx
    exact ⟨r, rfl, by simpa using hy⟩
  refine ⟨hα, hβ, ?_⟩
  have hγ0 : α * β * δ ≠ 0 := mul_ne_zero (mul_ne_zero hα hβ) hδ
  have hγ : α * β * δ ∈ O := by
    have h1 : φ.symm (α, 0) • w₀ ∈ L :=
      (hmem _).2 ⟨⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩
    have h2 : φ.symm (0, β) • w₀ ∈ L :=
      (hmem _).2 ⟨⟨0, O.zero_mem, by simp⟩, 1, O.one_mem, by simp⟩
    have h3 := (h𝔬 _).1 (hint _ h1 _ h2)
    rw [phi_h hh φ hc _ _ w₀ δ hd] at h3
    have h4 := h3.2
    simp only [RingEquiv.apply_symm_apply] at h4
    rwa [mul_comm β α] at h4
  have hab : α / (α * β * δ) * β * δ = 1 := by
    field_simp
  have hle : L ≤ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β := by
    intro v hv
    obtain ⟨r, rfl⟩ := hw v
    obtain ⟨⟨x, hx, h1⟩, y, hy, h2⟩ := (hmem r).1 hv
    refine ⟨r, rfl, ⟨α * β * δ * x, O.mul_mem _ _ hγ hx, ?_⟩, y, hy, h2⟩
    rw [h1]
    field_simp
  have hL₂ := hmax _ (lat_even hc h𝔬 hh w₀ δ hd _ _ hab) hle
  have hmem₂ : φ.symm (α / (α * β * δ), 0) • w₀ ∈ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β :=
    ⟨_, rfl, ⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩
  obtain ⟨⟨x, hx, h1⟩, _⟩ := (hmem _).1 (hL₂ hmem₂)
  simp only [RingEquiv.apply_symm_apply] at h1
  refine ⟨α * β * δ, hγ, ?_, ?_⟩
  · have h2 : (α * β * δ)⁻¹ = x := by
      apply mul_left_cancel₀ hα
      rw [← h1, div_eq_mul_inv]
    rwa [h2]
  · rw [hd]

end GlobalTheory.CompanionTheory.KFin.RankOne
