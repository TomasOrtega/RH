import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.MemSpanOfFrobeniusMemSpan
import Formalism.CoboundaryTransfers.WachBridges

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

/- English proof (translation)
Unfold `StatLiftSub`. Introduce `ℓ _ H₁ H₂ H₁' H₂' _ _ _ _ _ _ _ _ Hf₁ Hf₂ Hf₁' Hf₂' h h' res₂ cor₁ cor₂ g E hg hcr hcomm hres hcor hlift κ' hκ'`. Take `⟨κ₁, hκ₁, he⟩` from `hlift (res₂ κ') (hres κ' hκ')`. Use `set v := padicValNat ℓ g with hv`. Take `⟨m, hm⟩ : ℓ ^ v ∣ g` from `pow_padicValNat_dvd`.

Establish `hcop : ¬ ℓ ∣ m`. Introduce `hdvd`. Establish `h5 : ℓ ^ (v + 1) ∣ g`. Rewrite using `[hm, pow_succ]`. Conclude with `mul_dvd_mul_left _ hdvd`.

Conclude with `pow_succ_padicValNat_not_dvd (by omega) h5`. Establish `hu : IsUnit (m : ℤ_[ℓ])`. Rewrite using `[PadicInt.isUnit_iff]`. Establish `h1 : ‖((m : ℤ) : ℤ_[ℓ])‖ ≤ 1` using `PadicInt.norm_le_one _`. Establish `h2 : ¬ ‖((m : ℤ) : ℤ_[ℓ])‖ < 1`.

Rewrite using `[PadicInt.norm_int_lt_one_iff_dvd]`. Conclude with `hcop` after adjusting the coercions. Establish `h3 : ((m : ℤ) : ℤ_[ℓ]) = (m : ℤ_[ℓ])` using `Int.cast_natCast m`. Rewrite using `[← h3]`. Conclude with `le_antisymm h1 (not_lt.1 h2)`.

Use `⟨(↑hu.unit⁻¹ : ℤ_[ℓ]) • cor₁ κ₁, Hf₁'.smul_mem _ (hcor κ₁ hκ₁), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hcomm, he, map_smul, hcr, smul_smul, smul_smul]`. Use `congr 1`. Establish `hg' : (g : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ v * (m : ℤ_[ℓ])`. Rewrite using `[hm]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hum : (↑hu.unit⁻¹ : ℤ_[ℓ]) * (m : ℤ_[ℓ]) = 1` using `hu.val_inv_mul`. Rewrite using `[hg', pow_add]`. Take the linear combination `(ℓ : ℤ_[ℓ]) ^ E * (ℓ : ℤ_[ℓ]) ^ v * hum`.
-/
theorem lift_to_subgroup_exists : StatLiftSub := by
  unfold StatLiftSub
  intro ℓ _ H₁ H₂ H₁' H₂' _ _ _ _ _ _ _ _ Hf₁ Hf₂ Hf₁' Hf₂' h h' res₂ cor₁ cor₂ g E hg hcr hcomm hres hcor hlift κ' hκ'
  obtain ⟨κ₁, hκ₁, he⟩ := hlift (res₂ κ') (hres κ' hκ')
  set v := padicValNat ℓ g with hv
  obtain ⟨m, hm⟩ : ℓ ^ v ∣ g := pow_padicValNat_dvd
  have hcop : ¬ ℓ ∣ m := by
    intro hdvd
    have h5 : ℓ ^ (v + 1) ∣ g := by
      rw [hm, pow_succ]
      exact mul_dvd_mul_left _ hdvd
    exact pow_succ_padicValNat_not_dvd (by omega) h5
  have hu : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((m : ℤ) : ℤ_[ℓ])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      exact_mod_cast hcop
    have h3 : ((m : ℤ) : ℤ_[ℓ]) = (m : ℤ_[ℓ]) := Int.cast_natCast m
    rw [← h3]
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨(↑hu.unit⁻¹ : ℤ_[ℓ]) • cor₁ κ₁, Hf₁'.smul_mem _ (hcor κ₁ hκ₁), ?_⟩
  rw [map_smul, hcomm, he, map_smul, hcr, smul_smul, smul_smul]
  congr 1
  have hg' : (g : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ v * (m : ℤ_[ℓ]) := by
    rw [hm]
    push_cast
    ring
  have hum : (↑hu.unit⁻¹ : ℤ_[ℓ]) * (m : ℤ_[ℓ]) = 1 := hu.val_inv_mul
  rw [hg', pow_add]
  linear_combination (ℓ : ℤ_[ℓ]) ^ E * (ℓ : ℤ_[ℓ]) ^ v * hum

/- English proof (translation)
Unfold `StatRegX`. Introduce `ℓ _ A _ _ B M D _ _ _ _ W hreg y hy hX`. Unfold `RegXQ at hreg`. Establish `hy' : B.Q ^ M • y ∈ W.N` using `hy`. Establish `key : ∀ z : D, B.Q • z ∈ W.N → B.X • z ∈ W.N → z ∈ W.N`.

Introduce `z hQ hXz`. Take `⟨m', hm', he⟩` from `hreg (B.X • z) hXz ⟨B.Q • z, hQ, by rw [smul_smul, smul_smul, mul_comm]⟩`. Establish `h0 : B.X • (z - m') = 0` using `by rw [smul_sub, he, sub_self]`. Establish `hz : z - m' = 0` using `W.X_inj _ h0`. Rewrite `hz` using `[sub_eq_zero]`.

Rewrite using `[hz]`. Conclude with `hm'`. It suffices to establish `h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro h`. Simplify using `using h`. Consider the case `succ j ih`. Introduce `h`. Apply `ih` to reduce the goal to its premises.

Apply `key` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `h`. Rewrite using `[smul_comm]`. Conclude with `W.N.smul_mem _ hX`.
-/
theorem regulator_bound_for_x : StatRegX := by
  unfold StatRegX
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg y hy hX
  unfold RegXQ at hreg
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → B.X • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg (B.X • z) hXz ⟨B.Q • z, hQ, by rw [smul_smul, smul_smul, mul_comm]⟩
    have h0 : B.X • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := W.X_inj _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

/- English proof (translation)
Unfold `StatRegL`. Introduce `ℓ _ A _ _ B M D _ _ _ _ W hreg htor y hy hX`. Unfold `RegLQ at hreg`. Unfold `NoTors at htor`. Establish `hy' : B.Q ^ M • y ∈ W.N` using `hy`.

Establish `key : ∀ z : D, B.Q • z ∈ W.N → (ℓ : ℤ_[ℓ]) • z ∈ W.N → z ∈ W.N`. Introduce `z hQ hXz`. Take `⟨m', hm', he⟩` from `hreg ((ℓ : ℤ_[ℓ]) • z) hXz ⟨B.Q • z, hQ, smul_comm _ _ _⟩`. Establish `h0 : (ℓ : ℤ_[ℓ]) • (z - m') = 0` using `by rw [smul_sub, he, sub_self]`. Establish `hz : z - m' = 0` using `htor _ h0`.

Rewrite `hz` using `[sub_eq_zero]`. Rewrite using `[hz]`. Conclude with `hm'`. It suffices to establish `h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro h`. Simplify using `using h`. Consider the case `succ j ih`. Introduce `h`.

Apply `ih` to reduce the goal to its premises. Apply `key` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `h`. Rewrite using `[smul_comm]`.

Conclude with `W.N.smul_mem _ hX`.
-/
theorem regulator_bound_for_l : StatRegL := by
  unfold StatRegL
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg htor y hy hX
  unfold RegLQ at hreg
  unfold NoTors at htor
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → (ℓ : ℤ_[ℓ]) • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg ((ℓ : ℤ_[ℓ]) • z) hXz ⟨B.Q • z, hQ, smul_comm _ _ _⟩
    have h0 : (ℓ : ℤ_[ℓ]) • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := htor _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

/- English proof (translation)
Unfold `StatExtCocycle`. Introduce `ℓ _ A _ _ B M D _ _ _ _ W H _ _ cl κ E e hD hlift`. Take `⟨x, hxN, hx⟩` from `hlift E.e E.e_mem`. Establish `hπφ : E.S.π.f (E.Wp.φ x - x) = 0`. Rewrite using `[map_sub, E.S.π.φ_comm, hx, map_smul, E.φe, sub_self]`.

Establish `hπγ : E.S.π.f (E.Wp.γ x - x) = 0`. Rewrite using `[map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]`. Take `⟨y, hy⟩` from `(E.S.exact _).1 hπφ`. Take `⟨z, hz⟩` from `(E.S.exact _).1 hπγ`. Establish `hd : (W.γ y - y) - (W.φ z - z) = 0`.

Apply `E.S.ι_inj` to reduce the goal to its premises. Simplify using `only [map_sub, map_zero, E.S.ι.γ_comm, E.S.ι.φ_comm, hy, hz, E.Wp.comm]`. Normalize the expressions using the abelian group laws. Establish `hZ : ((y, z) : D × D) ∈ W.Z1` using `by show ((y, z) : D × D) ∈ LinearMap.ker ((W.γ - LinearMap.id).coprod (-(W.φ - LinearMap.id)))`. Simplify using `only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.neg_apply]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hQ : B.Q ^ M • y ∈ W.N`. Apply `E.S.sat` to reduce the goal to its premises. Rewrite using `[map_smul, hy, smul_sub]`. Conclude with `E.Wp.N.sub_mem (E.Wp.φ_N x hxN) (E.Wp.N.smul_mem _ hxN)`.

Take `⟨x', hx'N, hx'⟩` from `E.Wp.γ_N x hxN`. Establish `hπx' : E.S.π.f x' = 0`. Apply `E.Wt.X_inj` to reduce the goal to its premises. Rewrite using `[← map_smul, ← hx', map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]`. Take `⟨x₀, hx₀⟩` from `(E.S.exact x').1 hπx'`.

Establish `hx₀N : x₀ ∈ W.N` using `E.S.sat x₀ (by rw [hx₀]; exact hx'N)`. Establish `hzX : z = B.X • x₀`. Apply `E.S.ι_inj` to reduce the goal to its premises. Rewrite using `[map_smul, hx₀, hz, hx']`. Use `⟨⟨(y, z), hZ⟩, ?_, ?_⟩` and prove the remaining obligations.

Unfold `WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1`. Conclude with `⟨⟨hQ, x₀, hx₀N, hzX⟩, hd⟩`. Conclude with `hD ((ℓ : ℤ_[ℓ]) ^ e) x ⟨(y, z), hZ⟩ hx hy hz`.
-/
theorem extension_class_is_cocycle : StatExtCocycle := by
  unfold StatExtCocycle
  intro ℓ _ A _ _ B M D _ _ _ _ W H _ _ cl κ E e hD hlift
  obtain ⟨x, hxN, hx⟩ := hlift E.e E.e_mem
  have hπφ : E.S.π.f (E.Wp.φ x - x) = 0 := by
    rw [map_sub, E.S.π.φ_comm, hx, map_smul, E.φe, sub_self]
  have hπγ : E.S.π.f (E.Wp.γ x - x) = 0 := by
    rw [map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨y, hy⟩ := (E.S.exact _).1 hπφ
  obtain ⟨z, hz⟩ := (E.S.exact _).1 hπγ
  have hd : (W.γ y - y) - (W.φ z - z) = 0 := by
    apply E.S.ι_inj
    simp only [map_sub, map_zero, E.S.ι.γ_comm, E.S.ι.φ_comm, hy, hz, E.Wp.comm]
    abel
  have hZ : ((y, z) : D × D) ∈ W.Z1 := by
    show ((y, z) : D × D) ∈ LinearMap.ker ((W.γ - LinearMap.id).coprod (-(W.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = (W.γ y - y) - (W.φ z - z) := by abel
      _ = 0 := hd
  have hQ : B.Q ^ M • y ∈ W.N := by
    apply E.S.sat
    rw [map_smul, hy, smul_sub]
    exact E.Wp.N.sub_mem (E.Wp.φ_N x hxN) (E.Wp.N.smul_mem _ hxN)
  obtain ⟨x', hx'N, hx'⟩ := E.Wp.γ_N x hxN
  have hπx' : E.S.π.f x' = 0 := by
    apply E.Wt.X_inj
    rw [← map_smul, ← hx', map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨x₀, hx₀⟩ := (E.S.exact x').1 hπx'
  have hx₀N : x₀ ∈ W.N := E.S.sat x₀ (by rw [hx₀]; exact hx'N)
  have hzX : z = B.X • x₀ := by
    apply E.S.ι_inj
    rw [map_smul, hx₀, hz, hx']
  refine ⟨⟨(y, z), hZ⟩, ?_, ?_⟩
  · unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    exact ⟨⟨hQ, x₀, hx₀N, hzX⟩, hd⟩
  · exact hD ((ℓ : ℤ_[ℓ]) ^ e) x ⟨(y, z), hZ⟩ hx hy hz

/- English proof (translation)
Unfold `StatRatSurj`. Introduce `ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g e₁ hp hnat hcoc hherr honto hlift`. Unfold `Formalism.CoboundaryTransfers.RatSurj`. Introduce `y z hyz`. Establish `memZ : ∀ a b : D₂, W₂.γ a - a - (W₂.φ b - b) = 0 → ((a, b) : D₂ × D₂) ∈ W₂.Z1`.

Introduce `a b h`. Use `show ((a, b) : D₂ × D₂) ∈ LinearMap.ker ((W₂.γ - LinearMap.id).coprod (-(W₂.φ - LinearMap.id)))`. Simplify using `only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.neg_apply]`. Combine the equalities or inequalities in the displayed calculation. Establish `hyz'` using `hyz`.

Unfold `WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hyz'`. Take `⟨⟨hQ₂, n₂, hn₂, hz₂⟩, hd₂⟩` from `hyz'`. Establish `hκ : cl₂ ⟨(y, z), memZ y z hd₂⟩ ∈ Hf₂` using `hcoc _ hyz`. Take `⟨k, κ₁, hκ₁, hgk⟩` from `honto _ hκ`. Take `⟨⟨⟨y₁, z₁⟩, hZ₁⟩, hpr₁c, hpr₁⟩` from `hlift κ₁ hκ₁`.

Establish `hc₁` using `hpr₁c`. Unfold `WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hc₁`. Take `⟨⟨hQ₁', n₁, hn₁, hz₁'⟩, hd₁'r⟩` from `hc₁`. Establish `hz₁ : z₁ = B.X • n₁` using `hz₁'`. Establish `hd₁ : W₁.γ y₁ - y₁ - (W₁.φ z₁ - z₁) = 0` using `hd₁'r`.

Establish `hQ₁ : B.Q ^ M • y₁ ∈ W₁.N` using `hQ₁'`. Establish `hd₁' : W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁) = 0`. Establish `h` using `congrArg S.π.f hd₁`. Simplify `h` using `[map_sub, S.π.γ_comm, S.π.φ_comm]`. Take `⟨c, hc⟩ : ∃ c : ℤ_[ℓ], c = (ℓ : ℤ_[ℓ]) ^ (e₁ + k)` from `⟨_, rfl⟩`.

Establish `hcP : W₂.Cocycle (S.π.f y₁ - c • y) (S.π.f z₁ - c • z)`. Unfold `WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1`. Use `⟨⟨?_, S.π.f n₁ - c • n₂, W₂.N.sub_mem (S.π.N_le _ hn₁) (W₂.N.smul_of_tower_mem c hn₂), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← map_smul, smul_comm (B.Q ^ M) c y]`. Conclude with `W₂.N.sub_mem (S.π.N_le _ hQ₁) (W₂.N.smul_of_tower_mem c hQ₂)`.

Rewrite using `[hz₁, hz₂, map_smul, smul_sub, smul_comm c B.X n₂]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sub, map_sub, map_smul, map_smul]`. Simplify using `only [smul_sub]`. Normalize the expressions using the abelian group laws.

Use `_ = 0 := by rw [hd₁', hd₂, smul_zero, sub_zero]`. Establish `hcl : cl₂ (⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩ - c • ⟨(y, z), memZ y z hd₂⟩) = 0`. Apply the tactic sequence `rw [map_sub, map_smul, ← hnat ⟨(y₁, z₁), hZ₁⟩ ⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩ (by first | rfl | simp [Formalism.CoboundaryTransfers.Hom.f2]), hpr₁, map_smul, hgk, hc, pow_add, mul_smul, sub_self]`. Establish `hcob` using `hherr _ hcP hcl`. Unfold `WachMod.IsCob1 at hcob`.

Take `⟨x, hxN, hx1, hx2⟩` from `hcob`. Express the relevant statement in the definitionally equal form `S.π.f y₁ - c • y = W₂.φ x - x at hx1`. Express the relevant statement in the definitionally equal form `S.π.f z₁ - c • z = W₂.γ x - x at hx2`. Use `⟨e₁ + k, y₁, z₁, hpr₁c, x, hxN, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp, ← hc, ← hx1]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hp, ← hc, ← hx2]`. Normalize the expressions using the abelian group laws.
-/
theorem rational_points_map_surjective : StatRatSurj := by
  unfold StatRatSurj
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g e₁ hp hnat hcoc hherr honto hlift
  unfold Formalism.CoboundaryTransfers.RatSurj
  intro y z hyz
  have memZ : ∀ a b : D₂, W₂.γ a - a - (W₂.φ b - b) = 0 → ((a, b) : D₂ × D₂) ∈ W₂.Z1 := by
    intro a b h
    show ((a, b) : D₂ × D₂) ∈ LinearMap.ker ((W₂.γ - LinearMap.id).coprod (-(W₂.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = W₂.γ a - a - (W₂.φ b - b) := by abel
      _ = 0 := h
  have hyz' := hyz
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hyz'
  obtain ⟨⟨hQ₂, n₂, hn₂, hz₂⟩, hd₂⟩ := hyz'
  have hκ : cl₂ ⟨(y, z), memZ y z hd₂⟩ ∈ Hf₂ := hcoc _ hyz
  obtain ⟨k, κ₁, hκ₁, hgk⟩ := honto _ hκ
  obtain ⟨⟨⟨y₁, z₁⟩, hZ₁⟩, hpr₁c, hpr₁⟩ := hlift κ₁ hκ₁
  have hc₁ := hpr₁c
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hc₁
  obtain ⟨⟨hQ₁', n₁, hn₁, hz₁'⟩, hd₁'r⟩ := hc₁
  have hz₁ : z₁ = B.X • n₁ := hz₁'
  have hd₁ : W₁.γ y₁ - y₁ - (W₁.φ z₁ - z₁) = 0 := hd₁'r
  have hQ₁ : B.Q ^ M • y₁ ∈ W₁.N := hQ₁'
  have hd₁' : W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁) = 0 := by
    have h := congrArg S.π.f hd₁
    simpa [map_sub, S.π.γ_comm, S.π.φ_comm] using h
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ], c = (ℓ : ℤ_[ℓ]) ^ (e₁ + k) := ⟨_, rfl⟩
  have hcP : W₂.Cocycle (S.π.f y₁ - c • y) (S.π.f z₁ - c • z) := by
    unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    refine ⟨⟨?_, S.π.f n₁ - c • n₂, W₂.N.sub_mem (S.π.N_le _ hn₁) (W₂.N.smul_of_tower_mem c hn₂), ?_⟩, ?_⟩
    · rw [smul_sub, ← map_smul, smul_comm (B.Q ^ M) c y]
      exact W₂.N.sub_mem (S.π.N_le _ hQ₁) (W₂.N.smul_of_tower_mem c hQ₂)
    · rw [hz₁, hz₂, map_smul, smul_sub, smul_comm c B.X n₂]
    · calc W₂.γ (S.π.f y₁ - c • y) - (S.π.f y₁ - c • y) - (W₂.φ (S.π.f z₁ - c • z) - (S.π.f z₁ - c • z))
          = (W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁)) -
              c • (W₂.γ y - y - (W₂.φ z - z)) := by
            rw [map_sub, map_sub, map_smul, map_smul]
            simp only [smul_sub]
            abel
        _ = 0 := by rw [hd₁', hd₂, smul_zero, sub_zero]
  have hcl : cl₂ (⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩ - c • ⟨(y, z), memZ y z hd₂⟩) = 0 := by
    rw [map_sub, map_smul, ← hnat ⟨(y₁, z₁), hZ₁⟩ ⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩
      (by first | rfl | simp [Formalism.CoboundaryTransfers.Hom.f2]), hpr₁, map_smul, hgk, hc, pow_add, mul_smul, sub_self]
  have hcob := hherr _ hcP hcl
  unfold WachMod.IsCob1 at hcob
  obtain ⟨x, hxN, hx1, hx2⟩ := hcob
  change S.π.f y₁ - c • y = W₂.φ x - x at hx1
  change S.π.f z₁ - c • z = W₂.γ x - x at hx2
  refine ⟨e₁ + k, y₁, z₁, hpr₁c, x, hxN, ?_, ?_⟩
  · rw [hp, ← hc, ← hx1]
    abel
  · rw [hp, ← hc, ← hx2]
    abel

end Formalism.RepresentationBoundsCohomology.N2
