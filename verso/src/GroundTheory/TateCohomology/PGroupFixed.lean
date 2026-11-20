import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open Representation

section Fixed

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

/- English proof (translation)
Establish `hp : ∀ x : V, p • x = 0` using `fun x => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]`. Set `cast : ZMod p →+* k` to `ZMod.castHom (dvd_refl p) k`. Set `f : (G → ZMod p) →+ V` to `{ toFun := fun c => ∑ g, cast (c g) • ρ g m map_zero' := by simp map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }`. Establish `hf : ∀ c, f c = ∑ g, cast (c g) • ρ g m` using `fun _ => rfl`.

Establish `hstab : ∀ (h : G) (c : G → ZMod p), ρ h (f c) = f (fun g => c (h⁻¹ * g))`. Introduce `h c`. Rewrite using `[hf, hf, map_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_` and prove the remaining obligations. Simplify using `[map_mul, Module.End.mul_apply]`.

Establish `hmem : ∀ (h : G) (x : V), x ∈ f.range → ρ h x ∈ f.range`. Introduce and unpack `h x ⟨c, rfl⟩`. Conclude with `⟨fun g => c (h⁻¹ * g), (hstab h c).symm⟩`. Establish `: Finite f.range` using `Finite.of_injective (fun x : f.range => (⟨x.1, AddMonoidHom.mem_range.mp x.2⟩ : Set.range f)) fun a b h => Subtype.ext (congrArg Subtype.val h)`. Set `: MulAction G f.range` to `{ smul := fun h x => ⟨ρ h x, hmem h x x.2⟩ one_smul := fun x => Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `ρ 1 (x : V) = x`. Use the proof step `simp)`. Use `mul_smul := fun a b x => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `ρ (a * b) (x : V) = ρ a (ρ b x)`. Rewrite using `[map_mul, Module.End.mul_apply]) }`.

Establish `hm' : m ∈ f.range` using `⟨Pi.single 1 1, by`. Rewrite using `[hf, Fintype.sum_eq_single (1 : G) (fun g hg => by simp [hg])]`. Use the proof step `simp⟩`. Establish `horder : addOrderOf (⟨m, hm'⟩ : f.range) = p` using `addOrderOf_eq_prime (Subtype.ext (by simpa using hp m)) (fun h => hm (congrArg Subtype.val h))`. Establish `hdvd : p ∣ Nat.card f.range`.

Use `addOrderOf_dvd_natCard (⟨m, hm'⟩ : f.range)` as an intermediate fact. Rewrite `this` using `[horder]`. Then use the resulting hypothesis. Establish `h0 : (0 : f.range) ∈ MulAction.fixedPoints G f.range` using `fun g => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `ρ g 0 = 0`. Use the proof step `simp)`.

Take `⟨b, hb, hb0⟩` from `hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point f.range hdvd h0`. Use `⟨b.1, ?_, fun h => hb0 (Subtype.ext h.symm), fun g => congrArg Subtype.val (hb g)⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `AddMonoidHom.mem_range.mp b.2`. Rewrite using `[← hc, hf]`. Conclude with `Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)`.
-/
theorem exists_fixed_mem_span_orbit (hG : IsPGroup p G) (ρ : Representation k G V) {m : V}
    (hm : m ≠ 0) :
    ∃ v ∈ Submodule.span k (Set.range fun g : G => ρ g m), v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  classical
  have hp : ∀ x : V, p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  let cast : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  let f : (G → ZMod p) →+ V :=
    { toFun := fun c => ∑ g, cast (c g) • ρ g m
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  have hf : ∀ c, f c = ∑ g, cast (c g) • ρ g m := fun _ => rfl
  have hstab : ∀ (h : G) (c : G → ZMod p), ρ h (f c) = f (fun g => c (h⁻¹ * g)) := by
    intro h c
    rw [hf, hf, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp [map_mul, Module.End.mul_apply]
  have hmem : ∀ (h : G) (x : V), x ∈ f.range → ρ h x ∈ f.range := by
    rintro h x ⟨c, rfl⟩
    exact ⟨fun g => c (h⁻¹ * g), (hstab h c).symm⟩
  have : Finite f.range :=
    Finite.of_injective (fun x : f.range => (⟨x.1, AddMonoidHom.mem_range.mp x.2⟩ : Set.range f))
      fun a b h => Subtype.ext (congrArg Subtype.val h)
  let : MulAction G f.range :=
    { smul := fun h x => ⟨ρ h x, hmem h x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ρ 1 (x : V) = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ρ (a * b) (x : V) = ρ a (ρ b x)
        rw [map_mul, Module.End.mul_apply]) }
  have hm' : m ∈ f.range := ⟨Pi.single 1 1, by
    rw [hf, Fintype.sum_eq_single (1 : G) (fun g hg => by simp [hg])]
    simp⟩
  have horder : addOrderOf (⟨m, hm'⟩ : f.range) = p :=
    addOrderOf_eq_prime (Subtype.ext (by simpa using hp m))
      (fun h => hm (congrArg Subtype.val h))
  have hdvd : p ∣ Nat.card f.range := by
    have := addOrderOf_dvd_natCard (⟨m, hm'⟩ : f.range)
    rwa [horder] at this
  have h0 : (0 : f.range) ∈ MulAction.fixedPoints G f.range := fun g => Subtype.ext (by
    change ρ g 0 = 0
    simp)
  obtain ⟨b, hb, hb0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point f.range hdvd h0
  refine ⟨b.1, ?_, fun h => hb0 (Subtype.ext h.symm), fun g => congrArg Subtype.val (hb g)⟩
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.mp b.2
  rw [← hc, hf]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end Fixed

section Nakayama

variable {k G V : Type*} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hWf⟩` from `Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)`. Take `⟨v, hvspan, hv0, hvfix⟩` from `exists_fixed_mem_span_orbit hG ρ.dual hf0`. Establish `hd : ∀ (g : G) (φ : Module.Dual k V) (x : V), ρ.dual g φ x = φ (ρ g⁻¹ x)` using `fun _ _ _ => rfl`. Establish `hvW : W ≤ LinearMap.ker v`.

Establish `hle : Submodule.span k (Set.range fun g : G => ρ.dual g f) ≤ W.dualAnnihilator`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_dualAnnihilator]`. Introduce `w hw`.

Rewrite using `[hd]`. Conclude with `hWf (hW g⁻¹ hw)`. Introduce `w hw`. Conclude with `(Submodule.mem_dualAnnihilator v).mp (hle hvspan) w hw`. Establish `hvI : Coinvariants.ker ρ ≤ LinearMap.ker v`.

Rewrite using `[Coinvariants.ker, Submodule.span_le]`. Introduce and unpack `_ ⟨⟨g, x⟩, rfl⟩`. Use `congrArg (fun φ : Module.Dual k V => φ x) (hvfix g⁻¹)` as an intermediate fact. Simplify using `only [hd, inv_inv] at this`. Simplify using `[this]`.

Apply `hv0` to reduce the goal to its premises. Use extensionality with `x`. Establish `hx : x ∈ W ⊔ Coinvariants.ker ρ` using `h ▸ Submodule.mem_top`. Conclude with `(sup_le hvW hvI) hx`.
-/
theorem eq_top_of_sup_coinvariantsKer_eq_top (hG : IsPGroup p G) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g : G, W ≤ W.comap (ρ g)) (h : W ⊔ Coinvariants.ker ρ = ⊤) :
    W = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
  obtain ⟨v, hvspan, hv0, hvfix⟩ := exists_fixed_mem_span_orbit hG ρ.dual hf0
  have hd : ∀ (g : G) (φ : Module.Dual k V) (x : V), ρ.dual g φ x = φ (ρ g⁻¹ x) :=
    fun _ _ _ => rfl

  have hvW : W ≤ LinearMap.ker v := by
    have hle : Submodule.span k (Set.range fun g : G => ρ.dual g f) ≤ W.dualAnnihilator := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      intro w hw
      rw [hd]
      exact hWf (hW g⁻¹ hw)
    intro w hw
    exact (Submodule.mem_dualAnnihilator v).mp (hle hvspan) w hw

  have hvI : Coinvariants.ker ρ ≤ LinearMap.ker v := by
    rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    have := congrArg (fun φ : Module.Dual k V => φ x) (hvfix g⁻¹)
    simp only [hd, inv_inv] at this
    simp [this]
  apply hv0
  ext x
  have hx : x ∈ W ⊔ Coinvariants.ker ρ := h ▸ Submodule.mem_top
  exact (sup_le hvW hvI) hx

/- English proof (translation)
Establish `hbot` using `eq_top_of_sup_coinvariantsKer_eq_top hG ρ ⊥ (fun _ => bot_le) (by rw [bot_sup_eq, h])`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ (⊥ : Submodule k V)` using `hbot ▸ Submodule.mem_top`. Establish `hy : y ∈ (⊥ : Submodule k V)` using `hbot ▸ Submodule.mem_top`. Rewrite `hx`, `hy` using `[Submodule.mem_bot]`.

Rewrite using `[hx, hy]`.
-/
theorem subsingleton_of_coinvariantsKer_eq_top (hG : IsPGroup p G) (ρ : Representation k G V)
    (h : Coinvariants.ker ρ = ⊤) : Subsingleton V := by
  have hbot := eq_top_of_sup_coinvariantsKer_eq_top hG ρ ⊥ (fun _ => bot_le) (by rw [bot_sup_eq, h])
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

end Nakayama

end GroundTheory.GroupCoh
