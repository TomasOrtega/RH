import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced

noncomputable section

namespace GlobalTheory.FinGL.GGFree

open GlobalTheory.FinGL Formalism.L2.DIV Module

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `[eig, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_eig (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ) (v : V) :
    v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Set `S : Subrepresentation τ` to `{ toSubmodule := Submodule.span ℂ (Set.range fun g => τ g w) apply_mem_toSubmodule := by`. Introduce `g v hv`. Establish `: Submodule.span ℂ (Set.range fun g => τ g w) ≤ (Submodule.span ℂ (Set.range fun g => τ g w)).comap (τ g)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`.

Conclude with `Submodule.subset_span ⟨g * h, by simp⟩`. Conclude with `this hv }`. Break down `hτ.eq_bot_or_eq_top S with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : w ∈ S.toSubmodule` using `Submodule.subset_span ⟨1, by simp⟩`.

Rewrite `h1` using `[h]`. Conclude with `hw h1`. Conclude with `congrArg Subrepresentation.toSubmodule h`.
-/
theorem span_orbit (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) (w : V) (hw : w ≠ 0) :
    Submodule.span ℂ (Set.range fun g => τ g w) = ⊤ := by
  let S : Subrepresentation τ :=
    { toSubmodule := Submodule.span ℂ (Set.range fun g => τ g w)
      apply_mem_toSubmodule := by
        intro g v hv
        have : Submodule.span ℂ (Set.range fun g => τ g w) ≤
            (Submodule.span ℂ (Set.range fun g => τ g w)).comap (τ g) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp⟩
        exact this hv }
  rcases hτ.eq_bot_or_eq_top S with h | h
  · exfalso
    have h1 : w ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at h1
    exact hw h1
  · exact congrArg Subrepresentation.toSubmodule h

def avg (τ : Representation ℂ G V) (U : Subgroup G) [Fintype U] (χ : G → ℂ) : Module.End ℂ V :=
  ∑ u : U, χ ((u : G)⁻¹) • τ u

variable (τ : Representation ℂ G V) (U : Subgroup G) [Fintype U] (χ : G → ℂ)

/- English proof (translation)
Unfold `avg`. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : U)) _ _ fun u => ?_` and prove the remaining obligations. Establish `: χ ((u : G)⁻¹) = χ a * χ ((a * u)⁻¹)`. Rewrite using `[mul_comm, ← hmul _ (U.inv_mem (U.mul_mem ha u.2)) _ ha]`.

Simplify using the standard rewrite rules. Simplify using `only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, mul_smul_comm, smul_smul, this]`.
-/
theorem mul_avg (hmul : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (a : G) (ha : a ∈ U) :
    τ a * avg τ U χ = χ a • avg τ U χ := by
  unfold avg
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : U)) _ _ fun u => ?_
  have : χ ((u : G)⁻¹) = χ a * χ ((a * u)⁻¹) := by
    rw [mul_comm, ← hmul _ (U.inv_mem (U.mul_mem ha u.2)) _ ha]; simp
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, mul_smul_comm, smul_smul, this]

/- English proof (translation)
Unfold `avg`. Rewrite using `[Finset.sum_mul, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : U)) _ _ fun u => ?_` and prove the remaining obligations. Establish `: χ ((u : G)⁻¹) = χ a * χ ((u * a)⁻¹)`. Rewrite using `[← hmul _ ha _ (U.inv_mem (U.mul_mem u.2 ha))]`.

Simplify using the standard rewrite rules. Simplify using `only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_mul_assoc, smul_smul, this]`.
-/
theorem avg_mul (hmul : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (a : G) (ha : a ∈ U) :
    avg τ U χ * τ a = χ a • avg τ U χ := by
  unfold avg
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : U)) _ _ fun u => ?_
  have : χ ((u : G)⁻¹) = χ a * χ ((u * a)⁻¹) := by
    rw [← hmul _ ha _ (U.inv_mem (U.mul_mem u.2 ha))]; simp
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_mul_assoc, smul_smul, this]

/- English proof (translation)
Unfold `avg`. Rewrite using `[LinearMap.sum_apply]`. Establish `: ∀ u : U, (χ ((u : G)⁻¹) • τ u) w = w` using `fun u => by`. Rewrite using `[LinearMap.smul_apply, (mem_eig τ U χ w).1 hw u u.2, smul_smul, ← hmul _ (U.inv_mem u.2) _ u.2]`. Simplify using `[h1]`.

Simplify using `[this, Nat.cast_smul_eq_nsmul]`.
-/
theorem avg_apply (h1 : χ 1 = 1) (hmul : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (w : V)
    (hw : w ∈ eig τ U χ) : avg τ U χ w = (Fintype.card U : ℂ) • w := by
  unfold avg
  rw [LinearMap.sum_apply]
  have : ∀ u : U, (χ ((u : G)⁻¹) • τ u) w = w := fun u => by
    rw [LinearMap.smul_apply, (mem_eig τ U χ w).1 hw u u.2, smul_smul, ← hmul _ (U.inv_mem u.2) _ u.2]
    simp [h1]
  simp [this, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Rewrite using `[mem_eig]`. Introduce `g hg`. Conclude with `LinearMap.congr_fun (mul_avg τ U χ hmul g hg) v`.
-/
theorem avg_mem (hmul : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (v : V) :
    avg τ U χ v ∈ eig τ U χ := by
  rw [mem_eig]
  intro g hg
  exact LinearMap.congr_fun (mul_avg τ U χ hmul g hg) v

/- English proof (translation)
Establish `hN : (Fintype.card U : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Use `set E := avg τ U χ with hE`. Use `set W := eig τ (U : Set G) χ with hW`. Establish `hgen : ∀ w ∈ W, w ≠ 0 → ∀ P : Submodule ℂ V, (∀ h, E (τ h w) ∈ P) → W ≤ P`. Introduce `w _ hw0 P hP v hv`.

Establish `h2 : (⊤ : Submodule ℂ V) ≤ P.comap E`. Rewrite using `[← span_orbit τ hτ w hw0]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `hP h`.

Establish `h3 : E v ∈ P` using `h2 Submodule.mem_top`. Rewrite `h3` using `[avg_apply τ U χ h1 hmul v hv]`. Conclude with `(P.smul_mem_iff hN).1 h3`. Establish `hcomm : ∀ g h, ∀ w ∈ W, E (τ g (E (τ h w))) = E (τ h (E (τ g w)))`. Introduce `g h w hw`.

Use `LinearMap.congr_fun (hc g h) w` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite `this` using `[avg_apply τ U χ h1 hmul w hw]`. Simplify using `only [map_smul] at this`. Conclude with `smul_right_injective V hN this`.

Break down `subsingleton_or_nontrivial W with hs | hs` into its components or cases. Simplify using `[Module.finrank_zero_of_subsingleton]`. Establish `hsc : ∀ g, ∃ c : ℂ, ∀ w ∈ W, E (τ g w) = c • w`. Introduce `g`. Set `B : Module.End ℂ W` to `(E * τ g).restrict (p := W) (q := W) fun x _ => avg_mem τ U χ hmul _`.

Take `⟨c, hc'⟩` from `Module.End.exists_eigenvalue B`. Take `⟨w0, hw0⟩` from `hc'.exists_hasEigenvector`. Establish `e0 : E (τ g w0) = c • (w0 : V)` using `congrArg Subtype.val hw0.apply_eq_smul`. Use `hgen w0 w0.2 (fun h => hw0.2 (Subtype.ext h)) (LinearMap.ker (E * τ g - c • LinearMap.id)) (fun h => by` as an intermediate fact. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.

Rewrite using `[hcomm g h w0 w0.2, e0, map_smul, map_smul])`. Use `⟨c, fun w hw => ?_⟩` and prove the remaining obligations. Simplify `this hw` using `[sub_eq_zero]`. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Use `hgen w w.2 (fun h => hw (Subtype.ext h)) (Submodule.span ℂ {(w : V)}) (fun h => by` as an intermediate fact.

Take `⟨c, hc'⟩` from `hsc h`. Rewrite using `[hc' w w.2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))`. Use `finrank_le_one w fun v => ?_` and prove the remaining obligations. Take `⟨c, hc'⟩` from `Submodule.mem_span_singleton.1 (this v.2)`.

Conclude with `⟨c, Subtype.ext hc'⟩`.
-/
theorem finrank_le_one_of_comm [FiniteDimensional ℂ V] (hτ : τ.IsIrreducible) (h1 : χ 1 = 1)
    (hmul : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u')
    (hc : ∀ g h, avg τ U χ * τ g * avg τ U χ * τ h * avg τ U χ =
      avg τ U χ * τ h * avg τ U χ * τ g * avg τ U χ) :
    finrank ℂ (eig τ U χ) ≤ 1 := by
  have hN : (Fintype.card U : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set E := avg τ U χ with hE
  set W := eig τ (U : Set G) χ with hW
  have hgen : ∀ w ∈ W, w ≠ 0 → ∀ P : Submodule ℂ V, (∀ h, E (τ h w) ∈ P) → W ≤ P := by
    intro w _ hw0 P hP v hv
    have h2 : (⊤ : Submodule ℂ V) ≤ P.comap E := by
      rw [← span_orbit τ hτ w hw0]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      exact hP h
    have h3 : E v ∈ P := h2 Submodule.mem_top
    rw [avg_apply τ U χ h1 hmul v hv] at h3
    exact (P.smul_mem_iff hN).1 h3
  have hcomm : ∀ g h, ∀ w ∈ W, E (τ g (E (τ h w))) = E (τ h (E (τ g w))) := by
    intro g h w hw
    have := LinearMap.congr_fun (hc g h) w
    simp only [Module.End.mul_apply] at this
    rw [avg_apply τ U χ h1 hmul w hw] at this
    simp only [map_smul] at this
    exact smul_right_injective V hN this
  rcases subsingleton_or_nontrivial W with hs | hs
  · simp [Module.finrank_zero_of_subsingleton]
  have hsc : ∀ g, ∃ c : ℂ, ∀ w ∈ W, E (τ g w) = c • w := by
    intro g
    let B : Module.End ℂ W := (E * τ g).restrict (p := W) (q := W) fun x _ => avg_mem τ U χ hmul _
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue B
    obtain ⟨w0, hw0⟩ := hc'.exists_hasEigenvector
    have e0 : E (τ g w0) = c • (w0 : V) := congrArg Subtype.val hw0.apply_eq_smul
    have := hgen w0 w0.2 (fun h => hw0.2 (Subtype.ext h)) (LinearMap.ker (E * τ g - c • LinearMap.id)) (fun h => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
      rw [hcomm g h w0 w0.2, e0, map_smul, map_smul])
    refine ⟨c, fun w hw => ?_⟩
    simpa [sub_eq_zero] using this hw
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have := hgen w w.2 (fun h => hw (Subtype.ext h)) (Submodule.span ℂ {(w : V)}) (fun h => by
    obtain ⟨c, hc'⟩ := hsc h
    rw [hc' w w.2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine finrank_le_one w fun v => ?_
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 (this v.2)
  exact ⟨c, Subtype.ext hc'⟩

/- English proof (translation)
Use `finrank_le_one_of_comm τ U χ hτ h1 hmul ?_` and prove the remaining obligations. Use `set E := avg τ U χ with hE`. Establish `hT : ∀ u ∈ U, ∀ u' ∈ U, ∀ n, E * τ (u * n * u') * E = (χ u * χ u') • (E * τ n * E)`. Introduce `u hu u' hu' n`. Rewrite using `[map_mul, map_mul, ← mul_assoc, ← mul_assoc, avg_mul τ U χ hmul u hu, mul_assoc, mul_avg τ U χ hmul u' hu']`.

Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (χ u')]`. Both sides reduce to the same expression. Establish `hz : ∀ n, ∀ a ∈ U, ∀ b ∈ U, a * n = n * b → χ a ≠ χ b → E * τ n * E = 0`. Introduce `n a ha b hb e hne`. Establish `e1` using `hT a ha 1 U.one_mem n`.

Establish `e2` using `hT 1 U.one_mem b hb n`. Rewrite `e1` using `[mul_one, e, h1, mul_one]`. Rewrite `e2` using `[one_mul, h1, one_mul, e1, ← sub_eq_zero, ← sub_smul]`. Conclude with `(smul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne)`. Establish `hσ : ∀ x, E * τ (σ x) * E = E * τ x * E`.

Introduce `x`. Take `⟨u, hu, u', hu', n, rfl, hn⟩` from `hB x`. Rewrite using `[σmul, σmul, ← mul_assoc (σ u'), hT _ (σU _ hu') _ (σU _ hu), hT _ hu _ hu', σχ _ hu, σχ _ hu', mul_comm (χ u')]`. Use `congr 1`. Distinguish the cases in `hg : ∀ a ∈ U, ∀ b ∈ U, a * n = n * b → χ a = χ b`.

Rewrite using `[hn hg]`. Use `push Not at hg`. Take `⟨a, ha, b, hb, e, hne⟩` from `hg`. Rewrite using `[hz n a ha b hb e hne, hz (σ n) (σ b) (σU _ hb) (σ a) (σU _ ha) (by rw [← σmul, ← σmul, e]) (by rw [σχ _ ha, σχ _ hb]; exact hne.symm)]`. Establish `hexp : ∀ g h, E * τ g * E * τ h * E = ∑ u : U, χ ((u : G)⁻¹) • (E * τ (g * u * h) * E)`.

Introduce `g h`. Establish `: τ g * E * τ h = ∑ u : U, χ ((u : G)⁻¹) • τ (g * u * h)`. Rewrite using `[hE, avg, Finset.mul_sum, Finset.sum_mul]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Establish `hinv : ∀ u ∈ U, χ ((σ u)⁻¹) = χ u⁻¹`. Introduce `u hu`. Establish `e1 : χ (σ u) * χ (σ u)⁻¹ = 1` using `by rw [← hmul _ (σU _ hu) _ (U.inv_mem (σU _ hu))]; simp [h1]`. Establish `e2 : χ u * χ u⁻¹ = 1` using `by rw [← hmul _ hu _ (U.inv_mem hu)]; simp [h1]`. Rewrite `e1` using `[σχ _ hu]`.

Conclude with `mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e2) (e1.trans e2.symm)`. Set `s : U ≃ U` to `Function.Involutive.toPerm (fun u => ⟨σ u, σU _ u.2⟩) fun u => Subtype.ext (σσ _)`. Establish `hE2 : ∀ g h, E * τ g * E * τ h * E = E * τ (σ h) * E * τ (σ g) * E`. Introduce `g h`. Rewrite using `[hexp, hexp]`.

Use `Fintype.sum_equiv s _ _ fun u => ?_` and prove the remaining obligations. Establish `: ((s u : U) : G) = σ u` using `rfl`. Rewrite using `[this, hinv _ u.2, ← hσ, σmul, σmul, mul_assoc (σ h)]`. Introduce `g h`. Rewrite using `[hE2, hσ, mul_assoc (E * τ h) E, mul_assoc (E * τ h), hσ]`.

Simplify using `only [mul_assoc]`.
-/
theorem gelfand [FiniteDimensional ℂ V] (hτ : τ.IsIrreducible) (h1 : χ 1 = 1)
    (hmul : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u')
    (σ : G → G) (σmul : ∀ x y, σ (x * y) = σ y * σ x) (σσ : ∀ x, σ (σ x) = x)
    (σU : ∀ u ∈ U, σ u ∈ U) (σχ : ∀ u ∈ U, χ (σ u) = χ u)
    (hB : ∀ g, ∃ u ∈ U, ∃ u' ∈ U, ∃ n, g = u * n * u' ∧
      ((∀ a ∈ U, ∀ b ∈ U, a * n = n * b → χ a = χ b) → σ n = n)) :
    finrank ℂ (eig τ U χ) ≤ 1 := by
  refine finrank_le_one_of_comm τ U χ hτ h1 hmul ?_
  set E := avg τ U χ with hE
  have hT : ∀ u ∈ U, ∀ u' ∈ U, ∀ n, E * τ (u * n * u') * E = (χ u * χ u') • (E * τ n * E) := by
    intro u hu u' hu' n
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, avg_mul τ U χ hmul u hu, mul_assoc, mul_avg τ U χ hmul u' hu']
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (χ u')]
    rfl
  have hz : ∀ n, ∀ a ∈ U, ∀ b ∈ U, a * n = n * b → χ a ≠ χ b → E * τ n * E = 0 := by
    intro n a ha b hb e hne
    have e1 := hT a ha 1 U.one_mem n
    have e2 := hT 1 U.one_mem b hb n
    rw [mul_one, e, h1, mul_one] at e1
    rw [one_mul, h1, one_mul, e1, ← sub_eq_zero, ← sub_smul] at e2
    exact (smul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne)
  have hσ : ∀ x, E * τ (σ x) * E = E * τ x * E := by
    intro x
    obtain ⟨u, hu, u', hu', n, rfl, hn⟩ := hB x
    rw [σmul, σmul, ← mul_assoc (σ u'), hT _ (σU _ hu') _ (σU _ hu), hT _ hu _ hu', σχ _ hu, σχ _ hu', mul_comm (χ u')]
    congr 1
    by_cases hg : ∀ a ∈ U, ∀ b ∈ U, a * n = n * b → χ a = χ b
    · rw [hn hg]
    · push Not at hg
      obtain ⟨a, ha, b, hb, e, hne⟩ := hg
      rw [hz n a ha b hb e hne, hz (σ n) (σ b) (σU _ hb) (σ a) (σU _ ha) (by rw [← σmul, ← σmul, e])
        (by rw [σχ _ ha, σχ _ hb]; exact hne.symm)]
  have hexp : ∀ g h, E * τ g * E * τ h * E = ∑ u : U, χ ((u : G)⁻¹) • (E * τ (g * u * h) * E) := by
    intro g h
    have : τ g * E * τ h = ∑ u : U, χ ((u : G)⁻¹) • τ (g * u * h) := by
      rw [hE, avg, Finset.mul_sum, Finset.sum_mul]
      simp
    calc E * τ g * E * τ h * E = E * (τ g * E * τ h) * E := by simp only [mul_assoc]
      _ = _ := by rw [this, Finset.mul_sum, Finset.sum_mul]; simp
  have hinv : ∀ u ∈ U, χ ((σ u)⁻¹) = χ u⁻¹ := by
    intro u hu
    have e1 : χ (σ u) * χ (σ u)⁻¹ = 1 := by rw [← hmul _ (σU _ hu) _ (U.inv_mem (σU _ hu))]; simp [h1]
    have e2 : χ u * χ u⁻¹ = 1 := by rw [← hmul _ hu _ (U.inv_mem hu)]; simp [h1]
    rw [σχ _ hu] at e1
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e2) (e1.trans e2.symm)
  let s : U ≃ U := Function.Involutive.toPerm (fun u => ⟨σ u, σU _ u.2⟩) fun u => Subtype.ext (σσ _)
  have hE2 : ∀ g h, E * τ g * E * τ h * E = E * τ (σ h) * E * τ (σ g) * E := by
    intro g h
    rw [hexp, hexp]
    refine Fintype.sum_equiv s _ _ fun u => ?_
    have : ((s u : U) : G) = σ u := rfl
    rw [this, hinv _ u.2, ← hσ, σmul, σmul, mul_assoc (σ h)]
  intro g h
  rw [hE2, hσ, mul_assoc (E * τ h) E, mul_assoc (E * τ h), hσ]
  simp only [mul_assoc]

end Abstract

section Comb

/- English proof (translation)
Set `f : Equiv.Perm (Fin n)` to `w.trans Fin.revPerm`. Establish `hf : ∀ i, f i = (w i).rev` using `fun _ => rfl`. Establish `mono : ∀ p : Equiv.Perm (Fin n), (∀ a b : Fin n, b.val = a.val + 1 → (p b).val < (p a).val → (p a).val = (p b).val + 1) → Monotone fun i : Fin n => i.val + (p i).val`. Introduce `p hp`. Consider the cases of `n with`.

Consider the case `zero => intro a`. Conclude with `a.elim0`. Consider the case `succ m`. Use `Fin.monotone_iff_le_succ.2 fun i => ?_` and prove the remaining obligations. Use `hp i.castSucc i.succ (by simp)` as an intermediate fact.

Simplify using `only [Fin.val_succ, Fin.val_castSucc] at this ⊢`. Use linear arithmetic over natural numbers and integers. Establish `m1` using `mono f (fun a b hab hlt => by`. Establish `ha` using `(w a).2`. Establish `hb` using `(w b).2`.

Simplify using `only [hf, Fin.val_rev] at hlt ⊢`. Use `(h a b (by show a.val < b.val; omega) (by show (w a).val < (w b).val; omega)).1.2 hab` as an intermediate fact. Use the proof step `omega)`. Establish `m2` using `mono f.symm (fun a b hab hlt => by`. Establish `ea : (w (f.symm a)).rev = a` using `by rw [← hf]; simp`.

Establish `eb : (w (f.symm b)).rev = b` using `by rw [← hf]; simp`. Establish `ea'` using `congrArg Fin.val ea`. Establish `eb'` using `congrArg Fin.val eb`. Establish `ha` using `(w (f.symm a)).2`. Establish `hb` using `(w (f.symm b)).2`.

Simplify using `only [Fin.val_rev] at ea' eb'`. Conclude with `(h (f.symm b) (f.symm a) hlt (by show (w (f.symm b)).val < (w (f.symm a)).val; omega)).1.1 (by omega))`. Establish `e1 : (fun i : Fin n => i.val + (f.symm i).val) ∘ f = fun i : Fin n => i.val + (f i).val`. Use function extensionality and compare the values at `i`. Simplify using `[add_comm]`.

Establish `e2` using `Tuple.unique_monotone (f := fun i : Fin n => i.val + (f.symm i).val) (σ := f) (τ := 1) (by rw [e1]; exact m1) (by simpa using m2)`. Rewrite `e2` using `[e1]`. Establish `e3 : ∀ i, f i = f.symm i` using `fun i => by`. Use `congrFun e2 i` as an intermediate fact. Simplify using `at this`.

Conclude with `Fin.ext this`. Establish `e4 : ∀ i, f (f i) = i` using `fun i => by rw [e3 (f i)]; simp`. Establish `ht : ∀ k : ℕ, ∀ a b : Fin n, b.val = a.val + k → a.val + (f a).val = b.val + (f b).val → t a = t b`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro a b hab _; rw [show a = b from Fin.ext (by omega)]`. Consider the case `succ k ih`. Introduce `a b hab hs`. Set `a' : Fin n` to `⟨a.val + 1, by have := b.2; omega⟩`. Establish `ha' : a'.val = a.val + 1` using `rfl`.

Establish `l1 : a.val + (f a).val ≤ a'.val + (f a').val` using `m1 (show a.val ≤ a'.val by omega)`. Establish `l2 : a'.val + (f a').val ≤ b.val + (f b).val` using `m1 (show a'.val ≤ b.val by omega)`. Rewrite using `[← ih a' b (by omega) (by omega)]`. Establish `hlt : (f a').val < (f a).val` using `by omega`. Establish `h1` using `(w a).2`.

Establish `h2` using `(w a').2`. Simplify using `only [hf, Fin.val_rev] at hlt`. Conclude with `(h a a' (by show a.val < a'.val; omega) (by show (w a).val < (w a').val; omega)).2 ha'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `e4 c` as an intermediate fact.

Rewrite `this` using `[hf, hf]`. Conclude with `Fin.rev_eq_iff.1 this`. Rewrite using `[← hf]`. Break down `le_total c.val (f c).val with hc | hc` into its components or cases. Conclude with `(ht ((f c).val - c.val) c (f c) (by omega) (by rw [e4]; omega)).symm`.

Conclude with `ht (c.val - (f c).val) (f c) c (by omega) (by rw [e4]; omega)`.
-/
theorem perm_fixed {n : ℕ} {T : Type} (w : Equiv.Perm (Fin n)) (t : Fin n → T)
    (h : ∀ a b : Fin n, a < b → w a < w b →
      ((w b).val = (w a).val + 1 ↔ b.val = a.val + 1) ∧ (b.val = a.val + 1 → t a = t b)) (c : Fin n) :
    w (w c).rev = c.rev ∧ t (w c).rev = t c := by
  let f : Equiv.Perm (Fin n) := w.trans Fin.revPerm
  have hf : ∀ i, f i = (w i).rev := fun _ => rfl
  have mono : ∀ p : Equiv.Perm (Fin n),
      (∀ a b : Fin n, b.val = a.val + 1 → (p b).val < (p a).val → (p a).val = (p b).val + 1) →
      Monotone fun i : Fin n => i.val + (p i).val := by
    intro p hp
    cases n with
    | zero => intro a; exact a.elim0
    | succ m =>
      refine Fin.monotone_iff_le_succ.2 fun i => ?_
      have := hp i.castSucc i.succ (by simp)
      simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega
  have m1 := mono f (fun a b hab hlt => by
    have ha := (w a).2
    have hb := (w b).2
    simp only [hf, Fin.val_rev] at hlt ⊢
    have := (h a b (by show a.val < b.val; omega) (by show (w a).val < (w b).val; omega)).1.2 hab
    omega)
  have m2 := mono f.symm (fun a b hab hlt => by
    have ea : (w (f.symm a)).rev = a := by rw [← hf]; simp
    have eb : (w (f.symm b)).rev = b := by rw [← hf]; simp
    have ea' := congrArg Fin.val ea
    have eb' := congrArg Fin.val eb
    have ha := (w (f.symm a)).2
    have hb := (w (f.symm b)).2
    simp only [Fin.val_rev] at ea' eb'
    exact (h (f.symm b) (f.symm a) hlt (by show (w (f.symm b)).val < (w (f.symm a)).val; omega)).1.1 (by omega))
  have e1 : (fun i : Fin n => i.val + (f.symm i).val) ∘ f = fun i : Fin n => i.val + (f i).val := by
    funext i; simp [add_comm]
  have e2 := Tuple.unique_monotone (f := fun i : Fin n => i.val + (f.symm i).val) (σ := f) (τ := 1)
    (by rw [e1]; exact m1) (by simpa using m2)
  rw [e1] at e2
  have e3 : ∀ i, f i = f.symm i := fun i => by
    have := congrFun e2 i
    simp at this
    exact Fin.ext this
  have e4 : ∀ i, f (f i) = i := fun i => by rw [e3 (f i)]; simp
  have ht : ∀ k : ℕ, ∀ a b : Fin n, b.val = a.val + k → a.val + (f a).val = b.val + (f b).val → t a = t b := by
    intro k
    induction k with
    | zero => intro a b hab _; rw [show a = b from Fin.ext (by omega)]
    | succ k ih =>
      intro a b hab hs
      let a' : Fin n := ⟨a.val + 1, by have := b.2; omega⟩
      have ha' : a'.val = a.val + 1 := rfl
      have l1 : a.val + (f a).val ≤ a'.val + (f a').val := m1 (show a.val ≤ a'.val by omega)
      have l2 : a'.val + (f a').val ≤ b.val + (f b).val := m1 (show a'.val ≤ b.val by omega)
      rw [← ih a' b (by omega) (by omega)]
      have hlt : (f a').val < (f a).val := by omega
      have h1 := (w a).2
      have h2 := (w a').2
      simp only [hf, Fin.val_rev] at hlt
      exact (h a a' (by show a.val < a'.val; omega) (by show (w a).val < (w a').val; omega)).2 ha'
  refine ⟨?_, ?_⟩
  · have := e4 c
    rw [hf, hf] at this
    exact Fin.rev_eq_iff.1 this
  · rw [← hf]
    rcases le_total c.val (f c).val with hc | hc
    · exact (ht ((f c).val - c.val) c (f c) (by omega) (by rw [e4]; omega)).symm
    · exact ht (c.val - (f c).val) (f c) c (by omega) (by rw [e4]; omega)

end Comb

section Concrete

variable {F : Type} [Field F] {r : ℕ}

def refl (M : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F := M.transpose.submatrix Fin.revPerm Fin.revPerm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem refl_apply (M : Matrix (Fin r) (Fin r) F) (a b : Fin r) : refl M a b = M b.rev a.rev := rfl

/- English proof (translation)
Unfold `refl`. Rewrite using `[Matrix.transpose_mul, Matrix.submatrix_mul_equiv]`.
-/
theorem refl_mul (M N : Matrix (Fin r) (Fin r) F) : refl (M * N) = refl N * refl M := by
  unfold refl
  rw [Matrix.transpose_mul, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Unfold `refl`. Rewrite using `[Matrix.transpose_one, Matrix.submatrix_one_equiv]`.
-/
theorem refl_one : refl (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  unfold refl
  rw [Matrix.transpose_one, Matrix.submatrix_one_equiv]

def sg (g : GL (Fin r) F) : GL (Fin r) F :=
  ⟨refl g.val, refl g.inv, by rw [← refl_mul, g.inv_val, refl_one], by rw [← refl_mul, g.val_inv, refl_one]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sg_apply (g : GL (Fin r) F) (a b : Fin r) :
    (sg g : Matrix (Fin r) (Fin r) F) a b = (g : Matrix (Fin r) (Fin r) F) b.rev a.rev := rfl

/- English proof (translation)
The claim follows from `Units.ext (refl_mul _ _)`.
-/
theorem sg_mul (x y : GL (Fin r) F) : sg (x * y) = sg y * sg x := Units.ext (refl_mul _ _)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[sg_apply]`.
-/
theorem sg_sg (x : GL (Fin r) F) : sg (sg x) = x := by
  ext a b
  simp [sg_apply]

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[sg_apply]`. Conclude with `unip_lower hu (Fin.rev_lt_rev.2 hij)`. Rewrite using `[sg_apply]`. Conclude with `unip_diag hu _`.
-/
theorem sg_mem {u : GL (Fin r) F} (hu : u ∈ unip F r) : sg u ∈ unip F r := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [sg_apply]
    exact unip_lower hu (Fin.rev_lt_rev.2 hij)
  · rw [sg_apply]
    exact unip_diag hu _

/- English proof (translation)
Unfold `edgeSum`. Rewrite using `[Finset.sum_comm]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun i => Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_` and prove the remaining obligations. Rewrite using `[sg_apply]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations.

Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [supEdge, Fin.revPerm_apply, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem edgeSum_sg (u : GL (Fin r) F) : edgeSum supEdge (sg u) = edgeSum supEdge u := by
  unfold edgeSum
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  rw [sg_apply]
  refine if_congr ?_ rfl rfl
  have := i.2
  have := j.2
  simp only [supEdge, Fin.revPerm_apply, Fin.val_rev]
  omega

def tv (i j : Fin r) (h : i ≠ j) (x : F) : GL (Fin r) F :=
  ⟨Matrix.transvection i j x, Matrix.transvection i j (-x),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tv_val (i j : Fin r) (h : i ≠ j) (x : F) :
    (tv i j h x : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single i j x := rfl

/- English proof (translation)
Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `hab' : b < a` using `hab`. Rewrite using `[tv_val, Matrix.add_apply, Matrix.one_apply_ne hab'.ne', Matrix.single_apply_of_ne, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_asymm h hab'`.

Rewrite using `[tv_val, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_irrefl _ h`.
-/
theorem tv_mem (i j : Fin r) (h : i < j) (x : F) : tv i j h.ne x ∈ unip F r := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : b < a := hab
    rw [tv_val, Matrix.add_apply, Matrix.one_apply_ne hab'.ne', Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h hab'
  · rw [tv_val, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ h

/- English proof (translation)
Unfold `edgeSum`. Establish `key : ∀ a b : Fin r, (if supEdge a b then (tv i j h x : Matrix (Fin r) (Fin r) F) a b else 0) = if b = j then (if a = i then (if j.val = i.val + 1 then x else 0) else 0) else 0`. Introduce `a b`. Distinguish the cases in `hs : supEdge a b`. Establish `hab : a ≠ b` using `by rintro rfl; simp [supEdge] at hs`.

Rewrite using `[if_pos hs, tv_val, Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply]`. Distinguish the cases in `h1 : b = j`. Distinguish the cases in `h2 : a = i`. Substitute `h1 h2` using the available equality. Establish `hs' : b.val = a.val + 1` using `hs`.

Simplify using `[hs']`. Simplify using `[h1, h2, Ne.symm h2]`. Simplify using `[h1, Ne.symm h1]`. Rewrite using `[if_neg hs] split_ifs with h1 h2 h3`. Substitute `h1 h2` using the available equality.

Conclude with `absurd h3 hs`. Apply the tactic sequence `all_goals rfl`. Simplify using `[key]`.
-/
theorem edgeSum_tv (i j : Fin r) (h : i ≠ j) (x : F) :
    edgeSum supEdge (tv i j h x) = if j.val = i.val + 1 then x else 0 := by
  unfold edgeSum
  have key : ∀ a b : Fin r, (if supEdge a b then (tv i j h x : Matrix (Fin r) (Fin r) F) a b else 0) =
      if b = j then (if a = i then (if j.val = i.val + 1 then x else 0) else 0) else 0 := by
    intro a b
    by_cases hs : supEdge a b
    · have hab : a ≠ b := by rintro rfl; simp [supEdge] at hs
      rw [if_pos hs, tv_val, Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply]
      by_cases h1 : b = j
      · by_cases h2 : a = i
        · subst h1 h2
          have hs' : b.val = a.val + 1 := hs
          simp [hs']
        · simp [h1, h2, Ne.symm h2]
      · simp [h1, Ne.symm h1]
    · rw [if_neg hs]
      split_ifs with h1 h2 h3
      · subst h1 h2; exact absurd h3 hs
      all_goals rfl
  simp [key]

/- English proof (translation)
Establish `hker : ∀ c : F, (∀ z : F, ψ (z * c) = 1) → c = 0`. Introduce `c hc`. Assume the negation of the conclusion as `h0`. Apply `hψ` to reduce the goal to its premises. Use extensionality with `y`.

Use `hc (y / c)` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ h0]`. Simplify using `using this`. Establish `key` using `perm_fixed w t (fun a b hab hw => by`. Establish `h : ∀ z : F, ψ (if (w b).val = (w a).val + 1 then z * t a else 0) = ψ (if b.val = a.val + 1 then z * t b else 0)`.

Introduce `z`. Rewrite using `[← edgeSum_tv (w a) (w b) hw.ne, ← edgeSum_tv a b hab.ne]`. Use `hg _ (tv_mem _ _ hw _) _ (tv_mem _ _ hab _) (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, tv_val, tv_val, add_mul, mul_add, one_mul, mul_one, hn]`. Use `congr 1`.

Use extensionality with `i j`. Distinguish the cases in `hi : i = w a`. Distinguish the cases in `hj : j = b`. Substitute `hi hj` using the available equality. Simplify using `only [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same, Matrix.of_apply, if_true]`.

Expand and normalize the polynomial expressions, which then agree. Substitute `hi` using the available equality. Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hj, Matrix.single_mul_apply_same]`. Simplify using `[Ne.symm hj]`. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]`.

Distinguish the cases in `hj : j = b`. Substitute `hj` using the available equality. Rewrite using `[Matrix.mul_single_apply_same]`. Simplify using `[hi]`. Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]`.

Distinguish the cases in `h1 : (w b).val = (w a).val + 1`. Distinguish the cases in `h2 : b.val = a.val + 1`. Use `⟨iff_of_true h1 h2, fun _ => Units.ext (sub_eq_zero.1 (hker _ fun z => ?_))⟩` and prove the remaining obligations. Use `h z` as an intermediate fact. Rewrite `this` using `[if_pos h1, if_pos h2]`.

Rewrite using `[mul_sub, AddChar.map_sub_eq_div, this, div_self]`. Conclude with `(ψ.val_isUnit _).ne_zero`. Conclude with `absurd (hker (t a) fun z => by simpa [h1, h2] using h z) (t a).ne_zero`. Distinguish the cases in `h2 : b.val = a.val + 1`. Conclude with `absurd (hker (t b) fun z => by simpa [h1, h2] using (h z).symm) (t b).ne_zero`.

Conclude with `⟨iff_of_false h1 h2, fun h => absurd h h2⟩)`. Use extensionality with `a c`. Rewrite using `[sg_apply, hn, Matrix.of_apply, Matrix.of_apply]`. Distinguish the cases in `hac : a = w c`. Substitute `hac` using the available equality.

Rewrite using `[if_pos (key c).1.symm, if_pos rfl, (key c).2]`. Rewrite using `[if_neg hac, if_neg]`. Introduce `h`. Apply `hac` to reduce the goal to its premises. Use `(key a.rev).1` as an intermediate fact.

Rewrite `this` using `[← h, Fin.rev_rev, Fin.rev_rev]`. Conclude with `this.symm`.
-/
theorem sg_monomial (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (n : GL (Fin r) F) (w : Equiv.Perm (Fin r)) (t : Fin r → Fˣ)
    (hn : (n : Matrix (Fin r) (Fin r) F) = Matrix.of fun a c => if a = w c then (t c : F) else 0)
    (hg : ∀ a ∈ unip F r, ∀ b ∈ unip F r, a * n = n * b → ψ (edgeSum supEdge a) = ψ (edgeSum supEdge b)) :
    sg n = n := by
  have hker : ∀ c : F, (∀ z : F, ψ (z * c) = 1) → c = 0 := by
    intro c hc
    by_contra h0
    apply hψ
    ext y
    have := hc (y / c)
    rw [div_mul_cancel₀ _ h0] at this
    simpa using this
  have key := perm_fixed w t (fun a b hab hw => by
    have h : ∀ z : F, ψ (if (w b).val = (w a).val + 1 then z * t a else 0) =
        ψ (if b.val = a.val + 1 then z * t b else 0) := by
      intro z
      rw [← edgeSum_tv (w a) (w b) hw.ne, ← edgeSum_tv a b hab.ne]
      refine hg _ (tv_mem _ _ hw _) _ (tv_mem _ _ hab _) (Units.ext ?_)
      rw [Units.val_mul, Units.val_mul, tv_val, tv_val, add_mul, mul_add, one_mul, mul_one, hn]
      congr 1
      ext i j
      by_cases hi : i = w a
      · by_cases hj : j = b
        · subst hi hj
          simp only [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same, Matrix.of_apply, if_true]
          ring
        · subst hi
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj, Matrix.single_mul_apply_same]
          simp [Ne.symm hj]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]
        by_cases hj : j = b
        · subst hj
          rw [Matrix.mul_single_apply_same]
          simp [hi]
        · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]
    by_cases h1 : (w b).val = (w a).val + 1
    · by_cases h2 : b.val = a.val + 1
      · refine ⟨iff_of_true h1 h2, fun _ => Units.ext (sub_eq_zero.1 (hker _ fun z => ?_))⟩
        have := h z
        rw [if_pos h1, if_pos h2] at this
        rw [mul_sub, AddChar.map_sub_eq_div, this, div_self]
        exact (ψ.val_isUnit _).ne_zero
      · exact absurd (hker (t a) fun z => by simpa [h1, h2] using h z) (t a).ne_zero
    · by_cases h2 : b.val = a.val + 1
      · exact absurd (hker (t b) fun z => by simpa [h1, h2] using (h z).symm) (t b).ne_zero
      · exact ⟨iff_of_false h1 h2, fun h => absurd h h2⟩)
  ext a c
  rw [sg_apply, hn, Matrix.of_apply, Matrix.of_apply]
  by_cases hac : a = w c
  · subst hac
    rw [if_pos (key c).1.symm, if_pos rfl, (key c).2]
  · rw [if_neg hac, if_neg]
    intro h
    apply hac
    have := (key a.rev).1
    rw [← h, Fin.rev_rev, Fin.rev_rev] at this
    exact this.symm

end Concrete

/- English proof (translation)
Use `haveI : Fintype (unip F r) := Fintype.ofFinite _`. Use `gelfand τ (unip F r) (fun g => ψ (edgeSum supEdge g)) hτ ?_ ?_ sg sg_mul sg_sg (fun u hu => sg_mem hu) (fun u _ => by rw [edgeSum_sg]) ?_` and prove the remaining obligations. Establish `: edgeSum supEdge (1 : GL (Fin r) F) = 0` using `congrArg Multiplicative.toAdd (supHom F r).map_one`. Rewrite using `[this, AddChar.map_zero_eq_one]`. Introduce `u hu u' hu'`.

Establish `: edgeSum supEdge (u * u') = edgeSum supEdge u + edgeSum supEdge u'` using `congrArg Multiplicative.toAdd ((supHom F r).map_mul ⟨u, hu⟩ ⟨u', hu'⟩)`. Rewrite using `[this, AddChar.map_add_eq_mul]`. Introduce `g`. Take `⟨m, ⟨u, hu, u', hu', e⟩, -⟩` from `GlobalTheory.FinGL.Bruhat.bruhat F r g`. Use `⟨u, hu, u', hu', u⁻¹ * g * u'⁻¹, by group, sg_monomial ψ hψ _ m.1 m.2 ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul, e]`. Simplify using `only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left]`.
-/
theorem whDim_le_one (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V)
    (hτ : τ.IsIrreducible) : whDim ψ τ ≤ 1 := by
  classical
  haveI : Fintype (unip F r) := Fintype.ofFinite _
  refine gelfand τ (unip F r) (fun g => ψ (edgeSum supEdge g)) hτ ?_ ?_ sg sg_mul sg_sg (fun u hu => sg_mem hu)
    (fun u _ => by rw [edgeSum_sg]) ?_
  · have : edgeSum supEdge (1 : GL (Fin r) F) = 0 := congrArg Multiplicative.toAdd (supHom F r).map_one
    rw [this, AddChar.map_zero_eq_one]
  · intro u hu u' hu'
    have : edgeSum supEdge (u * u') = edgeSum supEdge u + edgeSum supEdge u' :=
      congrArg Multiplicative.toAdd ((supHom F r).map_mul ⟨u, hu⟩ ⟨u', hu'⟩)
    rw [this, AddChar.map_add_eq_mul]
  · intro g
    obtain ⟨m, ⟨u, hu, u', hu', e⟩, -⟩ := GlobalTheory.FinGL.Bruhat.bruhat F r g
    refine ⟨u, hu, u', hu', u⁻¹ * g * u'⁻¹, by group, sg_monomial ψ hψ _ m.1 m.2 ?_⟩
    rw [Units.val_mul, Units.val_mul, e]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left]

end GlobalTheory.FinGL.GGFree
