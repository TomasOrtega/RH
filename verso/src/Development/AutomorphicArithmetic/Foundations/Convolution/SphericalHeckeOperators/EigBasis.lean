import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private def eigCone (n : ℕ) : AddSubmonoid (Fin n → ℤ) where
  carrier := {a | Antitone a}
  add_mem' ha hb := Antitone.add ha hb
  zero_mem' := fun _ _ _ => le_rfl

private noncomputable def eigChar {n : ℕ} (w : Fin n → ℂˣ) : Multiplicative (eigCone n) →* ℂ where
  toFun a := monomialChar (a.toAdd : Fin n → ℤ) w
  map_one' := by simp [monomialChar_zero]
  map_mul' a b := by simp [monomialChar_add]

/- English proof (translation)
Establish `h` using `monomialChar_add a (-a) w`. Rewrite `h` using `[add_neg_cancel, monomialChar_zero]`. Introduce `h0`. Rewrite `h` using `[h0, zero_mul]`. Conclude with `one_ne_zero h`.
-/
private lemma eig_mc_ne {n : ℕ} (a : Fin n → ℤ) (w : Fin n → ℂˣ) : monomialChar a w ≠ 0 := by
  have h := monomialChar_add a (-a) w
  rw [add_neg_cancel, monomialChar_zero] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∏ j, (((w j) ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) j) : ℂˣ) : ℂ) = w i`. Rewrite using `[Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`.

Simplify using the standard rewrite rules.
-/
private lemma eig_mc_single {n : ℕ} (i : Fin n) (w : Fin n → ℂˣ) :
    monomialChar (Pi.single i 1) w = w i := by
  change ∏ j, (((w j) ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) j) : ℂˣ) : ℂ) = w i
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/- English proof (translation)
Introduce `w w' h`. Establish `H : ∀ a, Antitone a → monomialChar a w = monomialChar a w'` using `fun a ha => DFunLike.congr_fun h (Multiplicative.ofAdd ⟨a, ha⟩)`. Use function extensionality and compare the values at `i`. Set `p : Fin n → ℤ` to `fun j => if j < i then 1 else 0`. Establish `hp : Antitone p`.

Introduce `j k hjk`. Simplify using `only [p]`. Use `split_ifs with h1 h2`. Conclude with `le_rfl`. Conclude with `absurd (lt_of_le_of_lt hjk h1) h2`.

Conclude with `zero_le_one`. Conclude with `le_rfl`. Establish `hq : Antitone (Pi.single i 1 + p)`. Introduce `j k hjk`. Simplify using `only [p, Pi.add_apply, Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `h1` using `H _ hq`. Rewrite `h1` using `[monomialChar_add, monomialChar_add, H p hp, eig_mc_single, eig_mc_single]`. Conclude with `Units.ext (mul_right_cancel₀ (eig_mc_ne _ _) h1)`.
-/
private lemma eigChar_inj {n : ℕ} : Function.Injective (eigChar (n := n)) := by
  intro w w' h
  have H : ∀ a, Antitone a → monomialChar a w = monomialChar a w' := fun a ha =>
    DFunLike.congr_fun h (Multiplicative.ofAdd ⟨a, ha⟩)
  funext i
  let p : Fin n → ℤ := fun j => if j < i then 1 else 0
  have hp : Antitone p := by
    intro j k hjk
    simp only [p]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (lt_of_le_of_lt hjk h1) h2
    · exact zero_le_one
    · exact le_rfl
  have hq : Antitone (Pi.single i 1 + p) := by
    intro j k hjk
    simp only [p, Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  have h1 := H _ hq
  rw [monomialChar_add, monomialChar_add, H p hp, eig_mc_single, eig_mc_single] at h1
  exact Units.ext (mul_right_cancel₀ (eig_mc_ne _ _) h1)

/- English proof (translation)
Introduce `n V _ _ _ hdim θ h0 hadd u ℓ z c hz hc hu`. Set `χ : Equiv.Perm (Fin n) → Multiplicative (eigCone n) → ℂ` to `fun σ => eigChar (z ∘ σ)`. Establish `hχ : ∀ σ a, χ σ a = monomialChar (a.toAdd : Fin n → ℤ) (z ∘ σ)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective (fun σ : Equiv.Perm (Fin n) => eigChar (z ∘ σ))`. Introduce `σ τ h`.

Use `eigChar_inj h` as an intermediate fact. Conclude with `Equiv.ext fun i => hz (congrFun this i)`. Establish `hli : LinearIndependent ℂ χ` using `(linearIndependent_monoidHom (Multiplicative (eigCone n)) ℂ).comp _ hinj`. Set `Φ : V →ₗ[ℂ] (Multiplicative (eigCone n) → ℂ)` to `LinearMap.pi fun a => ℓ ∘ₗ θ (a.toAdd : Fin n → ℤ)`. Establish `hΦ : ∀ x a, Φ x a = ℓ (θ (a.toAdd : Fin n → ℤ) x)` using `fun _ _ => rfl`.

Set `L : (Equiv.Perm (Fin n) → ℂ) →ₗ[ℂ] (Multiplicative (eigCone n) → ℂ)` to `Fintype.linearCombination ℂ (fun σ => c σ • χ σ)`. Establish `hL : ∀ w a, L w a = ∑ σ, w σ * (c σ * χ σ a)`. Introduce `w a`. Simplify using `[L, Fintype.linearCombination_apply, Finset.sum_apply]`. Establish `hspan` using `span_flip_eq_top_iff_linearIndependent.2 hli`.

Establish `hle : Submodule.span ℂ (Set.range (flip χ)) ≤ (LinearMap.range Φ).comap L`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Use `⟨θ (b.toAdd : Fin n → ℤ) u, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Rewrite using `[hΦ, hL, ← Module.End.mul_apply, ← hadd _ _ a.toAdd.2 b.toAdd.2, hu (_ + _) (a.toAdd + b.toAdd).2]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[monomialChar_add]`. Simplify using `only [flip, hχ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hex : ∀ σ, ∃ x, Φ x = χ σ`. Introduce `σ`. Establish `h1 : (Pi.single σ (c σ)⁻¹ : Equiv.Perm (Fin n) → ℂ) ∈ (LinearMap.range Φ).comap L` using `hle (hspan ▸ Submodule.mem_top)`. Take `⟨x, hx⟩` from `h1`. Use `⟨x, hx.trans ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Rewrite using `[hL, Finset.sum_eq_single σ]`. Rewrite using `[Pi.single_eq_same, ← mul_assoc, inv_mul_cancel₀ (hc σ), one_mul]`. Introduce `τ _ hτ`. Simplify using `[Pi.single_eq_of_ne hτ]`.

Simplify using the standard rewrite rules. Use `choose v hv using hex`. Establish `hlc : LinearIndependent ℂ (Φ ∘ v)`. Establish `: Φ ∘ v = χ` using `funext hv`. Rewrite using `[this]`.

Conclude with `hli`. Establish `hlv : LinearIndependent ℂ v` using `LinearIndependent.of_comp Φ hlc`. Establish `hcard : Fintype.card (Equiv.Perm (Fin n)) = Module.finrank ℂ V`. Use `le_antisymm hlv.fintype_card_le_finrank ?_` and prove the remaining obligations. Rewrite using `[Fintype.card_perm, Fintype.card_fin]`.

Conclude with `hdim`. Set `B` to `basisOfLinearIndependentOfCardEqFinrank hlv hcard`. Establish `hB : ∀ σ, B σ = v σ` using `fun σ => by`. Simplify using `[B, coe_basisOfLinearIndependentOfCardEqFinrank]`. Establish `hΦinj : Function.Injective Φ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Rewrite `hx`, the goal using `[← B.sum_repr x]`. Simplify using `only [map_sum, map_smul, hB] at hx`. Use `Fintype.linearIndependent_iff.1 hlc (fun σ => B.repr x σ) hx` as an intermediate fact.

Simplify using `[this]`. Use `⟨B, fun σ a ha => ?_, fun σ => ?_, ?_⟩` and prove the remaining obligations. Apply `hΦinj` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Rewrite using `[hB, map_smul, hv, hΦ, ← Module.End.mul_apply, ← hadd _ _ b.toAdd.2 ha]`.

Use `congrFun (hv σ) (Multiplicative.ofAdd ⟨_, Antitone.add b.toAdd.2 ha⟩)` as an intermediate fact. Rewrite `this` using `[hΦ, hχ]`. Use `this.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `monomialChar (_ + a) _ = _`. Rewrite using `[monomialChar_add, Pi.smul_apply, hχ, smul_eq_mul, mul_comm]`.

Use `congrFun (hv σ) 1` as an intermediate fact. Rewrite `this` using `[hΦ, hχ]`. Simplify `this` using `[h0, monomialChar_zero, hB]`. Apply `hΦinj` to reduce the goal to its premises. Use function extensionality and compare the values at `a`.

Rewrite using `[hΦ, hu _ a.toAdd.2]`. Simplify using `only [map_sum, map_smul, hB, hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hχ]`.
-/
theorem UpperTheory.ConvolutionTheory.H.eigBasis :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V], Module.finrank ℂ V ≤ n.factorial →
      ∀ θ : (Fin n → ℤ) → Module.End ℂ V, θ 0 = 1 → (∀ a b, Antitone a → Antitone b → θ (a + b) = θ a * θ b) →
      ∀ (u : V) (ℓ : Module.Dual ℂ V) (z : Fin n → ℂˣ) (c : Equiv.Perm (Fin n) → ℂ), Function.Injective z → (∀ σ, c σ ≠ 0) →
      (∀ a, Antitone a → ℓ (θ a u) = ∑ σ, c σ * monomialChar a (z ∘ σ)) →
      ∃ v : Module.Basis (Equiv.Perm (Fin n)) ℂ V, (∀ σ a, Antitone a → θ a (v σ) = monomialChar a (z ∘ σ) • v σ) ∧ (∀ σ, ℓ (v σ) = 1) ∧
        u = ∑ σ, c σ • v σ := by
  intro n V _ _ _ hdim θ h0 hadd u ℓ z c hz hc hu
  classical
  let χ : Equiv.Perm (Fin n) → Multiplicative (eigCone n) → ℂ := fun σ => eigChar (z ∘ σ)
  have hχ : ∀ σ a, χ σ a = monomialChar (a.toAdd : Fin n → ℤ) (z ∘ σ) := fun _ _ => rfl
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin n) => eigChar (z ∘ σ)) := by
    intro σ τ h
    have := eigChar_inj h
    exact Equiv.ext fun i => hz (congrFun this i)
  have hli : LinearIndependent ℂ χ :=
    (linearIndependent_monoidHom (Multiplicative (eigCone n)) ℂ).comp _ hinj
  let Φ : V →ₗ[ℂ] (Multiplicative (eigCone n) → ℂ) :=
    LinearMap.pi fun a => ℓ ∘ₗ θ (a.toAdd : Fin n → ℤ)
  have hΦ : ∀ x a, Φ x a = ℓ (θ (a.toAdd : Fin n → ℤ) x) := fun _ _ => rfl
  let L : (Equiv.Perm (Fin n) → ℂ) →ₗ[ℂ] (Multiplicative (eigCone n) → ℂ) :=
    Fintype.linearCombination ℂ (fun σ => c σ • χ σ)
  have hL : ∀ w a, L w a = ∑ σ, w σ * (c σ * χ σ a) := by
    intro w a
    simp [L, Fintype.linearCombination_apply, Finset.sum_apply]
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  have hle : Submodule.span ℂ (Set.range (flip χ)) ≤ (LinearMap.range Φ).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    refine ⟨θ (b.toAdd : Fin n → ℤ) u, ?_⟩
    funext a
    rw [hΦ, hL, ← Module.End.mul_apply, ← hadd _ _ a.toAdd.2 b.toAdd.2,
      hu (_ + _) (a.toAdd + b.toAdd).2]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [monomialChar_add]
    simp only [flip, hχ]
    ring
  have hex : ∀ σ, ∃ x, Φ x = χ σ := by
    intro σ
    have h1 : (Pi.single σ (c σ)⁻¹ : Equiv.Perm (Fin n) → ℂ) ∈ (LinearMap.range Φ).comap L :=
      hle (hspan ▸ Submodule.mem_top)
    obtain ⟨x, hx⟩ := h1
    refine ⟨x, hx.trans ?_⟩
    funext a
    rw [hL, Finset.sum_eq_single σ]
    · rw [Pi.single_eq_same, ← mul_assoc, inv_mul_cancel₀ (hc σ), one_mul]
    · intro τ _ hτ
      simp [Pi.single_eq_of_ne hτ]
    · simp
  choose v hv using hex
  have hlc : LinearIndependent ℂ (Φ ∘ v) := by
    have : Φ ∘ v = χ := funext hv
    rw [this]; exact hli
  have hlv : LinearIndependent ℂ v := LinearIndependent.of_comp Φ hlc
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Module.finrank ℂ V := by
    refine le_antisymm hlv.fintype_card_le_finrank ?_
    rw [Fintype.card_perm, Fintype.card_fin]
    exact hdim
  let B := basisOfLinearIndependentOfCardEqFinrank hlv hcard
  have hB : ∀ σ, B σ = v σ := fun σ => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← B.sum_repr x] at hx ⊢
    simp only [map_sum, map_smul, hB] at hx
    have := Fintype.linearIndependent_iff.1 hlc (fun σ => B.repr x σ) hx
    simp [this]
  refine ⟨B, fun σ a ha => ?_, fun σ => ?_, ?_⟩
  · apply hΦinj
    funext b
    rw [hB, map_smul, hv, hΦ, ← Module.End.mul_apply, ← hadd _ _ b.toAdd.2 ha]
    have := congrFun (hv σ) (Multiplicative.ofAdd ⟨_, Antitone.add b.toAdd.2 ha⟩)
    rw [hΦ, hχ] at this
    refine this.trans ?_
    change monomialChar (_ + a) _ = _
    rw [monomialChar_add, Pi.smul_apply, hχ, smul_eq_mul, mul_comm]
  · have := congrFun (hv σ) 1
    rw [hΦ, hχ] at this
    simpa [h0, monomialChar_zero, hB] using this
  · apply hΦinj
    funext a
    rw [hΦ, hu _ a.toAdd.2]
    simp only [map_sum, map_smul, hB, hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hχ]
