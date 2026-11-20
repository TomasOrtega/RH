import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

/- English proof (translation)
Introduce `_` and use `IsLocallyConstant.const _`.
-/
private theorem ac_const {D R : Type} [TopologicalSpace D] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : D => c := fun _ => IsLocallyConstant.const _

/- English proof (translation)
Introduce `N` and use `by have h := (hf N).add (hg N) convert h using 1 funext s simp`.
-/
private theorem ac_add {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := fun N => by
  have h := (hf N).add (hg N)
  convert h using 1
  funext s
  simp

/- English proof (translation)
Introduce `N` and use `by have h := (hf N).mul (hg N) convert h using 1 funext s simp`.
-/
private theorem ac_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  have h := (hf N).mul (hg N)
  convert h using 1
  funext s
  simp

/- English proof (translation)
Introduce `N` and use `(hf N).comp_continuous hφ`.
-/
private theorem ac_comp {D E R : Type} [TopologicalSpace D] [TopologicalSpace E] [CommRing R] {I : Ideal R}
    {f : E → R} (hf : AdicCont I f) {φ : D → E} (hφ : Continuous φ) : AdicCont I fun s => f (φ s) :=
  fun N => (hf N).comp_continuous hφ

/- English proof (translation)
Simplify using `only [Fin.sum_univ_three]`. Conclude with `ac_add (ac_add (hf 0) (hf 1)) (hf 2)`.
-/
private theorem adic_continuous_sum_three {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f : Fin 3 → D → R}
    (hf : ∀ a, AdicCont I (f a)) : AdicCont I fun s => ∑ a, f a s := by
  simp only [Fin.sum_univ_three]
  exact ac_add (ac_add (hf 0) (hf 1)) (hf 2)

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem triOf_val {C : Type} [CommRing C] {κ : Type} [Field κ] {F : Frame l κ} (B : Box F 3 C) (v : F.V)
    (s : F.Gv v) : (triOf B v s : Matrix (Fin 3) (Fin 3) C) =
      (B.g v : Matrix (Fin 3) (Fin 3) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := rfl

/- English proof (translation)
Establish `w0 : w 3 0 = 1` using `by simp [w]`. Establish `w1 : w 3 1 = 0` using `by simp [w]`. Establish `w2 : w 3 2 = -1` using `by simp [w]`. Establish `h1 : x ≠ 1` using `fun e => hx (by simp [e])`. Establish `h2 : x ≠ x⁻¹` using `fun e => hx (by`.

Rewrite using `[pow_two]`. Use `nth_rewrite 2 [e]`. Use the proof step `simp)`. Establish `h3 : x⁻¹ ≠ 1` using `fun e => h1 (by simpa using e)`. Introduce `e`.

Establish `e'` using `Units.ext e`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`.
-/
private theorem pow_w_ne {κ : Type} [Field κ] (x : κˣ) (hx : x ^ 2 ≠ 1) (i j : Fin 3) (h : i ≠ j) :
    ((x ^ w 3 i : κˣ) : κ) ≠ ((x ^ w 3 j : κˣ) : κ) := by
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have h1 : x ≠ 1 := fun e => hx (by simp [e])
  have h2 : x ≠ x⁻¹ := fun e => hx (by
    rw [pow_two]
    nth_rewrite 2 [e]
    simp)
  have h3 : x⁻¹ ≠ 1 := fun e => h1 (by simpa using e)
  intro e
  have e' := Units.ext e
  fin_cases i <;> fin_cases j <;> simp_all

/- English proof (translation)
Take `⟨u, hu, hχ⟩` from `h`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Introduce `k A _ _ hk a hloc hadd hz g hg`. Establish `h1 : a 1 = 0` using `by simpa using hadd 1 1`. Set `χ : D →* Multiplicative A` to `{ toFun := fun s => Multiplicative.ofAdd (a s) map_one' := by rw [h1]; rfl map_mul' := fun s t => by rw [hadd]; rfl }`.

Establish `hp : IsPGroup l (Multiplicative A)` using `fun x => ⟨k, by show Multiplicative.ofAdd (l ^ k • Multiplicative.toAdd x) = 1`. Rewrite using `[hk]`. Use the proof step `rfl⟩`. Establish `ho : IsOpen (χ.ker : Set D)`. Establish `: (χ.ker : Set D) = a ⁻¹' {0}`.

Use extensionality with `s`. Use `show χ s = 1 ↔ a s = 0`. Conclude with `Iff.rfl`. Rewrite using `[this]`. Conclude with `hloc.isOpen_fiber 0`.

Conclude with `hχ (Multiplicative A) hp χ ho (fun j => by show Multiplicative.ofAdd (a (u j)) = 1`. Rewrite using `[hz]`. Use the proof step `rfl) g hg`.
-/
private theorem genI_of {D : Type} [Group D] [TopologicalSpace D] {I : Subgroup D} {d : ℕ}
    (h : ∃ u : Fin d → D, (∀ a, u a ∈ I) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : D →* A,
      IsOpen (χ.ker : Set D) → (∀ a, χ (u a) = 1) → ∀ g ∈ I, χ g = 1) : GenI l I d := by
  obtain ⟨u, hu, hχ⟩ := h
  refine ⟨u, hu, ?_⟩
  intro k A _ _ hk a hloc hadd hz g hg
  have h1 : a 1 = 0 := by simpa using hadd 1 1
  let χ : D →* Multiplicative A :=
    { toFun := fun s => Multiplicative.ofAdd (a s)
      map_one' := by rw [h1]; rfl
      map_mul' := fun s t => by rw [hadd]; rfl }
  have hp : IsPGroup l (Multiplicative A) := fun x => ⟨k, by
    show Multiplicative.ofAdd (l ^ k • Multiplicative.toAdd x) = 1
    rw [hk]
    rfl⟩
  have ho : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = a ⁻¹' {0} := by
      ext s
      show χ s = 1 ↔ a s = 0
      exact Iff.rfl
    rw [this]
    exact hloc.isOpen_fiber 0
  exact hχ (Multiplicative A) hp χ ho (fun j => by
    show Multiplicative.ofAdd (a (u j)) = 1
    rw [hz]
    rfl) g hg

end UpperTheory.V.Z.J

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ F C₀ hF _ ρ B hL hB hC v`. Establish `hd : ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O)`. Introduce `s j`. Rewrite using `[triOf_val]`. Establish `e : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s)` using `hB.res (F.loc0 v s)`.

Rewrite using `[e]`. Conclude with `hB.psi v j s`. Establish `hloc : Continuous (F.loc v)` using `continuous_subtype_val.comp (hF.loc_cont v)`. Use `⟨⟨fun i j => ?_, fun s => ?_, ?_⟩, ?_, hd⟩` and prove the remaining obligations. Establish `e : (fun s => (triOf B v s : Matrix (Fin 3) (Fin 3) O) i j) = fun s => ∑ b, (∑ a, (B.g v : Matrix (Fin 3) (Fin 3) O) i a * (B.r (F.loc v s)).mat a b) * (((B.g v)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) b j`.

Use function extensionality and compare the values at `s`. Rewrite using `[triOf_val, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply]`. Rewrite using `[e]`. Conclude with `adic_continuous_sum_three fun b => ac_mul (adic_continuous_sum_three fun a => ac_mul (ac_const _ _) (ac_comp (hC a b) hloc)) (ac_const _ _)`.

Conclude with `B.tri v s`. Take `⟨s, hs⟩` from `hF.f3 v`. Use `⟨s, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hd, hd]`. Assume the negation of the conclusion as `hn`.

Establish `hm : (ρ.ψ v i s : O) - (ρ.ψ v j s : O) ∈ maximalIdeal O` using `hn`. Establish `h0` using `(res_eq_zero_iff O O _).2 hm`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Establish `hi` using `hL.2.1.2 v i s`. Establish `hj` using `hL.2.1.2 v j s`.

Simplify using `only [NRep.map_ψ, RingHom.id_apply] at hi hj`. Conclude with `pow_w_ne _ hs i j hij (by rw [← hi, ← hj]; exact h0)`. Take `⟨u, a₀, hu, -, hχ⟩` from `hF.gen v`. Conclude with `genI_of ⟨u, fun a => (hu a).1, hχ⟩`.
-/
theorem UpperTheory.V.Z.J.triOk :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ v, TriRep (triOf B v) ∧ GenI l (F.Iv v) (F.dv v) ∧ ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
  intro l _ O _ _ _ _ _ F C₀ hF _ ρ B hL hB hC v
  have hd : ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
    intro s j
    rw [triOf_val]
    have e : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hB.res (F.loc0 v s)
    rw [e]
    exact hB.psi v j s
  have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
  refine ⟨⟨fun i j => ?_, fun s => ?_, ?_⟩, ?_, hd⟩
  · have e : (fun s => (triOf B v s : Matrix (Fin 3) (Fin 3) O) i j) = fun s =>
        ∑ b, (∑ a, (B.g v : Matrix (Fin 3) (Fin 3) O) i a * (B.r (F.loc v s)).mat a b) *
          (((B.g v)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) b j := by
      funext s
      rw [triOf_val, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    rw [e]
    exact adic_continuous_sum_three fun b => ac_mul (adic_continuous_sum_three fun a => ac_mul (ac_const _ _) (ac_comp (hC a b) hloc)) (ac_const _ _)
  · exact B.tri v s
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij => ?_⟩
    rw [hd, hd]
    by_contra hn
    have hm : (ρ.ψ v i s : O) - (ρ.ψ v j s : O) ∈ maximalIdeal O := hn
    have h0 := (res_eq_zero_iff O O _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    have hi := hL.2.1.2 v i s
    have hj := hL.2.1.2 v j s
    simp only [NRep.map_ψ, RingHom.id_apply] at hi hj
    exact pow_w_ne _ hs i j hij (by rw [← hi, ← hj]; exact h0)
  · obtain ⟨u, a₀, hu, -, hχ⟩ := hF.gen v
    exact genI_of ⟨u, fun a => (hu a).1, hχ⟩
