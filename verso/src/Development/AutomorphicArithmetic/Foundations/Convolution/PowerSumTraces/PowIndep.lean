import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Rewrite using `[Finset.sum_multiset_map_count]`. Establish `hsub : s.toFinset ⊆ S` using `fun z hz => h z (Multiset.mem_toFinset.1 hz)`. Rewrite using `[← Finset.sum_subset hsub]`. Conclude with `Finset.sum_congr rfl fun z _ => by simp [nsmul_eq_mul]`. Introduce `z _ hz`.

Establish `: s.count z = 0` using `Multiset.count_eq_zero.2 fun hm => hz (Multiset.mem_toFinset.2 hm)`. Simplify using `[this]`.
-/
private lemma powSum_eq_count (s : Multiset ℂ) (S : Finset ℂ) (h : ∀ z ∈ s, z ∈ S) (j : ℕ) :
    (s.map (· ^ j)).sum = ∑ z ∈ S, (s.count z : ℂ) * z ^ j := by
  classical
  rw [Finset.sum_multiset_map_count]
  have hsub : s.toFinset ⊆ S := fun z hz => h z (Multiset.mem_toFinset.1 hz)
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_congr rfl fun z _ => by simp [nsmul_eq_mul]
  · intro z _ hz
    have : s.count z = 0 := Multiset.count_eq_zero.2 fun hm => hz (Multiset.mem_toFinset.2 hm)
    simp [this]

private def powHom (z : ℂ) : Multiplicative ℕ →* ℂ where
  toFun n := z ^ n.toAdd
  map_one' := by simp
  map_mul' a b := by simp [pow_add]

/- English proof (translation)
Introduce `a b h`. Use `DFunLike.congr_fun h (Multiplicative.ofAdd 1)` as an intermediate fact. Simplify `this` using `[powHom]`.
-/
private lemma powHom_injective : Function.Injective powHom := by
  intro a b h
  have := DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  simpa [powHom] using this

/- English proof (translation)
Introduce `ι _ c Z hZ hev ζ`. Take `⟨N, hN⟩` from `eventually_atTop.1 hev`. Set `S : Finset ℂ` to `Finset.univ.biUnion fun i => (Z i).toFinset`. Set `a : ℂ → ℂ` to `fun z => ∑ i, c i * ((Z i).count z : ℂ)`. Establish `hmem : ∀ i, ∀ z ∈ Z i, z ∈ S` using `fun i z hz => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.2 hz⟩`.

Establish `key : ∀ j, N ≤ j → ∑ z ∈ S, a z * z ^ j = 0`. Introduce `j hj`. Establish `h0` using `hN j hj`. Simplify using `only [powSum_eq_count _ S (hmem _) j, Finset.mul_sum] at h0`. Rewrite `h0` using `[Finset.sum_comm]`.

Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [a, Finset.sum_mul, mul_assoc]`. Establish `hne : ∀ z ∈ S, z ≠ 0`. Introduce `z hz h0`.

Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 hz`. Conclude with `hZ i (h0 ▸ Multiset.mem_toFinset.1 hi)`. Establish `lin : LinearIndependent ℂ (fun z : S => (powHom z : Multiplicative ℕ → ℂ))` using `(linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun z : S => powHom z) (powHom_injective.comp Subtype.val_injective)`. Rewrite `lin` using `[Fintype.linearIndependent_iff]`. Establish `hb` using `lin (fun z => a z * (z : ℂ) ^ N) (by`.

Use function extensionality and compare the values at `n`. Use `key (N + n.toAdd) (Nat.le_add_right _ _)` as an intermediate fact. Rewrite `this` using `[← Finset.sum_coe_sort S]`. Simplify `this)` using `[powHom, pow_add, mul_assoc, Finset.sum_apply]`. Establish `ha : a ζ = 0`.

Distinguish the cases in `hζ : ζ ∈ S`. Use `hb ⟨ζ, hζ⟩` as an intermediate fact. Conclude with `(mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (hne ζ hζ))`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `: (Z i).count ζ = 0` using `Multiset.count_eq_zero.2 fun hm => hζ (hmem i ζ hm)`.

Simplify using `[this]`. Rewrite using `[← ha]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Rewrite using `[Multiset.filter_eq', Multiset.card_replicate]`.
-/
theorem UpperTheory.ConvolutionTheory.C.powIndep :
    UpperTheory.ConvolutionTheory.C.PowIndep := by
  classical
  intro ι _ c Z hZ hev ζ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Finset ℂ := Finset.univ.biUnion fun i => (Z i).toFinset
  let a : ℂ → ℂ := fun z => ∑ i, c i * ((Z i).count z : ℂ)
  have hmem : ∀ i, ∀ z ∈ Z i, z ∈ S := fun i z hz =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.2 hz⟩
  have key : ∀ j, N ≤ j → ∑ z ∈ S, a z * z ^ j = 0 := by
    intro j hj
    have h0 := hN j hj
    simp only [powSum_eq_count _ S (hmem _) j, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [a, Finset.sum_mul, mul_assoc]
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hZ i (h0 ▸ Multiset.mem_toFinset.1 hi)
  have lin : LinearIndependent ℂ (fun z : S => (powHom z : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun z : S => powHom z)
      (powHom_injective.comp Subtype.val_injective)
  rw [Fintype.linearIndependent_iff] at lin
  have hb := lin (fun z => a z * (z : ℂ) ^ N) (by
    funext n
    have := key (N + n.toAdd) (Nat.le_add_right _ _)
    rw [← Finset.sum_coe_sort S] at this
    simpa [powHom, pow_add, mul_assoc, Finset.sum_apply] using this)
  have ha : a ζ = 0 := by
    by_cases hζ : ζ ∈ S
    · have := hb ⟨ζ, hζ⟩
      exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (hne ζ hζ))
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : (Z i).count ζ = 0 := Multiset.count_eq_zero.2 fun hm => hζ (hmem i ζ hm)
      simp [this]
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Multiset.filter_eq', Multiset.card_replicate]
