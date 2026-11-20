import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UnitaryDetClass

set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Jets.TautMarking

/- English proof (translation)
Introduce `E _ _ _ n Q Λ _ hU ⟨k, hk, h1, h2⟩`. Take `⟨a, b, hab⟩ : IsCoprime (k : 𝓞 E) (Q : 𝓞 E)` from `Nat.Coprime.cast hk`. Establish `habE : (a : E) * (k : E) + (b : E) * (Q : E) = 1`. Use `congrArg (algebraMap (𝓞 E) E) hab` as an intermediate fact. Simplify using `using this`.

Establish `hf : ∀ (v : Λ.La) (j : Fin n), ∃ s : 𝓞 E, (s : E) = (k : E) * (v : Fin n → E) j`. Introduce `v j`. Use `h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 E)) v.2) j (Set.mem_univ j)` as an intermediate fact. Take `⟨s, hs⟩` from `Submodule.mem_one.mp this`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Simplify `hs` using `[Algebra.smul_def]`. Use `choose f hf using hf`. Establish `hg : ∀ x : Fin n → 𝓞 E, (fun j => (k : E) * (x j : E)) ∈ Λ.La`. Introduce `x`. Establish `hx : (fun j => (x j : E)) ∈ stdLat E n` using `fun j _ => Submodule.mem_one.mpr ⟨x j, rfl⟩`.

Use `h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 E)) hx)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Simplify using `[Algebra.smul_def]`. Establish `inj : Function.Injective (fun s : 𝓞 E => (s : E))` using `RingOfIntegers.coe_injective`.

Set `F : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E)` to `{ toFun := f map_add' := fun v w => funext fun j => inj (by simp [hf, mul_add]) map_smul' := fun c v => funext fun j => inj (by`. Simplify using `[hf, Algebra.smul_def]`. Use the proof step `ring) }`. Set `κ : Λ.La →ₗ[𝓞 E] GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.StdMod E n Q` to `LinearMap.pi fun j => (Ideal.span {(Q : 𝓞 E)}).mkQ ∘ₗ (a • (LinearMap.proj j ∘ₗ F))`. Establish `hκ : ∀ v j, κ v j = Ideal.Quotient.mk _ (a * f v j)` using `fun v j => rfl`.

Establish `key : ∀ (v : Λ.La) (j : Fin n) (x : 𝓞 E), κ v j = Ideal.Quotient.mk _ x → ∃ t : 𝓞 E, (a : E) * ((k : E) * (v : Fin n → E) j) - (x : E) = (Q : E) * (t : E)`. Introduce `v j x h`. Rewrite `h` using `[hκ, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `h`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Use `congrArg (algebraMap (𝓞 E) E) ht` as an intermediate fact. Rewrite using `[← hf]`. Simplify using `using this`. Establish `key2 : ∀ (v : Λ.La) (j : Fin n) (x : 𝓞 E), κ v j = Ideal.Quotient.mk _ x → ∃ s : 𝓞 E, (k : E) * ((v : Fin n → E) j - (x : E)) = (Q : E) * (s : E)`. Introduce `v j x h`.

Take `⟨t, ht⟩` from `key v j x h`. Use `⟨b * f v j + k * t, ?_⟩` and prove the remaining obligations. Establish `e : ((b * f v j + k * t : 𝓞 E) : E) = (b : E) * ((k : E) * (v : Fin n → E) j) + (k : E) * (t : E)`. Rewrite using `[← hf]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Take the linear combination `(k : E) * ht - (k : E) * (v : Fin n → E) j * habE`. Use `⟨κ, ⟨?_, ?_, ?_⟩, fun v x h => ⟨k, hk, fun j => key2 v j (x j) (h j)⟩⟩` and prove the remaining obligations. Introduce `z choose x hx using fun j => Ideal.Quotient.mk_surjective (z j)`. Use `⟨⟨_, hg fun j => a * x j⟩, funext fun j => ?_⟩` and prove the remaining obligations.

Establish `e : f ⟨_, hg fun j => a * x j⟩ j = k * (k * (a * x j))` using `inj (by simp [hf])`. Rewrite using `[hκ, e, ← hx, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `⟨-b * (a * k + 1) * x j, by linear_combination (a * k + 1) * x j * hab⟩`. Introduce `v`. Prove the components needed by the constructor for the conclusion.

Introduce `h choose t ht using fun j => key v j 0 (by rw [h]; simp)`. Use `⟨a • (⟨_, hg t⟩ : Λ.La) + (a * b * k + b) • v, Subtype.ext (funext fun j => ?_)⟩` and prove the remaining obligations. Use `ht j` as an intermediate fact. Simplify using `[Algebra.smul_def] at this ⊢`. Take the linear combination `(a : E) * (k : E) * this - ((a : E) * k + 1) * (v : Fin n → E) j * habE`.

Introduce and unpack `⟨u, rfl⟩`. Use function extensionality and compare the values at `j`. Rewrite using `[map_nsmul, Pi.smul_apply, hκ, Pi.zero_apply, ← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`. Introduce `v w x y hx hy choose s hs using fun j => key2 v j (x j) (hx j) choose t ht using fun j => key2 w j (y j) (hy j)`.

Take `⟨d, hd⟩` from `(hU v).mp v.2 w w.2`. Use `set c := IsCMField.ringOfIntegersComplexConj E with hc`. Establish `hcc : ∀ z : 𝓞 E, ((c z : 𝓞 E) : E) = IsCMField.complexConj E (z : E)` using `fun z => IsCMField.coe_ringOfIntegersComplexConj E z`. Establish `hs' : ∀ j, (k : E) * (IsCMField.complexConj E ((v : Fin n → E) j) - IsCMField.complexConj E (x j : E)) = (Q : E) * IsCMField.complexConj E (s j : E)` using `fun j => by`. Simplify using `using congrArg (IsCMField.complexConj E) (hs j)`.

Set `e : 𝓞 E` to `∑ j, (c (s j) * k * y j + k * c (x j) * t j + Q * c (s j) * t j)`. Set `d' : 𝓞 E` to `d - ∑ j, c (x j) * y j`. Establish `hd' : (d' : E) = ∑ j, IsCMField.complexConj E ((v : Fin n → E) j) * (w : Fin n → E) j - ∑ j, IsCMField.complexConj E (x j : E) * (y j : E)`. Rewrite using `[← hd]`. Simplify using `[d', ← hcc]`.

Establish `he : (k : E) ^ 2 * (d' : E) = (Q : E) * (e : E)`. Establish `e1 : (e : E) = ∑ j, (IsCMField.complexConj E (s j : E) * k * (y j : E) + k * IsCMField.complexConj E (x j : E) * (t j : E) + Q * IsCMField.complexConj E (s j : E) * (t j : E))`. Simplify using `[e, ← hcc]`. Rewrite using `[hd', e1, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Take the linear combination `((k : E) * (w : Fin n → E) j) * hs' j + ((k : E) * IsCMField.complexConj E (x j : E) + Q * IsCMField.complexConj E (s j : E)) * ht j`. Use `⟨a ^ 2 * e + (2 * a * k * b + b ^ 2 * Q) * d', ?_⟩` and prove the remaining obligations. Rewrite using `[← hd']`. Establish `e2 : ((a ^ 2 * e + (2 * a * k * b + b ^ 2 * Q) * d' : 𝓞 E) : E) = (a : E) ^ 2 * (e : E) + (2 * (a : E) * k * b + (b : E) ^ 2 * Q) * (d' : E)`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_pow, map_natCast, map_ofNat]`.

Rewrite using `[e2]`. Take the linear combination `(a : E) ^ 2 * he - ((a : E) * k + b * Q + 1) * (d' : E) * habE`.
-/
theorem exists_tautological_marking :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n Q : ℕ) (Λ : GenLat E n), 0 < Q → Λ.Unimod → Λ.TrivAt Q → ∃ κ : Λ.La →ₗ[𝓞 E] GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.StdMod E n Q, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsMarking Q Λ κ ∧ ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.CongrAt Q (v : Fin n → E) fun j => (x j : E) := by
  intro E _ _ _ n Q Λ _ hU ⟨k, hk, h1, h2⟩
  obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 E) (Q : 𝓞 E) := Nat.Coprime.cast hk
  have habE : (a : E) * (k : E) + (b : E) * (Q : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) hab
    simpa using this
  have hf : ∀ (v : Λ.La) (j : Fin n), ∃ s : 𝓞 E, (s : E) = (k : E) * (v : Fin n → E) j := by
    intro v j
    have := h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 E)) v.2) j (Set.mem_univ j)
    obtain ⟨s, hs⟩ := Submodule.mem_one.mp this
    refine ⟨s, ?_⟩
    simpa [Algebra.smul_def] using hs
  choose f hf using hf
  have hg : ∀ x : Fin n → 𝓞 E, (fun j => (k : E) * (x j : E)) ∈ Λ.La := by
    intro x
    have hx : (fun j => (x j : E)) ∈ stdLat E n := fun j _ => Submodule.mem_one.mpr ⟨x j, rfl⟩
    have := h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 E)) hx)
    convert this using 1
    ext j
    simp [Algebra.smul_def]
  have inj : Function.Injective (fun s : 𝓞 E => (s : E)) := RingOfIntegers.coe_injective
  let F : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E) :=
    { toFun := f
      map_add' := fun v w => funext fun j => inj (by simp [hf, mul_add])
      map_smul' := fun c v => funext fun j => inj (by
        simp [hf, Algebra.smul_def]; ring) }
  let κ : Λ.La →ₗ[𝓞 E] GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.StdMod E n Q :=
    LinearMap.pi fun j => (Ideal.span {(Q : 𝓞 E)}).mkQ ∘ₗ (a • (LinearMap.proj j ∘ₗ F))
  have hκ : ∀ v j, κ v j = Ideal.Quotient.mk _ (a * f v j) := fun v j => rfl
  have key : ∀ (v : Λ.La) (j : Fin n) (x : 𝓞 E), κ v j = Ideal.Quotient.mk _ x →
      ∃ t : 𝓞 E, (a : E) * ((k : E) * (v : Fin n → E) j) - (x : E) = (Q : E) * (t : E) := by
    intro v j x h
    rw [hκ, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    obtain ⟨t, ht⟩ := h
    refine ⟨t, ?_⟩
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [← hf]
    simpa using this
  have key2 : ∀ (v : Λ.La) (j : Fin n) (x : 𝓞 E), κ v j = Ideal.Quotient.mk _ x →
      ∃ s : 𝓞 E, (k : E) * ((v : Fin n → E) j - (x : E)) = (Q : E) * (s : E) := by
    intro v j x h
    obtain ⟨t, ht⟩ := key v j x h
    refine ⟨b * f v j + k * t, ?_⟩
    have e : ((b * f v j + k * t : 𝓞 E) : E) = (b : E) * ((k : E) * (v : Fin n → E) j) + (k : E) * (t : E) := by
      rw [← hf]; simp
    rw [e]
    linear_combination (k : E) * ht - (k : E) * (v : Fin n → E) j * habE
  refine ⟨κ, ⟨?_, ?_, ?_⟩, fun v x h => ⟨k, hk, fun j => key2 v j (x j) (h j)⟩⟩
  · intro z
    choose x hx using fun j => Ideal.Quotient.mk_surjective (z j)
    refine ⟨⟨_, hg fun j => a * x j⟩, funext fun j => ?_⟩
    have e : f ⟨_, hg fun j => a * x j⟩ j = k * (k * (a * x j)) := inj (by simp [hf])
    rw [hκ, e, ← hx, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-b * (a * k + 1) * x j, by linear_combination (a * k + 1) * x j * hab⟩
  · intro v
    constructor
    · intro h
      choose t ht using fun j => key v j 0 (by rw [h]; simp)
      refine ⟨a • (⟨_, hg t⟩ : Λ.La) + (a * b * k + b) • v, Subtype.ext (funext fun j => ?_)⟩
      have := ht j
      simp [Algebra.smul_def] at this ⊢
      linear_combination (a : E) * (k : E) * this - ((a : E) * k + 1) * (v : Fin n → E) j * habE
    · rintro ⟨u, rfl⟩
      funext j
      rw [map_nsmul, Pi.smul_apply, hκ, Pi.zero_apply, ← map_nsmul, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton, nsmul_eq_mul]
      exact dvd_mul_right _ _
  · intro v w x y hx hy
    choose s hs using fun j => key2 v j (x j) (hx j)
    choose t ht using fun j => key2 w j (y j) (hy j)
    obtain ⟨d, hd⟩ := (hU v).mp v.2 w w.2
    set c := IsCMField.ringOfIntegersComplexConj E with hc
    have hcc : ∀ z : 𝓞 E, ((c z : 𝓞 E) : E) = IsCMField.complexConj E (z : E) :=
      fun z => IsCMField.coe_ringOfIntegersComplexConj E z
    have hs' : ∀ j, (k : E) * (IsCMField.complexConj E ((v : Fin n → E) j) - IsCMField.complexConj E (x j : E)) =
        (Q : E) * IsCMField.complexConj E (s j : E) := fun j => by
      simpa using congrArg (IsCMField.complexConj E) (hs j)
    let e : 𝓞 E := ∑ j, (c (s j) * k * y j + k * c (x j) * t j + Q * c (s j) * t j)
    let d' : 𝓞 E := d - ∑ j, c (x j) * y j
    have hd' : (d' : E) = ∑ j, IsCMField.complexConj E ((v : Fin n → E) j) * (w : Fin n → E) j -
        ∑ j, IsCMField.complexConj E (x j : E) * (y j : E) := by
      rw [← hd]
      simp [d', ← hcc]
    have he : (k : E) ^ 2 * (d' : E) = (Q : E) * (e : E) := by
      have e1 : (e : E) = ∑ j, (IsCMField.complexConj E (s j : E) * k * (y j : E) +
          k * IsCMField.complexConj E (x j : E) * (t j : E) + Q * IsCMField.complexConj E (s j : E) * (t j : E)) := by
        simp [e, ← hcc]
      rw [hd', e1, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination ((k : E) * (w : Fin n → E) j) * hs' j +
        ((k : E) * IsCMField.complexConj E (x j : E) + Q * IsCMField.complexConj E (s j : E)) * ht j
    refine ⟨a ^ 2 * e + (2 * a * k * b + b ^ 2 * Q) * d', ?_⟩
    rw [← hd']
    have e2 : ((a ^ 2 * e + (2 * a * k * b + b ^ 2 * Q) * d' : 𝓞 E) : E) =
        (a : E) ^ 2 * (e : E) + (2 * (a : E) * k * b + (b : E) ^ 2 * Q) * (d' : E) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_pow, map_natCast, map_ofNat]
    rw [e2]
    linear_combination (a : E) ^ 2 * he - ((a : E) * k + b * Q + 1) * (d' : E) * habE

end GlobalTheory.Jets.TautMarking
