import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.ExistsStrictAnti

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.ConeCount

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `f : kˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun y => Multiplicative.ofAdd (ord k y)) fun a b => by`. Rewrite using `[ord_mul, ofAdd_add]`. Establish `hf` using `congrArg Multiplicative.toAdd (map_zpow f x n)`. Simplify `hf` using `[f, smul_eq_mul]`.
-/
private theorem ord_zpow_twisted_operators (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let f : kˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun y => Multiplicative.ofAdd (ord k y)) fun a b => by
      rw [ord_mul, ofAdd_add]
  have hf := congrArg Multiplicative.toAdd (map_zpow f x n)
  simpa [f, smul_eq_mul] using hf

/- English proof (translation)
Rewrite using `[← ord_eq_zero_iff, div_eq_mul_inv, ord_mul, ← zpow_neg, ord_zpow_twisted_operators, ord_eq_one hϖ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valuation_div_zpow_ord {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    valuation k ((x / ϖ ^ ord k x : kˣ) : k) = 1 := by
  rw [← ord_eq_zero_iff, div_eq_mul_inv, ord_mul, ← zpow_neg, ord_zpow_twisted_operators, ord_eq_one hϖ]
  ring

def powHom {G : Type} [CommGroup G] (ϖ : G) (r : ℕ) :
    Multiplicative (Fin r → ℤ) →* (Fin r → G) :=
  MonoidHom.mk' (fun a i => ϖ ^ (Multiplicative.toAdd a) i) fun a b => by
    funext i
    simp [zpow_add]

/- English proof (translation)
Use `MonoidHom.ext fun t => ?_` and prove the remaining obligations. Establish `hu : (fun i => t i / ϖ ^ ord k (t i)) ∈ torusO k (Fin r)` using `by show ∀ i, valuation k ((t i / ϖ ^ ord k (t i) : kˣ) : k) = 1`. Conclude with `fun i => valuation_div_zpow_ord hϖ (t i)`. Establish `ht : t = (fun i => t i / ϖ ^ ord k (t i)) * powHom ϖ r (Multiplicative.ofAdd fun i => ord k (t i))`. Use function extensionality and compare the values at `i`.

Use `show t i = t i / ϖ ^ ord k (t i) * ϖ ^ ord k (t i)`. Rewrite using `[div_mul_cancel]`. Establish `hp` using `DFunLike.congr_fun h (Multiplicative.ofAdd fun i => ord k (t i))`. Rewrite `hp` using `[MonoidHom.comp_apply, MonoidHom.comp_apply]`. Rewrite using `[ht, map_mul, map_mul, hχ _ hu, hψ _ hu, one_mul, one_mul, hp]`.
-/
theorem eq_of_comp_powHom {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {r : ℕ}
    {χ ψ : (Fin r → kˣ) →* ℂˣ} (hχ : ∀ t ∈ torusO k (Fin r), χ t = 1)
    (hψ : ∀ t ∈ torusO k (Fin r), ψ t = 1)
    (h : χ.comp (powHom ϖ r) = ψ.comp (powHom ϖ r)) : χ = ψ := by
  refine MonoidHom.ext fun t => ?_

  have hu : (fun i => t i / ϖ ^ ord k (t i)) ∈ torusO k (Fin r) := by
    show ∀ i, valuation k ((t i / ϖ ^ ord k (t i) : kˣ) : k) = 1
    exact fun i => valuation_div_zpow_ord hϖ (t i)
  have ht : t = (fun i => t i / ϖ ^ ord k (t i)) *
      powHom ϖ r (Multiplicative.ofAdd fun i => ord k (t i)) := by
    funext i
    show t i = t i / ϖ ^ ord k (t i) * ϖ ^ ord k (t i)
    rw [div_mul_cancel]
  have hp := DFunLike.congr_fun h (Multiplicative.ofAdd fun i => ord k (t i))
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hp
  rw [ht, map_mul, map_mul, hχ _ hu, hψ _ hu, one_mul, one_mul, hp]

/- English proof (translation)
Set `M : Submonoid (Multiplicative (Fin r → ℤ))` to `{ carrier := {a | Antitone (Multiplicative.toAdd a)} mul_mem' := by`. Introduce `a b ha hb i j hij`. Conclude with `add_le_add (ha hij) (hb hij)`. Use the proof step `one_mem' := by`. Introduce `i j _`.

Conclude with `le_rfl }`. Set `φ : M →* (Fin r → kˣ)` to `(powHom ϖ r).comp M.subtype`. Set `t₀ : Fin r → kˣ` to `fun i => ϖ ^ (-((i : ℕ) : ℤ))`. Establish `hcone : ∀ m : M, t₀ * φ m ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r`. Introduce `m`.

Establish `hm : Antitone (Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)))` using `m.2`. Use `⟨fun i => -((i : ℕ) : ℤ) + Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)) i, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `h1` using `hm hij.le`. Establish `h2 : (i : ℕ) < j` using `hij`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `i show ϖ ^ (-((i : ℕ) : ℤ)) * ϖ ^ (Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)) i) = _`. Rewrite using `[← zpow_add]`. Establish `hdiff : ∀ a : Multiplicative (Fin r → ℤ), ∃ m₁ m₂ : M, a = (m₁ : Multiplicative (Fin r → ℤ)) * (m₂ : Multiplicative (Fin r → ℤ))⁻¹`.

Introduce `a`. Use `set K : ℤ := ∑ l, |Multiplicative.toAdd a l| with hK`. Establish `hK0 : 0 ≤ K` using `Finset.sum_nonneg fun l _ => abs_nonneg _`. Establish `hKl : ∀ l, |Multiplicative.toAdd a l| ≤ K` using `fun l => Finset.single_le_sum (f := fun l => |Multiplicative.toAdd a l|) (fun l _ => abs_nonneg _) (Finset.mem_univ l)`. Set `b : Multiplicative (Fin r → ℤ)` to `Multiplicative.ofAdd fun i => 2 * K * (-((i : ℕ) : ℤ))`.

Establish `hb : b ∈ M`. Introduce `i j hij`. Establish `h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ)` using `by exact_mod_cast hij`. Use `show 2 * K * (-((j : ℕ) : ℤ)) ≤ 2 * K * (-((i : ℕ) : ℤ))`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hab : a * b ∈ M`. Introduce `i j hij`. Use `show Multiplicative.toAdd a j + 2 * K * (-((j : ℕ) : ℤ)) ≤ Multiplicative.toAdd a i + 2 * K * (-((i : ℕ) : ℤ))`. Break down `eq_or_lt_of_le hij with h | h` into its components or cases. Rewrite using `[h]`.

Establish `h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ)`. Establish `: (i : ℕ) < j` using `h`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `hKl i`. Establish `h3` using `hKl j`.

Establish `h4` using `le_abs_self (Multiplicative.toAdd a j)`. Establish `h5` using `neg_abs_le (Multiplicative.toAdd a i)`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `⟨⟨a * b, hab⟩, ⟨b, hb⟩, by simp⟩`. Set `S : Finset ((Fin r → kˣ) →* ℂˣ)` to `Finset.univ.biUnion fun i => (E i).toFinset`.

Establish `hS : ∀ ψ ∈ S, ∀ t ∈ torusO k (Fin r), ψ t = 1`. Introduce `ψ hψ t ht`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 hψ`. Conclude with `hE i ψ (Multiset.mem_toFinset.1 hi) t ht`. Set `G : ((Fin r → kˣ) →* ℂˣ) → (M →* ℂ)` to `fun ψ => (Units.coeHom ℂ).comp (ψ.comp φ)`.

Establish `hinj : Function.Injective fun ψ : S => G ψ`. Introduce and unpack `⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩ h`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hM : ∀ m : M, ψ₁ (φ m) = ψ₂ (φ m)` using `fun m => Units.ext (DFunLike.congr_fun h m)`. Use `eq_of_comp_powHom hϖ (hS ψ₁ h₁) (hS ψ₂ h₂) (MonoidHom.ext fun a => ?_)` and prove the remaining obligations.

Take `⟨m₁, m₂, rfl⟩` from `hdiff a`. Establish `e₁` using `hM m₁`. Establish `e₂` using `hM m₂`. Simplify using `only [φ, MonoidHom.comp_apply, Submonoid.coe_subtype] at e₁ e₂`. Simplify using `only [MonoidHom.comp_apply, map_mul, map_inv, e₁, e₂]`.

Establish `hli` using `(linearIndependent_monoidHom M ℂ).comp (fun ψ : S => G ψ) hinj`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Establish `hsum : ∀ i t, IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = ∑ ψ ∈ S, ((E i).count ψ : ℂ) * (ψ t : ℂ)`. Introduce `i t`. Unfold `IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum`.

Rewrite using `[Finset.sum_multiset_map_count]`. Simplify using `only [nsmul_eq_mul]`. Use `Finset.sum_subset (fun ψ hψ => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hψ⟩) ?_` and prove the remaining obligations. Introduce `ψ _ hψ`. Rewrite using `[Multiset.count_eq_zero.2 fun h' => hψ (Multiset.mem_toFinset.2 h'), Nat.cast_zero, zero_mul]`.

Establish `hw` using `hli (fun ψ => (∑ i, c i * ((E i).count (ψ : (Fin r → kˣ) →* ℂˣ) : ℂ)) * (ψ.1 t₀ : ℂ)) (by`. Use function extensionality and compare the values at `m`. Establish `hm` using `h _ (hcone m)`. Simplify using `only [hsum, Finset.mul_sum] at hm`. Rewrite `hm` using `[Finset.sum_comm, ← Finset.sum_coe_sort S]`.

Rewrite using `[Finset.sum_apply, Pi.zero_apply, ← hm]`. Use `Finset.sum_congr rfl fun ψ _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, G, φ, MonoidHom.comp_apply, Units.coeHom_apply, map_mul, Units.val_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use the proof step `ring)`.

Distinguish the cases in `hχ : χ ∈ S`. Establish `h0` using `hw ⟨χ, hχ⟩`. Conclude with `(mul_eq_zero.1 h0).resolve_right (Units.ne_zero _)`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Multiset.count_eq_zero.2 fun h' => hχ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.2 h'⟩)]`.

Simplify using the standard rewrite rules.
-/
theorem sum_count_eq_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (r n : ℕ)
    (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)) (c : Fin n → ℂ)
    (hE : ∀ i, ∀ χ ∈ E i, ∀ t ∈ torusO k (Fin r), χ t = 1)
    (h : ∀ t ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r, ∑ i, c i * IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = 0)
    [DecidableEq ((Fin r → kˣ) →* ℂˣ)] (χ : (Fin r → kˣ) →* ℂˣ) :
    ∑ i, c i * ((E i).count χ : ℂ) = 0 := by

  let M : Submonoid (Multiplicative (Fin r → ℤ)) :=
    { carrier := {a | Antitone (Multiplicative.toAdd a)}
      mul_mem' := by
        intro a b ha hb i j hij
        exact add_le_add (ha hij) (hb hij)
      one_mem' := by
        intro i j _
        exact le_rfl }
  let φ : M →* (Fin r → kˣ) := (powHom ϖ r).comp M.subtype

  let t₀ : Fin r → kˣ := fun i => ϖ ^ (-((i : ℕ) : ℤ))
  have hcone : ∀ m : M, t₀ * φ m ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r := by
    intro m
    have hm : Antitone (Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ))) := m.2
    refine ⟨fun i => -((i : ℕ) : ℤ) + Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)) i, ?_, ?_⟩
    · intro i j hij
      have h1 := hm hij.le
      have h2 : (i : ℕ) < j := hij
      simp only
      omega
    · funext i
      show ϖ ^ (-((i : ℕ) : ℤ)) * ϖ ^ (Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)) i) = _
      rw [← zpow_add]

  have hdiff : ∀ a : Multiplicative (Fin r → ℤ), ∃ m₁ m₂ : M,
      a = (m₁ : Multiplicative (Fin r → ℤ)) * (m₂ : Multiplicative (Fin r → ℤ))⁻¹ := by
    intro a
    set K : ℤ := ∑ l, |Multiplicative.toAdd a l| with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun l _ => abs_nonneg _
    have hKl : ∀ l, |Multiplicative.toAdd a l| ≤ K := fun l =>
      Finset.single_le_sum (f := fun l => |Multiplicative.toAdd a l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    let b : Multiplicative (Fin r → ℤ) := Multiplicative.ofAdd fun i => 2 * K * (-((i : ℕ) : ℤ))
    have hb : b ∈ M := by
      intro i j hij
      have h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
      show 2 * K * (-((j : ℕ) : ℤ)) ≤ 2 * K * (-((i : ℕ) : ℤ))
      nlinarith
    have hab : a * b ∈ M := by
      intro i j hij
      show Multiplicative.toAdd a j + 2 * K * (-((j : ℕ) : ℤ))
        ≤ Multiplicative.toAdd a i + 2 * K * (-((i : ℕ) : ℤ))
      rcases eq_or_lt_of_le hij with h | h
      · rw [h]
      · have h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by
          have : (i : ℕ) < j := h
          omega
        have h2 := hKl i
        have h3 := hKl j
        have h4 := le_abs_self (Multiplicative.toAdd a j)
        have h5 := neg_abs_le (Multiplicative.toAdd a i)
        nlinarith
    exact ⟨⟨a * b, hab⟩, ⟨b, hb⟩, by simp⟩

  let S : Finset ((Fin r → kˣ) →* ℂˣ) := Finset.univ.biUnion fun i => (E i).toFinset
  have hS : ∀ ψ ∈ S, ∀ t ∈ torusO k (Fin r), ψ t = 1 := by
    intro ψ hψ t ht
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hψ
    exact hE i ψ (Multiset.mem_toFinset.1 hi) t ht

  let G : ((Fin r → kˣ) →* ℂˣ) → (M →* ℂ) := fun ψ => (Units.coeHom ℂ).comp (ψ.comp φ)
  have hinj : Function.Injective fun ψ : S => G ψ := by
    rintro ⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩ h
    apply Subtype.ext
    have hM : ∀ m : M, ψ₁ (φ m) = ψ₂ (φ m) := fun m => Units.ext (DFunLike.congr_fun h m)
    refine eq_of_comp_powHom hϖ (hS ψ₁ h₁) (hS ψ₂ h₂) (MonoidHom.ext fun a => ?_)
    obtain ⟨m₁, m₂, rfl⟩ := hdiff a
    have e₁ := hM m₁
    have e₂ := hM m₂
    simp only [φ, MonoidHom.comp_apply, Submonoid.coe_subtype] at e₁ e₂
    simp only [MonoidHom.comp_apply, map_mul, map_inv, e₁, e₂]
  have hli := (linearIndependent_monoidHom M ℂ).comp (fun ψ : S => G ψ) hinj
  rw [Fintype.linearIndependent_iff] at hli

  have hsum : ∀ i t, IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = ∑ ψ ∈ S, ((E i).count ψ : ℂ) * (ψ t : ℂ) := by
    intro i t
    unfold IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum
    rw [Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
    refine Finset.sum_subset (fun ψ hψ => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hψ⟩) ?_
    intro ψ _ hψ
    rw [Multiset.count_eq_zero.2 fun h' => hψ (Multiset.mem_toFinset.2 h'), Nat.cast_zero, zero_mul]
  have hw := hli (fun ψ => (∑ i, c i * ((E i).count (ψ : (Fin r → kˣ) →* ℂˣ) : ℂ)) * (ψ.1 t₀ : ℂ))
    (by
      funext m
      have hm := h _ (hcone m)
      simp only [hsum, Finset.mul_sum] at hm
      rw [Finset.sum_comm, ← Finset.sum_coe_sort S] at hm
      rw [Finset.sum_apply, Pi.zero_apply, ← hm]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, G, φ, MonoidHom.comp_apply,
        Units.coeHom_apply, map_mul, Units.val_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  by_cases hχ : χ ∈ S
  · have h0 := hw ⟨χ, hχ⟩
    exact (mul_eq_zero.1 h0).resolve_right (Units.ne_zero _)
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [Multiset.count_eq_zero.2 fun h' =>
      hχ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.2 h'⟩)]
    simp

end GlobalTheory.ConeCount
