import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSCCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen

open NumberField

namespace GlobalTheory.PlaceInt

open NumberField in

/- English proof (translation)
Establish `inj : Function.Injective (algebraMap V k)` using `IsFractionRing.injective V k`. Establish `hint : ∀ x : 𝓞 E, ∃ y : V, algebraMap V k y = ψ (x : E)`. Introduce `x`. Establish `h1 : IsIntegral ℤ (ψ (x : E))` using `x.isIntegral_coe.map ψ.toIntAlgHom`. Establish `h2 : IsIntegral V (ψ (x : E))` using `h1.tower_top`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.mp h2`. Use `choose f hf using hint`. Use `⟨{ toFun := f map_one' := inj (by rw [hf, map_one]; simp) map_mul' := fun x y => inj (by rw [map_mul, hf, hf, hf]; push_cast; rw [map_mul]) map_zero' := inj (by rw [hf, map_zero]; simp) map_add' := fun x y => inj (by rw [map_add, hf, hf, hf]; push_cast; rw [map_add]) }, hf⟩` and prove the remaining obligations.
-/
theorem _root_.GlobalTheory.PlaceInt.exists_ringOfIntegers_lift (E : Type) [Field E] [NumberField E]
    (V : Type) [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by
  have inj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  have hint : ∀ x : 𝓞 E, ∃ y : V, algebraMap V k y = ψ (x : E) := by
    intro x
    have h1 : IsIntegral ℤ (ψ (x : E)) := x.isIntegral_coe.map ψ.toIntAlgHom
    have h2 : IsIntegral V (ψ (x : E)) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  choose f hf using hint
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, hf, hf, hf]; push_cast; rw [map_mul])
            map_zero' := inj (by rw [hf, map_zero]; simp)
            map_add' := fun x y => inj (by rw [map_add, hf, hf, hf]; push_cast; rw [map_add]) },
    hf⟩

open NumberField Polynomial IsLocalRing in

/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt`. Introduce `E _ _ V _ _ _ _ k _ _ _ P hP hP0`. Use `choose σ hσ using fun ψ : E →+* k => _root_.GlobalTheory.PlaceInt.exists_ringOfIntegers_lift E V k ψ`. Establish `inj : Function.Injective (algebraMap V k)` using `IsFractionRing.injective V k`. Take `⟨Q, hQ, hQp⟩ : ∃ Q : (E →+* k) → Ideal (𝓞 E), (∀ ψ x, x ∈ Q ψ ↔ σ ψ x ∈ maximalIdeal V) ∧ ∀ ψ, (Q ψ).IsPrime` from `⟨fun ψ => (maximalIdeal V).comap (σ ψ), fun _ _ => Iff.rfl, fun _ => inferInstance⟩`.

Establish `hcond : ∀ ψ : E →+* k, (∀ x : 𝓞 E, x ∈ P ↔ ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V)) ↔ Q ψ = P`. Introduce `ψ`. Establish `key : ∀ x : 𝓞 E, ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V) ↔ x ∈ Q ψ`. Introduce `x`. Rewrite using `[hQ, ← hσ]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Conclude with `inj h ▸ hy`. Introduce `h`. Conclude with `⟨_, h, rfl⟩`.

Simplify using `only [key]`. Rewrite using `[eq_comm, SetLike.ext_iff]`. Distinguish the cases in `hex : ∃ ψ0 : E →+* k, Q ψ0 = P`. Use `swap`. Use `⟨0, Fin.elim0, Fin.elim0, fun ψ => ?_⟩` and prove the remaining obligations.

Rewrite using `[if_neg (fun h => hex ⟨ψ, (hcond ψ).mp h⟩)]`. Simplify using the standard rewrite rules. Take `⟨ψ0, hψ0⟩` from `hex`. Use `haveI : CharZero k := ⟨fun a b h => by`. Rewrite `h` using `[← map_natCast ψ0, ← map_natCast ψ0 b]`.

Conclude with `Nat.cast_injective (ψ0.injective h)⟩`. Establish `hPmax : P.IsMaximal` using `hP.isMaximal hP0`. Use `set N : ℕ := Ideal.absNorm P with hN`. Establish `hNP : (N : 𝓞 E) ∈ P` using `Ideal.absNorm_mem P`. Establish `hN0 : (N : 𝓞 E) ≠ 0`.

Rewrite using `[Nat.cast_ne_zero, hN]`. Conclude with `fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hNQ : ∀ ψ, (N : 𝓞 E) ∈ Q ψ`. Introduce `ψ`. Establish `h0 : (N : 𝓞 E) ∈ Q ψ0` using `hψ0 ▸ hNP`.

Rewrite `h0`, the goal using `[hQ, map_natCast]`. Conclude with `h0`. Establish `hc : ∀ ψ, ∃ c : 𝓞 E, c ∉ P ∧ (Q ψ ≠ P → c ∈ Q ψ)`. Introduce `ψ`. Distinguish the cases in `h : Q ψ = P`.

Conclude with `⟨1, fun h1 => hPmax.ne_top ((Ideal.eq_top_iff_one _).2 h1), fun h' => (h' h).elim⟩`. Establish `hQ0 : Q ψ ≠ ⊥` using `fun h0 => hN0 (by simpa [h0] using hNQ ψ)`. Establish `hQmax : (Q ψ).IsMaximal` using `(hQp ψ).isMaximal hQ0`. Establish `hnle : ¬ Q ψ ≤ P` using `fun hle => h (hQmax.eq_of_le hPmax.ne_top hle)`. Take `⟨c, hcQ, hcP⟩` from `SetLike.not_le_iff_exists.mp hnle`.

Conclude with `⟨c, hcP, fun _ => hcQ⟩`. Use `choose c hcP hcQ using hc`. Establish `hprod : ∏ ψ, c ψ ∉ P`. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨ψ, -, h⟩`.

Conclude with `hcP ψ h`. Take `⟨y, i, hi, hyi⟩` from `hPmax.exists_inv hprod`. Use `set b : 𝓞 E := y * ∏ ψ, c ψ with hb`. Establish `hb1 : ∀ ψ, Q ψ = P → σ ψ b - 1 ∈ maximalIdeal V`. Introduce `ψ h`.

Establish `: b - 1 ∈ Q ψ`. Rewrite using `[h]`. Establish `: b - 1 = -i` using `by rw [hb, ← hyi]; ring`. Rewrite using `[this]`. Conclude with `P.neg_mem hi`.

Rewrite `this` using `[hQ, map_sub, map_one]`. Conclude with `this`. Establish `hb0 : ∀ ψ, Q ψ ≠ P → σ ψ b ∈ maximalIdeal V`. Introduce `ψ h`. Rewrite using `[← hQ]`.

Take `⟨r, hr⟩` from `Finset.dvd_prod_of_mem c (Finset.mem_univ ψ)`. Rewrite using `[hb, hr]`. Conclude with `(Q ψ).mul_mem_left _ ((Q ψ).mul_mem_right _ (hcQ ψ h))`. Use `set p0 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ ≠ P), (X - C (σ ψ b)) with hp0`. Use `set p1 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ = P), (X - C (σ ψ b)) with hp1`.

Establish `hcop : IsCoprime p0 p1`. Rewrite using `[hp0, hp1]`. Use `IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ hφ`. Apply `isCoprime_X_sub_C_of_isUnit_sub` to reduce the goal to its premises.

Establish `h0` using `hb0 ψ hψ`. Establish `h1` using `hb1 φ hφ`. Establish `hnot : σ ψ b - σ φ b ∉ maximalIdeal V`. Introduce `h`. Apply `(maximalIdeal.isMaximal V).ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Use `sub_mem (sub_mem h0 h) h1` as an intermediate fact. Simplify using `using this`. Simplify `hnot` using `[mem_maximalIdeal, mem_nonunits_iff]`. Take `⟨u, v, huv⟩` from `hcop`.

Use `set g : V[X] := u * p0 with hg`. Use `⟨g.natDegree + 1, fun j => b ^ (j : ℕ), fun j => g.coeff j, fun ψ => ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ j : Fin (g.natDegree + 1), algebraMap V k (g.coeff j) * ψ ((b ^ (j : ℕ) : 𝓞 E) : E) = algebraMap V k (g.eval (σ ψ b))`. Rewrite using `[eval_eq_sum_range' (Nat.lt_succ_self _), map_sum, ← Fin.sum_univ_eq_sum_range (fun j => algebraMap V k (g.coeff j * σ ψ b ^ j))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hσ]`. Simplify using `only [map_pow, map_mul]`. Rewrite using `[hsum]`. Distinguish the cases in `h : Q ψ = P`. Rewrite using `[if_pos ((hcond ψ).mpr h)]`.

Establish `hp1z : p1.eval (σ ψ b) = 0`. Rewrite using `[hp1, eval_prod]`. Conclude with `Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)`. Establish `: g.eval (σ ψ b) = 1`. Establish `h2 : (u * p0 + v * p1).eval (σ ψ b) = 1` using `by rw [huv, eval_one]`.

Rewrite `h2` using `[eval_add, show (v * p1).eval (σ ψ b) = 0 by rw [eval_mul, hp1z, mul_zero], add_zero]`. Conclude with `h2`. Rewrite using `[this, map_one]`. Rewrite using `[if_neg (fun h' => h ((hcond ψ).mp h'))]`. Establish `hp0z : p0.eval (σ ψ b) = 0`.

Rewrite using `[hp0, eval_prod]`. Conclude with `Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)`. Rewrite using `[hg, eval_mul, hp0z, mul_zero, map_zero]`.
-/
theorem _root_.GlobalTheory.PlaceInt.placeIdem : _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt
  intro E _ _ V _ _ _ _ k _ _ _ P hP hP0
  classical
  choose σ hσ using fun ψ : E →+* k => _root_.GlobalTheory.PlaceInt.exists_ringOfIntegers_lift E V k ψ
  have inj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  obtain ⟨Q, hQ, hQp⟩ : ∃ Q : (E →+* k) → Ideal (𝓞 E),
      (∀ ψ x, x ∈ Q ψ ↔ σ ψ x ∈ maximalIdeal V) ∧ ∀ ψ, (Q ψ).IsPrime :=
    ⟨fun ψ => (maximalIdeal V).comap (σ ψ), fun _ _ => Iff.rfl, fun _ => inferInstance⟩
  have hcond : ∀ ψ : E →+* k, (∀ x : 𝓞 E, x ∈ P ↔
      ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V)) ↔ Q ψ = P := by
    intro ψ
    have key : ∀ x : 𝓞 E, ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V) ↔ x ∈ Q ψ := by
      intro x
      rw [hQ, ← hσ]
      constructor
      · rintro ⟨y, hy, h⟩
        exact inj h ▸ hy
      · intro h
        exact ⟨_, h, rfl⟩
    simp only [key]
    rw [eq_comm, SetLike.ext_iff]
  by_cases hex : ∃ ψ0 : E →+* k, Q ψ0 = P
  swap
  · refine ⟨0, Fin.elim0, Fin.elim0, fun ψ => ?_⟩
    rw [if_neg (fun h => hex ⟨ψ, (hcond ψ).mp h⟩)]
    simp
  obtain ⟨ψ0, hψ0⟩ := hex
  haveI : CharZero k := ⟨fun a b h => by
    rw [← map_natCast ψ0, ← map_natCast ψ0 b] at h
    exact Nat.cast_injective (ψ0.injective h)⟩
  have hPmax : P.IsMaximal := hP.isMaximal hP0

  set N : ℕ := Ideal.absNorm P with hN
  have hNP : (N : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : (N : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero, hN]
    exact fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNQ : ∀ ψ, (N : 𝓞 E) ∈ Q ψ := by
    intro ψ
    have h0 : (N : 𝓞 E) ∈ Q ψ0 := hψ0 ▸ hNP
    rw [hQ, map_natCast] at h0 ⊢
    exact h0
  have hc : ∀ ψ, ∃ c : 𝓞 E, c ∉ P ∧ (Q ψ ≠ P → c ∈ Q ψ) := by
    intro ψ
    by_cases h : Q ψ = P
    · exact ⟨1, fun h1 => hPmax.ne_top ((Ideal.eq_top_iff_one _).2 h1), fun h' => (h' h).elim⟩
    · have hQ0 : Q ψ ≠ ⊥ := fun h0 => hN0 (by simpa [h0] using hNQ ψ)
      have hQmax : (Q ψ).IsMaximal := (hQp ψ).isMaximal hQ0
      have hnle : ¬ Q ψ ≤ P := fun hle => h (hQmax.eq_of_le hPmax.ne_top hle)
      obtain ⟨c, hcQ, hcP⟩ := SetLike.not_le_iff_exists.mp hnle
      exact ⟨c, hcP, fun _ => hcQ⟩
  choose c hcP hcQ using hc
  have hprod : ∏ ψ, c ψ ∉ P := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨ψ, -, h⟩
    exact hcP ψ h
  obtain ⟨y, i, hi, hyi⟩ := hPmax.exists_inv hprod
  set b : 𝓞 E := y * ∏ ψ, c ψ with hb
  have hb1 : ∀ ψ, Q ψ = P → σ ψ b - 1 ∈ maximalIdeal V := by
    intro ψ h
    have : b - 1 ∈ Q ψ := by
      rw [h]
      have : b - 1 = -i := by rw [hb, ← hyi]; ring
      rw [this]
      exact P.neg_mem hi
    rw [hQ, map_sub, map_one] at this
    exact this
  have hb0 : ∀ ψ, Q ψ ≠ P → σ ψ b ∈ maximalIdeal V := by
    intro ψ h
    rw [← hQ]
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ ψ)
    rw [hb, hr]
    exact (Q ψ).mul_mem_left _ ((Q ψ).mul_mem_right _ (hcQ ψ h))

  set p0 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ ≠ P), (X - C (σ ψ b)) with hp0
  set p1 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ = P), (X - C (σ ψ b)) with hp1
  have hcop : IsCoprime p0 p1 := by
    rw [hp0, hp1]
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ hφ
    apply isCoprime_X_sub_C_of_isUnit_sub
    have h0 := hb0 ψ hψ
    have h1 := hb1 φ hφ
    have hnot : σ ψ b - σ φ b ∉ maximalIdeal V := by
      intro h
      apply (maximalIdeal.isMaximal V).ne_top
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (sub_mem h0 h) h1
      simpa using this
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hnot
  obtain ⟨u, v, huv⟩ := hcop
  set g : V[X] := u * p0 with hg
  refine ⟨g.natDegree + 1, fun j => b ^ (j : ℕ), fun j => g.coeff j, fun ψ => ?_⟩
  have hsum : ∑ j : Fin (g.natDegree + 1), algebraMap V k (g.coeff j) * ψ ((b ^ (j : ℕ) : 𝓞 E) : E)
      = algebraMap V k (g.eval (σ ψ b)) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_self _), map_sum,
      ← Fin.sum_univ_eq_sum_range (fun j => algebraMap V k (g.coeff j * σ ψ b ^ j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hσ]
    simp only [map_pow, map_mul]
  rw [hsum]
  by_cases h : Q ψ = P
  · rw [if_pos ((hcond ψ).mpr h)]
    have hp1z : p1.eval (σ ψ b) = 0 := by
      rw [hp1, eval_prod]
      exact Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)
    have : g.eval (σ ψ b) = 1 := by
      have h2 : (u * p0 + v * p1).eval (σ ψ b) = 1 := by rw [huv, eval_one]
      rw [eval_add, show (v * p1).eval (σ ψ b) = 0 by rw [eval_mul, hp1z, mul_zero],
        add_zero] at h2
      exact h2
    rw [this, map_one]
  · rw [if_neg (fun h' => h ((hcond ψ).mp h'))]
    have hp0z : p0.eval (σ ψ b) = 0 := by
      rw [hp0, eval_prod]
      exact Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)
    rw [hg, eval_mul, hp0z, mul_zero, map_zero]

end GlobalTheory.PlaceInt
