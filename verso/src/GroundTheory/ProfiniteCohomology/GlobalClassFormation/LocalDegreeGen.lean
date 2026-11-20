import Mathlib
import GroundTheory.GlobalFields.SplittingFromInequality.Decomposition
import GroundTheory.GlobalFields.FirstInequality
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain Module

open scoped GroundTheory.Global.SemiLocal Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)] [IsGalois K.1 E.1]

variable (E) in

def localDegree (v : HeightOneSpectrum (𝓞 K.1)) : ℕ :=
  v.asIdeal.ramificationIdxIn (𝓞 E.1) * v.asIdeal.inertiaDegIn (𝓞 E.1)

/- English proof (translation)
Rewrite using `[SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg, localDegree, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal Gal(E.1/K.1), Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal Gal(E.1/K.1)]`.
-/
theorem finrank_eq_localDegree (v : HeightOneSpectrum (𝓞 K.1)) (w : SemiLocal.PlacesOver E.1 v) :
    finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) = localDegree E v := by
  rw [SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg, localDegree,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal Gal(E.1/K.1),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal Gal(E.1/K.1)]

/- English proof (translation)
The claim follows from `Ideal.card_stabilizer_eq (G := Gal(E.1/K.1)) v.asIdeal w.1.asIdeal`.
-/
theorem card_stabilizer_eq_localDegree (v : HeightOneSpectrum (𝓞 K.1)) (w : SemiLocal.PlacesOver E.1 v) :
    Nat.card (MulAction.stabilizer Gal(E.1/K.1) w.1.asIdeal) = localDegree E v :=
  Ideal.card_stabilizer_eq (G := Gal(E.1/K.1)) v.asIdeal w.1.asIdeal

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩`.
-/
theorem nonempty_heightOneSpectrum (F : Type) [Field F] [NumberField F] :
    Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

variable (E) in

/- English proof (translation)
Use `set n := finrank K.1 E.1 with hn`. Establish `hcard : Nat.card Gal(E.1/K.1) = n` using `IsGalois.card_aut_eq_finrank K.1 E.1`. Establish `hn0 : n ≠ 0` using `Module.finrank_pos.ne'`. Set `dl : HeightOneSpectrum (𝓞 E.1) → ℕ` to `fun w => localDegree E (AdeleBaseChange.below K.1 w)`. Establish `hdl : ∀ w, Nat.card (MulAction.stabilizer Gal(E.1/K.1) w.asIdeal) = dl w` using `fun w => card_stabilizer_eq_localDegree (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩`.

Establish `hdvd : ∀ w, dl w ∣ n` using `fun w => by`. Rewrite using `[← hdl w, ← hcard]`. Conclude with `Subgroup.card_subgroup_dvd_card _`. Establish `hdlpos : ∀ w, 0 < dl w` using `fun w => Nat.pos_of_ne_zero fun h => by`. Use `hdvd w` as an intermediate fact.

Rewrite `this` using `[h, zero_dvd_iff]`. Conclude with `hn0 this`. Set `A : Finset ℕ` to `n.divisors.filter fun a => ∃ w : HeightOneSpectrum (𝓞 E.1), n / dl w = a`. Establish `hA : ∀ w, n / dl w ∈ A` using `fun w => Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (hdvd w), hn0⟩, w, rfl⟩`. Use `choose pick hpick using fun a (ha : a ∈ A) => (Finset.mem_filter.1 ha).2`.

Take `⟨w₀⟩` from `nonempty_heightOneSpectrum E.1`. Establish `hdivpos : ∀ w, 0 < n / dl w` using `fun w => Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (hdvd w)) (hdlpos w)`. Establish `hg : A.gcd id = 1` using `by set g := A.gcd id with hgdef`. Establish `hg0 : g ≠ 0`. Introduce `h0`.

Use `Finset.gcd_dvd (f := id) (hA w₀)` as an intermediate fact. Rewrite `this` using `[← hgdef, h0, zero_dvd_iff]`. Conclude with `(hdivpos w₀).ne' this`. Set `` to `IsCyclic.commGroup (α := Gal(E.1/K.1))`. Set `H : Subgroup Gal(E.1/K.1)` to `(powMonoidHom (n / g) : Gal(E.1/K.1) →* Gal(E.1/K.1)).ker`.

Establish `hle : ∀ w : HeightOneSpectrum (𝓞 E.1), MulAction.stabilizer Gal(E.1/K.1) w.asIdeal ≤ H`. Introduce `w x hx`. Take `⟨k, hk⟩ : g ∣ n / dl w` from `Finset.gcd_dvd (f := id) (hA w)`. Establish `hdw : dl w ∣ n / g`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `h1 : n = dl w * (g * k)` using `by rw [← hk, Nat.mul_div_cancel' (hdvd w)]`. Rewrite using `[h1, mul_comm g k, ← mul_assoc, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hg0)]`. Take `⟨j, hj⟩` from `hdw`. Express the relevant statement in the definitionally equal form `x ^ (n / g) = 1`. Establish `hx1 : x ^ dl w = 1`.

Rewrite using `[← hdl w]`. Conclude with `congrArg Subtype.val (pow_card_eq_one' (G := MulAction.stabilizer Gal(E.1/K.1) w.asIdeal) (x := ⟨x, hx⟩))`. Rewrite using `[hj, pow_mul, hx1, one_pow]`. Establish `htop` using `FirstInequality.closure_stabilizer_eq_top (K := K.1) (L := E.1) firstInequality (T := ∅) Set.finite_empty`. Establish `hH : (⊤ : Subgroup Gal(E.1/K.1)) ≤ H`.

Rewrite using `[← htop, Subgroup.closure_le]`. Introduce `x hx`. Take `⟨w, _, hxw⟩` from `Set.mem_iUnion₂.1 hx`. Conclude with `hle w hxw`. Take `⟨γ, hγ⟩` from `IsCyclic.exists_generator (α := Gal(E.1/K.1))`.

Establish `hord : orderOf γ = n`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]`. Establish `hγH : γ ^ (n / g) = 1` using `hH (Subgroup.mem_top γ)`. Establish `hdvd' : n ∣ n / g`. Use `orderOf_dvd_of_pow_eq_one hγH` as an intermediate fact.

Rewrite `this` using `[hord]`. Then use the resulting hypothesis. Establish `hpos : 0 < n / g` using `Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ((Finset.gcd_dvd (f := id) (hA w₀)).trans (Nat.div_dvd_of_dvd (hdvd w₀)))) (Nat.pos_of_ne_zero hg0)`. Establish `hle' : n ≤ n / g` using `Nat.le_of_dvd hpos hdvd'`. Assume the negation of the conclusion as `hgt`. Establish `hgt' : 1 < g` using `by omega`.

Use `Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hgt'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc⟩` from `Finset.gcd_eq_sum_mul A (fun a => (a : ℤ))`. Establish `hgZ : A.gcd (fun a => (a : ℤ)) = 1`. Establish `h1 : (A.gcd fun a => (a : ℤ)).natAbs ∣ A.gcd id` using `Finset.dvd_gcd fun a ha => by`.

Use `Int.natAbs_dvd_natAbs.2 (Finset.gcd_dvd (s := A) (f := fun a : ℕ => (a : ℤ)) ha)` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[hg, Nat.dvd_one]`. Establish `h2 : 0 ≤ A.gcd fun a => (a : ℤ)` using `Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := A) (f := fun a => (a : ℤ)))`. Rewrite using `[← Int.natAbs_of_nonneg h2, h1, Nat.cast_one]`.

Set `f : {a // a ∈ A} → HeightOneSpectrum (𝓞 K.1)` to `fun a => AdeleBaseChange.below K.1 (pick a.1 a.2)`. Establish `hf : ∀ a : {a // a ∈ A}, n / localDegree E (f a) = a.1` using `fun a => hpick a.1 a.2`. Establish `hfinj : Set.InjOn f (A.attach : Set {a // a ∈ A})` using `fun a _ b _ hab => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hf a, ← hf b, hab]`.

Use `⟨A.attach.image f, fun v => c (n / localDegree E v), fun v hv => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, _, rfl⟩` from `Finset.mem_image.1 hv`. Conclude with `hdvd (pick a.1 a.2)`. Rewrite using `[Finset.sum_image hfinj]`. Repeatedly rewrite using `[hf]`.

Rewrite using `[Finset.sum_attach A (fun a => c a * (a : ℤ)), ← hgZ, hc]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.
-/
theorem exists_sum_mul_div_localDegree_eq_one [IsCyclic Gal(E.1/K.1)] :
    ∃ (s : Finset (HeightOneSpectrum (𝓞 K.1))) (c : HeightOneSpectrum (𝓞 K.1) → ℤ),
      (∀ v ∈ s, localDegree E v ∣ finrank K.1 E.1) ∧
        ∑ v ∈ s, c v * ((finrank K.1 E.1 / localDegree E v : ℕ) : ℤ) = 1 := by
  classical
  set n := finrank K.1 E.1 with hn
  have hcard : Nat.card Gal(E.1/K.1) = n := IsGalois.card_aut_eq_finrank K.1 E.1
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  let dl : HeightOneSpectrum (𝓞 E.1) → ℕ := fun w => localDegree E (AdeleBaseChange.below K.1 w)
  have hdl : ∀ w, Nat.card (MulAction.stabilizer Gal(E.1/K.1) w.asIdeal) = dl w := fun w =>
    card_stabilizer_eq_localDegree (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩
  have hdvd : ∀ w, dl w ∣ n := fun w => by
    rw [← hdl w, ← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hdlpos : ∀ w, 0 < dl w := fun w => Nat.pos_of_ne_zero fun h => by
    have := hdvd w
    rw [h, zero_dvd_iff] at this
    exact hn0 this
  let A : Finset ℕ := n.divisors.filter fun a => ∃ w : HeightOneSpectrum (𝓞 E.1), n / dl w = a
  have hA : ∀ w, n / dl w ∈ A := fun w =>
    Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (hdvd w), hn0⟩, w, rfl⟩
  choose pick hpick using fun a (ha : a ∈ A) => (Finset.mem_filter.1 ha).2
  obtain ⟨w₀⟩ := nonempty_heightOneSpectrum E.1
  have hdivpos : ∀ w, 0 < n / dl w := fun w =>
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (hdvd w)) (hdlpos w)

  have hg : A.gcd id = 1 := by
    set g := A.gcd id with hgdef
    have hg0 : g ≠ 0 := by
      intro h0
      have := Finset.gcd_dvd (f := id) (hA w₀)
      rw [← hgdef, h0, zero_dvd_iff] at this
      exact (hdivpos w₀).ne' this
    let := IsCyclic.commGroup (α := Gal(E.1/K.1))
    let H : Subgroup Gal(E.1/K.1) := (powMonoidHom (n / g) : Gal(E.1/K.1) →* Gal(E.1/K.1)).ker
    have hle : ∀ w : HeightOneSpectrum (𝓞 E.1), MulAction.stabilizer Gal(E.1/K.1) w.asIdeal ≤ H := by
      intro w x hx
      obtain ⟨k, hk⟩ : g ∣ n / dl w := Finset.gcd_dvd (f := id) (hA w)
      have hdw : dl w ∣ n / g := by
        refine ⟨k, ?_⟩
        have h1 : n = dl w * (g * k) := by rw [← hk, Nat.mul_div_cancel' (hdvd w)]
        rw [h1, mul_comm g k, ← mul_assoc, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hg0)]
      obtain ⟨j, hj⟩ := hdw
      change x ^ (n / g) = 1
      have hx1 : x ^ dl w = 1 := by
        rw [← hdl w]
        exact congrArg Subtype.val
          (pow_card_eq_one' (G := MulAction.stabilizer Gal(E.1/K.1) w.asIdeal) (x := ⟨x, hx⟩))
      rw [hj, pow_mul, hx1, one_pow]
    have htop := FirstInequality.closure_stabilizer_eq_top (K := K.1) (L := E.1) firstInequality
      (T := ∅) Set.finite_empty
    have hH : (⊤ : Subgroup Gal(E.1/K.1)) ≤ H := by
      rw [← htop, Subgroup.closure_le]
      intro x hx
      obtain ⟨w, _, hxw⟩ := Set.mem_iUnion₂.1 hx
      exact hle w hxw
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Gal(E.1/K.1))
    have hord : orderOf γ = n := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]
    have hγH : γ ^ (n / g) = 1 := hH (Subgroup.mem_top γ)
    have hdvd' : n ∣ n / g := by
      have := orderOf_dvd_of_pow_eq_one hγH
      rwa [hord] at this
    have hpos : 0 < n / g := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
      ((Finset.gcd_dvd (f := id) (hA w₀)).trans (Nat.div_dvd_of_dvd (hdvd w₀)))) (Nat.pos_of_ne_zero hg0)
    have hle' : n ≤ n / g := Nat.le_of_dvd hpos hdvd'
    by_contra hgt
    have hgt' : 1 < g := by omega
    have := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hgt'
    omega

  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul A (fun a => (a : ℤ))
  have hgZ : A.gcd (fun a => (a : ℤ)) = 1 := by
    have h1 : (A.gcd fun a => (a : ℤ)).natAbs ∣ A.gcd id :=
      Finset.dvd_gcd fun a ha => by
        have := Int.natAbs_dvd_natAbs.2 (Finset.gcd_dvd (s := A) (f := fun a : ℕ => (a : ℤ)) ha)
        simpa using this
    rw [hg, Nat.dvd_one] at h1
    have h2 : 0 ≤ A.gcd fun a => (a : ℤ) :=
      Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := A) (f := fun a => (a : ℤ)))
    rw [← Int.natAbs_of_nonneg h2, h1, Nat.cast_one]
  let f : {a // a ∈ A} → HeightOneSpectrum (𝓞 K.1) := fun a => AdeleBaseChange.below K.1 (pick a.1 a.2)
  have hf : ∀ a : {a // a ∈ A}, n / localDegree E (f a) = a.1 := fun a => hpick a.1 a.2
  have hfinj : Set.InjOn f (A.attach : Set {a // a ∈ A}) := fun a _ b _ hab => by
    apply Subtype.ext
    rw [← hf a, ← hf b, hab]
  refine ⟨A.attach.image f, fun v => c (n / localDegree E v), fun v hv => ?_, ?_⟩
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hv
    exact hdvd (pick a.1 a.2)
  · rw [Finset.sum_image hfinj]
    simp_rw [hf]
    rw [Finset.sum_attach A (fun a => c a * (a : ℤ)), ← hgZ, hc]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end

end GroundTheory.ProfCoh
