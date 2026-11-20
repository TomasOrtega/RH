import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogenyExists

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

universe u

section Defs

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) (p : ℕ)

def IsSupersingular : Prop :=
  ∀ P : E.toAffine.Point, p • P = 0 → P = 0

def IsOrdinary : Prop :=
  ¬ IsSupersingular E p

end Defs

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (E : WeierstrassCurve F)
  [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in

/- English proof (translation)
The claim follows from `AddSubgroup.torsionBy.nsmul_iff`.
-/
theorem mem_torsionBy_natCast_iff (n : ℕ) (P : E.toAffine.Point) :
    P ∈ AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) ↔ n • P = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

omit hp [CharP F p] in

/- English proof (translation)
Establish `hn' : (n : ℤ) ≠ 0` using `by exact_mod_cast hn`. Use `Finite.of_injective (fun P : AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) => (⟨P.1, ?_⟩ : (mulIsogeny E n hn').pointHom.ker)) ?_` and prove the remaining obligations. Rewrite using `[AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, natCast_zsmul]`. Conclude with `(mem_torsionBy_natCast_iff E n P.1).mp P.2`. Introduce `P Q h`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun x : (mulIsogeny E n hn').pointHom.ker => (x : E.toAffine.Point)) h`.
-/
theorem finite_torsionBy_natCast {n : ℕ} (hn : n ≠ 0) :
    Finite (AddSubgroup.torsionBy E.toAffine.Point (n : ℤ)) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine Finite.of_injective (fun P : AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) =>
    (⟨P.1, ?_⟩ : (mulIsogeny E n hn').pointHom.ker)) ?_
  · rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, natCast_zsmul]
    exact (mem_torsionBy_natCast_iff E n P.1).mp P.2
  · intro P Q h
    apply Subtype.ext
    exact congrArg (fun x : (mulIsogeny E n hn').pointHom.ker => (x : E.toAffine.Point)) h

omit [IsAlgClosed F] in

/- English proof (translation)
Establish `h` using `card_torsion_lt E p`. Rewrite `h` using `[← Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)]`. Then use the resulting hypothesis.
-/
theorem card_torsionBy_prime_lt :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) < p ^ 2 := by
  have h := card_torsion_lt E p
  rwa [← Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)] at h

/- English proof (translation)
Use `finite_torsionBy_natCast E hp.out.ne_zero` as an intermediate fact. Set `_ : Module (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ))` to `AddSubgroup.torsionBy.zmodModule`. Establish `_ : Fintype (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ))` using `Fintype.ofFinite _`. Establish `hc : Fintype.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) = p ^ Module.finrank (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ))`. Rewrite using `[Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]`.

Establish `hlt` using `card_torsionBy_prime_lt E p`. Rewrite `hlt`, the goal using `[Nat.card_eq_fintype_card, hc]`. Establish `hd : Module.finrank (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) < 2` using `(Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt`. Use `interval_cases Module.finrank (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ))`. Use `left`.

Both sides reduce to the same expression. Use `right`. Rewrite using `[pow_one]`.
-/
theorem card_torsionBy_prime_eq_one_or_eq :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) = 1 ∨
      Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) = p := by
  have := finite_torsionBy_natCast E hp.out.ne_zero
  let _ : Module (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) :=
    AddSubgroup.torsionBy.zmodModule
  have _ : Fintype (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) := Fintype.ofFinite _
  have hc : Fintype.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) =
      p ^ Module.finrank (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hlt := card_torsionBy_prime_lt E p
  rw [Nat.card_eq_fintype_card, hc] at hlt ⊢
  have hd : Module.finrank (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ)) < 2 :=
    (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt
  interval_cases Module.finrank (ZMod p) (AddSubgroup.torsionBy E.toAffine.Point (p : ℕ))
  · left; rfl
  · right; rw [pow_one]

omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[eq_bot_iff]`. Introduce `P hP`. Conclude with `(AddSubgroup.mem_bot).mpr (h P ((mem_torsionBy_natCast_iff E p P).mp hP))`.

Introduce `h P hP`. Establish `: P ∈ AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)` using `(mem_torsionBy_natCast_iff E p P).mpr hP`. Rewrite `this` using `[h]`. Conclude with `(AddSubgroup.mem_bot).mp this`.
-/
theorem isSupersingular_iff_torsionBy_eq_bot :
    IsSupersingular E p ↔ AddSubgroup.torsionBy E.toAffine.Point (p : ℤ) = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro P hP
    exact (AddSubgroup.mem_bot).mpr (h P ((mem_torsionBy_natCast_iff E p P).mp hP))
  · intro h P hP
    have : P ∈ AddSubgroup.torsionBy E.toAffine.Point (p : ℤ) := (mem_torsionBy_natCast_iff E p P).mpr hP
    rw [h] at this
    exact (AddSubgroup.mem_bot).mp this

omit [CharP F p] in

/- English proof (translation)
Rewrite using `[isSupersingular_iff_torsionBy_eq_bot]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Conclude with `AddSubgroup.card_bot`.

Introduce `h`. Use `finite_torsionBy_natCast E hp.out.ne_zero` as an intermediate fact. Conclude with `(AddSubgroup.eq_bot_iff_card _).mpr h`.
-/
theorem isSupersingular_iff_card_torsionBy_eq_one :
    IsSupersingular E p ↔ Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) = 1 := by
  rw [isSupersingular_iff_torsionBy_eq_bot]
  constructor
  · intro h; rw [h]; exact AddSubgroup.card_bot
  · intro h
    have := finite_torsionBy_natCast E hp.out.ne_zero
    exact (AddSubgroup.eq_bot_iff_card _).mpr h

/- English proof (translation)
The claim follows from `(card_torsionBy_prime_eq_one_or_eq E p).resolve_left (fun h1 => h ((isSupersingular_iff_card_torsionBy_eq_one E p).mpr h1))`.
-/
theorem IsOrdinary.card_torsionBy_prime (h : IsOrdinary E p) :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) = p :=
  (card_torsionBy_prime_eq_one_or_eq E p).resolve_left
    (fun h1 => h ((isSupersingular_iff_card_torsionBy_eq_one E p).mpr h1))

omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in

/- English proof (translation)
Establish `key : ∀ (r : ℕ) (P : E.toAffine.Point), p ^ r • P = 0 → P = 0`. Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => intro P hP`. Simplify using `using hP`.

Consider the case `succ r ih`. Introduce `P hP`. Conclude with `h P (ih (p • P) (by rw [smul_smul, ← pow_succ]; exact hP))`. Rewrite using `[eq_bot_iff]`. Introduce `P hP`.

Conclude with `(AddSubgroup.mem_bot).mpr (key r P ((mem_torsionBy_natCast_iff E _ P).mp hP))`.
-/
theorem IsSupersingular.torsionBy_pow_eq_bot (h : IsSupersingular E p) (r : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) = ⊥ := by
  have key : ∀ (r : ℕ) (P : E.toAffine.Point), p ^ r • P = 0 → P = 0 := by
    intro r
    induction r with
    | zero => intro P hP; simpa using hP
    | succ r ih =>
      intro P hP
      exact h P (ih (p • P) (by rw [smul_smul, ← pow_succ]; exact hP))
  rw [eq_bot_iff]
  intro P hP
  exact (AddSubgroup.mem_bot).mpr (key r P ((mem_torsionBy_natCast_iff E _ P).mp hP))

noncomputable def torsionPowSucc (r : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point ((p ^ (r + 1) : ℕ) : ℤ) →+
      AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) where
  toFun Q := ⟨p • Q.1, by
    rw [mem_torsionBy_natCast_iff, smul_smul, ← pow_succ]
    exact (mem_torsionBy_natCast_iff E _ _).mp Q.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [smul_add]

omit [CharP F p] in
/- English proof (translation)
Introduce `R`. Establish `hp0 : ((p : ℕ) : ℤ) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Take `⟨Q, hQ⟩` from `exists_zsmul_eq E hp0 R.1`. Rewrite `hQ` using `[natCast_zsmul]`. Use `⟨⟨Q, ?_⟩, Subtype.ext hQ⟩` and prove the remaining obligations.

Rewrite using `[mem_torsionBy_natCast_iff, pow_succ, ← smul_smul, hQ]`. Conclude with `(mem_torsionBy_natCast_iff E _ _).mp R.2`.
-/
theorem torsionPowSucc_surjective (r : ℕ) : Function.Surjective (torsionPowSucc E p r) := by
  intro R
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨Q, hQ⟩ := exists_zsmul_eq E hp0 R.1
  rw [natCast_zsmul] at hQ
  refine ⟨⟨Q, ?_⟩, Subtype.ext hQ⟩
  rw [mem_torsionBy_natCast_iff, pow_succ, ← smul_smul, hQ]
  exact (mem_torsionBy_natCast_iff E _ _).mp R.2

omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in
/- English proof (translation)
Use `Nat.card_congr { toFun := fun Q => ⟨Q.1.1, (mem_torsionBy_natCast_iff E p _).mpr (congrArg Subtype.val ((AddMonoidHom.mem_ker).mp Q.2))⟩ invFun := fun P => ⟨⟨P.1, ?_⟩, ?_⟩ left_inv := fun Q => rfl right_inv := fun P => rfl }` and prove the remaining obligations. Rewrite using `[mem_torsionBy_natCast_iff, pow_succ, ← smul_smul, (mem_torsionBy_natCast_iff E p _).mp P.2, smul_zero]`. Rewrite using `[AddMonoidHom.mem_ker]`. Conclude with `Subtype.ext ((mem_torsionBy_natCast_iff E p _).mp P.2)`.
-/
theorem card_ker_torsionPowSucc (r : ℕ) :
    Nat.card (torsionPowSucc E p r).ker = Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) := by
  refine Nat.card_congr
    { toFun := fun Q => ⟨Q.1.1, (mem_torsionBy_natCast_iff E p _).mpr
        (congrArg Subtype.val ((AddMonoidHom.mem_ker).mp Q.2))⟩
      invFun := fun P => ⟨⟨P.1, ?_⟩, ?_⟩
      left_inv := fun Q => rfl
      right_inv := fun P => rfl }
  · rw [mem_torsionBy_natCast_iff, pow_succ, ← smul_smul,
      (mem_torsionBy_natCast_iff E p _).mp P.2, smul_zero]
  · rw [AddMonoidHom.mem_ker]
    exact Subtype.ext ((mem_torsionBy_natCast_iff E p _).mp P.2)

omit [CharP F p] in

/- English proof (translation)
Establish `h` using `(torsionPowSucc E p r).ker.card_mul_index`. Rewrite `h` using `[AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (torsionPowSucc_surjective E p r), AddSubgroup.card_top, card_ker_torsionPowSucc]`. Conclude with `h.symm`.
-/
theorem card_torsionBy_pow_succ (r : ℕ) :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point ((p ^ (r + 1) : ℕ) : ℤ)) =
      Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) *
        Nat.card (AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ)) := by
  have h := (torsionPowSucc E p r).ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (torsionPowSucc_surjective E p r),
    AddSubgroup.card_top, card_ker_torsionPowSucc] at h
  exact h.symm

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Establish `: AddSubgroup.torsionBy E.toAffine.Point ((p ^ 0 : ℕ) : ℤ) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `P hP`.

Rewrite `hP` using `[mem_torsionBy_natCast_iff, pow_zero, one_smul]`. Conclude with `(AddSubgroup.mem_bot).mpr hP`. Rewrite using `[this, AddSubgroup.card_bot, pow_zero]`. Consider the case `succ r ih => rw [card_torsionBy_pow_succ, ih, h.card_torsionBy_prime, pow_succ, mul_comm]`.
-/
theorem IsOrdinary.card_torsionBy_pow (h : IsOrdinary E p) (r : ℕ) :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ)) = p ^ r := by
  induction r with
  | zero =>
    have : AddSubgroup.torsionBy E.toAffine.Point ((p ^ 0 : ℕ) : ℤ) = ⊥ := by
      rw [eq_bot_iff]
      intro P hP
      rw [mem_torsionBy_natCast_iff, pow_zero, one_smul] at hP
      exact (AddSubgroup.mem_bot).mpr hP
    rw [this, AddSubgroup.card_bot, pow_zero]
  | succ r ih => rw [card_torsionBy_pow_succ, ih, h.card_torsionBy_prime, pow_succ, mul_comm]

omit [CharP F p] in

/- English proof (translation)
Consider the cases of `r with`. Consider the case `zero => exact ⟨0, smul_zero _, by rw [addOrderOf_zero, pow_zero]⟩`. Consider the case `succ s`. Establish `h' : ¬ IsSupersingular E p` using `h`. Simplify using `only [IsSupersingular, not_forall] at h'`.

Take `⟨P, hP, hP0⟩` from `h'`. Establish `hn : ((p ^ s : ℕ) : ℤ) ≠ 0` using `by exact_mod_cast pow_ne_zero s hp.out.ne_zero`. Take `⟨Q, hQ⟩` from `exists_zsmul_eq E hn P`. Rewrite `hQ` using `[natCast_zsmul]`. Establish `hfin : p ^ (s + 1) • Q = 0` using `by rw [pow_succ', ← smul_smul, hQ, hP]`.

Conclude with `⟨Q, hfin, addOrderOf_eq_prime_pow (by rw [hQ]; exact hP0) hfin⟩`.
-/
theorem IsOrdinary.exists_addOrderOf_eq (h : IsOrdinary E p) (r : ℕ) :
    ∃ Q : E.toAffine.Point, p ^ r • Q = 0 ∧ addOrderOf Q = p ^ r := by
  cases r with
  | zero => exact ⟨0, smul_zero _, by rw [addOrderOf_zero, pow_zero]⟩
  | succ s =>
    have h' : ¬ IsSupersingular E p := h
    simp only [IsSupersingular, not_forall] at h'
    obtain ⟨P, hP, hP0⟩ := h'
    have hn : ((p ^ s : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero s hp.out.ne_zero
    obtain ⟨Q, hQ⟩ := exists_zsmul_eq E hn P
    rw [natCast_zsmul] at hQ
    have hfin : p ^ (s + 1) • Q = 0 := by rw [pow_succ', ← smul_smul, hQ, hP]
    exact ⟨Q, hfin, addOrderOf_eq_prime_pow (by rw [hQ]; exact hP0) hfin⟩

/- English proof (translation)
Use `finite_torsionBy_natCast E (pow_ne_zero r hp.out.ne_zero)` as an intermediate fact. Take `⟨Q, hQ, hord⟩` from `h.exists_addOrderOf_eq E p r`. Use `set G := AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ)`. Establish `hcard : Nat.card G = p ^ r` using `h.card_torsionBy_pow E p r`. Set `x : G` to `⟨Q, (mem_torsionBy_natCast_iff E _ Q).mpr hQ⟩`.

Establish `hx : addOrderOf x = Nat.card G`. Rewrite using `[hcard, ← hord]`. Conclude with `AddSubgroup.addOrderOf_mk Q _`. Establish `hcyc : IsAddCyclic G` using `isAddCyclic_of_addOrderOf_eq_card x hx`. Conclude with `⟨(zmodAddCyclicAddEquiv hcyc).symm.trans (ZMod.ringEquivCongr hcard).toAddEquiv⟩`.
-/
theorem IsOrdinary.nonempty_torsionBy_pow_addEquiv (h : IsOrdinary E p) (r : ℕ) :
    Nonempty (AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) ≃+ ZMod (p ^ r)) := by
  have := finite_torsionBy_natCast E (pow_ne_zero r hp.out.ne_zero)
  obtain ⟨Q, hQ, hord⟩ := h.exists_addOrderOf_eq E p r
  set G := AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ)
  have hcard : Nat.card G = p ^ r := h.card_torsionBy_pow E p r
  let x : G := ⟨Q, (mem_torsionBy_natCast_iff E _ Q).mpr hQ⟩
  have hx : addOrderOf x = Nat.card G := by
    rw [hcard, ← hord]
    exact AddSubgroup.addOrderOf_mk Q _
  have hcyc : IsAddCyclic G := isAddCyclic_of_addOrderOf_eq_card x hx
  exact ⟨(zmodAddCyclicAddEquiv hcyc).symm.trans (ZMod.ringEquivCongr hcard).toAddEquiv⟩

/- English proof (translation)
Distinguish the cases in `h : IsSupersingular E p`. Conclude with `Or.inl (h.torsionBy_pow_eq_bot E p r)`. Conclude with `Or.inr (IsOrdinary.nonempty_torsionBy_pow_addEquiv E p h r)`.
-/
theorem torsionBy_pow_eq_bot_or_nonempty_addEquiv (r : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) = ⊥ ∨
      Nonempty (AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) ≃+ ZMod (p ^ r)) := by
  by_cases h : IsSupersingular E p
  · exact Or.inl (h.torsionBy_pow_eq_bot E p r)
  · exact Or.inr (IsOrdinary.nonempty_torsionBy_pow_addEquiv E p h r)

omit hp [CharP F p] in

/- English proof (translation)
Use `Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)` and prove the remaining obligations. Rewrite using `[AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, mem_torsionBy_natCast_iff, natCast_zsmul]`.
-/
theorem card_ker_mulIsogeny_natCast (hn : (p : ℤ) ≠ 0) :
    Nat.card (mulIsogeny E p hn).pointHom.ker =
      Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny,
    mem_torsionBy_natCast_iff, natCast_zsmul]

omit [CharP F p] in

/- English proof (translation)
Rewrite using `[card_ker_mulIsogeny_natCast, isSupersingular_iff_card_torsionBy_eq_one]`.
-/
theorem isSupersingular_iff_card_ker_mulIsogeny (hn : (p : ℤ) ≠ 0) :
    IsSupersingular E p ↔ Nat.card (mulIsogeny E p hn).pointHom.ker = 1 := by
  rw [card_ker_mulIsogeny_natCast, isSupersingular_iff_card_torsionBy_eq_one]

omit [CharP F p] in

/- English proof (translation)
Use `φ.finiteDimensional` as an intermediate fact. Establish `hmul` using `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic φ.comap.fieldRange φ.fixedKer E.toAffine.FunctionField`. Rewrite `hmul` using `[φ.finSepDegree_fixedKer, one_mul]`. Conclude with `le_antisymm φ.finSepDegree_le_card_ker (hmul ▸ φ.card_ker_le_finSepDegree_fixedKer)`.
-/
private theorem finSepDegree_eq_card_ker' {E' : WeierstrassCurve F} [E'.IsElliptic]
    (φ : Isogeny E E') :
    Field.finSepDegree φ.comap.fieldRange E.toAffine.FunctionField = Nat.card φ.pointHom.ker := by
  have := φ.finiteDimensional
  have hmul := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic φ.comap.fieldRange φ.fixedKer
    E.toAffine.FunctionField
  rw [φ.finSepDegree_fixedKer, one_mul] at hmul
  exact le_antisymm φ.finSepDegree_le_card_ker (hmul ▸ φ.card_ker_le_finSepDegree_fixedKer)

omit [CharP F p] in

/- English proof (translation)
Rewrite using `[isPurelyInseparable_iff_finSepDegree_eq_one, finSepDegree_eq_card_ker', isSupersingular_iff_card_ker_mulIsogeny]`.
-/
theorem isSupersingular_iff_isPurelyInseparable (hn : (p : ℤ) ≠ 0) :
    IsSupersingular E p ↔
      IsPurelyInseparable (mulIsogeny E p hn).comap.fieldRange E.toAffine.FunctionField := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, finSepDegree_eq_card_ker',
    isSupersingular_iff_card_ker_mulIsogeny]

omit [CharP F p] in

/- English proof (translation)
Establish `hd` using `(mulIsogeny E p hn).degree_eq_insepDeg_mul`. Rewrite `hd` using `[degree_mulIsogeny, Int.natAbs_natCast]`. Rewrite using `[isSupersingular_iff_card_ker_mulIsogeny E p hn]`. Establish `hp2 : 0 < p ^ 2` using `pow_pos hp.out.pos 2`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `hd` using `[h, mul_one]`. Conclude with `hd.symm`. Introduce `h`. Rewrite `hd` using `[h]`.

Conclude with `(Nat.mul_eq_left hp2.ne').mp hd.symm`.
-/
theorem isSupersingular_iff_insepDeg_mulIsogeny (hn : (p : ℤ) ≠ 0) :
    IsSupersingular E p ↔ (mulIsogeny E p hn).insepDeg = p ^ 2 := by
  have hd := (mulIsogeny E p hn).degree_eq_insepDeg_mul
  rw [degree_mulIsogeny, Int.natAbs_natCast] at hd
  rw [isSupersingular_iff_card_ker_mulIsogeny E p hn]
  have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  constructor
  · intro h; rw [h, mul_one] at hd; exact hd.symm
  · intro h
    rw [h] at hd
    exact (Nat.mul_eq_left hp2.ne').mp hd.symm

/- English proof (translation)
Establish `hd` using `(mulIsogeny E p hn).degree_eq_insepDeg_mul`. Rewrite `hd` using `[degree_mulIsogeny, Int.natAbs_natCast, card_ker_mulIsogeny_natCast, h.card_torsionBy_prime, sq]`. Conclude with `(Nat.eq_of_mul_eq_mul_right hp.out.pos hd).symm`.
-/
theorem IsOrdinary.insepDeg_mulIsogeny (h : IsOrdinary E p) (hn : (p : ℤ) ≠ 0) :
    (mulIsogeny E p hn).insepDeg = p := by
  have hd := (mulIsogeny E p hn).degree_eq_insepDeg_mul
  rw [degree_mulIsogeny, Int.natAbs_natCast, card_ker_mulIsogeny_natCast,
    h.card_torsionBy_prime, sq] at hd
  exact (Nat.eq_of_mul_eq_mul_right hp.out.pos hd).symm

end GroundTheory.Arith.Abelian
