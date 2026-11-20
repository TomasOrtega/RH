import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

/- English proof (translation)
Establish `g0 : ∀ x, γ x 0 = 1` using `fun x => by`. Establish `h` using `ar x 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel₀ (nz x 0) (h.symm.trans (mul_one _).symm)`. Establish `g0' : ∀ y, γ 0 y = 1` using `fun y => by`.

Establish `h` using `al 0 0 y`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel₀ (nz 0 y) (h.symm.trans (mul_one _).symm)`. Establish `hfinQ : Finite (↥Q ⧸ Q0.addSubgroupOf Q)` using `Nat.finite_of_card_ne_zero hfin`. Use `letI : Fintype (↥Q ⧸ Q0.addSubgroupOf Q) := Fintype.ofFinite _`.

Set `f : ↥P → ↥Q →+ Additive ℂˣ` to `fun p => { toFun := fun q => Additive.ofMul (Units.mk0 (γ p q) (nz p q)) map_zero' := by show _ = Additive.ofMul 1`. Use `congr 1`. Use `ext`. Simplify using `[g0]`. Use the proof step `map_add' := fun q1 q2 => by`.

Rewrite using `[← ofMul_mul]`. Use `congr 1`. Use `ext`. Simplify using `[ar] }`. Establish `hker : ∀ p, Q0.addSubgroupOf Q ≤ (f p).ker`.

Introduce `p q hq`. Rewrite `hq` using `[AddSubgroup.mem_addSubgroupOf]`. Rewrite using `[AddMonoidHom.mem_ker]`. Use `show Additive.ofMul _ = Additive.ofMul 1`. Use `congr 1`.

Use `ext`. Simplify using `[h1 p p.2 q q.2 hq]`. Set `χ : ↥P → AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ` to `fun p => { toFun := fun g => ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) g) : ℂˣ) : ℂ) map_zero_eq_one' := by simp map_add_eq_mul' := fun a b => by simp }`. Establish `hχ : ∀ p (q : ↥Q), χ p (q : ↥Q ⧸ Q0.addSubgroupOf Q) = γ p q`. Introduce `p q`.

Use `show ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) (q : ↥Q ⧸ Q0.addSubgroupOf Q)) : ℂˣ) : ℂ) = _`. Rewrite using `[QuotientAddGroup.lift_mk]`. Both sides reduce to the same expression. Set `Φ : ↥P →+ Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)` to `{ toFun := fun p => Additive.ofMul (χ p) map_zero' := by show _ = Additive.ofMul 1`. Use `congr 1`.

Use extensionality with `g`. Take `⟨q, rfl⟩` from `QuotientAddGroup.mk_surjective g`. Rewrite using `[hχ, AddChar.one_apply]`. Simplify using `[g0']`. Use the proof step `map_add' := fun p1 p2 => by`.

Rewrite using `[← ofMul_mul]`. Use `congr 1`. Use extensionality with `g`. Take `⟨q, rfl⟩` from `QuotientAddGroup.mk_surjective g`. Rewrite using `[AddChar.mul_apply, hχ, hχ, hχ]`.

Simplify using `[al] }`. Establish `hkerΦ : Φ.ker ≤ P0.addSubgroupOf P`. Introduce `p hp`. Rewrite `hp` using `[AddMonoidHom.mem_ker]`. Establish `hp' : χ p = 1` using `hp`.

Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Apply `h3 p p.2` to reduce the goal to its premises. Introduce `q hq`. Establish `h4` using `congrArg (fun c : AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ => c ((⟨q, hq⟩ : ↥Q) : ↥Q ⧸ Q0.addSubgroupOf Q)) hp'`. Rewrite `h4` using `[hχ, AddChar.one_apply]`.

Conclude with `h4`. Use `haveI : Finite (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) := inferInstanceAs (Finite (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ))`. Establish `hΦfin : Nat.card Φ.range ≤ Q0.relIndex Q`. Combine the equalities or inequalities in the displayed calculation. Use `haveI : Finite Φ.range := Finite.of_injective _ Subtype.val_injective`.

Establish `hkpos : Φ.ker.index ≠ 0`. Rewrite using `[AddSubgroup.index_ker]`. Conclude with `Nat.card_pos.ne'`. Establish `hdvd` using `AddSubgroup.index_dvd_of_le hkerΦ`. Establish `hne : (P0.addSubgroupOf P).index ≠ 0` using `fun h => hkpos (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))`.

Use `⟨hne, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem idxHalf_half {X : Type} [AddCommGroup X] (γ : X → X → ℂ)
    (al : ∀ x y z, γ (x + y) z = γ x z * γ y z) (ar : ∀ x y z, γ x (y + z) = γ x y * γ x z)
    (nz : ∀ x y, γ x y ≠ 0) (P P0 Q Q0 : AddSubgroup X)
    (h1 : ∀ p ∈ P, ∀ q ∈ Q, q ∈ Q0 → γ p q = 1)
    (h3 : ∀ p ∈ P, (∀ q ∈ Q, γ p q = 1) → p ∈ P0)
    (hfin : Q0.relIndex Q ≠ 0) :
    P0.relIndex P ≠ 0 ∧ P0.relIndex P ≤ Q0.relIndex Q := by
  classical
  have g0 : ∀ x, γ x 0 = 1 := fun x => by
    have h := ar x 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (nz x 0) (h.symm.trans (mul_one _).symm)
  have g0' : ∀ y, γ 0 y = 1 := fun y => by
    have h := al 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel₀ (nz 0 y) (h.symm.trans (mul_one _).symm)
  have hfinQ : Finite (↥Q ⧸ Q0.addSubgroupOf Q) := Nat.finite_of_card_ne_zero hfin
  letI : Fintype (↥Q ⧸ Q0.addSubgroupOf Q) := Fintype.ofFinite _
  let f : ↥P → ↥Q →+ Additive ℂˣ := fun p =>
    { toFun := fun q => Additive.ofMul (Units.mk0 (γ p q) (nz p q))
      map_zero' := by
        show _ = Additive.ofMul 1
        congr 1
        ext
        simp [g0]
      map_add' := fun q1 q2 => by
        rw [← ofMul_mul]
        congr 1
        ext
        simp [ar] }
  have hker : ∀ p, Q0.addSubgroupOf Q ≤ (f p).ker := by
    intro p q hq
    rw [AddSubgroup.mem_addSubgroupOf] at hq
    rw [AddMonoidHom.mem_ker]
    show Additive.ofMul _ = Additive.ofMul 1
    congr 1
    ext
    simp [h1 p p.2 q q.2 hq]
  let χ : ↥P → AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ := fun p =>
    { toFun := fun g => ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) g) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp }
  have hχ : ∀ p (q : ↥Q), χ p (q : ↥Q ⧸ Q0.addSubgroupOf Q) = γ p q := by
    intro p q
    show ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) (q : ↥Q ⧸ Q0.addSubgroupOf Q)) : ℂˣ) : ℂ) = _
    rw [QuotientAddGroup.lift_mk]
    rfl
  let Φ : ↥P →+ Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) :=
    { toFun := fun p => Additive.ofMul (χ p)
      map_zero' := by
        show _ = Additive.ofMul 1
        congr 1
        ext g
        obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective g
        rw [hχ, AddChar.one_apply]
        simp [g0']
      map_add' := fun p1 p2 => by
        rw [← ofMul_mul]
        congr 1
        ext g
        obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective g
        rw [AddChar.mul_apply, hχ, hχ, hχ]
        simp [al] }
  have hkerΦ : Φ.ker ≤ P0.addSubgroupOf P := by
    intro p hp
    rw [AddMonoidHom.mem_ker] at hp
    have hp' : χ p = 1 := hp
    rw [AddSubgroup.mem_addSubgroupOf]
    apply h3 p p.2
    intro q hq
    have h4 := congrArg (fun c : AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ => c ((⟨q, hq⟩ : ↥Q) : ↥Q ⧸ Q0.addSubgroupOf Q)) hp'
    rw [hχ, AddChar.one_apply] at h4
    exact h4
  haveI : Finite (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) :=
    inferInstanceAs (Finite (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ))
  have hΦfin : Nat.card Φ.range ≤ Q0.relIndex Q := by
    calc Nat.card Φ.range ≤ Nat.card (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) := rfl
      _ = Fintype.card (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) := Nat.card_eq_fintype_card
      _ ≤ Fintype.card (↥Q ⧸ Q0.addSubgroupOf Q) := AddChar.card_addChar_le _ _
      _ = Q0.relIndex Q := Nat.card_eq_fintype_card.symm
  haveI : Finite Φ.range := Finite.of_injective _ Subtype.val_injective
  have hkpos : Φ.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  have hdvd := AddSubgroup.index_dvd_of_le hkerΦ
  have hne : (P0.addSubgroupOf P).index ≠ 0 := fun h => hkpos (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  refine ⟨hne, ?_⟩
  calc P0.relIndex P = (P0.addSubgroupOf P).index := rfl
    _ ≤ Φ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hkpos) hdvd
    _ = Nat.card Φ.range := AddSubgroup.index_ker Φ
    _ ≤ Q0.relIndex Q := hΦfin

/- English proof (translation)
Introduce `R X M _ _ _ _ _ σ w γ W hH A B hA hB hidx e e' he he' hee' he'e hadj hAe hBe hf`. Establish `memE : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) → ∀ x, x ∈ Submodule.map e S ↔ x ∈ S ∧ e x = x`. Introduce `S hS x`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨(hS y hy).1, he y⟩`. Introduce and unpack `⟨hx, hex⟩`. Conclude with `⟨x, hx, hex⟩`. Establish `memE' : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) → ∀ x, x ∈ Submodule.map e' S ↔ x ∈ S ∧ e' x = x`.

Introduce `S hS x`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨(hS y hy).2, he' y⟩`.

Introduce and unpack `⟨hx, hex⟩`. Conclude with `⟨x, hx, hex⟩`. Establish `prodF : idx A B = idx (Submodule.map e A) (Submodule.map e B) * idx (Submodule.map e' A) (Submodule.map e' B)`. Apply the tactic sequence `let φ : ↥B.toAddSubgroup →+ ↥(Submodule.map e B).toAddSubgroup × ↥(Submodule.map e' B).toAddSubgroup := { toFun := fun b => (⟨e b, Submodule.mem_map_of_mem b.2⟩, ⟨e' b, Submodule.mem_map_of_mem b.2⟩) map_zero' := by ext <;> simp map_add' := fun x y => by ext <;> simp }`. Establish `hφs : Function.Surjective φ`.

Introduce and unpack `⟨⟨x, hx⟩, ⟨y, hy⟩⟩`. Establish `hx'` using `(memE B hBe x).1 hx`. Establish `hy'` using `(memE' B hBe y).1 hy`. Use `⟨⟨x + y, B.add_mem hx'.1 hy'.1⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : e y = 0` using `by rw [← hy'.2, hee']`.

Establish `h2 : e' x = 0` using `by rw [← hx'.2, he'e]`. Apply the tactic sequence `ext <;> simp [φ, map_add, hx'.2, hy'.2, h1, h2]`. Establish `hcomap : A.toAddSubgroup.addSubgroupOf B.toAddSubgroup = AddSubgroup.comap φ (((Submodule.map e A).toAddSubgroup.addSubgroupOf (Submodule.map e B).toAddSubgroup).prod ((Submodule.map e' A).toAddSubgroup.addSubgroupOf (Submodule.map e' B).toAddSubgroup))`. Use extensionality with `b`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Conclude with `⟨Submodule.mem_map_of_mem hb, Submodule.mem_map_of_mem hb⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : e b ∈ A` using `((memE A hAe _).1 h1).1`.

Establish `h2' : e' b ∈ A` using `((memE' A hAe _).1 h2).1`. Establish `hbB : (b : X) ∈ B` using `b.2`. Establish `h3 : (b : X) - e b - e' b ∈ A` using `(hf b).2 (B.sub_mem (B.sub_mem hbB (hBe _ hbB).1) (hBe _ hbB).2)`. Use `A.add_mem (A.add_mem h3 h1') h2' using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Use `show (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).index = _`. Rewrite using `[hcomap, AddSubgroup.index_comap_of_surjective _ hφs, AddSubgroup.index_prod]`. Both sides reduce to the same expression. Establish `hfin2 : idx (Submodule.map e' A) (Submodule.map e' B) ≠ 0` using `fun h => hidx (by rw [prodF, h, mul_zero])`. Establish `s1h1 : ∀ p ∈ (Submodule.map e A).toAddSubgroup, ∀ q ∈ (Submodule.map e' B).toAddSubgroup, q ∈ (Submodule.map e' A).toAddSubgroup → γ p q = 1`.

Introduce `p hp q _ hq`. Conclude with `hH.iso hA ((memE A hAe p).1 hp).1 ((memE' A hAe q).1 hq).1`. Establish `s1h3 : ∀ p ∈ (Submodule.map e A).toAddSubgroup, (∀ q ∈ (Submodule.map e' B).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e B).toAddSubgroup`. Introduce `p hp hq`. Establish `hp'` using `(memE A hAe p).1 hp`.

Establish `hpB : p ∈ B`. Use `(hB p).2 (fun b hb => ?_)` and prove the remaining obligations. Rewrite using `[← hp'.2, hadj]`. Conclude with `hq _ ((memE' B hBe _).2 ⟨(hBe b hb).2, he' b⟩)`. Conclude with `(memE B hBe p).2 ⟨hpB, hp'.2⟩`.

Establish `st1` using `idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s1h1 s1h3 hfin2`. Establish `s2h1 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup, ∀ q ∈ (Submodule.map e A).toAddSubgroup, q ∈ (Submodule.map e B).toAddSubgroup → γ p q = 1`. Introduce `p hp q _ hq`. Conclude with `hH.iso hB ((memE' B hBe p).1 hp).1 ((memE B hBe q).1 hq).1`. Establish `s2h3 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup, (∀ q ∈ (Submodule.map e A).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e' A).toAddSubgroup`.

Introduce `p hp hq`. Establish `hp'` using `(memE' B hBe p).1 hp`. Establish `hpA : p ∈ A`. Use `(hA p).2 (fun a ha => hH.swap_eq_one ?_)` and prove the remaining obligations. Rewrite using `[← hp'.2, ← hadj]`.

Conclude with `hH.swap_eq_one (hq _ ((memE A hAe _).2 ⟨(hAe a ha).1, he a⟩))`. Conclude with `(memE' A hAe p).2 ⟨hpA, hp'.2⟩`. Establish `st2` using `idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s2h1 s2h3 st1.1`. Rewrite using `[prodF]`. Use `congr 1`.

Conclude with `le_antisymm st2.2 st1.2`.
-/
theorem UpperTheory.TP.W.idxHalf :
    IdxHalf := by
  intro R X M _ _ _ _ _ σ w γ W hH A B hA hB hidx e e' he he' hee' he'e hadj hAe hBe hf
  have memE : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) →
      ∀ x, x ∈ Submodule.map e S ↔ x ∈ S ∧ e x = x := by
    intro S hS x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hS y hy).1, he y⟩
    · rintro ⟨hx, hex⟩
      exact ⟨x, hx, hex⟩
  have memE' : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) →
      ∀ x, x ∈ Submodule.map e' S ↔ x ∈ S ∧ e' x = x := by
    intro S hS x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hS y hy).2, he' y⟩
    · rintro ⟨hx, hex⟩
      exact ⟨x, hx, hex⟩
  have prodF : idx A B = idx (Submodule.map e A) (Submodule.map e B) *
      idx (Submodule.map e' A) (Submodule.map e' B) := by
    let φ : ↥B.toAddSubgroup →+ ↥(Submodule.map e B).toAddSubgroup × ↥(Submodule.map e' B).toAddSubgroup :=
      { toFun := fun b => (⟨e b, Submodule.mem_map_of_mem b.2⟩, ⟨e' b, Submodule.mem_map_of_mem b.2⟩)
        map_zero' := by ext <;> simp
        map_add' := fun x y => by ext <;> simp }
    have hφs : Function.Surjective φ := by
      rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx' := (memE B hBe x).1 hx
      have hy' := (memE' B hBe y).1 hy
      refine ⟨⟨x + y, B.add_mem hx'.1 hy'.1⟩, ?_⟩
      have h1 : e y = 0 := by rw [← hy'.2, hee']
      have h2 : e' x = 0 := by rw [← hx'.2, he'e]
      ext <;> simp [φ, map_add, hx'.2, hy'.2, h1, h2]
    have hcomap : A.toAddSubgroup.addSubgroupOf B.toAddSubgroup =
        AddSubgroup.comap φ (((Submodule.map e A).toAddSubgroup.addSubgroupOf
          (Submodule.map e B).toAddSubgroup).prod
          ((Submodule.map e' A).toAddSubgroup.addSubgroupOf (Submodule.map e' B).toAddSubgroup)) := by
      ext b
      simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf,
        Submodule.mem_toAddSubgroup]
      constructor
      · intro hb
        exact ⟨Submodule.mem_map_of_mem hb, Submodule.mem_map_of_mem hb⟩
      · rintro ⟨h1, h2⟩
        have h1' : e b ∈ A := ((memE A hAe _).1 h1).1
        have h2' : e' b ∈ A := ((memE' A hAe _).1 h2).1
        have hbB : (b : X) ∈ B := b.2
        have h3 : (b : X) - e b - e' b ∈ A :=
          (hf b).2 (B.sub_mem (B.sub_mem hbB (hBe _ hbB).1) (hBe _ hbB).2)
        convert A.add_mem (A.add_mem h3 h1') h2' using 1
        abel
    show (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).index = _
    rw [hcomap, AddSubgroup.index_comap_of_surjective _ hφs, AddSubgroup.index_prod]
    rfl
  have hfin2 : idx (Submodule.map e' A) (Submodule.map e' B) ≠ 0 := fun h => hidx (by rw [prodF, h, mul_zero])
  have s1h1 : ∀ p ∈ (Submodule.map e A).toAddSubgroup, ∀ q ∈ (Submodule.map e' B).toAddSubgroup,
      q ∈ (Submodule.map e' A).toAddSubgroup → γ p q = 1 := by
    intro p hp q _ hq
    exact hH.iso hA ((memE A hAe p).1 hp).1 ((memE' A hAe q).1 hq).1
  have s1h3 : ∀ p ∈ (Submodule.map e A).toAddSubgroup,
      (∀ q ∈ (Submodule.map e' B).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e B).toAddSubgroup := by
    intro p hp hq
    have hp' := (memE A hAe p).1 hp
    have hpB : p ∈ B := by
      refine (hB p).2 (fun b hb => ?_)
      rw [← hp'.2, hadj]
      exact hq _ ((memE' B hBe _).2 ⟨(hBe b hb).2, he' b⟩)
    exact (memE B hBe p).2 ⟨hpB, hp'.2⟩
  have st1 := idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s1h1 s1h3 hfin2
  have s2h1 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup, ∀ q ∈ (Submodule.map e A).toAddSubgroup,
      q ∈ (Submodule.map e B).toAddSubgroup → γ p q = 1 := by
    intro p hp q _ hq
    exact hH.iso hB ((memE' B hBe p).1 hp).1 ((memE B hBe q).1 hq).1
  have s2h3 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup,
      (∀ q ∈ (Submodule.map e A).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e' A).toAddSubgroup := by
    intro p hp hq
    have hp' := (memE' B hBe p).1 hp
    have hpA : p ∈ A := by
      refine (hA p).2 (fun a ha => hH.swap_eq_one ?_)
      rw [← hp'.2, ← hadj]
      exact hH.swap_eq_one (hq _ ((memE A hAe _).2 ⟨(hAe a ha).1, he a⟩))
    exact (memE' A hAe p).2 ⟨hpA, hp'.2⟩
  have st2 := idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s2h1 s2h3 st1.1
  rw [prodF]
  congr 1
  exact le_antisymm st2.2 st1.2
