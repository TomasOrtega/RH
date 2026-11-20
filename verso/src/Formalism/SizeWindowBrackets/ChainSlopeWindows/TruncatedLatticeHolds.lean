import Formalism.SizeWindowBrackets.LcvBaseChange
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic

open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.LLcv

open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData

section Loc

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

def pLen (p : Ideal R) [p.IsPrime] (A B : Submodule R W) : ℕ∞ :=
  Module.length R ((localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype)

/- English proof (translation)
The claim follows from `indexBasic_len_add (localization₂ p B) (localization₂ p C) (localization₂ p A) (locBasic_locS_mono _ hBC) (locBasic_locS_mono _ hCA)`.
-/
theorem pLen_add (p : Ideal R) [p.IsPrime] {A C B : Submodule R W} (hBC : B ≤ C) (hCA : C ≤ A) :
    pLen p A B = pLen p C B + pLen p A C :=
  indexBasic_len_add (localization₂ p B) (localization₂ p C) (localization₂ p A) (locBasic_locS_mono _ hBC)
    (locBasic_locS_mono _ hCA)

/- English proof (translation)
Unfold `pLen`. Rewrite using `[Submodule.comap_subtype_self]`. Simplify using the standard rewrite rules.
-/
theorem pLen_self (p : Ideal R) [p.IsPrime] (A : Submodule R W) : pLen p A A = 0 := by
  unfold pLen
  rw [Submodule.comap_subtype_self]
  simp

/- English proof (translation)
Establish `hnle : ¬ m ≤ p` using `fun hle => h (hm.eq_of_le hp.ne_top hle).symm`. Take `⟨s, hsm, hsp⟩` from `SetLike.not_le_iff_exists.1 hnle`. Establish `hA : A ≤ localization₂ p C` using `fun x hx => ⟨s, hsp, hkill s hsm x hx⟩`. Establish `hle : localization₂ p A ≤ localization₂ p C`. Use `locBasic_locS_mono p.primeCompl hA` as an intermediate fact.

Unfold `localization₂ at this ⊢`. Rewrite `this` using `[locBasic_locS_idem]`. Then use the resulting hypothesis. Unfold `pLen`. Rewrite using `[Submodule.comap_subtype_eq_top.2 hle]`. Simplify using the standard rewrite rules.
-/
theorem pLen_simple_ne (p m : Ideal R) [hp : p.IsMaximal] [hm : m.IsMaximal] (h : p ≠ m)
    {A C : Submodule R W} (hkill : ∀ s ∈ m, ∀ x ∈ A, s • x ∈ C) : pLen p A C = 0 := by
  have hnle : ¬ m ≤ p := fun hle => h (hm.eq_of_le hp.ne_top hle).symm
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hnle
  have hA : A ≤ localization₂ p C := fun x hx => ⟨s, hsp, hkill s hsm x hx⟩
  have hle : localization₂ p A ≤ localization₂ p C := by
    have := locBasic_locS_mono p.primeCompl hA
    unfold localization₂ at this ⊢
    rwa [locBasic_locS_idem] at this
  unfold pLen
  rw [Submodule.comap_subtype_eq_top.2 hle]
  simp

/- English proof (translation)
Introduce `s hs x hx`. Establish `h0 : e (Submodule.Quotient.mk (s • (⟨x, hx⟩ : A))) = 0`. Rewrite using `[Submodule.Quotient.mk_smul, map_smul]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk (⟨x, hx⟩ : A)))`. Rewrite using `[← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `m.mul_mem_right _ hs`. Rewrite `h0` using `[map_eq_zero_iff e e.injective, Submodule.Quotient.mk_eq_zero]`. Conclude with `h0`.
-/
theorem kill_of_equiv (m : Ideal R) {A C : Submodule R W}
    (e : (A ⧸ C.comap A.subtype) ≃ₗ[R] (R ⧸ m)) : ∀ s ∈ m, ∀ x ∈ A, s • x ∈ C := by
    intro s hs x hx
    have h0 : e (Submodule.Quotient.mk (s • (⟨x, hx⟩ : A))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk (⟨x, hx⟩ : A)))
      rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact m.mul_mem_right _ hs
    rw [map_eq_zero_iff e e.injective, Submodule.Quotient.mk_eq_zero] at h0
    exact h0

/- English proof (translation)
Establish `hkill` using `kill_of_equiv m e`. Establish `hinv : ∀ s ∉ m, ∃ t, t * s - 1 ∈ m`. Introduce `s hs`. Take `⟨t, ht⟩` from `Ideal.Quotient.exists_inv (I := m) (a := Ideal.Quotient.mk m s) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective t`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, mul_comm, ht, sub_self]`. Establish `hAP : A ≤ localization₂ m A` using `locBasic_le_locS _ A`. Set `ψ : A →ₗ[R] (localization₂ m A) ⧸ (localization₂ m C).comap (localization₂ m A).subtype` to `((localization₂ m C).comap (localization₂ m A).subtype).mkQ ∘ₗ Submodule.inclusion hAP`. Establish `hsurj : Function.Surjective ψ`.

Introduce `z`. Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H x`. Take `⟨s, hs, hsx⟩` from `x.2`. Take `⟨t, ht⟩` from `hinv s hs`.

Use `⟨⟨t • s • (x : W), A.smul_mem t hsx⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.mkQ _ _ = Submodule.Quotient.mk x`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.eq]`. Use `show (t • s • (x : W) - x) ∈ localization₂ m C`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Establish `e1 : s • (t • s • (x : W) - x) = (t * s - 1) • (s • (x : W))` using `by module`. Rewrite using `[e1]`. Conclude with `hkill _ ht _ hsx`. Establish `hker : LinearMap.ker ψ = C.comap A.subtype`. Use extensionality with `x`.

Rewrite using `[LinearMap.mem_ker]`. Use `show Submodule.mkQ _ _ = 0 ↔ _`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `show (x : W) ∈ localization₂ m C ↔ (x : W) ∈ C`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs, hsx⟩`. Take `⟨t, ht⟩` from `hinv s hs`. Establish `e1 : (x : W) = t • (s • (x : W)) - (t * s - 1) • (x : W)` using `by module`. Rewrite using `[e1]`. Conclude with `C.sub_mem (C.smul_mem t hsx) (hkill _ ht _ x.2)`.

Introduce `hx`. Conclude with `locBasic_le_locS _ C hx`. Establish `e2 : (A ⧸ C.comap A.subtype) ≃ₗ[R] (localization₂ m A) ⧸ (localization₂ m C).comap (localization₂ m A).subtype` using `(Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)`. Establish `hs : IsSimpleModule R (R ⧸ m)` using `isSimpleModule_iff_isCoatom.2 hm.out`. Unfold `pLen`.

Rewrite using `[(e2.symm.trans e).length_eq]`. Conclude with `Module.length_eq_one_iff.2 hs`.
-/
theorem pLen_simple_self (m : Ideal R) [hm : m.IsMaximal] {A C : Submodule R W}
    (e : (A ⧸ C.comap A.subtype) ≃ₗ[R] (R ⧸ m)) : pLen m A C = 1 := by
  have hkill := kill_of_equiv m e
  have hinv : ∀ s ∉ m, ∃ t, t * s - 1 ∈ m := by
    intro s hs
    obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv (I := m)
      (a := Ideal.Quotient.mk m s) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, mul_comm, ht, sub_self]
  have hAP : A ≤ localization₂ m A := locBasic_le_locS _ A
  let ψ : A →ₗ[R] (localization₂ m A) ⧸ (localization₂ m C).comap (localization₂ m A).subtype :=
    ((localization₂ m C).comap (localization₂ m A).subtype).mkQ ∘ₗ Submodule.inclusion hAP
  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, hsx⟩ := x.2
      obtain ⟨t, ht⟩ := hinv s hs
      refine ⟨⟨t • s • (x : W), A.smul_mem t hsx⟩, ?_⟩
      show Submodule.mkQ _ _ = Submodule.Quotient.mk x
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      show (t • s • (x : W) - x) ∈ localization₂ m C
      refine ⟨s, hs, ?_⟩
      have e1 : s • (t • s • (x : W) - x) = (t * s - 1) • (s • (x : W)) := by module
      rw [e1]
      exact hkill _ ht _ hsx
  have hker : LinearMap.ker ψ = C.comap A.subtype := by
    ext x
    rw [LinearMap.mem_ker]
    show Submodule.mkQ _ _ = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (x : W) ∈ localization₂ m C ↔ (x : W) ∈ C
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨t, ht⟩ := hinv s hs
      have e1 : (x : W) = t • (s • (x : W)) - (t * s - 1) • (x : W) := by module
      rw [e1]
      exact C.sub_mem (C.smul_mem t hsx) (hkill _ ht _ x.2)
    · intro hx
      exact locBasic_le_locS _ C hx
  have e2 : (A ⧸ C.comap A.subtype) ≃ₗ[R] (localization₂ m A) ⧸ (localization₂ m C).comap (localization₂ m A).subtype :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  have hs : IsSimpleModule R (R ⧸ m) := isSimpleModule_iff_isCoatom.2 hm.out
  unfold pLen
  rw [(e2.symm.trans e).length_eq]
  exact Module.length_eq_one_iff.2 hs

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `A B hBA hn hn0`. Distinguish the cases in `hEq : B = A`.

Substitute `hEq` using the available equality. Use `⟨0, fun w => ?_, ?_⟩` and prove the remaining obligations. Use `w.2.isPrime` as an intermediate fact. Rewrite using `[pLen_self]`. Simplify using the standard rewrite rules.

Rewrite using `[Finsupp.prod_zero_index, AddSubgroup.relIndex_self]`. Use `set B' := B.comap A.subtype with hB'`. Establish `hcard : Nat.card (A ⧸ B') ≠ 0` using `by rw [← hn] at hn0; exact hn0`. Establish `hfin : Finite (A ⧸ B')` using `Nat.finite_of_card_ne_zero hcard`. Establish `hnt : Nontrivial (A ⧸ B')`.

Rewrite using `[Submodule.Quotient.nontrivial_iff]`. Introduce `htop`. Conclude with `hEq (le_antisymm hBA (Submodule.comap_subtype_eq_top.1 htop))`. Break down `eq_top_or_exists_le_coatom (⊥ : Submodule R (A ⧸ B')) with h | ⟨Q1, hQ1, -⟩` into its components or cases. Conclude with `absurd h bot_ne_top`.

Establish `hsimple : IsSimpleModule R ((A ⧸ B') ⧸ Q1)` using `isSimpleModule_iff_isCoatom.2 hQ1`. Take `⟨m0, hm0, ⟨e0⟩⟩` from `isSimpleModule_iff_quot_maximal.1 hsimple`. Use `set C' : Submodule R A := Q1.comap B'.mkQ with hC'`. Use `set C : Submodule R W := C'.map A.subtype with hC`. Establish `hCA : C ≤ A` using `Submodule.map_subtype_le A C'`.

Establish `hCc : C.comap A.subtype = C'` using `Submodule.comap_map_eq_of_injective A.injective_subtype C'`. Establish `hBC : B ≤ C`. Introduce `x hx`. Use `⟨⟨x, hBA hx⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show B'.mkQ ⟨x, hBA hx⟩ ∈ Q1`.

Establish `: B'.mkQ ⟨x, hBA hx⟩ = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hx`. Rewrite using `[this]`. Conclude with `Q1.zero_mem`.

Establish `hker : LinearMap.ker (Q1.mkQ ∘ₗ B'.mkQ) = C.comap A.subtype`. Rewrite using `[LinearMap.ker_comp, Submodule.ker_mkQ, hCc]`. Establish `hsurj : Function.Surjective (Q1.mkQ ∘ₗ B'.mkQ)` using `Q1.mkQ_surjective.comp B'.mkQ_surjective`. Establish `e : (A ⧸ C.comap A.subtype) ≃ₗ[R] (R ⧸ m0)` using `((Submodule.quotEquivOfEq _ _ hker.symm).trans ((Q1.mkQ ∘ₗ B'.mkQ).quotKerEquivOfSurjective hsurj)).trans e0`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex B.toAddSubgroup C.toAddSubgroup A.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 hBC) ((Submodule.toAddSubgroup_le _ _).2 hCA)`.

Establish `hCAcard : C.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ m0)`. Express the relevant statement in the definitionally equal form `Nat.card (A ⧸ C.comap A.subtype) = _`. Conclude with `Nat.card_congr e.toEquiv`. Establish `hne : B.toAddSubgroup.relIndex C.toAddSubgroup ≠ 0`. Introduce `h0`.

Rewrite `hmul` using `[h0, zero_mul, hn]`. Conclude with `hn0 hmul.symm`. Establish `hne2 : Nat.card (R ⧸ m0) ≠ 0`. Introduce `h0`. Rewrite `hmul` using `[hCAcard, h0, mul_zero, hn]`.

Conclude with `hn0 hmul.symm`. Establish `h1 : 1 < Nat.card (R ⧸ m0)`. Establish `: Finite (R ⧸ m0)` using `Nat.finite_of_card_ne_zero hne2`. Establish `: Nontrivial (R ⧸ m0)` using `Ideal.Quotient.nontrivial_iff.2 hm0.ne_top`. Conclude with `Finite.one_lt_card`.

Establish `hlt : B.toAddSubgroup.relIndex C.toAddSubgroup < n`. Rewrite using `[← hn, ← hmul, hCAcard]`. Use `Nat.pos_of_ne_zero hne` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨k1, hk1, hk1c⟩` from `ih _ hlt C B hBC rfl hne`.

Use `⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩` and prove the remaining obligations. Use `w.2.isPrime` as an intermediate fact. Use `w.2` as an intermediate fact. Rewrite using `[pLen_add w.1 hBC hCA, hk1 w, Finsupp.add_apply, Finsupp.single_apply]`. Distinguish the cases in `hw : (⟨m0, hm0⟩ : {p : Ideal R // p.IsMaximal}) = w`.

Substitute `hw` using the available equality. Rewrite using `[if_pos rfl, pLen_simple_self m0 e]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hw, pLen_simple_ne w.1 m0 (fun h => hw (Subtype.ext h.symm)) (kill_of_equiv m0 e)]`. Simplify using the standard rewrite rules.

Establish `hz : ∀ w : {p : Ideal R // p.IsMaximal}, Nat.card (R ⧸ w.1) ^ 0 = 1` using `fun _ => pow_zero _`. Establish `ha : ∀ (w : {p : Ideal R // p.IsMaximal}) (a c : ℕ), Nat.card (R ⧸ w.1) ^ (a + c) = Nat.card (R ⧸ w.1) ^ a * Nat.card (R ⧸ w.1) ^ c` using `fun _ _ _ => pow_add _ _ _`. Rewrite using `[Finsupp.prod_add_index' (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) hz ha, Finsupp.prod_single_index (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) (hz _), pow_one, ← hmul, hk1c, hCAcard]`.
-/
theorem card_pLen : ∀ (n : ℕ) (A B : Submodule R W), B ≤ A →
    B.toAddSubgroup.relIndex A.toAddSubgroup = n → n ≠ 0 →
    ∃ k : {p : Ideal R // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal R // p.IsMaximal}, (haveI := w.2.isPrime; pLen w.1 A B) = (k w : ℕ∞)) ∧
      B.toAddSubgroup.relIndex A.toAddSubgroup = k.prod fun w j => Nat.card (R ⧸ w.1) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B hBA hn hn0
  by_cases hEq : B = A
  · subst hEq
    refine ⟨0, fun w => ?_, ?_⟩
    · have := w.2.isPrime
      rw [pLen_self]; simp
    · rw [Finsupp.prod_zero_index, AddSubgroup.relIndex_self]
  · set B' := B.comap A.subtype with hB'
    have hcard : Nat.card (A ⧸ B') ≠ 0 := by rw [← hn] at hn0; exact hn0
    have hfin : Finite (A ⧸ B') := Nat.finite_of_card_ne_zero hcard
    have hnt : Nontrivial (A ⧸ B') := by
      rw [Submodule.Quotient.nontrivial_iff]
      intro htop
      exact hEq (le_antisymm hBA (Submodule.comap_subtype_eq_top.1 htop))
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R (A ⧸ B')) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R ((A ⧸ B') ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e0⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      set C' : Submodule R A := Q1.comap B'.mkQ with hC'
      set C : Submodule R W := C'.map A.subtype with hC
      have hCA : C ≤ A := Submodule.map_subtype_le A C'
      have hCc : C.comap A.subtype = C' :=
        Submodule.comap_map_eq_of_injective A.injective_subtype C'
      have hBC : B ≤ C := by
        intro x hx
        refine ⟨⟨x, hBA hx⟩, ?_, rfl⟩
        show B'.mkQ ⟨x, hBA hx⟩ ∈ Q1
        have : B'.mkQ ⟨x, hBA hx⟩ = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
        rw [this]; exact Q1.zero_mem
      have hker : LinearMap.ker (Q1.mkQ ∘ₗ B'.mkQ) = C.comap A.subtype := by
        rw [LinearMap.ker_comp, Submodule.ker_mkQ, hCc]
      have hsurj : Function.Surjective (Q1.mkQ ∘ₗ B'.mkQ) :=
        Q1.mkQ_surjective.comp B'.mkQ_surjective
      have e : (A ⧸ C.comap A.subtype) ≃ₗ[R] (R ⧸ m0) :=
        ((Submodule.quotEquivOfEq _ _ hker.symm).trans
          ((Q1.mkQ ∘ₗ B'.mkQ).quotKerEquivOfSurjective hsurj)).trans e0
      have hmul := AddSubgroup.relIndex_mul_relIndex B.toAddSubgroup C.toAddSubgroup
        A.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 hBC)
        ((Submodule.toAddSubgroup_le _ _).2 hCA)
      have hCAcard : C.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ m0) := by
        change Nat.card (A ⧸ C.comap A.subtype) = _
        exact Nat.card_congr e.toEquiv
      have hne : B.toAddSubgroup.relIndex C.toAddSubgroup ≠ 0 := by
        intro h0; rw [h0, zero_mul, hn] at hmul; exact hn0 hmul.symm
      have hne2 : Nat.card (R ⧸ m0) ≠ 0 := by
        intro h0; rw [hCAcard, h0, mul_zero, hn] at hmul; exact hn0 hmul.symm
      have h1 : 1 < Nat.card (R ⧸ m0) := by
        have : Finite (R ⧸ m0) := Nat.finite_of_card_ne_zero hne2
        have : Nontrivial (R ⧸ m0) := Ideal.Quotient.nontrivial_iff.2 hm0.ne_top
        exact Finite.one_lt_card
      have hlt : B.toAddSubgroup.relIndex C.toAddSubgroup < n := by
        rw [← hn, ← hmul, hCAcard]
        have := Nat.pos_of_ne_zero hne
        nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt C B hBC rfl hne
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.2.isPrime
        have := w.2
        rw [pLen_add w.1 hBC hCA, hk1 w, Finsupp.add_apply, Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : {p : Ideal R // p.IsMaximal}) = w
        · subst hw
          rw [if_pos rfl, pLen_simple_self m0 e]; simp
        · rw [if_neg hw, pLen_simple_ne w.1 m0 (fun h => hw (Subtype.ext h.symm))
            (kill_of_equiv m0 e)]; simp
      · have hz : ∀ w : {p : Ideal R // p.IsMaximal}, Nat.card (R ⧸ w.1) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : {p : Ideal R // p.IsMaximal}) (a c : ℕ), Nat.card (R ⧸ w.1) ^ (a + c) =
            Nat.card (R ⧸ w.1) ^ a * Nat.card (R ⧸ w.1) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) (hz _),
          pow_one, ← hmul, hk1c, hCAcard]

end Loc

/- English proof (translation)
Take `⟨k, hk, hc⟩` from `card_pLen _ A B hBA rfl h`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_pow, Real.log_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_comm]`.

Introduce `w hw h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[hc, Finsupp.prod]`. Conclude with `Finset.prod_eq_zero hw (by exact_mod_cast h0)`.
-/
theorem indexLocLen_finsupp {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module (𝓞 K) V] (A B : Submodule (𝓞 K) V) (hBA : B ≤ A)
    (h : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ k : {p : Ideal (𝓞 K) // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
        (haveI := w.2.isPrime; pLen w.1 A B) = (k w : ℕ∞)) ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ w ∈ k.support, Real.log (Ideal.absNorm w.1 : ℝ) * (k w : ℝ) := by
  obtain ⟨k, hk, hc⟩ := card_pLen _ A B hBA rfl h
  refine ⟨k, hk, ?_⟩
  rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Real.log_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_comm]
  · intro w hw h0
    apply h
    rw [hc, Finsupp.prod]
    exact Finset.prod_eq_zero hw (by exact_mod_cast h0)

/- English proof (translation)
Introduce `K V _ _ _ _ A B hBA h`. Take `⟨k, hk, hc⟩` from `indexLocLen_finsupp A B hBA h`. Establish `hl : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI` using `w.2.isPrime; Formalism.HermitianLatticesTheory.locLen w.1 A B) = k w := by`. Introduce `w`. Use `hk w` as an intermediate fact.

Unfold `pLen at this`. Unfold `Formalism.HermitianLatticesTheory.locLen`. Rewrite using `[this, ENat.toNat_natCast]`. Use `⟨fun w => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hk w` as an intermediate fact.

Unfold `pLen at this`. Rewrite using `[this]`. Conclude with `ENat.natCast_ne_top _`. Use `k.support.finite_toSet.subset fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[Function.mem_support, hl]`.

Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Conclude with `hw`. Rewrite using `[hc, finsum_eq_sum_of_support_subset (s := k.support)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hl]`.

Introduce `w hw`. Rewrite `hw` using `[Function.mem_support, hl]`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h0`. Rewrite `hw` using `[h0]`.

Simplify using `at hw`.
-/
theorem index_local_length : IndexLocLen := by
  intro K V _ _ _ _ A B hBA h
  obtain ⟨k, hk, hc⟩ := indexLocLen_finsupp A B hBA h
  have hl : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
      (haveI := w.2.isPrime; Formalism.HermitianLatticesTheory.locLen w.1 A B) = k w := by
    intro w
    have := hk w
    unfold pLen at this
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this, ENat.toNat_natCast]
  refine ⟨fun w => ?_, ?_, ?_⟩
  · have := hk w
    unfold pLen at this
    rw [this]; exact ENat.natCast_ne_top _
  · refine k.support.finite_toSet.subset fun w hw => ?_
    rw [Function.mem_support, hl] at hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    exact hw
  · rw [hc, finsum_eq_sum_of_support_subset (s := k.support)]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [hl]
    · intro w hw
      rw [Function.mem_support, hl] at hw
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      rw [h0] at hw
      simp at hw

section Span

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Set `T : Submodule K V` to `{ carrier := locS (nonZeroDivisors (𝓞 K)) Y add_mem' := (locS (nonZeroDivisors (𝓞 K)) Y).add_mem zero_mem' := (locS (nonZeroDivisors (𝓞 K)) Y).zero_mem smul_mem' := by`. Introduce and unpack `c v ⟨d, hd, hdv⟩`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (𝓞 K) c`. Establish `hb0 : algebraMap (𝓞 K) K b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Use `⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩` and prove the remaining obligations.

Establish `hc : algebraMap (𝓞 K) K b * (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) = algebraMap (𝓞 K) K a`. Clear the denominators using the available nonvanishing facts. Establish `: (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • v) = a • (d • v)`. Rewrite using `[mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul, smul_comm]`. Rewrite using `[this]`.

Conclude with `Y.smul_mem a hdv }`. Establish `hle : Submodule.span K (Y : Set V) ≤ T` using `Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)`. Conclude with `hle hx`.
-/
theorem span_le_locS (Y : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (Y : Set V)) :
    x ∈ locS (nonZeroDivisors (𝓞 K)) Y := by
  let T : Submodule K V :=
    { carrier := locS (nonZeroDivisors (𝓞 K)) Y
      add_mem' := (locS (nonZeroDivisors (𝓞 K)) Y).add_mem
      zero_mem' := (locS (nonZeroDivisors (𝓞 K)) Y).zero_mem
      smul_mem' := by
        rintro c v ⟨d, hd, hdv⟩
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
        have hb0 : algebraMap (𝓞 K) K b ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        refine ⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩
        have hc : algebraMap (𝓞 K) K b * (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
            algebraMap (𝓞 K) K a := by
          field_simp
        have : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • v) = a • (d • v) := by
          rw [mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul,
            smul_comm]
        rw [this]
        exact Y.smul_mem a hdv }
  have hle : Submodule.span K (Y : Set V) ≤ T :=
    Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)
  exact hle hx

/- English proof (translation)
Establish `hEM : E ≤ locS (nonZeroDivisors (𝓞 K)) M` using `fun x hx => span_le_locS M (h ▸ Submodule.subset_span hx)`. Take `⟨d, hd, hdE⟩` from `indexBasic_denom _ E M hE hEM`. Establish `hd0 : algebraMap (𝓞 K) K d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_mono (fun x hx => hx.1)`.

Use `Submodule.span_le.2 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : d • x ∈ (E ⊓ M : Submodule (𝓞 K) V)` using `⟨E.smul_mem d hx, hdE x hx⟩`. Establish `h2 : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x)`. Rewrite using `[← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul]`. Rewrite using `[h2]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem span_inf {E M : Submodule (𝓞 K) V} (hE : E.FG)
    (h : Submodule.span K (E : Set V) = Submodule.span K (M : Set V)) :
    Submodule.span K ((E ⊓ M : Submodule (𝓞 K) V) : Set V) = Submodule.span K (E : Set V) := by
  have hEM : E ≤ locS (nonZeroDivisors (𝓞 K)) M := fun x hx =>
    span_le_locS M (h ▸ Submodule.subset_span hx)
  obtain ⟨d, hd, hdE⟩ := indexBasic_denom _ E M hE hEM
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  apply le_antisymm
  · exact Submodule.span_mono (fun x hx => hx.1)
  · refine Submodule.span_le.2 fun x hx => ?_
    have h1 : d • x ∈ (E ⊓ M : Submodule (𝓞 K) V) := ⟨E.smul_mem d hx, hdE x hx⟩
    have h2 : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Span

section Main

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
Establish `hn` using `fun w => HeightGram.norm_det_gramPl b X w e`. Establish `hprod` using `(height_gram_determinant K V ι b X hX j e he).1`. Establish `hpos : 0 < ∏ w, (gramPl b X w e).det.re`. Rewrite using `[← hprod]`. Conclude with `ht_pos b X hX (Submodule.fg_span (Set.finite_range e))`.

Establish `h0 : (gramPl b X v e).det.re ≠ 0`. Introduce `h0`. Rewrite `hpos` using `[Finset.prod_eq_zero (Finset.mem_univ v) h0]`. Conclude with `lt_irrefl _ hpos`. Establish `hge : 0 ≤ (gramPl b X v e).det.re` using `by rw [← hn v]; exact norm_nonneg _`.

Use `⟨lt_of_le_of_ne hge h0.symm, ?_⟩` and prove the remaining obligations. Apply `(Complex.abs_re_eq_norm).1` to reduce the goal to its premises. Rewrite using `[hn v, abs_of_nonneg hge]`.
-/
theorem gram_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {j : ℕ} (e : Fin j → V) (he : LinearIndependent K e)
    (v : InfinitePlace K) : 0 < (gramPl b X v e).det.re ∧ (gramPl b X v e).det.im = 0 := by
  have hn := fun w => HeightGram.norm_det_gramPl b X w e
  have hprod := (height_gram_determinant K V ι b X hX j e he).1
  have hpos : 0 < ∏ w, (gramPl b X w e).det.re := by
    rw [← hprod]; exact ht_pos b X hX (Submodule.fg_span (Set.finite_range e))
  have h0 : (gramPl b X v e).det.re ≠ 0 := by
    intro h0
    rw [Finset.prod_eq_zero (Finset.mem_univ v) h0] at hpos
    exact lt_irrefl _ hpos
  have hge : 0 ≤ (gramPl b X v e).det.re := by rw [← hn v]; exact norm_nonneg _
  refine ⟨lt_of_le_of_ne hge h0.symm, ?_⟩
  apply (Complex.abs_re_eq_norm).1
  rw [hn v, abs_of_nonneg hge]

/- English proof (translation)
Establish `hs` using `span_inf hE h`. Establish `hrE : rkK (E ⊓ M) = rkK E` using `by unfold rkK; rw [hs]`. Establish `hrM : rkK (E ⊓ M) = rkK M` using `by unfold rkK; rw [hs, h]`. Establish `h1` using `ht_index b X hX hE inf_le_left hrE`. Establish `h2` using `ht_index b X hX hM inf_le_right hrM`.

Establish `n1` using `relIndex_ne_zero b X hX hE inf_le_left hrE`. Establish `n2` using `relIndex_ne_zero b X hX hM inf_le_right hrM`. Take `⟨kE, hkE, hcE⟩` from `indexLocLen_finsupp E (E ⊓ M) inf_le_left n1`. Take `⟨kM, hkM, hcM⟩` from `indexLocLen_finsupp M (E ⊓ M) inf_le_right n2`. Establish `hl : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI` using `w.2.isPrime; lidx w.1 E M) = (kE w : ℤ) - kM w := by`.

Introduce `w`. Establish `a1` using `hkE w`. Establish `a2` using `hkM w`. Unfold `pLen at a1 a2`. Unfold `lidx Formalism.HermitianLatticesTheory.locLen`.

Rewrite using `[a1, a2, ENat.toNat_natCast, ENat.toNat_natCast]`. Establish `hsub : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal}, w ∉ kE.support ∪ kM.support → (haveI` using `w.2.isPrime; lidx w.1 E M) = 0 := by`. Introduce `w hw`. Rewrite `hw` using `[Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff]`. Rewrite using `[hl, hw.1, hw.2]`.

Simplify using the standard rewrite rules. Use `⟨(kE.support ∪ kM.support).finite_toSet.subset fun w hw => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hw (hsub w hc)`. Rewrite using `[finsum_eq_sum_of_support_subset (s := kE.support ∪ kM.support)]`.

Establish `e1 : ∑ w ∈ kE.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) = ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ)` using `Finset.sum_subset Finset.subset_union_left fun w _ hw => by`. Rewrite using `[Finsupp.notMem_support_iff.1 hw]`. Simplify using the standard rewrite rules. Establish `e2 : ∑ w ∈ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) = ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ)` using `Finset.sum_subset Finset.subset_union_right fun w _ hw => by`. Rewrite using `[Finsupp.notMem_support_iff.1 hw]`.

Simplify using the standard rewrite rules. Establish `e3 : ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (haveI` using `w.2.isPrime; (lidx w.1 E M : ℝ)) = ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) - ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) := by`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hl]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, ← e1, ← e2, ← hcE, ← hcM]`. Establish `l1` using `congrArg Real.log h1`. Establish `l2` using `congrArg Real.log h2`.

Rewrite `l1` using `[Real.log_mul (ht_pos b X hX hE).ne' (by exact_mod_cast n1)]`. Rewrite `l2` using `[Real.log_mul (ht_pos b X hX hM).ne' (by exact_mod_cast n2)]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `w hw`. Assume the negation of the conclusion as `hc`.

Apply `hw` to reduce the goal to its premises. Use `show _ * _ = (0 : ℝ)`. Rewrite using `[hsub w hc]`. Simplify using the standard rewrite rules.
-/
theorem ht_lidx (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {E M : Submodule (𝓞 K) V} (hE : E.FG) (hM : M.FG)
    (h : Submodule.span K (E : Set V) = Submodule.span K (M : Set V)) :
    (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; lidx p.1 E M)).Finite ∧
      Real.log (ht b X M) = Real.log (ht b X E) +
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (lidx p.1 E M : ℝ)) := by
  classical
  have hs := span_inf hE h
  have hrE : rkK (E ⊓ M) = rkK E := by unfold rkK; rw [hs]
  have hrM : rkK (E ⊓ M) = rkK M := by unfold rkK; rw [hs, h]
  have h1 := ht_index b X hX hE inf_le_left hrE
  have h2 := ht_index b X hX hM inf_le_right hrM
  have n1 := relIndex_ne_zero b X hX hE inf_le_left hrE
  have n2 := relIndex_ne_zero b X hX hM inf_le_right hrM
  obtain ⟨kE, hkE, hcE⟩ := indexLocLen_finsupp E (E ⊓ M) inf_le_left n1
  obtain ⟨kM, hkM, hcM⟩ := indexLocLen_finsupp M (E ⊓ M) inf_le_right n2
  have hl : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
      (haveI := w.2.isPrime; lidx w.1 E M) = (kE w : ℤ) - kM w := by
    intro w
    have a1 := hkE w
    have a2 := hkM w
    unfold pLen at a1 a2
    unfold lidx Formalism.HermitianLatticesTheory.locLen
    rw [a1, a2, ENat.toNat_natCast, ENat.toNat_natCast]
  have hsub : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal}, w ∉ kE.support ∪ kM.support →
      (haveI := w.2.isPrime; lidx w.1 E M) = 0 := by
    intro w hw
    rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hw
    rw [hl, hw.1, hw.2]; simp
  refine ⟨(kE.support ∪ kM.support).finite_toSet.subset fun w hw => ?_, ?_⟩
  · by_contra hc
    exact hw (hsub w hc)
  · rw [finsum_eq_sum_of_support_subset (s := kE.support ∪ kM.support)]
    · have e1 : ∑ w ∈ kE.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) =
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) :=
        Finset.sum_subset Finset.subset_union_left fun w _ hw => by
          rw [Finsupp.notMem_support_iff.1 hw]; simp
      have e2 : ∑ w ∈ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) =
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) :=
        Finset.sum_subset Finset.subset_union_right fun w _ hw => by
          rw [Finsupp.notMem_support_iff.1 hw]; simp
      have e3 : ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) *
          (haveI := w.2.isPrime; (lidx w.1 E M : ℝ)) =
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) -
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hl]; push_cast; ring
      rw [e3, ← e1, ← e2, ← hcE, ← hcM]
      have l1 := congrArg Real.log h1
      have l2 := congrArg Real.log h2
      rw [Real.log_mul (ht_pos b X hX hE).ne' (by exact_mod_cast n1)] at l1
      rw [Real.log_mul (ht_pos b X hX hM).ne' (by exact_mod_cast n2)] at l2
      linarith
    · intro w hw
      by_contra hc
      apply hw
      show _ * _ = (0 : ℝ)
      rw [hsub w hc]; simp

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e M he hM hM0 hsp`. Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hrk : rkK M = j`. Unfold `rkK`. Rewrite using `[hsp, finrank_span_eq_card he, Fintype.card_fin]`.

Establish `hj : 0 < j` using `hrk ▸ rkK_pos hM0`. Establish `hE : (Submodule.span (𝓞 K) (Set.range e)).FG` using `Submodule.fg_span (Set.finite_range e)`. Establish `hsp' : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) : Set V) = Submodule.span K (M : Set V)`. Rewrite using `[Submodule.span_span_of_tower, hsp]`. Take `⟨hfin, hlog⟩` from `ht_lidx b X hX hE hM hsp'`.

Use `⟨hrk, hj, gram_pos b X hX e he, hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[muDef_eq_log b X hX hM hM0, hlog, (height_gram_determinant K V ι b X hX j e he).1, Real.log_prod (fun v _ => (gram_pos b X hX e he v).1.ne')]`. Unfold `lcv lcvInf lcvFin`. Establish `hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ)`. Rewrite using `[sizeMu_finrank_eq K]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hf : (nPl K : ℝ) ≠ 0`. Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hj' : (rkK M : ℝ) ≠ 0` using `by rw [hrk]; exact_mod_cast hj.ne'`. Establish `hsum : ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) * (haveI` using `p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ)) = (1 / (Module.finrank ℚ K : ℝ)) * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) * (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ)) := by`. Rewrite using `[mul_finsum']`. Use `finsum_congr fun p => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `hfin.subset fun p hp => ?_` and prove the remaining obligations. Rewrite `hp`, the goal using `[Function.mem_support]`. Introduce `h0`. Apply `hp` to reduce the goal to its premises. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Rewrite using `[hsum, hn]`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_covolume_slope_mu : LcvMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e M he hM hM0 hsp
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hrk : rkK M = j := by
    unfold rkK; rw [hsp, finrank_span_eq_card he, Fintype.card_fin]
  have hj : 0 < j := hrk ▸ rkK_pos hM0
  have hE : (Submodule.span (𝓞 K) (Set.range e)).FG := Submodule.fg_span (Set.finite_range e)
  have hsp' : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (M : Set V) := by
    rw [Submodule.span_span_of_tower, hsp]
  obtain ⟨hfin, hlog⟩ := ht_lidx b X hX hE hM hsp'
  refine ⟨hrk, hj, gram_pos b X hX e he, hfin, ?_⟩
  rw [muDef_eq_log b X hX hM hM0, hlog, (height_gram_determinant K V ι b X hX j e he).1,
    Real.log_prod (fun v _ => (gram_pos b X hX e he v).1.ne')]
  unfold lcv lcvInf lcvFin
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    rw [sizeMu_finrank_eq K]; push_cast; ring
  have hf : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hj' : (rkK M : ℝ) ≠ 0 := by rw [hrk]; exact_mod_cast hj.ne'
  have hsum : ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
      (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
        (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ)) =
      (1 / (Module.finrank ℚ K : ℝ)) * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
        Real.log (Ideal.absNorm p.1 : ℝ) *
        (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ)) := by
    rw [mul_finsum']
    · refine finsum_congr fun p => ?_
      ring
    · refine hfin.subset fun p hp => ?_
      rw [Function.mem_support] at hp ⊢
      intro h0
      apply hp
      rw [h0]; simp
  rw [hsum, hn]
  field_simp

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e M he hM hM0 hsp`. Take `⟨-, -, -, hfin, hmu⟩` from `log_covolume_slope_mu K V ι b X hX j e M he hM hM0 hsp`. Conclude with `⟨hfin, hmu⟩`.
-/
theorem covolume_formula : Formalism.HN.LcvFormula := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e M he hM hM0 hsp
  obtain ⟨-, -, -, hfin, hmu⟩ := log_covolume_slope_mu K V ι b X hX j e M he hM hM0 hsp
  exact ⟨hfin, hmu⟩

end Main

section Mod

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/- English proof (translation)
Rewrite using `[map_inv₀, Rat.cast_inv, Real.log_inv]`.
-/
theorem log_absNorm_inv (I : FI) :
    Real.log ((FractionalIdeal.absNorm I⁻¹ : ℚ) : ℝ) =
      -Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  rw [map_inv₀, Rat.cast_inv, Real.log_inv]

/- English proof (translation)
Establish `h` using `ht_fractional b X hX hN hI`. Establish `hp` using `ht_pos b X hX hN`. Unfold `ht at h hp`. Rewrite `h` using `[rkK_idealSmul hI]`. Use `set c : ℝ := (2 : ℝ) ^ (nPl K * rkK N) * |(NumberField.discr K : ℝ)| ^ (-(rkK N : ℝ) / 2) with hc`.

Establish `hD : 0 < |(NumberField.discr K : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))`. Establish `hc0 : 0 < c` using `by positivity`. Establish `hcov : 0 < Formalism.F.covol (zl (realize b X) N)`. Assume the negation of the conclusion as `hneg`. Establish `: c * Formalism.F.covol (zl (realize b X) N) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hc0.le (not_lt.1 hneg)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Formalism.F.covol (zl (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N)) = Formalism.F.covol (zl (realize b X) N) * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK N`. Apply `mul_left_cancel₀ hc0.ne'` to reduce the goal to its premises. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `deg Formalism.F.deg`. Rewrite using `[h2, Real.log_mul hcov.ne' (pow_ne_zero _ (absNorm_pos hI).ne'), Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {N : Submodule (𝓞 K) V} (hN : N.FG) {I : FI} (hI : I ≠ 0) :
    deg (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N) = deg (realize b X) N -
      (rkK N : ℝ) * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h := ht_fractional b X hX hN hI
  have hp := ht_pos b X hX hN
  unfold ht at h hp
  rw [rkK_idealSmul hI] at h
  set c : ℝ := (2 : ℝ) ^ (nPl K * rkK N) * |(NumberField.discr K : ℝ)| ^ (-(rkK N : ℝ) / 2)
    with hc
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hc0 : 0 < c := by positivity
  have hcov : 0 < Formalism.F.covol (zl (realize b X) N) := by
    by_contra hneg
    have : c * Formalism.F.covol (zl (realize b X) N) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc0.le (not_lt.1 hneg)
    linarith
  have h2 : Formalism.F.covol (zl (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N)) =
      Formalism.F.covol (zl (realize b X) N) * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK N := by
    apply mul_left_cancel₀ hc0.ne'
    rw [h]; ring
  unfold deg Formalism.F.deg
  rw [h2, Real.log_mul hcov.ne' (pow_ne_zero _ (absNorm_pos hI).ne'), Real.log_pow]
  ring

/- English proof (translation)
Rewrite using `[(place_lattice_structure K V ι b X hX _ (idealSmul_fg I hN)).2.1, (place_lattice_structure K V ι b X hX _ hN).2.1, rkK_idealSmul hI]`.
-/
theorem rk_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {N : Submodule (𝓞 K) V} (hN : N.FG) {I : FI} (hI : I ≠ 0) :
    rk (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N) = rk (realize b X) N := by
  rw [(place_lattice_structure K V ι b X hX _ (idealSmul_fg I hN)).2.1, (place_lattice_structure K V ι b X hX _ hN).2.1,
    rkK_idealSmul hI]

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)`. Establish `hILfg` using `idealSmul_fg I hL`. Establish `hlat` using `(place_lattice_structure K V ι b X hX L hL).1`. Establish `hlatI` using `(place_lattice_structure K V ι b X hX _ hILfg).1`.

Rewrite using `[(slope_characterization (𝓞 K) V _ (realize b X) _ hlatI hIL0).2.1]`. Introduce `N hN`. Establish `hI' : I⁻¹ ≠ 0` using `inv_ne_zero hI`. Use `set N' := idealSmul ((I⁻¹ : FI) : Submodule (𝓞 K) K) N with hN'`. Establish `hN'L : N' ≤ L`.

Use `idealSmul_mono_right ((I⁻¹ : FI) : Submodule (𝓞 K) K) hN` as an intermediate fact. Rewrite `this` using `[idealSmul_inv_cancel hI]`. Then use the resulting hypothesis. Establish `hNeq : N = idealSmul (I : Submodule (𝓞 K) K) N'` using `(idealSmul_cancel_inv hI N).symm`. Establish `hN'fg : N'.FG` using `fg_of_le hL hN'L`. Establish `hch` using `((slope_characterization (𝓞 K) V _ (realize b X) L hlat hL0).2.1 (muMin (realize b X) L)).1 le_rfl N' hN'L`.

Rewrite using `[hNeq, deg_fractional b X hX hL hI, deg_fractional b X hX hN'fg hI, rk_fractional b X hX hL hI, rk_fractional b X hX hN'fg hI]`. Establish `r1` using `(place_lattice_structure K V ι b X hX L hL).2.1`. Establish `r2` using `(place_lattice_structure K V ι b X hX N' hN'fg).2.1`. Establish `hq : (Module.finrank ℚ K : ℝ) ≠ 0` using `(finrank_pos' (K := K)).ne'`. Establish `e1 : Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) * ((rk (realize b X) L : ℝ) - rk (realize b X) N') = ((rkK L : ℝ) - rkK N') * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ)`.

Rewrite using `[r1, r2]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use polynomial arithmetic with `[hch, e1]`.
-/
theorem muMin_fractional_ge (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) {I : FI}
    (hI : I ≠ 0) :
    muMin (realize b X) L - Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) /
      (Module.finrank ℚ K : ℝ) ≤ muMin (realize b X) (idealSmul (I : Submodule (𝓞 K) K) L) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  have hILfg := idealSmul_fg I hL
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hlatI := (place_lattice_structure K V ι b X hX _ hILfg).1
  rw [(slope_characterization (𝓞 K) V _ (realize b X) _ hlatI hIL0).2.1]
  intro N hN
  have hI' : I⁻¹ ≠ 0 := inv_ne_zero hI
  set N' := idealSmul ((I⁻¹ : FI) : Submodule (𝓞 K) K) N with hN'
  have hN'L : N' ≤ L := by
    have := idealSmul_mono_right ((I⁻¹ : FI) : Submodule (𝓞 K) K) hN
    rwa [idealSmul_inv_cancel hI] at this
  have hNeq : N = idealSmul (I : Submodule (𝓞 K) K) N' := (idealSmul_cancel_inv hI N).symm
  have hN'fg : N'.FG := fg_of_le hL hN'L
  have hch := ((slope_characterization (𝓞 K) V _ (realize b X) L hlat hL0).2.1
    (muMin (realize b X) L)).1 le_rfl N' hN'L
  rw [hNeq, deg_fractional b X hX hL hI, deg_fractional b X hX hN'fg hI,
    rk_fractional b X hX hL hI, rk_fractional b X hX hN'fg hI]
  have r1 := (place_lattice_structure K V ι b X hX L hL).2.1
  have r2 := (place_lattice_structure K V ι b X hX N' hN'fg).2.1
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos' (K := K)).ne'
  have e1 : Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) *
      ((rk (realize b X) L : ℝ) - rk (realize b X) N') =
      ((rkK L : ℝ) - rkK N') * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
    rw [r1, r2]; push_cast; field_simp
  nlinarith [hch, e1]

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h` using `muMin_fractional_ge b X hX (idealSmul_fg I hL) hIL0 (inv_ne_zero hI)`. Rewrite `h` using `[idealSmul_inv_cancel hI, log_absNorm_inv]`.

Establish `e : -Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) = -(Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ))` using `by ring`. Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `muMin_fractional_ge b X hX hL hL0 hI`.
-/
theorem muMin_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) {I : FI}
    (hI : I ≠ 0) :
    muMin (realize b X) (idealSmul (I : Submodule (𝓞 K) K) L) = muMin (realize b X) L -
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  apply le_antisymm
  · have h := muMin_fractional_ge b X hX (idealSmul_fg I hL) hIL0 (inv_ne_zero hI)
    rw [idealSmul_inv_cancel hI, log_absNorm_inv] at h
    have e : -Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        -(Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ)) := by ring
    rw [e] at h
    linarith
  · exact muMin_fractional_ge b X hX hL hL0 hI

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `muMaxDef_fractional_le b X hX hL hL0 hI`. Establish `h` using `muMaxDef_fractional_le b X hX (idealSmul_fg I hL) hIL0 (inv_ne_zero hI)`.

Rewrite `h` using `[idealSmul_inv_cancel hI, log_absNorm_inv]`. Establish `e : 2 * -Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) = -(2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ))` using `by ring`. Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem muMaxDef_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) {I : FI}
    (hI : I ≠ 0) :
    muMaxDef b X (idealSmul (I : Submodule (𝓞 K) K) L) = muMaxDef b X L -
      2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  apply le_antisymm
  · exact muMaxDef_fractional_le b X hX hL hL0 hI
  · have h := muMaxDef_fractional_le b X hX (idealSmul_fg I hL) hIL0 (inv_ne_zero hI)
    rw [idealSmul_inv_cancel hI, log_absNorm_inv] at h
    have e : 2 * -Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        -(2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ)) := by ring
    rw [e] at h
    linarith

end Mod

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX I hI M hM hM0`. Use `⟨idealSmul_fg I hM, muDef_fractional b X hX hM hM0 hI, muMaxDef_fractional b X hX hM hM0 hI, ?_⟩` and prove the remaining obligations. Unfold `muMinDef`. Rewrite using `[muMin_fractional b X hX hM hM0 hI]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ideal_scaling_holds : Formalism.HN.IdealScale := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX I hI M hM hM0
  refine ⟨idealSmul_fg I hM, muDef_fractional b X hX hM hM0 hI,
    muMaxDef_fractional b X hX hM hM0 hI, ?_⟩
  unfold muMinDef
  rw [muMin_fractional b X hX hM hM0 hI]
  ring

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX M N hM hNM hN0 hrk`. Conclude with `⟨muDef_index b X hX hM hNM hN0 hrk, muMaxDef_mono b X hX hM hNM hN0⟩`.
-/
theorem index_slope_formula : Formalism.HN.IndexMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX M N hM hNM hN0 hrk
  exact ⟨muDef_index b X hX hM hNM hN0 hrk, muMaxDef_mono b X hX hM hNM hN0⟩

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX I hI M N' hM hM0 hN' hN'0 hrk`. Establish `hfg` using `idealSmul_fg I hM`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← muMaxDef_fractional b X hX hM hM0 hI]`. Conclude with `muMaxDef_mono b X hX hfg hN' hN'0`.

Rewrite using `[muDef_index b X hX hfg hN' hN'0 (by rw [hrk, rkK_idealSmul hI]), muDef_fractional b X hX hM hM0 hI, rkK_idealSmul hI]`.
-/
theorem truncated_lattice_holds : Formalism.HN.CutLattice := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX I hI M N' hM hM0 hN' hN'0 hrk
  have hfg := idealSmul_fg I hM
  refine ⟨?_, ?_⟩
  · rw [← muMaxDef_fractional b X hX hM hM0 hI]
    exact muMaxDef_mono b X hX hfg hN' hN'0
  · rw [muDef_index b X hX hfg hN' hN'0 (by rw [hrk, rkK_idealSmul hI]),
      muDef_fractional b X hX hM hM0 hI, rkK_idealSmul hI]

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX j j' e e' M he he' hM hM0 hsp hsp'`. Take `⟨hrk, hj, -, -, h1⟩` from `log_covolume_slope_mu K V ι b X hX j e M he hM hM0 hsp`. Take `⟨-, -, -, -, h2⟩` from `log_covolume_slope_mu K V ι b X hX j' e' M he' hM hM0 hsp'`. Establish `hj' : (rkK M : ℝ) ≠ 0` using `by rw [hrk]; exact_mod_cast hj.ne'`. Rewrite `h2` using `[h1]`.

Use `(div_left_inj' hj').1 h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem covolume_basis_free : LcvBasisFree := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j j' e e' M he he' hM hM0 hsp hsp'
  obtain ⟨hrk, hj, -, -, h1⟩ := log_covolume_slope_mu K V ι b X hX j e M he hM hM0 hsp
  obtain ⟨-, -, -, -, h2⟩ := log_covolume_slope_mu K V ι b X hX j' e' M he' hM hM0 hsp'
  have hj' : (rkK M : ℝ) ≠ 0 := by rw [hrk]; exact_mod_cast hj.ne'
  rw [h1] at h2
  have := (div_left_inj' hj').1 h2
  linarith

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ M`. Take `⟨s, hsN, hspan, hli⟩` from `exists_linearIndependent K (M : Set V)`. Establish `hfin : s.Finite` using `hli.setFinite`. Set `_ : Fintype s` to `hfin.fintype`. Set `e : Fin (Fintype.card s) → V` to `fun i => ((Fintype.equivFin s).symm i : V)`.

Establish `he : LinearIndependent K e` using `hli.comp _ (Fintype.equivFin s).symm.injective`. Establish `hrange : Set.range e = s`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `((Fintype.equivFin s).symm i).2`. Introduce `hx; exact ⟨Fintype.equivFin s ⟨x, hx⟩, by simp [e]⟩`. Conclude with `⟨_, e, he, fun a => hsN ((Fintype.equivFin s).symm a).2, by rw [hrange, hspan]⟩`.
-/
theorem covolume_exists : LcvExists := by
  intro K V _ _ _ _ _ _ _ M
  obtain ⟨s, hsN, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
  have hfin : s.Finite := hli.setFinite
  let _ : Fintype s := hfin.fintype
  let e : Fin (Fintype.card s) → V := fun i => ((Fintype.equivFin s).symm i : V)
  have he : LinearIndependent K e := hli.comp _ (Fintype.equivFin s).symm.injective
  have hrange : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin s).symm i).2
    · intro hx; exact ⟨Fintype.equivFin s ⟨x, hx⟩, by simp [e]⟩
  exact ⟨_, e, he, fun a => hsN ((Fintype.equivFin s).symm a).2, by rw [hrange, hspan]⟩

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e he hj`. Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hfin0 : lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0`. Unfold `lcvFin`. Establish `: ∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI` using `p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) (Submodule.span (𝓞 K) (Set.range e))) = 0 := by`.

Introduce `p`. Unfold `lidx`. Rewrite using `[sub_self]`. Simplify using `only [this, Int.cast_zero, mul_zero, finsum_zero]`. Establish `hrk` using `HeightGram.rkK_span (K := K) e he`.

Establish `h0 : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [hrk]; exact hj)`. Take `⟨-, -, -, -, h1⟩` from `log_covolume_slope_mu K V ι b X hX j e _ he (Submodule.fg_span (Set.finite_range e)) h0 (Submodule.span_span_of_tower _ _ _)`. Use `⟨hfin0, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, hrk, lcv, hfin0, add_zero]`.
-/
theorem covolume_free_module : LcvFree := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e he hj
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hfin0 : lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0 := by
    unfold lcvFin
    have : ∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI := p.2.isPrime;
        lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) (Submodule.span (𝓞 K) (Set.range e))) = 0 := by
      intro p
      unfold lidx
      rw [sub_self]
    simp only [this, Int.cast_zero, mul_zero, finsum_zero]
  have hrk := HeightGram.rkK_span (K := K) e he
  have h0 : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥ := ne_bot_of_rkK_pos (by rw [hrk]; exact hj)
  obtain ⟨-, -, -, -, h1⟩ := log_covolume_slope_mu K V ι b X hX j e _ he
    (Submodule.fg_span (Set.finite_range e)) h0 (Submodule.span_span_of_tower _ _ _)
  refine ⟨hfin0, ?_⟩
  rw [h1, hrk, lcv, hfin0, add_zero]

section BaseChange

open scoped Matrix

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Set `φ : V →+ (ι → ℂ)` to `AddMonoidHom.mk' (fcoord b X v) (fcoord_add b X v)`. Establish `h : φ (∑ k, c k • e k) = ∑ k, φ (c k • e k)` using `map_sum φ _ _`. Establish `h2 : ∀ x, φ x = fcoord b X v x` using `fun _ => rfl`. Simplify using `only [h2] at h`. Rewrite using `[h]`.

Conclude with `Finset.sum_congr rfl fun k _ => HeightGram.fcoord_smul b X v (c k) (e k)`.
-/
theorem fcoord_sum (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    {j : ℕ} (c : Fin j → K) (e : Fin j → V) :
    fcoord b X v (∑ k, c k • e k) = ∑ k, v.embedding (c k) • fcoord b X v (e k) := by
  let φ : V →+ (ι → ℂ) := AddMonoidHom.mk' (fcoord b X v) (fcoord_add b X v)
  have h : φ (∑ k, c k • e k) = ∑ k, φ (c k • e k) := map_sum φ _ _
  have h2 : ∀ x, φ x = fcoord b X v x := fun _ => rfl
  simp only [h2] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => HeightGram.fcoord_smul b X v (c k) (e k)

/- English proof (translation)
Set `Mv : Matrix ι (Fin j) ℂ` to `Matrix.of fun i a => fcoord b X v (e a) i`. Establish `hG : gramPl b X v e = Mvᴴ * Mv`. Use extensionality with `a c`. Simplify using `[gramPl, majAt, Mv, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Establish `hG' : gramPl b X v (fun a => ∑ c, g c a • e c) = (Mv * g.map v.embedding)ᴴ * (Mv * g.map v.embedding)`.

Use extensionality with `a c`. Simplify using `only [gramPl, majAt, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, fcoord_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Mv, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[hG', hG, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gramPl_baseChange (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K) :
    gramPl b X v (fun a => ∑ c, g c a • e c) =
      (g.map v.embedding)ᴴ * gramPl b X v e * g.map v.embedding := by
  let Mv : Matrix ι (Fin j) ℂ := Matrix.of fun i a => fcoord b X v (e a) i
  have hG : gramPl b X v e = Mvᴴ * Mv := by
    ext a c
    simp [gramPl, majAt, Mv, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hG' : gramPl b X v (fun a => ∑ c, g c a • e c) =
      (Mv * g.map v.embedding)ᴴ * (Mv * g.map v.embedding) := by
    ext a c
    simp only [gramPl, majAt, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      fcoord_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Mv, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hG', hG, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `hdet : (g.map v.embedding).det = v.embedding g.det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Establish `hw : (gramPl b X v e).det = (((gramPl b X v e).det.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [him])`. Rewrite using `[gramPl_baseChange, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet, hw]`. Establish `e1 : star (v.embedding g.det) * (((gramPl b X v e).det.re : ℝ) : ℂ) * v.embedding g.det = ((Complex.normSq (v.embedding g.det) * (gramPl b X v e).det.re : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, Complex.ofReal_re, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq, Complex.ofReal_re]`.
-/
theorem det_gramPl_baseChange (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K)
    (him : (gramPl b X v e).det.im = 0) :
    (gramPl b X v (fun a => ∑ c, g c a • e c)).det.re =
      v g.det ^ 2 * (gramPl b X v e).det.re := by
  have hdet : (g.map v.embedding).det = v.embedding g.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hw : (gramPl b X v e).det = (((gramPl b X v e).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  rw [gramPl_baseChange, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet, hw]
  have e1 : star (v.embedding g.det) * (((gramPl b X v e).det.re : ℝ) : ℂ) * v.embedding g.det =
      ((Complex.normSq (v.embedding g.det) * (gramPl b X v e).det.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [e1, Complex.ofReal_re, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq,
    Complex.ofReal_re]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Establish `h : e k = ∑ a, g⁻¹ a k • ∑ c, g c a • e c`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ c, ∑ a, (g⁻¹ a k * g c a) • e c = ((g * g⁻¹) c k) • e c`.

Introduce `c`. Rewrite using `[← Finset.sum_smul, Matrix.mul_apply]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Simplify using `only [this, Matrix.mul_nonsing_inv g hg, Matrix.one_apply]`.

Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))`.
-/
theorem span_baseChange {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K)
    (hg : IsUnit g.det) :
    Submodule.span K (Set.range fun a => ∑ c, g c a • e c) = Submodule.span K (Set.range e) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have h : e k = ∑ a, g⁻¹ a k • ∑ c, g c a • e c := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have : ∀ c, ∑ a, (g⁻¹ a k * g c a) • e c = ((g * g⁻¹) c k) • e c := by
        intro c
        rw [← Finset.sum_smul, Matrix.mul_apply]
        congr 1
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _
      simp only [this, Matrix.mul_nonsing_inv g hg, Matrix.one_apply]
      simp
    rw [h]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))

/- English proof (translation)
Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_baseChange e g hg]`. Conclude with `linearIndependent_iff_card_eq_finrank_span.1 he`.
-/
theorem linInd_baseChange {j : ℕ} (e : Fin j → V) (he : LinearIndependent K e)
    (g : Matrix (Fin j) (Fin j) K) (hg : IsUnit g.det) :
    LinearIndependent K (fun a => ∑ c, g c a • e c) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_baseChange e g hg]
  exact linearIndependent_iff_card_eq_finrank_span.1 he

end BaseChange

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e g M he hg hM hM0 hsp`. Establish `hd : g.det ≠ 0` using `hg.ne_zero`. Establish `hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ)`. Rewrite using `[sizeMu_finrank_eq K]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hf : (nPl K : ℝ) ≠ 0`. Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this.ne'` after adjusting the coercions. Establish `hprod : ∏ v : InfinitePlace K, v g.det ^ 2 = |((Algebra.norm ℚ g.det : ℚ) : ℝ)|`.

Establish `h` using `InfinitePlace.prod_eq_abs_norm g.det`. Rewrite using `[← Rat.cast_abs, ← h]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))]`. Establish `hinf : lcvInf b X (fun a => ∑ c, g c a • e c) = lcvInf b X e + 2 / (Module.finrank ℚ K : ℝ) * Real.log |((Algebra.norm ℚ g.det : ℚ) : ℝ)|`.

Unfold `lcvInf`. Establish `h1 : ∀ v : InfinitePlace K, Real.log (gramPl b X v (fun a => ∑ c, g c a • e c)).det.re = Real.log (v g.det ^ 2) + Real.log (gramPl b X v e).det.re`. Introduce `v`. Take `⟨hp, him⟩` from `gram_pos b X hX e he v`. Rewrite using `[det_gramPl_baseChange b X v e g him, Real.log_mul _ hp.ne']`.

Conclude with `pow_ne_zero _ ((map_ne_zero v).2 hd)`. Simplify using `only [h1]`. Rewrite using `[Finset.sum_add_distrib, ← Real.log_prod (fun v _ => pow_ne_zero _ ((map_ne_zero v).2 hd)), hprod, hn]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨hinf, ?_⟩` and prove the remaining obligations. Establish `hfree` using `covolume_basis_free K V ι b X hX j j e (fun a => ∑ c, g c a • e c) M he (linInd_baseChange e he g hg) hM hM0 hsp (by rw [span_baseChange e g hg, hsp])`. Unfold `lcv at hfree`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem covolume_base_change : LcvBaseChange := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e g M he hg hM hM0 hsp
  have hd : g.det ≠ 0 := hg.ne_zero
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    rw [sizeMu_finrank_eq K]; push_cast; ring
  have hf : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hprod : ∏ v : InfinitePlace K, v g.det ^ 2 = |((Algebra.norm ℚ g.det : ℚ) : ℝ)| := by
    have h := InfinitePlace.prod_eq_abs_norm g.det
    rw [← Rat.cast_abs, ← h]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex v))]
  have hinf : lcvInf b X (fun a => ∑ c, g c a • e c) = lcvInf b X e +
      2 / (Module.finrank ℚ K : ℝ) * Real.log |((Algebra.norm ℚ g.det : ℚ) : ℝ)| := by
    unfold lcvInf
    have h1 : ∀ v : InfinitePlace K,
        Real.log (gramPl b X v (fun a => ∑ c, g c a • e c)).det.re =
          Real.log (v g.det ^ 2) + Real.log (gramPl b X v e).det.re := by
      intro v
      obtain ⟨hp, him⟩ := gram_pos b X hX e he v
      rw [det_gramPl_baseChange b X v e g him, Real.log_mul _ hp.ne']
      exact pow_ne_zero _ ((map_ne_zero v).2 hd)
    simp only [h1]
    rw [Finset.sum_add_distrib, ← Real.log_prod (fun v _ =>
      pow_ne_zero _ ((map_ne_zero v).2 hd)), hprod, hn]
    field_simp
    ring
  refine ⟨hinf, ?_⟩
  have hfree := covolume_basis_free K V ι b X hX j j e (fun a => ∑ c, g c a • e c) M he
    (linInd_baseChange e he g hg) hM hM0 hsp (by rw [span_baseChange e g hg, hsp])
  unfold lcv at hfree
  linarith

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b j e I he hj hI`. Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Set `X : InfinitePlace K → Matrix ι ι ℂ` to `fun _ => 1`. Establish `hX : ∀ v, IsUnit (X v).det` using `fun v => by simp [X]`. Establish `hE : (Submodule.span (𝓞 K) (Set.range e)).FG` using `Submodule.fg_span (Set.finite_range e)`.

Establish `hrk` using `HeightGram.rkK_span (K := K) e he`. Establish `h0 : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [hrk]; exact hj)`. Establish `hI0 : idealSmul (I : Submodule (𝓞 K) K) (Submodule.span (𝓞 K) (Set.range e)) ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI, hrk]; exact hj)`. Take `⟨hr, -, -, -, h1⟩` from `log_covolume_slope_mu K V ι b X hX j e _ he (idealSmul_fg I hE) hI0 (by rw [span_idealSmul hI, Submodule.span_span_of_tower])`. Establish `h2` using `muDef_fractional b X hX hE h0 hI`.

Establish `h3` using `(covolume_free_module K V ι b X hX j e he hj).2`. Rewrite `h2` using `[h1, h3, hr, lcv]`. Establish `hj' : (j : ℝ) ≠ 0` using `by exact_mod_cast hj.ne'`. Establish `hq : (Module.finrank ℚ K : ℝ) ≠ 0` using `(finrank_pos' (K := K)).ne'`. Clear denominators, using `at h2 ⊢` for the nonvanishing conditions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem covolume_ideal : LcvIdeal := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b j e I he hj hI
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  let X : InfinitePlace K → Matrix ι ι ℂ := fun _ => 1
  have hX : ∀ v, IsUnit (X v).det := fun v => by simp [X]
  have hE : (Submodule.span (𝓞 K) (Set.range e)).FG := Submodule.fg_span (Set.finite_range e)
  have hrk := HeightGram.rkK_span (K := K) e he
  have h0 : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥ := ne_bot_of_rkK_pos (by rw [hrk]; exact hj)
  have hI0 : idealSmul (I : Submodule (𝓞 K) K) (Submodule.span (𝓞 K) (Set.range e)) ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI, hrk]; exact hj)
  obtain ⟨hr, -, -, -, h1⟩ := log_covolume_slope_mu K V ι b X hX j e _ he (idealSmul_fg I hE) hI0
    (by rw [span_idealSmul hI, Submodule.span_span_of_tower])
  have h2 := muDef_fractional b X hX hE h0 hI
  have h3 := (covolume_free_module K V ι b X hX j e he hj).2
  rw [h1, h3, hr, lcv] at h2
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos' (K := K)).ne'
  field_simp at h2 ⊢
  linarith

/- English proof (translation)
Set `_ : StarRing (CyclotomicField 3 ℚ)` to `starRingOfComm`. Establish `hcyc : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)` using `CyclotomicField.isCyclotomicExtension 3 ℚ`. Establish `hTC : IsTotallyComplex (CyclotomicField 3 ℚ)` using `IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) (CyclotomicField 3 ℚ) (by norm_num)`. Establish `he : LinearIndependent (CyclotomicField 3 ℚ) (fun _ : Fin 1 => (1 : CyclotomicField 3 ℚ))` using `LinearIndependent.of_subsingleton 0 one_ne_zero`. Establish `hI : (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ))) (2 : CyclotomicField 3 ℚ)) ≠ 0`.

Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `two_ne_zero`. Rewrite using `[covolume_ideal (CyclotomicField 3 ℚ) (CyclotomicField 3 ℚ) Unit (Basis.singleton Unit (CyclotomicField 3 ℚ)) 1 _ _ he one_pos hI, FractionalIdeal.absNorm_span_singleton]`. Establish `hn : Algebra.norm ℚ (2 : CyclotomicField 3 ℚ) = 2 ^ Module.finrank ℚ (CyclotomicField 3 ℚ)`. Use `Algebra.norm_algebraMap (S := CyclotomicField 3 ℚ) (2 : ℚ)` as an intermediate fact.

Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `hpos : 0 < Module.finrank ℚ (CyclotomicField 3 ℚ)` using `Module.finrank_pos`. Establish `h1 : (1 : ℝ) < ((|Algebra.norm ℚ (2 : CyclotomicField 3 ℚ)| : ℚ) : ℝ)`. Rewrite using `[hn, abs_of_pos (by positivity)]`. Use `push_cast`.

Conclude with `one_lt_pow₀ one_lt_two hpos.ne'`. Establish `h2` using `Real.log_pos h1`. Establish `h3 : (0 : ℝ) < (Module.finrank ℚ (CyclotomicField 3 ℚ) : ℝ)` using `by exact_mod_cast hpos`. Check the signs of the components of the expression.
-/
theorem lcv_nonvacuous :
    letI : StarRing (CyclotomicField 3 ℚ) := starRingOfComm
    0 < lcvFin (K := CyclotomicField 3 ℚ) (V := CyclotomicField 3 ℚ) (fun _ : Fin 1 => 1)
      (idealSmul ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
        (2 : CyclotomicField 3 ℚ) : FractionalIdeal (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
          (CyclotomicField 3 ℚ)) : Submodule (𝓞 (CyclotomicField 3 ℚ)) (CyclotomicField 3 ℚ))
        (Submodule.span (𝓞 (CyclotomicField 3 ℚ)) (Set.range fun _ : Fin 1 => 1))) := by
  let _ : StarRing (CyclotomicField 3 ℚ) := starRingOfComm
  have hcyc : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hTC : IsTotallyComplex (CyclotomicField 3 ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) (CyclotomicField 3 ℚ) (by norm_num)
  have he : LinearIndependent (CyclotomicField 3 ℚ)
      (fun _ : Fin 1 => (1 : CyclotomicField 3 ℚ)) :=
    LinearIndependent.of_subsingleton 0 one_ne_zero
  have hI : (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
      (2 : CyclotomicField 3 ℚ)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact two_ne_zero
  rw [covolume_ideal (CyclotomicField 3 ℚ) (CyclotomicField 3 ℚ) Unit
    (Basis.singleton Unit (CyclotomicField 3 ℚ)) 1 _ _ he one_pos hI,
    FractionalIdeal.absNorm_span_singleton]
  have hn : Algebra.norm ℚ (2 : CyclotomicField 3 ℚ) =
      2 ^ Module.finrank ℚ (CyclotomicField 3 ℚ) := by
    have := Algebra.norm_algebraMap (S := CyclotomicField 3 ℚ) (2 : ℚ)
    rwa [map_ofNat] at this
  have hpos : 0 < Module.finrank ℚ (CyclotomicField 3 ℚ) := Module.finrank_pos
  have h1 : (1 : ℝ) < ((|Algebra.norm ℚ (2 : CyclotomicField 3 ℚ)| : ℚ) : ℝ) := by
    rw [hn, abs_of_pos (by positivity)]
    push_cast
    exact one_lt_pow₀ one_lt_two hpos.ne'
  have h2 := Real.log_pos h1
  have h3 : (0 : ℝ) < (Module.finrank ℚ (CyclotomicField 3 ℚ) : ℝ) := by exact_mod_cast hpos
  positivity

end Formalism.LFunctionChainParameters.LLcv
