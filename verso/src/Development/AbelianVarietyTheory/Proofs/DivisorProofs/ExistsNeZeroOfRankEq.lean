import Mathlib

namespace GlobalTheory.SemisimpleCount

variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]

def killed (I : Set Rg) (M : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] : Submodule ℂ M where
  carrier := {m | ∀ x ∈ I, x • m = 0}
  add_mem' := fun ha hb x hx => by rw [smul_add, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => smul_zero x
  smul_mem' := fun c m hm x hx => by rw [smul_comm, hm x hx, smul_zero]

section
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_killed {m : M} : m ∈ killed I M ↔ ∀ x ∈ I, x • m = 0 := Iff.rfl

/- English proof (translation)
Introduce `x hx`. Rewrite using `[← map_smul, ha x hx, map_zero]`.
-/
theorem map_mem_killed {A B : Type} [AddCommGroup A] [Module Rg A] [AddCommGroup B] [Module Rg B]
    (f : A →ₗ[Rg] B) {a : A} (ha : ∀ x ∈ I, x • a = 0) : ∀ x ∈ I, x • f a = 0 := by
  intro x hx
  rw [← map_smul, ha x hx, map_zero]

/- English proof (translation)
Use `LinearMap.rank_le_of_injective ((f.restrictScalars ℂ).restrict (p := killed I M) (q := killed I N) (fun m hm => map_mem_killed I f hm)) ?_` and prove the remaining obligations. Introduce `a b hab`. Conclude with `Subtype.ext (hf (congrArg Subtype.val hab))`.
-/
theorem rank_killed_le (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (killed I M) ≤ Module.rank ℂ (killed I N) := by
  refine LinearMap.rank_le_of_injective
    ((f.restrictScalars ℂ).restrict (p := killed I M) (q := killed I N)
      (fun m hm => map_mem_killed I f hm)) ?_
  intro a b hab
  exact Subtype.ext (hf (congrArg Subtype.val hab))

/- English proof (translation)
The claim follows from `le_antisymm (rank_killed_le I e.toLinearMap e.injective) (rank_killed_le I e.symm.toLinearMap e.symm.injective)`.
-/
theorem rank_killed_congr (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I N) :=
  le_antisymm (rank_killed_le I e.toLinearMap e.injective)
    (rank_killed_le I e.symm.toLinearMap e.symm.injective)

/- English proof (translation)
Establish `h : killed I (M × N) = (killed I M).prod (killed I N)`. Use extensionality with `⟨a, b⟩`. Simplify using `only [mem_killed, Submodule.mem_prod, Prod.smul_mk, Prod.mk_eq_zero]`. Conclude with `⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩, fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩`. Rewrite using `[h, ← rank_prod']`.

Use `LinearEquiv.rank_eq { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩) invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }` and prove the remaining obligations.
-/
theorem rank_killed_prod :
    Module.rank ℂ (killed I (M × N)) =
      Module.rank ℂ (killed I M) + Module.rank ℂ (killed I N) := by
  have h : killed I (M × N) = (killed I M).prod (killed I N) := by
    ext ⟨a, b⟩
    simp only [mem_killed, Submodule.mem_prod, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  rw [h, ← rank_prod']
  refine LinearEquiv.rank_eq
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/- English proof (translation)
Rewrite using `[← rank_killed_congr I (Submodule.prodEquivOfIsCompl U V h), rank_killed_prod]`.
-/
theorem rank_killed_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I U) + Module.rank ℂ (killed I V) := by
  rw [← rank_killed_congr I (Submodule.prodEquivOfIsCompl U V h), rank_killed_prod]

variable {S : Type} [AddCommGroup S] [Module Rg S]

/- English proof (translation)
Use `LinearMap.rank_le_of_injective { toFun := fun g => f.comp g map_add' := fun a b => by ext; simp map_smul' := fun c a => by` and prove the remaining obligations. Use extensionality with `s`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]`. Conclude with `(f.restrictScalars ℂ).map_smul c (a s) } ?_`. Introduce `a b hab`.

Use extensionality with `s`. Conclude with `hf (LinearMap.congr_fun hab s)`.
-/
theorem rank_hom_le (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (S →ₗ[Rg] N) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => f.comp g
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by
        ext s
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact (f.restrictScalars ℂ).map_smul c (a s) } ?_
  intro a b hab
  ext s
  exact hf (LinearMap.congr_fun hab s)

/- English proof (translation)
The claim follows from `le_antisymm (rank_hom_le e.toLinearMap e.injective) (rank_hom_le e.symm.toLinearMap e.symm.injective)`.
-/
theorem rank_hom_congr (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N) :=
  le_antisymm (rank_hom_le e.toLinearMap e.injective)
    (rank_hom_le e.symm.toLinearMap e.symm.injective)

/- English proof (translation)
Rewrite using `[← rank_hom_congr (Submodule.prodEquivOfIsCompl U V h), ← rank_prod']`. Conclude with `(LinearMap.prodEquiv ℂ).rank_eq.symm`.
-/
theorem rank_hom_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] U) + Module.rank ℂ (S →ₗ[Rg] V) := by
  rw [← rank_hom_congr (Submodule.prodEquivOfIsCompl U V h), ← rank_prod']
  exact (LinearMap.prodEquiv ℂ).rank_eq.symm

/- English proof (translation)
The claim follows from `LinearEquiv.rank_eq { toFun := fun g => g.comp e.symm.toLinearMap invFun := fun g => g.comp e.toLinearMap map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun g => by ext; simp right_inv := fun g => by ext; simp }`.
-/
theorem rank_hom_congr_left {S' : Type} [AddCommGroup S'] [Module Rg S'] (e : S ≃ₗ[Rg] S') :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S' →ₗ[Rg] M) :=
  LinearEquiv.rank_eq
    { toFun := fun g => g.comp e.symm.toLinearMap
      invFun := fun g => g.comp e.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }

/- English proof (translation)
The claim follows from `(LinearMap.injective_or_eq_zero f).resolve_right hf`.
-/
theorem injective_of_ne_zero {A : Type} [AddCommGroup A] [Module Rg A] [IsSimpleModule Rg S]
    {f : S →ₗ[Rg] A} (hf : f ≠ 0) : Function.Injective f :=
  (LinearMap.injective_or_eq_zero f).resolve_right hf

/- English proof (translation)
Use `LinearMap.rank_le_of_injective { toFun := fun g => ⟨g s, map_mem_killed I g hI⟩ map_add' := fun a b => rfl map_smul' := fun c a => rfl } ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h`. Establish `h0 : a s = 0` using `congrArg Subtype.val ha`.

Conclude with `hs (injective_of_ne_zero h (h0.trans (map_zero a).symm))`.
-/
theorem rank_hom_le_killed [IsSimpleModule Rg S] {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (killed I M) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => ⟨g s, map_mem_killed I g hI⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl } ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h0 : a s = 0 := congrArg Subtype.val ha
  exact hs (injective_of_ne_zero h (h0.trans (map_zero a).symm))

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Use `push_neg at hb`. Conclude with `ha (rank_zero_iff_forall_zero.1 (h.trans (rank_zero_iff_forall_zero.2 hb)) a)`.
-/
theorem exists_ne_zero_of_rank_eq {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (h : Module.rank ℂ A = Module.rank ℂ B) {a : A} (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 := by
  by_contra hb
  push_neg at hb
  exact ha (rank_zero_iff_forall_zero.1 (h.trans (rank_zero_iff_forall_zero.2 hb)) a)

/- English proof (translation)
Establish `hj : a ∉ Module.jacobson Rg A`. Rewrite using `[IsSemisimpleModule.jacobson_eq_bot]`. Simplify using `using ha`. Simplify using `only [Module.jacobson, Submodule.mem_sInf, not_forall] at hj`. Take `⟨P, hP, haP⟩` from `hj`.

Take `⟨U, hU⟩` from `exists_isCompl P`. Establish `e` using `Submodule.quotientEquivOfIsCompl P U hU`. Use `haveI : IsSimpleModule Rg (A ⧸ P) := isSimpleModule_iff_isCoatom.2 hP`. Use `⟨U, IsSimpleModule.congr e.symm, e (P.mkQ a), ?_, ?_⟩` and prove the remaining obligations. Simplify using `using haP`.

Conclude with `map_mem_killed I (e.toLinearMap.comp P.mkQ) hI`.
-/
theorem exists_simple {A : Type} [AddCommGroup A] [Module Rg A] [IsSemisimpleModule Rg A]
    {a : A} (ha : a ≠ 0) (hI : ∀ x ∈ I, x • a = 0) :
    ∃ U : Submodule Rg A, IsSimpleModule Rg U ∧ ∃ u : U, u ≠ 0 ∧ ∀ x ∈ I, x • u = 0 := by
  have hj : a ∉ Module.jacobson Rg A := by
    rw [IsSemisimpleModule.jacobson_eq_bot]
    simpa using ha
  simp only [Module.jacobson, Submodule.mem_sInf, not_forall] at hj
  obtain ⟨P, hP, haP⟩ := hj
  obtain ⟨U, hU⟩ := exists_isCompl P
  have e := Submodule.quotientEquivOfIsCompl P U hU
  haveI : IsSimpleModule Rg (A ⧸ P) := isSimpleModule_iff_isCoatom.2 hP
  refine ⟨U, IsSimpleModule.congr e.symm, e (P.mkQ a), ?_, ?_⟩
  · simpa using haP
  · exact map_mem_killed I (e.toLinearMap.comp P.mkQ) hI

end

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `M N _ _ _ _ _ _ _ _ _ _ hn H`. Establish `sub_ne : ∀ {A : Type} [AddCommGroup A] [Module Rg A] (U : Submodule Rg A) (u : U), u ≠ 0 → U.subtype ≠ 0`. Introduce `A _ _ U u hu h`.

Conclude with `hu (Subtype.ext (LinearMap.congr_fun h u))`. Distinguish the cases in `h0 : ∀ m : killed I M, m = 0`. Rewrite using `[← hn, rank_zero_iff_forall_zero.2 h0, rank_zero_iff_forall_zero]`. Introduce `a`. Assume the negation of the conclusion as `ha`.

Take `⟨U, hU, u, hu, hI⟩` from `exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2`. Take `⟨f, hf⟩` from `exists_ne_zero_of_rank_eq (H U u hu hI).symm (sub_ne U u hu)`. Establish `h1 : f u = 0` using `congrArg Subtype.val (h0 ⟨f u, map_mem_killed I f hI⟩)`. Conclude with `hu (injective_of_ne_zero hf (h1.trans (map_zero f).symm))`. Use `push_neg at h0`.

Take `⟨a, ha⟩` from `h0`. Take `⟨U, hU, u, hu, hI⟩` from `exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2`. Take `⟨f, hf⟩` from `exists_ne_zero_of_rank_eq (H U u hu hI) (sub_ne U u hu)`. Establish `e : U ≃ₗ[Rg] LinearMap.range f` using `LinearEquiv.ofInjective f (injective_of_ne_zero hf)`. Take `⟨M', hM'⟩` from `exists_isCompl U`.

Take `⟨N', hN'⟩` from `exists_isCompl (LinearMap.range f)`. Establish `hM` using `rank_killed_compl I hM'`. Rewrite `hM` using `[hn]`. Establish `hUf : Module.rank ℂ (killed I U) < Cardinal.aleph0` using `lt_of_le_of_lt (hM ▸ le_self_add) (Cardinal.natCast_lt_aleph0 (n := n))`. Establish `hMf : Module.rank ℂ (killed I M') < Cardinal.aleph0` using `lt_of_le_of_lt (hM ▸ le_add_self) (Cardinal.natCast_lt_aleph0 (n := n))`.

Take `⟨k, hk⟩` from `Cardinal.lt_aleph0.1 hUf`. Take `⟨l, hl⟩` from `Cardinal.lt_aleph0.1 hMf`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Use `rank_zero_iff_forall_zero.1 (hk.trans Nat.cast_zero) ⟨u, hI⟩` as an intermediate fact.

Conclude with `hu (congrArg Subtype.val this)`. Establish `hkl : n = k + l`. Rewrite `hM` using `[hk, hl]`. Conclude with `hM` after adjusting the coercions. Establish `hN` using `ih l (by omega) M' N' hl (by`.

Introduce `S _ _ _ s hs hsI`. Establish `h` using `H S s hs hsI`. Rewrite `h` using `[rank_hom_compl hM', rank_hom_compl hN', ← rank_hom_congr e]`. Establish `hfin : Module.rank ℂ (S →ₗ[Rg] U) < Cardinal.aleph0` using `lt_of_le_of_lt (rank_hom_le_killed I hs hsI) hUf`. Conclude with `Cardinal.eq_of_add_eq_add_left h hfin)`.

Rewrite using `[rank_killed_compl I hN', ← rank_killed_congr I e, hk, hN, hkl, Nat.cast_add]`.
-/
theorem rank_killed_eq (I : Set Rg) (n : ℕ) :
    ∀ (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
    [IsSemisimpleModule Rg M] [IsSemisimpleModule Rg N],
    Module.rank ℂ (killed I M) = n →
    (∀ (S : Type) [AddCommGroup S] [Module Rg S] [IsSimpleModule Rg S] (s : S), s ≠ 0 →
      (∀ x ∈ I, x • s = 0) → Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N)) →
    Module.rank ℂ (killed I N) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ hn H
  have sub_ne : ∀ {A : Type} [AddCommGroup A] [Module Rg A] (U : Submodule Rg A) (u : U),
      u ≠ 0 → U.subtype ≠ 0 := by
    intro A _ _ U u hu h
    exact hu (Subtype.ext (LinearMap.congr_fun h u))
  by_cases h0 : ∀ m : killed I M, m = 0
  · rw [← hn, rank_zero_iff_forall_zero.2 h0, rank_zero_iff_forall_zero]
    intro a
    by_contra ha
    obtain ⟨U, hU, u, hu, hI⟩ := exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2
    obtain ⟨f, hf⟩ := exists_ne_zero_of_rank_eq (H U u hu hI).symm (sub_ne U u hu)
    have h1 : f u = 0 := congrArg Subtype.val (h0 ⟨f u, map_mem_killed I f hI⟩)
    exact hu (injective_of_ne_zero hf (h1.trans (map_zero f).symm))
  · push_neg at h0
    obtain ⟨a, ha⟩ := h0
    obtain ⟨U, hU, u, hu, hI⟩ := exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2
    obtain ⟨f, hf⟩ := exists_ne_zero_of_rank_eq (H U u hu hI) (sub_ne U u hu)
    have e : U ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f (injective_of_ne_zero hf)
    obtain ⟨M', hM'⟩ := exists_isCompl U
    obtain ⟨N', hN'⟩ := exists_isCompl (LinearMap.range f)
    have hM := rank_killed_compl I hM'
    rw [hn] at hM
    have hUf : Module.rank ℂ (killed I U) < Cardinal.aleph0 :=
      lt_of_le_of_lt (hM ▸ le_self_add) (Cardinal.natCast_lt_aleph0 (n := n))
    have hMf : Module.rank ℂ (killed I M') < Cardinal.aleph0 :=
      lt_of_le_of_lt (hM ▸ le_add_self) (Cardinal.natCast_lt_aleph0 (n := n))
    obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 hUf
    obtain ⟨l, hl⟩ := Cardinal.lt_aleph0.1 hMf
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := rank_zero_iff_forall_zero.1 (hk.trans Nat.cast_zero) ⟨u, hI⟩
      exact hu (congrArg Subtype.val this)
    have hkl : n = k + l := by
      rw [hk, hl] at hM
      exact_mod_cast hM
    have hN := ih l (by omega) M' N' hl (by
      intro S _ _ _ s hs hsI
      have h := H S s hs hsI
      rw [rank_hom_compl hM', rank_hom_compl hN', ← rank_hom_congr e] at h
      have hfin : Module.rank ℂ (S →ₗ[Rg] U) < Cardinal.aleph0 :=
        lt_of_le_of_lt (rank_hom_le_killed I hs hsI) hUf
      exact Cardinal.eq_of_add_eq_add_left h hfin)
    rw [rank_killed_compl I hN', ← rank_killed_congr I e, hk, hN, hkl, Nat.cast_add]

/- English proof (translation)
Introduce `Rg _ _ M N _ _ _ _ _ _ _ _ _ _ I FM FN hM hN hFM hFN fM fN HM HN`. Take `rfl : FM = killed I M` from `Submodule.ext hFM`. Take `rfl : FN = killed I N` from `Submodule.ext hFN`. Establish `key` using `rank_killed_eq I (Module.finrank ℂ (killed I M)) M N (Module.finrank_eq_rank ℂ _).symm (by`. Introduce `S _ _ _ s hs hI`.

Distinguish the cases in `h1 : ∃ f : S →ₗ[Rg] M, f ≠ 0`. Take `⟨f, hf⟩` from `h1`. Establish `hi` using `injective_of_ne_zero hf`. Establish `e : S ≃ₗ[Rg] LinearMap.range f` using `LinearEquiv.ofInjective f hi`. Rewrite using `[rank_hom_congr_left e, rank_hom_congr_left e]`.

Conclude with `HM _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩, fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩`. Distinguish the cases in `h2 : ∃ f : S →ₗ[Rg] N, f ≠ 0`. Take `⟨f, hf⟩` from `h2`. Establish `hi` using `injective_of_ne_zero hf`. Establish `e : S ≃ₗ[Rg] LinearMap.range f` using `LinearEquiv.ofInjective f hi`.

Rewrite using `[rank_hom_congr_left e, rank_hom_congr_left e]`. Conclude with `HN _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩, fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩`. Use `push_neg at h1 h2`. Rewrite using `[rank_zero_iff_forall_zero.2 h1, rank_zero_iff_forall_zero.2 h2])`. Conclude with `(Module.finrank_eq_of_rank_eq key).symm`.
-/
theorem finrank_killed_eq : ∀ (Rg : Type) [Ring Rg] [Algebra ℂ Rg] (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M] [IsScalarTower ℂ Rg M] [SMulCommClass Rg ℂ M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N] [SMulCommClass Rg ℂ N] (I : Set Rg) (FM : Submodule ℂ M) (FN : Submodule ℂ N), IsSemisimpleModule Rg M → IsSemisimpleModule Rg N → (∀ m, m ∈ FM ↔ ∀ x ∈ I, x • m = 0) → (∀ n, n ∈ FN ↔ ∀ x ∈ I, x • n = 0) → FiniteDimensional ℂ FM → FiniteDimensional ℂ FN → (∀ U : Submodule Rg M, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FM) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → (∀ U : Submodule Rg N, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FN) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → Module.finrank ℂ FM = Module.finrank ℂ FN := by
  intro Rg _ _ M N _ _ _ _ _ _ _ _ _ _ I FM FN hM hN hFM hFN fM fN HM HN
  obtain rfl : FM = killed I M := Submodule.ext hFM
  obtain rfl : FN = killed I N := Submodule.ext hFN
  have key := rank_killed_eq I (Module.finrank ℂ (killed I M)) M N
    (Module.finrank_eq_rank ℂ _).symm (by
      intro S _ _ _ s hs hI
      by_cases h1 : ∃ f : S →ₗ[Rg] M, f ≠ 0
      · obtain ⟨f, hf⟩ := h1
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HM _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      by_cases h2 : ∃ f : S →ₗ[Rg] N, f ≠ 0
      · obtain ⟨f, hf⟩ := h2
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HN _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      push_neg at h1 h2
      rw [rank_zero_iff_forall_zero.2 h1, rank_zero_iff_forall_zero.2 h2])
  exact (Module.finrank_eq_of_rank_eq key).symm

end GlobalTheory.SemisimpleCount
