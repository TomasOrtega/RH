import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTwistedNormOneMulCardFixedUnitsStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.NormSurj

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_galAct (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incl, gal]`.
-/
theorem map_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  simp [incl, gal]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx, map_incl]`. Conclude with `Algebra.subset_adjoin rfl`.

Consider the case `algebraMap r`. Establish `: (algebraMap F' (Matrix (Fin n) (Fin n) F') r).map t = algebraMap F' _ (t r)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Matrix.map_add _ (map_add t)]`. Conclude with `Subalgebra.add_mem _ hx hy`.

Consider the case `mul x y _ _ hx hy`. Use `Matrix.map_mul (L := x) (M := y) (f := (t : F' →+* F'))` as an intermediate fact. Use `erw [this]`. Conclude with `Subalgebra.mul_mem _ hx hy`.
-/
theorem adjoin_stable (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ∀ x ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      x.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx, map_incl]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : (algebraMap F' (Matrix (Fin n) (Fin n) F') r).map t = algebraMap F' _ (t r) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add t)]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have := Matrix.map_mul (L := x) (M := y) (f := (t : F' →+* F'))
    erw [this]; exact Subalgebra.mul_mem _ hx hy

/- English proof (translation)
Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `(AlgHom.mem_range _).1 hx`. Take `⟨q, rfl⟩` from `(AlgHom.mem_range _).1 hy`. Rewrite using `[← map_mul, mul_comm, map_mul]`.
-/
theorem adjoin_comm {A : Type} [Ring A] [Algebra F' A] (M : A) :
    ∀ x ∈ Algebra.adjoin F' {M}, ∀ y ∈ Algebra.adjoin F' {M}, x * y = y * x := by
  intro x hx y hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hx
  obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).1 hy
  rw [← map_mul, mul_comm, map_mul]

/- English proof (translation)
Use `haveI : Finite (Matrix (Fin n) (Fin n) F') := inferInstanceAs (Finite (Fin n → Fin n → F'))`. Set `f : B → B` to `fun b => ⟨δ, h⟩ * b`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Establish `h1 : (δ : Matrix (Fin n) (Fin n) F') * a = δ * b` using `congrArg Subtype.val hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2` using `congrArg (fun m => ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * m) h1`. Simplify `h2` using `[← mul_assoc]`. Take `⟨b, hb⟩` from `(Finite.injective_iff_surjective.1 hf) 1`. Establish `hb' : (δ : Matrix (Fin n) (Fin n) F') * b = 1` using `congrArg Subtype.val hb`.

Establish `: ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `b.2`.
-/
theorem inv_mem_of_finite {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (δ : GL (Fin n) F') (h : (δ : Matrix (Fin n) (Fin n) F') ∈ B) :
    ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
  haveI : Finite (Matrix (Fin n) (Fin n) F') := inferInstanceAs (Finite (Fin n → Fin n → F'))
  let f : B → B := fun b => ⟨δ, h⟩ * b
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (δ : Matrix (Fin n) (Fin n) F') * a = δ * b := congrArg Subtype.val hab
    apply Subtype.ext
    have h2 := congrArg (fun m => ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * m) h1
    simpa [← mul_assoc] using h2
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hf) 1
  have hb' : (δ : Matrix (Fin n) (Fin n) F') * b = 1 := congrArg Subtype.val hb
  have : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = b := by
    calc ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')
        = ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (δ * b) := by rw [hb', mul_one]
      _ = b := by rw [← mul_assoc]; simp
  rw [this]; exact b.2

def unitsIn {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) :
    Subgroup (GL (Fin n) F') where
  carrier := {δ | (δ : Matrix (Fin n) (Fin n) F') ∈ B}
  one_mem' := by simpa using B.one_mem
  mul_mem' := fun ha hb => by simpa using B.mul_mem ha hb
  inv_mem' := fun h => inv_mem_of_finite B _ h

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs n γ`. Use `set M : Matrix (Fin n) (Fin n) F' := ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') with hM`. Use `set B := Algebra.adjoin F' {M} with hB`. Take `⟨hfix, hinj, -, hcomm4, hmul⟩` from `GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n`. Establish `hcard` using `GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B (adjoin_stable n s γ)`.

Establish `hstab : ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), δ ∈ unitsIn B → galAct F F' n t δ ∈ unitsIn B` using `fun t δ h => by show ((galAct F F' n t δ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B`. Rewrite using `[coe_galAct]`. Conclude with `adjoin_stable n t γ _ h`. Establish `hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x` using `adjoin_comm M`. Establish `hcommU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, δ * ε = ε * δ` using `fun δ hδ ε hε => Units.ext (by simpa using hcommB _ hδ _ hε)`.

Establish `hnrm_mem : ∀ δ ∈ unitsIn B, nrm s δ ∈ unitsIn B`. Introduce `δ hδ`. Unfold `nrm nrmG`. Apply `Subgroup.list_prod_mem` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨i, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hstab _ _ hδ`. Establish `hmulU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, nrm s (δ * ε) = nrm s δ * nrm s ε` using `fun δ hδ ε hε => hmul δ ε (fun t u => hcommU _ (hstab t δ hδ) _ (hstab u ε hε))`. Set `N : unitsIn B →* unitsIn B` to `MonoidHom.mk' (fun δ => ⟨nrm s δ, hnrm_mem δ δ.2⟩) (fun a b => Subtype.ext (hmulU a a.2 b b.2))`. Establish `hfixN : ∀ δ ∈ unitsIn B, galAct F F' n s (nrm s δ) = nrm s δ`.

Introduce `δ hδ`. Establish `h4` using `hcomm4 δ`. Rewrite `h4` using `[hcommU _ (hnrm_mem δ hδ) _ hδ]`. Conclude with `mul_left_cancel h4`. Set `W : Set (unitsIn B)` to `{x | galAct F F' n s x = x}`.

Establish `hRW : (N.range : Set (unitsIn B)) ⊆ W`. Introduce and unpack `_ ⟨δ, rfl⟩`. Conclude with `hfixN δ δ.2`. Establish `hVW : Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card W`. Apply `Nat.card_congr` to reduce the goal to its premises.

Use `Equiv.ofBijective (fun x => ⟨⟨incl F F' n x.1, x.2⟩, (hfix _).2 ⟨x.1, rfl⟩⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Use `congrArg (fun y : W => ((y : unitsIn B) : GL (Fin n) F')) h` as an intermediate fact. Conclude with `Subtype.ext (hinj this)`. Introduce and unpack `⟨⟨x, hx⟩, hxW⟩`.

Take `⟨y, rfl⟩` from `(hfix x).1 hxW`. Conclude with `⟨⟨y, hx⟩, rfl⟩`. Establish `hUc : Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card (unitsIn B)` using `Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))`. Establish `hKc : Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} = Nat.card N.ker`. Apply `Nat.card_congr` to reduce the goal to its premises.

Conclude with `{ toFun := fun ε => ⟨⟨ε.1, ε.2.1⟩, (MonoidHom.mem_ker).2 (Subtype.ext ε.2.2)⟩ invFun := fun ε => ⟨ε.1.1, ε.1.2, congrArg Subtype.val ((MonoidHom.mem_ker).1 ε.2)⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `hsplit : Nat.card N.ker * Nat.card N.range = Nat.card (unitsIn B)`. Rewrite using `[← Subgroup.index_ker]`. Conclude with `Subgroup.card_mul_index _`. Establish `hKpos : 0 < Nat.card N.ker` using `Nat.card_pos`.

Establish `hVR : Nat.card W = Nat.card N.range`. Rewrite using `[← hVW]`. Rewrite `hcard` using `[hKc, hUc, ← hsplit]`. Conclude with `Nat.eq_of_mul_eq_mul_left hKpos hcard`. Establish `hEq : (N.range : Set (unitsIn B)) = W`.

Apply `Set.eq_of_subset_of_ncard_le hRW` to reduce the goal to its premises. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hVR]`. Both sides reduce to the same expression. Establish `hmem : (⟨incl F F' n γ, Algebra.subset_adjoin rfl⟩ : unitsIn B) ∈ W` using `by show galAct F F' n s (incl F F' n γ) = incl F F' n γ`. Conclude with `(hfix _).2 ⟨γ, rfl⟩`.

Rewrite `hmem` using `[← hEq]`. Take `⟨δ, hδ⟩` from `hmem`. Conclude with `⟨δ, δ.2, congrArg Subtype.val hδ⟩`.
-/
theorem nrm_surj_adjoin : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F',
      (δ : Matrix (Fin n) (Fin n) F') ∈
        Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
      nrm s δ = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n γ
  set M : Matrix (Fin n) (Fin n) F' := ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') with hM
  set B := Algebra.adjoin F' {M} with hB
  obtain ⟨hfix, hinj, -, hcomm4, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hcard := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B (adjoin_stable n s γ)
  have hstab : ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), δ ∈ unitsIn B → galAct F F' n t δ ∈ unitsIn B :=
    fun t δ h => by
      show ((galAct F F' n t δ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B
      rw [coe_galAct]; exact adjoin_stable n t γ _ h
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := adjoin_comm M
  have hcommU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, δ * ε = ε * δ := fun δ hδ ε hε =>
    Units.ext (by simpa using hcommB _ hδ _ hε)
  have hnrm_mem : ∀ δ ∈ unitsIn B, nrm s δ ∈ unitsIn B := by
    intro δ hδ
    unfold nrm nrmG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab _ _ hδ
  have hmulU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, nrm s (δ * ε) = nrm s δ * nrm s ε :=
    fun δ hδ ε hε => hmul δ ε (fun t u => hcommU _ (hstab t δ hδ) _ (hstab u ε hε))
  let N : unitsIn B →* unitsIn B := MonoidHom.mk' (fun δ => ⟨nrm s δ, hnrm_mem δ δ.2⟩)
    (fun a b => Subtype.ext (hmulU a a.2 b b.2))
  have hfixN : ∀ δ ∈ unitsIn B, galAct F F' n s (nrm s δ) = nrm s δ := by
    intro δ hδ
    have h4 := hcomm4 δ
    rw [hcommU _ (hnrm_mem δ hδ) _ hδ] at h4
    exact mul_left_cancel h4
  let W : Set (unitsIn B) := {x | galAct F F' n s x = x}
  have hRW : (N.range : Set (unitsIn B)) ⊆ W := by
    rintro _ ⟨δ, rfl⟩
    exact hfixN δ δ.2
  have hVW : Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
      = Nat.card W := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨⟨incl F F' n x.1, x.2⟩, (hfix _).2 ⟨x.1, rfl⟩⟩) ⟨?_, ?_⟩
    · intro a b h
      have := congrArg (fun y : W => ((y : unitsIn B) : GL (Fin n) F')) h
      exact Subtype.ext (hinj this)
    · rintro ⟨⟨x, hx⟩, hxW⟩
      obtain ⟨y, rfl⟩ := (hfix x).1 hxW
      exact ⟨⟨y, hx⟩, rfl⟩
  have hUc : Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card (unitsIn B) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  have hKc : Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
      = Nat.card N.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun ε => ⟨⟨ε.1, ε.2.1⟩, (MonoidHom.mem_ker).2 (Subtype.ext ε.2.2)⟩
        invFun := fun ε => ⟨ε.1.1, ε.1.2, congrArg Subtype.val ((MonoidHom.mem_ker).1 ε.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsplit : Nat.card N.ker * Nat.card N.range = Nat.card (unitsIn B) := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have hKpos : 0 < Nat.card N.ker := Nat.card_pos
  have hVR : Nat.card W = Nat.card N.range := by
    rw [← hVW]
    rw [hKc, hUc, ← hsplit] at hcard
    exact Nat.eq_of_mul_eq_mul_left hKpos hcard
  have hEq : (N.range : Set (unitsIn B)) = W := by
    apply Set.eq_of_subset_of_ncard_le hRW
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hVR]; rfl
  have hmem : (⟨incl F F' n γ, Algebra.subset_adjoin rfl⟩ : unitsIn B) ∈ W := by
    show galAct F F' n s (incl F F' n γ) = incl F F' n γ
    exact (hfix _).2 ⟨γ, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨δ, hδ⟩ := hmem
  exact ⟨δ, δ.2, congrArg Subtype.val hδ⟩

end GlobalTheory.Shin.NormSurj
