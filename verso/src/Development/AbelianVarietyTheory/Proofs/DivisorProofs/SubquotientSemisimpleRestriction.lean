import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubImage

variable {k H V Y Q : Type} [Field k] [Group H] [AddCommGroup V] [Module k V] [AddCommGroup Y]
  [Module k Y] [AddCommGroup Q] [Module k Q]

/- English proof (translation)
Use `{ toNontrivial := ?_, eq_bot_or_eq_top := ?_ }` and prove the remaining obligations. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Use `⟨⊥, ⊤, fun he => hy0 ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨y, hy⟩ : R.toSubmodule) ∈ (⊤ : Subrepresentation R.toRepresentation).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← he]`.

Establish `h2` using `(Submodule.mem_bot k).1 h1`. Simplify using `using congrArg Subtype.val h2`. Introduce `U'`. Set `U : Subrepresentation η` to `⟨U'.toSubmodule.map R.toSubmodule.subtype, by`. Introduce and unpack `g _ ⟨v, hv, rfl⟩`.

Conclude with `⟨R.toRepresentation g v, U'.apply_mem_toSubmodule g hv, rfl⟩⟩`. Break down `h U (by rintro _ ⟨v, -, rfl⟩; exact v.2) with h1 | h1` into its components or cases. Use `left`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show U'.toSubmodule = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Establish `h3 : (v : Y) ∈ U.toSubmodule` using `⟨v, hv, rfl⟩`. Rewrite `h3` using `[h1]`. Conclude with `(Submodule.mem_bot k).2 (Subtype.ext ((Submodule.mem_bot k).1 h3))`.

Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show U'.toSubmodule = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Take `⟨w, hw, hwv⟩` from `h1 v.2`. Establish `h4 : w = v` using `Subtype.ext hwv`. Substitute `h4` using the available equality. Conclude with `hw`.
-/
theorem isIrreducible_of_minimal {η : Representation k H Y} (R : Subrepresentation η)
    (hne : R.toSubmodule ≠ ⊥)
    (h : ∀ U : Subrepresentation η, U.toSubmodule ≤ R.toSubmodule →
      U.toSubmodule = ⊥ ∨ R.toSubmodule ≤ U.toSubmodule) :
    R.toRepresentation.IsIrreducible := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨⊥, ⊤, fun he => hy0 ?_⟩
    have h1 : (⟨y, hy⟩ : R.toSubmodule) ∈ (⊤ : Subrepresentation R.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← he] at h1
    have h2 := (Submodule.mem_bot k).1 h1
    simpa using congrArg Subtype.val h2
  · intro U'
    let U : Subrepresentation η := ⟨U'.toSubmodule.map R.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨R.toRepresentation g v, U'.apply_mem_toSubmodule g hv, rfl⟩⟩
    rcases h U (by rintro _ ⟨v, -, rfl⟩; exact v.2) with h1 | h1
    · left
      apply Subrepresentation.toSubmodule_injective
      show U'.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro v hv
      have h3 : (v : Y) ∈ U.toSubmodule := ⟨v, hv, rfl⟩
      rw [h1] at h3
      exact (Submodule.mem_bot k).2 (Subtype.ext ((Submodule.mem_bot k).1 h3))
    · right
      apply Subrepresentation.toSubmodule_injective
      show U'.toSubmodule = ⊤
      rw [eq_top_iff]
      intro v _
      obtain ⟨w, hw, hwv⟩ := h1 v.2
      have h4 : w = v := Subtype.ext hwv
      subst h4
      exact hw

/- English proof (translation)
Set `T : Submodule k V` to `A.toSubmodule.comap q.toLinearMap`. Establish `hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T` using `fun g x hx => by show q (ρ g x) ∈ A.toSubmodule`. Rewrite using `[q.isIntertwining]`. Conclude with `A.apply_mem_toSubmodule g hx`. Set `R : Subrepresentation η` to `⟨T.map F.toLinearMap, by`.

Introduce and unpack `g _ ⟨x, hx, rfl⟩`. Conclude with `⟨ρ g x, hT g x hx, F.isIntertwining _ _ g x⟩⟩`. Use `⟨R, isIrreducible_of_minimal R ?_ ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `: F x₀ ∈ R.toSubmodule` using `⟨x₀, hx₀, rfl⟩`.

Rewrite `this` using `[h0]`. Conclude with `hF ((Submodule.mem_bot k).1 this)`. Introduce `U hUR`. Set `T' : Subrepresentation τ` to `⟨(T ⊓ U.toSubmodule.comap F.toLinearMap).map q.toLinearMap, by`. Introduce and unpack `g _ ⟨x, ⟨hxT, hxU⟩, rfl⟩`.

Use `⟨ρ g x, ⟨hT g x hxT, ?_⟩, q.isIntertwining _ _ g x⟩` and prove the remaining obligations. Use `show F (ρ g x) ∈ U.toSubmodule`. Rewrite using `[F.isIntertwining]`. Conclude with `U.apply_mem_toSubmodule g hxU⟩`. Establish `hT'A : T' ≤ A`.

Introduce and unpack `_ ⟨x, ⟨hxT, -⟩, rfl⟩`. Conclude with `hxT`. Break down `hA.le_iff.1 hT'A with h0 | h0` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Take `⟨x, hxT, rfl⟩` from `hUR hy`. Establish `hq : q x = 0`. Establish `: q x ∈ T'.toSubmodule` using `⟨x, ⟨hxT, hy⟩, rfl⟩`. Rewrite `this` using `[h0]`.

Conclude with `(Submodule.mem_bot k).1 this`. Conclude with `(Submodule.mem_bot k).2 (hker x hq)`. Use `right`. Introduce and unpack `_ ⟨x, hxT, rfl⟩`. Establish `: q x ∈ T'.toSubmodule` using `by rw [h0]; exact hxT`.

Take `⟨t, ⟨htT, htU⟩, hqt⟩` from `this`. Establish `hd : F (x - t) = 0` using `hker _ (by`. Rewrite using `[map_sub]; exact sub_eq_zero.2 (by exact hqt.symm))`. Rewrite `hd` using `[map_sub, sub_eq_zero]`. Use `show F x ∈ U.toSubmodule`.

Rewrite using `[hd]`. Conclude with `htU`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `⟨x, rfl⟩`.
-/
theorem exists_irreducible_of_atom {ρ : Representation k H V} {η : Representation k H Y}
    {τ : Representation k H Q} (F : ρ.IntertwiningMap η) (q : ρ.IntertwiningMap τ)
    (hker : ∀ x, q x = 0 → F x = 0) (A : Subrepresentation τ) (hA : IsAtom A)
    (x₀ : V) (hx₀ : q x₀ ∈ A.toSubmodule) (hF : F x₀ ≠ 0) :
    ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
      R.toSubmodule ≤ LinearMap.range F.toLinearMap := by
  let T : Submodule k V := A.toSubmodule.comap q.toLinearMap
  have hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T := fun g x hx => by
    show q (ρ g x) ∈ A.toSubmodule
    rw [q.isIntertwining]
    exact A.apply_mem_toSubmodule g hx
  let R : Subrepresentation η := ⟨T.map F.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hT g x hx, F.isIntertwining _ _ g x⟩⟩
  refine ⟨R, isIrreducible_of_minimal R ?_ ?_, ?_⟩
  · intro h0
    have : F x₀ ∈ R.toSubmodule := ⟨x₀, hx₀, rfl⟩
    rw [h0] at this
    exact hF ((Submodule.mem_bot k).1 this)
  · intro U hUR

    let T' : Subrepresentation τ := ⟨(T ⊓ U.toSubmodule.comap F.toLinearMap).map q.toLinearMap, by
      rintro g _ ⟨x, ⟨hxT, hxU⟩, rfl⟩
      refine ⟨ρ g x, ⟨hT g x hxT, ?_⟩, q.isIntertwining _ _ g x⟩
      show F (ρ g x) ∈ U.toSubmodule
      rw [F.isIntertwining]
      exact U.apply_mem_toSubmodule g hxU⟩
    have hT'A : T' ≤ A := by
      rintro _ ⟨x, ⟨hxT, -⟩, rfl⟩
      exact hxT
    rcases hA.le_iff.1 hT'A with h0 | h0
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxT, rfl⟩ := hUR hy
      have hq : q x = 0 := by
        have : q x ∈ T'.toSubmodule := ⟨x, ⟨hxT, hy⟩, rfl⟩
        rw [h0] at this
        exact (Submodule.mem_bot k).1 this
      exact (Submodule.mem_bot k).2 (hker x hq)
    · right
      rintro _ ⟨x, hxT, rfl⟩
      have : q x ∈ T'.toSubmodule := by rw [h0]; exact hxT
      obtain ⟨t, ⟨htT, htU⟩, hqt⟩ := this
      have hd : F (x - t) = 0 := hker _ (by
        rw [map_sub]; exact sub_eq_zero.2 (by exact hqt.symm))
      rw [map_sub, sub_eq_zero] at hd
      show F x ∈ U.toSubmodule
      rw [hd]; exact htU
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Use `haveI : IsSemisimpleModule (MonoidAlgebra k H) τ.asModule := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule τ).1 hss`. Set `e` to `Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)`. Set `B : Subrepresentation τ` to `⟨(LinearMap.ker F.toLinearMap).map q.toLinearMap, by`.

Introduce and unpack `g _ ⟨x, hx, rfl⟩`. Use `⟨ρ g x, ?_, q.isIntertwining _ _ g x⟩` and prove the remaining obligations. Use `show F (ρ g x) = 0`. Rewrite using `[F.isIntertwining]`. Establish `hx' : F x = 0` using `hx`.

Rewrite using `[hx', map_zero]⟩`. Establish `hRB : q.range ≤ B`. Rewrite using `[← e.le_iff_le, ← IsSemisimpleModule.sSup_simples_le (e q.range)]`. Use `sSup_le ?_` and prove the remaining obligations. Introduce and unpack `m ⟨hm, hmle⟩`.

Establish `hm' : IsAtom m` using `(isSimpleModule_iff_isAtom).1 hm`. Rewrite `hm'`, `hmle`, the goal using `[← e.apply_symm_apply m]`. Rewrite `hm'` using `[e.isAtom_iff]`. Rewrite `hmle`, the goal using `[e.le_iff_le]`. Introduce `a ha`.

Take `⟨x, rfl⟩` from `hmle ha`. Conclude with `⟨x, hno _ hm' x ha, rfl⟩`. Apply `hF` to reduce the goal to its premises. Use extensionality with `x`. Take `⟨y, hy, hyx⟩` from `hRB (show q x ∈ q.range from ⟨x, rfl⟩)`.

Establish `hy' : F y = 0` using `hy`. Establish `hd : F (x - y) = 0` using `hker _ (by`. Rewrite using `[map_sub]; exact sub_eq_zero.2 (by exact hyx.symm))`. Rewrite `hd` using `[map_sub, hy', sub_zero]`. Use `show F x = 0`.

Conclude with `hd`.
-/
theorem exists_atom_of_semisimple {ρ : Representation k H V} {η : Representation k H Y}
    {τ : Representation k H Q} (hss : τ.IsSemisimpleRepresentation) (F : ρ.IntertwiningMap η)
    (q : ρ.IntertwiningMap τ) (hker : ∀ x, q x = 0 → F x = 0) (hF : F ≠ 0) :
    ∃ A : Subrepresentation τ, IsAtom A ∧ ∃ x₀, q x₀ ∈ A.toSubmodule ∧ F x₀ ≠ 0 := by
  by_contra hno
  push_neg at hno
  haveI : IsSemisimpleModule (MonoidAlgebra k H) τ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule τ).1 hss
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)
  let B : Subrepresentation τ := ⟨(LinearMap.ker F.toLinearMap).map q.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨ρ g x, ?_, q.isIntertwining _ _ g x⟩
    show F (ρ g x) = 0
    rw [F.isIntertwining]
    have hx' : F x = 0 := hx
    rw [hx', map_zero]⟩
  have hRB : q.range ≤ B := by
    rw [← e.le_iff_le, ← IsSemisimpleModule.sSup_simples_le (e q.range)]
    refine sSup_le ?_
    rintro m ⟨hm, hmle⟩
    have hm' : IsAtom m := (isSimpleModule_iff_isAtom).1 hm
    rw [← e.apply_symm_apply m] at hm' hmle ⊢
    rw [e.isAtom_iff] at hm'
    rw [e.le_iff_le] at hmle ⊢
    intro a ha
    obtain ⟨x, rfl⟩ := hmle ha
    exact ⟨x, hno _ hm' x ha, rfl⟩
  apply hF
  ext x
  obtain ⟨y, hy, hyx⟩ := hRB (show q x ∈ q.range from ⟨x, rfl⟩)
  have hy' : F y = 0 := hy
  have hd : F (x - y) = 0 := hker _ (by
    rw [map_sub]; exact sub_eq_zero.2 (by exact hyx.symm))
  rw [map_sub, hy', sub_zero] at hd
  show F x = 0
  exact hd

section Quot

variable {G X : Type} [Group G] [AddCommGroup X] [Module k X]

/- English proof (translation)
Take `⟨x, hxM, hxM'⟩` from `SetLike.exists_of_lt hlt`. Use `{ toNontrivial := ?_, eq_bot_or_eq_top := ?_ }` and prove the remaining obligations. Use `⟨⊥, ⊤, fun he => hxM' ?_⟩` and prove the remaining obligations. Establish `h1 : (Submodule.Quotient.mk (⟨x, hxM⟩ : M.toSubmodule) : M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) ∈ (⊤ : Subrepresentation (subQuot M M')).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← he]`.

Establish `h2 : (Submodule.Quotient.mk (⟨x, hxM⟩ : M.toSubmodule) : M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) = 0` using `(Submodule.mem_bot k).1 h1`. Conclude with `(Submodule.Quotient.mk_eq_zero (M'.toSubmodule.comap M.toSubmodule.subtype)).1 h2`. Introduce `U`. Set `W : Subrepresentation σ` to `⟨(U.toSubmodule.comap (Submodule.mkQ _)).map M.toSubmodule.subtype, by`. Introduce and unpack `g _ ⟨m, hm, rfl⟩`.

Conclude with `⟨M.toRepresentation g m, U.apply_mem_toSubmodule g hm, rfl⟩⟩`. Establish `hM'W : M' ≤ W`. Introduce `y hy`. Use `⟨⟨y, hlt.le hy⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show Submodule.mkQ _ _ ∈ U.toSubmodule`.

Establish `h0 : (Submodule.Quotient.mk (⟨y, hlt.le hy⟩ : M.toSubmodule) : M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hy`. Rewrite using `[Submodule.mkQ_apply, h0]`. Conclude with `zero_mem _`. Establish `hWM : W ≤ M`. Introduce and unpack `_ ⟨m, -, rfl⟩`.

Conclude with `m.2`. Break down `eq_or_lt_of_le hWM with h | h` into its components or cases. Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show U.toSubmodule = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `z _`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Establish `hm : (m : X) ∈ W` using `by rw [h]; exact m.2`. Take `⟨m', hm', hm'm⟩` from `hm`.

Establish `: m' = m` using `Subtype.ext hm'm`. Substitute `this` using the available equality. Conclude with `hm'`. Use `left`. Establish `hW : W = M'` using `(eq_of_le_of_not_lt hM'W (hmax W h)).symm`.

Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show U.toSubmodule = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`.

Establish `hm : (m : X) ∈ W` using `⟨m, hz, rfl⟩`. Rewrite `hm` using `[hW]`. Conclude with `(Submodule.mem_bot k).2 ((Submodule.Quotient.mk_eq_zero _).2 hm)`.
-/
theorem isIrreducible_subQuot {σ : Representation k G X} (M M' : Subrepresentation σ)
    (hlt : M' < M) (hmax : ∀ W : Subrepresentation σ, W < M → ¬ M' < W) :
    (subQuot M M').IsIrreducible := by
  obtain ⟨x, hxM, hxM'⟩ := SetLike.exists_of_lt hlt
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun he => hxM' ?_⟩
    have h1 : (Submodule.Quotient.mk (⟨x, hxM⟩ : M.toSubmodule) :
        M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) ∈
        (⊤ : Subrepresentation (subQuot M M')).toSubmodule := Submodule.mem_top
    rw [← he] at h1
    have h2 : (Submodule.Quotient.mk (⟨x, hxM⟩ : M.toSubmodule) :
        M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) = 0 :=
      (Submodule.mem_bot k).1 h1
    exact (Submodule.Quotient.mk_eq_zero (M'.toSubmodule.comap M.toSubmodule.subtype)).1 h2
  · intro U
    let W : Subrepresentation σ :=
      ⟨(U.toSubmodule.comap (Submodule.mkQ _)).map M.toSubmodule.subtype, by
        rintro g _ ⟨m, hm, rfl⟩
        exact ⟨M.toRepresentation g m, U.apply_mem_toSubmodule g hm, rfl⟩⟩
    have hM'W : M' ≤ W := by
      intro y hy
      refine ⟨⟨y, hlt.le hy⟩, ?_, rfl⟩
      show Submodule.mkQ _ _ ∈ U.toSubmodule
      have h0 : (Submodule.Quotient.mk (⟨y, hlt.le hy⟩ : M.toSubmodule) :
          M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hy
      rw [Submodule.mkQ_apply, h0]
      exact zero_mem _
    have hWM : W ≤ M := by
      rintro _ ⟨m, -, rfl⟩
      exact m.2
    rcases eq_or_lt_of_le hWM with h | h
    · right
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊤
      rw [eq_top_iff]
      intro z _
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hm : (m : X) ∈ W := by rw [h]; exact m.2
      obtain ⟨m', hm', hm'm⟩ := hm
      have : m' = m := Subtype.ext hm'm
      subst this
      exact hm'
    · left
      have hW : W = M' := (eq_of_le_of_not_lt hM'W (hmax W h)).symm
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hm : (m : X) ∈ W := ⟨m, hz, rfl⟩
      rw [hW] at hm
      exact (Submodule.mem_bot k).2 ((Submodule.Quotient.mk_eq_zero _).2 hm)

/- English proof (translation)
Assemble the required witnesses or components as `⟨M, ⟨Submodule.mkQ _, fun g => LinearMap.ext fun _ => rfl⟩, Submodule.mkQ_surjective _⟩`.
-/
theorem isSubquotient_subQuot {σ : Representation k G X} (M M' : Subrepresentation σ) :
    IsSubquotient (subQuot M M') σ :=
  ⟨M, ⟨Submodule.mkQ _, fun g => LinearMap.ext fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

end Quot

/- English proof (translation)
Introduce `L H _ _ s X _ _ σ hfl hss S Y _ _ η`. Establish `φ` using `Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)`. Rewrite `hfl` using `[HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', isArtinian_iff]`. Take `⟨hN, hA⟩` from `hfl`. Use `haveI : WellFoundedGT (Subrepresentation σ) := φ.toOrderEmbedding.wellFoundedGT`.

Use `haveI : WellFoundedLT (Submodule (MonoidAlgebra ℂ L) σ.asModule) := ⟨hA⟩`. Use `haveI : WellFoundedLT (Subrepresentation σ) := φ.toOrderEmbedding.wellFoundedLT`. It suffices to establish `key : ∀ M : Subrepresentation σ, ∀ S : Subrepresentation (σ.comp s), S.toSubmodule ≤ M.toSubmodule → ∀ F : S.toRepresentation.IntertwiningMap η, F ≠ 0 → ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧ R.toSubmodule ≤ LinearMap.range F.toLinearMap from fun F hF => ke …`. Introduce `M`. Proceed by induction on `M using WellFoundedLT.induction with`.

Consider the case `_ M ih`. Introduce `S hSM F hF`. Choose the witnesses or unpack the hypotheses as in `⟨x₁, hx₁⟩ : ∃ x, F x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hF (by ext x; exact h x)`. Establish `hMbot : ⊥ < M`. Use `bot_lt_iff_ne_bot.2 fun h => hx₁ ?_` and prove the remaining obligations. Establish `h1 : (x₁ : X) ∈ M.toSubmodule` using `hSM x₁.2`. Rewrite `h1` using `[h]`.

Establish `h0 : x₁ = 0` using `Subtype.ext ((Submodule.mem_bot ℂ).1 h1)`. Rewrite using `[h0, map_zero]`. Take `⟨M', hM'lt, hM'max⟩` from `(wellFounded_gt (α := Subrepresentation σ)).has_min {W | W < M} ⟨⊥, hMbot⟩`. Establish `hM'lt' : M' < M` using `hM'lt`. Set `M'H : Subrepresentation (σ.comp s)` to `⟨M'.toSubmodule, fun h _ hv => M'.apply_mem_toSubmodule (s h) hv⟩`.

Distinguish the cases in `hcase : ∃ x : S.toSubmodule, (x : X) ∈ M'.toSubmodule ∧ F x ≠ 0`. Take `⟨x, hxM', hFx⟩` from `hcase`. Set `S' : Subrepresentation (σ.comp s)` to `S ⊓ M'H`. Establish `hle : S'.toSubmodule ≤ S.toSubmodule` using `inf_le_left`. Set `F' : S'.toRepresentation.IntertwiningMap η` to `⟨F.toLinearMap ∘ₗ Submodule.inclusion hle, fun h => by`.

Use extensionality with `v`. Conclude with `F.isIntertwining _ _ h (Submodule.inclusion hle v)⟩`. Establish `hF' : F' ≠ 0`. Introduce `h0`. Apply `hFx` to reduce the goal to its premises.

Establish `h2 : F' ⟨x, x.2, hxM'⟩ = 0` using `by rw [h0]; rfl`. Conclude with `h2`. Take `⟨R, hR, hRle⟩` from `ih M' hM'lt' S' inf_le_right F' hF'`. Use `⟨R, hR, hRle.trans ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `⟨Submodule.inclusion hle v, rfl⟩`. Use `push_neg at hcase`. Establish `hirr` using `isIrreducible_subQuot M M' hM'lt' (fun W hW h => hM'max W hW h)`. Establish `hssτ` using `hss _ (subQuot M M') (isSubquotient_subQuot M M') hirr`. Set `q : S.toRepresentation.IntertwiningMap ((subQuot M M').comp s)` to `⟨(Submodule.mkQ _) ∘ₗ Submodule.inclusion hSM, fun h => LinearMap.ext fun _ => rfl⟩`.

Establish `hker : ∀ x, q x = 0 → F x = 0` using `fun x hx => hcase x ((Submodule.Quotient.mk_eq_zero (M'.toSubmodule.comap M.toSubmodule.subtype)).1 hx)`. Take `⟨A, hA, x₀, hx₀, hF₀⟩` from `exists_atom_of_semisimple hssτ F q hker hF`. Conclude with `exists_irreducible_of_atom F q hker A hA x₀ hx₀ hF₀`.
-/
theorem exists_irreducible_le_range : ∀ (L H : Type) [Group L] [Group H] (s : H →* L) (X : Type)
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ L X), GlobalTheory.SmGL.HasFiniteLength σ →
    (∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ L Z), GlobalTheory.SmGL.IsSubquotient τ σ →
      τ.IsIrreducible → Representation.IsSemisimpleRepresentation (τ.comp s)) →
    ∀ (S : Subrepresentation (σ.comp s)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
      (η : Representation ℂ H Y) (F : S.toRepresentation.IntertwiningMap η), F ≠ 0 →
      ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
        R.toSubmodule ≤ LinearMap.range F.toLinearMap := by
  intro L H _ _ s X _ _ σ hfl hss S Y _ _ η
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff',
    isArtinian_iff] at hfl
  obtain ⟨hN, hA⟩ := hfl
  haveI : WellFoundedGT (Subrepresentation σ) := φ.toOrderEmbedding.wellFoundedGT
  haveI : WellFoundedLT (Submodule (MonoidAlgebra ℂ L) σ.asModule) := ⟨hA⟩
  haveI : WellFoundedLT (Subrepresentation σ) := φ.toOrderEmbedding.wellFoundedLT
  suffices key : ∀ M : Subrepresentation σ, ∀ S : Subrepresentation (σ.comp s),
      S.toSubmodule ≤ M.toSubmodule → ∀ F : S.toRepresentation.IntertwiningMap η, F ≠ 0 →
      ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
        R.toSubmodule ≤ LinearMap.range F.toLinearMap from
    fun F hF => key ⊤ S le_top F hF
  intro M
  induction M using WellFoundedLT.induction with
  | _ M ih =>
  intro S hSM F hF
  obtain ⟨x₁, hx₁⟩ : ∃ x, F x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF (by ext x; exact h x)
  have hMbot : ⊥ < M := by
    refine bot_lt_iff_ne_bot.2 fun h => hx₁ ?_
    have h1 : (x₁ : X) ∈ M.toSubmodule := hSM x₁.2
    rw [h] at h1
    have h0 : x₁ = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 h1)
    rw [h0, map_zero]
  obtain ⟨M', hM'lt, hM'max⟩ :=
    (wellFounded_gt (α := Subrepresentation σ)).has_min {W | W < M} ⟨⊥, hMbot⟩
  have hM'lt' : M' < M := hM'lt
  let M'H : Subrepresentation (σ.comp s) :=
    ⟨M'.toSubmodule, fun h _ hv => M'.apply_mem_toSubmodule (s h) hv⟩
  by_cases hcase : ∃ x : S.toSubmodule, (x : X) ∈ M'.toSubmodule ∧ F x ≠ 0
  · obtain ⟨x, hxM', hFx⟩ := hcase
    let S' : Subrepresentation (σ.comp s) := S ⊓ M'H
    have hle : S'.toSubmodule ≤ S.toSubmodule := inf_le_left
    let F' : S'.toRepresentation.IntertwiningMap η :=
      ⟨F.toLinearMap ∘ₗ Submodule.inclusion hle, fun h => by
        ext v
        exact F.isIntertwining _ _ h (Submodule.inclusion hle v)⟩
    have hF' : F' ≠ 0 := by
      intro h0
      apply hFx
      have h2 : F' ⟨x, x.2, hxM'⟩ = 0 := by rw [h0]; rfl
      exact h2
    obtain ⟨R, hR, hRle⟩ := ih M' hM'lt' S' inf_le_right F' hF'
    refine ⟨R, hR, hRle.trans ?_⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨Submodule.inclusion hle v, rfl⟩
  · push_neg at hcase
    have hirr := isIrreducible_subQuot M M' hM'lt' (fun W hW h => hM'max W hW h)
    have hssτ := hss _ (subQuot M M') (isSubquotient_subQuot M M') hirr
    let q : S.toRepresentation.IntertwiningMap ((subQuot M M').comp s) :=
      ⟨(Submodule.mkQ _) ∘ₗ Submodule.inclusion hSM, fun h => LinearMap.ext fun _ => rfl⟩
    have hker : ∀ x, q x = 0 → F x = 0 := fun x hx =>
      hcase x ((Submodule.Quotient.mk_eq_zero (M'.toSubmodule.comap M.toSubmodule.subtype)).1 hx)
    obtain ⟨A, hA, x₀, hx₀, hF₀⟩ := exists_atom_of_semisimple hssτ F q hker hF
    exact exists_irreducible_of_atom F q hker A hA x₀ hx₀ hF₀

end GlobalTheory.IrrSubImage
