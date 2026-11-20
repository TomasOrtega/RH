import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors

noncomputable section

namespace GlobalTheory.CuspFactor

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke Representation

section General

variable {G V W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Conclude with `bot_ne_top (α := Subrepresentation τ) (Subrepresentation.ext (Subsingleton.elim _ _))`.
-/
theorem nontrivial_of_irr (τ : Representation ℂ G V) (h : τ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation τ) (Subrepresentation.ext (Subsingleton.elim _ _))

/- English proof (translation)
Use `nontrivial_of_irr τ h` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Set `S : Subrepresentation τ` to `⟨Submodule.span ℂ (Set.range fun g => τ g v), fun g w hw => by`. Establish `: Submodule.span ℂ (Set.range fun g => τ g v) ≤ (Submodule.span ℂ (Set.range fun g => τ g v)).comap (τ g)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * x, by simp⟩`. Conclude with `this hw⟩`. Break down `eq_bot_or_eq_top S with hS | hS` into its components or cases. Establish `h1 : v ∈ S.toSubmodule` using `Submodule.subset_span ⟨1, by simp⟩`.

Rewrite `h1` using `[hS]`. Conclude with `absurd h1 hv`. Establish `h2 : Submodule.span ℂ (Set.range fun g => τ g v) = ⊤` using `congrArg Subrepresentation.toSubmodule hS`. Conclude with `⟨h2 ▸ Submodule.fg_span (Set.finite_range _)⟩`.
-/
theorem finiteDimensional_of_irr [Finite G] (τ : Representation ℂ G V) (h : τ.IsIrreducible) :
    FiniteDimensional ℂ V := by
  have := nontrivial_of_irr τ h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g v), fun g w hw => by
    have : Submodule.span ℂ (Set.range fun g => τ g v) ≤
        (Submodule.span ℂ (Set.range fun g => τ g v)).comap (τ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨g * x, by simp⟩
    exact this hw⟩
  rcases eq_bot_or_eq_top S with hS | hS
  · have h1 : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [hS] at h1
    exact absurd h1 hv
  · have h2 : Submodule.span ℂ (Set.range fun g => τ g v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
    exact ⟨h2 ▸ Submodule.fg_span (Set.finite_range _)⟩

/- English proof (translation)
Establish `: (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) ≤ (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap).comap T.toLinearMap`. Use `iSup_le fun f => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem (T.comp f) ⟨w, rfl⟩`. Conclude with `this hv`.
-/
theorem span_stable (τ : Representation ℂ G V) (ρ : Representation ℂ G W) (T : IntertwiningMap τ τ) {v : V}
    (hv : v ∈ ⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) :
    T v ∈ ⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap := by
  have : (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) ≤
      (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap).comap T.toLinearMap := by
    refine iSup_le fun f => ?_
    rintro _ ⟨w, rfl⟩
    exact Submodule.mem_iSup_of_mem (T.comp f) ⟨w, rfl⟩
  exact this hv

def spanRep (τ : Representation ℂ G V) (ρ : Representation ℂ G W) : Subrepresentation τ :=
  ⟨⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap, fun g v hv => by
    have : (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) ≤
        (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap).comap (τ g) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨ρ g w, f.isIntertwining _ _ g w⟩
    exact this hv⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1 : isotypicComponent (MonoidAlgebra ℂ G) ρ.asModule ρ.asModule = ⊤` using `isotypicComponent_eq_top_iff.2 (IsIsotypicOfType.of_isSimpleModule _ _)`. Establish `h2 : (spanRep τ ρ).toSubmodule ≤ (Subrepresentation.ofSubmodule' (isotypicComponent (MonoidAlgebra ℂ G) τ.asModule ρ.asModule)).toSubmodule`. Use `iSup_le fun f => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`.

Establish `h3` using `LinearMap.le_comap_isotypicComponent ρ.asModule (IntertwiningMap.equivLinearMapAsModule ρ τ f)`. Rewrite `h3` using `[h1]`. Conclude with `h3 (@Submodule.mem_top _ ρ.asModule _ _ _ w)`. Conclude with `h2`. Use `sSup_le ?_` and prove the remaining obligations.

Introduce and unpack `m ⟨e⟩ v hv`. Establish `key : ∀ (f : IntertwiningMap ρ τ) (w : W), f w ∈ (spanRep τ ρ).toSubmodule` using `fun f w => Submodule.mem_iSup_of_mem f ⟨w, rfl⟩`. Establish `h1` using `key ((IntertwiningMap.equivLinearMapAsModule ρ τ).symm (m.subtype ∘ₗ e.symm.toLinearMap)) (e ⟨v, hv⟩)`. Establish `h2 : (m.subtype ∘ₗ e.symm.toLinearMap) (e ⟨v, hv⟩) = v` using `by simp`. Rewrite using `[← h2]`.

Conclude with `h1`.
-/
theorem spanRep_asSubmodule (τ : Representation ℂ G V) (ρ : Representation ℂ G W) (hρ : ρ.IsIrreducible) :
    (spanRep τ ρ).asSubmodule = isotypicComponent (MonoidAlgebra ℂ G) τ.asModule ρ.asModule := by
  apply le_antisymm
  · have h1 : isotypicComponent (MonoidAlgebra ℂ G) ρ.asModule ρ.asModule = ⊤ :=
      isotypicComponent_eq_top_iff.2 (IsIsotypicOfType.of_isSimpleModule _ _)
    have h2 : (spanRep τ ρ).toSubmodule ≤ (Subrepresentation.ofSubmodule'
        (isotypicComponent (MonoidAlgebra ℂ G) τ.asModule ρ.asModule)).toSubmodule := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      have h3 := LinearMap.le_comap_isotypicComponent ρ.asModule
        (IntertwiningMap.equivLinearMapAsModule ρ τ f)
      rw [h1] at h3
      exact h3 (@Submodule.mem_top _ ρ.asModule _ _ _ w)
    exact h2
  · refine sSup_le ?_
    rintro m ⟨e⟩ v hv
    have key : ∀ (f : IntertwiningMap ρ τ) (w : W), f w ∈ (spanRep τ ρ).toSubmodule := fun f w =>
      Submodule.mem_iSup_of_mem f ⟨w, rfl⟩
    have h1 := key ((IntertwiningMap.equivLinearMapAsModule ρ τ).symm (m.subtype ∘ₗ e.symm.toLinearMap)) (e ⟨v, hv⟩)
    have h2 : (m.subtype ∘ₗ e.symm.toLinearMap) (e ⟨v, hv⟩) = v := by simp
    rw [← h2]
    exact h1

/- English proof (translation)
Rewrite using `[← isotypicComponent_eq_top_iff, ← spanRep_asSubmodule τ ρ hρ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `top_le_iff.1 fun v _ => ?_` and prove the remaining obligations. Establish `: (v : V) ∈ (spanRep τ ρ).toSubmodule`.

Rewrite using `[show (spanRep τ ρ).toSubmodule = ⊤ from h]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `this`. Introduce `h`. Use `top_le_iff.1 fun v _ => ?_` and prove the remaining obligations.

Establish `: (v : τ.asModule) ∈ (spanRep τ ρ).asSubmodule`. Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `this`.
-/
theorem isotypic_iff [Finite G] (τ : Representation ℂ G V) (ρ : Representation ℂ G W) (hρ : ρ.IsIrreducible) :
    BlockProductIsomorphism.IsIsotypicOf τ ρ ↔ IsIsotypicOfType (MonoidAlgebra ℂ G) τ.asModule ρ.asModule := by
  rw [← isotypicComponent_eq_top_iff, ← spanRep_asSubmodule τ ρ hρ]
  constructor
  · intro h
    refine top_le_iff.1 fun v _ => ?_
    have : (v : V) ∈ (spanRep τ ρ).toSubmodule := by
      rw [show (spanRep τ ρ).toSubmodule = ⊤ from h]; trivial
    exact this
  · intro h
    refine top_le_iff.1 fun v _ => ?_
    have : (v : τ.asModule) ∈ (spanRep τ ρ).asSubmodule := by
      rw [h]; trivial
    exact this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨e⟩ => ⟨LinearEquiv.ofBijective (IntertwiningMap.equivLinearMapAsModule ρ ρ' e.toIntertwiningMap) e.toLinearEquiv.bijective⟩, fun ⟨e⟩ => ⟨((IntertwiningMap.equivLinearMapAsModule ρ ρ').symm e.toLinearMap).ofBijective e.bijective⟩⟩`.
-/
theorem nonempty_equiv_iff (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') :
    Nonempty (ρ.Equiv ρ') ↔ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ G] ρ'.asModule) :=
  ⟨fun ⟨e⟩ => ⟨LinearEquiv.ofBijective (IntertwiningMap.equivLinearMapAsModule ρ ρ' e.toIntertwiningMap)
      e.toLinearEquiv.bijective⟩,
    fun ⟨e⟩ => ⟨((IntertwiningMap.equivLinearMapAsModule ρ ρ').symm e.toLinearMap).ofBijective e.bijective⟩⟩

/- English proof (translation)
Establish `: Nontrivial τ.asModule` using `‹Nontrivial V›`. Take `⟨S, hS⟩` from `IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ G) τ.asModule)`. Rewrite `hS` using `[← isSimpleModule_iff_isAtom]`. Conclude with `⟨(h S).some.symm.trans (h' S).some⟩`.
-/
theorem type_unique [Finite G] [Nontrivial V] (τ : Representation ℂ G V) (ρ : Representation ℂ G W)
    (ρ' : Representation ℂ G W') (h : IsIsotypicOfType (MonoidAlgebra ℂ G) τ.asModule ρ.asModule)
    (h' : IsIsotypicOfType (MonoidAlgebra ℂ G) τ.asModule ρ'.asModule) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ G] ρ'.asModule) := by
  have : Nontrivial τ.asModule := ‹Nontrivial V›
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ G) τ.asModule)
  rw [← isSimpleModule_iff_isAtom] at hS
  exact ⟨(h S).some.symm.trans (h' S).some⟩

/- English proof (translation)
Use `{ toNontrivial := ⟨⟨⊥, ⊤, fun h => hS.1 ?_⟩⟩, eq_bot_or_eq_top := fun T => ?_ }` and prove the remaining obligations. Establish `h1 : (⊥ : Submodule ℂ S.toSubmodule) = ⊤` using `congrArg Subrepresentation.toSubmodule h`. Use `Subrepresentation.ext (eq_bot_iff.2 fun v hv => ?_)` and prove the remaining obligations. Establish `h2 : (⟨v, hv⟩ : S.toSubmodule) ∈ (⊥ : Submodule ℂ S.toSubmodule)` using `by rw [h1]; trivial`. Conclude with `congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h2)`.

Set `T' : Subrepresentation τ` to `⟨T.toSubmodule.map S.toSubmodule.subtype, by`. Introduce and unpack `g _ ⟨w, hw, rfl⟩`. Conclude with `⟨_, T.apply_mem_toSubmodule g hw, rfl⟩⟩`. Establish `hle : T' ≤ S`. Introduce and unpack `_ ⟨w, -, rfl⟩`.

Conclude with `w.2`. Break down `hS.le_iff.1 hle with h | h` into its components or cases. Use `left`. Use `Subrepresentation.ext (eq_bot_iff.2 fun w hw => ?_)` and prove the remaining obligations. Establish `h2 : (w : V) ∈ T'.toSubmodule` using `⟨w, hw, rfl⟩`.

Rewrite `h2` using `[h]`. Conclude with `Subtype.ext h2`. Use `right`. Use `Subrepresentation.ext (eq_top_iff.2 fun w _ => ?_)` and prove the remaining obligations. Establish `h2 : (w : V) ∈ T'.toSubmodule` using `by rw [h]; exact w.2`.

Take `⟨w', hw', e⟩` from `h2`. Conclude with `(Subtype.ext e : w' = w) ▸ hw'`.
-/
theorem irr_of_atom (τ : Representation ℂ G V) (S : Subrepresentation τ) (hS : IsAtom S) :
    S.toRepresentation.IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => hS.1 ?_⟩⟩, eq_bot_or_eq_top := fun T => ?_ }
  · have h1 : (⊥ : Submodule ℂ S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    refine Subrepresentation.ext (eq_bot_iff.2 fun v hv => ?_)
    have h2 : (⟨v, hv⟩ : S.toSubmodule) ∈ (⊥ : Submodule ℂ S.toSubmodule) := by rw [h1]; trivial
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h2)
  · let T' : Subrepresentation τ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨_, T.apply_mem_toSubmodule g hw, rfl⟩⟩
    have hle : T' ≤ S := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    rcases hS.le_iff.1 hle with h | h
    · left
      refine Subrepresentation.ext (eq_bot_iff.2 fun w hw => ?_)
      have h2 : (w : V) ∈ T'.toSubmodule := ⟨w, hw, rfl⟩
      rw [h] at h2
      exact Subtype.ext h2
    · right
      refine Subrepresentation.ext (eq_top_iff.2 fun w _ => ?_)
      have h2 : (w : V) ∈ T'.toSubmodule := by rw [h]; exact w.2
      obtain ⟨w', hw', e⟩ := h2
      exact (Subtype.ext e : w' = w) ▸ hw'

/- English proof (translation)
Set `τ : Representation ℂ G V` to `σ.comp φ`. Use `nontrivial_of_irr σ hσ` as an intermediate fact. Establish `: Nontrivial τ.asModule` using `‹Nontrivial V›`. Take `⟨S₀, hS₀⟩` from `IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ G) τ.asModule)`. Establish `hS` using `(Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)).symm.isAtom_iff S₀ |>.2 hS₀`.

Use `set S := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)).symm S₀`. Use `⟨S.toSubmodule, inferInstance, inferInstance, S.toRepresentation, irr_of_atom τ S hS, ?_⟩` and prove the remaining obligations. Set `U : Subrepresentation σ` to `⟨(spanRep τ S.toRepresentation).toSubmodule, fun p v hv => by`. Take `⟨g, q, rfl, hq⟩` from `H p`. Rewrite using `[map_mul]`.

Conclude with `span_stable τ S.toRepresentation ⟨σ q, fun x => by`. Use `hq x` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Conclude with `this⟩ ((spanRep τ S.toRepresentation).apply_mem_toSubmodule g hv)⟩`. Break down `eq_bot_or_eq_top U with h | h` into its components or cases.

Use `absurd (Subrepresentation.ext (eq_bot_iff.2 fun v hv => ?_)) hS.1` and prove the remaining obligations. Establish `h2 : v ∈ U.toSubmodule` using `Submodule.mem_iSup_of_mem (⟨S.toSubmodule.subtype, fun _ => rfl⟩ : IntertwiningMap S.toRepresentation τ) ⟨⟨v, hv⟩, rfl⟩`. Rewrite `h2` using `[h]`. Conclude with `h2`. Conclude with `congrArg Subrepresentation.toSubmodule h`.
-/
theorem exists_type {P : Type} [Group P] [Finite G] (σ : Representation ℂ P V) (hσ : σ.IsIrreducible) (φ : G →* P)
    (H : ∀ p : P, ∃ (g : G) (q : P), p = q * φ g ∧ ∀ x, σ (q * φ x) = σ (φ x * q)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (ρ : Representation ℂ G W), ρ.IsIrreducible ∧
      BlockProductIsomorphism.IsIsotypicOf (show Representation ℂ G V from σ.comp φ) ρ := by
  let τ : Representation ℂ G V := σ.comp φ
  have := nontrivial_of_irr σ hσ
  have : Nontrivial τ.asModule := ‹Nontrivial V›
  obtain ⟨S₀, hS₀⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ G) τ.asModule)
  have hS := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)).symm.isAtom_iff S₀ |>.2 hS₀
  set S := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)).symm S₀
  refine ⟨S.toSubmodule, inferInstance, inferInstance, S.toRepresentation, irr_of_atom τ S hS, ?_⟩
  let U : Subrepresentation σ := ⟨(spanRep τ S.toRepresentation).toSubmodule, fun p v hv => by
    obtain ⟨g, q, rfl, hq⟩ := H p
    rw [map_mul]
    exact span_stable τ S.toRepresentation ⟨σ q, fun x => by
      have := hq x
      rw [map_mul, map_mul] at this
      exact this⟩ ((spanRep τ S.toRepresentation).apply_mem_toSubmodule g hv)⟩
  rcases eq_bot_or_eq_top U with h | h
  · refine absurd (Subrepresentation.ext (eq_bot_iff.2 fun v hv => ?_)) hS.1
    have h2 : v ∈ U.toSubmodule :=
      Submodule.mem_iSup_of_mem (⟨S.toSubmodule.subtype, fun _ => rfl⟩ : IntertwiningMap S.toRepresentation τ)
        ⟨⟨v, hv⟩, rfl⟩
    rw [h] at h2
    exact h2
  · exact congrArg Subrepresentation.toSubmodule h

end General

variable {F : Type} [Field F] {r : ℕ}

def diagBlock (b : Fin r → ℕ) (c : ℕ) : blockTri (κ := F) b →* Matrix (BlockEmbeddingFactors.Block b c) (BlockEmbeddingFactors.Block b c) F where
  toFun p := ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).submatrix Subtype.val Subtype.val
  map_one' := by
    ext i j
    simp [Matrix.one_apply, Subtype.ext_iff]
  map_mul' p q := by
    ext i k
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.submatrix_apply, Matrix.mul_apply]
    rw [← Finset.sum_subtype (Finset.univ.filter fun l => b l = c) (by simp)
      (fun l => ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i l * ((q : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) l k),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · rfl
    · have hi := i.2
      have hk := k.2
      rcases lt_or_gt_of_ne h with h1 | h1
      · rw [mem_blockTri.1 p.2 i l (by omega), zero_mul]
      · rw [mem_blockTri.1 q.2 l k (by omega), mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Conclude with `BlockEmbeddingFactors.blockMat_in b c _ i j`.
-/
theorem diagBlock_emb_self (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (BlockEmbeddingFactors.Block b c) = d)
    (g : GL (Fin d) F) : diagBlock b c (BlockEmbeddingFactors.blockEmb b c h g) = BlockEmbeddingFactors.toBlock b c h g := by
  ext i j
  exact BlockEmbeddingFactors.blockMat_in b c _ i j

/- English proof (translation)
Use extensionality with `i j`. Use `BlockEmbeddingFactors.blockEmb_out b c h g i j (fun x => hce (i.2.symm.trans x.1))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply, Subtype.ext_iff]`.
-/
theorem diagBlock_emb_ne (b : Fin r → ℕ) (c e : ℕ) (hce : e ≠ c) {d : ℕ} (h : Fintype.card (BlockEmbeddingFactors.Block b c) = d)
    (g : GL (Fin d) F) : diagBlock b e (BlockEmbeddingFactors.blockEmb b c h g) = 1 := by
  ext i j
  have := BlockEmbeddingFactors.blockEmb_out b c h g i j (fun x => hce (i.2.symm.trans x.1))
  refine this.trans ?_
  simp [Matrix.one_apply, Subtype.ext_iff]

variable {V : Type} [AddCommGroup V] [Module ℂ V] {V' : Type} [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Establish `h : σ (x * y⁻¹) = 1`. Use `hσ.infl _ fun i j hij => ?_` and prove the remaining obligations. Establish `h1 : diagBlock b (b j) (x * y⁻¹) = 1` using `by rw [map_mul, H, ← map_mul, mul_inv_cancel, map_one]`. Establish `h2` using `congrFun (congrFun h1 ⟨i, hij⟩) ⟨j, rfl⟩`. Use `Eq.trans h2 ?_` and prove the remaining obligations.

Simplify using `[Matrix.one_apply, Subtype.ext_iff]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem apply_eq_of_diagBlock {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ)
    {x y : blockTri (κ := F) b} (H : ∀ e, diagBlock b e x = diagBlock b e y) : σ x = σ y := by
  have h : σ (x * y⁻¹) = 1 := by
    refine hσ.infl _ fun i j hij => ?_
    have h1 : diagBlock b (b j) (x * y⁻¹) = 1 := by rw [map_mul, H, ← map_mul, mul_inv_cancel, map_one]
    have h2 := congrFun (congrFun h1 ⟨i, hij⟩) ⟨j, rfl⟩
    refine Eq.trans h2 ?_
    simp [Matrix.one_apply, Subtype.ext_iff]
  calc σ x = σ (x * y⁻¹ * y) := by rw [inv_mul_cancel_right]
    _ = σ y := by rw [map_mul, h, one_mul]

/- English proof (translation)
Simplify using `[BlockProductIsomorphism.block, Fintype.card_subtype]`.
-/
theorem card_block (b : Fin r → ℕ) (c : ℕ) : Fintype.card (BlockEmbeddingFactors.Block b c) = (BlockProductIsomorphism.block b c).card := by
  simp [BlockProductIsomorphism.block, Fintype.card_subtype]

/- English proof (translation)
Establish `he : ∀ a, (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h' a).1 = BlockProductIsomorphism.blockEnum b c h a`. Use `Finset.orderEmbOfFin_unique h (f := fun a => (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h' a).1) (fun a => Finset.mem_filter.2 ⟨Finset.mem_univ _, (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h' a).2⟩) (fun a a' haa => (monoEquivOfFin (BlockEmbeddingFactors.Block b c) …` as an intermediate fact. Conclude with `fun a => congrFun this a`. Use extensionality with `g i j`. Use `show BlockProductIsomorphism.extendMat (BlockProductIsomorphism.blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = _`.

Distinguish the cases in `hij : b i = c ∧ b j = c`. Take `⟨a, ha⟩` from `(monoEquivOfFin (BlockEmbeddingFactors.Block b c) h').surjective ⟨i, hij.1⟩`. Take `⟨a', ha'⟩` from `(monoEquivOfFin (BlockEmbeddingFactors.Block b c) h').surjective ⟨j, hij.2⟩`. Establish `h1` using `BlockEmbeddingFactors.blockEmb_in b c h' g a a'`. Establish `h2` using `BlockProductIsomorphism.extendMat_in (BlockProductIsomorphism.blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) a a'`.

Rewrite `h2` using `[← he, ← he]`. Rewrite `h1`, `h2` using `[ha, ha']`. Conclude with `h2.trans h1.symm`. Rewrite using `[BlockEmbeddingFactors.blockEmb_out b c h' g i j hij, BlockProductIsomorphism.extendMat_out]`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Take `⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩` from `hc`. Conclude with `hij ⟨BlockProductIsomorphism.blockEnum_mem b c h a, BlockProductIsomorphism.blockEnum_mem b c h a'⟩`.
-/
theorem blockHom_eq (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : (BlockProductIsomorphism.block b c).card = d)
    (h' : Fintype.card (BlockEmbeddingFactors.Block b c) = d) : BlockProductIsomorphism.blockHom F b c h = BlockEmbeddingFactors.blockEmb b c h' := by
  have he : ∀ a, (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h' a).1 = BlockProductIsomorphism.blockEnum b c h a := by
    have := Finset.orderEmbOfFin_unique h (f := fun a => (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h' a).1)
      (fun a => Finset.mem_filter.2 ⟨Finset.mem_univ _, (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h' a).2⟩)
      (fun a a' haa => (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h').strictMono haa)
    exact fun a => congrFun this a
  ext g i j
  show BlockProductIsomorphism.extendMat (BlockProductIsomorphism.blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = _
  by_cases hij : b i = c ∧ b j = c
  · obtain ⟨a, ha⟩ := (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h').surjective ⟨i, hij.1⟩
    obtain ⟨a', ha'⟩ := (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h').surjective ⟨j, hij.2⟩
    have h1 := BlockEmbeddingFactors.blockEmb_in b c h' g a a'
    have h2 := BlockProductIsomorphism.extendMat_in (BlockProductIsomorphism.blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) a a'
    rw [← he, ← he] at h2
    rw [ha, ha'] at h1 h2
    exact h2.trans h1.symm
  · rw [BlockEmbeddingFactors.blockEmb_out b c h' g i j hij, BlockProductIsomorphism.extendMat_out]
    by_contra hc
    push Not at hc
    obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hc
    exact hij ⟨BlockProductIsomorphism.blockEnum_mem b c h a, BlockProductIsomorphism.blockEnum_mem b c h a'⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hρ, h, H⟩`. Use `⟨(card_block b c).trans h, hρ, ?_⟩` and prove the remaining obligations. Rewrite `H` using `[blockHom_eq b c h ((card_block b c).trans h)]`. Conclude with `(isotypic_iff _ ρ hρ).1 H`.

Introduce and unpack `⟨h, hρ, H⟩`. Use `⟨hρ, (card_block b c).symm.trans h, ?_⟩` and prove the remaining obligations. Rewrite using `[blockHom_eq b c _ h]`. Conclude with `(isotypic_iff _ ρ hρ).2 H`.
-/
theorem isFactor_iff [Finite F] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ) {d : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin d) F) W) :
    BlockProductIsomorphism.IsFactor b σ c ρ ↔ ∃ h, BlockEmbeddingFactors.HasFactor b σ c h ρ := by
  constructor
  · rintro ⟨hρ, h, H⟩
    refine ⟨(card_block b c).trans h, hρ, ?_⟩
    rw [blockHom_eq b c h ((card_block b c).trans h)] at H
    exact (isotypic_iff _ ρ hρ).1 H
  · rintro ⟨h, hρ, H⟩
    refine ⟨hρ, (card_block b c).symm.trans h, ?_⟩
    rw [blockHom_eq b c _ h]
    exact (isotypic_iff _ ρ hρ).2 H

/- English proof (translation)
Establish `h` using `card_block b c`. Take `⟨W, i1, i2, ρ, hρ, H⟩` from `exists_type σ hσ.irr (BlockEmbeddingFactors.blockEmb b c h) fun p => by`. Set `E` to `(Matrix.reindexAlgEquiv F F (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h).toEquiv).toMulEquiv`. Set `g : GL (Fin (BlockProductIsomorphism.block b c).card) F` to `(E.symm.toMonoidHom.comp (diagBlock b c)).toHomUnits p`. Establish `hg : diagBlock b c (BlockEmbeddingFactors.blockEmb b c h g) = diagBlock b c p`.

Rewrite using `[diagBlock_emb_self]`. Conclude with `E.apply_symm_apply _`. Use `⟨g, p * (BlockEmbeddingFactors.blockEmb b c h g)⁻¹, by rw [inv_mul_cancel_right], fun x => ?_⟩` and prove the remaining obligations. Use `apply_eq_of_diagBlock hσ fun e => ?_` and prove the remaining obligations. Rewrite using `[map_mul _ (p * _), map_mul _ _ (p * _)]`.

Distinguish the cases in `he : e = c`. Substitute `he` using the available equality. Rewrite using `[map_mul, ← hg, ← map_mul, mul_inv_cancel, map_one, one_mul, mul_one]`. Rewrite using `[diagBlock_emb_ne b c e he, one_mul, mul_one]`. Use `⟨W, i1, i2, ρ, hρ, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[blockHom_eq b c rfl h]`. Conclude with `H`.
-/
theorem exists_factor [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ)
    (c : ℕ) : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (ρ : Representation ℂ (GL (Fin (BlockProductIsomorphism.block b c).card) F) W), BlockProductIsomorphism.IsFactor b σ c ρ := by
  have h := card_block b c
  obtain ⟨W, i1, i2, ρ, hρ, H⟩ := exists_type σ hσ.irr (BlockEmbeddingFactors.blockEmb b c h) fun p => by
    let E := (Matrix.reindexAlgEquiv F F (monoEquivOfFin (BlockEmbeddingFactors.Block b c) h).toEquiv).toMulEquiv
    let g : GL (Fin (BlockProductIsomorphism.block b c).card) F := (E.symm.toMonoidHom.comp (diagBlock b c)).toHomUnits p
    have hg : diagBlock b c (BlockEmbeddingFactors.blockEmb b c h g) = diagBlock b c p := by
      rw [diagBlock_emb_self]
      exact E.apply_symm_apply _
    refine ⟨g, p * (BlockEmbeddingFactors.blockEmb b c h g)⁻¹, by rw [inv_mul_cancel_right], fun x => ?_⟩
    refine apply_eq_of_diagBlock hσ fun e => ?_
    rw [map_mul _ (p * _), map_mul _ _ (p * _)]
    by_cases he : e = c
    · subst he
      rw [map_mul, ← hg, ← map_mul, mul_inv_cancel, map_one, one_mul, mul_one]
    · rw [diagBlock_emb_ne b c e he, one_mul, mul_one]
  refine ⟨W, i1, i2, ρ, hρ, rfl, ?_⟩
  rw [blockHom_eq b c rfl h]
  exact H

/- English proof (translation)
Take `⟨h, H⟩` from `(isFactor_iff b σ c ρ).1 H`. Take `⟨h', H'⟩` from `(isFactor_iff b' σ' c' ρ').1 H'`. Prove the components needed by the constructor for the conclusion. Introduce `hiso`. Take `rfl : d' = d` from `hiso.1`.

Take `⟨e⟩` from `(nonempty_equiv_iff _ _).1 ((BlockProductIsomorphism.isoGL_iff ρ ρ').1 hiso)`. Conclude with `⟨d', h, h', W, _, _, ρ, H, H.1, H'.2.of_linearEquiv_type e.symm⟩`. Introduce and unpack `⟨d₀, h₀, h₀', W₀, _, _, ρ₀, K, K'⟩`. Take `rfl : d₀ = d` from `h₀.symm.trans h`. Take `rfl : d₀ = d'` from `h₀'.symm.trans h'`.

Take `⟨e⟩` from `type_unique _ _ _ H.2 K.2`. Take `⟨e'⟩` from `type_unique _ _ _ K'.2 H'.2`. Conclude with `(BlockProductIsomorphism.isoGL_iff ρ ρ').2 ((nonempty_equiv_iff _ _).2 ⟨e.trans e'⟩)`.
-/
theorem isoGL_iff_sameFactor [Finite F] [Nontrivial V] [Nontrivial V'] {b b' : Fin r → ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) V} {σ' : Representation ℂ (blockTri (κ := F) b') V'} {c c' d d' : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] {W' : Type} [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ (GL (Fin d) F) W} {ρ' : Representation ℂ (GL (Fin d') F) W'}
    (H : BlockProductIsomorphism.IsFactor b σ c ρ) (H' : BlockProductIsomorphism.IsFactor b' σ' c' ρ') :
    BlockProductIsomorphism.IsoGL ρ ρ' ↔ BlockEmbeddingFactors.SameFactor b σ c b' σ' c' := by
  obtain ⟨h, H⟩ := (isFactor_iff b σ c ρ).1 H
  obtain ⟨h', H'⟩ := (isFactor_iff b' σ' c' ρ').1 H'
  constructor
  · intro hiso
    obtain rfl : d' = d := hiso.1
    obtain ⟨e⟩ := (nonempty_equiv_iff _ _).1 ((BlockProductIsomorphism.isoGL_iff ρ ρ').1 hiso)
    exact ⟨d', h, h', W, _, _, ρ, H, H.1, H'.2.of_linearEquiv_type e.symm⟩
  · rintro ⟨d₀, h₀, h₀', W₀, _, _, ρ₀, K, K'⟩
    obtain rfl : d₀ = d := h₀.symm.trans h
    obtain rfl : d₀ = d' := h₀'.symm.trans h'
    obtain ⟨e⟩ := type_unique _ _ _ H.2 K.2
    obtain ⟨e'⟩ := type_unique _ _ _ K'.2 H'.2
    exact (BlockProductIsomorphism.isoGL_iff ρ ρ').2 ((nonempty_equiv_iff _ _).2 ⟨e.trans e'⟩)

/- English proof (translation)
Use `nontrivial_of_irr σ H.1.irr` as an intermediate fact. Conclude with `⟨H.1, fun c hc c' hc' hne hs => H.2.2 c hc c' hc' hne ((isoGL_iff_sameFactor (H.2.1 c hc) (H.2.1 c' hc')).2 hs)⟩`.
-/
theorem distinct_of_regular [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    {d : ℕ → ℕ} {W : ℕ → Type} [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    {ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)} (H : BlockProductIsomorphism.IsRegularCusp b σ d W ρ) :
    IsCuspDatum b σ ∧ BlockEmbeddingFactors.DistinctFactors b σ := by
  have := nontrivial_of_irr σ H.1.irr
  exact ⟨H.1, fun c hc c' hc' hne hs =>
    H.2.2 c hc c' hc' hne ((isoGL_iff_sameFactor (H.2.1 c hc) (H.2.1 c' hc')).2 hs)⟩

/- English proof (translation)
Use `nontrivial_of_irr σ hσ.irr` as an intermediate fact. Use `choose W i1 i2 ρ hρ using exists_factor hσ`. Conclude with `⟨_, W, i1, i2, ρ, hσ, fun c _ => hρ c, fun c hc c' hc' hne hs => hd c hc c' hc' hne ((isoGL_iff_sameFactor (hρ c) (hρ c')).1 hs)⟩`.
-/
theorem regular_of_distinct [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    (hσ : IsCuspDatum b σ) (hd : BlockEmbeddingFactors.DistinctFactors b σ) :
    ∃ (d : ℕ → ℕ) (W : ℕ → Type) (_ : ∀ c, AddCommGroup (W c)) (_ : ∀ c, Module ℂ (W c))
      (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)), BlockProductIsomorphism.IsRegularCusp b σ d W ρ := by
  have := nontrivial_of_irr σ hσ.irr
  choose W i1 i2 ρ hρ using exists_factor hσ
  exact ⟨_, W, i1, i2, ρ, hσ, fun c _ => hρ c, fun c hc c' hc' hne hs =>
    hd c hc c' hc' hne ((isoGL_iff_sameFactor (hρ c) (hρ c')).1 hs)⟩

/- English proof (translation)
Use `nontrivial_of_irr σ H.1.irr` as an intermediate fact. Use `nontrivial_of_irr σ' H'.1.irr` as an intermediate fact. Conclude with `and_congr (forall₂_congr fun c hc => exists_congr fun c' => and_congr_right fun hc' => isoGL_iff_sameFactor (H.2.1 c hc) (H'.2.1 c' hc')) (forall₂_congr fun c' hc' => exists_congr fun c => and_congr_right fun hc => isoGL_iff_sameFactor (H.2.1 c hc) (H'.2.1 c' hc'))`.
-/
theorem factorSet_iff [Finite F] {b b' : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    {σ' : Representation ℂ (blockTri (κ := F) b') V'}
    {d : ℕ → ℕ} {W : ℕ → Type} [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    {ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)}
    {d' : ℕ → ℕ} {W' : ℕ → Type} [∀ c, AddCommGroup (W' c)] [∀ c, Module ℂ (W' c)]
    {ρ' : ∀ c, Representation ℂ (GL (Fin (d' c)) F) (W' c)}
    (H : BlockProductIsomorphism.IsRegularCusp b σ d W ρ) (H' : BlockProductIsomorphism.IsRegularCusp b' σ' d' W' ρ') :
    ((∀ c ∈ Set.range b, ∃ c' ∈ Set.range b', BlockProductIsomorphism.IsoGL (ρ c) (ρ' c')) ∧
      (∀ c' ∈ Set.range b', ∃ c ∈ Set.range b, BlockProductIsomorphism.IsoGL (ρ c) (ρ' c'))) ↔ BlockEmbeddingFactors.SameFactorSet b σ b' σ' := by
  have := nontrivial_of_irr σ H.1.irr
  have := nontrivial_of_irr σ' H'.1.irr
  exact and_congr
    (forall₂_congr fun c hc => exists_congr fun c' => and_congr_right fun hc' =>
      isoGL_iff_sameFactor (H.2.1 c hc) (H'.2.1 c' hc'))
    (forall₂_congr fun c' hc' => exists_congr fun c => and_congr_right fun hc =>
      isoGL_iff_sameFactor (H.2.1 c hc) (H'.2.1 c' hc'))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H F _ _ r b V _ _ _ σ hσ hd`. Take `⟨d, W, _, _, ρ, h⟩` from `regular_of_distinct hσ hd`. Conclude with `H F r b V σ d W ρ h`. Introduce `H F _ _ r b V _ _ σ d W _ _ ρ h`.

Use `finiteDimensional_of_irr σ h.1.irr` as an intermediate fact. Conclude with `H F r b V σ h.1 (distinct_of_regular h).2`.
-/
theorem productIrreducible_iff : BlockProductIsomorphism.ProductIrreducible ↔ BlockEmbeddingFactors.ProductIrreducible := by
  constructor
  · intro H F _ _ r b V _ _ _ σ hσ hd
    obtain ⟨d, W, _, _, ρ, h⟩ := regular_of_distinct hσ hd
    exact H F r b V σ d W ρ h
  · intro H F _ _ r b V _ _ σ d W _ _ ρ h
    have := finiteDimensional_of_irr σ h.1.irr
    exact H F r b V σ h.1 (distinct_of_regular h).2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H F _ _ r b b' V _ _ _ V' _ _ _ σ σ' hσ hd hσ' hd'`. Take `⟨d, W, _, _, ρ, h⟩` from `regular_of_distinct hσ hd`. Take `⟨d', W', _, _, ρ', h'⟩` from `regular_of_distinct hσ' hd'`. Conclude with `(H F r b V σ d W ρ b' V' σ' d' W' ρ' h h').trans (factorSet_iff h h')`.

Introduce `H F _ _ r b V _ _ σ d W _ _ ρ b' V' _ _ σ' d' W' _ _ ρ' h h'`. Use `finiteDimensional_of_irr σ h.1.irr` as an intermediate fact. Use `finiteDimensional_of_irr σ' h'.1.irr` as an intermediate fact. Conclude with `(H F r b b' V V' σ σ' h.1 (distinct_of_regular h).2 h'.1 (distinct_of_regular h').2).trans (factorSet_iff h h').symm`.
-/
theorem productIsoIff_iff : BlockProductIsomorphism.ProductIsoIff ↔ BlockEmbeddingFactors.ProductIsoIff := by
  constructor
  · intro H F _ _ r b b' V _ _ _ V' _ _ _ σ σ' hσ hd hσ' hd'
    obtain ⟨d, W, _, _, ρ, h⟩ := regular_of_distinct hσ hd
    obtain ⟨d', W', _, _, ρ', h'⟩ := regular_of_distinct hσ' hd'
    exact (H F r b V σ d W ρ b' V' σ' d' W' ρ' h h').trans (factorSet_iff h h')
  · intro H F _ _ r b V _ _ σ d W _ _ ρ b' V' _ _ σ' d' W' _ _ ρ' h h'
    have := finiteDimensional_of_irr σ h.1.irr
    have := finiteDimensional_of_irr σ' h'.1.irr
    exact (H F r b b' V V' σ σ' h.1 (distinct_of_regular h).2 h'.1 (distinct_of_regular h').2).trans
      (factorSet_iff h h').symm

/- English proof (translation)
The claim follows from `and_congr productIrreducible_iff productIsoIff_iff`.
-/
theorem irrPar_iff_cuspidalProduct : BlockProductIsomorphism.IrrPar ↔ BlockEmbeddingFactors.CuspidalProduct :=
  and_congr productIrreducible_iff productIsoIff_iff

end GlobalTheory.CuspFactor
