import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Introduce `p A A' _ _ g h1 h2 h3`. Unfold `pIdx pTor pows at *`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `set f : A →* A := powMonoidHom p with hf`. Establish `hP : ((⊤ : Subgroup A).map f).relIndex g.ker ≠ 0` using `fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right le_top h0)`.

Establish `hBD : g.ker ≤ g.ker.comap f`. Introduce `x hx`. Conclude with `g.ker.pow_mem hx p`. Establish `hD : g.ker.relIndex (g.ker.comap f) ≠ 0`. Rewrite using `[Subgroup.relIndex_ker]`.

Establish `: Nat.card ((g.ker.comap f).map g) = Nat.card {x : A' // x ∈ g.range ∧ x ^ p = 1}`. Use `Nat.card_congr (Equiv.subtypeEquivRight ?_)` and prove the remaining obligations. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`.

Use `⟨⟨a, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: g (a ^ p) = 1` using `ha`. Rewrite `this` using `[map_pow]`. Then use the resulting hypothesis. Introduce and unpack `⟨⟨a, rfl⟩, ha⟩`. Use `⟨a, ?_, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g (a ^ p) = 1`. Rewrite using `[map_pow]` and apply the resulting hypothesis. Rewrite using `[this]`. Conclude with `h3`. Establish `hQ : (g.ker.map f).relIndex ((g.ker.comap f).map f) ≠ 0`.

Introduce `h0`. Establish `hd` using `Subgroup.relIndex_map_map f g.ker (g.ker.comap f)`. Establish `hk : f.ker ≤ g.ker.comap f`. Introduce `x hx`. Establish `: f x = 1` using `hx`.

Express the relevant statement in the definitionally equal form `f x ∈ g.ker`. Rewrite using `[this]`. Conclude with `one_mem _`. Rewrite `hd` using `[h0, sup_eq_left.2 hk]`. Establish `hdv : (g.ker ⊔ f.ker).relIndex (g.ker.comap f) ∣ g.ker.relIndex (g.ker.comap f)` using `Subgroup.relIndex_dvd_of_le_left _ le_sup_left`.

Rewrite `hdv` using `[← hd]`. Conclude with `hD (Nat.eq_zero_of_zero_dvd hdv)`. Establish `he : (g.ker.comap f).map f = ((⊤ : Subgroup A).map f) ⊓ g.ker`. Rewrite using `[Subgroup.map_comap_eq, ← MonoidHom.range_eq_map]`. Use `Subgroup.relIndex_ne_zero_trans hQ ?_` and prove the remaining obligations.

Rewrite using `[he, Subgroup.inf_relIndex_right]`. Conclude with `hP`. Establish `hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1}` using `Nat.finite_of_card_ne_zero h2`. Establish `: Finite {x : A // x ∈ g.ker ∧ x ^ p = 1}` using `Finite.of_injective (fun x => (⟨x.1, Subgroup.mem_top _, x.2.2⟩ : {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1})) (fun x y h => Subtype.ext (congrArg (fun z => z.1) h))`. Establish `: Nonempty {x : A // x ∈ g.ker ∧ x ^ p = 1}` using `⟨⟨1, one_mem _, one_pow p⟩⟩`.

Conclude with `Nat.card_pos.ne'`. Establish `he : g.range.map (powMonoidHom p) = ((⊤ : Subgroup A).map (powMonoidHom p)).map g`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, rfl⟩, rfl⟩`.

Conclude with `⟨a ^ p, ⟨a, Subgroup.mem_top _, rfl⟩, by simp⟩`. Introduce and unpack `⟨_, ⟨a, -, rfl⟩, rfl⟩`. Conclude with `⟨g a, ⟨a, rfl⟩, by simp⟩`. Rewrite using `[he]`. Introduce `h0`.

Establish `hd` using `Subgroup.relIndex_map_map g ((⊤ : Subgroup A).map (powMonoidHom p)) ⊤`. Rewrite `hd` using `[← MonoidHom.range_eq_map g, h0, top_sup_eq]`. Establish `hdv : ((⊤ : Subgroup A).map (powMonoidHom p) ⊔ g.ker).relIndex ⊤ ∣ ((⊤ : Subgroup A).map (powMonoidHom p)).relIndex ⊤` using `Subgroup.relIndex_dvd_of_le_left _ le_sup_left`. Rewrite `hdv` using `[← hd]`. Conclude with `h1 (Nat.eq_zero_of_zero_dvd hdv)`.
-/
theorem pIdx_pTor_ker_range_ne_zero :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'),
      pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 →
      pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by
  intro p A A' _ _ g h1 h2 h3
  unfold pIdx pTor pows at *
  refine ⟨?_, ?_, ?_⟩
  · set f : A →* A := powMonoidHom p with hf
    have hP : ((⊤ : Subgroup A).map f).relIndex g.ker ≠ 0 :=
      fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right le_top h0)
    have hBD : g.ker ≤ g.ker.comap f := by
      intro x hx
      exact g.ker.pow_mem hx p
    have hD : g.ker.relIndex (g.ker.comap f) ≠ 0 := by
      rw [Subgroup.relIndex_ker]
      have : Nat.card ((g.ker.comap f).map g) = Nat.card {x : A' // x ∈ g.range ∧ x ^ p = 1} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
        intro x
        constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨⟨a, rfl⟩, ?_⟩
          have : g (a ^ p) = 1 := ha
          rwa [map_pow] at this
        · rintro ⟨⟨a, rfl⟩, ha⟩
          refine ⟨a, ?_, rfl⟩
          change g (a ^ p) = 1
          rwa [map_pow]
      rw [this]
      exact h3
    have hQ : (g.ker.map f).relIndex ((g.ker.comap f).map f) ≠ 0 := by
      intro h0
      have hd := Subgroup.relIndex_map_map f g.ker (g.ker.comap f)
      have hk : f.ker ≤ g.ker.comap f := by
        intro x hx
        have : f x = 1 := hx
        change f x ∈ g.ker
        rw [this]
        exact one_mem _
      rw [h0, sup_eq_left.2 hk] at hd
      have hdv : (g.ker ⊔ f.ker).relIndex (g.ker.comap f) ∣ g.ker.relIndex (g.ker.comap f) :=
        Subgroup.relIndex_dvd_of_le_left _ le_sup_left
      rw [← hd] at hdv
      exact hD (Nat.eq_zero_of_zero_dvd hdv)
    have he : (g.ker.comap f).map f = ((⊤ : Subgroup A).map f) ⊓ g.ker := by
      rw [Subgroup.map_comap_eq, ← MonoidHom.range_eq_map]
    refine Subgroup.relIndex_ne_zero_trans hQ ?_
    rw [he, Subgroup.inf_relIndex_right]
    exact hP
  · have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero h2
    have : Finite {x : A // x ∈ g.ker ∧ x ^ p = 1} :=
      Finite.of_injective
        (fun x => (⟨x.1, Subgroup.mem_top _, x.2.2⟩ : {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1}))
        (fun x y h => Subtype.ext (congrArg (fun z => z.1) h))
    have : Nonempty {x : A // x ∈ g.ker ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow p⟩⟩
    exact Nat.card_pos.ne'
  · have he : g.range.map (powMonoidHom p) = ((⊤ : Subgroup A).map (powMonoidHom p)).map g := by
      ext x
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a ^ p, ⟨a, Subgroup.mem_top _, rfl⟩, by simp⟩
      · rintro ⟨_, ⟨a, -, rfl⟩, rfl⟩
        exact ⟨g a, ⟨a, rfl⟩, by simp⟩
    rw [he]
    intro h0
    have hd := Subgroup.relIndex_map_map g ((⊤ : Subgroup A).map (powMonoidHom p)) ⊤
    rw [← MonoidHom.range_eq_map g, h0, top_sup_eq] at hd
    have hdv : ((⊤ : Subgroup A).map (powMonoidHom p) ⊔ g.ker).relIndex ⊤ ∣
        ((⊤ : Subgroup A).map (powMonoidHom p)).relIndex ⊤ :=
      Subgroup.relIndex_dvd_of_le_left _ le_sup_left
    rw [← hd] at hdv
    exact h1 (Nat.eq_zero_of_zero_dvd hdv)

end GlobalTheory.CNorm
