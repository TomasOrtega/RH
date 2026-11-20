import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨Representation.Equiv.mk' (Representation.IntertwiningMap.id _) id (fun _ => rfl) (fun _ => rfl)⟩`.
-/
theorem nonempty_equiv_quotient_of_eq {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P Q : Submodule ℂ W)
    (hP : ∀ g, P ≤ P.comap (σ g)) (hQ : ∀ g, Q ≤ Q.comap (σ g)) (h : P = Q) :
    Nonempty ((σ.quotient P hP).Equiv (σ.quotient Q hQ)) := by
  subst h
  exact ⟨Representation.Equiv.mk' (Representation.IntertwiningMap.id _) id
    (fun _ => rfl) (fun _ => rfl)⟩

/- English proof (translation)
Use `haveI : IsSimpleOrder (Subrepresentation (σ.quotient P hP)) := hirr`. Set `N : Subrepresentation (σ.quotient P hP)` to `⟨M.map P.mkQ, by`. Introduce and unpack `g _ ⟨m, hm, rfl⟩`. Conclude with `⟨σ g m, hM g hm, rfl⟩⟩`. Set `S₀ : Subrepresentation (σ.quotient P hP)` to `⟨⊥, by`.

Introduce `g v hv`. Rewrite `hv`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hv, map_zero]⟩`. Set `S₁ : Subrepresentation (σ.quotient P hP)` to `⟨⊤, by`. Introduce `_ _ _`.

Conclude with `Submodule.mem_top⟩`. Establish `hcomap : (M.map P.mkQ).comap P.mkQ = M`. Rewrite using `[Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hPM]`. Break down `IsSimpleOrder.eq_bot_or_eq_top N with hN | hN` into its components or cases. Use `left`.

Establish `h1 : N ⊓ S₀ = N` using `by rw [hN, bot_inf_eq]`. Establish `h2` using `congrArg Subrepresentation.toSubmodule h1`. Rewrite `h2` using `[Subrepresentation.toSubmodule_inf]`. Establish `h3 : M.map P.mkQ = ⊥` using `le_bot_iff.mp (inf_eq_left.mp h2)`. Rewrite using `[← hcomap, h3, Submodule.comap_bot, Submodule.ker_mkQ]`.

Use `right`. Establish `h1 : N ⊔ S₁ = N` using `by rw [hN, top_sup_eq]`. Establish `h2` using `congrArg Subrepresentation.toSubmodule h1`. Rewrite `h2` using `[Subrepresentation.toSubmodule_sup]`. Establish `h3 : M.map P.mkQ = ⊤` using `top_le_iff.mp (sup_eq_left.mp h2)`.

Rewrite using `[← hcomap, h3, Submodule.comap_top]`.
-/
theorem eq_or_eq_top_of_isIrreducible_quotient {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P : Submodule ℂ W) (hP : ∀ g, P ≤ P.comap (σ g))
    (hirr : (σ.quotient P hP).IsIrreducible) (M : Submodule ℂ W)
    (hM : ∀ g, M ≤ M.comap (σ g)) (hPM : P ≤ M) : M = P ∨ M = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation (σ.quotient P hP)) := hirr
  let N : Subrepresentation (σ.quotient P hP) :=
    ⟨M.map P.mkQ, by
      rintro g _ ⟨m, hm, rfl⟩
      exact ⟨σ g m, hM g hm, rfl⟩⟩
  let S₀ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊥, by
      intro g v hv
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]⟩
  let S₁ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊤, by
      intro _ _ _
      exact Submodule.mem_top⟩
  have hcomap : (M.map P.mkQ).comap P.mkQ = M := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hPM]
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · left
    have h1 : N ⊓ S₀ = N := by rw [hN, bot_inf_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_inf] at h2
    have h3 : M.map P.mkQ = ⊥ := le_bot_iff.mp (inf_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_bot, Submodule.ker_mkQ]
  · right
    have h1 : N ⊔ S₁ = N := by rw [hN, top_sup_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_sup] at h2
    have h3 : M.map P.mkQ = ⊤ := top_le_iff.mp (sup_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_top]

/- English proof (translation)
Establish `hPK : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ≤ (K.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g)`. Introduce `g x hx`. Conclude with `K.2 g hx`. Establish `hPL : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ≤ (L.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g)`. Introduce `g x hx`.

Conclude with `L.2 g hx`. Establish `hK' : (E.toRepresentation.quotient _ hPK).IsIrreducible` using `hK`. Establish `hL' : (E.toRepresentation.quotient _ hPL).IsIrreducible` using `hL`. Establish `hsup : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≤ (K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g)`. Introduce `g`.

Conclude with `sup_le ((hPK g).trans (Submodule.comap_mono le_sup_left)) ((hPL g).trans (Submodule.comap_mono le_sup_right))`. Establish `hsup' : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≤ (L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g)`. Introduce `g`. Rewrite using `[sup_comm]`. Conclude with `hsup g`.

Establish `hne : K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤`. Introduce `htop`. Apply `hE` to reduce the goal to its premises. Establish `hle : E.toSubmodule ≤ E.toSubmodule ⊓ K.toSubmodule ⊔ E.toSubmodule ⊓ L.toSubmodule`. Introduce `x hx`.

Establish `hmem : (⟨x, hx⟩ : E.toSubmodule) ∈ K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hmem`. Conclude with `Submodule.mem_sup.mpr ⟨y, ⟨y.2, hy⟩, z, ⟨z.2, hz⟩, congrArg Subtype.val hyz⟩`.

Rewrite using `[← inf_eq_left]`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_inf]`. Conclude with `inf_eq_left.mpr hle`. Establish `hne' : L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤`.

Rewrite using `[sup_comm]`. Conclude with `hne`. Establish `h1` using `(GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPK hK' _ hsup le_sup_left).resolve_right hne`. Establish `h2` using `(GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPL hL' _ hsup' le_sup_left).resolve_right hne'`. Establish `hPQ : K.toSubmodule.comap E.toSubmodule.subtype = L.toSubmodule.comap E.toSubmodule.subtype` using `le_antisymm (sup_eq_left.mp h2) (sup_eq_left.mp h1)`.

Conclude with `GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_quotient_of_eq E.toRepresentation _ _ hPK hPL hPQ`.
-/
theorem nonempty_equiv_subQuot (ρ : Representation ℂ G V) (E K L : Subrepresentation ρ)
    (hK : (subQuot E K).IsIrreducible) (hL : (subQuot E L).IsIrreducible)
    (hE : ¬ E ≤ E ⊓ K ⊔ E ⊓ L) : Nonempty ((subQuot E K).Equiv (subQuot E L)) := by
  have hPK : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact K.2 g hx
  have hPL : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact L.2 g hx
  have hK' : (E.toRepresentation.quotient _ hPK).IsIrreducible := hK
  have hL' : (E.toRepresentation.quotient _ hPL).IsIrreducible := hL
  have hsup : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    exact sup_le ((hPK g).trans (Submodule.comap_mono le_sup_left))
      ((hPL g).trans (Submodule.comap_mono le_sup_right))
  have hsup' : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    rw [sup_comm]
    exact hsup g
  have hne : K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    intro htop
    apply hE
    have hle : E.toSubmodule ≤ E.toSubmodule ⊓ K.toSubmodule ⊔ E.toSubmodule ⊓ L.toSubmodule := by
      intro x hx
      have hmem : (⟨x, hx⟩ : E.toSubmodule) ∈
          K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      exact Submodule.mem_sup.mpr ⟨y, ⟨y.2, hy⟩, z, ⟨z.2, hz⟩, congrArg Subtype.val hyz⟩
    rw [← inf_eq_left]
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_sup,
      Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_inf]
    exact inf_eq_left.mpr hle
  have hne' : L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    rw [sup_comm]
    exact hne
  have h1 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPK hK' _ hsup le_sup_left).resolve_right hne
  have h2 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPL hL' _ hsup' le_sup_left).resolve_right hne'
  have hPQ : K.toSubmodule.comap E.toSubmodule.subtype = L.toSubmodule.comap E.toSubmodule.subtype :=
    le_antisymm (sup_eq_left.mp h2) (sup_eq_left.mp h1)
  exact GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_quotient_of_eq E.toRepresentation _ _ hPK hPL hPQ

end GlobalTheory.CompanionTheory.GenCore
