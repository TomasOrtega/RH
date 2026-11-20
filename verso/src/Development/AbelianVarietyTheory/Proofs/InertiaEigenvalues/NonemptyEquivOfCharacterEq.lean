import Mathlib

namespace GlobalTheory.CharacterDetermines

open Representation Module

variable {G V W V' W' : Type} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

noncomputable def prodEquivOfIsCompl {ρ : Representation ℂ G V} (p q : Subrepresentation ρ)
    (h : IsCompl p.toSubmodule q.toSubmodule) :
    (p.toRepresentation.prod q.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl _ _ h) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    simp [Representation.prod, Subrepresentation.toRepresentation]

noncomputable def prodCongr {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (e : ρ.Equiv σ) (e' : ρ'.Equiv σ') : (ρ.prod ρ').Equiv (σ.prod σ') :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr e'.toLinearEquiv) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    refine Prod.ext ?_ ?_
    · exact e.toIntertwiningMap.isIntertwining _ _ g a
    · exact e'.toIntertwiningMap.isIntertwining _ _ g b

/- English proof (translation)
Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g)) = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)`. Rewrite using `[LinearMap.trace_prodMap']`.
-/
theorem character_prod [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  funext g
  change LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g)) = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)
  rw [LinearMap.trace_prodMap']

/- English proof (translation)
Establish `: NeZero (Nat.card G : ℂ)` using `⟨by exact_mod_cast Nat.card_pos.ne'⟩`. Take `⟨c, hc⟩` from `MonoidAlgebra.Submodule.exists_isCompl (Subrepresentation.asSubmodule p)`. Use `⟨Subrepresentation.ofSubmodule' c, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`.

Introduce `x hx hx'`. Conclude with `(Submodule.disjoint_def.mp hc.disjoint) x hx hx'`. Rewrite using `[codisjoint_iff, Submodule.eq_top_iff']`. Introduce `x`. Establish `hx : (show ρ.asModule from x) ∈ (Subrepresentation.asSubmodule p ⊔ c)`.

Rewrite using `[hc.sup_eq_top]`. Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hx`. Conclude with `Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩`.
-/
theorem exists_isCompl [Finite G] {ρ : Representation ℂ G V} (p : Subrepresentation ρ) :
    ∃ q : Subrepresentation ρ, IsCompl p.toSubmodule q.toSubmodule := by
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨c, hc⟩ := MonoidAlgebra.Submodule.exists_isCompl (Subrepresentation.asSubmodule p)
  refine ⟨Subrepresentation.ofSubmodule' c, ?_⟩
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact (Submodule.disjoint_def.mp hc.disjoint) x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : (show ρ.asModule from x) ∈ (Subrepresentation.asSubmodule p ⊔ c) := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩

/- English proof (translation)
Set `φ : q.toSubmodule →ₗ[ℂ] f.range.toSubmodule` to `(f.toLinearMap.comp q.toSubmodule.subtype).codRestrict f.range.toSubmodule (fun v => LinearMap.mem_range_self _ _)`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `ha' : f.toLinearMap (a : V) = 0` using `congrArg Subtype.val ha`.

Establish `hk : (a : V) ∈ f.ker.toSubmodule` using `ha'`. Conclude with `Subtype.ext ((Submodule.disjoint_def.mp h.disjoint) _ hk a.2)`. Establish `hsurj : Function.Surjective φ`. Introduce and unpack `⟨w, v, rfl⟩`. Establish `hv : v ∈ f.ker.toSubmodule ⊔ q.toSubmodule`.

Rewrite using `[h.sup_eq_top]`. Conclude with `Submodule.mem_top`. Take `⟨k, hk, u, hu, hku⟩` from `Submodule.mem_sup.mp hv`. Use `⟨⟨u, hu⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hk' : f.toLinearMap k = 0` using `hk`.

Express the relevant statement in the definitionally equal form `f.toLinearMap u = f.toLinearMap v`. Rewrite using `[← hku, map_add, hk', zero_add]`. Set `ψ : IntertwiningMap q.toRepresentation f.range.toRepresentation` to `φ.intertwiningMap_of_isIntertwiningMap _ _ (by`. Introduce `g v`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `f.toLinearMap (ρ g (v : V)) = σ g (f.toLinearMap v)`. Conclude with `IntertwiningMap.isIntertwining _ _ f g v)`. Conclude with `⟨ψ.ofBijective ⟨hinj, hsurj⟩⟩`.
-/
theorem nonempty_equiv_range {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : IntertwiningMap ρ σ) (q : Subrepresentation ρ)
    (h : IsCompl f.ker.toSubmodule q.toSubmodule) :
    Nonempty (q.toRepresentation.Equiv f.range.toRepresentation) := by
  let φ : q.toSubmodule →ₗ[ℂ] f.range.toSubmodule :=
    (f.toLinearMap.comp q.toSubmodule.subtype).codRestrict f.range.toSubmodule
      (fun v => LinearMap.mem_range_self _ _)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : f.toLinearMap (a : V) = 0 := congrArg Subtype.val ha
    have hk : (a : V) ∈ f.ker.toSubmodule := ha'
    exact Subtype.ext ((Submodule.disjoint_def.mp h.disjoint) _ hk a.2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨w, v, rfl⟩
    have hv : v ∈ f.ker.toSubmodule ⊔ q.toSubmodule := by
      rw [h.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    have hk' : f.toLinearMap k = 0 := hk
    change f.toLinearMap u = f.toLinearMap v
    rw [← hku, map_add, hk', zero_add]
  let ψ : IntertwiningMap q.toRepresentation f.range.toRepresentation :=
    φ.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      apply Subtype.ext
      change f.toLinearMap (ρ g (v : V)) = σ g (f.toLinearMap v)
      exact IntertwiningMap.isIntertwining _ _ f g v)
  exact ⟨ψ.ofBijective ⟨hinj, hsurj⟩⟩

/- English proof (translation)
Use `Fintype.ofFinite G` as an intermediate fact. Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')`. Establish `h1` using `card_inv_mul_sum_char_mul_char_eq_finrank ρ σ`. Establish `h2` using `card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ`. Rewrite `h1` using `[← h, h2]`.

Establish `hid : IntertwiningMap.id ρ ≠ 0`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Introduce `h0`. Conclude with `hv (by simpa using DFunLike.congr_fun h0 v)`. Establish `hpos : 0 < finrank ℂ (IntertwiningMap ρ ρ)` using `Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid⟩`.

Establish `heq : finrank ℂ (IntertwiningMap ρ ρ) = finrank ℂ (IntertwiningMap ρ σ)`. Conclude with `h1` after adjusting the coercions. Rewrite `hpos` using `[heq]`. Conclude with `Module.finrank_pos_iff_exists_ne_zero.mp hpos`.
-/
theorem exists_ne_zero [Finite G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (h : ρ.character = σ.character) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [← h, h2] at h1
  have hid : IntertwiningMap.id ρ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0
    exact hv (by simpa using DFunLike.congr_fun h0 v)
  have hpos : 0 < finrank ℂ (IntertwiningMap ρ ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid⟩
  have heq : finrank ℂ (IntertwiningMap ρ ρ) = finrank ℂ (IntertwiningMap ρ σ) := by
    exact_mod_cast h1
  rw [heq] at hpos
  exact Module.finrank_pos_iff_exists_ne_zero.mp hpos

/- English proof (translation)
Use `Nat.strong_induction_on n ?_` and prove the remaining obligations. Introduce `n ih V W _ _ _ _ _ _ ρ σ hn h`. Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Establish `hW : finrank ℂ V = finrank ℂ W`. Establish `h1` using `congrFun h 1`.

Rewrite `h1` using `[char_one, char_one]`. Conclude with `h1` after adjusting the coercions. Use `⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hW) fun g => ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Rewrite using `[Subsingleton.elim v 0]`.

Simplify using the standard rewrite rules. Take `⟨f, hf⟩` from `exists_ne_zero ρ σ h`. Take `⟨q, hq⟩` from `exists_isCompl f.ker`. Take `⟨r, hr⟩` from `exists_isCompl f.range`. Take `⟨e⟩` from `nonempty_equiv_range f q hq`.

Establish `h1` using `char_iso (prodEquivOfIsCompl q f.ker hq.symm)`. Establish `h2` using `char_iso (prodEquivOfIsCompl f.range r hr)`. Rewrite `h1`, `h2` using `[character_prod]`. Establish `h3` using `char_iso e`. Establish `hsum : q.toRepresentation.character + f.ker.toRepresentation.character = f.range.toRepresentation.character + r.toRepresentation.character`.

Rewrite using `[h1, h2, h]`. Rewrite `hsum` using `[h3]`. Establish `hK` using `add_left_cancel hsum`. Establish `hlt : finrank ℂ f.ker.toSubmodule < n`. Rewrite using `[← hn]`.

Apply `Submodule.finrank_lt` to reduce the goal to its premises. Introduce `htop`. Apply `hf` to reduce the goal to its premises. Use extensionality with `v`. Establish `hv : v ∈ f.ker.toSubmodule` using `htop ▸ Submodule.mem_top`.

Establish `hv' : f.toLinearMap v = 0` using `hv`. Simplify using `using hv'`. Take `⟨eK⟩` from `ih _ hlt f.ker.toSubmodule r.toSubmodule f.ker.toRepresentation r.toRepresentation rfl hK`. Conclude with `⟨((prodEquivOfIsCompl q f.ker hq.symm).symm.trans (prodCongr e eK)).trans (prodEquivOfIsCompl f.range r hr)⟩`.
-/
theorem aux [Finite G] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), finrank ℂ V = n →
    ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  refine Nat.strong_induction_on n ?_
  intro n ih V W _ _ _ _ _ _ ρ σ hn h
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hW : finrank ℂ V = finrank ℂ W := by
      have h1 := congrFun h 1
      rw [char_one, char_one] at h1
      exact_mod_cast h1
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hW) fun g => ?_⟩
    ext v
    rw [Subsingleton.elim v 0]
    simp
  · obtain ⟨f, hf⟩ := exists_ne_zero ρ σ h
    obtain ⟨q, hq⟩ := exists_isCompl f.ker
    obtain ⟨r, hr⟩ := exists_isCompl f.range
    obtain ⟨e⟩ := nonempty_equiv_range f q hq
    have h1 := char_iso (prodEquivOfIsCompl q f.ker hq.symm)
    have h2 := char_iso (prodEquivOfIsCompl f.range r hr)
    rw [character_prod] at h1 h2
    have h3 := char_iso e
    have hsum : q.toRepresentation.character + f.ker.toRepresentation.character =
        f.range.toRepresentation.character + r.toRepresentation.character := by
      rw [h1, h2, h]
    rw [h3] at hsum
    have hK := add_left_cancel hsum
    have hlt : finrank ℂ f.ker.toSubmodule < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hf
      ext v
      have hv : v ∈ f.ker.toSubmodule := htop ▸ Submodule.mem_top
      have hv' : f.toLinearMap v = 0 := hv
      simpa using hv'
    obtain ⟨eK⟩ := ih _ hlt f.ker.toSubmodule r.toSubmodule f.ker.toRepresentation
      r.toRepresentation rfl hK
    exact ⟨((prodEquivOfIsCompl q f.ker hq.symm).symm.trans (prodCongr e eK)).trans
      (prodEquivOfIsCompl f.range r hr)⟩

/- English proof (translation)
Introduce `G V W _ _ _ _ _ _ _ _ ρ σ h`. Conclude with `aux (finrank ℂ V) V W ρ σ rfl h`.
-/
theorem nonempty_equiv_of_character_eq : ∀ (G V W : Type) [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ h
  exact aux (finrank ℂ V) V W ρ σ rfl h

end GlobalTheory.CharacterDetermines
