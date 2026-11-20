import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Module Representation

universe uk uG uU uV uW

variable {k : Type uk} {G : Type uG} [Field k] [Group G]

/- English proof (translation)
The claim follows from `LinearMap.trace_prodMap' (ρ g) (σ g)`.
-/
theorem character_prod {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g :=
  LinearMap.trace_prodMap' (ρ g) (σ g)

noncomputable def equivProdRight {U : Type uU} {V : Type uV} {W : Type uW} [AddCommGroup U]
    [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (τ : Representation k G U) {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : (τ.prod ρ).Equiv (τ.prod σ) :=
  Representation.Equiv.mk ((LinearEquiv.refl k U).prodCongr e.toLinearEquiv) fun g =>
    LinearMap.ext fun x => Prod.ext rfl (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x.2)

/- English proof (translation)
Take `⟨Z, hZ⟩` from `exists_isCompl f.range`. Establish `hZ' : IsCompl (LinearMap.range f.toLinearMap) Z.toSubmodule` using `⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hZ.disjoint)), codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hZ.codisjoint))⟩`. Set `e : (U × Z.toSubmodule) ≃ₗ[k] W` to `((LinearEquiv.ofInjective f.toLinearMap hf).prodCongr (LinearEquiv.refl k Z.toSubmodule)).trans (Submodule.prodEquivOfIsCompl _ _ hZ')`. Establish `he : ∀ u z, e (u, z) = f u + z` using `fun u z => by`. Simplify using `[e, Submodule.coe_prodEquivOfIsCompl']`.

Use `⟨Z, ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩⟩` and prove the remaining obligations. Take `⟨u, z⟩` from `x`. Establish `h1 : f (τ g u) = σ g (f u)` using `LinearMap.congr_fun (f.isIntertwining' g) u`. Use `show e (τ g u, Z.toRepresentation g z) = σ g (e (u, z))`. Rewrite using `[he, he, map_add, h1]`.

Both sides reduce to the same expression.
-/
theorem exists_equiv_prod_of_injective [Finite G] [NeZero (Nat.card G : k)] {U : Type uU}
    {W : Type uW} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    {τ : Representation k G U} {σ : Representation k G W} (f : IntertwiningMap τ σ)
    (hf : Function.Injective f) :
    ∃ Z : Subrepresentation σ, Nonempty ((τ.prod Z.toRepresentation).Equiv σ) := by
  obtain ⟨Z, hZ⟩ := exists_isCompl f.range
  have hZ' : IsCompl (LinearMap.range f.toLinearMap) Z.toSubmodule :=
    ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hZ.disjoint)),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hZ.codisjoint))⟩
  let e : (U × Z.toSubmodule) ≃ₗ[k] W :=
    ((LinearEquiv.ofInjective f.toLinearMap hf).prodCongr (LinearEquiv.refl k Z.toSubmodule)).trans
      (Submodule.prodEquivOfIsCompl _ _ hZ')
  have he : ∀ u z, e (u, z) = f u + z := fun u z => by
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨Z, ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩⟩
  obtain ⟨u, z⟩ := x
  have h1 : f (τ g u) = σ g (f u) := LinearMap.congr_fun (f.isIntertwining' g) u
  show e (τ g u, Z.toRepresentation g z) = σ g (e (u, z))
  rw [he, he, map_add, h1]
  rfl

/- English proof (translation)
It suffices to establish `H : ∀ n : ℕ, ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W), finrank k V = n → ρ.character = σ.character → Nonempty (ρ.Equiv σ) from H …`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V W _ _ _ _ _ _ ρ σ hn h`.

Establish `: Fintype G` using `Fintype.ofFinite G`. Establish `hG : (Nat.card G : k) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `: NeZero (Nat.card G : k)` using `⟨hG⟩`. Establish `: Invertible (Nat.card G : k)` using `invertibleOfNonzero hG`. Establish `hdim : finrank k W = finrank k V`.

Establish `h1` using `congrFun h 1`. Rewrite `h1` using `[Representation.char_one, Representation.char_one]`. Conclude with `h1.symm` after adjusting the coercions. Distinguish the cases in `hV : finrank k V = 0`. Establish `: Subsingleton W` using `Module.finrank_zero_iff.1 (hdim.trans hV)`.

Conclude with `⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hdim.symm) fun g => LinearMap.ext fun _ => Subsingleton.elim _ _⟩`. Establish `hex : ∃ m, ∃ Y : Subrepresentation ρ, Y ≠ ⊥ ∧ finrank k Y.toSubmodule = m`. Use `⟨finrank k V, ⊤, fun h0 => hV ?_, finrank_top k V⟩` and prove the remaining obligations. Establish `h1 : (⊤ : Submodule k V) = ⊥` using `congrArg Subrepresentation.toSubmodule h0`. Rewrite using `[← finrank_top k V, h1, finrank_bot]`.

Take `⟨Y, hY0, hYm⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ Y' : Subrepresentation ρ, Y' ≠ ⊥ → finrank k Y.toSubmodule ≤ finrank k Y'.toSubmodule` using `fun Y' hY' => by`. Rewrite using `[hYm]`. Conclude with `Nat.find_min' hex ⟨Y', hY', rfl⟩`. Establish `hYsub : Y.toSubmodule ≠ ⊥` using `fun h0 => hY0 (Subrepresentation.toSubmodule_injective h0)`.

Set `ι : IntertwiningMap Y.toRepresentation ρ` to `⟨Y.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩`. Establish `hιinj : Function.Injective ι` using `Subtype.val_injective`. Establish `hι0 : ι ≠ 0`. Take `⟨y, hy, hy0⟩` from `Submodule.ne_bot_iff _ |>.1 hYsub`. Introduce `h0`.

Conclude with `hy0 (congrArg (fun φ : IntertwiningMap Y.toRepresentation ρ => φ ⟨y, hy⟩) h0)`. Establish `hHom : finrank k (IntertwiningMap Y.toRepresentation σ) = finrank k (IntertwiningMap Y.toRepresentation ρ)`. Establish `h1` using `card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation ρ`. Establish `h2` using `card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation σ`. Rewrite `h1` using `[h]`.

Conclude with `h2.symm.trans h1` after adjusting the coercions. Establish `hpos : 0 < finrank k (IntertwiningMap Y.toRepresentation σ)` using `hHom ▸ Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι0⟩`. Take `⟨f, hf0⟩` from `Module.finrank_pos_iff_exists_ne_zero.1 hpos`. Establish `hfinj : Function.Injective f`. Set `K : Submodule k Y.toSubmodule` to `LinearMap.ker f.toLinearMap`.

Distinguish the cases in `hK : K = ⊥`. Conclude with `LinearMap.ker_eq_bot.1 hK`. It suffices to derive a contradiction. Set `K' : Subrepresentation ρ` to `⟨K.map Y.toSubmodule.subtype, by`. Introduce and unpack `g _ ⟨y, hy, rfl⟩`.

Use `⟨Y.toRepresentation g y, ?_, rfl⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun (f.isIntertwining' g) y`. Establish `hy' : f.toLinearMap y = 0` using `hy`. Use `show f.toLinearMap (Y.toRepresentation g y) = 0`. Rewrite `h1` using `[LinearMap.comp_apply, LinearMap.comp_apply]`.

Rewrite using `[h1, hy', map_zero]⟩`. Establish `hK'dim : finrank k K'.toSubmodule = finrank k K` using `Submodule.finrank_map_subtype_eq _ _`. Establish `hKpos : finrank k K ≠ 0` using `fun h0 => hK (Submodule.finrank_eq_zero.1 h0)`. Establish `hK'0 : K' ≠ ⊥`. Introduce `h0`.

Establish `h1 : K'.toSubmodule = ⊥` using `congrArg Subrepresentation.toSubmodule h0`. Rewrite `hK'dim` using `[h1, finrank_bot]`. Conclude with `hKpos hK'dim.symm`. Establish `h1` using `hmin K' hK'0`. Establish `h2 : finrank k K = finrank k Y.toSubmodule` using `le_antisymm (Submodule.finrank_le K) (hK'dim ▸ h1)`.

Establish `hKtop : K = ⊤` using `Submodule.eq_top_of_finrank_eq h2`. Conclude with `hf0 (IntertwiningMap.ext (LinearMap.ker_eq_top.1 hKtop))`. Take `⟨V', ⟨eV⟩⟩` from `exists_equiv_prod_of_injective ι hιinj`. Take `⟨W', ⟨eW⟩⟩` from `exists_equiv_prod_of_injective f hfinj`. Establish `hchar : V'.toRepresentation.character = W'.toRepresentation.character`.

Use function extensionality and compare the values at `g`. Establish `h1` using `congrFun (char_iso eV) g`. Establish `h2` using `congrFun (char_iso eW) g`. Establish `h3` using `congrFun h g`. Rewrite `h1`, `h2` using `[character_prod]`.

Take the linear combination `h1 - h2 + h3`. Establish `hYpos : 0 < finrank k Y.toSubmodule` using `Nat.pos_of_ne_zero fun h0 => hYsub (Submodule.finrank_eq_zero.1 h0)`. Establish `hlt : finrank k V'.toSubmodule < n`. Establish `h1` using `eV.toLinearEquiv.finrank_eq`. Rewrite `h1` using `[Module.finrank_prod]`.

Use linear arithmetic over natural numbers and integers. Take `⟨e'⟩` from `ih _ hlt V'.toRepresentation W'.toRepresentation rfl hchar`. Conclude with `⟨eV.symm.trans ((equivProdRight Y.toRepresentation e').trans eW)⟩`.
-/
theorem nonempty_equiv_of_character_eq [CharZero k] [Finite G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  suffices H : ∀ n : ℕ, ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W), finrank k V = n →
      ρ.character = σ.character → Nonempty (ρ.Equiv σ) from H _ ρ σ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ ρ σ hn h
  have : Fintype G := Fintype.ofFinite G
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  have hdim : finrank k W = finrank k V := by
    have h1 := congrFun h 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1.symm
  by_cases hV : finrank k V = 0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (hdim.trans hV)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hdim.symm) fun g =>
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩

  have hex : ∃ m, ∃ Y : Subrepresentation ρ, Y ≠ ⊥ ∧ finrank k Y.toSubmodule = m := by
    refine ⟨finrank k V, ⊤, fun h0 => hV ?_, finrank_top k V⟩
    have h1 : (⊤ : Submodule k V) = ⊥ := congrArg Subrepresentation.toSubmodule h0
    rw [← finrank_top k V, h1, finrank_bot]
  classical
  obtain ⟨Y, hY0, hYm⟩ := Nat.find_spec hex
  have hmin : ∀ Y' : Subrepresentation ρ, Y' ≠ ⊥ →
      finrank k Y.toSubmodule ≤ finrank k Y'.toSubmodule := fun Y' hY' => by
    rw [hYm]
    exact Nat.find_min' hex ⟨Y', hY', rfl⟩
  have hYsub : Y.toSubmodule ≠ ⊥ := fun h0 => hY0 (Subrepresentation.toSubmodule_injective h0)

  let ι : IntertwiningMap Y.toRepresentation ρ :=
    ⟨Y.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hι0 : ι ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hYsub
    intro h0
    exact hy0 (congrArg (fun φ : IntertwiningMap Y.toRepresentation ρ => φ ⟨y, hy⟩) h0)

  have hHom : finrank k (IntertwiningMap Y.toRepresentation σ) =
      finrank k (IntertwiningMap Y.toRepresentation ρ) := by
    have h1 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation ρ
    have h2 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation σ
    rw [h] at h1
    exact_mod_cast h2.symm.trans h1
  have hpos : 0 < finrank k (IntertwiningMap Y.toRepresentation σ) :=
    hHom ▸ Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι0⟩
  obtain ⟨f, hf0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos

  have hfinj : Function.Injective f := by
    let K : Submodule k Y.toSubmodule := LinearMap.ker f.toLinearMap
    by_cases hK : K = ⊥
    · exact LinearMap.ker_eq_bot.1 hK
    exfalso
    let K' : Subrepresentation ρ := ⟨K.map Y.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      refine ⟨Y.toRepresentation g y, ?_, rfl⟩
      have h1 := LinearMap.congr_fun (f.isIntertwining' g) y
      have hy' : f.toLinearMap y = 0 := hy
      show f.toLinearMap (Y.toRepresentation g y) = 0
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
      rw [h1, hy', map_zero]⟩
    have hK'dim : finrank k K'.toSubmodule = finrank k K := Submodule.finrank_map_subtype_eq _ _
    have hKpos : finrank k K ≠ 0 := fun h0 => hK (Submodule.finrank_eq_zero.1 h0)
    have hK'0 : K' ≠ ⊥ := by
      intro h0
      have h1 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [h1, finrank_bot] at hK'dim
      exact hKpos hK'dim.symm
    have h1 := hmin K' hK'0
    have h2 : finrank k K = finrank k Y.toSubmodule :=
      le_antisymm (Submodule.finrank_le K) (hK'dim ▸ h1)
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq h2
    exact hf0 (IntertwiningMap.ext (LinearMap.ker_eq_top.1 hKtop))

  obtain ⟨V', ⟨eV⟩⟩ := exists_equiv_prod_of_injective ι hιinj
  obtain ⟨W', ⟨eW⟩⟩ := exists_equiv_prod_of_injective f hfinj
  have hchar : V'.toRepresentation.character = W'.toRepresentation.character := by
    funext g
    have h1 := congrFun (char_iso eV) g
    have h2 := congrFun (char_iso eW) g
    have h3 := congrFun h g
    rw [character_prod] at h1 h2
    linear_combination h1 - h2 + h3
  have hYpos : 0 < finrank k Y.toSubmodule :=
    Nat.pos_of_ne_zero fun h0 => hYsub (Submodule.finrank_eq_zero.1 h0)
  have hlt : finrank k V'.toSubmodule < n := by
    have h1 := eV.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h1
    omega
  obtain ⟨e'⟩ := ih _ hlt V'.toRepresentation W'.toRepresentation rfl hchar
  exact ⟨eV.symm.trans ((equivProdRight Y.toRepresentation e').trans eW)⟩

end GroundTheory.ProfCoh
