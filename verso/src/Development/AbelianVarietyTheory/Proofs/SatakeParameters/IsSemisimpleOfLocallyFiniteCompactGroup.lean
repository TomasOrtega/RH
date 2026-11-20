import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

namespace GlobalTheory.LocFinSemisimple

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `Y hY hn hne`. Distinguish the cases in `hA : IsAtom Y`.

Conclude with `⟨Y, hA, le_rfl⟩`. Establish `: ∃ Z, Z < Y ∧ Z ≠ ⊥`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hA ⟨hne, hc⟩`.

Take `⟨Z, hZY, hZ⟩` from `this`. Establish `hlt : Z.toSubmodule < Y.toSubmodule` using `lt_of_le_of_ne hZY.le fun h => hZY.ne (Subrepresentation.toSubmodule_injective h)`. Establish `hZf : FiniteDimensional ℂ Z.toSubmodule` using `Submodule.finiteDimensional_of_le hlt.le`. Establish `hr` using `Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨T, hT, hTZ⟩` from `ih _ (hn ▸ hr) Z hZf rfl hZ`.

Conclude with `⟨T, hT, hTZ.trans hZY.le⟩`.
-/
theorem exists_isAtom_le : ∀ (n : ℕ) (Y : Subrepresentation ρ),
    FiniteDimensional ℂ Y.toSubmodule → Module.finrank ℂ Y.toSubmodule = n → Y ≠ ⊥ →
      ∃ T : Subrepresentation ρ, IsAtom T ∧ T ≤ Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY hn hne
    by_cases hA : IsAtom Y
    · exact ⟨Y, hA, le_rfl⟩
    · have : ∃ Z, Z < Y ∧ Z ≠ ⊥ := by
        by_contra hc
        push_neg at hc
        exact hA ⟨hne, hc⟩
      obtain ⟨Z, hZY, hZ⟩ := this
      have hlt : Z.toSubmodule < Y.toSubmodule :=
        lt_of_le_of_ne hZY.le fun h => hZY.ne (Subrepresentation.toSubmodule_injective h)
      have hZf : FiniteDimensional ℂ Z.toSubmodule := Submodule.finiteDimensional_of_le hlt.le
      have hr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT, hTZ⟩ := ih _ (hn ▸ hr) Z hZf rfl hZ
      exact ⟨T, hT, hTZ.trans hZY.le⟩

def ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U) : Subrepresentation ρ :=
  ⟨U, fun k _ hu => hU k _ hu⟩

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (ofInvariant U hU).toSubmodule := hfd`. Use `GlobalTheory.isSemisimpleRepresentation_of_continuous_coeff _ fun l v => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `LinearMap.exists_extend (p := U) l`. Establish `h : ∀ k, l ((ofInvariant U hU).toRepresentation k v) = g (ρ k v)` using `fun k => by`. Rewrite using `[← hg]`.

Both sides reduce to the same expression. Simplify using `only [h]`. Conclude with `hc g v v.2`.
-/
theorem isSemisimple_ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U)
    (hfd : FiniteDimensional ℂ U)
    (hc : ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) :
    (ofInvariant U hU).toRepresentation.IsSemisimpleRepresentation := by
  haveI : FiniteDimensional ℂ (ofInvariant U hU).toSubmodule := hfd
  refine GlobalTheory.isSemisimpleRepresentation_of_continuous_coeff _ fun l v => ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := U) l
  have h : ∀ k, l ((ofInvariant U hU).toRepresentation k v) = g (ρ k v) := fun k => by
    rw [← hg]; rfl
  simp only [h]
  exact hc g v v.2

/- English proof (translation)
Use `set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef`. Establish `hNX : N ≤ X.toSubmodule` using `iSup₂_le fun S hS => hS.2`. Establish `hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N`. Introduce `k`. Establish `: N ≤ N.comap (ρ k)` using `iSup₂_le fun S hS x hx => (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS) (S.apply_mem_toSubmodule k hx)`.

Conclude with `fun x hx => this hx`. Introduce `x hxX`. Take `⟨U, hxU, hfd, hU, hc⟩` from `H x`. Set `R` to `ofInvariant U hU`. Use `haveI : ComplementedLattice (Subrepresentation R.toRepresentation) := isSemisimple_ofInvariant U hU hfd hc`.

Set `W : Subrepresentation R.toRepresentation` to `⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩`. Take `⟨W', hW'⟩` from `exists_isCompl W`. Establish `hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥` using `congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot`. Establish `hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤` using `congrArg Subrepresentation.toSubmodule hW'.sup_eq_top`. Set `Xc : Submodule ℂ U` to `X.toSubmodule.comap U.subtype`.

Set `Y : Subrepresentation ρ` to `⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by`. Introduce and unpack `k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩`. Conclude with `⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1, X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩`. Establish `hY : Y = ⊥`. Assume the negation of the conclusion as `hne`.

Use `haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)`. Take `⟨T, hT, hTY⟩` from `exists_isAtom_le _ Y this rfl hne`. Establish `hTX : T ≤ X`. Introduce `t ht`. Take `⟨u, ⟨_, hu2⟩, rfl⟩` from `hTY ht`.

Conclude with `hu2`. Establish `hTN : T.toSubmodule ≤ N` using `le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩`. Establish `hT0 : T.toSubmodule ≠ ⊥` using `fun h => hT.1 (Subrepresentation.toSubmodule_injective h)`. Take `⟨t, ht, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hT0`. Take `⟨u, ⟨hu1, _⟩, rfl⟩` from `hTY ht`.

Establish `hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule` using `⟨hTN ht, hu1⟩`. Rewrite `hu` using `[hdis]`. Establish `hu0 : ((u : R.toSubmodule) : V) = 0` using `congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)`. Conclude with `ht0 hu0`. Establish `hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule` using `by rw [hsup]; trivial`.

Take `⟨w, hw, w', hw', hww⟩` from `Submodule.mem_sup.1 hx'`. Establish `hsum : (w : V) + (w' : V) = x` using `congrArg Subtype.val hww`. Establish `hw'X : w' ∈ Xc`. Establish `h1 : (w : V) ∈ X.toSubmodule` using `hNX hw`. Establish `h2 : (w' : V) = x - w`.

Rewrite using `[← hsum]`. Normalize the expressions using the abelian group laws. Use `show (w' : V) ∈ X.toSubmodule`. Rewrite using `[h2]`. Conclude with `X.toSubmodule.sub_mem hxX h1`.

Establish `hw'0 : (w' : V) ∈ Y.toSubmodule` using `⟨w', ⟨hw', hw'X⟩, rfl⟩`. Rewrite `hw'0` using `[hY]`. Establish `: (w' : V) = 0` using `(Submodule.mem_bot ℂ).1 hw'0`. Establish `hxw : x = w`. Rewrite using `[← hsum, ‹(w' : V) = 0›, add_zero]`.

Rewrite using `[hxw]`. Conclude with `hw`.
-/
theorem le_iSup_atoms
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef
  have hNX : N ≤ X.toSubmodule := iSup₂_le fun S hS => hS.2
  have hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N := by
    intro k
    have : N ≤ N.comap (ρ k) := iSup₂_le fun S hS x hx =>
      (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun x hx => this hx
  intro x hxX
  obtain ⟨U, hxU, hfd, hU, hc⟩ := H x
  let R := ofInvariant U hU
  haveI : ComplementedLattice (Subrepresentation R.toRepresentation) :=
    isSemisimple_ofInvariant U hU hfd hc
  let W : Subrepresentation R.toRepresentation :=
    ⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩
  obtain ⟨W', hW'⟩ := exists_isCompl W
  have hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
  let Xc : Submodule ℂ U := X.toSubmodule.comap U.subtype
  let Y : Subrepresentation ρ := ⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by
    rintro k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1,
      X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩
  have hY : Y = ⊥ := by
    by_contra hne
    haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le
      (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)
    obtain ⟨T, hT, hTY⟩ := exists_isAtom_le _ Y this rfl hne
    have hTX : T ≤ X := by
      intro t ht
      obtain ⟨u, ⟨_, hu2⟩, rfl⟩ := hTY ht
      exact hu2
    have hTN : T.toSubmodule ≤ N :=
      le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨u, ⟨hu1, _⟩, rfl⟩ := hTY ht
    have hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule := ⟨hTN ht, hu1⟩
    rw [hdis] at hu
    have hu0 : ((u : R.toSubmodule) : V) = 0 :=
      congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)
    exact ht0 hu0
  have hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', hww⟩ := Submodule.mem_sup.1 hx'
  have hsum : (w : V) + (w' : V) = x := congrArg Subtype.val hww
  have hw'X : w' ∈ Xc := by
    have h1 : (w : V) ∈ X.toSubmodule := hNX hw
    have h2 : (w' : V) = x - w := by
      rw [← hsum]; abel
    show (w' : V) ∈ X.toSubmodule
    rw [h2]
    exact X.toSubmodule.sub_mem hxX h1
  have hw'0 : (w' : V) ∈ Y.toSubmodule := ⟨w', ⟨hw', hw'X⟩, rfl⟩
  rw [hY] at hw'0
  have : (w' : V) = 0 := (Submodule.mem_bot ℂ).1 hw'0
  have hxw : x = w := by
    rw [← hsum, ‹(w' : V) = 0›, add_zero]
  rw [hxw]
  exact hw

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ ρ H`. Establish `hle` using `le_iSup_atoms H`. Use `⟨?_, ?_, fun X => le_antisymm (hle X) (iSup₂_le fun S hS => hS.2)⟩` and prove the remaining obligations. Rewrite using `[Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule, ← sSup_simples_eq_top_iff_isSemisimpleModule]`. Set `e` to `Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)`.

Use `set s := sSup {m : Submodule (MonoidAlgebra ℂ K) ρ.asModule | IsSimpleModule (MonoidAlgebra ℂ K) m} with hs`. Establish `hZ : (e.symm s).toSubmodule = ⊤`. Use `eq_top_iff.2 ((hle ⊤).trans (iSup₂_le fun S hS => ?_))` and prove the remaining obligations. Establish `: S ≤ e.symm s` using `e.le_symm_apply.2 (le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff S).2 hS.1)))`. Conclude with `this`.

Establish `h1 : e.symm s = ⊤` using `Subrepresentation.toSubmodule_injective hZ`. Rewrite using `[← e.apply_symm_apply s, h1, e.map_top]`. Introduce `S hS`. Establish `hS0 : S.toSubmodule ≠ ⊥` using `fun h => hS.1 (Subrepresentation.toSubmodule_injective h)`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hS0`.

Take `⟨U, hvU, hfd, hU, -⟩` from `H v`. Break down `hS.le_iff.1 (inf_le_left : S ⊓ ofInvariant U hU ≤ S) with h | h` into its components or cases. Establish `hm : v ∈ (S ⊓ ofInvariant U hU).toSubmodule` using `⟨hv, hvU⟩`. Rewrite `hm` using `[h]`. Conclude with `absurd ((Submodule.mem_bot ℂ).1 hm) hv0`.

Establish `hSU : S.toSubmodule ≤ U`. Rewrite using `[← h]`. Conclude with `fun x hx => hx.2`. Conclude with `Submodule.finiteDimensional_of_le hSU`.
-/
theorem semisimple_of_locallyFinite : ∀ (K V : Type) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) →
    ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S →
      FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ,
        X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  intro K V _ _ _ _ _ _ ρ H
  have hle := le_iSup_atoms H
  refine ⟨?_, ?_, fun X => le_antisymm (hle X) (iSup₂_le fun S hS => hS.2)⟩
  · rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
      ← sSup_simples_eq_top_iff_isSemisimpleModule]
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
    set s := sSup {m : Submodule (MonoidAlgebra ℂ K) ρ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ K) m} with hs
    have hZ : (e.symm s).toSubmodule = ⊤ := by
      refine eq_top_iff.2 ((hle ⊤).trans (iSup₂_le fun S hS => ?_))
      have : S ≤ e.symm s := e.le_symm_apply.2
        (le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff S).2 hS.1)))
      exact this
    have h1 : e.symm s = ⊤ := Subrepresentation.toSubmodule_injective hZ
    rw [← e.apply_symm_apply s, h1, e.map_top]
  · intro S hS
    have hS0 : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    obtain ⟨U, hvU, hfd, hU, -⟩ := H v
    rcases hS.le_iff.1 (inf_le_left : S ⊓ ofInvariant U hU ≤ S) with h | h
    · have hm : v ∈ (S ⊓ ofInvariant U hU).toSubmodule := ⟨hv, hvU⟩
      rw [h] at hm
      exact absurd ((Submodule.mem_bot ℂ).1 hm) hv0
    · have hSU : S.toSubmodule ≤ U := by
        rw [← h]; exact fun x hx => hx.2
      exact Submodule.finiteDimensional_of_le hSU

end GlobalTheory.LocFinSemisimple
