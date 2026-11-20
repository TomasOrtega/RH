import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpen
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

/- English proof (translation)
Set `A` to `(OAff s').obj (op W)`. Set `B` to `(OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))`. Set `ψ : A →ₐ[R'] B` to `mp (OAff s') (homOfLE hle).op`. Use `letI : Algebra A B := (ψ : A →+* B).toAlgebra`. Use `haveI : IsScalarTower R' A B := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm`.

Use `haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f`. Establish `e` using `(semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B) (fun b ↦ rfl) ω`. Establish `h' : KaehlerDifferential.map R' R' A B ω = 0` using `e.symm.trans h`. Take `⟨⟨c, hc⟩, hc0⟩` from `(IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f)) (f := KaehlerDifferential.map R' R' A B)).1 h'`. Take `⟨n, rfl⟩` from `hc`.

Conclude with `⟨n, hc0⟩`.
-/
theorem form_pow_smul_eq_zero_of_basicOpen {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  let A := (OAff s').obj (op W)
  let B := (OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))
  let ψ : A →ₐ[R'] B := mp (OAff s') (homOfLE hle).op
  letI : Algebra A B := (ψ : A →+* B).toAlgebra
  haveI : IsScalarTower R' A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f
  have e := (semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B)
    (fun b ↦ rfl) ω
  have h' : KaehlerDifferential.map R' R' A B ω = 0 := e.symm.trans h
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f))
    (f := KaehlerDifferential.map R' R' A B)).1 h'
  obtain ⟨n, rfl⟩ := hc
  exact ⟨n, hc0⟩

/- English proof (translation)
Set `A` to `(OAff s').obj (op W)`. Set `J : Ideal A` to `(Submodule.span A {ω}).annihilator`. Set `I : Set Γ(X', W.1)` to `{a | (show A from a) ∈ J}`. Establish `hcov : W.1 ≤ ⨆ a : I, X'.basicOpen a.1`. Introduce `x hx`.

Take `⟨p, f, e, hxp⟩` from `Pair.exists_basicOpen φ W hx`. Take `⟨⟨⟨U, hU⟩, V⟩, hpV⟩` from `p`. Simplify using `only at e hxp`. Substitute `e` using the available equality. Establish `hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W` using `X'.basicOpen_le f`.

Take `⟨n, hn⟩` from `form_pow_smul_eq_zero_of_basicOpen s' W f hU hle ω (h ⟨(⟨X'.basicOpen f, hU⟩, V), hpV⟩ hle)`. Establish `hxn : x ∈ X'.basicOpen (f ^ n)`. Break down `n with _ | n` into its components or cases. Rewrite using `[pow_zero, X'.basicOpen_of_isUnit isUnit_one]`. Conclude with `hx`.

Rewrite using `[X'.basicOpen_pow f n.succ_pos]` and apply the resulting hypothesis. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f ^ n, show ((show A from f) ^ n) ∈ J from (Submodule.mem_annihilator_span_singleton ω _).2 hn⟩, hxn⟩`. Establish `hI` using `(W.2.self_le_iSup_basicOpen_iff).1 hcov`. Establish `hJ : Ideal.span I ≤ J` using `Ideal.span_le.2 fun a ha ↦ ha`. Establish `h1 : (1 : A) ∈ J` using `hJ (hI ▸ Submodule.mem_top)`.

Simplify using `using (Submodule.mem_annihilator_span_singleton _ _).1 h1`.
-/
theorem form_eq_zero_of_pair {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) : ω = 0 := by
  let A := (OAff s').obj (op W)
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  let I : Set Γ(X', W.1) := {a | (show A from a) ∈ J}
  have hcov : W.1 ≤ ⨆ a : I, X'.basicOpen a.1 := by
    intro x hx
    obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
    obtain ⟨⟨⟨U, hU⟩, V⟩, hpV⟩ := p
    dsimp only at e hxp
    subst e
    have hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W := X'.basicOpen_le f
    obtain ⟨n, hn⟩ := form_pow_smul_eq_zero_of_basicOpen s' W f hU hle ω
      (h ⟨(⟨X'.basicOpen f, hU⟩, V), hpV⟩ hle)
    have hxn : x ∈ X'.basicOpen (f ^ n) := by
      rcases n with _ | n
      · rw [pow_zero, X'.basicOpen_of_isUnit isUnit_one]; exact hx
      · rwa [X'.basicOpen_pow f n.succ_pos]
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨f ^ n, show ((show A from f) ^ n) ∈ J from
        (Submodule.mem_annihilator_span_singleton ω _).2 hn⟩, hxn⟩
  have hI := (W.2.self_le_iSup_basicOpen_iff).1 hcov
  have hJ : Ideal.span I ≤ J := Ideal.span_le.2 fun a ha ↦ ha
  have h1 : (1 : A) ∈ J := hJ (hI ▸ Submodule.mem_top)
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1

end GlobalTheory.CechDR
