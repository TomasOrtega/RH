import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.CutTrivIne

section Gen

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1 : Br.vecS Bw k v ∈ stdG (Br.Ow Bw) (Br.LLw Bw) k` using `(Submodule.Quotient.mk_eq_zero _).1 hx`. Take `⟨u, hu⟩` from `h1`. Use `(Submodule.Quotient.mk_eq_zero _).2 ⟨fun j => Bw.eO.symm (u j), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`.

Apply `(Br.toLLK Bw).injective` to reduce the goal to its premises. Establish `h2` using `Br.toLLK_alg Bw (Bw.eO.symm (u j))`. Rewrite `h2` using `[RingEquiv.apply_symm_apply]`. Conclude with `h2.trans (congrFun hu j)`.
-/
theorem eq_zero_of_phi (k : ℕ) (x : KOG O k) (hx : Br.phi Bw k x = 0) : x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : Br.vecS Bw k v ∈ stdG (Br.Ow Bw) (Br.LLw Bw) k :=
    (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨u, hu⟩ := h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨fun j => Bw.eO.symm (u j), ?_⟩
  funext j
  apply (Br.toLLK Bw).injective
  have h2 := Br.toLLK_alg Bw (Bw.eO.symm (u j))
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.trans (congrFun hu j)

end Gen

/- English proof (translation)
Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h : matRep M g v = v` using `by show Matrix.toLin' (M g) v = v`. Rewrite using `[hg, Matrix.toLin'_one]`. Both sides reduce to the same expression. Use `show Submodule.Quotient.mk (matRep M g v) = _`.

Rewrite using `[h]`.
-/
theorem actD_eq_of_eq_one {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] {k : ℕ}
    (M : G →* Matrix (Fin k) (Fin k) LL) (L : Lattice (O := O) (matRep M)) (g : G) (hg : M g = 1)
    (x : (Fin k → LL) ⧸ L.T) : actD L g x = x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : matRep M g v = v := by
    show Matrix.toLin' (M g) v = v
    rw [hg, Matrix.toLin'_one]
    rfl
  show Submodule.Quotient.mk (matRep M g v) = _
  rw [h]

/- English proof (translation)
Simplify using `[chiRatO, twistM]`.
-/
theorem chiRatO_one (D : D7) (i : D.nd.Loc) (γ : GE D.nd) : chiRatO D.nd i 1 γ = 1 := by
  simp [chiRatO, twistM]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D i C w hw h`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨x, hx⟩` from `h f hf`. Rewrite using `[Submodule.mem_bot]`.

Use function extensionality and compare the values at `γ`. Take `⟨g, hg⟩` from `(Br.ι_bijective (D.nbr i w hw)).2 ⟨γ.1, Ine_le_Dec _ γ.2⟩`. Establish `hg' : ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) = γ.1` using `congrArg Subtype.val hg`. Establish `hmem : g ∈ Br.inert D.nbr i w hw` using `by show ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)`. Rewrite using `[hg']`.

Conclude with `γ.2`. Establish `h1 : Br.loc D.nbr i w hw (chiRatO D.nd i 1) g = 1` using `by show (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).mapMatrix ((D.nbr i w hw).eO.toRingHom.mapMatrix (chiRatO D.nd i 1 ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))) = 1`. Rewrite using `[chiRatO_one, map_one, map_one]`. Establish `h2` using `hx g hmem`. Rewrite `h2` using `[actD_eq_of_eq_one _ _ g h1, sub_self]`.

Establish `h3` using `eq_zero_of_phi (D.nbr i w hw) 1 _ h2`. Rewrite `h3` using `[hg']`. Conclude with `h3`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ C, locFun i (chiRatO D.nd i 1) w hw f ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) → resIne i C w = ⊥ := by
  intro D i C w hw h
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, hx⟩ := h f hf
  rw [Submodule.mem_bot]
  funext γ
  obtain ⟨g, hg⟩ := (Br.ι_bijective (D.nbr i w hw)).2 ⟨γ.1, Ine_le_Dec _ γ.2⟩
  have hg' : ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) = γ.1 := congrArg Subtype.val hg
  have hmem : g ∈ Br.inert D.nbr i w hw := by
    show ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)
    rw [hg']
    exact γ.2
  have h1 : Br.loc D.nbr i w hw (chiRatO D.nd i 1) g = 1 := by
    show (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).mapMatrix
      ((D.nbr i w hw).eO.toRingHom.mapMatrix
        (chiRatO D.nd i 1 ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))) = 1
    rw [chiRatO_one, map_one, map_one]
  have h2 := hx g hmem
  rw [actD_eq_of_eq_one _ _ g h1, sub_self] at h2
  have h3 := eq_zero_of_phi (D.nbr i w hw) 1 _ h2
  rw [hg'] at h3
  exact h3

end GlobalTheory.CutTrivIne

end
