import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt

variable {D : D7}

open Classical in

def sys (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (x : L.X.nd.X i) : PlE D.host → ℕ → ℂ := fun v k =>
  if SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then
    iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x)
  else 0

/- English proof (translation)
Take `⟨Sp, -, -⟩` from `hB`. Establish `hw : L.X.nd.w i = w` using `((L.X.nd.locs_mem j w i).1 hi).2`. Establish `hl : L.X.nd.l i = D.what₂.places.resChar w` using `by rw [← hw]; exact (L.X.nd.w_l i).symm`. Establish `hQ : L.X.nd.Q i = C.Q w` using `(Sp.Q_eq j w i hi).trans (Sp.Qc_eq j w)`. Establish `hS : v ∈ L.X.nd.S i ↔ v ∈ placesS D (L.X.nd.l i)` using `L.X.nd.S_def i v`.

Unfold `SplitOut GenAt`. Rewrite using `[hS, ← hl, ← hQ]`. The claim follows by propositional logic.
-/
theorem splitOut_iff_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (C.Q w) v k := by
  obtain ⟨Sp, -, -⟩ := hB
  have hw : L.X.nd.w i = w := ((L.X.nd.locs_mem j w i).1 hi).2
  have hl : L.X.nd.l i = D.what₂.places.resChar w := by rw [← hw]; exact (L.X.nd.w_l i).symm
  have hQ : L.X.nd.Q i = C.Q w := (Sp.Q_eq j w i hi).trans (Sp.Qc_eq j w)
  have hS : v ∈ L.X.nd.S i ↔ v ∈ placesS D (L.X.nd.l i) := L.X.nd.S_def i v
  unfold SplitOut GenAt
  rw [hS, ← hl, ← hQ]
  tauto

/- English proof (translation)
Unfold `sys`. Rewrite using `[if_pos ((splitOut_iff_genAt hB hi v k).2 h)]`.
-/
theorem sys_of_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) :
    sys L i x v k = iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) := by
  unfold sys
  rw [if_pos ((splitOut_iff_genAt hB hi v k).2 h)]

/- English proof (translation)
Unfold `sys`. Rewrite using `[if_neg (fun h' => h ((splitOut_iff_genAt hB hi v k).1 h'))]`.
-/
theorem sys_of_not_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : ¬ GenAt D (D.what₂.places.resChar w) (C.Q w) v k) : sys L i x v k = 0 := by
  unfold sys
  rw [if_neg (fun h' => h ((splitOut_iff_genAt hB hi v k).1 h'))]

/- English proof (translation)
Use `⟨fun v k h => sys_of_not_genAt hB hi x h, ?_⟩` and prove the remaining obligations. Establish `hB'` using `hB`. Take `⟨Sp, ⟨Au⟩, -⟩` from `hB'`. Take `⟨hj, hw⟩` from `(L.X.nd.locs_mem j w i).1 hi`. Substitute `hj hw` using the available equality.

Take `⟨P, hP⟩` from `L.Y.naut.pt_surj i x`. Establish `key : ∃ y : D.what₂.Mt (L.X.nd.mu i) (L.X.nd.j i), y ≠ 0 ∧ ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) v k → IsConjPl D.host v s.w → IsUnif D.host.E …`. Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff _).1 (L.Y.naut.typeV_ne i P)`. Use `⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩` and prove the remaining obligations. Take `⟨hso, k1, k2⟩` from `(splitOut_iff_genAt hB hi v k).2 hg`.

Rewrite using `[sys_of_genAt hB hi x hg]`. Conclude with `(Au.ptV i P x).1 hP v k s ϖ hso hc hu k1 k2 y hy`. Rewrite `key` using `[L.X.nd.mu_w i]`. Conclude with `key`.
-/
theorem sys_mem {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) :
    sys L i x ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w) := by
  refine ⟨fun v k h => sys_of_not_genAt hB hi x h, ?_⟩
  have hB' := hB
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB'
  obtain ⟨hj, hw⟩ := (L.X.nd.locs_mem j w i).1 hi
  subst hj hw
  obtain ⟨P, hP⟩ := L.Y.naut.pt_surj i x
  have key : ∃ y : D.what₂.Mt (L.X.nd.mu i) (L.X.nd.j i), y ≠ 0 ∧
      ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        GenAt D (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) v k → IsConjPl D.host v s.w →
        IsUnif D.host.E s.v ϖ →
        NG.tN (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).J s ϖ k ((M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y) =
          sys L i x v k • (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y := by
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (L.Y.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hso, k1, k2⟩ := (splitOut_iff_genAt hB hi v k).2 hg
    rw [sys_of_genAt hB hi x hg]
    exact (Au.ptV i P x).1 hP v k s ϖ hso hc hu k1 k2 y hy
  rw [L.X.nd.mu_w i] at key
  exact key

/- English proof (translation)
Introduce `a b h`. Unfold `iotaO at h`. Simplify using `only [RingHom.coe_comp, Function.comp_apply] at h`. Conclude with `IsFractionRing.injective (L.X.nd.O i) (FractionRing (L.X.nd.O i)) ((L.Y.naut.iotaQ i).injective ((L.Y.naut.iotaQC i).injective h))`.
-/
theorem iotaO_injective (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Function.Injective (iotaO L.X.nd L.Y.naut i) := by
  intro a b h
  unfold iotaO at h
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  exact IsFractionRing.injective (L.X.nd.O i) (FractionRing (L.X.nd.O i))
    ((L.Y.naut.iotaQ i).injective ((L.Y.naut.iotaQC i).injective h))

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf, hfx⟩` from `L.X.nd.T_sep i x x' hne`. Apply `hfx` to reduce the goal to its premises. Set `E : Subalgebra (L.X.nd.O i) (L.X.nd.X i → L.X.nd.O i)` to `AlgHom.equalizer (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x) (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x')`. Establish `hle : L.X.nd.T i ≤ E`.

Rewrite using `[← L.X.nd.T_gen i, Algebra.adjoin_le_iff]`. Introduce and unpack `g ⟨v, k, hs, hl, hS, hQ, k1, k2, rfl⟩`. Establish `hv : SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV` using `⟨⟨hs, hl, hS, hQ⟩, k1, k2⟩`. Use `congrFun (congrFun h v) k` as an intermediate fact. Unfold `sys at this`.

Rewrite `this` using `[if_pos hv, if_pos hv]`. Conclude with `iotaO_injective L i this`. Conclude with `hle hf`.
-/
theorem sys_inj (L : LocAll (lay0 D)) (i : L.X.nd.Loc) {x x' : L.X.nd.X i} (h : sys L i x = sys L i x') : x = x' := by
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := L.X.nd.T_sep i x x' hne
  apply hfx
  let E : Subalgebra (L.X.nd.O i) (L.X.nd.X i → L.X.nd.O i) :=
    AlgHom.equalizer (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x)
      (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x')
  have hle : L.X.nd.T i ≤ E := by
    rw [← L.X.nd.T_gen i, Algebra.adjoin_le_iff]
    rintro g ⟨v, k, hs, hl, hS, hQ, k1, k2, rfl⟩
    have hv : SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV := ⟨⟨hs, hl, hS, hQ⟩, k1, k2⟩
    have := congrFun (congrFun h v) k
    unfold sys at this
    rw [if_pos hv, if_pos hv] at this
    exact iotaO_injective L i this
  exact hle hf

end GlobalTheory.PtExt

end
