import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLOneEqDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.BaseComp
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨star (r : E), r.2.map (starRingEnd E).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_int (r : 𝓞 E) : ∃ s : 𝓞 E, (s : E) = star (r : E) :=
  ⟨⟨star (r : E), r.2.map (starRingEnd E).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Both sides reduce to the same expression.
-/
theorem mem_dual_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

/- English proof (translation)
Set `f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E)` to `LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)`. Establish `hle : L ≤ LinearMap.range f`. Introduce `x hx`. Use `choose r hr using h x hx`. Conclude with `⟨r, funext fun j => (hr j).symm⟩`.

Use `haveI : IsNoetherian (𝓞 E) (LinearMap.range f) := isNoetherian_of_isNoetherianRing_of_finite _ _`. Use `(isNoetherian_submodule.1 (inferInstance : IsNoetherian (𝓞 E) (LinearMap.range f))) L hle` as an intermediate fact. Conclude with `this`.
-/
theorem fg_of_int (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) : L.FG := by
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  have hle : L ≤ LinearMap.range f := by
    intro x hx
    choose r hr using h x hx
    exact ⟨r, funext fun j => (hr j).symm⟩
  haveI : IsNoetherian (𝓞 E) (LinearMap.range f) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have := (isNoetherian_submodule.1 (inferInstance : IsNoetherian (𝓞 E) (LinearMap.range f))) L hle
  exact this

/- English proof (translation)
Establish `hst : star (t : E) ≠ 0`. Rewrite using `[star_ne_zero]`. Conclude with `ht` after adjusting the coercions. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Introduce `j`. Take `⟨r, hr, -⟩` from `(hLb x).1 hx j`. Conclude with `⟨r, hr.symm⟩`.

Rewrite using `[Submodule.smul_le]`. Introduce `a ha y hy`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Introduce `j`.

Establish `hx : (Pi.single j (t : E) : Fin n → E) ∈ Lb`. Rewrite using `[hLb]`. Introduce `k`. Distinguish the cases in `hk : k = j`. Substitute `hk; exact ⟨t, by simp, fun _ => dvd_refl t⟩` using the available equality.

Conclude with `⟨0, by simp [hk], fun _ => dvd_zero t⟩`. Take `⟨r, hr⟩` from `(mem_dual_iff Lb y).1 hy _ hx`. Establish `hsum : ∑ k, star ((Pi.single j (t : E) : Fin n → E) k) * y k = star (t : E) * y j`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Rewrite `hr` using `[hsum]`. Use `⟨s * r, ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hr]`. Rewrite using `[show algebraMap (𝓞 E) E c = (c : E) from rfl, hc, mul_assoc]`. Introduce `x hx`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one] at hx`. Use `choose r hr using hx`.

Set `x' : Fin n → E` to `fun j => if j.1 + 1 = n then 0 else x j`. Set `w : Fin n → E` to `fun j => if j.1 + 1 = n then x j / star (t : E) else 0`. Establish `hx' : x' ∈ Lb`. Rewrite using `[hLb]`. Introduce `j`.

Distinguish the cases in `hj : j.1 + 1 = n`. Conclude with `⟨0, by simp [x', hj], fun _ => dvd_zero t⟩`. Conclude with `⟨r j, by simp [x', hj, hr j], fun h => absurd h hj⟩`. Establish `hw : w ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) Lb`. Rewrite using `[mem_dual_iff]`.

Introduce `z hz`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k.1 + 1 = n`. Take `⟨q, hq, hdiv⟩` from `(hLb z).1 hz k`. Take `⟨d, rfl⟩` from `hdiv hk`.

Take `⟨s, hs⟩` from `star_int d`. Use `⟨s * r k, ?_⟩` and prove the remaining obligations. Simplify using `only [w, hk, if_true, hq]`. Rewrite using `[map_mul, hr k, show algebraMap (𝓞 E) E s = (s : E) from rfl, hs]`. Use `push_cast`.

Rewrite using `[star_mul', ← hr k]`. Clear the denominators using the available nonvanishing facts. Conclude with `⟨0, by simp [w, hk]⟩`. Establish `hxe : x = x' + c • w`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j.1 + 1 = n`. Simplify using `only [x', w, hj, if_true, Pi.add_apply, Pi.smul_apply, zero_add]`. Rewrite using `[Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl, hc]`. Clear the denominators using the available nonvanishing facts. Simplify using `[x', w, hj]`.

Rewrite using `[hxe]`. Conclude with `Submodule.add_mem_sup hx' (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hw)`.
-/
theorem sup_dual_eq_std (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E))
    (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    Lb ⊔ Ideal.span {c} • Formalism.HermitianLatticesTheory.dual (hStd E n) Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  have hst : star (t : E) ≠ 0 := by
    rw [star_ne_zero]; exact_mod_cast ht
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.smul_le]
      intro a ha y hy
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      have hx : (Pi.single j (t : E) : Fin n → E) ∈ Lb := by
        rw [hLb]
        intro k
        by_cases hk : k = j
        · subst hk; exact ⟨t, by simp, fun _ => dvd_refl t⟩
        · exact ⟨0, by simp [hk], fun _ => dvd_zero t⟩
      obtain ⟨r, hr⟩ := (mem_dual_iff Lb y).1 hy _ hx
      have hsum : ∑ k, star ((Pi.single j (t : E) : Fin n → E) k) * y k = star (t : E) * y j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      rw [hsum] at hr
      refine ⟨s * r, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hr]
      rw [show algebraMap (𝓞 E) E c = (c : E) from rfl, hc, mul_assoc]
  · intro x hx
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one] at hx
    choose r hr using hx
    let x' : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let w : Fin n → E := fun j => if j.1 + 1 = n then x j / star (t : E) else 0
    have hx' : x' ∈ Lb := by
      rw [hLb]
      intro j
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x', hj], fun _ => dvd_zero t⟩
      · exact ⟨r j, by simp [x', hj, hr j], fun h => absurd h hj⟩
    have hw : w ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) Lb := by
      rw [mem_dual_iff]
      intro z hz
      refine Subring.sum_mem _ fun k _ => ?_
      by_cases hk : k.1 + 1 = n
      · obtain ⟨q, hq, hdiv⟩ := (hLb z).1 hz k
        obtain ⟨d, rfl⟩ := hdiv hk
        obtain ⟨s, hs⟩ := star_int d
        refine ⟨s * r k, ?_⟩
        simp only [w, hk, if_true, hq]
        rw [map_mul, hr k, show algebraMap (𝓞 E) E s = (s : E) from rfl, hs]
        push_cast
        rw [star_mul', ← hr k]
        field_simp
      · exact ⟨0, by simp [w, hk]⟩
    have hxe : x = x' + c • w := by
      funext j
      by_cases hj : j.1 + 1 = n
      · simp only [x', w, hj, if_true, Pi.add_apply, Pi.smul_apply, zero_add]
        rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl, hc]
        field_simp
      · simp [x', w, hj]
    rw [hxe]
    exact Submodule.add_mem_sup hx' (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hw)

end GlobalTheory.TwU.BaseComp

open scoped TensorProduct

namespace GlobalTheory.TwU.BaseComp

/- English proof (translation)
Substitute `hJ` using the available equality. Establish `hfg : Lb.FG` using `fg_of_int Lb fun x hx j => by`. Take `⟨r, hr, -⟩` from `(hLb x).1 hx j`. Conclude with `⟨r, hr⟩`. Establish `hA : Formalism.L2.PairingIndexBounds.F.latAd (F` using `F) (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb := GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ Lb Lb (Module.Finite.iff_fg.2 hfg) (fun x => by simp)`.

Unfold `GlobalTheory.TwU.latCo`. Rewrite using `[hA]`. Unfold `Formalism.L2.PairingIndexBounds.F.compan`. Rewrite using `[GlobalTheory.Mem.Col2.AdT.mvL_one]`. Establish `key` using `GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual ((sp.cm.sig : E →+* E)) hσ Lb`.

Unfold `dualL at key`. Use `erw [key]`. Conclude with `sup_dual_eq_std t c ht hc Lb hLb`.
-/
theorem latCo_one_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (sp : Spaces R F E) (hσ : ∀ x, (sp.cm.sig : E →+* E) x = star x) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E)) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    GlobalTheory.TwU.latCo sp J 1 c 1 Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  subst hJ
  have hfg : Lb.FG := fg_of_int Lb fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have hA : Formalism.L2.PairingIndexBounds.F.latAd (F := F) (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb :=
    GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ Lb Lb (Module.Finite.iff_fg.2 hfg) (fun x => by simp)
  unfold GlobalTheory.TwU.latCo
  rw [hA]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual ((sp.cm.sig : E →+* E)) hσ Lb
  unfold dualL at key
  erw [key]
  exact sup_dual_eq_std t c ht hc Lb hLb

end GlobalTheory.TwU.BaseComp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `B X I hI hP l Z u i hi Lb hLb`. Establish `hG : gramN (I.rec7 l Z) i hi = 1` using `((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1`. Establish `ht : X.piT u ≠ 0`. Introduce `h0`. Establish `hc` using `l.pr.piT_cop u`.

Establish `h0' : (B.primes X).piT u = 0` using `h0`. Rewrite `hc` using `[h0', map_zero]`. Conclude with `not_isCoprime_zero_zero hc`. Conclude with `GlobalTheory.TwU.BaseComp.latCo_one_base _ (fun x => rfl) _ hG (X.piT u) (B.fields.conjO (X.piT u)) ht rfl Lb hLb`.
-/
theorem GlobalTheory.TwU.latCo_base_eq_stdL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), (∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N i) (X.piT u)) → GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) 1 Lb = StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i) := by
  intro B X I hI hP l Z u i hi Lb hLb
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have ht : X.piT u ≠ 0 := by
    intro h0
    have hc := l.pr.piT_cop u
    have h0' : (B.primes X).piT u = 0 := h0
    rw [h0', map_zero] at hc
    exact not_isCoprime_zero_zero hc
  exact GlobalTheory.TwU.BaseComp.latCo_one_base _ (fun x => rfl) _ hG (X.piT u) (B.fields.conjO (X.piT u)) ht rfl Lb hLb
