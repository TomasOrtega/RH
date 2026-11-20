import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Introduce `h0`. Use `hPr.piG_norm a` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `(Nat.cast_ne_zero.2 (hPr.g_prime a).ne_zero) this.symm`.
-/
theorem conjO_piG_ne (hPr : Pr.Ok) (a : Fin 2) : X.conjO (Pr.piG a) ≠ 0 := by
  intro h0
  have := hPr.piG_norm a
  rw [h0, mul_zero] at this
  exact (Nat.cast_ne_zero.2 (hPr.g_prime a).ne_zero) this.symm

/- English proof (translation)
The claim follows from `mem_divs (conjO_piG_ne hPr a) P`.
-/
theorem mem_vG_iff (hPr : Pr.Ok) (a : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Pr.vG a ↔ X.conjO (Pr.piG a) ∈ P.asIdeal := mem_divs (conjO_piG_ne hPr a) P

/- English proof (translation)
Rewrite `h` using `[hv, Ideal.mem_comap, map_natCast]`. Conclude with `h`.
-/
theorem g_mem_of_isOver {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)}
    (hv : IsOver v P) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ((Pr.g a : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [hv, Ideal.mem_comap, map_natCast] at h
  exact h

/- English proof (translation)
Break down `rll_over_cases hc hPv hQv with e | e` into its components or cases. Conclude with `e`. It suffices to derive a contradiction. Establish `hPa` using `mem_vG_of_g_mem hPr hP (g_mem_of_isOver hPv h)`. Establish `hQa` using `mem_vG_of_g_mem hPr hQ (g_mem_of_isOver hQv h)`.

Rewrite `hPa`, `hQa` using `[mem_vG_iff hPr]`. Rewrite `hQa` using `[e, mem_conjP]`. Establish `h2 : cO X.E (X.conjO (Pr.piG a)) = Pr.piG a` using `RingOfIntegers.ext (star_star _)`. Rewrite `hQa` using `[h2]`. Take `⟨x, y, hxy⟩` from `hPr.piG_cop a`.

Use `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)` and prove the remaining obligations. Rewrite using `[← hxy]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hQa) (Ideal.mul_mem_left _ _ hPa)`.
-/
theorem eq_of_isOver (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) {P Q : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) (hQ : Q ∈ Pr.vGs)
    (hPv : IsOver v P) (hQv : IsOver v Q) : Q = P := by
  rcases rll_over_cases hc hPv hQv with e | e
  · exact e
  exfalso
  have hPa := mem_vG_of_g_mem hPr hP (g_mem_of_isOver hPv h)
  have hQa := mem_vG_of_g_mem hPr hQ (g_mem_of_isOver hQv h)
  rw [mem_vG_iff hPr] at hPa hQa
  rw [e, mem_conjP] at hQa
  have h2 : cO X.E (X.conjO (Pr.piG a)) = Pr.piG a := RingOfIntegers.ext (star_star _)
  rw [h2] at hQa
  obtain ⟨x, y, hxy⟩ := hPr.piG_cop a
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ hQa) (Ideal.mul_mem_left _ _ hPa)

/- English proof (translation)
Establish `h01 : ∀ b : Fin 2, b = 0 ∨ b = 1` using `by decide`. Establish `hv : v ∈ plUnder X.F Pr.vGs`. Rewrite using `[plUnder_vGs hc hPr v]`. Break down `h01 a with rfl | rfl` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr h`. Take `⟨P, hP, hPv⟩` from `hv`. Conclude with `⟨⟨P, hP⟩, hPv⟩`.
-/
theorem exists_over_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ∃ w : {w // w ∈ Pr.vGs}, IsOver v w.1 := by
  have h01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  have hv : v ∈ plUnder X.F Pr.vGs := by
    rw [plUnder_vGs hc hPr v]
    rcases h01 a with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨P, hP, hPv⟩ := hv
  exact ⟨⟨P, hP⟩, hPv⟩

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem isOver_of_under {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : P.under (𝓞 X.F) = v) :
    IsOver v P := by
  subst h
  rfl

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext h.symm`.
-/
theorem under_of_isOver {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : IsOver v P) :
    P.under (𝓞 X.F) = v :=
  HeightOneSpectrum.ext h.symm

end GlobalTheory.Mem.TypePrimes

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Use `haveI : NeZero (Pr.g a) := ⟨(hPr.g_prime a).ne_zero⟩`. Establish `e` using `(nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime a) (by`. Rewrite using `[← hPr.vG_norm a w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some`. Conclude with `⟨(e.symm c).val, by rw [← map_natCast e, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]⟩`.
-/
theorem residue_natCast (hPr : Pr.Ok) {a : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG a)
    (c : 𝓞 X.E ⧸ w.asIdeal) : ∃ k : ℕ, c = k := by
  haveI : NeZero (Pr.g a) := ⟨(hPr.g_prime a).ne_zero⟩
  have e := (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime a) (by
    rw [← hPr.vG_norm a w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  exact ⟨(e.symm c).val, by rw [← map_natCast e, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]⟩

/- English proof (translation)
Rewrite using `[Finset.disjoint_left]`. Introduce `w h0 h1`. Establish `hc : IsCoprime ((Pr.g 0 : ℕ) : 𝓞 X.E) ((Pr.g 1 : ℕ) : 𝓞 X.E)` using `Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime 0) (hPr.g_prime 1)).2 hPr.g_ne)`. Take `⟨x, y, hxy⟩` from `hc`. Use `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)` and prove the remaining obligations.

Rewrite using `[← hxy]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h0)) (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h1))`.
-/
theorem vG_disjoint (hPr : Pr.Ok) : Disjoint (Pr.vG 0) (Pr.vG 1) := by
  rw [Finset.disjoint_left]
  intro w h0 h1
  have hc : IsCoprime ((Pr.g 0 : ℕ) : 𝓞 X.E) ((Pr.g 1 : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime 0) (hPr.g_prime 1)).2 hPr.g_ne)
  obtain ⟨x, y, hxy⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h0)) (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h1))

/- English proof (translation)
Introduce `X Pr hc hPr`. Set `wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs}` to `fun a v h => (exists_over_vGs hc hPr h).choose`. Establish `hspec : ∀ a v h, IsOver v (wOf a v h).1` using `fun a v h => (exists_over_vGs hc hPr h).choose_spec`. Establish `h1 : ∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h`. Introduce `a v h w`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `Subtype.ext (eq_of_isOver hc hPr h (wOf a v h).2 w.2 (hspec a v h) hw)`. Introduce and unpack `rfl`. Conclude with `hspec a v h`.

Establish `hin : ∀ a v h, (wOf a v h).1 ∈ Pr.vG a` using `fun a v h => mem_vG_of_g_mem hPr (wOf a v h).2 (g_mem_of_isOver (hspec a v h) h)`. Use `⟨wOf, h1, fun a v h => ⟨?_, under_of_isOver (hspec a v h), residue_natCast hPr (hin a v h)⟩, ?_⟩` and prove the remaining obligations. Introduce `P hPu hP`. Establish `hPa : P ∈ Pr.vG a` using `(mem_vG_iff hPr a P).2 hP`. Conclude with `eq_of_isOver hc hPr h (wOf a v h).2 (mem_vGs hPa) (hspec a v h) (isOver_of_under hPu)`.

Introduce `φ`. Set `φ' : HeightOneSpectrum (𝓞 X.E) → ℂ` to `fun w => if hw : w ∈ Pr.vGs then φ ⟨w, hw⟩ else 1`. Establish `hL : ∏ w, φ w = ∏ w ∈ Pr.vGs, φ' w`. Rewrite using `[← Finset.prod_coe_sort Pr.vGs φ']`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `only [φ', dif_pos w.2]`. Establish `hA : ∀ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) = ∏ w ∈ Pr.vG a, φ' w`. Introduce `a`. Set `f : HeightOneSpectrum (𝓞 X.F) → ℂ` to `fun v => if h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal then φ (wOf a v h) else 1`. Establish `e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h)) = ∏ᶠ v, f v`.

Use `finprod_congr fun v => ?_` and prove the remaining obligations. Conclude with `finprod_eq_dif _`. Establish `hsupp : Function.mulSupport f ⊆ ((Pr.vG a).image fun w => w.under (𝓞 X.F) : Finset _)`. Introduce `v hv`. Establish `h' : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal`.

Assume the negation of the conclusion as `hn`. Conclude with `hv (by simp only [f, dif_neg hn])`. Rewrite using `[Finset.coe_image]`. Conclude with `⟨(wOf a v h').1, hin a v h', under_of_isOver (hspec a v h')⟩`. Rewrite using `[e1, finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_image]`.

Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations. Establish `hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal` using `by show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `g_mem_of_vG hPr hw`. Establish `hw' : w ∈ Pr.vGs` using `mem_vGs hw`.

Establish `e2 : wOf a (w.under (𝓞 X.F)) hg = ⟨w, hw'⟩` using `((h1 a _ hg ⟨w, hw'⟩).1 (isOver_of_under rfl)).symm`. Simplify using `only [f, φ', dif_pos hg, dif_pos hw', e2]`. Introduce `w hw w' hw' he`. Establish `hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal` using `by show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`.

Conclude with `g_mem_of_vG hPr hw`. Conclude with `(eq_of_isOver hc hPr hg (mem_vGs hw) (mem_vGs hw') (isOver_of_under rfl) (isOver_of_under he.symm)).symm`. Rewrite using `[hL, Fin.prod_univ_two, hA 0, hA 1]`. Unfold `Primes.vGs`. Conclude with `Finset.prod_union (vG_disjoint hPr)`.
-/
theorem primes_over_places : ∀ (X : Fields) (Pr : Primes X) (hc : Formalism.BasicNotions.CMData X.F X.E), Pr.Ok →
    ∃ wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs},
      (∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h) ∧
      (∀ a v h, (∀ P : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = v → X.conjO (Pr.piG a) ∈ P.asIdeal →
          P = (wOf a v h).1) ∧ (wOf a v h).1.under (𝓞 X.F) = v ∧
        ∀ c : 𝓞 X.E ⧸ (wOf a v h).1.asIdeal, ∃ k : ℕ, c = k) ∧
      ∀ φ : {w // w ∈ Pr.vGs} → ℂ, ∏ w, φ w =
        ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) := by
  intro X Pr hc hPr
  classical
  let wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs} :=
    fun a v h => (exists_over_vGs hc hPr h).choose
  have hspec : ∀ a v h, IsOver v (wOf a v h).1 := fun a v h => (exists_over_vGs hc hPr h).choose_spec
  have h1 : ∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h := by
    intro a v h w
    constructor
    · intro hw
      exact Subtype.ext (eq_of_isOver hc hPr h (wOf a v h).2 w.2 (hspec a v h) hw)
    · rintro rfl
      exact hspec a v h
  have hin : ∀ a v h, (wOf a v h).1 ∈ Pr.vG a := fun a v h =>
    mem_vG_of_g_mem hPr (wOf a v h).2 (g_mem_of_isOver (hspec a v h) h)
  refine ⟨wOf, h1, fun a v h => ⟨?_, under_of_isOver (hspec a v h), residue_natCast hPr (hin a v h)⟩, ?_⟩
  · intro P hPu hP
    have hPa : P ∈ Pr.vG a := (mem_vG_iff hPr a P).2 hP
    exact eq_of_isOver hc hPr h (wOf a v h).2 (mem_vGs hPa) (hspec a v h) (isOver_of_under hPu)
  · intro φ
    let φ' : HeightOneSpectrum (𝓞 X.E) → ℂ := fun w => if hw : w ∈ Pr.vGs then φ ⟨w, hw⟩ else 1
    have hL : ∏ w, φ w = ∏ w ∈ Pr.vGs, φ' w := by
      rw [← Finset.prod_coe_sort Pr.vGs φ']
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [φ', dif_pos w.2]
    have hA : ∀ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) =
        ∏ w ∈ Pr.vG a, φ' w := by
      intro a
      let f : HeightOneSpectrum (𝓞 X.F) → ℂ := fun v => if h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal then φ (wOf a v h) else 1
      have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h)) = ∏ᶠ v, f v := by
        refine finprod_congr fun v => ?_
        exact finprod_eq_dif _
      have hsupp : Function.mulSupport f ⊆ ((Pr.vG a).image fun w => w.under (𝓞 X.F) : Finset _) := by
        intro v hv
        have h' : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal := by
          by_contra hn
          exact hv (by simp only [f, dif_neg hn])
        rw [Finset.coe_image]
        exact ⟨(wOf a v h').1, hin a v h', under_of_isOver (hspec a v h')⟩
      rw [e1, finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_image]
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        have hw' : w ∈ Pr.vGs := mem_vGs hw
        have e2 : wOf a (w.under (𝓞 X.F)) hg = ⟨w, hw'⟩ :=
          ((h1 a _ hg ⟨w, hw'⟩).1 (isOver_of_under rfl)).symm
        simp only [f, φ', dif_pos hg, dif_pos hw', e2]
      · intro w hw w' hw' he
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        exact (eq_of_isOver hc hPr hg (mem_vGs hw) (mem_vGs hw') (isOver_of_under rfl) (isOver_of_under he.symm)).symm
    rw [hL, Fin.prod_univ_two, hA 0, hA 1]
    unfold Primes.vGs
    exact Finset.prod_union (vG_disjoint hPr)

end GlobalTheory.Mem.TypePrimes
