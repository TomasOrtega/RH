import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExtCContract
import ReciprocityTheory.AnalyticForms.RegularLocalRings.GenSmooth
import Lemmata.GeneralBFactThirdLast.Imports

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `p`. Rewrite using `[RingHom.comp_apply, MvPolynomial.map_map]`. Use `congr 1`.
-/
theorem map_int_comp :
    (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := by
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply, MvPolynomial.map_map]
  congr 1

/- English proof (translation)
Unfold `pC extC extQ`. Rewrite using `[Ideal.map_map, map_int_comp]`. Both sides reduce to the same expression.
-/
theorem pC_eq_extC_extQ (P : Ideal (MRing ι)) : pC P = extC (extQ P) := by
  unfold pC extC extQ
  rw [Ideal.map_map, map_int_comp]
  rfl

/- English proof (translation)
Introduce `m hm`. Establish `h1 : m ∈ P.comap (C : ℤ →+* MRing ι)` using `hm`. Unfold `IsHorizontal at h`. Rewrite `h1` using `[h]`. Conclude with `Ideal.mem_bot.mp h1`.
-/
theorem horizontal_spec {P : Ideal (MRing ι)} (h : IsHorizontal P) :
    ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
  intro m hm
  have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
  unfold IsHorizontal at h
  rw [h] at h1
  exact Ideal.mem_bot.mp h1

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. Rewrite `h` using `[WithBot.bot_add]`. Conclude with `absurd h.symm (by simp)`. Consider the case `coe b`.

Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top`. Simplify using `at h`. Conclude with `absurd h.symm (fun h2 => ENat.coe_ne_top n (WithBot.coe_injective (show ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from h2)))`. Consider the case `coe k`.

Establish `h' : ((k + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)` using `by exact_mod_cast h`. Establish `h2 : k + 1 = n + 1` using `by exact_mod_cast h'`. Establish `hk : k = n` using `by omega`. Substitute `hk` using the available equality. Use `norm_cast`.
-/
theorem withBot_eq_of_add_one {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : a = (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h.symm (by simp)
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      simp at h
      exact absurd h.symm (fun h2 => ENat.coe_ne_top n (WithBot.coe_injective
        (show ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from h2)))
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h2 : k + 1 = n + 1 := by exact_mod_cast h'
      have hk : k = n := by omega
      subst hk
      norm_cast

/- English proof (translation)
Introduce `K _ ι _ P e hP`. Take `⟨_, hMP, hH, _⟩` from `hP`. Use `haveI : P.IsPrime := hMP.1`. Take `⟨hpr, _, _⟩` from `extQ_spec P (horizontal_spec hH)`. Use `haveI := hpr`.

Rewrite using `[pC_eq_extC_extQ]`. Conclude with `extC_isRadical (extQ P)`.
-/
theorem pcRadical : PCRadicalStatement := by
  intro K _ ι _ P e hP
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, _⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ]
  exact extC_isRadical (extQ P)

/- English proof (translation)
Introduce `K _ ι _ P e hP Q hQ`. Take `⟨_, hMP, hH, hdim⟩` from `hP`. Use `haveI : P.IsPrime := hMP.1`. Take `⟨hpr, _, hd⟩` from `extQ_spec P (horizontal_spec hH)`. Use `haveI := hpr`.

Rewrite `hQ` using `[pC_eq_extC_extQ]`. Rewrite using `[ringKrullDim_of_mem_minimalPrimes_extC (extQ P) Q hQ]`. Apply `withBot_eq_of_add_one` to reduce the goal to its premises. Rewrite using `[hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]`.
-/
theorem pcEquidim : PCEquidimStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [ringKrullDim_of_mem_minimalPrimes_extC (extQ P) Q hQ]
  apply withBot_eq_of_add_one
  rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]

/- English proof (translation)
Introduce `K _ ι _ P e hP Q hQ`. Take `⟨_, hMP, hH, _⟩` from `hP`. Use `haveI : P.IsPrime := hMP.1`. Take `⟨hpr, hcomap, _⟩` from `extQ_spec P (horizontal_spec hH)`. Use `haveI := hpr`.

Rewrite `hQ` using `[pC_eq_extC_extQ]`. Rewrite using `[← map_int_comp, ← Ideal.comap_comap, comap_of_mem_minimalPrimes_extC (extQ P) Q hQ, hcomap]`.
-/
theorem pcMinContract : PCMinContractStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [← map_int_comp, ← Ideal.comap_comap, comap_of_mem_minimalPrimes_extC (extQ P) Q hQ, hcomap]

/- English proof (translation)
Introduce `K _ ι _ P e hP f hf`. Take `⟨_, hMP, hH, _⟩` from `hP`. Use `haveI : P.IsPrime := hMP.1`. Take `⟨_, hcomap, _⟩` from `extQ_spec P (horizontal_spec hH)`. Rewrite `hf` using `[pC_eq_extC_extQ]`.

Establish `h1 : f ∈ (extC (extQ P)).comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)` using `hf`. Rewrite `h1` using `[← map_int_comp, ← Ideal.comap_comap, comap_extC, hcomap]`. Conclude with `h1`.
-/
theorem pcContract : PCContractStatement := by
  intro K _ ι _ P e hP f hf
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨_, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  rw [pC_eq_extC_extQ] at hf
  have h1 : f ∈ (extC (extQ P)).comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := hf
  rw [← map_int_comp, ← Ideal.comap_comap, comap_extC, hcomap] at h1
  exact h1

/- English proof (translation)
Introduce `K _ ι _ P e hP`. Take `⟨_, hMP, hH, hdim⟩` from `hP`. Use `haveI : P.IsPrime := hMP.1`. Take `⟨S, hShom, hSspan⟩` from `hMP.2.1`. Take `⟨hpr, _, hd⟩` from `extQ_spec P (horizontal_spec hH)`.

Use `haveI := hpr`. Take `⟨F0, hF0⟩ : P.FG` from `IsNoetherian.noetherian P`. Establish `hfin : ∀ x ∈ F0, ∃ T : Finset (MRing ι), (↑T : Set (MRing ι)) ⊆ S ∧ x ∈ Submodule.span (MRing ι) (↑T : Set (MRing ι))`. Introduce `x hx`. Establish `hxP : x ∈ P` using `hF0 ▸ Submodule.subset_span hx`.

Rewrite `hxP` using `[hSspan]`. Conclude with `Submodule.mem_span_finite_of_mem_span hxP`. Use `choose T hTS hxT using hfin`. Set `T' : Finset (MRing ι)` to `F0.attach.biUnion fun x => T x.1 x.2`. Establish `hT'S : (↑T' : Set (MRing ι)) ⊆ S`.

Introduce `y hy`. Take `⟨x, _, hyx⟩` from `Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)`. Conclude with `hTS x.1 x.2 hyx`. Establish `hspanT' : Ideal.span (↑T' : Set (MRing ι)) = P`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[hSspan]`. Conclude with `Ideal.span_mono hT'S`. Rewrite using `[← hF0]`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce `x hx`.

Conclude with `Ideal.span_mono (fun y hy => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩)) (hxT x hx)`. Set `G : Fin T'.card → MRing ι` to `fun i => (T'.equivFin.symm i : MRing ι)`. Establish `hrange : Set.range G = ↑T'`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(T'.equivFin.symm i).2`. Introduce `hy`. Conclude with `⟨T'.equivFin ⟨y, hy⟩, by simp [G]⟩`. Use `⟨T'.card, G, fun i => hShom _ (hT'S (T'.equivFin.symm i).2), by rw [hrange, hspanT'], ?_⟩` and prove the remaining obligations.

Set `Gq : Fin T'.card → MvPolynomial (Σ k, ι k) ℚ` to `fun i => MvPolynomial.map (Int.castRingHom ℚ) (G i)`. Establish `hGq : Ideal.span (Set.range Gq) = extQ P`. Unfold `extQ`. Rewrite using `[← hspanT', ← hrange, Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.

Establish `hdq : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ extQ P) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)`. Apply `withBot_eq_of_add_one` to reduce the goal to its premises. Rewrite using `[hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]`. Take `⟨a, b, hab⟩` from `exists_jacobian_minor_not_mem (extQ P) Gq hGq (e + Fintype.card K) hdq`. Introduce `hle`.

Apply `hab` to reduce the goal to its premises. Establish `hmem : Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∈ P` using `hle (Submodule.subset_span ⟨a, b, rfl⟩)`. Establish `hmap : MvPolynomial.map (Int.castRingHom ℚ) (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) ∈ extQ P` using `Ideal.mem_map_of_mem _ hmem`. Rewrite `hmap` using `[RingHom.map_det]`. Use `hmap using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `[Gq, RingHom.mapMatrix_apply, MvPolynomial.pderiv_map]`.
-/
theorem jacNotInP : JacNotInPStatement := by
  classical
  intro K _ ι _ P e hP
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨S, hShom, hSspan⟩ := hMP.2.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  obtain ⟨F0, hF0⟩ : P.FG := IsNoetherian.noetherian P
  have hfin : ∀ x ∈ F0, ∃ T : Finset (MRing ι), (↑T : Set (MRing ι)) ⊆ S ∧
      x ∈ Submodule.span (MRing ι) (↑T : Set (MRing ι)) := by
    intro x hx
    have hxP : x ∈ P := hF0 ▸ Submodule.subset_span hx
    rw [hSspan] at hxP
    exact Submodule.mem_span_finite_of_mem_span hxP
  choose T hTS hxT using hfin
  let T' : Finset (MRing ι) := F0.attach.biUnion fun x => T x.1 x.2
  have hT'S : (↑T' : Set (MRing ι)) ⊆ S := by
    intro y hy
    obtain ⟨x, _, hyx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    exact hTS x.1 x.2 hyx
  have hspanT' : Ideal.span (↑T' : Set (MRing ι)) = P := by
    apply le_antisymm
    · rw [hSspan]
      exact Ideal.span_mono hT'S
    · rw [← hF0]
      apply Submodule.span_le.mpr
      intro x hx
      exact Ideal.span_mono (fun y hy => Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩)) (hxT x hx)
  let G : Fin T'.card → MRing ι := fun i => (T'.equivFin.symm i : MRing ι)
  have hrange : Set.range G = ↑T' := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (T'.equivFin.symm i).2
    · intro hy
      exact ⟨T'.equivFin ⟨y, hy⟩, by simp [G]⟩
  refine ⟨T'.card, G, fun i => hShom _ (hT'S (T'.equivFin.symm i).2), by rw [hrange, hspanT'], ?_⟩
  let Gq : Fin T'.card → MvPolynomial (Σ k, ι k) ℚ := fun i => MvPolynomial.map (Int.castRingHom ℚ) (G i)
  have hGq : Ideal.span (Set.range Gq) = extQ P := by
    unfold extQ
    rw [← hspanT', ← hrange, Ideal.map_span, ← Set.range_comp]
    rfl
  have hdq : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ extQ P) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_eq_of_add_one
    rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]
  obtain ⟨a, b, hab⟩ := exists_jacobian_minor_not_mem (extQ P) Gq hGq (e + Fintype.card K) hdq
  intro hle
  apply hab
  have hmem : Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∈ P :=
    hle (Submodule.subset_span ⟨a, b, rfl⟩)
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) ∈
      extQ P := Ideal.mem_map_of_mem _ hmem
  rw [RingHom.map_det] at hmap
  convert hmap using 2
  ext i j
  simp [Gq, RingHom.mapMatrix_apply, MvPolynomial.pderiv_map]

end ReciprocityTheory.ChartRestriction.G.Geo
