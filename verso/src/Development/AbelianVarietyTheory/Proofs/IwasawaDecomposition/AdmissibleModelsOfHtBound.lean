import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemCommonRefinementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemLevelGrowthStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace AdmExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
The claim follows from `((Complex.isPrimitiveRoot_exp n hn).isIntegral (Nat.pos_of_ne_zero hn)).tower_top`.
-/
theorem zeta_isIntegral (n : ℕ) (hn : n ≠ 0) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn).isIntegral (Nat.pos_of_ne_zero hn)).tower_top

/- English proof (translation)
Set `l : Level H` to `{ i₀.l with A := i₀.l.A * k, A_pos := Nat.mul_pos i₀.l.A_pos hk }`. Establish `hA : l.A ≠ 0` using `l.A_pos.ne'`. Establish `hM : l.M' ≠ 0` using `Nat.lcm_ne_zero (by have := l.three_le; omega) hA`. Set `F : IntermediateField ℚ ℂ` to `i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M', zeta l.A}`. Establish `hfin : FiniteDimensional ℚ F` using `by haveI := i₀.c.fin haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ)) := IntermediateField.finiteDimensional_adjoin (by`.

Introduce and unpack `x (rfl | rfl)`. Conclude with `zeta_isIntegral _ hM`. Conclude with `zeta_isIntegral _ hA)`. Conclude with `IntermediateField.finiteDimensional_sup _ _`. Establish `h1 : i₀.c.F ≤ F` using `le_sup_left`.

Establish `h2 : IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ) ≤ F` using `le_sup_right`. Set `c : Coeff l` to `{ F := F fin := hfin conj := fun τ a => h1 (i₀.c.conj τ a) zeta_mem := h2 (IntermediateField.subset_adjoin _ _ (by simp)) le := by`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `h1 (i₀.c.le (IntermediateField.subset_adjoin _ _ (by simp)))`.

Conclude with `h2 (IntermediateField.subset_adjoin _ _ (by simp)) }`. Conclude with `⟨⟨l, c, i₀.good⟩, rfl, rfl, rfl, h1⟩`.
-/
theorem exists_idx {p : ℕ} (i₀ : Idx H p) (k : ℕ) (hk : 0 < k) :
    ∃ i : Idx H p, i.l.M = i₀.l.M ∧ i.l.Mb = i₀.l.Mb ∧ i.l.A = i₀.l.A * k ∧ i₀.c.F ≤ i.c.F := by
  let l : Level H := { i₀.l with A := i₀.l.A * k, A_pos := Nat.mul_pos i₀.l.A_pos hk }
  have hA : l.A ≠ 0 := l.A_pos.ne'
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) hA
  let F : IntermediateField ℚ ℂ := i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M', zeta l.A}
  have hfin : FiniteDimensional ℚ F := by
    haveI := i₀.c.fin
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ)) :=
      IntermediateField.finiteDimensional_adjoin (by
        rintro x (rfl | rfl)
        · exact zeta_isIntegral _ hM
        · exact zeta_isIntegral _ hA)
    exact IntermediateField.finiteDimensional_sup _ _
  have h1 : i₀.c.F ≤ F := le_sup_left
  have h2 : IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ) ≤ F := le_sup_right
  let c : Coeff l :=
    { F := F
      fin := hfin
      conj := fun τ a => h1 (i₀.c.conj τ a)
      zeta_mem := h2 (IntermediateField.subset_adjoin _ _ (by simp))
      le := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        rintro x (rfl | rfl)
        · exact h1 (i₀.c.le (IntermediateField.subset_adjoin _ _ (by simp)))
        · exact h2 (IntermediateField.subset_adjoin _ _ (by simp)) }
  exact ⟨⟨l, c, i₀.good⟩, rfl, rfl, rfl, h1⟩

/- English proof (translation)
Set `f : Letter Dw ⊕ Fin (letters Dw).length → ((E →+* ℂ) × ℕ) ⊕ ℕ` to `fun a => match a with`. Consider the case `.inl x => .inl (x.1, x.2)`. Consider the case `.inr k => .inr k`. Establish `: {st | ∃ x, letterOf Dw st = some x} ⊆ Set.range f`. Introduce and unpack `(⟨τ, k⟩ | k) ⟨x, hx⟩`.

Distinguish the cases in `h : k < Dw.mult τ`. Conclude with `⟨.inl ⟨τ, ⟨k, h⟩⟩, rfl⟩`. Simplify using `[letterOf, h] at hx`. Establish `h : k < (letters Dw).length`. Assume the negation of the conclusion as `h`.

Simplify using `only [letterOf] at hx`. Rewrite `hx` using `[List.getElem?_eq_none (not_lt.1 h)]`. Consider the cases of `hx`. Conclude with `⟨.inr ⟨k, h⟩, rfl⟩`. Conclude with `((Set.finite_range f).subset this).to_subtype`.
-/
theorem finite_steps (Dw : Datum H) : Finite {st // ∃ x, letterOf Dw st = some x} := by
  let f : Letter Dw ⊕ Fin (letters Dw).length → ((E →+* ℂ) × ℕ) ⊕ ℕ := fun a => match a with
    | .inl x => .inl (x.1, x.2)
    | .inr k => .inr k
  have : {st | ∃ x, letterOf Dw st = some x} ⊆ Set.range f := by
    rintro (⟨τ, k⟩ | k) ⟨x, hx⟩
    · by_cases h : k < Dw.mult τ
      · exact ⟨.inl ⟨τ, ⟨k, h⟩⟩, rfl⟩
      · simp [letterOf, h] at hx
    · have h : k < (letters Dw).length := by
        by_contra h
        simp only [letterOf] at hx
        rw [List.getElem?_eq_none (not_lt.1 h)] at hx
        cases hx
      exact ⟨.inr ⟨k, h⟩, rfl⟩
  exact ((Set.finite_range f).subset this).to_subtype

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h1 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h0` using `H.sqrt_neg_disc_sq`.

Establish `key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z` using `fun z hz => by`. Establish `hre` using `congrArg Complex.re hz`. Establish `him` using `congrArg Complex.im hz`. Simplify using `[pow_two] at hre him`. Establish `: z.re = 0`.

Assume the negation of the conclusion as `hne`. Establish `: z.im = 0`. Establish `: z.re * z.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `hre` using `[this]`.

Use polynomial arithmetic with `[sq_nonneg z.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [this]`. Establish `hne : H.rt0 ≠ 0`. Introduce `h`. Rewrite `h0` using `[h]`.

Establish `: (H.d : ℂ) = 0` using `by simpa using h0.symm`. Conclude with `hd.ne' (by exact_mod_cast this)`. Establish `hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ (H.rt : E) = -τ (H.rt : E)` using `key _ h1`. Unfold `Datum.mult`. Rewrite using `[hc]`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans h0.symm) with h | h` into its components or cases. Establish `: ¬ (-H.rt0 = H.rt0)` using `fun e => hne (by linear_combination -e / 2)`. Simplify using `[h, this]`. Establish `: ¬ (-H.rt0 = H.rt0)` using `fun e => hne (by linear_combination -e / 2)`. Simplify using `[h, this, add_comm]`.
-/
theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) : D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    simpa using this
  have h0 := H.sqrt_neg_disc_sq
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := fun z hz => by
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [pow_two] at hre him
    have : z.re = 0 := by
      by_contra hne
      have : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [sq_nonneg z.re]
    apply Complex.ext <;> simp [this]
  have hne : H.rt0 ≠ 0 := by
    intro h; rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0.symm
    exact hd.ne' (by exact_mod_cast this)
  have hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ (H.rt : E) = -τ (H.rt : E) := key _ h1
  unfold Datum.mult
  rw [hc]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans h0.symm) with h | h
  · have : ¬ (-H.rt0 = H.rt0) := fun e => hne (by linear_combination -e / 2)
    simp [h, this]
  · have : ¬ (-H.rt0 = H.rt0) := fun e => hne (by linear_combination -e / 2)
    simp [h, this, add_comm]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h2` using `mult_add_mult_conj Dw τ`. Distinguish the cases in `h0 : 0 < Dw.mult τ`. Conclude with `⟨⟨τ, ⟨0, h0⟩⟩⟩`. Conclude with `⟨⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ, ⟨0, by omega⟩⟩⟩`.
-/
theorem exists_letter (Dw : Datum H) (h : 1 ≤ Dw.p + Dw.q) : Nonempty (Letter Dw) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 := mult_add_mult_conj Dw τ
  by_cases h0 : 0 < Dw.mult τ
  · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
  · exact ⟨⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ, ⟨0, by omega⟩⟩⟩

/- English proof (translation)
Take `⟨i, hM, hMb, hA, hF⟩` from `exists_idx i₀ (p ^ n) (pow_pos hp.pos n)`. Establish `hd : i₀.l.Dvd i.l` using `⟨hM ▸ dvd_rfl, hMb.le, hA ▸ dvd_mul_right _ _⟩`. Establish `hpn : p ^ n ∣ i.l.A` using `hA ▸ dvd_mul_left _ _`. Establish `hex : ∀ b st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z b st x)`. Introduce `b st x hx`.

Consider the cases of `b`. Conclude with `GlobalTheory.T.local_system_model_exists E H Dw Xo p W Y i₀ hp hW hY i hd hF st x hx`. Conclude with `GlobalTheory.T.local_system_level_growth hB E H Dw Xo p W Y i₀ hp hW hY i n hd hF hpn hn st x hx`. Use `haveI := finite_steps Dw`. Set `T` to `Bool × {st // ∃ x, letterOf Dw st = some x}`.

Take `⟨x₀⟩` from `exists_letter Dw hr`. Use `haveI : Nonempty T := ⟨(false, ⟨.inl (x₀.1, x₀.2), x₀, by simp [letterOf]⟩)⟩`. Take `⟨m, hm⟩ : ∃ m, Nat.card T = m + 1` from `⟨Nat.card T - 1, by have := Nat.card_pos (α := T); omega⟩`. Set `e : T ≃ Fin (m + 1)` to `Finite.equivFinOfCardEq hm`. Use `choose Z hZi hZty hZl using fun t : T => hex t.1 t.2.1 t.2.2.choose t.2.2.choose_spec`.

Take `⟨Z', h1, h2, h3⟩` from `GlobalTheory.T.local_system_common_refinement E H Dw Xo p W Y i₀ hp hW hY m (fun a => Z (e.symm a)) (fun a => ⟨(hZi _).trans (hZi _).symm, (hZty _).trans (hZty _).symm⟩)`. Establish `h1' : Z'.i = i` using `h1.trans (hZi _)`. Establish `h2'` using `h2.trans (hZty _)`. Establish `hl : ∀ b st x, letterOf Dw st = some x → Nonempty (LineModel Z' b st x)`. Introduce `b st x hx`.

Set `t : T` to `(b, ⟨st, x, hx⟩)`. Take `⟨f, hf⟩` from `h3 (e t)`. Establish `hxe : t.2.2.choose = x` using `Option.some.inj (t.2.2.choose_spec.symm.trans hx)`. Establish `hl` using `hZl t`. Rewrite `hl` using `[hxe]`.

Use `GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY _ Z' f hf ?_ b st x hx ?_` and prove the remaining obligations. Introduce `τ k hk`. Rewrite using `[hZty]`. Conclude with `Finset.mem_range.2 (Nat.lt_succ_of_le hk)`. Rewrite using `[e.symm_apply_apply]`.

Conclude with `hl`. Use `⟨⟨Z', ?_, n, ?_, fun b st x hx => (hl b st x hx).some⟩, rfl⟩` and prove the remaining obligations. Introduce `τ k hk`. Rewrite using `[h2']`. Conclude with `Finset.mem_range.2 (Nat.lt_succ_of_le hk)`.

Rewrite using `[h1']`. Conclude with `⟨hM, hMb, hA⟩`.
-/
theorem exists_adm [IsGalois ℚ E] (hB : HTBoundSt) {Dw : Datum H} (hr : 1 ≤ Dw.p + Dw.q) {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ}
    {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) (i₀ : Idx H p) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hY : N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) (n : ℕ) (hn : 1 + 1 / ((p : ℝ) - 1) < n) :
    ∃ z : admitted Y i₀, z.n = n := by
  obtain ⟨i, hM, hMb, hA, hF⟩ := exists_idx i₀ (p ^ n) (pow_pos hp.pos n)
  have hd : i₀.l.Dvd i.l := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ dvd_mul_right _ _⟩
  have hpn : p ^ n ∣ i.l.A := hA ▸ dvd_mul_left _ _
  have hex : ∀ b st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧
      (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z b st x) := by
    intro b st x hx
    cases b
    · exact GlobalTheory.T.local_system_model_exists E H Dw Xo p W Y i₀ hp hW hY i hd hF st x hx
    · exact GlobalTheory.T.local_system_level_growth hB E H Dw Xo p W Y i₀ hp hW hY i n hd hF hpn hn st x hx
  haveI := finite_steps Dw
  let T := Bool × {st // ∃ x, letterOf Dw st = some x}
  obtain ⟨x₀⟩ := exists_letter Dw hr
  haveI : Nonempty T := ⟨(false, ⟨.inl (x₀.1, x₀.2), x₀, by simp [letterOf]⟩)⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card T = m + 1 := ⟨Nat.card T - 1, by have := Nat.card_pos (α := T); omega⟩
  let e : T ≃ Fin (m + 1) := Finite.equivFinOfCardEq hm
  choose Z hZi hZty hZl using fun t : T => hex t.1 t.2.1 t.2.2.choose t.2.2.choose_spec
  obtain ⟨Z', h1, h2, h3⟩ := GlobalTheory.T.local_system_common_refinement E H Dw Xo p W Y i₀ hp hW hY m (fun a => Z (e.symm a))
    (fun a => ⟨(hZi _).trans (hZi _).symm, (hZty _).trans (hZty _).symm⟩)
  have h1' : Z'.i = i := h1.trans (hZi _)
  have h2' := h2.trans (hZty _)
  have hl : ∀ b st x, letterOf Dw st = some x → Nonempty (LineModel Z' b st x) := by
    intro b st x hx
    let t : T := (b, ⟨st, x, hx⟩)
    obtain ⟨f, hf⟩ := h3 (e t)
    have hxe : t.2.2.choose = x := Option.some.inj (t.2.2.choose_spec.symm.trans hx)
    have hl := hZl t
    rw [hxe] at hl
    refine GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY _ Z' f hf ?_ b st x hx ?_
    · intro τ k hk
      rw [hZty]
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    · rw [e.symm_apply_apply]
      exact hl
  refine ⟨⟨Z', ?_, n, ?_, fun b st x hx => (hl b st x hx).some⟩, rfl⟩
  · intro τ k hk
    rw [h2']
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  · rw [h1']
    exact ⟨hM, hMb, hA⟩

end AdmExist

/- English proof (translation)
Introduce `hB D A N j S κ p hp W hW n hn`. Use `haveI := D.host.hostE_isGalois`. Conclude with `AdmExist.exists_adm hB (by have := S.rank_eq; have := S.two_le; omega) _ _ hp hW (S.sys.clauses p W hp hW) n hn`.
-/
theorem admEx_of_htBound : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), AdmEx S κ := by
  intro hB D A N j S κ p hp W hW n hn
  haveI := D.host.hostE_isGalois
  exact AdmExist.exists_adm hB (by have := S.rank_eq; have := S.two_le; omega) _ _ hp hW (S.sys.clauses p W hp hW) n hn

end GlobalTheory.ShFam.Pad
