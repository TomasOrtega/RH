import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsRank
import Formalism.LocalToGlobal.Columns.RowFormsNZs
import Formalism.LocalToGlobal.Columns.RowFormsNZc
import Formalism.LocalToGlobal.Columns.RowFormsNZw

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Chr

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[mem_btG]`. Introduce `i j hij`. Rewrite using `[permGL_val, pM_apply, if_neg]`. Introduce `h`. Rewrite `hij` using `[h, hβ]`.

Conclude with `lt_irrefl _ hij`.
-/
theorem nz_pM_bt (κ : Type) [CommRing κ] {β : ℕ → ℕ} (s : Equiv.Perm (Fin n)) (hβ : ∀ b : Fin n, β (s b).val = β b.val) :
    permGL κ s ∈ btG n κ β := by
  rw [mem_btG]
  intro i j hij
  rw [permGL_val, pM_apply, if_neg]
  intro h
  rw [h, hβ] at hij
  exact lt_irrefl _ hij

def sgnU (κ : Type) [CommRing κ] : ℤˣ →* κˣ := Units.map (Int.castRingHom κ).toMonoidHom

/- English proof (translation)
Break down `Int.units_eq_one_or ε with h | h` into its components or cases. Use `left`. Rewrite using `[h, map_one]`. Use `right`. Rewrite using `[h]`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[sgnU]`.
-/
theorem sgnU_eq (κ : Type) [CommRing κ] (ε : ℤˣ) : sgnU κ ε = 1 ∨ sgnU κ ε = -1 := by
  rcases Int.units_eq_one_or ε with h | h
  · left; rw [h, map_one]
  · right
    rw [h]
    apply Units.ext
    simp [sgnU]

/- English proof (translation)
Use `⟨blkDet n ℤ β c ⟨permGL ℤ s, nz_pM_bt ℤ s hβ⟩, fun κ _ hM => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `show _ = (Int.castRingHom κ) ((blkDet n ℤ β c ⟨permGL ℤ s, nz_pM_bt ℤ s hβ⟩ : ℤˣ) : ℤ)`. Rewrite using `[blkDet_val, blkDet_val, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Use `show pM κ s i.1 j.1 = (Int.castRingHom κ) (pM ℤ s i.1 j.1)`. Rewrite using `[pM_apply, pM_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem nz_blkDet {β : ℕ → ℕ} (s : Equiv.Perm (Fin n)) (hβ : ∀ b : Fin n, β (s b).val = β b.val) (c : ℕ) :
    ∃ ε : ℤˣ, ∀ (κ : Type) [CommRing κ] (hM : permGL κ s ∈ btG n κ β), blkDet n κ β c ⟨permGL κ s, hM⟩ = sgnU κ ε := by
  refine ⟨blkDet n ℤ β c ⟨permGL ℤ s, nz_pM_bt ℤ s hβ⟩, fun κ _ hM => ?_⟩
  apply Units.ext
  show _ = (Int.castRingHom κ) ((blkDet n ℤ β c ⟨permGL ℤ s, nz_pM_bt ℤ s hβ⟩ : ℤˣ) : ℤ)
  rw [blkDet_val, blkDet_val, RingHom.map_det]
  congr 1
  ext i j
  show pM κ s i.1 j.1 = (Int.castRingHom κ) (pM ℤ s i.1 j.1)
  rw [pM_apply, pM_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[blockZero_val]`. Use `show pM κ s (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix (Fin r) (Fin r) κ) i j`. Rewrite using `[pM_apply, hfix _ (show (Fin.castLE h j).val < r from j.2), Matrix.one_apply]`.

Distinguish the cases in `hij : i = j`. Rewrite using `[if_pos hij, if_pos (by rw [hij])]`. Rewrite using `[if_neg hij, if_neg (fun hc => hij (Fin.castLE_injective h hc))]`.
-/
theorem blockZero_permutation_eq_one {κ : Type} [CommRing κ] {r : ℕ} (h : r ≤ n) (bl : List ℕ) (s : Equiv.Perm (Fin n))
    (hfix : ∀ b : Fin n, b.val < r → s b = b) (hM : permGL κ s ∈ blockUT n κ r bl) :
    blk0 n κ h bl ⟨permGL κ s, hM⟩ = 1 := by
  apply Units.ext
  ext i j
  rw [blockZero_val]
  show pM κ s (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix (Fin r) (Fin r) κ) i j
  rw [pM_apply, hfix _ (show (Fin.castLE h j).val < r from j.2), Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos (by rw [hij])]
  · rw [if_neg hij, if_neg (fun hc => hij (Fin.castLE_injective h hc))]

variable {κ K : Type} [CommRing κ] [Field K]

/- English proof (translation)
Distinguish the cases in `hm : permGL κ s ∈ HPar n κ h bl H₀`. Rewrite using `[Lev.ev_of_mem _ hm] show lamPar h bl lam₀ χ ⟨permGL κ s, hm⟩ = 1`. Rewrite using `[lamPar_apply, detChar_apply]`. Establish `h1 : (⟨blk0 n κ h bl ⟨permGL κ s, HPar_le h bl H₀ hm⟩, (mem_HPar.mp hm).2⟩ : ↥H₀) = 1` using `Subtype.ext (blockZero_permutation_eq_one h bl s hfix _)`. Rewrite using `[h1, map_one, one_mul]`.

Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Take `⟨ε, hε⟩` from `nz_blkDet (β := coarse r bl) s hco (c + 1)`. Rewrite using `[hε κ, hχ]`. Conclude with `dif_neg hm`.
-/
theorem nz_lamPar_ev {r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) (lam₀ : ↥H₀ →* Kˣ) (χ : ℕ → κˣ →* Kˣ)
    (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b)
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (hχ : ∀ (c : ℕ) (ε : ℤˣ), χ c (sgnU κ ε) = 1) :
    (⟨HPar n κ h bl H₀, lamPar h bl lam₀ χ⟩ : Lev κ K n).ev (permGL κ s) = 1 := by
  by_cases hm : permGL κ s ∈ HPar n κ h bl H₀
  · rw [Lev.ev_of_mem _ hm]
    show lamPar h bl lam₀ χ ⟨permGL κ s, hm⟩ = 1
    rw [lamPar_apply, detChar_apply]
    have h1 : (⟨blk0 n κ h bl ⟨permGL κ s, HPar_le h bl H₀ hm⟩, (mem_HPar.mp hm).2⟩ : ↥H₀) = 1 :=
      Subtype.ext (blockZero_permutation_eq_one h bl s hfix _)
    rw [h1, map_one, one_mul]
    refine Finset.prod_eq_one fun c _ => ?_
    obtain ⟨ε, hε⟩ := nz_blkDet (β := coarse r bl) s hco (c + 1)
    rw [hε κ, hχ]
  · exact dif_neg hm

/- English proof (translation)
Distinguish the cases in `h : x < a`. Rewrite using `[if_pos h, coarse_of_lt h]`. Rewrite using `[if_neg h, coarse_of_le (Nat.not_lt.mp h)]`. Establish `: x - a < b` using `by omega`. Simplify using `[blkIdx, this]`.
-/
theorem nz_coarse_two {a b x : ℕ} (hx : x < a + b) : coarse a [b] x = if x < a then 0 else 1 := by
  by_cases h : x < a
  · rw [if_pos h, coarse_of_lt h]
  · rw [if_neg h, coarse_of_le (Nat.not_lt.mp h)]
    have : x - a < b := by omega
    simp [blkIdx, this]

/- English proof (translation)
Rewrite using `[nz_coarse_two (lt_of_lt_of_le (s x).2 hn), nz_coarse_two (lt_of_lt_of_le x.2 hn)]`. Use `nz_ge_of_fix s hfix x` as an intermediate fact. Distinguish the cases in `h : x.val < a`. Rewrite using `[if_pos h, if_pos (by omega)]`. Rewrite using `[if_neg h, if_neg (by omega)]`.
-/
theorem nz_coarse_two_perm {a b : ℕ} (hn : n ≤ a + b) (s : Equiv.Perm (Fin n)) (hfix : ∀ x : Fin n, x.val < a → s x = x)
    (x : Fin n) : coarse a [b] (s x).val = coarse a [b] x.val := by
  rw [nz_coarse_two (lt_of_lt_of_le (s x).2 hn), nz_coarse_two (lt_of_lt_of_le x.2 hn)]
  have := nz_ge_of_fix s hfix x
  by_cases h : x.val < a
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/- English proof (translation)
Take `⟨ε, hε⟩` from `nz_blkDet (β := coarse a [b]) s (nz_coarse_two_perm hn s hfix) 1`. Use `⟨ε, fun κ _ ξ => ?_⟩` and prove the remaining obligations. Establish `hm : permGL κ s ∈ HQ κ n a b` using `nz_pM_bt κ s (nz_coarse_two_perm hn s hfix)`. Rewrite using `[Lev.ev_of_mem _ hm]`. Use `show lamQ ξ n a b ⟨permGL κ s, hm⟩ = _`.

Rewrite using `[lamQ_apply, hε κ]`.
-/
theorem nz_lamQ_ev {a b : ℕ} (hn : n ≤ a + b) (s : Equiv.Perm (Fin n)) (hfix : ∀ x : Fin n, x.val < a → s x = x) :
    ∃ ε : ℤˣ, ∀ (κ : Type) [CommRing κ] (ξ : κˣ →* Kˣ),
      (⟨HQ κ n a b, lamQ ξ n a b⟩ : Lev κ K n).ev (permGL κ s) = ξ (sgnU κ ε) := by
  obtain ⟨ε, hε⟩ := nz_blkDet (β := coarse a [b]) s (nz_coarse_two_perm hn s hfix) 1
  refine ⟨ε, fun κ _ ξ => ?_⟩
  have hm : permGL κ s ∈ HQ κ n a b := nz_pM_bt κ s (nz_coarse_two_perm hn s hfix)
  rw [Lev.ev_of_mem _ hm]
  show lamQ ξ n a b ⟨permGL κ s, hm⟩ = _
  rw [lamQ_apply, hε κ]

end Chr

section Gen

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}

/- English proof (translation)
Use `(GSD.finrank_pos_iff hOk).mpr ⟨nzPt (nzFr pos i0 hi w1), v, hv, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨s, hfix, hco, hγ, hh⟩` from `nz_stab_perm hX pos bl i0 hi w1 w2 hne hg1 hg2 hgw1 hgw2 hb1 hb2 g.1 g.2.1 (hΛ2 (Λ.mem_at g.2 w2)) (hΛ1 (Λ.mem_at g.2 w1)) hg`. Use `show ((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 v = v`. Rewrite using `[hchr s g.2 hfix hco hh, hrho s g.1 hfix hco hγ, Units.val_one, one_smul]`.
-/
theorem nz_form_pos (C : CoefPk X n (DecoSet X.E n ∅ SG)) (Λ : LevFam X.E X.K n SG) (hOk : (formGSD C Λ).Ok) (hX : X.Ok)
    (pos : Equiv.Perm (Fin n)) {r : ℕ} (bl : List ℕ) (i0 : Fin n) (hi : i0.val < r)
    (w1 w2 : SG) (hne : w2 ≠ w1) {g1 g2 : ℕ} (hg1 : g1.Prime) (hg2 : g2.Prime)
    (hgw1 : (g1 : 𝓞 X.E) ∈ w1.1.asIdeal) (hgw2 : (g2 : 𝓞 X.E) ∈ w2.1.asIdeal) (hb1 : 2 * X.f + 1 < g1)
    (hb2 : 2 * X.f + 1 < g2) (hΛ2 : (Λ w2).H ≤ uniUT n _ r bl) (hΛ1 : (Λ w1).H ≤ blockUT n _ r bl)
    (v : C.V) (hv : v ≠ 0)
    (hrho : ∀ (s : Equiv.Perm (Fin n)) (γ : UF X.E n), (∀ b : Fin n, b.val < r → s b = b) →
      (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) → ufGL X.E n γ = permGL X.E (pos * s * pos⁻¹) → C.rho γ v = v)
    (hchr : ∀ (s : Equiv.Perm (Fin n)) (h : ↥Λ.grp), (∀ b : Fin n, b.val < r → s b = b) →
      (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) → (∀ w, h.1 w = permGL _ s) → Λ.chr h = 1) :
    0 < finrank X.K (formGSD C Λ).EqFun := by
  refine (GSD.finrank_pos_iff hOk).mpr ⟨nzPt (nzFr pos i0 hi w1), v, hv, fun g hg => ?_⟩
  obtain ⟨s, hfix, hco, hγ, hh⟩ := nz_stab_perm hX pos bl i0 hi w1 w2 hne hg1 hg2 hgw1 hgw2 hb1 hb2 g.1 g.2.1
    (hΛ2 (Λ.mem_at g.2 w2)) (hΛ1 (Λ.mem_at g.2 w1)) hg
  show ((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 v = v
  rw [hchr s g.2 hfix hco hh, hrho s g.1 hfix hco hγ, Units.val_one, one_smul]

end Gen

section Signs

variable {X : Fields} {Pr : Primes X} {R : Ranks}

open Classical in
/- English proof (translation)
Unfold `Primes.vGs at hw`. Break down `Finset.mem_union.mp hw with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`.
-/
theorem nz_mem_vG {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) : ∃ i, w ∈ Pr.vG i := by
  unfold Primes.vGs at hw
  rcases Finset.mem_union.mp hw with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/- English proof (translation)
Take `⟨i, hi⟩` from `nz_mem_vG w.2`. Take `⟨om, -, hom⟩` from `hCh.chi_om i`. Establish `hp : Fact (Pr.g i).Prime` using `⟨hPr.g_prime i⟩`. Establish `hg0 : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.mpr (hPr.g_mem hi)` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hval : (((-1 : (ZMod (Pr.g i))ˣ) : ZMod (Pr.g i))).val = Pr.g i - 1`. Rewrite using `[Units.val_neg, Units.val_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]`. Rewrite using `[hom w hi j (-1) (-1) (by`. Rewrite using `[hval, Nat.cast_sub (hPr.g_prime i).one_le, hg0, Nat.cast_one, zero_sub, Units.val_neg, Units.val_one])]`.

Rewrite using `[pow_mul, ← map_pow, neg_one_sq, map_one, one_pow]`.
-/
theorem nz_chi_neg_one {m : ℕ} {Ch : Chars X Pr m} (hPr : Pr.Ok) (hCh : Ch.Ok) (w : {w // w ∈ Pr.vGs}) (j : Fin m) :
    Ch.chi j w (-1) = 1 := by
  obtain ⟨i, hi⟩ := nz_mem_vG w.2
  obtain ⟨om, -, hom⟩ := hCh.chi_om i
  have hp : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hPr.g_mem hi)
    rwa [map_natCast] at this
  have hval : (((-1 : (ZMod (Pr.g i))ˣ) : ZMod (Pr.g i))).val = Pr.g i - 1 := by
    rw [Units.val_neg, Units.val_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  rw [hom w hi j (-1) (-1) (by
    rw [hval, Nat.cast_sub (hPr.g_prime i).one_le, hg0, Nat.cast_one, zero_sub, Units.val_neg, Units.val_one])]
  rw [pow_mul, ← map_pow, neg_one_sq, map_one, one_pow]

/- English proof (translation)
Break down `sgnU_eq (𝓞 X.E ⧸ w.1.asIdeal) ε with h | h` into its components or cases. Rewrite using `[h, map_one]`. Rewrite using `[h]`. Unfold `chiAt extChi`. Use `split_ifs`.

Conclude with `nz_chi_neg_one hPr hCh w _`. Both sides reduce to the same expression.
-/
theorem nz_chiAt_sgn {Ch : Chars X Pr R.m} (hPr : Pr.Ok) (hCh : Ch.Ok) (w : {w // w ∈ Pr.vGs}) (c : ℕ) (ε : ℤˣ) :
    chiAt Ch w c (sgnU _ ε) = 1 := by
  rcases sgnU_eq (𝓞 X.E ⧸ w.1.asIdeal) ε with h | h
  · rw [h, map_one]
  · rw [h]
    unfold chiAt extChi
    split_ifs
    · exact nz_chi_neg_one hPr hCh w _
    · rfl

open Classical in

def XiSign (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (ξ : Chr X.F X.E X.K) : Prop :=
  ∏ P ∈ QE sel ξ \ Pr.vGs, resChar ξ P (-1) = 1

open Classical in
/- English proof (translation)
Break down `Int.units_eq_one_or ε with he | he` into its components or cases. Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations. Rewrite using `[he, map_one, map_one, ite_self]`. Establish `h1 : ∀ w : HeightOneSpectrum (𝓞 X.E), sgnU (𝓞 X.E ⧸ w.asIdeal) ε = -1`. Introduce `w`.

Rewrite using `[he]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[sgnU]`. Simplify using `only [h1]`. Rewrite using `[Finset.prod_coe_sort (uSG Pr.vGs (QE sel ξ)) (fun w => if w ∈ Pr.vGs then (1 : X.Kˣ) else resChar ξ w (-1)), Finset.prod_ite, Finset.prod_const_one, one_mul]`.

Establish `h2 : (uSG Pr.vGs (QE sel ξ)).filter (fun w => ¬ w ∈ Pr.vGs) = QE sel ξ \ Pr.vGs`. Use extensionality with `w`. Simplify using `only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]`. The claim follows by propositional logic. Rewrite using `[h2]`.

Conclude with `h`.
-/
theorem XiSign.prod {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {ξ : Chr X.F X.E X.K}
    (h : XiSign Pr sel ξ) (ε : ℤˣ) :
    (∏ w : uSG Pr.vGs (QE sel ξ), if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar ξ w.1 (sgnU _ ε)) = 1 := by
  rcases Int.units_eq_one_or ε with he | he
  · refine Finset.prod_eq_one fun w _ => ?_
    rw [he, map_one, map_one, ite_self]
  · have h1 : ∀ w : HeightOneSpectrum (𝓞 X.E), sgnU (𝓞 X.E ⧸ w.asIdeal) ε = -1 := by
      intro w
      rw [he]
      apply Units.ext
      simp [sgnU]
    simp only [h1]
    rw [Finset.prod_coe_sort (uSG Pr.vGs (QE sel ξ))
      (fun w => if w ∈ Pr.vGs then (1 : X.Kˣ) else resChar ξ w (-1)), Finset.prod_ite, Finset.prod_const_one, one_mul]
    have h2 : (uSG Pr.vGs (QE sel ξ)).filter (fun w => ¬ w ∈ Pr.vGs) = QE sel ξ \ Pr.vGs := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [h2]
    exact h

/- English proof (translation)
Unfold `XiSign`. Rewrite using `[twistPrimes_trivialTuple_empty]`. Simplify using the standard rewrite rules.
-/
theorem signCondition_trivialTuple (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) :
    XiSign Pr sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) := by
  unfold XiSign
  rw [twistPrimes_trivialTuple_empty]
  simp

/- English proof (translation)
Establish `hc : ∀ i, (Pr.vG i).Nonempty` using `fun i => by`. Rewrite using `[← Finset.card_pos, hPr.vG_card]`. Conclude with `hX.f_pos`. Take `⟨w1, h1⟩` from `hc 0`. Take `⟨w2, h2⟩` from `hc 1`.

Use `⟨w1, h1, w2, h2, fun h => hPr.g_ne ?_⟩` and prove the remaining obligations. Rewrite using `[← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h]`.
-/
theorem nz_two_primes (hX : X.Ok) (hPr : Pr.Ok) : ∃ w1 ∈ Pr.vG 0, ∃ w2 ∈ Pr.vG 1, w2 ≠ w1 := by
  have hc : ∀ i, (Pr.vG i).Nonempty := fun i => by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  obtain ⟨w1, h1⟩ := hc 0
  obtain ⟨w2, h2⟩ := hc 1
  refine ⟨w1, h1, w2, h2, fun h => hPr.g_ne ?_⟩
  rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h]

end Signs

section Final

/- English proof (translation)
Introduce `_ hM` and use `by obtain ⟨h1, h2⟩ := mem_HPar.mp hM exact mem_HPar.mpr ⟨h1, hH h2⟩`.
-/
theorem HPar_mono {κ : Type} [CommRing κ] {n r : ℕ} (h : r ≤ n) (bl : List ℕ) {H₀ H₁ : Subgroup (GL (Fin r) κ)} (hH : H₀ ≤ H₁) :
    HPar n κ h bl H₀ ≤ HPar n κ h bl H₁ := fun _ hM => by
  obtain ⟨h1, h2⟩ := mem_HPar.mp hM
  exact mem_HPar.mpr ⟨h1, hH h2⟩

/- English proof (translation)
Use `R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_r_pos (R : Ranks) : 0 < R.r := by
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

/- English proof (translation)
Establish `: NeZero (R.N R.m - 1)` using `⟨(X'_pos R).ne'⟩`. Take `⟨w1, h1, w2, h2, hne⟩` from `nz_two_primes hX hPr`. Establish `m1 : w1 ∈ Pr.vGs` using `Finset.mem_union_left _ h1`. Establish `m2 : w2 ∈ Pr.vGs` using `Finset.mem_union_right _ h2`. Set `W1 : rowSG Pr sel mu` to `⟨w1, Finset.mem_union_left _ m1⟩`.

Set `W2 : rowSG Pr sel mu` to `⟨w2, Finset.mem_union_left _ m2⟩`. Use `nz_form_pos (rowVal W _) (rowTy Ch sel mu P).inv (mtildeOk W Ch sel mu hX P) hX (posX R) (List.replicate R.m R.t) ⟨0, X'_pos R⟩ (nz_r_pos R) W1 W2 (fun h => hne (congrArg Subtype.val h)) (hPr.g_prime 0) (hPr.g_prime 1) (hPr.g_mem h1) (hPr.g_mem h2) (hg 0) (hg 1) ?_ ?_ (nzExt X.K …` and prove the remaining obligations. Use `show (rowTy Ch sel mu P W2).H ≤ _`. Rewrite using `[rowTy, LevFam.glue_of_mem _ _ W2 m2, uniUT_eq_HPar (r_le_X' R)]`. Conclude with `HPar_mono _ _ (hP _)`.

Use `show (rowTy Ch sel mu P W1).H ≤ _`. Rewrite using `[rowTy, LevFam.glue_of_mem _ _ W1 m1]`. Conclude with `HPar_le _ _ _`. Introduce `s γ hfix hco hγ show rhoV X.emb W.sgTrue (ufGL X.E _ γ) (nzExt X.K W.sgTrue) = _`. Rewrite using `[hγ]`.

Establish `hx : ∀ x, (posX R * s * (posX R)⁻¹) x = posX R (s ((posX R)⁻¹ x))` using `fun _ => rfl`. Establish `hx' : ∀ x, posX R ((posX R)⁻¹ x) = x` using `fun x => by simp`. Apply `nz_rhoV_perm` to reduce the goal to its premises. Introduce `τ x`. Rewrite using `[hx]`.

Distinguish the cases in `hb : ((posX R)⁻¹ x).val < R.r`. Rewrite using `[hfix _ hb, hx']`. Rewrite using `[nz_sg_const hW τ _ _ ((nz_ge_of_fix s hfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb) (hco _), hx']`. Introduce `x hne'`. Rewrite `hne'` using `[hx]`.

Establish `hb : ¬ ((posX R)⁻¹ x).val < R.r` using `fun hb => hne' (by rw [hfix _ hb, hx'])`. Use `hpar _ (Nat.not_lt.mp hb)` as an intermediate fact. Rewrite `this` using `[hx']`. Then use the resulting hypothesis. Introduce `s h hfix hco hh`. Take `⟨ε, hε⟩` from `nz_lamQ_ev (K := X.K) (a := R.r) (b := R.m * R.t) (le_of_eq (rank_X'_eq R)) s hfix`.

Establish `key : ∀ w : rowSG Pr sel mu, ((rowTy Ch sel mu P).inv w).ev (h.1 w) = if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε)`. Introduce `w`. Rewrite using `[hh w]`. Use `show ((rowTy Ch sel mu P w).inv).ev _ = _`. Rewrite using `[Lev.inv_ev]`.

Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Rewrite using `[if_pos hw, rowTy, LevFam.glue_of_mem _ _ w hw] show ((⟨HPar _ _ (r_le_X' R) (List.replicate R.m R.t) (P ⟨w.1, hw⟩).H, lamPar (r_le_X' R) (List.replicate R.m R.t) (P ⟨w.1, hw⟩).lam (chiAt Ch ⟨w.1, hw⟩)⟩ : Lev _ X.K _).ev _)⁻¹ = 1`. Rewrite using `[nz_lamPar_ev _ _ _ _ _ s hfix hco (nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩), inv_one]`. Rewrite using `[if_neg hw, rowTy, LevFam.glue_of_not _ _ w hw] show (((⟨HQ _ _ R.r (R.m * R.t), lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r (R.m * R.t)⟩ : Lev _ X.K _).inv).ev _)⁻¹ = _`. Rewrite using `[Lev.inv_ev, inv_inv, hε]`.

Rewrite using `[LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w]`. Conclude with `hξ.prod ε`.
-/
theorem mtilde_finrank_pos' (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (hpar : ∀ a : Fin (R.N R.m - 1), R.r ≤ a.val → Even (∑ τ, (W.sgTrue τ).w (posX R a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r) :
    0 < finrank X.K (MtildeV W Ch sel mu P) := by
  have : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩
  obtain ⟨w1, h1, w2, h2, hne⟩ := nz_two_primes hX hPr
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  refine nz_form_pos (rowVal W _) (rowTy Ch sel mu P).inv (mtildeOk W Ch sel mu hX P) hX (posX R) (List.replicate R.m R.t)
    ⟨0, X'_pos R⟩ (nz_r_pos R) W1 W2 (fun h => hne (congrArg Subtype.val h)) (hPr.g_prime 0) (hPr.g_prime 1) (hPr.g_mem h1)
    (hPr.g_mem h2) (hg 0) (hg 1) ?_ ?_ (nzExt X.K W.sgTrue) (nzExt_ne_zero _ _) ?_ ?_
  · show (rowTy Ch sel mu P W2).H ≤ _
    rw [rowTy, LevFam.glue_of_mem _ _ W2 m2, uniUT_eq_HPar (r_le_X' R)]
    exact HPar_mono _ _ (hP _)
  · show (rowTy Ch sel mu P W1).H ≤ _
    rw [rowTy, LevFam.glue_of_mem _ _ W1 m1]
    exact HPar_le _ _ _
  · intro s γ hfix hco hγ
    show rhoV X.emb W.sgTrue (ufGL X.E _ γ) (nzExt X.K W.sgTrue) = _
    rw [hγ]
    have hx : ∀ x, (posX R * s * (posX R)⁻¹) x = posX R (s ((posX R)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posX R ((posX R)⁻¹ x) = x := fun x => by simp
    apply nz_rhoV_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posX R)⁻¹ x).val < R.r
      · rw [hfix _ hb, hx']
      · rw [nz_sg_const hW τ _ _ ((nz_ge_of_fix s hfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb) (hco _), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posX R)⁻¹ x).val < R.r := fun hb => hne' (by rw [hfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro s h hfix hco hh
    obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.m * R.t) (le_of_eq (rank_X'_eq R)) s hfix
    have key : ∀ w : rowSG Pr sel mu, ((rowTy Ch sel mu P).inv w).ev (h.1 w) =
        if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε) := by
      intro w
      rw [hh w]
      show ((rowTy Ch sel mu P w).inv).ev _ = _
      rw [Lev.inv_ev]
      by_cases hw : w.1 ∈ Pr.vGs
      · rw [if_pos hw, rowTy, LevFam.glue_of_mem _ _ w hw]
        show ((⟨HPar _ _ (r_le_X' R) (List.replicate R.m R.t) (P ⟨w.1, hw⟩).H,
          lamPar (r_le_X' R) (List.replicate R.m R.t) (P ⟨w.1, hw⟩).lam (chiAt Ch ⟨w.1, hw⟩)⟩ : Lev _ X.K _).ev _)⁻¹ = 1
        rw [nz_lamPar_ev _ _ _ _ _ s hfix hco (nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩), inv_one]
      · rw [if_neg hw, rowTy, LevFam.glue_of_not _ _ w hw]
        show (((⟨HQ _ _ R.r (R.m * R.t), lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r (R.m * R.t)⟩ :
          Lev _ X.K _).inv).ev _)⁻¹ = _
        rw [Lev.inv_ev, inv_inv, hε]
    rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w]
    exact hξ.prod ε

open Classical in

/- English proof (translation)
Establish `: NeZero R.nV` using `⟨(nV_pos R).ne'⟩`. Take `⟨w1, h1, w2, h2, hne⟩` from `nz_two_primes hX hPr`. Establish `m1 : w1 ∈ Pr.vGs` using `Finset.mem_union_left _ h1`. Establish `m2 : w2 ∈ Pr.vGs` using `Finset.mem_union_right _ h2`. Set `W1 : rowSG Pr sel mu` to `⟨w1, Finset.mem_union_left _ m1⟩`.

Set `W2 : rowSG Pr sel mu` to `⟨w2, Finset.mem_union_left _ m2⟩`. Use `nz_form_pos (mtVal W j _) (mtTy Ch sel mu P j).inv (mtOk W Ch sel mu hX P j) hX (posV R j) [R.t] ⟨0, nV_pos R⟩ (nz_r_pos R) W1 W2 (fun h => hne (congrArg Subtype.val h)) (hPr.g_prime 0) (hPr.g_prime 1) (hPr.g_mem h1) (hPr.g_mem h2) (hg 0) (hg 1) ?_ ?_ (nzExt X.K (W.lamV j)) (nzEx …` and prove the remaining obligations. Use `show (mtTy Ch sel mu P j W2).H ≤ _`. Rewrite using `[mtTy, LevFam.glue_of_mem _ _ W2 m2, uniUT_eq_HPar (r_le_nV R)]`. Conclude with `HPar_mono _ _ (hP _)`.

Use `show (mtTy Ch sel mu P j W1).H ≤ _`. Rewrite using `[mtTy, LevFam.glue_of_mem _ _ W1 m1]`. Conclude with `HPar_le _ _ _`. Introduce `s γ hfix hco hγ show rhoVr X.emb (W.lamV j) (ufGL X.E _ γ) (nzExt X.K (W.lamV j)) = _`. Rewrite using `[hγ]`.

Establish `hx : ∀ x, (posV R j * s * (posV R j)⁻¹) x = posV R j (s ((posV R j)⁻¹ x))` using `fun _ => rfl`. Establish `hx' : ∀ x, posV R j ((posV R j)⁻¹ x) = x` using `fun x => by simp`. Apply `nz_rhoVr_perm` to reduce the goal to its premises. Introduce `τ x`. Rewrite using `[hx]`.

Distinguish the cases in `hb : ((posV R j)⁻¹ x).val < R.r`. Rewrite using `[hfix _ hb, hx']`. Rewrite using `[nz_lamV_const hW hj1 hj2 τ _ _ ((nz_ge_of_fix s hfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb), hx']`. Introduce `x hne'`. Rewrite `hne'` using `[hx]`.

Establish `hb : ¬ ((posV R j)⁻¹ x).val < R.r` using `fun hb => hne' (by rw [hfix _ hb, hx'])`. Use `hpar _ (Nat.not_lt.mp hb)` as an intermediate fact. Rewrite `this` using `[hx']`. Then use the resulting hypothesis. Introduce `s h hfix hco hh`. Take `⟨ε, hε⟩` from `nz_lamQ_ev (K := X.K) (a := R.r) (b := R.t) (le_refl R.nV) s hfix`.

Establish `key : ∀ w : rowSG Pr sel mu, ((mtTy Ch sel mu P j).inv w).ev (h.1 w) = (if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε))⁻¹`. Introduce `w`. Rewrite using `[hh w]`. Use `show ((mtTy Ch sel mu P j w).inv).ev _ = _`. Rewrite using `[Lev.inv_ev]`.

Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Rewrite using `[if_pos hw, mtTy, LevFam.glue_of_mem _ _ w hw] show (((⟨HPar _ _ (r_le_nV R) [R.t] (P ⟨w.1, hw⟩).H, lamPar (r_le_nV R) [R.t] (P ⟨w.1, hw⟩).lam fun _ => chiAt Ch ⟨w.1, hw⟩ (j - 1)⟩ : Lev _ X.K _).inv).ev _)⁻¹ = 1⁻¹`. Rewrite using `[Lev.inv_ev, nz_lamPar_ev _ _ _ _ _ s hfix hco (fun _ => nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩ (j - 1)), inv_one, inv_one]`. Rewrite using `[if_neg hw, mtTy, LevFam.glue_of_not _ _ w hw] show ((⟨HQ _ _ R.r R.t, lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r R.t⟩ : Lev _ X.K _).ev _)⁻¹ = _`. Rewrite using `[hε]`.

Rewrite using `[LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w, Finset.prod_inv_distrib, hξ.prod ε, inv_one]`.
-/
theorem mt_finrank_pos' (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m)
    (hpar : ∀ a : Fin R.nV, R.r ≤ a.val → Even (∑ τ, (W.lamV j τ).w (posV R j a))) :
    0 < finrank X.K (MtV W Ch sel mu P j) := by
  have : NeZero R.nV := ⟨(nV_pos R).ne'⟩
  obtain ⟨w1, h1, w2, h2, hne⟩ := nz_two_primes hX hPr
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  refine nz_form_pos (mtVal W j _) (mtTy Ch sel mu P j).inv (mtOk W Ch sel mu hX P j) hX (posV R j) [R.t]
    ⟨0, nV_pos R⟩ (nz_r_pos R) W1 W2 (fun h => hne (congrArg Subtype.val h)) (hPr.g_prime 0) (hPr.g_prime 1) (hPr.g_mem h1)
    (hPr.g_mem h2) (hg 0) (hg 1) ?_ ?_ (nzExt X.K (W.lamV j)) (nzExt_ne_zero _ _) ?_ ?_
  · show (mtTy Ch sel mu P j W2).H ≤ _
    rw [mtTy, LevFam.glue_of_mem _ _ W2 m2, uniUT_eq_HPar (r_le_nV R)]
    exact HPar_mono _ _ (hP _)
  · show (mtTy Ch sel mu P j W1).H ≤ _
    rw [mtTy, LevFam.glue_of_mem _ _ W1 m1]
    exact HPar_le _ _ _
  · intro s γ hfix hco hγ
    show rhoVr X.emb (W.lamV j) (ufGL X.E _ γ) (nzExt X.K (W.lamV j)) = _
    rw [hγ]
    have hx : ∀ x, (posV R j * s * (posV R j)⁻¹) x = posV R j (s ((posV R j)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posV R j ((posV R j)⁻¹ x) = x := fun x => by simp
    apply nz_rhoVr_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posV R j)⁻¹ x).val < R.r
      · rw [hfix _ hb, hx']
      · rw [nz_lamV_const hW hj1 hj2 τ _ _ ((nz_ge_of_fix s hfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posV R j)⁻¹ x).val < R.r := fun hb => hne' (by rw [hfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro s h hfix hco hh
    obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.t) (le_refl R.nV) s hfix
    have key : ∀ w : rowSG Pr sel mu, ((mtTy Ch sel mu P j).inv w).ev (h.1 w) =
        (if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε))⁻¹ := by
      intro w
      rw [hh w]
      show ((mtTy Ch sel mu P j w).inv).ev _ = _
      rw [Lev.inv_ev]
      by_cases hw : w.1 ∈ Pr.vGs
      · rw [if_pos hw, mtTy, LevFam.glue_of_mem _ _ w hw]
        show (((⟨HPar _ _ (r_le_nV R) [R.t] (P ⟨w.1, hw⟩).H,
          lamPar (r_le_nV R) [R.t] (P ⟨w.1, hw⟩).lam fun _ => chiAt Ch ⟨w.1, hw⟩ (j - 1)⟩ : Lev _ X.K _).inv).ev _)⁻¹ = 1⁻¹
        rw [Lev.inv_ev, nz_lamPar_ev _ _ _ _ _ s hfix hco (fun _ => nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩ (j - 1)), inv_one, inv_one]
      · rw [if_neg hw, mtTy, LevFam.glue_of_not _ _ w hw]
        show ((⟨HQ _ _ R.r R.t, lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r R.t⟩ : Lev _ X.K _).ev _)⁻¹ = _
        rw [hε]
    rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w, Finset.prod_inv_distrib, hξ.prod ε, inv_one]

/- English proof (translation)
The claim follows from `mtilde_finrank_pos' W Ch sel mu hX hPr hCh hW (fun a ha => nz_sg_even hW hf he a ha) hg hξ P hP`.
-/
theorem mtilde_finrank_pos (hX : X.Ok) (hf : Even X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ)) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r) :
    0 < finrank X.K (MtildeV W Ch sel mu P) :=
  mtilde_finrank_pos' W Ch sel mu hX hPr hCh hW (fun a ha => nz_sg_even hW hf he a ha) hg hξ P hP

/- English proof (translation)
The claim follows from `mt_finrank_pos' W Ch sel mu hX hPr hCh hW hg hξ P hP j hj1 hj2 (fun a ha => nz_lamV_even hW hf he hj1 hj2 a ha)`.
-/
theorem mt_finrank_pos (hX : X.Ok) (hf : Even X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ)) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m) : 0 < finrank X.K (MtV W Ch sel mu P j) :=
  mt_finrank_pos' W Ch sel mu hX hPr hCh hW hg hξ P hP j hj1 hj2 (fun a ha => nz_lamV_even hW hf he hj1 hj2 a ha)

/- English proof (translation)
Assemble the required witnesses or components as `⟨mtilde_finrank_pos W Ch sel mu hX hf hPr hCh hW he hg hξ P hP, fun j h1 h2 => mt_finrank_pos W Ch sel mu hX hf hPr hCh hW he hg hξ P hP j h1 h2⟩`.
-/
theorem rowsNonzero_of (hX : X.Ok) (hf : Even X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ)) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r) :
    RowsNonzero W Ch sel mu P :=
  ⟨mtilde_finrank_pos W Ch sel mu hX hf hPr hCh hW he hg hξ P hP,
    fun j h1 h2 => mt_finrank_pos W Ch sel mu hX hf hPr hCh hW he hg hξ P hP j h1 h2⟩

end Final

section Dat

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
The claim follows from `HPsym_le _ _ _ _`.
-/
theorem rPsym_le (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs}) : (rPsym (R := R) Ch w).H ≤ HU _ R.r := HPsym_le _ _ _ _

/- English proof (translation)
Establish `h1` using `h.g_big i`. Establish `h2 : 2 * X.f * 1 ≤ 2 * X.f * R.k` using `Nat.mul_le_mul_left _ (by have := R.m_add_three_le_k; omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem Sizes.g_gt {W : Wts X Pr.Word R} {a : ℝ} (h : Sizes Pr W a) (i : Fin 2) : 2 * X.f + 1 < Pr.g i := by
  have h1 := h.g_big i
  have h2 : 2 * X.f * 1 ≤ 2 * X.f * R.k := Nat.mul_le_mul_left _ (by have := R.m_add_three_le_k; omega)
  omega

/- English proof (translation)
The claim follows from `rowsNonzero_of D.W D.Ch sel mu hD.fields hD.fieldsConditions.f_even hD.primes hD.chars hD.wts hD.e_even hD.sizes.g_gt hξ P hP`.
-/
theorem Dat.Ok.rowsNonzero {D : Dat} (hD : D.Ok) (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) {S : Set ℕ}
    (mu : Tup D.X.F D.X.E D.X.K S) (hξ : XiSign D.Pr sel (mu : Chr D.X.F D.X.E D.X.K))
    (P : LevFam D.X.E D.X.K D.R.r D.Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ D.R.r) : RowsNonzero D.W D.Ch sel mu P :=
  rowsNonzero_of D.W D.Ch sel mu hD.fields hD.fieldsConditions.f_even hD.primes hD.chars hD.wts hD.e_even hD.sizes.g_gt hξ P hP

end Dat

end Formalism.L2.Col
