import Mathlib
import Formalism.HermitianLattices.DefsCS
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusScale
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.FockGram.FockGramProofs.CovolGram

open Module NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section PartS

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem genusCovol_mem_locS (S : Submonoid R) (L : Submodule R W) (x : W) :
    x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := Iff.rfl

/- English proof (translation)
Introduce `x hx` and use `⟨1, S.one_mem, by simpa using hx⟩`.
-/
theorem genusCovol_le_locS (S : Submonoid R) (L : Submodule R W) : L ≤ locS S L :=
  fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

/- English proof (translation)
Introduce `_ ⟨s, hs, hx⟩` and use `⟨s, hs, h hx⟩`.
-/
theorem genusCovol_locS_mono (S : Submonoid R) {L M : Submodule R W} (h : L ≤ M) :
    locS S L ≤ locS S M := fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, t, ht, hx⟩`. Use `⟨t * s, S.mul_mem ht hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]` and apply the resulting hypothesis.
-/
theorem genusCovol_locS_idem (S : Submonoid R) (L : Submodule R W) :
    locS S (locS S L) ≤ locS S L := by
  rintro x ⟨s, hs, t, ht, hx⟩
  refine ⟨t * s, S.mul_mem ht hs, ?_⟩
  rwa [mul_smul]

/- English proof (translation)
Introduce `y hy`. Set `I : Ideal R` to `X.comap (LinearMap.toSpanSingleton R W y)`. Distinguish the cases in `hI : I = ⊤`. Establish `: (1 : R) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify `this` using `[I]`.

Take `⟨P, hP, hIP⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨s, hs, hsy⟩` from `h P hy`. Conclude with `absurd (hIP (show s ∈ I by simpa [I] using hsy)) hs`.
-/
theorem genusCovol_le_of_loc {Y X : Submodule R W}
    (h : ∀ (P : Ideal R) [P.IsMaximal], Y ≤ locS P.primeCompl X) : Y ≤ X := by
  intro y hy
  let I : Ideal R := X.comap (LinearMap.toSpanSingleton R W y)
  by_cases hI : I = ⊤
  · have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using this
  · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨s, hs, hsy⟩ := h P hy
    exact absurd (hIP (show s ∈ I by simpa [I] using hsy)) hs

/- English proof (translation)
Establish `: (X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup).FiniteIndex` using `⟨hfin⟩`. Establish `: Finite (Y.toAddSubgroup ⧸ X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Set `f : ℕ → Y.toAddSubgroup ⧸ X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup` to `fun n => QuotientAddGroup.mk (⟨r ^ n • z, Y.smul_mem _ hz⟩ : Y.toAddSubgroup)`. Take `⟨a, b, hab, hf⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Establish `key : ∀ a b : ℕ, f a = f b → r ^ a • z - r ^ b • z ∈ X`.

Introduce `a b e`. Use `(QuotientAddGroup.eq).mp e` as an intermediate fact. Rewrite `this` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `h2 : -(r ^ a • z) + r ^ b • z ∈ X` using `this`. Establish `h3` using `X.neg_mem h2`.

Simplify `h3` using `[sub_eq_add_neg, add_comm]`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Use `⟨a, b - a, Nat.sub_pos_of_lt h, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel' h.le]`. Conclude with `key a b hf`.

Use `⟨b, a - b, Nat.sub_pos_of_lt h, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel' h.le]`. Conclude with `key b a hf.symm`.
-/
theorem genusCovol_pigeon {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (r : R) {z : W} (hz : z ∈ Y) :
    ∃ m k : ℕ, 0 < k ∧ r ^ m • z - r ^ (m + k) • z ∈ X := by
  classical
  have : (X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup).FiniteIndex := ⟨hfin⟩
  have : Finite (Y.toAddSubgroup ⧸ X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  let f : ℕ → Y.toAddSubgroup ⧸ X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup :=
    fun n => QuotientAddGroup.mk (⟨r ^ n • z, Y.smul_mem _ hz⟩ : Y.toAddSubgroup)
  obtain ⟨a, b, hab, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, f a = f b → r ^ a • z - r ^ b • z ∈ X := by
    intro a b e
    have := (QuotientAddGroup.eq).mp e
    rw [AddSubgroup.mem_addSubgroupOf] at this
    have h2 : -(r ^ a • z) + r ^ b • z ∈ X := this
    have h3 := X.neg_mem h2
    simpa [sub_eq_add_neg, add_comm] using h3
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, Nat.sub_pos_of_lt h, ?_⟩
    rw [Nat.add_sub_cancel' h.le]
    exact key a b hf
  · refine ⟨b, a - b, Nat.sub_pos_of_lt h, ?_⟩
    rw [Nat.add_sub_cancel' h.le]
    exact key b a hf.symm

/- English proof (translation)
Introduce and unpack `y ⟨s, hs, hsy⟩`. Take `⟨m, k, hk, hmk⟩` from `genusCovol_pigeon hfin s hsy`. Establish `hb : s ^ k • y ∈ Y`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[pow_succ, mul_smul]`.

Conclude with `Y.smul_mem _ hsy`. Establish `hr : y - s ^ k • y ∈ locS S X`. Use `⟨s ^ (m + 1), S.pow_mem hs _, ?_⟩` and prove the remaining obligations. Establish `e : s ^ (m + 1) • (y - s ^ k • y) = s ^ m • (s • y) - s ^ (m + k) • (s • y)`. Rewrite using `[smul_sub, smul_smul, smul_smul, smul_smul, ← pow_succ, ← pow_succ, ← pow_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hmk`. Establish `: y = s ^ k • y + (y - s ^ k • y)` using `by abel`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hb hr`.
-/
theorem genusCovol_claimA (S : Submonoid R) {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    locS S Y ≤ Y ⊔ locS S X := by
  rintro y ⟨s, hs, hsy⟩
  obtain ⟨m, k, hk, hmk⟩ := genusCovol_pigeon hfin s hsy
  have hb : s ^ k • y ∈ Y := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, mul_smul]
    exact Y.smul_mem _ hsy
  have hr : y - s ^ k • y ∈ locS S X := by
    refine ⟨s ^ (m + 1), S.pow_mem hs _, ?_⟩
    have e : s ^ (m + 1) • (y - s ^ k • y) = s ^ m • (s • y) - s ^ (m + k) • (s • y) := by
      rw [smul_sub, smul_smul, smul_smul, smul_smul, ← pow_succ, ← pow_succ, ← pow_add]
      congr 2
      ring
    rw [e]
    exact hmk
  have : y = s ^ k • y + (y - s ^ k • y) := by abel
  rw [this]
  exact Submodule.add_mem_sup hb hr

/- English proof (translation)
Introduce and unpack `y' ⟨t, ht, hty⟩`. Take `⟨m, k, hk, hmk⟩` from `genusCovol_pigeon hfin a hty`. Use `⟨a ^ m * t, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Break down `(Ideal.IsPrime.mem_or_mem inferInstance hmem) with h1 | h1` into its components or cases.

Conclude with `haQ (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h1)`. Conclude with `ht h1`. Rewrite using `[mul_smul]`. Conclude with `Y.smul_mem _ hty`. Use `⟨1 - a ^ k, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hmem`. Establish `h1 : a ^ k ∈ P` using `P.pow_mem_of_mem haP k hk`. Establish `: (1 : R) ∈ P` using `by simpa using P.add_mem hmem h1`. Conclude with `(Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).mpr this)`. Establish `e : (1 - a ^ k) • (a ^ m * t) • y' = a ^ m • (t • y') - a ^ (m + k) • (t • y')`.

Rewrite using `[sub_smul, one_smul, smul_smul, smul_smul, smul_smul, pow_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hmk`.
-/
theorem genusCovol_claimB (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] {a : R} (haP : a ∈ P)
    (haQ : a ∉ Q) {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    locS Q.primeCompl Y ≤ locS Q.primeCompl (Y ⊓ locS P.primeCompl X) := by
  rintro y' ⟨t, ht, hty⟩
  obtain ⟨m, k, hk, hmk⟩ := genusCovol_pigeon hfin a hty
  refine ⟨a ^ m * t, ?_, ?_, ?_⟩
  · intro hmem
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hmem) with h1 | h1
    · exact haQ (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h1)
    · exact ht h1
  · rw [mul_smul]
    exact Y.smul_mem _ hty
  · refine ⟨1 - a ^ k, ?_, ?_⟩
    · intro hmem
      have h1 : a ^ k ∈ P := P.pow_mem_of_mem haP k hk
      have : (1 : R) ∈ P := by simpa using P.add_mem hmem h1
      exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).mpr this)
    · have e : (1 - a ^ k) • (a ^ m * t) • y' = a ^ m • (t • y') - a ^ (m + k) • (t • y') := by
        rw [sub_smul, one_smul, smul_smul, smul_smul, smul_smul, pow_add]
        congr 2
        ring
      rw [e]
      exact hmk

/- English proof (translation)
Establish `e : locS S Y = locS S X ⊔ Y` using `le_antisymm (by rw [sup_comm]; exact genusCovol_claimA S hfin) (sup_le (genusCovol_locS_mono S hXY) (genusCovol_le_locS S Y))`. Rewrite using `[e, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right (locS S X).toAddSubgroup, inf_comm]`. Both sides reduce to the same expression.
-/
theorem genusCovol_ri_peel (S : Submonoid R) {X Y : Submodule R W} (hXY : X ≤ Y)
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    (Y ⊓ locS S X).toAddSubgroup.relIndex Y.toAddSubgroup =
      (locS S X).toAddSubgroup.relIndex (locS S Y).toAddSubgroup := by
  have e : locS S Y = locS S X ⊔ Y :=
    le_antisymm (by rw [sup_comm]; exact genusCovol_claimA S hfin)
      (sup_le (genusCovol_locS_mono S hXY) (genusCovol_le_locS S Y))
  rw [e, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left,
    ← AddSubgroup.inf_relIndex_right (locS S X).toAddSubgroup, inf_comm]
  rfl

/- English proof (translation)
The claim follows from `le_antisymm ((genusCovol_locS_mono S h2).trans (genusCovol_locS_idem S X)) (genusCovol_locS_mono S h1)`.
-/
theorem genusCovol_loc_eq_of_le_of_le (S : Submonoid R) {X Z : Submodule R W} (h1 : X ≤ Z)
    (h2 : Z ≤ locS S X) : locS S Z = locS S X :=
  le_antisymm ((genusCovol_locS_mono S h2).trans (genusCovol_locS_idem S X))
    (genusCovol_locS_mono S h1)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `X Y X' Y' hXY hXY' hn hn0 hfin' hloc`. Establish `hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0` using `hn ▸ hn0`.

Distinguish the cases in `hall : ∀ (P : Ideal R) [P.IsMaximal], Y ≤ locS P.primeCompl X`. Establish `h1 : Y ≤ X` using `genusCovol_le_of_loc hall`. Establish `h1' : Y' ≤ X'`. Apply `genusCovol_le_of_loc` to reduce the goal to its premises. Introduce `P _`.

Take `⟨f, _, hfX, hfY⟩` from `hloc P`. Establish `hYX : locS P.primeCompl Y ≤ locS P.primeCompl X` using `(genusCovol_locS_mono _ (hall P)).trans (genusCovol_locS_idem _ X)`. Establish `: (locS P.primeCompl Y').toAddSubgroup ≤ (locS P.primeCompl X').toAddSubgroup`. Rewrite using `[← hfX, ← hfY]`. Conclude with `AddSubgroup.map_mono ((Submodule.toAddSubgroup_le _ _).mpr hYX)`.

Conclude with `(genusCovol_le_locS _ Y').trans ((Submodule.toAddSubgroup_le _ _).mp this)`. Rewrite using `[← hn, AddSubgroup.relIndex_eq_one.mpr ((Submodule.toAddSubgroup_le _ _).mpr h1), AddSubgroup.relIndex_eq_one.mpr ((Submodule.toAddSubgroup_le _ _).mpr h1')]`. Use `push Not at hall`. Take `⟨P, hP, hY⟩` from `hall`. Take `⟨f, hfi, hfX, hfY⟩` from `hloc P`.

Use `set Z := Y ⊓ locS P.primeCompl X with hZ`. Use `set Z' := Y' ⊓ locS P.primeCompl X' with hZ'`. Establish `hXZ : X ≤ Z` using `le_inf hXY (genusCovol_le_locS _ X)`. Establish `hXZ' : X' ≤ Z'` using `le_inf hXY' (genusCovol_le_locS _ X')`. Establish `hm` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXZ) ((Submodule.toAddSubgroup_le _ _).mpr (inf_le_left : Z ≤ Y))`.

Establish `hm'` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXZ') ((Submodule.toAddSubgroup_le _ _).mpr (inf_le_left : Z' ≤ Y'))`. Establish `hp` using `genusCovol_ri_peel P.primeCompl hXY hfin`. Establish `hp'` using `genusCovol_ri_peel P.primeCompl hXY' hfin'`. Rewrite `hp'` using `[← hfX, ← hfY, AddSubgroup.relIndex_map_map_of_injective _ _ hfi]`. Establish `hne1 : Z.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 1`.

Introduce `h`. Conclude with `hY (((Submodule.toAddSubgroup_le _ _).mp (AddSubgroup.relIndex_eq_one.mp h)).trans inf_le_right)`. Establish `hlt : X.toAddSubgroup.relIndex Z.toAddSubgroup < n`. Rewrite using `[← hn, ← hm]`. Establish `h0 : X.toAddSubgroup.relIndex Z.toAddSubgroup ≠ 0`.

Introduce `h`. Rewrite `hfin` using `[← hm, h, zero_mul]`. Conclude with `hfin rfl`. Establish `h2 : Z.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0`. Introduce `h`.

Rewrite `hfin` using `[← hm, h, mul_zero]`. Conclude with `hfin rfl`. Establish `: 2 ≤ Z.toAddSubgroup.relIndex Y.toAddSubgroup` using `by omega`. Establish `h4` using `Nat.pos_of_ne_zero h0`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hfinZ' : X'.toAddSubgroup.relIndex Z'.toAddSubgroup ≠ 0`. Introduce `h`. Rewrite `hfin'` using `[← hm', h, zero_mul]`. Conclude with `hfin' rfl`. Establish `hIH` using `ih _ hlt X Z X' Z' hXZ hXZ' rfl (by intro h; rw [← hm, h, zero_mul] at hfin; exact hfin rfl) hfinZ' (by`.

Introduce `Q _`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Use `⟨f, hfi, hfX, ?_⟩` and prove the remaining obligations. Rewrite using `[genusCovol_loc_eq_of_le_of_le _ hXZ inf_le_right, genusCovol_loc_eq_of_le_of_le _ hXZ' inf_le_right, hfX]`.

Take `⟨g, hgi, hgX, hgY⟩` from `hloc Q`. Establish `hPQ : ¬ P ≤ Q` using `fun h => hQ ((Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsMaximal.ne_top inferInstance) h).symm)`. Take `⟨a, haP, haQ⟩` from `Set.not_subset.mp hPQ`. Establish `e1 : locS Q.primeCompl Z = locS Q.primeCompl Y` using `le_antisymm (genusCovol_locS_mono _ inf_le_left) (genusCovol_claimB P Q haP haQ hfin)`. Establish `e2 : locS Q.primeCompl Z' = locS Q.primeCompl Y'` using `le_antisymm (genusCovol_locS_mono _ inf_le_left) (genusCovol_claimB P Q haP haQ hfin')`.

Conclude with `⟨g, hgi, hgX, by rw [e1, e2, hgY]⟩)`. Rewrite using `[← hm', hIH, hp', ← hp, hm, hn]`.
-/
theorem genusCovol_lemmaS : ∀ (n : ℕ) (X Y X' Y' : Submodule R W), X ≤ Y → X' ≤ Y' →
    X.toAddSubgroup.relIndex Y.toAddSubgroup = n → n ≠ 0 →
    X'.toAddSubgroup.relIndex Y'.toAddSubgroup ≠ 0 →
    (∀ (P : Ideal R) [P.IsMaximal], ∃ f : W →+ W, Function.Injective f ∧
      (locS P.primeCompl X).toAddSubgroup.map f = (locS P.primeCompl X').toAddSubgroup ∧
      (locS P.primeCompl Y).toAddSubgroup.map f = (locS P.primeCompl Y').toAddSubgroup) →
    X'.toAddSubgroup.relIndex Y'.toAddSubgroup = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y X' Y' hXY hXY' hn hn0 hfin' hloc
  have hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := hn ▸ hn0
  by_cases hall : ∀ (P : Ideal R) [P.IsMaximal], Y ≤ locS P.primeCompl X
  · have h1 : Y ≤ X := genusCovol_le_of_loc hall
    have h1' : Y' ≤ X' := by
      apply genusCovol_le_of_loc
      intro P _
      obtain ⟨f, _, hfX, hfY⟩ := hloc P
      have hYX : locS P.primeCompl Y ≤ locS P.primeCompl X :=
        (genusCovol_locS_mono _ (hall P)).trans (genusCovol_locS_idem _ X)
      have : (locS P.primeCompl Y').toAddSubgroup ≤ (locS P.primeCompl X').toAddSubgroup := by
        rw [← hfX, ← hfY]
        exact AddSubgroup.map_mono ((Submodule.toAddSubgroup_le _ _).mpr hYX)
      exact (genusCovol_le_locS _ Y').trans ((Submodule.toAddSubgroup_le _ _).mp this)
    rw [← hn, AddSubgroup.relIndex_eq_one.mpr ((Submodule.toAddSubgroup_le _ _).mpr h1),
      AddSubgroup.relIndex_eq_one.mpr ((Submodule.toAddSubgroup_le _ _).mpr h1')]
  · push Not at hall
    obtain ⟨P, hP, hY⟩ := hall
    obtain ⟨f, hfi, hfX, hfY⟩ := hloc P
    set Z := Y ⊓ locS P.primeCompl X with hZ
    set Z' := Y' ⊓ locS P.primeCompl X' with hZ'
    have hXZ : X ≤ Z := le_inf hXY (genusCovol_le_locS _ X)
    have hXZ' : X' ≤ Z' := le_inf hXY' (genusCovol_le_locS _ X')
    have hm := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXZ)
      ((Submodule.toAddSubgroup_le _ _).mpr (inf_le_left : Z ≤ Y))
    have hm' := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXZ')
      ((Submodule.toAddSubgroup_le _ _).mpr (inf_le_left : Z' ≤ Y'))
    have hp := genusCovol_ri_peel P.primeCompl hXY hfin
    have hp' := genusCovol_ri_peel P.primeCompl hXY' hfin'
    rw [← hfX, ← hfY, AddSubgroup.relIndex_map_map_of_injective _ _ hfi] at hp'
    have hne1 : Z.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 1 := by
      intro h
      exact hY (((Submodule.toAddSubgroup_le _ _).mp (AddSubgroup.relIndex_eq_one.mp h)).trans
        inf_le_right)
    have hlt : X.toAddSubgroup.relIndex Z.toAddSubgroup < n := by
      rw [← hn, ← hm]
      have h0 : X.toAddSubgroup.relIndex Z.toAddSubgroup ≠ 0 := by
        intro h; rw [← hm, h, zero_mul] at hfin; exact hfin rfl
      have h2 : Z.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
        intro h; rw [← hm, h, mul_zero] at hfin; exact hfin rfl
      have : 2 ≤ Z.toAddSubgroup.relIndex Y.toAddSubgroup := by omega
      have h4 := Nat.pos_of_ne_zero h0
      nlinarith
    have hfinZ' : X'.toAddSubgroup.relIndex Z'.toAddSubgroup ≠ 0 := by
      intro h; rw [← hm', h, zero_mul] at hfin'; exact hfin' rfl
    have hIH := ih _ hlt X Z X' Z' hXZ hXZ' rfl
      (by intro h; rw [← hm, h, zero_mul] at hfin; exact hfin rfl) hfinZ' (by
        intro Q _
        by_cases hQ : Q = P
        · subst hQ
          refine ⟨f, hfi, hfX, ?_⟩
          rw [genusCovol_loc_eq_of_le_of_le _ hXZ inf_le_right,
            genusCovol_loc_eq_of_le_of_le _ hXZ' inf_le_right, hfX]
        · obtain ⟨g, hgi, hgX, hgY⟩ := hloc Q
          have hPQ : ¬ P ≤ Q := fun h =>
            hQ ((Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsMaximal.ne_top inferInstance) h).symm)
          obtain ⟨a, haP, haQ⟩ := Set.not_subset.mp hPQ
          have e1 : locS Q.primeCompl Z = locS Q.primeCompl Y :=
            le_antisymm (genusCovol_locS_mono _ inf_le_left) (genusCovol_claimB P Q haP haQ hfin)
          have e2 : locS Q.primeCompl Z' = locS Q.primeCompl Y' :=
            le_antisymm (genusCovol_locS_mono _ inf_le_left) (genusCovol_claimB P Q haP haQ hfin')
          exact ⟨g, hgi, hgX, by rw [e1, e2, hgY]⟩)
    rw [← hm', hIH, hp', ← hp, hm, hn]

end PartS

section PartT

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_algebraMap_ringOfIntegers_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
The claim follows from `FaithfulSMul.algebraMap_injective _ _`.
-/
theorem genusCovol_hinj : Function.Injective (algebraMap (𝓞 K) K) :=
  FaithfulSMul.algebraMap_injective _ _

def genusCovol_tdual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {y | ∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [map_add, map_add, h1, h2]; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro r y hy x hx
    obtain ⟨z, hz⟩ := hy (locBasic_sigma genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r • x)
      (L.smul_mem _ hx)
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right,
      locBasic_sigma_spec, locBasic_sigma_spec, star_star]

/- English proof (translation)
The claim follows from `le_antisymm ((genusCovol_locS_mono T (locBasic_locS_le_of_le hST Z)).trans (genusCovol_locS_idem T Z)) (genusCovol_locS_mono T (genusCovol_le_locS S Z))`.
-/
theorem genusCovol_locS_locS {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {S T : Submonoid R} (hST : S ≤ T) (Z : Submodule R W) : locS T (locS S Z) = locS T Z :=
  le_antisymm ((genusCovol_locS_mono T (locBasic_locS_le_of_le hST Z)).trans
    (genusCovol_locS_idem T Z)) (genusCovol_locS_mono T (genusCovol_le_locS S Z))

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[isomAct_mem_gmap, isomAct_mem_locS, isomAct_mem_locS]`. Simplify using `only [isomAct_mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`.

Conclude with `⟨s, hs, by rw [isomAct_smul]; exact hx⟩`. Introduce and unpack `⟨s, hs, hx⟩`. Conclude with `⟨s, hs, by rw [← isomAct_smul]; exact hx⟩`.
-/
theorem gmap_locS_comm (g : V ≃ₗ[K] V) (S : Submonoid (𝓞 K)) (Z : Submodule (𝓞 K) V) :
    gmap g (locS S Z) = locS S (gmap g Z) := by
  ext x
  rw [isomAct_mem_gmap, isomAct_mem_locS, isomAct_mem_locS]
  simp only [isomAct_mem_gmap]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [isomAct_smul]; exact hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← isomAct_smul]; exact hx⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [isomAct_mem_gmap, Submodule.mem_inf]`.
-/
theorem genusCovol_gmap_inf (g : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    gmap g (A ⊓ B) = gmap g A ⊓ gmap g B := by
  ext x
  simp only [isomAct_mem_gmap, Submodule.mem_inf]

/- English proof (translation)
Use `genusBasic_gmap_inv g⁻¹ Z` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem genusCovol_gmap_gmap_inv (g : V ≃ₗ[K] V) (Z : Submodule (𝓞 K) V) :
    gmap g (gmap g⁻¹ Z) = Z := by
  have := genusBasic_gmap_inv g⁻¹ Z
  rwa [inv_inv] at this

/- English proof (translation)
Establish `hg' : ∀ x y, h (g x) (g y) = h x y` using `hg`. Take `⟨F, hF⟩` from `hM`. Establish `hgen : ∀ m ∈ F, ∃ t ∈ hcompl (K` using `K) P, t • g.symm m ∈ L := by`. Introduce `m hm`. Establish `: m ∈ gmap g (loc (K` using `K) P L) := hML (hF ▸ Submodule.subset_span hm)`.

Rewrite `this` using `[isomAct_mem_gmap]`. Conclude with `this`. Use `choose! t ht htL using hgen`. Use `set T := ∏ m ∈ F, t m with hT`. Establish `hTmem : T ∈ hcompl (K` using `K) P := Submonoid.prod_mem _ (fun m hm => ht m hm)`.

Set `f : V →ₗ[𝓞 K] V` to `T • (g.symm : V →ₗ[K] V).restrictScalars (𝓞 K)`. Establish `hMf : M ≤ L.comap f`. Rewrite using `[← hF, Submodule.span_le]`. Introduce `m hm`. Express the relevant statement in the definitionally equal form `T • g.symm m ∈ L`.

Rewrite using `[hT, ← Finset.mul_prod_erase F t hm, mul_comm, mul_smul]`. Conclude with `L.smul_mem _ (htL m hm)`. Introduce `x hx`. Rewrite `hx` using `[isomAct_mem_gmap]`. Take `⟨s, hs, hsx⟩` from `hx`.

Use `set σT := locBasic_sigma genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range T with hσT`. Establish `hσmem : σT ∈ hcompl (K` using `K) P := genusBasic_sigma_mem genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range P T hTmem`. Use `⟨σT * s, P.primeCompl.mul_mem (locBasic_hcompl_le (K := K) P hσmem) hs, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Take `⟨z, hz⟩` from `hsx (T • g.symm m) (hMf hm)`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz]`. Use `congr 1`. Rewrite using `[genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right, genusBasic_hsmul_right, ← hg' (g.symm m) (g.symm x), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_mul, mul_assoc]`.
-/
theorem genus_covolume_local_dual_le (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (P : Ideal (𝓞 K)) [P.IsPrime] (L M : Submodule (𝓞 K) V) (hM : M.FG)
    (hML : M ≤ gmap g (loc (K := K) P L)) :
    gmap g (locS P.primeCompl (genusCovol_tdual h L)) ≤
      locS P.primeCompl (genusCovol_tdual h M) := by
  classical
  have hg' : ∀ x y, h (g x) (g y) = h x y := hg
  obtain ⟨F, hF⟩ := hM
  have hgen : ∀ m ∈ F, ∃ t ∈ hcompl (K := K) P, t • g.symm m ∈ L := by
    intro m hm
    have : m ∈ gmap g (loc (K := K) P L) := hML (hF ▸ Submodule.subset_span hm)
    rw [isomAct_mem_gmap] at this
    exact this
  choose! t ht htL using hgen
  set T := ∏ m ∈ F, t m with hT
  have hTmem : T ∈ hcompl (K := K) P := Submonoid.prod_mem _ (fun m hm => ht m hm)
  let f : V →ₗ[𝓞 K] V := T • (g.symm : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hMf : M ≤ L.comap f := by
    rw [← hF, Submodule.span_le]
    intro m hm
    change T • g.symm m ∈ L
    rw [hT, ← Finset.mul_prod_erase F t hm, mul_comm, mul_smul]
    exact L.smul_mem _ (htL m hm)
  intro x hx
  rw [isomAct_mem_gmap] at hx
  obtain ⟨s, hs, hsx⟩ := hx
  set σT := locBasic_sigma genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range T with hσT
  have hσmem : σT ∈ hcompl (K := K) P := genusBasic_sigma_mem genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range P T hTmem
  refine ⟨σT * s, P.primeCompl.mul_mem (locBasic_hcompl_le (K := K) P hσmem) hs, ?_⟩
  intro m hm
  obtain ⟨z, hz⟩ := hsx (T • g.symm m) (hMf hm)
  refine ⟨z, ?_⟩
  rw [← hz]
  congr 1
  rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right,
    genusBasic_hsmul_right, ← hg' (g.symm m) (g.symm x), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, map_mul, mul_assoc]

end PartT

section PartE

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `set Λ := zmap ι M with hΛ`. Set `bz` to `Module.Free.chooseBasis ℤ Λ`. Set `bR` to `bz.ofZLatticeBasis ℝ Λ`. Establish `hmem : ∀ i, ∃ m ∈ M, ι m = (bz i : EuclideanSpace ℝ (Fin N))` using `fun i => (genusCovolBound_mem_zmap N ι M _).mp (bz i).2`. Use `choose m hmM hmι using hmem`.

Use `set b : V → V → ℚ := fun x y => Algebra.trace ℚ K (h x y) with hbdef`. Establish `hb : ∀ x y, ((b x y : ℚ) : ℝ) = inner ℝ (ι x) (ι y)` using `fun x y => (hι x y).symm`. Establish `hsymm : ∀ x y, b x y = b y x` using `fun x y => by`. Establish `e` using `hb x y`. Rewrite `e` using `[real_inner_comm, ← hb]`.

Conclude with `e` after adjusting the coercions. Use `set G : Matrix (Module.Free.ChooseBasisIndex ℤ Λ) (Module.Free.ChooseBasisIndex ℤ Λ) ℚ := Matrix.of fun i j => b (m i) (m j) with hG`. Establish `hgram : Matrix.gram ℝ bR = (Rat.castHom ℝ).mapMatrix G`. Use extensionality with `i j`. Simplify using `only [Matrix.gram_apply, bR, Basis.ofZLatticeBasis_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hG, Matrix.of_apply, ← hmι]`.

Conclude with `(hb _ _).symm`. Establish `hcov : ZLattice.covolume Λ = Real.sqrt ((G.det : ℚ) : ℝ)`. Establish `e` using `Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) _ bR`. Rewrite `e` using `[Basis.ofZLatticeBasis_span]`. Rewrite using `[e, hgram, ← RingHom.map_det]`.

Both sides reduce to the same expression. Establish `hdetpos : 0 < G.det`. Use `ZLattice.covolume_pos Λ` as an intermediate fact. Rewrite `this` using `[hcov, Real.sqrt_pos]`. Conclude with `this` after adjusting the coercions.

Establish `hGsymm : G.transpose = G`. Use extensionality with `i j`. Simplify using `[hG, hsymm (m j) (m i)]`. Establish `hGunit : IsUnit G.det` using `(ne_of_gt hdetpos).isUnit`. Use `set Gi := G⁻¹ with hGi`.

Establish `hGiT : Gi.transpose = Gi` using `by rw [hGi, Matrix.transpose_nonsing_inv, hGsymm]`. Establish `hGisymm : ∀ i j, Gi i j = Gi j i`. Introduce `i j`. Use `conv_lhs => rw [← hGiT]`. Both sides reduce to the same expression.

Use `set y : Module.Free.ChooseBasisIndex ℤ Λ → V := fun i => ∑ j, (algebraMap ℚ K (Gi i j)) • m j with hy`. Establish `hlin : ∀ x i, b x (y i) = ∑ j, Gi i j * b x (m j)`. Introduce `x i`. Simplify using `only [hbdef, hy]`. Rewrite using `[map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`. Establish `hdelta : ∀ k i, b (m k) (y i) = (1 : Matrix _ _ ℚ) k i`. Introduce `k i`. Rewrite using `[hlin]`.

Establish `e : (G * Gi) k i = (1 : Matrix _ _ ℚ) k i` using `by rw [hGi, Matrix.mul_nonsing_inv _ hGunit]`. Rewrite using `[← e, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hGisymm i j, mul_comm]`. Both sides reduce to the same expression.

Establish `hint : ∀ i, ∀ x ∈ M, ∃ z : ℤ, b x (y i) = z`. Introduce `i x hx`. Establish `hxΛ : ι x ∈ Λ` using `(genusCovolBound_mem_zmap N ι M _).mpr ⟨x, hx, rfl⟩`. Take `⟨c, hc⟩ : ∃ c, c = bz.repr ⟨ι x, hxΛ⟩` from `⟨_, rfl⟩`. Use `⟨c i, ?_⟩` and prove the remaining obligations.

Establish `hsum : ι x = ∑ k, ((c k : ℤ) : ℝ) • bR k` using `by conv_lhs => rw [← bR.sum_repr (ι x)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `Basis.ofZLatticeBasis_repr_apply ℝ Λ bz ⟨ι x, hxΛ⟩ k` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this, hc]`.

Establish `e : ((b x (y i) : ℚ) : ℝ) = (((c i : ℤ) : ℚ) : ℝ)`. Rewrite using `[hb, hsum, sum_inner]`. Repeatedly rewrite using `[real_inner_smul_left, bR, Basis.ofZLatticeBasis_apply, ← hmι, ← hb, hdelta]`. Rewrite using `[Finset.sum_eq_single i (fun k _ hk => by simp [Matrix.one_apply, hk]) (by simp)]`. Simplify using `[Matrix.one_apply]`.

Conclude with `e` after adjusting the coercions. Establish `hyy : ∀ i j, b (y i) (y j) = Gi j i`. Introduce `i j`. Rewrite using `[hlin]`. Establish `e : ∀ l, Gi j l * b (y i) (m l) = Gi j l * (1 : Matrix _ _ ℚ) l i`.

Introduce `l`. Rewrite using `[hsymm (y i) (m l), hdelta]`. Rewrite using `[Finset.sum_congr rfl fun l _ => e l]`. Simplify using `[Matrix.one_apply]`. Use `set v : Module.Free.ChooseBasisIndex ℤ Λ → EuclideanSpace ℝ (Fin N) := fun i => ι (y i) with hv`.

Establish `hRdelta : ∀ k i, inner ℝ (bR k) (v i) = if k = i then (1 : ℝ) else 0`. Introduce `k i`. Simplify using `only [bR, Basis.ofZLatticeBasis_apply, ← hmι, hv, ← hb, hdelta, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hli : LinearIndependent ℝ v`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc k`. Use `congrArg (fun u => inner ℝ (bR k) u) hc` as an intermediate fact. Simplify using `only [inner_sum, real_inner_smul_right, hRdelta, inner_zero_right] at this`. Simplify using `using this`.

Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = finrank ℝ (EuclideanSpace ℝ (Fin N))`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ]`. Set `bv` to `basisOfLinearIndependentOfCardEqFinrank' v hli hcard`. Establish `hbv : ∀ i, bv i = v i` using `fun i => by simp [bv, basisOfLinearIndependentOfCardEqFinrank']`. Use `⟨bv, ?_, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `u hu`. Take `⟨w, hw, rfl⟩` from `(genusCovolBound_mem_zmap N ι _ _).mp hu`. Establish `hc : ∀ i, ∃ z : ℤ, b (m i) w = z` using `fun i => hw (m i) (hmM i)`. Use `choose c hc using hc`.

Establish `e : ι w = ∑ i, (c i) • bv i`. Apply `InnerProductSpace.ext_inner_left_basis bR` to reduce the goal to its premises. Introduce `k`. Rewrite using `[inner_sum]`. Repeatedly rewrite using `[← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbv, hRdelta]`.

Simplify using `only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `only [bR, Basis.ofZLatticeBasis_apply, ← hmι, ← hb, hc]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hbv]`. Conclude with `(genusCovolBound_mem_zmap N ι _ _).mpr ⟨y i, hint i, rfl⟩`. Establish `e` using `Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) _ bv`.

Establish `hgv : Matrix.gram ℝ bv = (Rat.castHom ℝ).mapMatrix Gi`. Use extensionality with `i j`. Simplify using `only [Matrix.gram_apply, hbv, hv, RingHom.mapMatrix_apply, Matrix.map_apply, ← hb, hyy]`. Rewrite using `[hGisymm]`. Both sides reduce to the same expression.

Rewrite using `[e, hgv, ← RingHom.map_det, hcov, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Establish `h0 : (0 : ℝ) ≤ ((G.det : ℚ) : ℝ)` using `by exact_mod_cast hdetpos.le`. Express the relevant statement in the definitionally equal form `Real.sqrt ((G.det : ℚ) : ℝ) * Real.sqrt (((G.det)⁻¹ : ℚ) : ℝ) = 1`. Rewrite using `[← Real.sqrt_mul h0, Rat.cast_inv, mul_inv_cancel₀ (by exact_mod_cast hdetpos.ne'), Real.sqrt_one]`.
-/
theorem genusCovol_dualBasis (h : V →ₗ⋆[K] V →ₗ[K] K) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)] :
    ∃ bv : Basis (Module.Free.ChooseBasisIndex ℤ (zmap ι M)) ℝ (EuclideanSpace ℝ (Fin N)),
      zmap ι (genusCovol_tdual h M) = Submodule.span ℤ (Set.range bv) ∧
      ZLattice.covolume (zmap ι M) * ZLattice.covolume (Submodule.span ℤ (Set.range bv)) = 1 := by
  classical
  set Λ := zmap ι M with hΛ
  let bz := Module.Free.chooseBasis ℤ Λ
  let bR := bz.ofZLatticeBasis ℝ Λ
  have hmem : ∀ i, ∃ m ∈ M, ι m = (bz i : EuclideanSpace ℝ (Fin N)) := fun i =>
    (genusCovolBound_mem_zmap N ι M _).mp (bz i).2
  choose m hmM hmι using hmem
  set b : V → V → ℚ := fun x y => Algebra.trace ℚ K (h x y) with hbdef
  have hb : ∀ x y, ((b x y : ℚ) : ℝ) = inner ℝ (ι x) (ι y) := fun x y => (hι x y).symm
  have hsymm : ∀ x y, b x y = b y x := fun x y => by
    have e := hb x y
    rw [real_inner_comm, ← hb] at e
    exact_mod_cast e
  set G : Matrix (Module.Free.ChooseBasisIndex ℤ Λ) (Module.Free.ChooseBasisIndex ℤ Λ) ℚ :=
    Matrix.of fun i j => b (m i) (m j) with hG
  have hgram : Matrix.gram ℝ bR = (Rat.castHom ℝ).mapMatrix G := by
    ext i j
    simp only [Matrix.gram_apply, bR, Basis.ofZLatticeBasis_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, hG, Matrix.of_apply, ← hmι]
    exact (hb _ _).symm
  have hcov : ZLattice.covolume Λ = Real.sqrt ((G.det : ℚ) : ℝ) := by
    have e := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) _ bR
    rw [Basis.ofZLatticeBasis_span] at e
    rw [e, hgram, ← RingHom.map_det]
    rfl
  have hdetpos : 0 < G.det := by
    have := ZLattice.covolume_pos Λ
    rw [hcov, Real.sqrt_pos] at this
    exact_mod_cast this
  have hGsymm : G.transpose = G := by
    ext i j
    simp [hG, hsymm (m j) (m i)]
  have hGunit : IsUnit G.det := (ne_of_gt hdetpos).isUnit
  set Gi := G⁻¹ with hGi
  have hGiT : Gi.transpose = Gi := by rw [hGi, Matrix.transpose_nonsing_inv, hGsymm]
  have hGisymm : ∀ i j, Gi i j = Gi j i := by
    intro i j
    conv_lhs => rw [← hGiT]
    rfl
  set y : Module.Free.ChooseBasisIndex ℤ Λ → V :=
    fun i => ∑ j, (algebraMap ℚ K (Gi i j)) • m j with hy
  have hlin : ∀ x i, b x (y i) = ∑ j, Gi i j * b x (m j) := by
    intro x i
    simp only [hbdef, hy]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hdelta : ∀ k i, b (m k) (y i) = (1 : Matrix _ _ ℚ) k i := by
    intro k i
    rw [hlin]
    have e : (G * Gi) k i = (1 : Matrix _ _ ℚ) k i := by rw [hGi, Matrix.mul_nonsing_inv _ hGunit]
    rw [← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hGisymm i j, mul_comm]
    rfl
  have hint : ∀ i, ∀ x ∈ M, ∃ z : ℤ, b x (y i) = z := by
    intro i x hx
    have hxΛ : ι x ∈ Λ := (genusCovolBound_mem_zmap N ι M _).mpr ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = bz.repr ⟨ι x, hxΛ⟩ := ⟨_, rfl⟩
    refine ⟨c i, ?_⟩
    have hsum : ι x = ∑ k, ((c k : ℤ) : ℝ) • bR k := by
      conv_lhs => rw [← bR.sum_repr (ι x)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := Basis.ofZLatticeBasis_repr_apply ℝ Λ bz ⟨ι x, hxΛ⟩ k
      simp only at this
      rw [this, hc]
    have e : ((b x (y i) : ℚ) : ℝ) = (((c i : ℤ) : ℚ) : ℝ) := by
      rw [hb, hsum, sum_inner]
      simp_rw [real_inner_smul_left, bR, Basis.ofZLatticeBasis_apply, ← hmι, ← hb, hdelta]
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Matrix.one_apply, hk]) (by simp)]
      simp [Matrix.one_apply]
    exact_mod_cast e
  have hyy : ∀ i j, b (y i) (y j) = Gi j i := by
    intro i j
    rw [hlin]
    have e : ∀ l, Gi j l * b (y i) (m l) = Gi j l * (1 : Matrix _ _ ℚ) l i := by
      intro l
      rw [hsymm (y i) (m l), hdelta]
    rw [Finset.sum_congr rfl fun l _ => e l]
    simp [Matrix.one_apply]

  set v : Module.Free.ChooseBasisIndex ℤ Λ → EuclideanSpace ℝ (Fin N) := fun i => ι (y i) with hv
  have hRdelta : ∀ k i, inner ℝ (bR k) (v i) = if k = i then (1 : ℝ) else 0 := by
    intro k i
    simp only [bR, Basis.ofZLatticeBasis_apply, ← hmι, hv, ← hb, hdelta, Matrix.one_apply]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have := congrArg (fun u => inner ℝ (bR k) u) hc
    simp only [inner_sum, real_inner_smul_right, hRdelta, inner_zero_right] at this
    simpa using this
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) =
      finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ]
  let bv := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  have hbv : ∀ i, bv i = v i := fun i => by simp [bv, basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨bv, ?_, ?_⟩
  · apply le_antisymm
    · intro u hu
      obtain ⟨w, hw, rfl⟩ := (genusCovolBound_mem_zmap N ι _ _).mp hu
      have hc : ∀ i, ∃ z : ℤ, b (m i) w = z := fun i => hw (m i) (hmM i)
      choose c hc using hc
      have e : ι w = ∑ i, (c i) • bv i := by
        apply InnerProductSpace.ext_inner_left_basis bR
        intro k
        rw [inner_sum]
        simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbv, hRdelta]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [bR, Basis.ofZLatticeBasis_apply, ← hmι, ← hb, hc]
        simp
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hbv]
      exact (genusCovolBound_mem_zmap N ι _ _).mpr ⟨y i, hint i, rfl⟩
  · have e := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) _ bv
    have hgv : Matrix.gram ℝ bv = (Rat.castHom ℝ).mapMatrix Gi := by
      ext i j
      simp only [Matrix.gram_apply, hbv, hv, RingHom.mapMatrix_apply, Matrix.map_apply, ← hb, hyy]
      rw [hGisymm]
      rfl
    rw [e, hgv, ← RingHom.map_det, hcov, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have h0 : (0 : ℝ) ≤ ((G.det : ℚ) : ℝ) := by exact_mod_cast hdetpos.le
    change Real.sqrt ((G.det : ℚ) : ℝ) * Real.sqrt (((G.det)⁻¹ : ℚ) : ℝ) = 1
    rw [← Real.sqrt_mul h0, Rat.cast_inv, mul_inv_cancel₀ (by exact_mod_cast hdetpos.ne'),
      Real.sqrt_one]

/- English proof (translation)
Introduce `v hv`. Take `⟨x, hx, rfl⟩` from `(genusCovolBound_mem_zmap N ι A v).mp hv`. Conclude with `(genusCovolBound_mem_zmap N ι B _).mpr ⟨x, hAB hx, rfl⟩`.
-/
theorem genusCovol_zmap_mono (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)) {A B : Submodule (𝓞 K) V}
    (hAB : A ≤ B) : zmap ι A ≤ zmap ι B := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (genusCovolBound_mem_zmap N ι A v).mp hv
  exact (genusCovolBound_mem_zmap N ι B _).mpr ⟨x, hAB hx, rfl⟩

/- English proof (translation)
Unfold `zmap`. Rewrite using `[AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hinj`.
-/
theorem genusCovol_ri_zmap (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)) (hinj : Function.Injective ι)
    (A B : Submodule (𝓞 K) V) :
    (zmap ι A).toAddSubgroup.relIndex (zmap ι B).toAddSubgroup =
      A.toAddSubgroup.relIndex B.toAddSubgroup := by
  unfold zmap
  rw [AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

/- English proof (translation)
Take `⟨bv, hE2, hprod⟩` from `genusCovol_dualBasis h N ι hι A`. Establish `hinj : Function.Injective ι`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hpos x hne`. Establish `h2` using `hι x x`. Rewrite `h2` using `[hx, inner_zero_left]`. Establish `: ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = 0` using `h2.symm`. Establish `: Algebra.trace ℚ K (h x x) = 0` using `by exact_mod_cast this`.

Conclude with `lt_irrefl _ (this ▸ h1)`. Use `set Λ := zmap ι A with hΛ`. Use `set NE := zmap ι (A ⊓ genusCovol_tdual h A) with hNE`. Establish `hNΛ : NE ≤ Λ` using `genusCovol_zmap_mono N ι inf_le_left`. Establish `hNT : NE ≤ Submodule.span ℤ (Set.range bv)` using `hE2 ▸ genusCovol_zmap_mono N ι inf_le_right`.

Use `haveI : DiscreteTopology NE := DiscreteTopology.of_subset (s := (Λ : Set (EuclideanSpace ℝ (Fin N)))) inferInstance hNΛ`. Use `haveI : IsZLattice ℝ NE := by`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ), Submodule.span_le]`. Introduce `v hv`.

Take `⟨x, hx, rfl⟩` from `(genusCovolBound_mem_zmap N ι A v).mp hv`. Establish `hDx : ι (D • x) ∈ NE` using `(genusCovolBound_mem_zmap N ι _ _).mpr ⟨D • x, ⟨A.nsmul_mem hx D, hD x hx⟩, rfl⟩`. Rewrite `hDx` using `[map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]`. Establish `hD' : (D : ℝ) ≠ 0` using `by exact_mod_cast hD0.ne'`. Establish `: ι x = (D : ℝ)⁻¹ • ((D : ℝ) • ι x)` using `by rw [smul_smul, inv_mul_cancel₀ hD', one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hDx)`. Establish `e1` using `ZLattice.covolume_div_covolume_eq_relIndex' NE Λ hNΛ`. Establish `e2` using `ZLattice.covolume_div_covolume_eq_relIndex' NE _ hNT`. Establish `hri1 : NE.toAddSubgroup.relIndex Λ.toAddSubgroup = (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup`.

Rewrite using `[hNE, hΛ, genusCovol_ri_zmap N ι hinj]`. Rewrite `e1` using `[hri1]`. Establish `hri2 : NE.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range bv)).toAddSubgroup = (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup`. Rewrite using `[← hE2, hNE, genusCovol_ri_zmap N ι hinj]`. Rewrite `e2` using `[hri2]`.

Establish `hc` using `ZLattice.covolume_pos Λ`. Establish `hc'` using `ZLattice.covolume_pos (Submodule.span ℤ (Set.range bv))`. Establish `hn` using `ZLattice.covolume_pos NE`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Rewrite `e1` using `[h0, Nat.cast_zero]`. Conclude with `(div_pos hn hc).ne' e1`. Introduce `h0`. Rewrite `e2` using `[h0, Nat.cast_zero]`. Conclude with `(div_pos hn hc').ne' e2`.

Rewrite using `[← e1, ← e2]`. Establish `hc'eq` using `eq_inv_of_mul_eq_one_right hprod`. Rewrite using `[hc'eq, div_inv_eq_mul, ← hΛ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem genusCovol_sq (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (A : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι A)] [IsZLattice ℝ (zmap ι A)]
    (D : ℕ) (hD0 : 0 < D) (hD : ∀ x ∈ A, D • x ∈ genusCovol_tdual h A) :
    (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 ∧
    (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup ≠ 0 ∧
    ZLattice.covolume (zmap ι A) ^ 2 *
        ((A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ((A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup : ℝ) := by
  classical
  obtain ⟨bv, hE2, hprod⟩ := genusCovol_dualBasis h N ι hι A
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have h1 := hpos x hne
    have h2 := hι x x
    rw [hx, inner_zero_left] at h2
    have : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = 0 := h2.symm
    have : Algebra.trace ℚ K (h x x) = 0 := by exact_mod_cast this
    exact lt_irrefl _ (this ▸ h1)
  set Λ := zmap ι A with hΛ
  set NE := zmap ι (A ⊓ genusCovol_tdual h A) with hNE
  have hNΛ : NE ≤ Λ := genusCovol_zmap_mono N ι inf_le_left
  have hNT : NE ≤ Submodule.span ℤ (Set.range bv) := hE2 ▸ genusCovol_zmap_mono N ι inf_le_right
  haveI : DiscreteTopology NE :=
    DiscreteTopology.of_subset (s := (Λ : Set (EuclideanSpace ℝ (Fin N)))) inferInstance hNΛ
  haveI : IsZLattice ℝ NE := by
    refine ⟨?_⟩
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ), Submodule.span_le]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (genusCovolBound_mem_zmap N ι A v).mp hv
    have hDx : ι (D • x) ∈ NE :=
      (genusCovolBound_mem_zmap N ι _ _).mpr ⟨D • x, ⟨A.nsmul_mem hx D, hD x hx⟩, rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at hDx
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD0.ne'
    have : ι x = (D : ℝ)⁻¹ • ((D : ℝ) • ι x) := by rw [smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hDx)
  have e1 := ZLattice.covolume_div_covolume_eq_relIndex' NE Λ hNΛ
  have e2 := ZLattice.covolume_div_covolume_eq_relIndex' NE _ hNT
  have hri1 : NE.toAddSubgroup.relIndex Λ.toAddSubgroup =
      (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup := by
    rw [hNE, hΛ, genusCovol_ri_zmap N ι hinj]
  rw [hri1] at e1
  have hri2 : NE.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range bv)).toAddSubgroup =
      (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup := by
    rw [← hE2, hNE, genusCovol_ri_zmap N ι hinj]
  rw [hri2] at e2
  have hc := ZLattice.covolume_pos Λ
  have hc' := ZLattice.covolume_pos (Submodule.span ℤ (Set.range bv))
  have hn := ZLattice.covolume_pos NE
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, Nat.cast_zero] at e1
    exact (div_pos hn hc).ne' e1
  · intro h0
    rw [h0, Nat.cast_zero] at e2
    exact (div_pos hn hc').ne' e2
  · rw [← e1, ← e2]
    have hc'eq := eq_inv_of_mul_eq_one_right hprod
    rw [hc'eq, div_inv_eq_mul, ← hΛ]
    field_simp

end PartE

section PartF

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hle` using `locBasic_hcompl_le (K := K) P`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← genusCovol_locS_locS hle L, gmap_locS_comm]`. Express the relevant statement in the definitionally equal form `locS P.primeCompl (gmap g (loc (K := K) P L)) = _`. Rewrite using `[hgL]`.

Conclude with `genusCovol_locS_locS hle M`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `genus_covolume_local_dual_le h g hg P L M hMfg (hgL ▸ genusCovol_le_locS _ M)`. Establish `hL' : L ≤ gmap g⁻¹ (loc (K` using `K) P M) := by`. Rewrite using `[← hgL, genusBasic_gmap_inv]`.

Conclude with `genusCovol_le_locS _ L`. Use `genus_covolume_local_dual_le h g⁻¹ ((isom h).inv_mem hg) P M L hLfg hL'` as an intermediate fact. Establish `h2` using `Submodule.map_mono (f := ((g : V →ₗ[K] V).restrictScalars (𝓞 K))) this`. Express the relevant statement in the definitionally equal form `gmap g (gmap g⁻¹ _) ≤ gmap g _ at h2`. Rewrite `h2` using `[genusCovol_gmap_gmap_inv]`. Then use the resulting hypothesis.
-/
theorem genusCovol_local (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule (𝓞 K) V) (hLfg : L.FG)
    (hMfg : M.FG) (P : Ideal (𝓞 K)) [P.IsPrime] (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (hgL : gmap g (loc (K := K) P L) = loc (K := K) P M) :
    gmap g (locS P.primeCompl L) = locS P.primeCompl M ∧
    gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
      locS P.primeCompl (genusCovol_tdual h M) := by
  have hle := locBasic_hcompl_le (K := K) P
  refine ⟨?_, ?_⟩
  · rw [← genusCovol_locS_locS hle L, gmap_locS_comm]
    change locS P.primeCompl (gmap g (loc (K := K) P L)) = _
    rw [hgL]
    exact genusCovol_locS_locS hle M
  · apply le_antisymm
    · exact genus_covolume_local_dual_le h g hg P L M hMfg (hgL ▸ genusCovol_le_locS _ M)
    · have hL' : L ≤ gmap g⁻¹ (loc (K := K) P M) := by
        rw [← hgL, genusBasic_gmap_inv]
        exact genusCovol_le_locS _ L
      have := genus_covolume_local_dual_le h g⁻¹ ((isom h).inv_mem hg) P M L hLfg hL'
      have h2 := Submodule.map_mono (f := ((g : V →ₗ[K] V).restrictScalars (𝓞 K))) this
      change gmap g (gmap g⁻¹ _) ≤ gmap g _ at h2
      rwa [genusCovol_gmap_gmap_inv] at h2

/- English proof (translation)
Rewrite using `[← hXY]`. Both sides reduce to the same expression.
-/
theorem genusCovol_addData (g : V ≃ₗ[K] V) (X Y : Submodule (𝓞 K) V) (hXY : gmap g X = Y) :
    X.toAddSubgroup.map (((g : V →ₗ[K] V).restrictScalars (𝓞 K) : V →ₗ[𝓞 K] V) : V →+ V) =
      Y.toAddSubgroup := by
  rw [← hXY]
  rfl

end PartF

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hs hpos N ι hι L M hL hM _ _ _ _`. Establish `hMl : Submodule.IsLattice K M` using `hM.1`. Take `⟨d, hd0, hd⟩` from `genusScale K V h hs L hL`. Establish `hLgen : L ∈ genus h L` using `⟨hL, fun p _ => ⟨1, (isom h).one_mem, genusBasic_gmap_one _⟩⟩`. Establish `hDmem : ∀ A ∈ genus h L, ∀ x ∈ A, d • x ∈ genusCovol_tdual h A`.

Introduce `A hA x hx y hy`. Take `⟨r, hr⟩` from `Submodule.mem_one.mp (hd A hA y hy x hx)`. Take `⟨z, hz⟩` from `genusCovolBound_trace_int r`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul, nsmul_eq_mul, ← hz, hr]`.

Take `⟨hL1, hL2, hLsq⟩` from `genusCovol_sq h hpos N ι hι L d hd0 (hDmem L hLgen)`. Take `⟨hM1, hM2, hMsq⟩` from `genusCovol_sq h hpos N ι hι M d hd0 (hDmem M hM)`. Establish `hloc : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], ∃ g : V ≃ₗ[K] V, gmap g (locS P.primeCompl L) = locS P.primeCompl M ∧ gmap g (locS P.primeCompl (genusCovol_tdual h L)) = locS P.primeCompl (genusCovol_tdual h M)`. Introduce `P hP`. Take `⟨g, hg, hgL⟩` from `hM.2 P hP`.

Conclude with `⟨g, genusCovol_local h L M hL.fg hMl.fg P g hg hgL⟩`. Establish `hinf : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal] (g : V ≃ₗ[K] V), gmap g (locS P.primeCompl L) = locS P.primeCompl M → gmap g (locS P.primeCompl (genusCovol_tdual h L)) = locS P.primeCompl (genusCovol_tdual h M) → gmap g (locS P.primeCompl (L ⊓ genusCovol_tdual h L)) = locS P.primeCompl …`. Introduce `P _ g e1 e2`. Rewrite using `[locBasic_locS_inf, locBasic_locS_inf, genusCovol_gmap_inf, e1, e2]`. Establish `eA` using `genusCovol_lemmaS _ (L ⊓ genusCovol_tdual h L) L (M ⊓ genusCovol_tdual h M) M inf_le_left inf_le_left rfl hL1 hM1 (by`.

Introduce `P _`. Take `⟨g, e1, e2⟩` from `hloc P`. Conclude with `⟨_, g.injective, genusCovol_addData g _ _ (hinf P g e1 e2), genusCovol_addData g _ _ e1⟩)`. Establish `eB` using `genusCovol_lemmaS _ (L ⊓ genusCovol_tdual h L) (genusCovol_tdual h L) (M ⊓ genusCovol_tdual h M) (genusCovol_tdual h M) inf_le_right inf_le_right rfl hL2 hM2 (by`. Introduce `P _`.

Take `⟨g, e1, e2⟩` from `hloc P`. Conclude with `⟨_, g.injective, genusCovol_addData g _ _ (hinf P g e1 e2), genusCovol_addData g _ _ e2⟩)`. Rewrite `hMsq` using `[eA, eB, ← hLsq]`. Establish `hr0 : (0 : ℝ) < ((L ⊓ genusCovol_tdual h L).toAddSubgroup.relIndex L.toAddSubgroup : ℝ)`. Conclude with `Nat.pos_of_ne_zero hL1` after adjusting the coercions.

Establish `hsq` using `mul_right_cancel₀ hr0.ne' hMsq`. Conclude with `(pow_left_inj₀ (ZLattice.covolume_pos (zmap ι M)).le (ZLattice.covolume_pos (zmap ι L)).le two_ne_zero).mp hsq`.
-/
theorem genusCovol : GenusCovol := by
  intro K V _ _ _ _ _ _ _ _ h hs hpos N ι hι L M hL hM _ _ _ _
  classical
  have hMl : Submodule.IsLattice K M := hM.1
  obtain ⟨d, hd0, hd⟩ := genusScale K V h hs L hL
  have hLgen : L ∈ genus h L := ⟨hL, fun p _ => ⟨1, (isom h).one_mem, genusBasic_gmap_one _⟩⟩
  have hDmem : ∀ A ∈ genus h L, ∀ x ∈ A, d • x ∈ genusCovol_tdual h A := by
    intro A hA x hx y hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hd A hA y hy x hx)
    obtain ⟨z, hz⟩ := genusCovolBound_trace_int r
    refine ⟨z, ?_⟩
    rw [map_nsmul, nsmul_eq_mul, ← hz, hr]
  obtain ⟨hL1, hL2, hLsq⟩ := genusCovol_sq h hpos N ι hι L d hd0 (hDmem L hLgen)
  obtain ⟨hM1, hM2, hMsq⟩ := genusCovol_sq h hpos N ι hι M d hd0 (hDmem M hM)
  have hloc : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], ∃ g : V ≃ₗ[K] V,
      gmap g (locS P.primeCompl L) = locS P.primeCompl M ∧
      gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
        locS P.primeCompl (genusCovol_tdual h M) := by
    intro P hP
    obtain ⟨g, hg, hgL⟩ := hM.2 P hP
    exact ⟨g, genusCovol_local h L M hL.fg hMl.fg P g hg hgL⟩
  have hinf : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal] (g : V ≃ₗ[K] V),
      gmap g (locS P.primeCompl L) = locS P.primeCompl M →
      gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
        locS P.primeCompl (genusCovol_tdual h M) →
      gmap g (locS P.primeCompl (L ⊓ genusCovol_tdual h L)) =
        locS P.primeCompl (M ⊓ genusCovol_tdual h M) := by
    intro P _ g e1 e2
    rw [locBasic_locS_inf, locBasic_locS_inf, genusCovol_gmap_inf, e1, e2]
  have eA := genusCovol_lemmaS _ (L ⊓ genusCovol_tdual h L) L (M ⊓ genusCovol_tdual h M) M
    inf_le_left inf_le_left rfl hL1 hM1 (by
      intro P _
      obtain ⟨g, e1, e2⟩ := hloc P
      exact ⟨_, g.injective, genusCovol_addData g _ _ (hinf P g e1 e2),
        genusCovol_addData g _ _ e1⟩)
  have eB := genusCovol_lemmaS _ (L ⊓ genusCovol_tdual h L) (genusCovol_tdual h L)
    (M ⊓ genusCovol_tdual h M) (genusCovol_tdual h M)
    inf_le_right inf_le_right rfl hL2 hM2 (by
      intro P _
      obtain ⟨g, e1, e2⟩ := hloc P
      exact ⟨_, g.injective, genusCovol_addData g _ _ (hinf P g e1 e2),
        genusCovol_addData g _ _ e2⟩)
  rw [eA, eB, ← hLsq] at hMsq
  have hr0 : (0 : ℝ) < ((L ⊓ genusCovol_tdual h L).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hL1
  have hsq := mul_right_cancel₀ hr0.ne' hMsq
  exact (pow_left_inj₀ (ZLattice.covolume_pos (zmap ι M)).le (ZLattice.covolume_pos (zmap ι L)).le
    two_ne_zero).mp hsq

end Formalism.HermitianLatticesTheory
