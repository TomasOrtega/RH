import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardQuotientGenericOfIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.BZSeg.NuPairIrr

section Lists

variable {α : Type*} {h : ℕ}

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `List.getElem_of_mem hw`. Establish `hpl : p < (A ++ B).length` using `by simp; omega`. Set `P : Fin (A ++ B).length` to `⟨p, hpl⟩`. Establish `hget : (A ++ B).get P = A[p]`. Simplify using `[P, List.getElem_append_left hp]`.

Use `⟨c P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc (c P), Zc.Cos.sub]`. Use `List.mem_map.2 ⟨P, ?_, hget⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[← hc (c P), Zc.Cos.sub]`.

Establish `hP : P ∈ (List.finRange (A ++ B).length).filter (fun q => c q = c P)` using `by simp`. Establish `hpw : ((List.finRange (A ++ B).length).filter (fun q => c q = c P)).Pairwise (· < ·)` using `(List.pairwise_lt_finRange _).filter _`. Use `revert hP hpw`. Generalize the expression as in `(List.finRange (A ++ B).length).filter (fun q => c q = c P) = L`. Introduce `hP hpw`.

Consider the cases of `L with`. Consider the case `nil => simp at hP`. Consider the case `cons q L`. Establish `hq : q.1 ≤ p`. Break down `List.mem_cons.1 hP with e | e` into its components or cases.

Rewrite using `[← e]`. Conclude with `le_of_lt (List.rel_of_pairwise_cons hpw e)`. Establish `hqA : q.1 < A.length` using `by omega`. Use `⟨A[q.1], List.getElem_mem hqA, ?_⟩` and prove the remaining obligations. Simplify using `[List.getElem_append_left hqA]`.
-/
theorem exists_head_of_mem_left (A B : List α) (c : Fin (A ++ B).length → Fin h) (D : Fin h → List α)
    (hc : ∀ i, sub (A ++ B) c i = D i) {w : α} (hw : w ∈ A) :
    ∃ i, w ∈ D i ∧ ∃ t ∈ A, (D i).head? = some t := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hw
  have hpl : p < (A ++ B).length := by simp; omega
  let P : Fin (A ++ B).length := ⟨p, hpl⟩
  have hget : (A ++ B).get P = A[p] := by
    simp [P, List.getElem_append_left hp]
  refine ⟨c P, ?_, ?_⟩
  · rw [← hc (c P), Zc.Cos.sub]
    refine List.mem_map.2 ⟨P, ?_, hget⟩
    simp
  · rw [← hc (c P), Zc.Cos.sub]
    have hP : P ∈ (List.finRange (A ++ B).length).filter (fun q => c q = c P) := by simp
    have hpw : ((List.finRange (A ++ B).length).filter (fun q => c q = c P)).Pairwise (· < ·) :=
      (List.pairwise_lt_finRange _).filter _
    revert hP hpw
    generalize (List.finRange (A ++ B).length).filter (fun q => c q = c P) = L
    intro hP hpw
    cases L with
    | nil => simp at hP
    | cons q L =>
      have hq : q.1 ≤ p := by
        rcases List.mem_cons.1 hP with e | e
        · rw [← e]
        · exact le_of_lt (List.rel_of_pairwise_cons hpw e)
      have hqA : q.1 < A.length := by omega
      refine ⟨A[q.1], List.getElem_mem hqA, ?_⟩
      simp [List.getElem_append_left hqA]

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `List.getElem_of_mem hw`. Establish `hpl : A.length + p < (A ++ B).length` using `by simp; omega`. Set `P : Fin (A ++ B).length` to `⟨A.length + p, hpl⟩`. Establish `hget : (A ++ B).get P = B[p]`. Simplify using `[P]`.

Use `⟨c P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc (c P), Zc.Cos.sub]`. Use `List.mem_map.2 ⟨P, ?_, hget⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[← hc (c P), Zc.Cos.sub]`.

Establish `hP : P ∈ (List.finRange (A ++ B).length).filter (fun q => c q = c P)` using `by simp`. Establish `hpw : ((List.finRange (A ++ B).length).filter (fun q => c q = c P)).Pairwise (· < ·)` using `(List.pairwise_lt_finRange _).filter _`. Use `revert hP hpw`. Generalize the expression as in `(List.finRange (A ++ B).length).filter (fun q => c q = c P) = L`. Introduce `hP hpw`.

Break down `List.eq_nil_or_concat L with rfl | ⟨L', q, rfl⟩` into its components or cases. Simplify using `at hP`. Rewrite `hP`, `hpw`, the goal using `[List.concat_eq_append]`. Establish `hq : A.length + p ≤ q.1`. Break down `List.mem_append.1 hP with e | e` into its components or cases.

Conclude with `le_of_lt ((List.pairwise_append.1 hpw).2.2 _ e q (by simp))`. Conclude with `le_of_eq (congrArg Fin.val (List.mem_singleton.1 e))`. Establish `hqA : q.1 - A.length < B.length`. Use `q.2` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Use `⟨B[q.1 - A.length], List.getElem_mem hqA, ?_⟩` and prove the remaining obligations. Establish `hle : A.length ≤ q.1` using `by omega`. Simplify using `[List.getElem_append_right hle]`.
-/
theorem exists_last_of_mem_right (A B : List α) (c : Fin (A ++ B).length → Fin h) (D : Fin h → List α)
    (hc : ∀ i, sub (A ++ B) c i = D i) {w : α} (hw : w ∈ B) :
    ∃ i, w ∈ D i ∧ ∃ t ∈ B, (D i).getLast? = some t := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hw
  have hpl : A.length + p < (A ++ B).length := by simp; omega
  let P : Fin (A ++ B).length := ⟨A.length + p, hpl⟩
  have hget : (A ++ B).get P = B[p] := by
    simp [P]
  refine ⟨c P, ?_, ?_⟩
  · rw [← hc (c P), Zc.Cos.sub]
    refine List.mem_map.2 ⟨P, ?_, hget⟩
    simp
  · rw [← hc (c P), Zc.Cos.sub]
    have hP : P ∈ (List.finRange (A ++ B).length).filter (fun q => c q = c P) := by simp
    have hpw : ((List.finRange (A ++ B).length).filter (fun q => c q = c P)).Pairwise (· < ·) :=
      (List.pairwise_lt_finRange _).filter _
    revert hP hpw
    generalize (List.finRange (A ++ B).length).filter (fun q => c q = c P) = L
    intro hP hpw
    rcases List.eq_nil_or_concat L with rfl | ⟨L', q, rfl⟩
    · simp at hP
    · rw [List.concat_eq_append] at hP hpw ⊢
      have hq : A.length + p ≤ q.1 := by
        rcases List.mem_append.1 hP with e | e
        · exact le_of_lt ((List.pairwise_append.1 hpw).2.2 _ e q (by simp))
        · exact le_of_eq (congrArg Fin.val (List.mem_singleton.1 e))
      have hqA : q.1 - A.length < B.length := by
        have := q.2
        simp at this
        omega
      refine ⟨B[q.1 - A.length], List.getElem_mem hqA, ?_⟩
      have hle : A.length ≤ q.1 := by omega
      simp [List.getElem_append_right hle]

end Lists

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[IrrGL.nu_nu]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem nu_nat_add (x : IrrGL k) (a b : ℕ) : (x.nu (a : ℂ)).nu (b : ℂ) = x.nu ((a + b : ℕ) : ℂ) := by
  rw [IrrGL.nu_nu]
  push_cast
  rfl

def top (Γ : Segment k) : IrrGL k := Γ.first.nu ((Γ.len - 1 : ℕ) : ℂ)

/- English proof (translation)
The claim follows from `(Γ.isCusp_first.nu _).1`.
-/
theorem top_pos (Γ : Segment k) : 0 < (top Γ).1 := (Γ.isCusp_first.nu _).1

/- English proof (translation)
Simplify using `only [decWord, List.mem_reverse, List.mem_ofFn]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨a, a.2, rfl⟩`. Introduce and unpack `⟨a, ha, rfl⟩`.

Conclude with `⟨⟨a, ha⟩, rfl⟩`.
-/
theorem mem_decWord {Γ : Segment k} {w : IrrGL k} : w ∈ decWord Γ ↔ ∃ a : ℕ, a < Γ.len ∧ Γ.first.nu (a : ℂ) = w := by
  simp only [decWord, List.mem_reverse, List.mem_ofFn]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/- English proof (translation)
Establish `hl` using `Γ.len_pos`. Take `⟨n, hn⟩ : ∃ n, Γ.len = n + 1` from `⟨Γ.len - 1, by omega⟩`. Establish `h1 : (decWord Γ).length = Γ.len` using `by simp [decWord]`. Rewrite using `[List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]`. Use `congr 1`.

Simplify using `[decWord, Segment.term, top, List.getElem_reverse]`.
-/
theorem head?_decWord (Γ : Segment k) : (decWord Γ).head? = some (top Γ) := by
  have hl := Γ.len_pos
  obtain ⟨n, hn⟩ : ∃ n, Γ.len = n + 1 := ⟨Γ.len - 1, by omega⟩
  have h1 : (decWord Γ).length = Γ.len := by simp [decWord]
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  congr 1
  simp [decWord, Segment.term, top, List.getElem_reverse]

/- English proof (translation)
Establish `hl` using `Γ.len_pos`. Establish `h1 : (decWord Γ).length = Γ.len` using `by simp [decWord]`. Rewrite using `[List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]`. Use `congr 1`. Simplify using `[decWord, Segment.term, List.getElem_reverse]`.
-/
theorem getLast?_decWord (Γ : Segment k) : (decWord Γ).getLast? = some Γ.first := by
  have hl := Γ.len_pos
  have h1 : (decWord Γ).length = Γ.len := by simp [decWord]
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  congr 1
  simp [decWord, Segment.term, List.getElem_reverse]

/- English proof (translation)
Establish `hpos : 0 < Γ.first.1` using `Γ.isCusp_first.1`. Establish `hl'` using `Γ'.len_pos`. Use `⟨⟨Segment.ofFirst Γ.first Γ.isCusp_first (e + Γ'.len) (by omega), ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Set.mem_union, Segment.mem_carrier, Segment.first_ofFirst, Segment.len_ofFirst]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Distinguish the cases in `hc : a < Γ.len`. Conclude with `Or.inl ⟨a, hc, rfl⟩`. Use `Or.inr ⟨a - e, by omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, nu_nat_add]`. Use `congr 3`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `(⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)`. Conclude with `⟨a, by omega, rfl⟩`.

Conclude with `⟨e + a, by omega, by rw [he, nu_nat_add]⟩`. Introduce `hs`. Take `⟨a, ha, hx⟩` from `Segment.mem_carrier.1 (hs (Segment.mem_carrier.2 ⟨0, Γ.len_pos, rfl⟩))`. Rewrite `hx` using `[he, nu_nat_add]`. Use `(IrrGL.nu_natCast_inj hpos).1 hx` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `hs`. Take `⟨a, ha, hx⟩` from `Segment.mem_carrier.1 (hs (Segment.mem_carrier.2 ⟨Γ'.len - 1, by omega, rfl⟩))`. Rewrite `hx` using `[he, nu_nat_add]`. Use `(IrrGL.nu_natCast_inj hpos).1 hx` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem linked_of (Γ Γ' : Segment k) {e : ℕ} (he : Γ'.first = Γ.first.nu (e : ℂ)) (h0 : 0 < e) (h1 : e ≤ Γ.len)
    (h2 : Γ.len < e + Γ'.len) : Γ.Linked Γ' := by
  have hpos : 0 < Γ.first.1 := Γ.isCusp_first.1
  have hl' := Γ'.len_pos
  refine ⟨⟨Segment.ofFirst Γ.first Γ.isCusp_first (e + Γ'.len) (by omega), ?_⟩, ?_, ?_⟩
  · ext x
    simp only [Set.mem_union, Segment.mem_carrier, Segment.first_ofFirst, Segment.len_ofFirst]
    constructor
    · rintro ⟨a, ha, rfl⟩
      by_cases hc : a < Γ.len
      · exact Or.inl ⟨a, hc, rfl⟩
      · refine Or.inr ⟨a - e, by omega, ?_⟩
        rw [he, nu_nat_add]
        congr 3
        omega
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact ⟨a, by omega, rfl⟩
      · exact ⟨e + a, by omega, by rw [he, nu_nat_add]⟩
  · intro hs
    obtain ⟨a, ha, hx⟩ := Segment.mem_carrier.1 (hs (Segment.mem_carrier.2 ⟨0, Γ.len_pos, rfl⟩))
    rw [he, nu_nat_add] at hx
    have := (IrrGL.nu_natCast_inj hpos).1 hx
    omega
  · intro hs
    obtain ⟨a, ha, hx⟩ := Segment.mem_carrier.1 (hs (Segment.mem_carrier.2 ⟨Γ'.len - 1, by omega, rfl⟩))
    rw [he, nu_nat_add] at hx
    have := (IrrGL.nu_natCast_inj hpos).1 hx
    omega

/- English proof (translation)
Take `⟨j, hj, t, ht, hfj⟩` from `H2 _ hi`. Take `⟨a, ha, hja⟩` from `mem_decWord.1 hj`. Take `⟨m, hm, htop⟩` from `H1 t ht`. Take `⟨r, hr, hmr⟩` from `mem_decWord.1 hm`. Establish `hlj` using `(Δ j).len_pos`.

Establish `hlm` using `(Δ m).len_pos`. Establish `hfj' : (Δ j).first = (Δ m).first.nu ((r + 1 : ℕ) : ℂ)`. Rewrite using `[← hfj, ← hmr, ← nu_nat_add]`. Simplify using the standard rewrite rules. Establish `hle : r + (Δ j).len + 1 ≤ (Δ m).len`.

Assume the negation of the conclusion as `hc`. Conclude with `hun m j (linked_of _ _ hfj' (by omega) (by omega) (by omega))`. Use `⟨m, htop, (1 + ((Δ j).len - 1 - a)) + ((Δ m).len - 1 - (r + (Δ j).len)), by omega, ?_⟩` and prove the remaining obligations. Establish `e1 : (top (Δ i)).nu ((1 : ℕ) : ℂ) = (Δ m).first.nu ((r + 1 + a : ℕ) : ℂ)`. Establish `: (top (Δ i)).nu ((1 : ℕ) : ℂ) = (Δ j).first.nu (a : ℂ)`.

Rewrite using `[hja]`. Simplify using the standard rewrite rules. Rewrite using `[this, hfj', nu_nat_add]`. Establish `e2 : (top (Δ i)).nu (((1 + ((Δ j).len - 1 - a)) + ((Δ m).len - 1 - (r + (Δ j).len)) : ℕ) : ℂ) = ((top (Δ i)).nu ((1 : ℕ) : ℂ)).nu ((((Δ j).len - 1 - a) + ((Δ m).len - 1 - (r + (Δ j).len)) : ℕ) : ℂ)`. Rewrite using `[nu_nat_add, Nat.add_assoc]`.

Rewrite using `[e2, e1, nu_nat_add, top]`. Use `congr 3`. Use linear arithmetic over natural numbers and integers.
-/
theorem step {h : ℕ} (Δ : Fin h → Segment k) (hun : ∀ i j, ¬ (Δ i).Linked (Δ j)) (u : List (IrrGL k))
    (H1 : ∀ w ∈ u, ∃ i, w ∈ decWord (Δ i) ∧ top (Δ i) ∈ u)
    (H2 : ∀ w ∈ u, ∃ j, w.nu 1 ∈ decWord (Δ j) ∧ ∃ t ∈ u, t.nu 1 = (Δ j).first)
    (i : Fin h) (hi : top (Δ i) ∈ u) : ∃ m, top (Δ m) ∈ u ∧ ∃ n : ℕ, 0 < n ∧ top (Δ m) = (top (Δ i)).nu (n : ℂ) := by
  obtain ⟨j, hj, t, ht, hfj⟩ := H2 _ hi
  obtain ⟨a, ha, hja⟩ := mem_decWord.1 hj
  obtain ⟨m, hm, htop⟩ := H1 t ht
  obtain ⟨r, hr, hmr⟩ := mem_decWord.1 hm
  have hlj := (Δ j).len_pos
  have hlm := (Δ m).len_pos
  have hfj' : (Δ j).first = (Δ m).first.nu ((r + 1 : ℕ) : ℂ) := by
    rw [← hfj, ← hmr, ← nu_nat_add]
    simp
  have hle : r + (Δ j).len + 1 ≤ (Δ m).len := by
    by_contra hc
    exact hun m j (linked_of _ _ hfj' (by omega) (by omega) (by omega))
  refine ⟨m, htop, (1 + ((Δ j).len - 1 - a)) + ((Δ m).len - 1 - (r + (Δ j).len)), by omega, ?_⟩
  have e1 : (top (Δ i)).nu ((1 : ℕ) : ℂ) = (Δ m).first.nu ((r + 1 + a : ℕ) : ℂ) := by
    have : (top (Δ i)).nu ((1 : ℕ) : ℂ) = (Δ j).first.nu (a : ℂ) := by
      rw [hja]
      simp
    rw [this, hfj', nu_nat_add]
  have e2 : (top (Δ i)).nu (((1 + ((Δ j).len - 1 - a)) + ((Δ m).len - 1 - (r + (Δ j).len)) : ℕ) : ℂ) =
      ((top (Δ i)).nu ((1 : ℕ) : ℂ)).nu ((((Δ j).len - 1 - a) + ((Δ m).len - 1 - (r + (Δ j).len)) : ℕ) : ℂ) := by
    rw [nu_nat_add, Nat.add_assoc]
  rw [e2, e1, nu_nat_add, top]
  congr 3
  omega

/- English proof (translation)
Take `⟨w, hw⟩` from `List.exists_mem_of_ne_nil u hu`. Take `⟨i₀, -, hi₀⟩` from `H1 w hw`. Set `S` to `{i : Fin h // top (Δ i) ∈ u}`. Set `r : S → S → Prop` to `fun a b => ∃ n : ℕ, 0 < n ∧ top (Δ a.1) = (top (Δ b.1)).nu (n : ℂ)`. Use `haveI : IsTrans S r := ⟨fun a b c ⟨n, hn, e⟩ ⟨n', hn', e'⟩ => ⟨n' + n, by omega, by rw [e, e', nu_nat_add]⟩⟩`.

Use `haveI : IsIrrefl S r := ⟨fun a ⟨n, hn, e⟩ => by`. Establish `e' : (top (Δ a.1)).nu ((0 : ℕ) : ℂ) = (top (Δ a.1)).nu (n : ℂ)`. Rewrite using `[← e]`. Simplify using the standard rewrite rules. Use `(IrrGL.nu_natCast_inj (top_pos _)).1 e'` as an intermediate fact.

Use the proof step `omega⟩`. Establish `wf : WellFounded r` using `Finite.wellFounded_of_trans_of_irrefl r`. Take `⟨a, -, hmin⟩` from `wf.has_min Set.univ ⟨⟨i₀, hi₀⟩, trivial⟩`. Take `⟨m, hm, n, hn, e⟩` from `step Δ hun u H1 H2 a.1 a.2`. Conclude with `hmin ⟨m, hm⟩ trivial ⟨n, hn, e⟩`.
-/
theorem false_of_shift {h : ℕ} (Δ : Fin h → Segment k) (hun : ∀ i j, ¬ (Δ i).Linked (Δ j)) (u : List (IrrGL k))
    (hu : u ≠ []) (H1 : ∀ w ∈ u, ∃ i, w ∈ decWord (Δ i) ∧ top (Δ i) ∈ u)
    (H2 : ∀ w ∈ u, ∃ j, w.nu 1 ∈ decWord (Δ j) ∧ ∃ t ∈ u, t.nu 1 = (Δ j).first) : False := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil u hu
  obtain ⟨i₀, -, hi₀⟩ := H1 w hw
  let S := {i : Fin h // top (Δ i) ∈ u}
  let r : S → S → Prop := fun a b => ∃ n : ℕ, 0 < n ∧ top (Δ a.1) = (top (Δ b.1)).nu (n : ℂ)
  haveI : IsTrans S r := ⟨fun a b c ⟨n, hn, e⟩ ⟨n', hn', e'⟩ =>
    ⟨n' + n, by omega, by rw [e, e', nu_nat_add]⟩⟩
  haveI : IsIrrefl S r := ⟨fun a ⟨n, hn, e⟩ => by
    have e' : (top (Δ a.1)).nu ((0 : ℕ) : ℂ) = (top (Δ a.1)).nu (n : ℂ) := by
      rw [← e]
      simp
    have := (IrrGL.nu_natCast_inj (top_pos _)).1 e'
    omega⟩
  have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨a, -, hmin⟩ := wf.has_min Set.univ ⟨⟨i₀, hi₀⟩, trivial⟩
  obtain ⟨m, hm, n, hn, e⟩ := step Δ hun u H1 H2 a.1 a.2
  exact hmin ⟨m, hm⟩ trivial ⟨n, hn, e⟩

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Rewrite `h` using `[jmL, dif_neg hc]`. Simplify using `at h`.
-/
theorem deg_of_one_le {W : List (IrrGL k)} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : 1 ≤ jmL W π) : ∑ a, (W.get a).1 = N := by
  by_contra hc
  rw [jmL, dif_neg hc] at h
  simp at h

/- English proof (translation)
Establish `hst` using `GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le hA y hy ![A, B] π hs hf (by`. Introduce `b`. Use `Fin.cases ?_ (fun b => ?_) b` and prove the remaining obligations. Conclude with `deg_of_one_le hA'`. Rewrite using `[Subsingleton.elim b 0]`.

Conclude with `deg_of_one_le hB)`. Establish `hfl : (List.ofFn ![A, B]).flatten = A ++ B`. Simplify using `[List.ofFn_succ]`. Rewrite `hst` using `[hfl, Fin.prod_univ_two]`. Use `le_trans ?_ hst` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_jmL_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : Fin 2 → IrrGL k) {N : ℕ}
    (hy : ∑ b, (y b).1 = N) (A B : List (IrrGL k)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hf : HasFiniteLength π) (h : 1 ≤ jm y hy π)
    (hA' : 1 ≤ jmL A (y 0).rep) (hB : 1 ≤ jmL B (y 1).rep) : 1 ≤ jmL (A ++ B) π := by
  have hst := GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le hA y hy ![A, B] π hs hf (by
    intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · exact deg_of_one_le hA'
    · rw [Subsingleton.elim b 0]
      exact deg_of_one_le hB)
  have hfl : (List.ofFn ![A, B]).flatten = A ++ B := by
    simp [List.ofFn_succ]
  rw [hfl, Fin.prod_univ_two] at hst
  refine le_trans ?_ hst
  calc (1 : ℕ∞) = 1 * (1 * 1) := by simp
    _ ≤ _ := mul_le_mul' h (mul_le_mul' hA' hB)

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Conclude with `GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA x hd τ hτ f ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩`.
-/
theorem one_le_jm_of_injective (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ) (f : τ.IntertwiningMap (prodIrr x hd))
    (hf : Function.Injective f) : 1 ≤ jm x hd τ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA x hd τ hτ f ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩

/- English proof (translation)
Establish `hd : ∑ a : Fin 1, ((fun _ : Fin 1 => ρ) a).1 = ρ.1` using `by simp`. Take `⟨φ⟩` from `nonempty_equiv_prodIrr_one ρ hd`. Rewrite using `[GlobalTheory.CompanionTheory.CsStages.jmL_eq_jm [ρ] (fun _ : Fin 1 => ρ) (by simp) hd ρ.rep]`. Use `haveI := nontrivial_of_irreducible ρ.2.rep.irr`. Conclude with `one_le_jm_of_injective hA (fun _ : Fin 1 => ρ) hd ρ.rep ρ.2.rep.smooth φ.toIntertwiningMap φ.injective`.
-/
theorem one_le_jmL_single (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL k) : 1 ≤ jmL [ρ] ρ.rep := by
  have hd : ∑ a : Fin 1, ((fun _ : Fin 1 => ρ) a).1 = ρ.1 := by simp
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one ρ hd
  rw [GlobalTheory.CompanionTheory.CsStages.jmL_eq_jm [ρ] (fun _ : Fin 1 => ρ) (by simp) hd ρ.rep]
  haveI := nontrivial_of_irreducible ρ.2.rep.irr
  exact one_le_jm_of_injective hA (fun _ : Fin 1 => ρ) hd ρ.rep ρ.2.rep.smooth φ.toIntertwiningMap φ.injective

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Module.Dual ℂ V, l v ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)`. Use `⟨⟨l.smulRight w, fun g => ?_⟩, v, smul_ne_zero hl hw⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim g 1, map_one, map_one]`. Conclude with `LinearMap.ext fun _ => rfl`.
-/
theorem exists_intertwiningMap_ne_zero {G V W : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] [Nontrivial W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    ∃ f : ρ.IntertwiningMap σ, ∃ v, f v ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ V, l v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  refine ⟨⟨l.smulRight w, fun g => ?_⟩, v, smul_ne_zero hl hw⟩
  rw [Subsingleton.elim g 1, map_one, map_one]
  exact LinearMap.ext fun _ => rfl

/- English proof (translation)
Take `⟨d, c⟩` from `z`. Take `rfl : d = 0` from `hz`. Set `e : Fin 0 → IrrGL k` to `Fin.elim0`. Establish `hd : ∑ a, (e a).1 = 0` using `by simp`. Rewrite using `[GlobalTheory.CompanionTheory.CsStages.jmL_eq_jm [] e (by simp) hd _]`.

Use `haveI := nontrivial_of_irreducible c.rep.irr`. Use `haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr e hd`. Use `haveI : Subsingleton (GL (Fin 0) k) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩`. Take `⟨f, hf⟩` from `exists_intertwiningMap_ne_zero c.rep.ρ (prodIrr e hd)`. Conclude with `GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA e hd _ c.rep.smooth f hf`.
-/
theorem one_le_jmL_nil (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (z : IrrGL k) (hz : z.1 = 0) : 1 ≤ jmL [] z.rep := by
  obtain ⟨d, c⟩ := z
  obtain rfl : d = 0 := hz
  let e : Fin 0 → IrrGL k := Fin.elim0
  have hd : ∑ a, (e a).1 = 0 := by simp
  rw [GlobalTheory.CompanionTheory.CsStages.jmL_eq_jm [] e (by simp) hd _]
  haveI := nontrivial_of_irreducible c.rep.irr
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr e hd
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨f, hf⟩ := exists_intertwiningMap_ne_zero c.rep.ρ (prodIrr e hd)
  exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA e hd _ c.rep.smooth f hf

/- English proof (translation)
Use `haveI := nontrivial_of_irreducible X.2.rep.irr`. Establish `hfl : HasFiniteLength X.rep` using `GlobalTheory.ProdLength.hasFiniteLength_of_injective g hg (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA z hz)`. Conclude with `one_le_jmL_append hA z hz [z 0] W X.rep X.2.rep.smooth hfl (one_le_jm_of_injective hA z hz X.rep X.2.rep.smooth g hg) (one_le_jmL_single hA _) hW`.
-/
theorem one_le_jmL_cons (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (X : IrrGL k) (z : Fin 2 → IrrGL k)
    (hz : ∑ a, (z a).1 = X.1) (g : X.rep.IntertwiningMap (prodIrr z hz)) (hg : Function.Injective g)
    (W : List (IrrGL k)) (hW : 1 ≤ jmL W (z 1).rep) : 1 ≤ jmL (z 0 :: W) X.rep := by
  haveI := nontrivial_of_irreducible X.2.rep.irr
  have hfl : HasFiniteLength X.rep :=
    GlobalTheory.ProdLength.hasFiniteLength_of_injective g hg (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA z hz)
  exact one_le_jmL_append hA z hz [z 0] W X.rep X.2.rep.smooth hfl
    (one_le_jm_of_injective hA z hz X.rep X.2.rep.smooth g hg) (one_le_jmL_single hA _) hW

/- English proof (translation)
Set `φ₁` to `x.twEquiv (absPow k s) (isSmoothChar_absPow s)`. Set `φ₂` to `prodIrrTwistEquiv y hd (absPow k s) (isSmoothChar_absPow s)`. Use `⟨φ₂.toIntertwiningMap.comp ((twistMap f _).comp φ₁.symm.toIntertwiningMap), ?_⟩` and prove the remaining obligations. Introduce `a b e`. Conclude with `φ₁.symm.injective (hf (φ₂.injective e))`.
-/
theorem exists_nu_embedding (x : IrrGL k) (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1)
    (f : x.rep.IntertwiningMap (prodIrr y hd)) (hf : Function.Injective f) (s : ℂ) :
    ∃ g : (x.nu s).rep.IntertwiningMap (prodIrr (fun a => (y a).nu s)
      (show ∑ a, ((y a).nu s).1 = (x.nu s).1 from hd)), Function.Injective g := by
  let φ₁ := x.twEquiv (absPow k s) (isSmoothChar_absPow s)
  let φ₂ := prodIrrTwistEquiv y hd (absPow k s) (isSmoothChar_absPow s)
  refine ⟨φ₂.toIntertwiningMap.comp ((twistMap f _).comp φ₁.symm.toIntertwiningMap), ?_⟩
  intro a b e
  exact φ₁.symm.injective (hf (φ₂.injective e))

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `x hx`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨[], by simp, fun s => one_le_jmL_nil hA _ hx⟩`.

Take `⟨y, hd, hy0, f, hf⟩` from `GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft hA x (by omega)`. Establish `hlt : (y 1).1 < n`. Establish `h1` using `hy0.1`. Rewrite `hd` using `[Fin.sum_univ_two]`. Use linear arithmetic over natural numbers and integers.

Take `⟨W, hWc, hW⟩` from `ih _ hlt (y 1) rfl`. Use `⟨y 0 :: W, ?_, fun s => ?_⟩` and prove the remaining obligations. Introduce `w hw`. Break down `List.mem_cons.1 hw with rfl | hw` into its components or cases. Conclude with `hy0`.

Conclude with `hWc w hw`. Take `⟨g, hg⟩` from `exists_nu_embedding x y hd f hf s`. Conclude with `one_le_jmL_cons hA (x.nu s) (fun a => (y a).nu s) hd g hg _ (hW s)`.
-/
theorem exists_word (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (n : ℕ) : ∀ x : IrrGL k, x.1 = n →
    ∃ W : List (IrrGL k), (∀ w ∈ W, w.IsCusp) ∧ ∀ s : ℂ, 1 ≤ jmL (W.map fun w => w.nu s) (x.nu s).rep := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨[], by simp, fun s => one_le_jmL_nil hA _ hx⟩
  obtain ⟨y, hd, hy0, f, hf⟩ := GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft hA x (by omega)
  have hlt : (y 1).1 < n := by
    have h1 := hy0.1
    rw [Fin.sum_univ_two] at hd
    omega
  obtain ⟨W, hWc, hW⟩ := ih _ hlt (y 1) rfl
  refine ⟨y 0 :: W, ?_, fun s => ?_⟩
  · intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hy0
    · exact hWc w hw
  obtain ⟨g, hg⟩ := exists_nu_embedding x y hd f hf s
  exact one_le_jmL_cons hA (x.nu s) (fun a => (y a).nu s) hd g hg _ (hW s)

/- English proof (translation)
Establish `h1 : 0 < shuffleCount W D` using `by exact_mod_cast hW`. Take `⟨c, hc⟩` from `Finset.card_pos.1 (by simpa [shuffleCount] using h1)`. Conclude with `⟨c, (Finset.mem_filter.1 hc).2⟩`.
-/
theorem exists_colouring {α : Type*} {h : ℕ} {W : List α} {D : Fin h → List α}
    (hW : (1 : ℕ∞) ≤ (shuffleCount W D : ℕ∞)) : ∃ c : Fin W.length → Fin h, ∀ i, Zc.Cos.sub W c i = D i := by
  classical
  have h1 : 0 < shuffleCount W D := by exact_mod_cast hW
  obtain ⟨c, hc⟩ := Finset.card_pos.1 (by simpa [shuffleCount] using h1)
  exact ⟨c, (Finset.mem_filter.1 hc).2⟩

/- English proof (translation)
Assume the negation of the conclusion as `hg`. Take `⟨α, β, β', hd₁, hd₂, hα, -, -, h₁, h₂⟩` from `hNu N V ω hs hi hg`. Take `⟨u, hu, hu'⟩` from `exists_word hA _ α rfl`. Take `⟨v, hv, hv'⟩` from `exists_word hA _ β rfl`. Take `⟨v₂, hv₂, hv₂'⟩` from `exists_word hA _ β' rfl`.

Establish `hP` using `isSmooth_prodIrr x hd`. Establish `hfl` using `GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd`. Establish `w₀ : ∀ (y : IrrGL k) (W : List (IrrGL k)), (∀ s : ℂ, 1 ≤ jmL (W.map fun w => w.nu s) (y.nu s).rep) → 1 ≤ jmL W y.rep`. Introduce `y W hW`. Establish `h0` using `hW 0`.

Establish `e : (W.map fun w => w.nu 0) = W` using `by simp`. Rewrite `h0` using `[e, IrrGL.nu_zero]`. Conclude with `h0`. Establish `m₁` using `h₁.trans (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient ![α, β] hd₁ ω _ hP hsq)`. Establish `m₂` using `h₂.trans (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient ![β', α.nu 1] hd₂ ω _ hP hsq)`.

Establish `W₁` using `one_le_jmL_append hA ![α, β] hd₁ u v _ hP hfl m₁ (w₀ _ _ hu') (w₀ _ _ hv')`. Establish `W₂` using `one_le_jmL_append hA ![β', α.nu 1] hd₂ v₂ (u.map fun w => w.nu 1) _ hP hfl m₂ (w₀ _ _ hv₂') (hu' 1)`. Establish `hune : u ≠ []`. Introduce and unpack `rfl`. Use `deg_of_one_le (w₀ _ _ hu')` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `c₁ : ∀ w ∈ u ++ v, w.IsCusp`. Introduce `w hw`. Break down `List.mem_append.1 hw with hw | hw` into its components or cases.

Conclude with `hu w hw`. Conclude with `hv w hw`. Establish `c₂ : ∀ w ∈ v₂ ++ u.map (fun w => w.nu 1), w.IsCusp`. Introduce `w hw`. Break down `List.mem_append.1 hw with hw | hw` into its components or cases.

Conclude with `hv₂ w hw`. Take `⟨t, ht, rfl⟩` from `List.mem_map.1 hw`. Conclude with `(hu t ht).nu _`. Rewrite `W₁` using `[GlobalTheory.T.segment_product_jacquet_shuffle_count hA hJ Δ x hd hL _ c₁]`. Rewrite `W₂` using `[GlobalTheory.T.segment_product_jacquet_shuffle_count hA hJ Δ x hd hL _ c₂]`.

Take `⟨f₁, hf₁⟩` from `exists_colouring W₁`. Take `⟨f₂, hf₂⟩` from `exists_colouring W₂`. Use `false_of_shift Δ hun u hune (fun w hw => ?_) (fun w hw => ?_)` and prove the remaining obligations. Take `⟨i, hwi, t, ht, hti⟩` from `exists_head_of_mem_left u v f₁ _ hf₁ hw`. Use `⟨i, hwi, ?_⟩` and prove the remaining obligations.

Rewrite `hti` using `[head?_decWord]`. Rewrite using `[Option.some.inj hti]`. Conclude with `ht`. Take `⟨j, hwj, t, ht, htj⟩` from `exists_last_of_mem_right v₂ _ f₂ _ hf₂ (List.mem_map.2 ⟨w, hw, rfl⟩)`. Use `⟨j, hwj, ?_⟩` and prove the remaining obligations.

Rewrite `htj` using `[getLast?_decWord]`. Take `⟨t', ht', rfl⟩` from `List.mem_map.1 ht`. Conclude with `⟨t', ht', (Option.some.inj htj).symm⟩`.
-/
theorem isGeneric_of_isSubquotient (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJ : LSegJacquet k)
    (hNu : GlobalTheory.BZSeg.NuPair k) {h N : ℕ} (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hun : ∀ i j, ¬ (Δ i).Linked (Δ j)) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ω : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ω) (hi : ω.IsIrreducible)
    (hsq : IsSubquotient ω (prodIrr x hd)) : IsGeneric ω := by
  by_contra hg
  obtain ⟨α, β, β', hd₁, hd₂, hα, -, -, h₁, h₂⟩ := hNu N V ω hs hi hg
  obtain ⟨u, hu, hu'⟩ := exists_word hA _ α rfl
  obtain ⟨v, hv, hv'⟩ := exists_word hA _ β rfl
  obtain ⟨v₂, hv₂, hv₂'⟩ := exists_word hA _ β' rfl
  have hP := isSmooth_prodIrr x hd
  have hfl := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  have w₀ : ∀ (y : IrrGL k) (W : List (IrrGL k)),
      (∀ s : ℂ, 1 ≤ jmL (W.map fun w => w.nu s) (y.nu s).rep) → 1 ≤ jmL W y.rep := by
    intro y W hW
    have h0 := hW 0
    have e : (W.map fun w => w.nu 0) = W := by simp
    rw [e, IrrGL.nu_zero] at h0
    exact h0
  have m₁ := h₁.trans (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient ![α, β] hd₁ ω _ hP hsq)
  have m₂ := h₂.trans (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient ![β', α.nu 1] hd₂ ω _ hP hsq)
  have W₁ := one_le_jmL_append hA ![α, β] hd₁ u v _ hP hfl m₁ (w₀ _ _ hu') (w₀ _ _ hv')
  have W₂ := one_le_jmL_append hA ![β', α.nu 1] hd₂ v₂ (u.map fun w => w.nu 1) _ hP hfl m₂ (w₀ _ _ hv₂') (hu' 1)
  have hune : u ≠ [] := by
    rintro rfl
    have := deg_of_one_le (w₀ _ _ hu')
    simp at this
    omega
  have c₁ : ∀ w ∈ u ++ v, w.IsCusp := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hu w hw
    · exact hv w hw
  have c₂ : ∀ w ∈ v₂ ++ u.map (fun w => w.nu 1), w.IsCusp := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hv₂ w hw
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
      exact (hu t ht).nu _
  rw [GlobalTheory.T.segment_product_jacquet_shuffle_count hA hJ Δ x hd hL _ c₁] at W₁
  rw [GlobalTheory.T.segment_product_jacquet_shuffle_count hA hJ Δ x hd hL _ c₂] at W₂
  obtain ⟨f₁, hf₁⟩ := exists_colouring W₁
  obtain ⟨f₂, hf₂⟩ := exists_colouring W₂
  refine false_of_shift Δ hun u hune (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨i, hwi, t, ht, hti⟩ := exists_head_of_mem_left u v f₁ _ hf₁ hw
    refine ⟨i, hwi, ?_⟩
    rw [head?_decWord] at hti
    rw [Option.some.inj hti]
    exact ht
  · obtain ⟨j, hwj, t, ht, htj⟩ := exists_last_of_mem_right v₂ _ f₂ _ hf₂ (List.mem_map.2 ⟨w, hw, rfl⟩)
    refine ⟨j, hwj, ?_⟩
    rw [getLast?_decWord] at htj
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨t', ht', (Option.some.inj htj).symm⟩

end GlobalTheory.CompanionTheory.BZSeg.NuPairIrr

open GlobalTheory.CompanionTheory.BZSeg.NuPairIrr in

/- English proof (translation)
Introduce `k _ _ _ _ hA hJ _ hNu hR hFL h N Δ x hd hun hL`. Take `⟨ψ, hψ, h1⟩` from `exists_continuous_addChar_ne_one k`. Use `haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr x hd`. Establish `hP` using `isSmooth_prodIrr x hd`. Establish `key : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin N) k) W), IsSmooth τ → HasFiniteLength τ → Nontrivial W → IsSubquotient τ (prodIrr x hd) → IsGeneric τ`.

Introduce `W _ _ τ hs hl hW hsq`. Take `⟨Y, _, _, τ', hτs, hi, q, hq⟩` from `GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient τ hs hl hW`. Take `⟨ψ', hc, h1', hg⟩` from `isGeneric_of_isSubquotient hA hJ hNu Δ x hd hun hL τ' hτs hi ((IsSubquotient.of_surjective q hq).trans hsq)`. Use `⟨ψ', hc, h1', nontrivial_twJacquet_of_surjective q.toLinearMap hq (fun u v => ?_) hg⟩` and prove the remaining obligations. Use `Submodule.subset_span ⟨u, q v, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_smul]`. Conclude with `congrArg (· - _) (q.isIntertwining _ _ (u : GL (Fin N) k) v)`. Conclude with `GlobalTheory.CompanionTheory.BZSeg.Unlinked.isIrreducible_of_generic hψ h1 (prodIrr x hd) hP (hR ψ hψ h1 h N x hd) (fun W _ _ σ f hf hW => key W σ ((IsSubquotient.of_injective f hf).isSmooth hP) (GlobalTheory.ProdLength.hasFiniteLength_of_injective f hf (hFL h N x hd)) hW (IsSubq …`.
-/
theorem GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k →
    GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.WhitRankStd k →
    GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  intro k _ _ _ _ hA hJ _ hNu hR hFL h N Δ x hd hun hL
  obtain ⟨ψ, hψ, h1⟩ := exists_continuous_addChar_ne_one k
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr x hd
  have hP := isSmooth_prodIrr x hd
  have key : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin N) k) W), IsSmooth τ →
      HasFiniteLength τ → Nontrivial W → IsSubquotient τ (prodIrr x hd) → IsGeneric τ := by
    intro W _ _ τ hs hl hW hsq
    obtain ⟨Y, _, _, τ', hτs, hi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient τ hs hl hW
    obtain ⟨ψ', hc, h1', hg⟩ := isGeneric_of_isSubquotient hA hJ hNu Δ x hd hun hL τ' hτs hi
      ((IsSubquotient.of_surjective q hq).trans hsq)
    refine ⟨ψ', hc, h1', nontrivial_twJacquet_of_surjective q.toLinearMap hq (fun u v => ?_) hg⟩
    refine Submodule.subset_span ⟨u, q v, ?_⟩
    rw [map_sub, map_smul]
    exact congrArg (· - _) (q.isIntertwining _ _ (u : GL (Fin N) k) v)
  exact GlobalTheory.CompanionTheory.BZSeg.Unlinked.isIrreducible_of_generic hψ h1 (prodIrr x hd) hP (hR ψ hψ h1 h N x hd)
    (fun W _ _ σ f hf hW => key W σ ((IsSubquotient.of_injective f hf).isSmooth hP)
      (GlobalTheory.ProdLength.hasFiniteLength_of_injective f hf (hFL h N x hd)) hW (IsSubquotient.of_injective f hf))
    (fun W _ _ τ f hf hW => key W τ ((IsSubquotient.of_surjective f hf).isSmooth hP)
      (IsFiniteLength.of_surjective (hFL h N x hd)
        (f := Representation.IntertwiningMap.equivLinearMapAsModule _ τ f) hf) hW (IsSubquotient.of_surjective f hf))

end
