import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL k := Δ.first.nu (n : ℂ)

/- English proof (translation)
Introduce `a b h` and use `GlobalTheory.T.cuspidal_twist_injective PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h`.
-/
theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  GlobalTheory.T.cuspidal_twist_injective PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

/- English proof (translation)
Simplify using `[tN]`.
-/
theorem tN_zero (Δ : Segment k) : tN Δ 0 = Δ.first := by
  simp [tN]

/- English proof (translation)
Establish `key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) → ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q`. Introduce `p q hpq`. Rewrite using `[← List.map_coe_finRange_eq_range, List.filter_map]`. Use `congr 1`. Conclude with `List.filter_congr fun a _ => hpq a`.

Establish `hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S` using `fun a => Finset.mem_map' Fin.valEmbedding`. Unfold `vWord AltC.wN`. Rewrite using `[← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]), ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]), ← List.map_reverse, ← List.map_append, List.map_map]`. Both sides reduce to the same expression.
-/
theorem vWord_eq (Δ : Segment k) (S : Finset (Fin Δ.len)) :
    vWord Δ S = (AltC.wN Δ.len (S.map Fin.valEmbedding)).map (tN Δ) := by
  have key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) →
      ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q := by
    intro p q hpq
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    congr 1
    exact List.filter_congr fun a _ => hpq a
  have hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S := fun a => Finset.mem_map' Fin.valEmbedding
  unfold vWord AltC.wN
  rw [← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← List.map_reverse, ← List.map_append, List.map_map]
  rfl

/- English proof (translation)
Unfold `decWord`. Rewrite using `[List.map_reverse]`. Use `congr 1`. Apply `List.ext_getElem (by simp)` to reduce the goal to its premises. Introduce `n h1 h2`.

Simplify using `only [List.getElem_ofFn, List.getElem_map, List.getElem_range']`. Rewrite using `[Segment.term, hb, tN, tN]`. Simplify using `[Nat.cast_add]`.
-/
theorem decWord_eq (Δ Γ : Segment k) (b : ℕ) (hb : Γ.first = tN Δ b) :
    decWord Γ = ((List.range' b Γ.len).reverse).map (tN Δ) := by
  unfold decWord
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
  rw [Segment.term, hb, tN, tN]
  simp [Nat.cast_add]

/- English proof (translation)
Unfold `decWord`. Rewrite using `[List.mem_reverse, List.mem_ofFn]`. Conclude with `⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩`.
-/
theorem first_mem_decWord (Γ : Segment k) : Γ.first ∈ decWord Γ := by
  unfold decWord
  rw [List.mem_reverse, List.mem_ofFn]
  exact ⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩

end PositivityTheory.Groth.AltS

namespace PositivityTheory.Groth

open AltS

/- English proof (translation)
Introduce `Δ h Γ`. Establish `hW : ∀ S, (vWord Δ S).Nodup` using `fun S => by`. Rewrite using `[vWord_eq]`. Conclude with `(AltC.nodup_wN _ _).map (tN_injective Δ)`. Establish `hmapiff : (Finset.univ.val.map Γ = {Δ}) ↔ h = 1 ∧ ∀ i, Γ i = Δ`.

Rewrite using `[← Multiset.replicate_one, Multiset.eq_replicate]`. Simplify using the standard rewrite rules. Distinguish the cases in `hex : ∀ i, ∃ n, (Γ i).first = tN Δ n`. Use `choose b hb using hex`. Establish `hd : ∀ i, decWord (Γ i) = ((List.range' (b i) (Γ i).len).reverse).map (tN Δ)` using `fun i => decWord_eq Δ (Γ i) (b i) (hb i)`.

Establish `H` using `AltC.altSumN Δ.len Δ.len_pos (vSets Δ) (by intro S; simp [vSets]) b (fun i => (Γ i).len) (fun i => (Γ i).len_pos) (fun S => (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ)) (by`. Introduce `S`. Use `congr 1`. Rewrite using `[AltC.shuffleCount_eq _ _ (hW S)]`. Establish `e : ((∀ i, (decWord (Γ i)).Sublist (vWord Δ S)) ∧ ∀ x ∈ vWord Δ S, ∃! i, x ∈ decWord (Γ i)) ↔ AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)`.

Simplify using `only [hd, vWord_eq]`. Rewrite using `[AltC.cond_map (tN Δ) (tN_injective Δ)]`. Both sides reduce to the same expression. Distinguish the cases in `hC : AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)`. Rewrite using `[if_pos (e.2 hC), if_pos hC]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (mt e.1 hC), if_neg hC]`. Use the proof step `simp)`. Rewrite using `[H]`. Establish `hiff : (h = 1 ∧ ∀ i, b i = 0 ∧ (Γ i).len = Δ.len) ↔ Finset.univ.val.map Γ = {Δ}`.

Rewrite using `[hmapiff]`. Use `and_congr_right fun _ => forall_congr' fun i => ⟨fun ⟨h0, hl⟩ => ?_, fun he => ⟨?_, by rw [he]⟩⟩` and prove the remaining obligations. Conclude with `Segment.ext_first (by rw [hb i, h0, tN_zero]) hl`. Conclude with `tN_injective Δ (by rw [← hb i, he, tN_zero])`. Distinguish the cases in `hc : Finset.univ.val.map Γ = {Δ}`.

Rewrite using `[if_pos (hiff.2 hc), if_pos hc]`. Rewrite using `[if_neg (mt hiff.1 hc), if_neg hc]`. Use `push Not at hex`. Take `⟨i, hi⟩` from `hex`. Rewrite using `[if_neg]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `S _`. Rewrite using `[AltC.shuffleCount_eq _ _ (hW S), if_neg]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨hs, _⟩`.

Use `(hs i).subset (first_mem_decWord (Γ i))` as an intermediate fact. Rewrite `this` using `[vWord_eq, List.mem_map]`. Take `⟨n, _, hn⟩` from `this`. Conclude with `hi n hn.symm`. Rewrite using `[hmapiff]`.

Introduce and unpack `⟨_, hall⟩`. Conclude with `hi 0 (by rw [hall i, tN_zero])`.
-/
theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  intro Δ h Γ
  have hW : ∀ S, (vWord Δ S).Nodup := fun S => by
    rw [vWord_eq]; exact (AltC.nodup_wN _ _).map (tN_injective Δ)
  have hmapiff : (Finset.univ.val.map Γ = {Δ}) ↔ h = 1 ∧ ∀ i, Γ i = Δ := by
    rw [← Multiset.replicate_one, Multiset.eq_replicate]
    simp
  by_cases hex : ∀ i, ∃ n, (Γ i).first = tN Δ n
  · choose b hb using hex
    have hd : ∀ i, decWord (Γ i) = ((List.range' (b i) (Γ i).len).reverse).map (tN Δ) :=
      fun i => decWord_eq Δ (Γ i) (b i) (hb i)
    have H := AltC.altSumN Δ.len Δ.len_pos (vSets Δ) (by intro S; simp [vSets]) b (fun i => (Γ i).len)
      (fun i => (Γ i).len_pos)
      (fun S => (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ)) (by
        intro S
        congr 1
        rw [AltC.shuffleCount_eq _ _ (hW S)]
        have e : ((∀ i, (decWord (Γ i)).Sublist (vWord Δ S)) ∧ ∀ x ∈ vWord Δ S, ∃! i, x ∈ decWord (Γ i)) ↔
            AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len) := by
          simp only [hd, vWord_eq]
          rw [AltC.cond_map (tN Δ) (tN_injective Δ)]
          rfl
        by_cases hC : AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)
        · rw [if_pos (e.2 hC), if_pos hC]; simp
        · rw [if_neg (mt e.1 hC), if_neg hC]; simp)
    rw [H]
    have hiff : (h = 1 ∧ ∀ i, b i = 0 ∧ (Γ i).len = Δ.len) ↔ Finset.univ.val.map Γ = {Δ} := by
      rw [hmapiff]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun ⟨h0, hl⟩ => ?_, fun he => ⟨?_, by rw [he]⟩⟩
      · exact Segment.ext_first (by rw [hb i, h0, tN_zero]) hl
      · exact tN_injective Δ (by rw [← hb i, he, tN_zero])
    by_cases hc : Finset.univ.val.map Γ = {Δ}
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (mt hiff.1 hc), if_neg hc]
  · push Not at hex
    obtain ⟨i, hi⟩ := hex
    rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [AltC.shuffleCount_eq _ _ (hW S), if_neg]
      · simp
      rintro ⟨hs, _⟩
      have := (hs i).subset (first_mem_decWord (Γ i))
      rw [vWord_eq, List.mem_map] at this
      obtain ⟨n, _, hn⟩ := this
      exact hi n hn.symm
    · rw [hmapiff]
      rintro ⟨_, hall⟩
      exact hi 0 (by rw [hall i, tN_zero])

end PositivityTheory.Groth

end
