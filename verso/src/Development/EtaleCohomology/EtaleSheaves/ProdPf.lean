import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.ProdPf

/- English proof (translation)
Proceed by induction on `hq with`. Consider the case `iso e he`. Introduce `X P' g a q' h`. Establish `: IsIso (pullback.snd e g)` using `inferInstance`. Establish `hq' : q' = h.isoPullback.hom ≫ pullback.snd e g` using `(IsPullback.isoPullback_hom_snd h).symm`.

Rewrite using `[hq']`. Conclude with `IterLine.iso _ inferInstance`. Consider the case `comp l k hl _ ih`. Introduce `X P' g a q' h`. Establish `w : q' ≫ g = (a ≫ l) ≫ k` using `by rw [Category.assoc, ← h.w]`.

Set `m` to `pullback.lift q' (a ≫ l) w`. Establish `hb : IsPullback (pullback.snd g k) (pullback.fst g k) k g` using `(IsPullback.of_hasPullback g k).flip`. Establish `e1 : m ≫ pullback.fst g k = q'` using `pullback.lift_fst _ _ _`. Establish `e2 : m ≫ pullback.snd g k = a ≫ l` using `pullback.lift_snd _ _ _`. Establish `hs : IsPullback a (m ≫ pullback.fst g k) (l ≫ k) g`.

Rewrite using `[e1]`. Conclude with `h`. Establish `ht : IsPullback a m l (pullback.snd g k)` using `IsPullback.of_bot hs e2.symm hb`. Establish `hm : IsLine m` using `hl.bc ht`. Establish `e : q' = m ≫ pullback.fst g k` using `e1.symm`.

Rewrite using `[e]`. Conclude with `IterLine.comp _ _ hm (ih g (pullback.snd g k) (pullback.fst g k) hb)`.
-/
theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} (g : X ⟶ S) (a : P' ⟶ P) (q' : P' ⟶ X), IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' g a q' h
    have : IsIso (pullback.snd e g) := inferInstance
    have hq' : q' = h.isoPullback.hom ≫ pullback.snd e g := (IsPullback.isoPullback_hom_snd h).symm
    rw [hq']
    exact IterLine.iso _ inferInstance
  | comp l k hl _ ih =>
    intro X P' g a q' h
    have w : q' ≫ g = (a ≫ l) ≫ k := by rw [Category.assoc, ← h.w]
    let m := pullback.lift q' (a ≫ l) w
    have hb : IsPullback (pullback.snd g k) (pullback.fst g k) k g := (IsPullback.of_hasPullback g k).flip
    have e1 : m ≫ pullback.fst g k = q' := pullback.lift_fst _ _ _
    have e2 : m ≫ pullback.snd g k = a ≫ l := pullback.lift_snd _ _ _
    have hs : IsPullback a (m ≫ pullback.fst g k) (l ≫ k) g := by
      rw [e1]; exact h
    have ht : IsPullback a m l (pullback.snd g k) := IsPullback.of_bot hs e2.symm hb
    have hm : IsLine m := hl.bc ht
    have e : q' = m ≫ pullback.fst g k := e1.symm
    rw [e]
    exact IterLine.comp _ _ hm (ih g (pullback.snd g k) (pullback.fst g k) hb)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Pj qj _`. Use `⟨S, 𝟙 S, fun j => j.elim0, IterLine.iso _ inferInstance, fun j => j.elim0, ?_⟩` and prove the remaining obligations.

Introduce `T t f _`. Use `⟨t, ⟨by simp, fun j => j.elim0⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hg, -⟩`. Simplify using `using hg`. Consider the case `succ n ih`.

Introduce `Pj qj hqj`. Take `⟨P0, q0, π0, hq0, hπ0, hU0⟩` from `ih (fun j => Pj j.succ) (fun j => qj j.succ) (fun j => hqj j.succ)`. Establish `hfst : IterLine (pullback.fst q0 (qj 0))` using `iterLine_of_isPullback (hqj 0) q0 (pullback.snd q0 (qj 0)) (pullback.fst q0 (qj 0)) (IsPullback.of_hasPullback q0 (qj 0)).flip`. Set `π : ∀ j, pullback q0 (qj 0) ⟶ Pj j` to `Fin.cases (motive := fun j => pullback q0 (qj 0) ⟶ Pj j) (pullback.snd q0 (qj 0)) (fun j => pullback.fst q0 (qj 0) ≫ π0 j)`. Establish `hπ0' : π 0 = pullback.snd q0 (qj 0)` using `rfl`.

Establish `hπs : ∀ j : Fin n, π j.succ = pullback.fst q0 (qj 0) ≫ π0 j` using `fun j => rfl`. Use `⟨pullback q0 (qj 0), pullback.fst q0 (qj 0) ≫ q0, π, hI _ _ hfst hq0, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[hπ0', ← pullback.condition]`.

Rewrite using `[hπs, Category.assoc, hπ0]`. Introduce `T t f hf`. Take `⟨g0, ⟨hg0q, hg0π⟩, hu⟩` from `hU0 t (fun j => f j.succ) (fun j => hf j.succ)`. Establish `w : g0 ≫ q0 = f 0 ≫ qj 0` using `by rw [hg0q, hf 0]`. Use `⟨pullback.lift g0 (f 0) w, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, pullback.lift_fst, hg0q]`. Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[hπ0', pullback.lift_snd]`. Rewrite using `[hπs, ← Category.assoc, pullback.lift_fst, hg0π]`.

Introduce and unpack `g' ⟨hg'q, hg'π⟩`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`. Apply `hu` to reduce the goal to its premises. Use `⟨by rw [Category.assoc, hg'q], fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, ← hπs, hg'π]`. Rewrite using `[pullback.lift_snd, ← hπ0', hg'π]`.
-/
theorem exists_widePullback_of_iteratedLine (hI : IterComp) {S : Scheme.{0}} : ∀ (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S),
    (∀ j, IterLine (qj j)) →
    ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
        ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j := by
  intro n
  induction n with
  | zero =>
    intro Pj qj _
    refine ⟨S, 𝟙 S, fun j => j.elim0, IterLine.iso _ inferInstance, fun j => j.elim0, ?_⟩
    intro T t f _
    refine ⟨t, ⟨by simp, fun j => j.elim0⟩, ?_⟩
    rintro g ⟨hg, -⟩
    simpa using hg
  | succ n ih =>
    intro Pj qj hqj
    obtain ⟨P0, q0, π0, hq0, hπ0, hU0⟩ := ih (fun j => Pj j.succ) (fun j => qj j.succ) (fun j => hqj j.succ)
    have hfst : IterLine (pullback.fst q0 (qj 0)) :=
      iterLine_of_isPullback (hqj 0) q0 (pullback.snd q0 (qj 0)) (pullback.fst q0 (qj 0))
        (IsPullback.of_hasPullback q0 (qj 0)).flip
    let π : ∀ j, pullback q0 (qj 0) ⟶ Pj j :=
      Fin.cases (motive := fun j => pullback q0 (qj 0) ⟶ Pj j) (pullback.snd q0 (qj 0))
        (fun j => pullback.fst q0 (qj 0) ≫ π0 j)
    have hπ0' : π 0 = pullback.snd q0 (qj 0) := rfl
    have hπs : ∀ j : Fin n, π j.succ = pullback.fst q0 (qj 0) ≫ π0 j := fun j => rfl
    refine ⟨pullback q0 (qj 0), pullback.fst q0 (qj 0) ≫ q0, π, hI _ _ hfst hq0, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hπ0', ← pullback.condition]
      · rw [hπs, Category.assoc, hπ0]
    · intro T t f hf
      obtain ⟨g0, ⟨hg0q, hg0π⟩, hu⟩ := hU0 t (fun j => f j.succ) (fun j => hf j.succ)
      have w : g0 ≫ q0 = f 0 ≫ qj 0 := by rw [hg0q, hf 0]
      refine ⟨pullback.lift g0 (f 0) w, ⟨?_, ?_⟩, ?_⟩
      · rw [← Category.assoc, pullback.lift_fst, hg0q]
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [hπ0', pullback.lift_snd]
        · rw [hπs, ← Category.assoc, pullback.lift_fst, hg0π]
      · rintro g' ⟨hg'q, hg'π⟩
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply hu
          refine ⟨by rw [Category.assoc, hg'q], fun j => ?_⟩
          rw [Category.assoc, ← hπs, hg'π]
        · rw [pullback.lift_snd, ← hπ0', hg'π]

/- English proof (translation)
Introduce `S n Pj qj hq`. Conclude with `exists_widePullback_of_iteratedLine hI n Pj qj hq`.
-/
theorem Prod_of (hI : IterComp) : LateralTheory.E.ChowGraphCut.Prod := by
  intro S n Pj qj hq
  exact exists_widePullback_of_iteratedLine hI n Pj qj hq

end LateralTheory.E.ProdPf
end
