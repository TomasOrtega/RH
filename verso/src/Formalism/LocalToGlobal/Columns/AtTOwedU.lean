import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_notMem Q, 1, one_notMem Q, fun x hx => by rwa [one_smul], fun x hx => by rwa [one_smul]⟩`.
-/
theorem SameAt.refl (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) : SameAt Q N N :=
  ⟨1, one_notMem Q, 1, one_notMem Q, fun x hx => by rwa [one_smul], fun x hx => by rwa [one_smul]⟩

/- English proof (translation)
Take `⟨a, ha, a', ha', h1, h2⟩` from `h`. Conclude with `⟨a', ha', a, ha, h2, h1⟩`.
-/
theorem SameAt.symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

/- English proof (translation)
Take `⟨a, ha, a', ha', h1, h2⟩` from `h`. Take `⟨b, hb, b', hb', k1, k2⟩` from `h'`. Use `⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a', fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `h1 _ (k1 _ hx)`.

Rewrite using `[mul_smul]`. Conclude with `k2 _ (h2 _ hx)`.
-/
theorem SameAt.trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', k1, k2⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]
    exact h1 _ (k1 _ hx)
  · rw [mul_smul]
    exact k2 _ (h2 _ hx)

/- English proof (translation)
Take `⟨a, ha, a', ha', h1, h2⟩` from `h`. Use `⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)`.
-/
theorem SameAt.sup {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (S : Submodule (𝓞 E) (Sp E n)) : SameAt Q (N ⊔ S) (N' ⊔ S) := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `r`. Rewrite using `[mem_conjP, mem_conjP, cO_cO]`.
-/
theorem conjP_conjP_eq (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

/- English proof (translation)
Set `I : Ideal (𝓞 E)` to `(1 : Submodule (𝓞 E) E).comap (LinearMap.toSpanSingleton (𝓞 E) E a)`. Establish `hI : ∀ s : 𝓞 E, s ∈ I ↔ s • a ∈ (1 : Submodule (𝓞 E) E)` using `fun s => Iff.rfl`. Distinguish the cases in `hT : I = ⊤`. Establish `: (1 : 𝓞 E) ∈ I` using `hT ▸ Submodule.mem_top`. Rewrite `this` using `[hI, one_smul]`.

Conclude with `this`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hT`. Take `⟨s, hs, hsa⟩` from `h ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩`. Conclude with `(hs (hIM ((hI s).2 hsa))).elim`.
-/
theorem mem_one_of_forall_heightOne {a : E}
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ s • a ∈ (1 : Submodule (𝓞 E) E)) :
    a ∈ (1 : Submodule (𝓞 E) E) := by
  let I : Ideal (𝓞 E) := (1 : Submodule (𝓞 E) E).comap (LinearMap.toSpanSingleton (𝓞 E) E a)
  have hI : ∀ s : 𝓞 E, s ∈ I ↔ s • a ∈ (1 : Submodule (𝓞 E) E) := fun s => Iff.rfl
  by_cases hT : I = ⊤
  · have : (1 : 𝓞 E) ∈ I := hT ▸ Submodule.mem_top
    rw [hI, one_smul] at this
    exact this
  · obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hT
    obtain ⟨s, hs, hsa⟩ := h ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
    exact (hs (hIM ((hI s).2 hsa))).elim

/- English proof (translation)
Rewrite using `[← algebraMap_smul E r y, map_smul, algebraMap_smul]`.
-/
theorem hStd_smul_right' (r : 𝓞 E) (x y : Sp E n) : hStd E n x (r • y) = r • hStd E n x y := by
  rw [← algebraMap_smul E r y, map_smul, algebraMap_smul]

/- English proof (translation)
Use `unimodular_eq_of_le hM hM' fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← show dual (hStd E n) M' = M' from hM', mem_dual]`. Introduce `y hy`. Apply `mem_one_of_forall_heightOne` to reduce the goal to its premises. Introduce `Q`.

Break down `h Q with ⟨a, ha, a', ha', h1, h2⟩ | ⟨a, ha, a', ha', h1, h2⟩` into its components or cases. Use `⟨a', ha', ?_⟩` and prove the remaining obligations. Establish `h3 : a' • x ∈ dual (hStd E n) M'`. Rewrite using `[show dual (hStd E n) M' = M' from hM']`. Conclude with `h2 x hx`.

Establish `h4` using `(mem_dual M' (a' • x)).1 h3 y hy`. Rewrite `h4` using `[hStd_smul_right']`. Then use the resulting hypothesis. Use `⟨cO E a, ha, ?_⟩` and prove the remaining obligations. Establish `h3 : x ∈ dual (hStd E n) M`. Rewrite using `[show dual (hStd E n) M = M from hM]`.

Conclude with `hx`. Establish `h4` using `(mem_dual M x).1 h3 (a • y) (h1 y hy)`. Rewrite `h4` using `[hStd_osmul_left, hStd_smul_right']`. Then use the resulting hypothesis.
-/
theorem isUnimodular_eq_of_sameAt {M M' : Submodule (𝓞 E) (Sp E n)} (hM : IsUnimodular (hStd E n) M)
    (hM' : IsUnimodular (hStd E n) M')
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), SameAt Q M M' ∨ SameAt (conjPrime₂ Q) M M') : M = M' := by
  refine unimodular_eq_of_le hM hM' fun x hx => ?_
  rw [← show dual (hStd E n) M' = M' from hM', mem_dual]
  intro y hy
  apply mem_one_of_forall_heightOne
  intro Q
  rcases h Q with ⟨a, ha, a', ha', h1, h2⟩ | ⟨a, ha, a', ha', h1, h2⟩
  · refine ⟨a', ha', ?_⟩
    have h3 : a' • x ∈ dual (hStd E n) M' := by
      rw [show dual (hStd E n) M' = M' from hM']
      exact h2 x hx
    have h4 := (mem_dual M' (a' • x)).1 h3 y hy
    rwa [hStd_smul_right'] at h4
  · refine ⟨cO E a, ha, ?_⟩
    have h3 : x ∈ dual (hStd E n) M := by
      rw [show dual (hStd E n) M = M from hM]
      exact hx
    have h4 := (mem_dual M x).1 h3 (a • y) (h1 y hy)
    rwa [hStd_osmul_left, hStd_smul_right'] at h4

/- English proof (translation)
Take `⟨-, -, -, h4, h5⟩` from `upN_spec hlat huni P hne hx`. Take `⟨a, ha, haP⟩` from `exists_mem_notMem hne`. Conclude with `⟨1, one_notMem P, a, haP, fun y hy => by rw [one_smul]; exact h4 hy, fun y hy => h5 (Submodule.smul_mem_smul ha hy)⟩`.
-/
theorem sameAt_upA_upN {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    {x : Sp E n} (hx : x ∈ N) : SameAt P (upA P.asIdeal N x) (upN P.asIdeal N x) := by
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hlat huni P hne hx
  obtain ⟨a, ha, haP⟩ := exists_mem_notMem hne
  exact ⟨1, one_notMem P, a, haP, fun y hy => by rw [one_smul]; exact h4 hy,
    fun y hy => h5 (Submodule.smul_mem_smul ha hy)⟩

/- English proof (translation)
Take `⟨l1, u1, s1, -, -⟩` from `upN_spec hlat huni P hne hx`. Take `⟨l1', u1', s1', -, -⟩` from `upN_spec hlat huni P' hne' hx'`. Take `⟨l2, u2, s2, -, -⟩` from `upN_spec l1 u1 P' hne' hx1'`. Take `⟨l2', u2', s2', -, -⟩` from `upN_spec l1' u1' P hne hx1`. Establish `good : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ conjPrime₂ P → Q ≠ conjPrime₂ P' → SameAt Q (upN P'.asIdeal (upN P.asIdeal N x) x') (upN P.asIdeal (upN P'.asIdeal N x') x)`.

Introduce `Q hQ hQ'`. Distinguish the cases in `h1 : Q = P`. Substitute `h1` using the available equality. Establish `a1` using `(s2 Q hPP hQ').symm`. Establish `a2` using `(sameAt_upA_upN hlat huni Q hne hx).symm`.

Establish `a3 : SameAt Q (upA Q.asIdeal N x) (upA Q.asIdeal (upN P'.asIdeal N x') x)` using `(s1' Q hPP hQ').sup _`. Establish `a4` using `sameAt_upA_upN l1' u1' Q hne hx1`. Conclude with `((a1.trans a2).trans a3).trans a4`. Distinguish the cases in `h2 : Q = P'`. Substitute `h2` using the available equality.

Establish `a1` using `(sameAt_upA_upN l1 u1 Q hne' hx1').symm`. Establish `a2 : SameAt Q (upA Q.asIdeal (upN P.asIdeal N x) x') (upA Q.asIdeal N x')` using `((s1 Q h1 hQ).symm).sup _`. Establish `a3` using `sameAt_upA_upN hlat huni Q hne' hx'`. Establish `a4` using `s2' Q h1 hQ`. Conclude with `((a1.trans a2).trans a3).trans a4`.

Conclude with `(((s2 Q h2 hQ').symm.trans (s1 Q h1 hQ).symm).trans (s1' Q h2 hQ')).trans (s2' Q h1 hQ)`. Use `isUnimodular_eq_of_sameAt u2 u2' fun Q => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : Q = conjPrime₂ P`. Use `right`. Rewrite using `[h1, conjP_conjP_eq]`.

Conclude with `good P hne.symm hPc`. Distinguish the cases in `h2 : Q = conjPrime₂ P'`. Use `right`. Rewrite using `[h2, conjP_conjP_eq]`. Conclude with `good P' hPc' hne'.symm`.

Conclude with `Or.inl (good Q h1 h2)`.
-/
theorem upN_upN_comm {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) {P P' : HeightOneSpectrum (𝓞 E)} (hne : conjPrime₂ P ≠ P)
    (hne' : conjPrime₂ P' ≠ P') (hPP : P ≠ P') (hPc : P ≠ conjPrime₂ P') (hPc' : P' ≠ conjPrime₂ P) {x x' : Sp E n}
    (hx : x ∈ N) (hx' : x' ∈ N) (hx1 : x ∈ upN P'.asIdeal N x') (hx1' : x' ∈ upN P.asIdeal N x) :
    upN P'.asIdeal (upN P.asIdeal N x) x' = upN P.asIdeal (upN P'.asIdeal N x') x := by
  obtain ⟨l1, u1, s1, -, -⟩ := upN_spec hlat huni P hne hx
  obtain ⟨l1', u1', s1', -, -⟩ := upN_spec hlat huni P' hne' hx'
  obtain ⟨l2, u2, s2, -, -⟩ := upN_spec l1 u1 P' hne' hx1'
  obtain ⟨l2', u2', s2', -, -⟩ := upN_spec l1' u1' P hne hx1
  have good : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ conjPrime₂ P → Q ≠ conjPrime₂ P' →
      SameAt Q (upN P'.asIdeal (upN P.asIdeal N x) x') (upN P.asIdeal (upN P'.asIdeal N x') x) := by
    intro Q hQ hQ'
    by_cases h1 : Q = P
    · subst h1
      have a1 := (s2 Q hPP hQ').symm
      have a2 := (sameAt_upA_upN hlat huni Q hne hx).symm
      have a3 : SameAt Q (upA Q.asIdeal N x) (upA Q.asIdeal (upN P'.asIdeal N x') x) := (s1' Q hPP hQ').sup _
      have a4 := sameAt_upA_upN l1' u1' Q hne hx1
      exact ((a1.trans a2).trans a3).trans a4
    · by_cases h2 : Q = P'
      · subst h2
        have a1 := (sameAt_upA_upN l1 u1 Q hne' hx1').symm
        have a2 : SameAt Q (upA Q.asIdeal (upN P.asIdeal N x) x') (upA Q.asIdeal N x') := ((s1 Q h1 hQ).symm).sup _
        have a3 := sameAt_upA_upN hlat huni Q hne' hx'
        have a4 := s2' Q h1 hQ
        exact ((a1.trans a2).trans a3).trans a4
      · exact (((s2 Q h2 hQ').symm.trans (s1 Q h1 hQ).symm).trans (s1' Q h2 hQ')).trans (s2' Q h1 hQ)
  refine isUnimodular_eq_of_sameAt u2 u2' fun Q => ?_
  by_cases h1 : Q = conjPrime₂ P
  · right
    rw [h1, conjP_conjP_eq]
    exact good P hne.symm hPc
  · by_cases h2 : Q = conjPrime₂ P'
    · right
      rw [h2, conjP_conjP_eq]
      exact good P' hPc' hne'.symm
    · exact Or.inl (good Q h1 h2)

end Loc

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Establish `hne1 : P.1 ≠ P'.1` using `fun h => hne (Subtype.ext h)`. Establish `hN : upN P'.1.asIdeal (upN P.1.asIdeal d.N x) x' = upN P.1.asIdeal (upN P'.1.asIdeal d.N x') x` using `upN_upN_comm hd.lat hd.uni hP.ne hP'.ne hne1 (hP'.st P) (hP.st P') hx hx' hx1 hx1'`. Take `⟨l1, u1, s1, -, -⟩` from `upN_spec hd.lat hd.uni P.1 hP.ne hx`. Take `⟨l1', u1', s1', -, -⟩` from `upN_spec hd.lat hd.uni P'.1 hP'.ne hx'`. Take `⟨-, -, s2, -, -⟩` from `upN_spec l1 u1 P'.1 hP'.ne hx1'`.

Take `⟨-, -, s2', -, -⟩` from `upN_spec l1' u1' P.1 hP.ne hx1`. Use `ext1`. Conclude with `hN`. Use function extensionality and compare the values at `Q`. Distinguish the cases in `h1 : Q = P`.

Substitute `h1` using the available equality. Rewrite using `[Deco.up_f_ne _ _ _ _ hne]`. Use function extensionality and compare the values at `y`. Rewrite using `[Deco.up_f, Deco.up_f, Deco.up_f_ne _ _ _ _ hne]`. Establish `e : localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.up P' q' x').N x) = localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x)` using `by show localization₂ Q.1.asIdeal (upN Q.1.asIdeal (upN P'.1.asIdeal d.N x') x) = _`.

Rewrite using `[← hN]`. Conclude with `(s2 Q.1 hne1 (hP'.st Q)).localization_eq`. Rewrite using `[e]`. Distinguish the cases in `h2 : Q = P'`. Substitute `h2` using the available equality.

Rewrite using `[Deco.up_f_ne _ _ _ _ h1]`. Use function extensionality and compare the values at `y`. Rewrite using `[Deco.up_f, Deco.up_f, Deco.up_f_ne _ _ _ _ h1]`. Establish `e : localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.up P q x).N x') = localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x')` using `by show localization₂ Q.1.asIdeal (upN Q.1.asIdeal (upN P.1.asIdeal d.N x) x') = _`. Rewrite using `[hN]`.

Conclude with `(s2' Q.1 hne1.symm (hP.st Q)).localization_eq`. Rewrite using `[e]`. Rewrite using `[Deco.up_f_ne _ _ _ _ h2, Deco.up_f_ne _ _ _ _ h1, Deco.up_f_ne _ _ _ _ h1, Deco.up_f_ne _ _ _ _ h2]`. Both sides reduce to the same expression.
-/
theorem Deco.Ok.up_up_comm {d : Deco E n ST SG} (hd : d.Ok) {P P' : ST} (hP : MoveHyp ST SG P)
    (hP' : MoveHyp ST SG P') (hne : P ≠ P') (q q' : 𝓞 E) {x x' : Sp E n} (hx : x ∈ d.N) (hx' : x' ∈ d.N)
    (hx1 : x ∈ upN P'.1.asIdeal d.N x') (hx1' : x' ∈ upN P.1.asIdeal d.N x) :
    (d.up P q x).up P' q' x' = (d.up P' q' x').up P q x := by
  have hne1 : P.1 ≠ P'.1 := fun h => hne (Subtype.ext h)
  have hN : upN P'.1.asIdeal (upN P.1.asIdeal d.N x) x' = upN P.1.asIdeal (upN P'.1.asIdeal d.N x') x :=
    upN_upN_comm hd.lat hd.uni hP.ne hP'.ne hne1 (hP'.st P) (hP.st P') hx hx' hx1 hx1'
  obtain ⟨l1, u1, s1, -, -⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  obtain ⟨l1', u1', s1', -, -⟩ := upN_spec hd.lat hd.uni P'.1 hP'.ne hx'
  obtain ⟨-, -, s2, -, -⟩ := upN_spec l1 u1 P'.1 hP'.ne hx1'
  obtain ⟨-, -, s2', -, -⟩ := upN_spec l1' u1' P.1 hP.ne hx1
  ext1
  · exact hN
  · funext Q
    by_cases h1 : Q = P
    · subst h1
      rw [Deco.up_f_ne _ _ _ _ hne]
      funext y
      rw [Deco.up_f, Deco.up_f, Deco.up_f_ne _ _ _ _ hne]
      have e : localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.up P' q' x').N x) = localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x) := by
        show localization₂ Q.1.asIdeal (upN Q.1.asIdeal (upN P'.1.asIdeal d.N x') x) = _
        rw [← hN]
        exact (s2 Q.1 hne1 (hP'.st Q)).localization_eq
      rw [e]
    · by_cases h2 : Q = P'
      · subst h2
        rw [Deco.up_f_ne _ _ _ _ h1]
        funext y
        rw [Deco.up_f, Deco.up_f, Deco.up_f_ne _ _ _ _ h1]
        have e : localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.up P q x).N x') = localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x') := by
          show localization₂ Q.1.asIdeal (upN Q.1.asIdeal (upN P.1.asIdeal d.N x) x') = _
          rw [hN]
          exact (s2' Q.1 hne1.symm (hP.st Q)).localization_eq
        rw [e]
      · rw [Deco.up_f_ne _ _ _ _ h2, Deco.up_f_ne _ _ _ _ h1, Deco.up_f_ne _ _ _ _ h1, Deco.up_f_ne _ _ _ _ h2]
  · rfl

/- English proof (translation)
Take `⟨x₀, hx₀, hfx₀, rfl⟩` from `h1`. Take `⟨a, ha, b, hb, hab⟩` from `exists_coprime (hP'.st P).symm`. Establish `hmk : Ideal.Quotient.mk P.1.asIdeal a = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk P.1.asIdeal), Ideal.Quotient.eq, ← hab]`. Simplify using `using Ideal.neg_mem_iff _ |>.2 hb`.

Establish `hx : a • x₀ ∈ d.N` using `d.N.smul_mem a hx₀`. Establish `hfx : d.f P (a • x₀) = 1`. Rewrite using `[hd.f_smul P a x₀ (le_locP _ _ hx₀), hmk, hfx₀, one_mul]`. Establish `hc : d.up P q x₀ = d.up P q (a • x₀)`. Apply `Deco.up_congr` to reduce the goal to its premises.

Establish `: x₀ - a • x₀ = b • x₀`. Rewrite using `[show b = 1 - a by rw [← hab]; ring, sub_smul, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul hb hx₀`. Rewrite `h2` using `[hc]`.

Establish `hd1 : (d.up P q (a • x₀)).Ok` using `hd.up P hP hq hq2 hx hfx`. Take `⟨x₀', hx₀', hfx₀', rfl⟩` from `h2`. Take `⟨l1, u1, s1, le1, -⟩` from `upN_spec hd.lat hd.uni P.1 hP.ne hx`. Establish `hne1 : P.1 ≠ P'.1` using `fun h => hne (Subtype.ext h)`. Take `⟨e, he, e', he', hee⟩` from `exists_coprime hne1`.

Establish `hmk' : Ideal.Quotient.mk P'.1.asIdeal e = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk P'.1.asIdeal), Ideal.Quotient.eq, ← hee]`. Simplify using `using Ideal.neg_mem_iff _ |>.2 he'`. Establish `hy1 : e • x₀' ∈ upN P.1.asIdeal d.N (a • x₀)` using `Submodule.smul_mem _ e hx₀'`. Establish `hy : e • x₀' ∈ d.N` using `smul_upA_mem hx he (le1 hx₀')`.

Establish `hfy1 : (d.up P q (a • x₀)).f P' (e • x₀') = 1`. Rewrite using `[hd1.f_smul P' e x₀' (le_locP _ _ hx₀'), hmk', hfx₀', one_mul]`. Establish `hfy : d.f P' (e • x₀') = 1`. Rewrite `hfy1` using `[Deco.up_f_ne _ _ _ _ hne.symm]`. Conclude with `hfy1`.

Establish `hc' : (d.up P q (a • x₀)).up P' q' x₀' = (d.up P q (a • x₀)).up P' q' (e • x₀')`. Apply `Deco.up_congr` to reduce the goal to its premises. Establish `: x₀' - e • x₀' = e' • x₀'`. Rewrite using `[show e' = 1 - e by rw [← hee]; ring, sub_smul, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem_smul he' hx₀'`. Take `⟨-, -, -, -, ge1'⟩` from `upN_spec hd.lat hd.uni P'.1 hP'.ne hy`. Establish `hx1 : a • x₀ ∈ upN P'.1.asIdeal d.N (e • x₀')` using `ge1' (Submodule.smul_mem_smul ha ((le_sup_left : d.N ≤ upA P'.1.asIdeal d.N (e • x₀')) hx₀))`. Use `⟨d.up P' q' (e • x₀'), hd.up P' hP' hq' hq2' hy hfy, ⟨e • x₀', hy, hfy, rfl⟩, a • x₀, hx1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Deco.up_f_ne _ _ _ _ hne]`.

Conclude with `hfx`. Rewrite using `[hc']`. Conclude with `hd.up_up_comm hP hP' hne q q' hx hy hx1 hy1`.
-/
theorem Deco.IsUp.diamond {d d₁ d₂ : Deco E n ST SG} (hd : d.Ok) {P P' : ST} (hP : MoveHyp ST SG P)
    (hP' : MoveHyp ST SG P') (hne : P ≠ P') {q q' : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    (hq' : q' ∈ P'.1.asIdeal) (hq2' : q' ∉ P'.1.asIdeal ^ 2) (h1 : Deco.IsUp P q d d₁)
    (h2 : Deco.IsUp P' q' d₁ d₂) : ∃ d₁' : Deco E n ST SG, d₁'.Ok ∧ Deco.IsUp P' q' d d₁' ∧ Deco.IsUp P q d₁' d₂ := by
  obtain ⟨x₀, hx₀, hfx₀, rfl⟩ := h1

  obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime (hP'.st P).symm
  have hmk : Ideal.Quotient.mk P.1.asIdeal a = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.1.asIdeal), Ideal.Quotient.eq, ← hab]
    simpa using Ideal.neg_mem_iff _ |>.2 hb
  have hx : a • x₀ ∈ d.N := d.N.smul_mem a hx₀
  have hfx : d.f P (a • x₀) = 1 := by
    rw [hd.f_smul P a x₀ (le_locP _ _ hx₀), hmk, hfx₀, one_mul]
  have hc : d.up P q x₀ = d.up P q (a • x₀) := by
    apply Deco.up_congr
    have : x₀ - a • x₀ = b • x₀ := by
      rw [show b = 1 - a by rw [← hab]; ring, sub_smul, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul hb hx₀
  rw [hc] at h2
  have hd1 : (d.up P q (a • x₀)).Ok := hd.up P hP hq hq2 hx hfx
  obtain ⟨x₀', hx₀', hfx₀', rfl⟩ := h2
  obtain ⟨l1, u1, s1, le1, -⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx

  have hne1 : P.1 ≠ P'.1 := fun h => hne (Subtype.ext h)
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hne1
  have hmk' : Ideal.Quotient.mk P'.1.asIdeal e = 1 := by
    rw [← map_one (Ideal.Quotient.mk P'.1.asIdeal), Ideal.Quotient.eq, ← hee]
    simpa using Ideal.neg_mem_iff _ |>.2 he'
  have hy1 : e • x₀' ∈ upN P.1.asIdeal d.N (a • x₀) := Submodule.smul_mem _ e hx₀'
  have hy : e • x₀' ∈ d.N := smul_upA_mem hx he (le1 hx₀')
  have hfy1 : (d.up P q (a • x₀)).f P' (e • x₀') = 1 := by
    rw [hd1.f_smul P' e x₀' (le_locP _ _ hx₀'), hmk', hfx₀', one_mul]
  have hfy : d.f P' (e • x₀') = 1 := by
    rw [Deco.up_f_ne _ _ _ _ hne.symm] at hfy1
    exact hfy1
  have hc' : (d.up P q (a • x₀)).up P' q' x₀' = (d.up P q (a • x₀)).up P' q' (e • x₀') := by
    apply Deco.up_congr
    have : x₀' - e • x₀' = e' • x₀' := by
      rw [show e' = 1 - e by rw [← hee]; ring, sub_smul, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul he' hx₀'
  obtain ⟨-, -, -, -, ge1'⟩ := upN_spec hd.lat hd.uni P'.1 hP'.ne hy
  have hx1 : a • x₀ ∈ upN P'.1.asIdeal d.N (e • x₀') :=
    ge1' (Submodule.smul_mem_smul ha ((le_sup_left : d.N ≤ upA P'.1.asIdeal d.N (e • x₀')) hx₀))
  refine ⟨d.up P' q' (e • x₀'), hd.up P' hP' hq' hq2' hy hfy, ⟨e • x₀', hy, hfy, rfl⟩, a • x₀, hx1, ?_, ?_⟩
  · rw [Deco.up_f_ne _ _ _ _ hne]
    exact hfx
  · rw [hc']
    exact hd.up_up_comm hP hP' hne q q' hx hy hx1 hy1

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
