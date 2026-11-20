import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultiplicityAtIdentity
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SymmetricFamilySpan

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Basic

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

def wjSub (w : O) (j : ℕ) : Submodule O (MvPolynomial σ (KK O)) where
  carrier := {P | InWj w P j}
  add_mem' := by
    intro P Q hP hQ m
    obtain ⟨a, ha⟩ := hP m
    obtain ⟨b, hb⟩ := hQ m
    exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add, mul_add]⟩
  zero_mem' := fun m => ⟨0, by simp⟩
  smul_mem' := by
    intro c P hP m
    obtain ⟨a, ha⟩ := hP m
    exact ⟨c * a, by rw [coeff_smul, ha, Algebra.smul_def, ← map_mul]; congr 1; ring⟩

/- English proof (translation)
Unfold `InA InWj`. Simplify using `only [pow_zero, one_mul]`.
-/
theorem inA_iff_wj (w : O) {P : MvPolynomial σ (KK O)} : InA (O := O) P ↔ InWj w P 0 := by
  unfold InA InWj
  simp only [pow_zero, one_mul]

/- English proof (translation)
Introduce `m`. Take `⟨a, ha⟩` from `h m`. Conclude with `⟨a, by rw [coeff_smul, ha, Algebra.smul_def, ← map_mul]; congr 1; ring⟩`.
-/
theorem wj_smul_pow {w : O} {j : ℕ} {P : MvPolynomial σ (KK O)} (h : InWj w P j) (e : ℕ) :
    InWj w ((w ^ e) • P) (j + e) := by
  intro m
  obtain ⟨a, ha⟩ := h m
  exact ⟨a, by rw [coeff_smul, ha, Algebra.smul_def, ← map_mul]; congr 1; ring⟩

/- English proof (translation)
Introduce `m`. Take `⟨a, ha⟩` from `h m`. Use `⟨w ^ (j - j') * a, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]`.
-/
theorem wj_mono {w : O} {j j' : ℕ} (hj : j' ≤ j) {P : MvPolynomial σ (KK O)} (h : InWj w P j) : InWj w P j' := by
  intro m
  obtain ⟨a, ha⟩ := h m
  refine ⟨w ^ (j - j') * a, ?_⟩
  rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]

/- English proof (translation)
Rewrite using `[← smul_eq_C_mul, algebraMap_smul]`.
-/
theorem C_mul_eq_smul (a : O) (P : MvPolynomial σ (KK O)) : C (algebraMap O (KK O) a) * P = a • P := by
  rw [← smul_eq_C_mul, algebraMap_smul]

end Basic

section Clean

variable (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
  (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))

def cleanSub (o : ℕ) : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) where
  carrier := {F | IsCleanAwayFromPlane X O w g o F}
  add_mem' := by
    rintro F G ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨Submodule.add_mem _ h1 k1, ?_, fun g' hg' hne => ?_⟩
    · rw [mul_add, inA_iff_wj w]
      exact (wjSub w 0).add_mem ((inA_iff_wj w).1 h2) ((inA_iff_wj w).1 k2)
    · unfold InWjRg
      rw [map_add]
      exact (wjSub w X.c).add_mem (h3 g' hg' hne) (k3 g' hg' hne)
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_, fun g' _ _ => ?_⟩
    · rw [mul_zero]; exact fun m => ⟨0, by simp⟩
    · unfold InWjRg
      rw [map_zero]
      exact (wjSub w X.c).zero_mem
  smul_mem' := by
    rintro a F ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun g' hg' hne => ?_⟩
    · rw [← algebraMap_smul (KK O) a F]
      exact Submodule.smul_mem _ _ h1
    · rw [mul_smul_comm, inA_iff_wj w]
      exact (wjSub w 0).smul_mem a ((inA_iff_wj w).1 h2)
    · unfold InWjRg
      rw [AlgHom.map_smul_of_tower]
      exact (wjSub w X.c).smul_mem a (h3 g' hg' hne)

variable {X O w g}

/- English proof (translation)
Use `⟨hF.1, ?_, hF.2.2⟩` and prove the remaining obligations. Establish `h2` using `hF.2.1`. Rewrite `h2`, the goal using `[C_mul_eq_smul, inA_iff_wj w]`. Establish `: (w ^ o') • F = (w ^ (o' - o)) • ((w ^ o) • F)`. Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel h]`.

Rewrite using `[this]`. Conclude with `(wjSub w 0).smul_mem _ h2`.
-/
theorem clean_mono {o o' : ℕ} (h : o ≤ o') {F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)}
    (hF : IsCleanAwayFromPlane X O w g o F) : IsCleanAwayFromPlane X O w g o' F := by
  refine ⟨hF.1, ?_, hF.2.2⟩
  have h2 := hF.2.1
  rw [C_mul_eq_smul, inA_iff_wj w] at h2 ⊢
  have : (w ^ o') • F = (w ^ (o' - o)) • ((w ^ o) • F) := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel h]
  rw [this]
  exact (wjSub w 0).smul_mem _ h2

/- English proof (translation)
Use `⟨?_, ?_, fun g' hg' hne => ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul (KK O) (w ^ e) F]`. Conclude with `Submodule.smul_mem _ _ hF.1`. Establish `h2` using `hF.2.1`. Rewrite `h2`, the goal using `[C_mul_eq_smul]`.

Rewrite using `[smul_smul, ← pow_add]` and apply the resulting hypothesis. Unfold `InWjRg`. Rewrite using `[AlgHom.map_smul_of_tower]`. Conclude with `(wjSub w X.c).smul_mem _ (hF.2.2 g' hg' hne)`.
-/
theorem clean_smul_pow {o e : ℕ} {F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)}
    (hF : IsCleanAwayFromPlane X O w g (o + e) F) : IsCleanAwayFromPlane X O w g o ((w ^ e) • F) := by
  refine ⟨?_, ?_, fun g' hg' hne => ?_⟩
  · rw [← algebraMap_smul (KK O) (w ^ e) F]
    exact Submodule.smul_mem _ _ hF.1
  · have h2 := hF.2.1
    rw [C_mul_eq_smul] at h2 ⊢
    rwa [smul_smul, ← pow_add]
  · unfold InWjRg
    rw [AlgHom.map_smul_of_tower]
    exact (wjSub w X.c).smul_mem _ (hF.2.2 g' hg' hne)

end Clean

section Multi

variable {O : Type} [CommRing O] [IsDomain O] {C0 CE1 CE2 : ℝ} {X : Loc}

/- English proof (translation)
Unfold `ioBlock`. Rewrite using `[map_add, mul_add]`.
-/
theorem ioBlock_add (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (u v : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)) :
    ioBlock (KK O) X.p C0 CE1 CE2 X j b (u + v) =
      ioBlock (KK O) X.p C0 CE1 CE2 X j b u + ioBlock (KK O) X.p C0 CE1 CE2 X j b v := by
  unfold ioBlock
  rw [map_add, mul_add]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SymmetricFamilySpan.symFam_span β G M hM s hs`.
-/
theorem symFam_span (β : GlobalTheory X)
    (G : ∀ j : Fin (numSeg X.TT), Set (MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)))
    (M : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)))
    (hM : ∀ s : Syms O C0 CE1 CE2 X, (∀ j, s j ∈ G j) → symFam (KK O) X.p C0 CE1 CE2 X β s ∈ M)
    (s : Syms O C0 CE1 CE2 X) (hs : ∀ j, s j ∈ Submodule.span O (G j)) :
    symFam (KK O) X.p C0 CE1 CE2 X β s ∈ M :=
  _root_.UpperTheory.Reformulated.B.SymmetricFamilySpan.symFam_span β G M hM s hs

end Multi

/- English proof (translation)
Establish `: SSg O C0 Cde CE1 CE2 X mu E o ≤ wjSub w 0`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `σ ⟨β, _, _, s, hs, rfl⟩`. Conclude with `(inA_iff_wj w).1 (symIntAt C0 CE1 CE2 X O mu β s fun j => Submodule.subset_span (hs j))`. Conclude with `this h`.
-/
theorem ssg_int {O : Type} [CommRing O] [IsDomain O] {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] {mu E : ℝ} {o : ℕ}
    (w : O) {σ : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)} (h : σ ∈ SSg O C0 Cde CE1 CE2 X mu E o) :
    InWj w σ 0 := by
  have : SSg O C0 Cde CE1 CE2 X mu E o ≤ wjSub w 0 := by
    refine Submodule.span_le.2 ?_
    rintro σ ⟨β, _, _, s, hs, rfl⟩
    exact (inA_iff_wj w).1 (symIntAt C0 CE1 CE2 X O mu β s fun j => Submodule.subset_span (hs j))
  exact this h

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn o σ hσ`. Break down `Nat.eq_zero_or_pos n with rfl | hn1` into its components or cases.

Use `⟨0, (cleanSub X O S.w g o).zero_mem, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_sub]`. Conclude with `(wjSub S.w 0).neg_mem (ssg_int S.w hσ)`. Set `M : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O))` to `{ carrier := {σ | ∃ F, IsCleanAwayFromPlane X O S.w g o F ∧ InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - σ) n} add_mem' := by`. Introduce and unpack `σ σ' ⟨F, hF, hFσ⟩ ⟨F', hF', hFσ'⟩`.

Use `⟨F + F', (cleanSub X O S.w g o).add_mem hF hF', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `(wjSub S.w n).add_mem hFσ hFσ'`. Use the proof step `zero_mem' := by`. Use `⟨0, (cleanSub X O S.w g o).zero_mem, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero, sub_zero]`. Conclude with `(wjSub S.w n).zero_mem`. Use the proof step `smul_mem' := by`. Introduce and unpack `a σ ⟨F, hF, hFσ⟩`. Use `⟨a • F, (cleanSub X O S.w g o).smul_mem a hF, ?_⟩` and prove the remaining obligations.

Rewrite using `[AlgHom.map_smul_of_tower, ← smul_sub]`. Conclude with `(wjSub S.w n).smul_mem a hFσ }`. Establish `hle : SSg O C0 Cde CE1 CE2 X (mm + (n : ℝ) * ka1 X) (((X.c - n : ℕ) : ℝ) * ka1 X) o ≤ M`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `σ ⟨β, hβ, ho, s, hs, rfl⟩`.

Take `⟨raw, τ, hraw, hτ, hcong⟩` from `hRT n hn1 hn β hβ s hs`. Establish `hF : ∀ ε ∈ Finset.Ico 1 n, ∃ F, IsCleanAwayFromPlane X O S.w g (ordFam C0 CE1 CE2 X β + ε) F ∧ InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - τ ε) (n - ε)`. Introduce `ε hε`. Establish `h1` using `(Finset.mem_Ico.1 hε).1`. Establish `h2` using `(Finset.mem_Ico.1 hε).2`.

Conclude with `ih (n - ε) (by omega) (by omega) _ _ (hτ ε hε)`. Use `choose! Fe hFe1 hFe2 using hF`. Use `⟨raw - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • Fe ε, ?_, ?_⟩` and prove the remaining obligations. Use `clean_mono ho ((cleanSub X O S.w g _).sub_mem hraw ?_)` and prove the remaining obligations. Conclude with `(cleanSub X O S.w g _).sum_mem fun ε hε => clean_smul_pow (hFe1 ε hε)`.

Establish `e1 : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (raw - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • Fe ε) - symFam (KK O) X.p C0 CE1 CE2 X β s = (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g raw - symFam (KK O) X.p C0 CE1 CE2 X β s - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • τ ε) - ∑ ε ∈ Finset …`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [AlgHom.map_smul_of_tower, smul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Use `(wjSub S.w n).sub_mem hcong ((wjSub S.w n).sum_mem fun ε hε => ?_)` and prove the remaining obligations. Establish `h2` using `(Finset.mem_Ico.1 hε).2`. Use `wj_smul_pow (hFe2 ε hε) ε` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel h2.le]`. Then use the resulting hypothesis. Conclude with `hle hσ`.
-/
theorem t44 {C0 Cde CE1 CE2 : ℝ}
    (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (mm : ℝ)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hRT : RawTailBody C0 Cde CE1 CE2 X O S.w mm g) :
    ∀ n : ℕ, n ≤ X.c → ∀ (o : ℕ),
      ∀ σ ∈ SSg O C0 Cde CE1 CE2 X (mm + (n : ℝ) * ka1 X) (((X.c - n : ℕ) : ℝ) * ka1 X) o,
      ∃ F, IsCleanAwayFromPlane X O S.w g o F ∧ InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - σ) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn o σ hσ
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · refine ⟨0, (cleanSub X O S.w g o).zero_mem, ?_⟩
      rw [map_zero, zero_sub]
      exact (wjSub S.w 0).neg_mem (ssg_int S.w hσ)
    ·
      let M : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) :=
        { carrier := {σ | ∃ F, IsCleanAwayFromPlane X O S.w g o F ∧
            InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - σ) n}
          add_mem' := by
            rintro σ σ' ⟨F, hF, hFσ⟩ ⟨F', hF', hFσ'⟩
            refine ⟨F + F', (cleanSub X O S.w g o).add_mem hF hF', ?_⟩
            rw [map_add, add_sub_add_comm]
            exact (wjSub S.w n).add_mem hFσ hFσ'
          zero_mem' := by
            refine ⟨0, (cleanSub X O S.w g o).zero_mem, ?_⟩
            rw [map_zero, sub_zero]
            exact (wjSub S.w n).zero_mem
          smul_mem' := by
            rintro a σ ⟨F, hF, hFσ⟩
            refine ⟨a • F, (cleanSub X O S.w g o).smul_mem a hF, ?_⟩
            rw [AlgHom.map_smul_of_tower, ← smul_sub]
            exact (wjSub S.w n).smul_mem a hFσ }
      have hle : SSg O C0 Cde CE1 CE2 X (mm + (n : ℝ) * ka1 X) (((X.c - n : ℕ) : ℝ) * ka1 X) o ≤ M := by
        refine Submodule.span_le.2 ?_
        rintro σ ⟨β, hβ, ho, s, hs, rfl⟩
        obtain ⟨raw, τ, hraw, hτ, hcong⟩ := hRT n hn1 hn β hβ s hs
        have hF : ∀ ε ∈ Finset.Ico 1 n, ∃ F, IsCleanAwayFromPlane X O S.w g (ordFam C0 CE1 CE2 X β + ε) F ∧
            InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - τ ε) (n - ε) := by
          intro ε hε
          have h1 := (Finset.mem_Ico.1 hε).1
          have h2 := (Finset.mem_Ico.1 hε).2
          exact ih (n - ε) (by omega) (by omega) _ _ (hτ ε hε)
        choose! Fe hFe1 hFe2 using hF
        refine ⟨raw - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • Fe ε, ?_, ?_⟩
        · refine clean_mono ho ((cleanSub X O S.w g _).sub_mem hraw ?_)
          exact (cleanSub X O S.w g _).sum_mem fun ε hε => clean_smul_pow (hFe1 ε hε)
        · have e1 : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (raw - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • Fe ε) -
              symFam (KK O) X.p C0 CE1 CE2 X β s =
              (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g raw - symFam (KK O) X.p C0 CE1 CE2 X β s -
                ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • τ ε) -
              ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (Fe ε) - τ ε) := by
            rw [map_sub, map_sum]
            simp only [AlgHom.map_smul_of_tower, smul_sub, Finset.sum_sub_distrib]
            ring
          rw [e1]
          refine (wjSub S.w n).sub_mem hcong ((wjSub S.w n).sum_mem fun ε hε => ?_)
          have h2 := (Finset.mem_Ico.1 hε).2
          have := wj_smul_pow (hFe2 ε hε) ε
          rwa [Nat.sub_add_cancel h2.le] at this
      exact hle hσ

/- English proof (translation)
Establish `hmar : 13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm = mm + (X.c : ℝ) * ka1 X`. Unfold `ka1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hs` using `[hmar]`. Establish `hσ : symFam (KK O) X.p C0 CE1 CE2 X β s ∈ SSg O C0 Cde CE1 CE2 X (mm + (X.c : ℝ) * ka1 X) (((X.c - X.c : ℕ) : ℝ) * ka1 X) (ordFam C0 CE1 CE2 X β)`.

Use `symFam_span β (fun j => genSet O (r := X.m) (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (X.c : ℝ) * ka1 X) (β j))) _ (fun s' hs' => ?_) s hs` and prove the remaining obligations. Use `Submodule.subset_span ⟨β, fun j => ?_, le_rfl, s', hs', rfl⟩` and prove the remaining obligations. Rewrite using `[Nat.sub_self, Nat.cast_zero, zero_mul]`. Conclude with `hK X hD hH hc j (β j) (hβ j)`. Conclude with `t44 X O S mm g hRT X.c le_rfl _ _ hσ`.
-/
theorem lemma44_at_body {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hK : KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hD : D1num X) (hH : HIext C0 CYb Cde Ck CD Cb X)
    (hc : CBound Cc X) (mm : ℝ) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
    (hRT : RawTailBody C0 Cde CE1 CE2 X O S.w mm g) (β : GlobalTheory X) (hβ : KeptAll C0 CE1 CE2 X β)
    (s : Syms O C0 CE1 CE2 X) (hs : InSSZ O C0 CE1 CE2 (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) X β s) :
    ∃ F, IsCleanAwayFromPlane X O S.w g (ordFam C0 CE1 CE2 X β) F ∧
      InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c := by
  have hmar : 13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm = mm + (X.c : ℝ) * ka1 X := by
    unfold ka1; ring
  rw [hmar] at hs
  have hσ : symFam (KK O) X.p C0 CE1 CE2 X β s ∈ SSg O C0 Cde CE1 CE2 X (mm + (X.c : ℝ) * ka1 X)
      (((X.c - X.c : ℕ) : ℝ) * ka1 X) (ordFam C0 CE1 CE2 X β) := by
    refine symFam_span β (fun j => genSet O (r := X.m)
      (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (mm + (X.c : ℝ) * ka1 X) (β j))) _ (fun s' hs' => ?_) s hs
    refine Submodule.subset_span ⟨β, fun j => ?_, le_rfl, s', hs', rfl⟩
    rw [Nat.sub_self, Nat.cast_zero, zero_mul]
    exact hK X hD hH hc j (β j) (hβ j)
  exact t44 X O S mm g hRT X.c le_rfl _ _ hσ

/- English proof (translation)
Introduce `X _ _ O _ _ _ _ S hSq hD hH hc mm hmm g hg β hβ s hs`. Take `⟨F, hF, hcong⟩` from `lemma44_at_body hK X O S hD hH hc mm g (hRT X O S hSq hD hH hc mm hmm g hg) β hβ s hs`. Conclude with `⟨F, hF.1, hF.2.1, hcong, hF.2.2⟩`.
-/
theorem lemma44_at_of_raw_tail {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hRT : RawTailAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hK : KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : Lemma44At C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm g hg β hβ s hs
  obtain ⟨F, hF, hcong⟩ := lemma44_at_body hK X O S hD hH hc mm g (hRT X O S hSq hD hH hc mm hmm g hg) β hβ s hs
  exact ⟨F, hF.1, hF.2.1, hcong, hF.2.2⟩

/- English proof (translation)
Introduce `X _ _ O _ _ _ _ S hSq hD hH hc mm hmm β hβ s hs`. Take `⟨F, hF, hcong⟩` from `lemma44_at_body hK X O S hD hH hc mm 1 (hRT X O S hSq hD hH hc mm hmm) β hβ s hs`. Conclude with `⟨F, hF.1, hF.2.1, hcong, hF.2.2⟩`.
-/
theorem lemma44_identity_of_raw_tail {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hRT : RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hK : KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : CoarseMultiplicityAtIdentity C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm β hβ s hs
  obtain ⟨F, hF, hcong⟩ := lemma44_at_body hK X O S hD hH hc mm 1 (hRT X O S hSq hD hH hc mm hmm) β hβ s hs
  exact ⟨F, hF.1, hF.2.1, hcong, hF.2.2⟩

/- English proof (translation)
The claim follows from `TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => lemma44_at_of_raw_tail h.1 h.2) (hRT.and hK)`.
-/
theorem lemma44_of_raw_tail_kept (hRT : RestRawTail) (hK : RestKeptBL) : BinomialRatioBeyondThreshold :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => lemma44_at_of_raw_tail h.1 h.2) (hRT.and hK)

end Formalism.MainNotions.ColumnSystems.Pf
