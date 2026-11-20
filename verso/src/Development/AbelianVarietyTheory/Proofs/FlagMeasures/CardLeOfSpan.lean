import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.GenericOrder

/- English proof (translation)
Establish `hk : ∀ b, Ideal.span {g} ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q (q b))`. Introduce `b`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Simplify using `using hq b`. Set `φ : (Fin n → R ⧸ Ideal.span {g}) → Q` to `fun a => ∑ b, Submodule.liftQ (Ideal.span {g}) (LinearMap.toSpanSingleton R Q (q b)) (hk b) (a b)`.

Establish `hφ : Function.Surjective φ`. Introduce `x`. Establish `hx : x ∈ Submodule.span R (Set.range q)` using `hs ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hx`. Use `⟨fun b => Submodule.Quotient.mk (c b), ?_⟩` and prove the remaining obligations.

Simplify using `only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]`. Conclude with `hc`. Use `Nat.card_le_card_of_surjective φ hφ` as an intermediate fact. Simplify `this` using `[Nat.card_pi]`.
-/
theorem card_le_of_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (g : R) {n : ℕ}
    [Finite (R ⧸ Ideal.span {g})] (q : Fin n → Q) (hq : ∀ b, g • q b = 0)
    (hs : Submodule.span R (Set.range q) = ⊤) :
    Nat.card Q ≤ Nat.card (R ⧸ Ideal.span {g}) ^ n := by
  have hk : ∀ b, Ideal.span {g} ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q (q b)) := by
    intro b
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa using hq b
  let φ : (Fin n → R ⧸ Ideal.span {g}) → Q := fun a =>
    ∑ b, Submodule.liftQ (Ideal.span {g}) (LinearMap.toSpanSingleton R Q (q b)) (hk b) (a b)
  have hφ : Function.Surjective φ := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range q) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
    refine ⟨fun b => Submodule.Quotient.mk (c b), ?_⟩
    simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
    exact hc
  have := Nat.card_le_card_of_surjective φ hφ
  simpa [Nat.card_pi] using this

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_locP' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

/- English proof (translation)
Establish `key : ∀ J : Ideal R, (∀ P : HeightOneSpectrum R, ∃ s ∈ J, s ∉ P.asIdeal) → (1 : R) ∈ J`. Introduce `J hJ`. Assume the negation of the conclusion as `h1`. Establish `hne : J ≠ ⊤` using `fun e => h1 (e ▸ Submodule.mem_top)`. Take `⟨m, hm, hJm⟩` from `Ideal.exists_le_maximal J hne`.

Take `⟨s, hs, hs'⟩` from `hJ ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm hR⟩`. Conclude with `hs' (hJm hs)`. Set `I : Ideal R` to `⨅ b, B.comap (LinearMap.toSpanSingleton R W (w b))`. Establish `hI : ∀ s, s ∈ I ↔ ∀ b, s • w b ∈ B`. Introduce `s`.

Simplify using `[I]`. Establish `h1 : (1 : R) ∈ I ⊔ Ideal.span {g}`. Apply `key` to reduce the goal to its premises. Introduce `P`. Use `haveI := P.isPrime`.

Distinguish the cases in `hg : g ∈ P.asIdeal`. Establish `hb : ∀ b, ∃ s, s ∉ P.asIdeal ∧ s • w b ∈ B`. Introduce `b`. Rewrite using `[← mem_locP', (h P).1 hg, mem_locP']`. Conclude with `⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hwM b⟩`.

Use `choose s hs hsB using hb`. Use `⟨∏ b, s b, Submodule.mem_sup_left ((hI _).2 fun b => ?_), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ b), mul_smul]`. Conclude with `B.smul_mem _ (hsB b)`. Introduce `hm`.

Take `⟨b, -, hb⟩` from `(Ideal.IsPrime.prod_mem_iff).1 hm`. Conclude with `hs b hb`. Conclude with `⟨g, Submodule.mem_sup_right (Ideal.mem_span_singleton_self g), hg⟩`. Take `⟨c, hc, d, hd, hcd⟩` from `Submodule.mem_sup.1 h1`. Establish `hcB` using `(hI c).1 hc`.

Set `q : Fin n → B ⧸ U.comap B.subtype` to `fun b => Submodule.Quotient.mk ⟨c • w b, hcB b⟩`. Apply `card_le_of_span g q` to reduce the goal to its premises. Introduce `b`. Simplify using `only [q]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Use `show g • c • w b ∈ U`. Rewrite using `[smul_comm]`. Conclude with `U.smul_mem _ (hw b)`. Set `N : Submodule R W` to `U ⊔ Submodule.span R (Set.range fun b => c • w b)`. Establish `hcM : ∀ y ∈ M, c • y ∈ N`.

Introduce `y hy`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 (hM hy)`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hv`. Rewrite using `[smul_add, Finset.smul_sum]`. Use `N.add_mem (Submodule.mem_sup_left (U.smul_mem _ hu)) (N.sum_mem fun b _ => Submodule.mem_sup_right ?_)` and prove the remaining obligations.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`. Establish `hBN : ∀ x ∈ B, x ∈ N`. Introduce `x hx`. Establish `: (1 : R) ∈ N.comap (LinearMap.toSpanSingleton R W x)`.

Apply `key` to reduce the goal to its premises. Introduce `P`. Use `haveI := P.isPrime`. Establish `hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B` using `(mem_locP' _ _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hx⟩`. Distinguish the cases in `hg : g ∈ P.asIdeal`.

Rewrite `hxl` using `[(h P).1 hg, mem_locP']`. Take `⟨s, hs, hsx⟩` from `hxl`. Establish `hcP : c ∉ P.asIdeal`. Introduce `hcP`. Establish `hdP : d ∈ P.asIdeal`.

Use `(Ideal.span_le.2 ?_) hd` and prove the remaining obligations. Simplify using `using hg`. Conclude with `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top (hcd ▸ P.asIdeal.add_mem hcP hdP)`. Use `⟨c * s, ?_, fun hm => (P.isPrime.mem_or_mem hm).elim hcP hs⟩` and prove the remaining obligations. Use `show (c * s) • x ∈ N`.

Rewrite using `[mul_smul]`. Conclude with `hcM _ hsx`. Rewrite `hxl` using `[(h P).2 hg, mem_locP']`. Take `⟨s, hs, hsx⟩` from `hxl`. Conclude with `⟨s, (Submodule.mem_sup_left hsx : s • x ∈ N), hs⟩`.

Simplify using `using this`. Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`. Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 (hBN x hx)`.

Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hv`. Use `(Submodule.mem_span_range_iff_exists_fun R).2 ⟨a, ?_⟩` and prove the remaining obligations. Establish `e : ∑ b, a b • q b = Submodule.Quotient.mk (∑ b, a b • (⟨c • w b, hcB b⟩ : B))`. Simplify using `only [q]`. Rewrite using `[← Submodule.mkQ_apply, map_sum]`.

Simplify using `only [map_smul, Submodule.mkQ_apply]`. Rewrite using `[e, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap]`. Establish `: B.subtype (⟨x, hx⟩ - ∑ b, a b • (⟨c • w b, hcB b⟩ : B)) = u`. Simplify using `[← huv]`. Rewrite using `[this]`.

Conclude with `hu`.
-/
theorem card_quot_le {R W : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup W] [Module R W]
    (hR : ¬ IsField R) (g : R) [Finite (R ⧸ Ideal.span {g})] {n : ℕ}
    (B U M : Submodule R W) (w : Fin n → W) (hw : ∀ b, g • w b ∈ U) (hwM : ∀ b, w b ∈ M)
    (hM : M ≤ U ⊔ Submodule.span R (Set.range w))
    (h : ∀ P : HeightOneSpectrum R,
      (g ∈ P.asIdeal → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)) ∧
      (g ∉ P.asIdeal → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal U))) :
    Nat.card (B ⧸ U.comap B.subtype) ≤ Nat.card (R ⧸ Ideal.span {g}) ^ n := by
  have key : ∀ J : Ideal R, (∀ P : HeightOneSpectrum R, ∃ s ∈ J, s ∉ P.asIdeal) → (1 : R) ∈ J := by
    intro J hJ
    by_contra h1
    have hne : J ≠ ⊤ := fun e => h1 (e ▸ Submodule.mem_top)
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hs, hs'⟩ := hJ ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm hR⟩
    exact hs' (hJm hs)
  let I : Ideal R := ⨅ b, B.comap (LinearMap.toSpanSingleton R W (w b))
  have hI : ∀ s, s ∈ I ↔ ∀ b, s • w b ∈ B := by
    intro s; simp [I]
  have h1 : (1 : R) ∈ I ⊔ Ideal.span {g} := by
    apply key
    intro P
    haveI := P.isPrime
    by_cases hg : g ∈ P.asIdeal
    · have hb : ∀ b, ∃ s, s ∉ P.asIdeal ∧ s • w b ∈ B := by
        intro b
        rw [← mem_locP', (h P).1 hg, mem_locP']
        exact ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hwM b⟩
      choose s hs hsB using hb
      refine ⟨∏ b, s b, Submodule.mem_sup_left ((hI _).2 fun b => ?_), ?_⟩
      · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ b), mul_smul]
        exact B.smul_mem _ (hsB b)
      · intro hm
        obtain ⟨b, -, hb⟩ := (Ideal.IsPrime.prod_mem_iff).1 hm
        exact hs b hb
    · exact ⟨g, Submodule.mem_sup_right (Ideal.mem_span_singleton_self g), hg⟩
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.1 h1
  have hcB := (hI c).1 hc
  let q : Fin n → B ⧸ U.comap B.subtype := fun b => Submodule.Quotient.mk ⟨c • w b, hcB b⟩
  apply card_le_of_span g q
  · intro b
    simp only [q]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show g • c • w b ∈ U
    rw [smul_comm]
    exact U.smul_mem _ (hw b)
  · let N : Submodule R W := U ⊔ Submodule.span R (Set.range fun b => c • w b)
    have hcM : ∀ y ∈ M, c • y ∈ N := by
      intro y hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hM hy)
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hv
      rw [smul_add, Finset.smul_sum]
      refine N.add_mem (Submodule.mem_sup_left (U.smul_mem _ hu))
        (N.sum_mem fun b _ => Submodule.mem_sup_right ?_)
      rw [smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    have hBN : ∀ x ∈ B, x ∈ N := by
      intro x hx
      have : (1 : R) ∈ N.comap (LinearMap.toSpanSingleton R W x) := by
        apply key
        intro P
        haveI := P.isPrime
        have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B :=
          (mem_locP' _ _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hx⟩
        by_cases hg : g ∈ P.asIdeal
        · rw [(h P).1 hg, mem_locP'] at hxl
          obtain ⟨s, hs, hsx⟩ := hxl
          have hcP : c ∉ P.asIdeal := by
            intro hcP
            have hdP : d ∈ P.asIdeal := by
              refine (Ideal.span_le.2 ?_) hd
              simpa using hg
            exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top (hcd ▸ P.asIdeal.add_mem hcP hdP)
          refine ⟨c * s, ?_, fun hm => (P.isPrime.mem_or_mem hm).elim hcP hs⟩
          show (c * s) • x ∈ N
          rw [mul_smul]
          exact hcM _ hsx
        · rw [(h P).2 hg, mem_locP'] at hxl
          obtain ⟨s, hs, hsx⟩ := hxl
          exact ⟨s, (Submodule.mem_sup_left hsx : s • x ∈ N), hs⟩
      simpa using this
    rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hBN x hx)
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hv
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨a, ?_⟩
    have e : ∑ b, a b • q b = Submodule.Quotient.mk (∑ b, a b • (⟨c • w b, hcB b⟩ : B)) := by
      simp only [q]
      rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    rw [e, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap]
    have : B.subtype (⟨x, hx⟩ - ∑ b, a b • (⟨c • w b, hcB b⟩ : B)) = u := by
      simp [← huv]
    rw [this]; exact hu

/- English proof (translation)
Establish `hb` using `hF b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Use `Submodule.mem_sup_right (Submodule.subset_span ?_)` and prove the remaining obligations. Simplify using `[frame, Formalism.MainNotions.S.FlagG.fvec, hL.2]`.

Consider the case `cast i`. Use `Submodule.mem_sup_left ⟨hb, ?_⟩` and prove the remaining obligations. Establish `: frame F i.castSucc = F.fl.e i` using `by simp [frame, Formalism.MainNotions.S.FlagG.fvec]`. Rewrite using `[this]`. Conclude with `Submodule.subset_span (s := Set.range F.fl.e) ⟨i, rfl⟩`.
-/
theorem frame_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) (hL : IsLift Λ F) (hF : ∀ b, frame F b ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} := by
  have hb := hF b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [frame, Formalism.MainNotions.S.FlagG.fvec, hL.2]
  | cast i =>
    refine Submodule.mem_sup_left ⟨hb, ?_⟩
    have : frame F i.castSucc = F.fl.e i := by simp [frame, Formalism.MainNotions.S.FlagG.fvec]
    rw [this]
    exact Submodule.subset_span (s := Set.range F.fl.e) ⟨i, rfl⟩

/- English proof (translation)
Introduce `E _ _ _ S r Λ g T T' F F' hg _ hL hL' hF hF' hG`. Take `⟨ξ, -, hξ⟩` from `hG`. Establish `hcard : Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ finrank ℚ E`. Rewrite using `[← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`.

Establish `hU1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F'` using `le_sup_left.trans le_sup_left`. Establish `hU2 : XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F'` using `sup_le (le_sup_right.trans le_sup_left) le_sup_right`. Establish `hsm : ∀ (o : 𝓞 E) (x : S.V), (o : E) • x = o • x` using `fun o x => algebraMap_smul E o x`. Establish `main` using `card_quot_le (RingOfIntegers.not_isField E) (g : 𝓞 E) (BLat Λ F F') (UU Λ F F') (Mplus Λ g F F' ξ) (fun b => ((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b)) (by`. Introduce `b`.

Establish `hg' : (g : E) ≠ 0` using `Nat.cast_ne_zero.2 hg`. Establish `e : ((g : 𝓞 E) : E) = (g : E)` using `by simp`. Rewrite using `[← hsm, e, smul_smul, mul_inv_cancel₀ hg', one_smul]`. Use `Submodule.sub_mem _ (hU2 (frame_mem Λ F' hL' hF' b)) (Submodule.sum_mem _ fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[hsm]`.

Conclude with `Submodule.smul_mem _ _ (hU1 (frame_mem Λ F hL hF a)))`. Use the proof step `(fun b => Submodule.subset_span (Or.inr ⟨b, rfl⟩))`. Use the proof step `(by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ((hx | hx) | hx)`.

Conclude with `Submodule.mem_sup_left (hU1 (Submodule.mem_sup_left hx))`. Conclude with `Submodule.mem_sup_left (hU1 (Submodule.mem_sup_right (Submodule.subset_span hx)))`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span hx))`. Use `hξ`. Rewrite `main` using `[hcard]`.

Unfold `NE`. Conclude with `main` after adjusting the coercions.
-/
theorem card_BQ_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsGeneric Λ g F F' → (Nat.card (BQ Λ F F') : ℝ) ≤ NE (E := E) g ^ (r + 1) := by
  intro E _ _ _ S r Λ g T T' F F' hg _ hL hL' hF hF' hG
  obtain ⟨ξ, -, hξ⟩ := hG
  have hcard : Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ finrank ℚ E := by
    rw [← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hU1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F' :=
    le_sup_left.trans le_sup_left
  have hU2 : XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F' :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hsm : ∀ (o : 𝓞 E) (x : S.V), (o : E) • x = o • x := fun o x => algebraMap_smul E o x
  have main := card_quot_le (RingOfIntegers.not_isField E) (g : 𝓞 E) (BLat Λ F F') (UU Λ F F')
    (Mplus Λ g F F' ξ) (fun b => ((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b))
    (by
      intro b
      have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
      have e : ((g : 𝓞 E) : E) = (g : E) := by simp
      rw [← hsm, e, smul_smul, mul_inv_cancel₀ hg', one_smul]
      refine Submodule.sub_mem _ (hU2 (frame_mem Λ F' hL' hF' b)) (Submodule.sum_mem _ fun a _ => ?_)
      rw [hsm]
      exact Submodule.smul_mem _ _ (hU1 (frame_mem Λ F hL hF a)))
    (fun b => Submodule.subset_span (Or.inr ⟨b, rfl⟩))
    (by
      refine Submodule.span_le.2 ?_
      rintro x ((hx | hx) | hx)
      · exact Submodule.mem_sup_left (hU1 (Submodule.mem_sup_left hx))
      · exact Submodule.mem_sup_left (hU1 (Submodule.mem_sup_right (Submodule.subset_span hx)))
      · exact Submodule.mem_sup_right (Submodule.subset_span hx))
    hξ
  rw [hcard] at main
  unfold NE
  exact_mod_cast main

end GlobalTheory.GenericOrder
