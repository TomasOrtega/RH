import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegLTGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

/- English proof (translation)
Introduce `bs`. Establish `h` using `hf (Fin.snoc bs b)`. Establish `he : mixedDiff (Fin.snoc bs b) f = mixedDiff bs (diffStep b f)`. Unfold `mixedDiff`. Rewrite using `[List.ofFn_succ', List.concat_eq_append, List.foldr_append]`.

Simplify using `[Fin.snoc_castSucc, Fin.snoc_last]`. Rewrite `h` using `[he]`. Then use the resulting hypothesis.
-/
theorem degLT_diffStep {K : Type*} {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1))
    (b : K → ℤ) : DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b)
  have he : mixedDiff (Fin.snoc bs b) f = mixedDiff bs (diffStep b f) := by
    unfold mixedDiff
    rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rwa [he] at h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hs : ∀ j, ∃ s ∈ q j, s ∉ p` using `fun j => Set.not_subset.mp (hne j)`. Use `choose s hsq hsp using hs`. Establish `key : ∀ i (hi : i < n + 1), ∃ t ∉ p, ∀ y ∈ N ⟨i, hi⟩, t • y = 0`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `hi`. Use `⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite `hy` using `[show (⟨0, hi⟩ : Fin (n + 1)) = 0 from Fin.ext (by simp), h0, Submodule.mem_bot]`. Simplify using `[hy]`. Consider the case `succ i ih`. Introduce `hi`. Take `⟨t, htp, ht⟩` from `ih (by omega)`.

Set `j : Fin n` to `⟨i, by omega⟩`. Use `⟨t * s j, fun hm => (hp.mem_or_mem hm).elim htp (hsp j), fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : y ∈ N j.succ` using `hy`. Rewrite `hy'` using `[(hstep j).1, Submodule.mem_sup]`. Take `⟨z, hz, w, hw, rfl⟩` from `hy'`.

Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hw`. Establish `h1 : s j • (z + r • x j) ∈ N j.castSucc`. Rewrite using `[smul_add, smul_comm (s j) r (x j)]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ hz) (Submodule.smul_mem _ _ (((hstep j).2 _).2 (hsq j)))`. Rewrite using `[mul_smul]`.

Conclude with `ht _ h1`. Take `⟨t, htp, ht⟩` from `key n (Nat.lt_succ_self n)`. Apply `htp` to reduce the goal to its premises. Apply `hann` to reduce the goal to its premises. Rewrite using `[Module.mem_annihilator]`.

Introduce `y`. Apply `ht` to reduce the goal to its premises. Rewrite using `[show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, htop]`. Discharge the goal by the elementary cases of `trivial`.
-/
theorem exists_le_of_filtration {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (h0 : N 0 = ⊥) (htop : N (Fin.last n) = ⊤)
    (hstep : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j} ∧
      ∀ s : R, s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (p : Ideal R) [hp : p.IsPrime] (hann : Module.annihilator R M ≤ p) : ∃ j, q j ≤ p := by
  by_contra hne
  push Not at hne
  have hs : ∀ j, ∃ s ∈ q j, s ∉ p := fun j => Set.not_subset.mp (hne j)
  choose s hsq hsp using hs
  have key : ∀ i (hi : i < n + 1), ∃ t ∉ p, ∀ y ∈ N ⟨i, hi⟩, t • y = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun y hy => ?_⟩
      rw [show (⟨0, hi⟩ : Fin (n + 1)) = 0 from Fin.ext (by simp), h0, Submodule.mem_bot] at hy
      simp [hy]
    | succ i ih =>
      intro hi
      obtain ⟨t, htp, ht⟩ := ih (by omega)
      let j : Fin n := ⟨i, by omega⟩
      refine ⟨t * s j, fun hm => (hp.mem_or_mem hm).elim htp (hsp j), fun y hy => ?_⟩
      have hy' : y ∈ N j.succ := hy
      rw [(hstep j).1, Submodule.mem_sup] at hy'
      obtain ⟨z, hz, w, hw, rfl⟩ := hy'
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h1 : s j • (z + r • x j) ∈ N j.castSucc := by
        rw [smul_add, smul_comm (s j) r (x j)]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hz)
          (Submodule.smul_mem _ _ (((hstep j).2 _).2 (hsq j)))
      rw [mul_smul]
      exact ht _ h1
  obtain ⟨t, htp, ht⟩ := key n (Nat.lt_succ_self n)
  apply htp
  apply hann
  rw [Module.mem_annihilator]
  intro y
  apply ht
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, htop]
  trivial

/- English proof (translation)
Introduce `d hP F _ K _ _ ι _ M _ _ _ _ _ piece hM hdim`. Take `⟨n, N, x, c, q, hN0, hNtop, hstep, hcount⟩` from `hF F K ι M piece hM`. Establish `hsum` using `hS F K ι M piece hM n N x c q hN0 hNtop (fun j => ⟨(hstep j).1, (hstep j).2.1, (hstep j).2.2.2.2⟩)`. Establish `hann : ∀ j, Module.annihilator (MRing ι F) M ≤ q j`. Introduce `j s hs`.

Use `((hstep j).2.2.2.2 s).1 ?_` and prove the remaining obligations. Rewrite using `[Module.mem_annihilator.mp hs (x j)]`. Conclude with `Submodule.zero_mem _`. Establish `hmin : ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → Module.annihilator (MRing ι F) M ≤ W → ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes ∧ ∃ j, q j = W`. Introduce `W hW hannW hdimW`.

Use `hW.isPrime` as an intermediate fact. Take `⟨p, hp, hpW⟩` from `Ideal.exists_minimalPrimes_le hannW`. Establish `: p.IsPrime` using `hp.1.1`. Take `⟨j, hjp⟩` from `exists_le_of_filtration N x q hN0 hNtop (fun j => ⟨(hstep j).2.1, (hstep j).2.2.2.2⟩) p hp.1.2`. Establish `hjW : q j = W`.

Assume the negation of the conclusion as `hne`. Establish `hlt : q j < W` using `lt_of_le_of_ne (hjp.trans hpW) hne`. Take `⟨-, -, hprime, hhom, -⟩` from `hstep j`. Use `hprime` as an intermediate fact. Establish `hrel : IsRelevant (q j)` using `fun k => (hW.relevant k).imp fun i hi hm => hi ((hjp.trans hpW) hm)`.

Establish `h1` using `hdim (q j) ⟨hprime, hhom, hrel⟩ (hann j)`. Establish `h2` using `DimStrictDrop.full (MRing ι F) (q j) W hlt`. Rewrite `h2` using `[hdimW]`. Establish `h3` using `h2.trans h1`. Establish `h4 : (((d + Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)` using `by exact_mod_cast h3`.

Establish `h5 : d + Fintype.card K + 1 ≤ d + Fintype.card K` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers. Establish `hpeq : p = W` using `le_antisymm hpW (hjW ▸ hjp)`. Conclude with `⟨hpeq ▸ hp, j, hjW⟩`. Take `⟨t, ht_def⟩ : ∃ t : Fin n → (K → ℕ) → ℤ, ∀ j a, t j a = if IsRelevant (q j) ∧ ringKrullDim (MRing ι F ⧸ q j) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then intNum F (q j) (fun _ : Fin d => fun k => (a k : ℤ)) else 0` from `⟨_, fun _ _ => rfl⟩`.

Establish `hj : ∀ j, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → |(hilbFn (q j) ((fun k => (a k : ℤ)) - c j) : ℝ) - (t j a : ℝ) / d.factorial| ≤ C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)`. Introduce `j`. Take `⟨-, -, hprime, hhom, -⟩` from `hstep j`. Distinguish the cases in `hrel : IsRelevant (q j)`. Distinguish the cases in `htop : ringKrullDim (MRing ι F ⧸ q j) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)`.

Take `⟨a₁, C₁, h₁⟩` from `hP d le_rfl F K ι (q j) ⟨hprime, hhom, hrel⟩ htop`. Establish `hlt : ringKrullDim (MRing ι F ⧸ q j) < (((d + 1) + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[htop]`. Conclude with `(by omega : d + Fintype.card K < d + 1 + Fintype.card K)` after adjusting the coercions. Establish `hdeg` using `HilbDegBound.full F K ι (d + 1) (q j) hprime hhom hlt`.

Take `⟨a₂, C₂, h₂⟩` from `hG K d _ (degLT_diffStep hdeg (c j))`. Use `⟨max a₁ a₂, C₁ + C₂, fun a ha => ?_⟩` and prove the remaining obligations. Establish `e1` using `h₁ a (fun k => le_trans (le_max_left _ _) (ha k))`. Establish `e2` using `h₂ a (fun k => le_trans (le_max_right _ _) (ha k))`. Rewrite using `[ht_def, if_pos ⟨hrel, htop⟩]`.

Simplify using `only [diffStep] at e2`. Move the coercions through the operations in `at e2`. Rewrite `e1`, `e2`, the goal using `[abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2]`. Establish `hle` using `hdim (q j) ⟨hprime, hhom, hrel⟩ (hann j)`.

Establish `hlt : ringKrullDim (MRing ι F ⧸ q j) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞)` using `lt_of_le_of_ne hle htop`. Establish `hdeg` using `HilbDegBound.full F K ι d (q j) hprime hhom hlt`. Establish `hsh` using `(DegLTClosure.full K d (hilbFn (q j)) (hilbFn (q j)) 0 (c j)).2.2.1 hdeg`. Take `⟨a₀, C, h⟩` from `hG K d _ hsh`. Use `⟨a₀, C, fun a ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[ht_def, if_neg (fun h' => htop h'.2)]`. Simplify `h a ha` using `[shiftFn]`. Establish `ht0 : ∀ a, t j a = 0` using `fun a => by rw [ht_def, if_neg (fun h' => hrel h'.1)]`. Simplify using `only [IsRelevant, not_forall, not_exists, not_not] at hrel`. Take `⟨k₀, hk₀⟩` from `hrel`.

Use `⟨(c j k₀).toNat + 1, 0, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hv : hilbFn (q j) ((fun k => (a k : ℤ)) - c j) = 0`. Apply `HilbFnVanishBlock.full F K ι (q j) k₀ hk₀` to reduce the goal to its premises. Use `ha k₀` as an intermediate fact. Simplify using `only [Pi.sub_apply]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[ht0, hv]`. Simplify using the standard rewrite rules. Use `choose A C hAC using hj`. Use `⟨Finset.univ.sup A, ∑ j, C j, fun a ha => ?_⟩` and prove the remaining obligations.

Establish `hA : ∀ j k, A j ≤ a k` using `fun j k => le_trans (Finset.le_sup (Finset.mem_univ j)) (ha k)`. Establish `hcyc : topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) = ∑ j, t j a`. Unfold `topCycleNum`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := Finset.univ.image q) ?sub]`. Use `case sub =>`.

Introduce `W hW`. Rewrite `hW` using `[Function.mem_support]`. Rewrite using `[Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Assume the negation of the conclusion as `hnot`. Apply `hW` to reduce the goal to its premises.

Rewrite using `[dif_neg]`. Introduce and unpack `⟨h1, h2, h3⟩`. Take `⟨-, j, hj⟩` from `hmin W h1 h2 h3`. Conclude with `hnot ⟨j, hj⟩`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image q) (g := q) (fun j _ => Finset.mem_image_of_mem q (Finset.mem_univ j))]`.

Use `Finset.sum_congr rfl fun W hW => ?_` and prove the remaining obligations. Take `⟨j₀, -, rfl⟩` from `Finset.mem_image.mp hW`. Establish `hfib : ∀ j ∈ Finset.univ.filter (fun j => q j = q j₀), t j a = t j₀ a`. Introduce `j hj`. Rewrite using `[ht_def, ht_def, (Finset.mem_filter.mp hj).2]`.

Rewrite using `[Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, ht_def]`. Take `⟨-, -, hprime, hhom, -⟩` from `hstep j₀`. Distinguish the cases in `htop : IsRelevant (q j₀) ∧ ringKrullDim (MRing ι F ⧸ q j₀) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)`. Establish `hc : IsMultiProjPrime (q j₀) ∧ Module.annihilator (MRing ι F) M ≤ q j₀ ∧ ringKrullDim (MRing ι F ⧸ q j₀) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)` using `⟨⟨hprime, hhom, htop.1⟩, hann j₀, htop.2⟩`. Rewrite using `[dif_pos hc, if_pos htop]`.

Establish `hm` using `(hmin _ hc.1 hc.2.1 hc.2.2).1`. Establish `hct` using `hcount (q j₀) hm`. Use `congr 1`. Rewrite using `[← hct]`. Simplify using the standard rewrite rules.

Rewrite using `[dif_neg (fun h => htop ⟨h.1.relevant, h.2.2⟩), if_neg htop, mul_zero]`. Establish `hfin : (Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) = ∑ j, (hilbFn (q j) ((fun k => (a k : ℤ)) - c j) : ℝ)`. Use `hsum (fun k => (a k : ℤ))` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[hfin, hcyc, Int.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_mul]`.

Conclude with `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hAC j a (hA j))`.
-/
theorem ModulesFromPrimes.proof (hF : MultigradedFiltration.Statement.{u, v})
    (hS : FiltrationHilbSum.Statement.{u, v}) (hG : DegLTGrowth.Statement) :
    ModulesFromPrimes.Statement.{u, v} := by
  intro d hP F _ K _ _ ι _ M _ _ _ _ _ piece hM hdim
  classical
  obtain ⟨n, N, x, c, q, hN0, hNtop, hstep, hcount⟩ := hF F K ι M piece hM
  have hsum := hS F K ι M piece hM n N x c q hN0 hNtop
    (fun j => ⟨(hstep j).1, (hstep j).2.1, (hstep j).2.2.2.2⟩)
  have hann : ∀ j, Module.annihilator (MRing ι F) M ≤ q j := by
    intro j s hs
    refine ((hstep j).2.2.2.2 s).1 ?_
    rw [Module.mem_annihilator.mp hs (x j)]
    exact Submodule.zero_mem _

  have hmin : ∀ W : Ideal (MRing ι F), IsMultiProjPrime W →
      Module.annihilator (MRing ι F) M ≤ W →
      ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes ∧ ∃ j, q j = W := by
    intro W hW hannW hdimW
    have := hW.isPrime
    obtain ⟨p, hp, hpW⟩ := Ideal.exists_minimalPrimes_le hannW
    have : p.IsPrime := hp.1.1
    obtain ⟨j, hjp⟩ := exists_le_of_filtration N x q hN0 hNtop
      (fun j => ⟨(hstep j).2.1, (hstep j).2.2.2.2⟩) p hp.1.2
    have hjW : q j = W := by
      by_contra hne
      have hlt : q j < W := lt_of_le_of_ne (hjp.trans hpW) hne
      obtain ⟨-, -, hprime, hhom, -⟩ := hstep j
      have := hprime
      have hrel : IsRelevant (q j) := fun k =>
        (hW.relevant k).imp fun i hi hm => hi ((hjp.trans hpW) hm)
      have h1 := hdim (q j) ⟨hprime, hhom, hrel⟩ (hann j)
      have h2 := DimStrictDrop.full (MRing ι F) (q j) W hlt
      rw [hdimW] at h2
      have h3 := h2.trans h1
      have h4 : (((d + Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by exact_mod_cast h3
      have h5 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
      omega
    have hpeq : p = W := le_antisymm hpW (hjW ▸ hjp)
    exact ⟨hpeq ▸ hp, j, hjW⟩

  obtain ⟨t, ht_def⟩ : ∃ t : Fin n → (K → ℕ) → ℤ, ∀ j a, t j a =
      if IsRelevant (q j) ∧
          ringKrullDim (MRing ι F ⧸ q j) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
        intNum F (q j) (fun _ : Fin d => fun k => (a k : ℤ))
      else 0 := ⟨_, fun _ _ => rfl⟩

  have hj : ∀ j, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(hilbFn (q j) ((fun k => (a k : ℤ)) - c j) : ℝ) - (t j a : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1) := by
    intro j
    obtain ⟨-, -, hprime, hhom, -⟩ := hstep j
    by_cases hrel : IsRelevant (q j)
    · by_cases htop : ringKrullDim (MRing ι F ⧸ q j) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
      ·
        obtain ⟨a₁, C₁, h₁⟩ := hP d le_rfl F K ι (q j) ⟨hprime, hhom, hrel⟩ htop
        have hlt : ringKrullDim (MRing ι F ⧸ q j) <
            (((d + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
          rw [htop]
          exact_mod_cast (by omega : d + Fintype.card K < d + 1 + Fintype.card K)
        have hdeg := HilbDegBound.full F K ι (d + 1) (q j) hprime hhom hlt
        obtain ⟨a₂, C₂, h₂⟩ := hG K d _ (degLT_diffStep hdeg (c j))
        refine ⟨max a₁ a₂, C₁ + C₂, fun a ha => ?_⟩
        have e1 := h₁ a (fun k => le_trans (le_max_left _ _) (ha k))
        have e2 := h₂ a (fun k => le_trans (le_max_right _ _) (ha k))
        rw [ht_def, if_pos ⟨hrel, htop⟩]
        simp only [diffStep] at e2
        push_cast at e2
        rw [abs_le] at e1 e2 ⊢
        constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2]
      ·
        have hle := hdim (q j) ⟨hprime, hhom, hrel⟩ (hann j)
        have hlt : ringKrullDim (MRing ι F ⧸ q j) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
          lt_of_le_of_ne hle htop
        have hdeg := HilbDegBound.full F K ι d (q j) hprime hhom hlt
        have hsh := (DegLTClosure.full K d (hilbFn (q j)) (hilbFn (q j)) 0 (c j)).2.2.1 hdeg
        obtain ⟨a₀, C, h⟩ := hG K d _ hsh
        refine ⟨a₀, C, fun a ha => ?_⟩
        rw [ht_def, if_neg (fun h' => htop h'.2)]
        simpa [shiftFn] using h a ha
    ·
      have ht0 : ∀ a, t j a = 0 := fun a => by rw [ht_def, if_neg (fun h' => hrel h'.1)]
      simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
      obtain ⟨k₀, hk₀⟩ := hrel
      refine ⟨(c j k₀).toNat + 1, 0, fun a ha => ?_⟩
      have hv : hilbFn (q j) ((fun k => (a k : ℤ)) - c j) = 0 := by
        apply HilbFnVanishBlock.full F K ι (q j) k₀ hk₀
        have := ha k₀
        simp only [Pi.sub_apply]
        omega
      rw [ht0, hv]
      simp
  choose A C hAC using hj
  refine ⟨Finset.univ.sup A, ∑ j, C j, fun a ha => ?_⟩
  have hA : ∀ j k, A j ≤ a k := fun j k => le_trans (Finset.le_sup (Finset.mem_univ j)) (ha k)

  have hcyc : topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) = ∑ j, t j a := by
    unfold topCycleNum
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image q) ?sub]
    case sub =>
      intro W hW
      rw [Function.mem_support] at hW
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      by_contra hnot
      apply hW
      rw [dif_neg]
      rintro ⟨h1, h2, h3⟩
      obtain ⟨-, j, hj⟩ := hmin W h1 h2 h3
      exact hnot ⟨j, hj⟩
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image q) (g := q)
      (fun j _ => Finset.mem_image_of_mem q (Finset.mem_univ j))]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.mp hW
    have hfib : ∀ j ∈ Finset.univ.filter (fun j => q j = q j₀), t j a = t j₀ a := by
      intro j hj
      rw [ht_def, ht_def, (Finset.mem_filter.mp hj).2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, ht_def]
    obtain ⟨-, -, hprime, hhom, -⟩ := hstep j₀
    by_cases htop : IsRelevant (q j₀) ∧
        ringKrullDim (MRing ι F ⧸ q j₀) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · have hc : IsMultiProjPrime (q j₀) ∧ Module.annihilator (MRing ι F) M ≤ q j₀ ∧
          ringKrullDim (MRing ι F ⧸ q j₀) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
        ⟨⟨hprime, hhom, htop.1⟩, hann j₀, htop.2⟩
      rw [dif_pos hc, if_pos htop]
      have hm := (hmin _ hc.1 hc.2.1 hc.2.2).1
      have hct := hcount (q j₀) hm
      congr 1
      rw [← hct]
      simp
    · rw [dif_neg (fun h => htop ⟨h.1.relevant, h.2.2⟩), if_neg htop, mul_zero]
  have hfin : (Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) =
      ∑ j, (hilbFn (q j) ((fun k => (a k : ℤ)) - c j) : ℝ) := by
    have := hsum (fun k => (a k : ℤ))
    exact_mod_cast this
  rw [hfin, hcyc, Int.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hAC j a (hA j))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
