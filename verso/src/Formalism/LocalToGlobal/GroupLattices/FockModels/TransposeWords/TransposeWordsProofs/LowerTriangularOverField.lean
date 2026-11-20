import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas

open MvPolynomial

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
It suffices to establish `key : ∀ (k : ℕ) (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 from fun a s has => key s.val s rfl a has`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `s hs a ha`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `s hs a ha`. Establish `hk : k < n` using `by have := s.isLt; omega`. Establish `h1` using `h ⟨k, hk⟩ s (by simpa using hs) a`.

Establish `h2 : (∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n))) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b hb`. Establish `hba : b < a` using `(Finset.mem_filter.mp hb).2`. Establish `hba' : b.val < a.val` using `hba`.

Conclude with `ih ⟨k, hk⟩ rfl b (by show b.val < k; omega)`. Rewrite `h1` using `[h2, zero_add]`. Establish `h3 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s)` using `Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩)`. Use linear arithmetic over natural numbers and integers.
-/
theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  suffices key : ∀ (k : ℕ) (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 from
    fun a s has => key s.val s rfl a has
  intro k
  induction k with
  | zero =>
    intro s hs a ha
    omega
  | succ k ih =>
    intro s hs a ha
    have hk : k < n := by have := s.isLt; omega
    have h1 := h ⟨k, hk⟩ s (by simpa using hs) a
    have h2 : (∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b < a := (Finset.mem_filter.mp hb).2
      have hba' : b.val < a.val := hba
      exact ih ⟨k, hk⟩ rfl b (by show b.val < k; omega)
    rw [h2, zero_add] at h1
    have h3 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
      Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩)
    omega

/- English proof (translation)
Introduce `O K _ _ _ _ _ r n ν Q hQ`. Establish `hlead : ∀ f ∈ dualWeyl K r n ν, f ≠ 0 → LowerTri ((colLex r n).degree f)` using `fun f hf hf0 => lowerTri_of_interlaced (leadInterlaced K r n ν f hf hf0)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. It suffices to establish `key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl K r n ν, (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → coeff e f ∈ Set.range (algebraMap O K)) → (colLex r n).toSyn ((colLex r n).degree f) = d → f ∈ (dualWeyl O r n ν).map (toK O K) by`. Introduce `h`.

Conclude with `key _ Q hQ h rfl`. Introduce `d`. Proceed by induction on `d using WellFoundedLT.induction with`. Consider the case `_ d ih`. Introduce `f hf hco hd`.

Distinguish the cases in `hf0 : f = 0`. Rewrite using `[hf0]`. Conclude with `Submodule.zero_mem _`. Use `set m := (colLex r n).degree f with hm`. Establish `hint : Interlaced m` using `leadInterlaced K r n ν f hf hf0`.

Establish `hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t` using `colSums K r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)`. Take `⟨N, sz, hsz, I, hshape, hmono, hexp⟩` from `sSYTExists r n ν m hcol hint`. Take `⟨hbdeg, hblc⟩` from `column_lex_bideterminant K r n N sz hsz I hmono`. Establish `hbO : bideterminant O sz hsz I ∈ dualWeyl O r n ν`. Use `bidetMem O r n N sz hsz I` as an intermediate fact.

Rewrite `this` using `[hshape]`. Conclude with `this`. Establish `hbK : bideterminant K sz hsz I ∈ dualWeyl K r n ν`. Use `bidetMem K r n N sz hsz I` as an intermediate fact. Rewrite `this` using `[hshape]`.

Conclude with `this`. Establish `hmap : toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I` using `ldlat_map_bidet (algebraMap O K) sz hsz I`. Take `⟨c, hc⟩` from `hco m (lowerTri_of_interlaced hint)`. Establish `hc' : (colLex r n).leadingCoeff f = algebraMap O K c` using `hc.symm`. Establish `hcb : (colLex r n).leadingCoeff f • bideterminant K sz hsz I = toK O K (c • bideterminant O sz hsz I)`.

Rewrite using `[map_smul, hmap, hc', algebraMap_smul]`. Establish `hcbmem : (colLex r n).leadingCoeff f • bideterminant K sz hsz I ∈ (dualWeyl O r n ν).map (toK O K)`. Rewrite using `[hcb]`. Conclude with `Submodule.mem_map_of_mem (Submodule.smul_mem _ _ hbO)`. Use `set f' := f - (colLex r n).leadingCoeff f • bideterminant K sz hsz I with hf'`.

Establish `hf'mem : f' ∈ dualWeyl K r n ν` using `Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbK)`. Establish `hdecomp : f = f' + (colLex r n).leadingCoeff f • bideterminant K sz hsz I`. Rewrite using `[hf']`. Normalize the expressions using the abelian group laws. Rewrite using `[hdecomp]`.

Use `Submodule.add_mem _ ?_ hcbmem` and prove the remaining obligations. Distinguish the cases in `h0 : f' = 0`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `hlt` using `lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant K sz hsz I) (hbdeg.trans hexp) hblc h0`.

Use `ih _ (hd ▸ hlt) f' hf'mem ?_ rfl` and prove the remaining obligations. Introduce `e he`. Take `⟨x, hx⟩` from `hco e he`. Use `⟨x - coeff e (c • bideterminant O sz hsz I), ?_⟩` and prove the remaining obligations. Establish `hce : coeff e (toK O K (c • bideterminant O sz hsz I)) = algebraMap O K (coeff e (c • bideterminant O sz hsz I))` using `coeff_map (algebraMap O K) _ e`.

Rewrite using `[hf', coeff_sub, hcb, map_sub, hx, hce]`. Introduce `h`. Assume the negation of the conclusion as `hQ0`. Conclude with `((colLex r n).coeff_degree_ne_zero_iff).mpr hQ0 (h _ (hlead Q hQ hQ0))`.
-/
theorem lower_triangular_over_field : LowerTriK := by
  intro O K _ _ _ _ _ r n ν Q hQ
  have hlead : ∀ f ∈ dualWeyl K r n ν, f ≠ 0 → LowerTri ((colLex r n).degree f) := fun f hf hf0 =>
    lowerTri_of_interlaced (leadInterlaced K r n ν f hf hf0)
  refine ⟨?_, ?_⟩
  · suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl K r n ν,
        (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → coeff e f ∈ Set.range (algebraMap O K)) →
        (colLex r n).toSyn ((colLex r n).degree f) = d → f ∈ (dualWeyl O r n ν).map (toK O K) by
      intro h
      exact key _ Q hQ h rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hco hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      set m := (colLex r n).degree f with hm
      have hint : Interlaced m := leadInterlaced K r n ν f hf hf0
      have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
        colSums K r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨N, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
      obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant K r n N sz hsz I hmono
      have hbO : bideterminant O sz hsz I ∈ dualWeyl O r n ν := by
        have := bidetMem O r n N sz hsz I
        rw [hshape] at this
        exact this
      have hbK : bideterminant K sz hsz I ∈ dualWeyl K r n ν := by
        have := bidetMem K r n N sz hsz I
        rw [hshape] at this
        exact this
      have hmap : toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I :=
        ldlat_map_bidet (algebraMap O K) sz hsz I
      obtain ⟨c, hc⟩ := hco m (lowerTri_of_interlaced hint)
      have hc' : (colLex r n).leadingCoeff f = algebraMap O K c := hc.symm
      have hcb : (colLex r n).leadingCoeff f • bideterminant K sz hsz I = toK O K (c • bideterminant O sz hsz I) := by
        rw [map_smul, hmap, hc', algebraMap_smul]
      have hcbmem : (colLex r n).leadingCoeff f • bideterminant K sz hsz I ∈ (dualWeyl O r n ν).map (toK O K) := by
        rw [hcb]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ hbO)
      set f' := f - (colLex r n).leadingCoeff f • bideterminant K sz hsz I with hf'
      have hf'mem : f' ∈ dualWeyl K r n ν :=
        Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbK)
      have hdecomp : f = f' + (colLex r n).leadingCoeff f • bideterminant K sz hsz I := by
        rw [hf']; abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ hcbmem
      by_cases h0 : f' = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant K sz hsz I) (hbdeg.trans hexp) hblc h0
      refine ih _ (hd ▸ hlt) f' hf'mem ?_ rfl
      intro e he
      obtain ⟨x, hx⟩ := hco e he
      refine ⟨x - coeff e (c • bideterminant O sz hsz I), ?_⟩
      have hce : coeff e (toK O K (c • bideterminant O sz hsz I)) = algebraMap O K (coeff e (c • bideterminant O sz hsz I)) :=
        coeff_map (algebraMap O K) _ e
      rw [hf', coeff_sub, hcb, map_sub, hx, hce]
  · intro h
    by_contra hQ0
    exact ((colLex r n).coeff_degree_ne_zero_iff).mpr hQ0 (h _ (hlead Q hQ hQ0))

end Formalism.L2.G.Model.TS
