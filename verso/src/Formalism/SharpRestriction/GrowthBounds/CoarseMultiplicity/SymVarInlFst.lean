import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

/- English proof (translation)
Rewrite using `[y.as_sum, map_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[rename_monomial]`. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises. Establish `hdS : ∀ i, multideg d i = dd i` using `(mem_restrictSupport_iff K).1 hy hd`.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • ω i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _), Finsupp.sum_fintype _ (fun a m => m • ω (chainEmb N r t a)) (fun _ => zero_smul _ _)]`. Simplify using `only [chainEmb, h1, smul_eq_mul]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← hdS a, multideg, Finset.sum_mul]`.
-/
private theorem isWeightedHomogeneous_rename_chainEmb_of_mem_Pol {K : Type} [CommSemiring K] {N r t : ℕ} (ω : BVar N r t → ℕ)
    (ωL : Fin (N + 1) → ℕ) (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a) (dd : Fin N → ℕ)
    (y : MvPolynomial (Fin N × Fin r) K) (hy : y ∈ Pol K r dd) :
    IsWeightedHomogeneous ω (rename (chainEmb N r t) y) (∑ a : Fin N, dd a * ωL a.castSucc) := by
  rw [y.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  have hdS : ∀ i, multideg d i = dd i := (mem_restrictSupport_iff K).1 hy hd
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • ω i)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_fintype _ (fun a m => m • ω (chainEmb N r t a)) (fun _ => zero_smul _ _)]
  simp only [chainEmb, h1, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hdS a, multideg, Finset.sum_mul]

/- English proof (translation)
Rewrite using `[g.as_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises. Take `⟨hsupp, hsum⟩` from `(mem_restrictSupport_iff K).1 hg hd`. Rewrite using `[Finsupp.weight_apply, ← hsum, Finset.sum_mul, Finsupp.sum]`.

Establish `hv : ∀ v ∈ d.support, d v • ω v = d v * ωL (Fin.last N)`. Introduce `v hv`. Take `⟨c, rfl⟩` from `hsupp v hv`. Simplify using `[xiVar, h1]`. Rewrite using `[Finset.sum_congr rfl hv]`.

Establish `hinj : Function.Injective (xiVar N r t)` using `fun a b h => by simpa [xiVar] using h`. Rewrite using `[← Finset.sum_image (f := fun v => d v * ωL (Fin.last N)) (fun a _ b _ h => hinj h)]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `v hv`. Take `⟨c, rfl⟩` from `hsupp v hv`.

Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ c)`. Introduce `v _ hv`. Simplify using `at hv`. Simplify using `[hv]`.
-/
private theorem isWeightedHomogeneous_of_mem_restrictSupport_xiVar {K : Type} [CommSemiring K] {N r t : ℕ} (ω : BVar N r t → ℕ)
    (ωL : Fin (N + 1) → ℕ) (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a) (B : ℕ)
    (g : MvPolynomial (BVar N r t) K)
    (hg : g ∈ restrictSupport K {m : BVar N r t →₀ ℕ |
      (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c : Fin r, m (xiVar N r t c) = B}) :
    IsWeightedHomogeneous ω g (B * ωL (Fin.last N)) := by
  classical
  rw [g.as_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  apply isWeightedHomogeneous_monomial
  obtain ⟨hsupp, hsum⟩ := (mem_restrictSupport_iff K).1 hg hd
  rw [Finsupp.weight_apply, ← hsum, Finset.sum_mul, Finsupp.sum]
  have hv : ∀ v ∈ d.support, d v • ω v = d v * ωL (Fin.last N) := by
    intro v hv
    obtain ⟨c, rfl⟩ := hsupp v hv
    simp [xiVar, h1]
  rw [Finset.sum_congr rfl hv]
  have hinj : Function.Injective (xiVar N r t) := fun a b h => by simpa [xiVar] using h
  rw [← Finset.sum_image (f := fun v => d v * ωL (Fin.last N)) (fun a _ b _ h => hinj h)]
  apply Finset.sum_subset
  · intro v hv
    obtain ⟨c, rfl⟩ := hsupp v hv
    exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
  · intro v _ hv
    simp at hv
    simp [hv]

/- English proof (translation)
Use `set corr : Fin (2 * s + 1) → ℕ := fun a => ∑ i, if (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1 then jj i else 0 with hcorr`. Establish `hc : ∀ a, corr a ≤ deg a ∧ ((a : ℕ) = 2 * s → corr a = 0)`. Introduce `a`. Distinguish the cases in `hex : ∃ i, (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1`. Take `⟨i, hi⟩` from `hex`.

Establish `hsum : corr a = jj i`. Simplify using `only [hcorr]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[hi]`. Introduce `i' _ hne`.

Rewrite using `[if_neg]`. Introduce `h'`. Apply `hne` to reduce the goal to its premises. Apply `hu` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish `hlt` using `(u i).isLt`. Use `⟨by rw [hsum]; exact hj i a hi, fun h2 => by omega⟩` and prove the remaining obligations. Use `push_neg at hex`.

Establish `h0 : corr a = 0` using `Finset.sum_eq_zero fun i _ => if_neg (by have := hex i; omega)`. Conclude with `⟨by rw [h0]; exact Nat.zero_le _, fun _ => h0⟩`. Establish `hsplit : ∀ a, deg a = ((deg a - corr a) - if a = ⟨2 * s, by omega⟩ then jp else 0) + corr a + (if a = ⟨2 * s, by omega⟩ then jp else 0)`. Introduce `a`. Take `⟨h1, h2⟩` from `hc a`.

Use `split_ifs with ha`. Establish `ha' : (a : ℕ) = 2 * s` using `by rw [ha]`. Establish `h3` using `h2 ha'`. Establish `h4` using `hjp a ha'`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hfold : ∑ a : Fin (2 * s + 1), corr a * f a.castSucc = ∑ i, jj i * (f (finPos (2 * s + 1) (2 * u i)) + f (finPos (2 * s + 1) (2 * u i + 1)))`. Simplify using `only [hcorr, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hi` using `(u i).isLt`. Establish `hz : ∀ a : Fin (2 * s + 1), a ≠ ⟨2 * u i, by omega⟩ ∧ a ≠ ⟨2 * u i + 1, by omega⟩ → (if (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1 then jj i else 0) * f a.castSucc = 0`. Introduce and unpack `a ⟨ha1, ha2⟩`. Rewrite using `[if_neg, zero_mul]`. Rewrite `ha1`, `ha2` using `[Ne, Fin.ext_iff]`.

Simplify using `only at ha1 ha2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Fintype.sum_eq_add _ _ (by rw [Ne, Fin.ext_iff]; simp) hz]`. Establish `e1 : finPos (2 * s + 1) (2 * u i) = (⟨2 * u i, by omega⟩ : Fin (2 * s + 1)).castSucc`. Apply `Fin.ext` to reduce the goal to its premises.

Apply the tactic sequence `simp [finPos] <;> omega`. Establish `e2 : finPos (2 * s + 1) (2 * u i + 1) = (⟨2 * u i + 1, by omega⟩ : Fin (2 * s + 1)).castSucc`. Apply `Fin.ext` to reduce the goal to its premises. Apply the tactic sequence `simp [finPos] <;> omega`. Rewrite using `[e1, e2, mul_add]`.

Apply the tactic sequence `congr 1 <;> simp`. Establish `hjp' : ∑ a : Fin (2 * s + 1), (if a = ⟨2 * s, by omega⟩ then jp else 0) * f a.castSucc = jp * f (⟨2 * s, by omega⟩ : Fin (2 * s + 1)).castSucc`. Simplify using `[ite_mul]`. Rewrite using `[← hfold, ← hjp', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `conv_rhs => rw [hsplit a]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_deg_sub_mul_add_eq_sum_deg_mul {s t : ℕ} (u : Fin t → Fin s) (hu : Function.Injective u)
    (deg : Fin (2 * s + 1) → ℕ) (jj : Fin t → ℕ) (jp : ℕ) (f : Fin (2 * s + 1 + 1) → ℕ)
    (hj : ∀ i (a : Fin (2 * s + 1)), ((a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1) → jj i ≤ deg a)
    (hjp : ∀ a : Fin (2 * s + 1), (a : ℕ) = 2 * s → jp ≤ deg a) :
    ∑ i, jj i * (f (finPos (2 * s + 1) (2 * u i)) + f (finPos (2 * s + 1) (2 * u i + 1))) +
      jp * f (⟨2 * s, by omega⟩ : Fin (2 * s + 1)).castSucc +
      ∑ a : Fin (2 * s + 1), ((deg a - ∑ i, if (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1 then jj i else 0) -
        if a = ⟨2 * s, by omega⟩ then jp else 0) * f a.castSucc =
    ∑ a : Fin (2 * s + 1), deg a * f a.castSucc := by
  set corr : Fin (2 * s + 1) → ℕ :=
    fun a => ∑ i, if (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1 then jj i else 0 with hcorr
  have hc : ∀ a, corr a ≤ deg a ∧ ((a : ℕ) = 2 * s → corr a = 0) := by
    intro a
    by_cases hex : ∃ i, (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1
    · obtain ⟨i, hi⟩ := hex
      have hsum : corr a = jj i := by
        simp only [hcorr]
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro i' _ hne
          rw [if_neg]
          intro h'
          apply hne
          apply hu
          apply Fin.ext
          omega
        · simp
      have hlt := (u i).isLt
      refine ⟨by rw [hsum]; exact hj i a hi, fun h2 => by omega⟩
    · push_neg at hex
      have h0 : corr a = 0 := Finset.sum_eq_zero fun i _ => if_neg (by have := hex i; omega)
      exact ⟨by rw [h0]; exact Nat.zero_le _, fun _ => h0⟩
  have hsplit : ∀ a, deg a = ((deg a - corr a) - if a = ⟨2 * s, by omega⟩ then jp else 0) + corr a +
      (if a = ⟨2 * s, by omega⟩ then jp else 0) := by
    intro a
    obtain ⟨h1, h2⟩ := hc a
    split_ifs with ha
    · have ha' : (a : ℕ) = 2 * s := by rw [ha]
      have h3 := h2 ha'
      have h4 := hjp a ha'
      omega
    · omega
  have hfold : ∑ a : Fin (2 * s + 1), corr a * f a.castSucc =
      ∑ i, jj i * (f (finPos (2 * s + 1) (2 * u i)) + f (finPos (2 * s + 1) (2 * u i + 1))) := by
    simp only [hcorr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := (u i).isLt
    have hz : ∀ a : Fin (2 * s + 1), a ≠ ⟨2 * u i, by omega⟩ ∧ a ≠ ⟨2 * u i + 1, by omega⟩ →
        (if (a : ℕ) = 2 * u i ∨ (a : ℕ) = 2 * u i + 1 then jj i else 0) * f a.castSucc = 0 := by
      rintro a ⟨ha1, ha2⟩
      rw [if_neg, zero_mul]
      rw [Ne, Fin.ext_iff] at ha1 ha2
      simp only at ha1 ha2
      omega
    rw [Fintype.sum_eq_add _ _ (by rw [Ne, Fin.ext_iff]; simp) hz]
    have e1 : finPos (2 * s + 1) (2 * u i) = (⟨2 * u i, by omega⟩ : Fin (2 * s + 1)).castSucc := by
      apply Fin.ext
      simp [finPos] <;> omega
    have e2 : finPos (2 * s + 1) (2 * u i + 1) =
        (⟨2 * u i + 1, by omega⟩ : Fin (2 * s + 1)).castSucc := by
      apply Fin.ext
      simp [finPos] <;> omega
    rw [e1, e2, mul_add]
    congr 1 <;> simp
  have hjp' : ∑ a : Fin (2 * s + 1), (if a = ⟨2 * s, by omega⟩ then jp else 0) * f a.castSucc =
      jp * f (⟨2 * s, by omega⟩ : Fin (2 * s + 1)).castSucc := by
    simp [ite_mul]
  rw [← hfold, ← hjp', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [hsplit a]
  ring

/- English proof (translation)
Introduce `X _ O _ _ _ _ _ j b _ mm u hu μ hμ ω ωL hbal`. Take `⟨h1, h2, h3⟩` from `hbal`. Use `set W := OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω ωL with hW`. Establish `hgen : ∀ (jj : Fin (bD C0 CE1 CE2 X j mm b).T.t → ℕ) (jp : ℕ), (bD C0 CE1 CE2 X j mm b).LevelOK jj jp → ∀ z ∈ BlockData.gens O (bD C0 CE1 CE2 X j mm b) jj jp, IsWeightedHomogeneous ω z W`. Introduce `jj jp hok z hz`.

Take `⟨y, hy, g, hg, rfl⟩` from `hz`. Establish `hE : ∀ i : Fin (X.seg C0 CE1 CE2 j).t, IsWeightedHomogeneous ω (BlockData.Ehat (r` using `X.m) O (bD C0 CE1 CE2 X j mm b) i) (ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i))) + ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1))) := by`. Introduce `i`. Use `IsWeightedHomogeneous.add ?_ ?_` and prove the remaining obligations. Rewrite using `[← h2 i]`.

Conclude with `(isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)`. Use `IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_` and prove the remaining obligations. Establish `hX` using `(isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i)), c))).mul (isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1), c)))`. Rewrite `hX` using `[h1, h1]`. Conclude with `hX`.

Establish `hEp : IsWeightedHomogeneous ω (BlockData.Eplus (r` using `X.m) O (bD C0 CE1 CE2 X j mm b)) (ωL (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).castSucc + ωL (Fin.last (2 * segS X.TT j + 1))) := by`. Use `IsWeightedHomogeneous.add ?_ ?_` and prove the remaining obligations. Rewrite using `[← h3]`. Conclude with `(isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)`. Use `IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_` and prove the remaining obligations.

Establish `hX` using `(isWeightedHomogeneous_X (KK O) ω (Sum.inl ((⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).castSucc, c))).mul (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)))`. Rewrite `hX` using `[h1, h1]`. Conclude with `hX`. Establish `hyP : y ∈ Pol (KK O) X.m ((bD C0 CE1 CE2 X j mm b).lettersAt jj jp).deg` using `(Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1`. Establish `hY` using `isWeightedHomogeneous_rename_chainEmb_of_mem_Pol ω ωL h1 _ y hyP`.

Establish `hG` using `isWeightedHomogeneous_of_mem_restrictSupport_xiVar ω ωL h1 _ g (Submodule.mem_inf.1 hg).1`. Establish `hP1` using `IsWeightedHomogeneous.prod Finset.univ (fun i => BlockData.Ehat (r := X.m) O (bD C0 CE1 CE2 X j mm b) i ^ jj i) _ fun i _ => (hE i).pow (jj i)`. Establish `hP3` using `IsWeightedHomogeneous.prod Finset.univ (fun i : Fin (X.seg C0 CE1 CE2 j).t => (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t i.castSucc) : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) ^ (bD C0 CE1 CE2 X j mm b).T.z i) _ fun i _ => (isWeightedHomogeneous_X (KK …`. Establish `hP4` using `(isWeightedHomogeneous_X (KK O) ω (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _))).pow (bD C0 CE1 CE2 X j mm b).zPlus`. Establish `key` using `((((hP1.mul (hEp.pow jp)).mul hP3).mul hP4).mul hY).mul hG`.

Introduce `d hd`. Use `(key hd).trans ?_` and prove the remaining obligations. Establish `hinj : Function.Injective (uTop (X.seg C0 CE1 CE2 j))`. Introduce `l1 l2 h`. Apply `Fin.ext` to reduce the goal to its premises.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [uTop] at this`. Use linear arithmetic over natural numbers and integers. Establish `hj : ∀ i (a : Fin (2 * segS X.TT j + 1)), ((a : ℕ) = 2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) ∨ (a : ℕ) = 2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1) → jj i ≤ (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a`. Introduce `i a ha`.

Establish `hlt` using `a.isLt`. Take `⟨k1, k2⟩` from `hok.1 i`. Break down `ha with ha | ha` into its components or cases. Establish `e : (bD C0 CE1 CE2 X j mm b).letterAt ((bD C0 CE1 CE2 X j mm b).T.pos i) = a` using `Fin.ext (show min (2 * (uTop (X.seg C0 CE1 CE2 j) i : ℕ)) (2 * segS X.TT j + 1 - 1) = (a : ℕ) by omega)`. Rewrite `k1` using `[e]`.

Conclude with `k1`. Establish `e : (bD C0 CE1 CE2 X j mm b).letterAt ((bD C0 CE1 CE2 X j mm b).T.pos i + 1) = a` using `Fin.ext (show min (2 * (uTop (X.seg C0 CE1 CE2 j) i : ℕ) + 1) (2 * segS X.TT j + 1 - 1) = (a : ℕ) by omega)`. Rewrite `k2` using `[e]`. Conclude with `k2`. Establish `hjp : ∀ a : Fin (2 * segS X.TT j + 1), (a : ℕ) = 2 * segS X.TT j → jp ≤ (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a`.

Introduce `a ha`. Establish `e : a = (bD C0 CE1 CE2 X j mm b).uPos` using `Fin.ext ha`. Rewrite using `[e]`. Conclude with `(le_min_iff.1 hok.2).1`. Establish `hR` using `sum_deg_sub_mul_add_eq_sum_deg_mul (uTop (X.seg C0 CE1 CE2 j)) hinj (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg jj jp ωL hj hjp`.

Establish `hR' : ∑ i : Fin (bD C0 CE1 CE2 X j mm b).T.t, jj i * (ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i))) + ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1))) + jp * ωL (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).castSucc …` using `hR`. Take `⟨k, hk⟩ : ∃ k, (X.seg C0 CE1 CE2 j).bPlus = jp + k` from `⟨_, (Nat.add_sub_of_le (le_min_iff.1 hok.2).2).symm⟩`. Establish `hk' : (bD C0 CE1 CE2 X j mm b).B - jp = k` using `by show (X.seg C0 CE1 CE2 j).bPlus - jp = k`. Use linear arithmetic over natural numbers and integers. Establish `hZ : ∑ i : Fin (X.seg C0 CE1 CE2 j).t, (bD C0 CE1 CE2 X j mm b).T.z i * ω (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t i.castSucc) = ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) …` using `rfl`.

Establish `hzP : (bD C0 CE1 CE2 X j mm b).zPlus * ω (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last (X.seg C0 CE1 CE2 j).t)) = (segAPlus X.TT X.aT j - b.oPlus) * ω (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false))` using `rfl`. Simplify using `only [smul_eq_mul]`. Rewrite using `[hk', hW, hZ, hzP]`. Unfold `OmB`. Rewrite using `[← hR', hk]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hS : sszB O C0 CE1 CE2 X j mm b ≤ (weightedHomogeneousSubmodule (KK O) ω W).restrictScalars O`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Set.mem_iUnion] at hz`.

Take `⟨jj, jp, hok, hz⟩` from `hz`. Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).2 (hgen jj jp hok z hz)`. Establish `hu' : u ∈ weightedHomogeneousSubmodule (KK O) ω W`. Use `Submodule.span_le.2 ?_ hu` and prove the remaining obligations. Introduce `z hz`.

Conclude with `hS hz`. Establish `hc` using `((mem_weightedHomogeneousSubmodule _ _ _ _).1 hu') (mem_support_iff.1 hμ)`. Rewrite `hc` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω i) (fun _ => zero_smul _ _)]`. Simplify `hc` using `[smul_eq_mul]`.
-/
theorem homAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : HomAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ O _ _ _ _ _ j b _ mm u hu μ hμ ω ωL hbal
  obtain ⟨h1, h2, h3⟩ := hbal
  set W := OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω ωL with hW
  have hgen : ∀ (jj : Fin (bD C0 CE1 CE2 X j mm b).T.t → ℕ) (jp : ℕ),
      (bD C0 CE1 CE2 X j mm b).LevelOK jj jp →
      ∀ z ∈ BlockData.gens O (bD C0 CE1 CE2 X j mm b) jj jp, IsWeightedHomogeneous ω z W := by
    intro jj jp hok z hz
    obtain ⟨y, hy, g, hg, rfl⟩ := hz
    have hE : ∀ i : Fin (X.seg C0 CE1 CE2 j).t,
        IsWeightedHomogeneous ω (BlockData.Ehat (r := X.m) O (bD C0 CE1 CE2 X j mm b) i)
          (ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i))) +
            ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1))) := by
      intro i
      refine IsWeightedHomogeneous.add ?_ ?_
      · rw [← h2 i]
        exact (isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)
      · refine IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_
        have hX := (isWeightedHomogeneous_X (KK O) ω
          (Sum.inl (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i)), c))).mul
          (isWeightedHomogeneous_X (KK O) ω
          (Sum.inl (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1), c)))
        rw [h1, h1] at hX
        exact hX
    have hEp : IsWeightedHomogeneous ω (BlockData.Eplus (r := X.m) O (bD C0 CE1 CE2 X j mm b))
        (ωL (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).castSucc +
          ωL (Fin.last (2 * segS X.TT j + 1))) := by
      refine IsWeightedHomogeneous.add ?_ ?_
      · rw [← h3]
        exact (isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)
      · refine IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_
        have hX := (isWeightedHomogeneous_X (KK O) ω
          (Sum.inl ((⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).castSucc, c))).mul
          (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)))
        rw [h1, h1] at hX
        exact hX
    have hyP : y ∈ Pol (KK O) X.m ((bD C0 CE1 CE2 X j mm b).lettersAt jj jp).deg :=
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1
    have hY := isWeightedHomogeneous_rename_chainEmb_of_mem_Pol ω ωL h1 _ y hyP
    have hG := isWeightedHomogeneous_of_mem_restrictSupport_xiVar ω ωL h1 _ g (Submodule.mem_inf.1 hg).1
    have hP1 := IsWeightedHomogeneous.prod Finset.univ
      (fun i => BlockData.Ehat (r := X.m) O (bD C0 CE1 CE2 X j mm b) i ^ jj i) _ fun i _ => (hE i).pow (jj i)
    have hP3 := IsWeightedHomogeneous.prod Finset.univ
      (fun i : Fin (X.seg C0 CE1 CE2 j).t => (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t i.castSucc) :
        MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) ^ (bD C0 CE1 CE2 X j mm b).T.z i) _
      fun i _ => (isWeightedHomogeneous_X (KK O) ω _).pow _
    have hP4 := (isWeightedHomogeneous_X (KK O) ω
      (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _))).pow (bD C0 CE1 CE2 X j mm b).zPlus
    have key := ((((hP1.mul (hEp.pow jp)).mul hP3).mul hP4).mul hY).mul hG
    intro d hd
    refine (key hd).trans ?_
    have hinj : Function.Injective (uTop (X.seg C0 CE1 CE2 j)) := by
      intro l1 l2 h
      apply Fin.ext
      have := congrArg Fin.val h
      simp only [uTop] at this
      omega
    have hj : ∀ i (a : Fin (2 * segS X.TT j + 1)),
        ((a : ℕ) = 2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) ∨ (a : ℕ) = 2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1) →
        jj i ≤ (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a := by
      intro i a ha
      have hlt := a.isLt
      obtain ⟨k1, k2⟩ := hok.1 i
      rcases ha with ha | ha
      · have e : (bD C0 CE1 CE2 X j mm b).letterAt ((bD C0 CE1 CE2 X j mm b).T.pos i) = a :=
          Fin.ext (show min (2 * (uTop (X.seg C0 CE1 CE2 j) i : ℕ)) (2 * segS X.TT j + 1 - 1) = (a : ℕ) by omega)
        rw [e] at k1
        exact k1
      · have e : (bD C0 CE1 CE2 X j mm b).letterAt ((bD C0 CE1 CE2 X j mm b).T.pos i + 1) = a :=
          Fin.ext (show min (2 * (uTop (X.seg C0 CE1 CE2 j) i : ℕ) + 1) (2 * segS X.TT j + 1 - 1) = (a : ℕ) by
            omega)
        rw [e] at k2
        exact k2
    have hjp : ∀ a : Fin (2 * segS X.TT j + 1), (a : ℕ) = 2 * segS X.TT j →
        jp ≤ (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a := by
      intro a ha
      have e : a = (bD C0 CE1 CE2 X j mm b).uPos := Fin.ext ha
      rw [e]
      exact (le_min_iff.1 hok.2).1
    have hR := sum_deg_sub_mul_add_eq_sum_deg_mul (uTop (X.seg C0 CE1 CE2 j)) hinj
      (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg jj jp ωL hj hjp
    have hR' : ∑ i : Fin (bD C0 CE1 CE2 X j mm b).T.t,
          jj i * (ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i))) +
            ωL (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) i) + 1))) +
        jp * ωL (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).castSucc +
        ∑ a : Fin (2 * segS X.TT j + 1), ((bD C0 CE1 CE2 X j mm b).lettersAt jj jp).deg a * ωL a.castSucc =
        ∑ a : Fin (2 * segS X.TT j + 1),
          (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a * ωL a.castSucc := hR
    obtain ⟨k, hk⟩ : ∃ k, (X.seg C0 CE1 CE2 j).bPlus = jp + k :=
      ⟨_, (Nat.add_sub_of_le (le_min_iff.1 hok.2).2).symm⟩
    have hk' : (bD C0 CE1 CE2 X j mm b).B - jp = k := by
      show (X.seg C0 CE1 CE2 j).bPlus - jp = k
      omega
    have hZ : ∑ i : Fin (X.seg C0 CE1 CE2 j).t,
        (bD C0 CE1 CE2 X j mm b).T.z i * ω (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t i.castSucc) =
        ∑ l : Fin (X.seg C0 CE1 CE2 j).t,
          (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) *
            ω (Sum.inr (l.castSucc, false)) := rfl
    have hzP : (bD C0 CE1 CE2 X j mm b).zPlus *
        ω (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last (X.seg C0 CE1 CE2 j).t)) =
        (segAPlus X.TT X.aT j - b.oPlus) * ω (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) := rfl
    simp only [smul_eq_mul]
    rw [hk', hW, hZ, hzP]
    unfold OmB
    rw [← hR', hk]
    ring
  have hS : sszB O C0 CE1 CE2 X j mm b ≤
      (weightedHomogeneousSubmodule (KK O) ω W).restrictScalars O := by
    refine Submodule.span_le.2 ?_
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨jj, jp, hok, hz⟩ := hz
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).2 (hgen jj jp hok z hz)
  have hu' : u ∈ weightedHomogeneousSubmodule (KK O) ω W := by
    refine Submodule.span_le.2 ?_ hu
    intro z hz
    exact hS hz
  have hc := ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hu') (mem_support_iff.1 hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω i) (fun _ => zero_smul _ _)] at hc
  simpa [smul_eq_mul] using hc

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `ha : a.val < 2 * segS X.TT j` using `by omega`. Simplify using `only [letterOf, dif_pos ha]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show topOdd X j _ = topOdd X j i`.

Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[h]`. Simplify using `[h]`.
-/
theorem letterOf_eq_odd_letter_true_of_val_eq_two_mul (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1 + 1)) (i : Fin (segS X.TT j))
    (h : a.val = 2 * i.val) : letterOf X j a = (topOdd X j i, true) := by
  have hi := i.isLt
  have ha : a.val < 2 * segS X.TT j := by omega
  simp only [letterOf, dif_pos ha]
  refine Prod.ext ?_ ?_
  · show topOdd X j _ = topOdd X j i
    congr 1
    apply Fin.ext
    simp [h]
  · simp [h]

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `ha : a.val < 2 * segS X.TT j` using `by omega`. Simplify using `only [letterOf, dif_pos ha]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show topOdd X j _ = topOdd X j i`.

Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [h]`. Use linear arithmetic over natural numbers and integers. Simplify using `[h, Nat.add_mod]`.
-/
theorem letterOf_E (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1 + 1)) (i : Fin (segS X.TT j))
    (h : a.val = 2 * i.val + 1) : letterOf X j a = (topOdd X j i, false) := by
  have hi := i.isLt
  have ha : a.val < 2 * segS X.TT j := by omega
  simp only [letterOf, dif_pos ha]
  refine Prod.ext ?_ ?_
  · show topOdd X j _ = topOdd X j i
    congr 1
    apply Fin.ext
    simp only [h]
    omega
  · simp [h, Nat.add_mod]

/- English proof (translation)
Simplify using `only [symVar, letterOf]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem symVar_inl_fst (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1 + 1))
    (c : Fin X.m) : (symVar C0 CE1 CE2 X j (Sum.inl (a, c))).1 = letterOf X j a := by
  simp only [symVar, letterOf]
  split_ifs <;> rfl

/- English proof (translation)
Use `⟨fun a c => ?_, fun l => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [lamW, lamL, symVar_inl_fst]`. Establish `hu` using `(uTop (X.seg C0 CE1 CE2 j) l).isLt`. Establish `e1 : letterOf X j (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) l))) = (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true)` using `letterOf_eq_odd_letter_true_of_val_eq_two_mul X j _ _ (by simp only [finPos]; omega)`. Establish `e2 : letterOf X j (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) l) + 1)) = (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false)` using `letterOf_E X j _ _ (by simp only [finPos]; omega)`.

Establish `s1 : ∀ β : Bool, (symVar C0 CE1 CE2 X j (Sum.inr (l.castSucc, β))).1 = (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β)`. Introduce `β`. Simplify using `[symVar]`. Simplify using `only [lamW, lamL, e1, e2, s1, Bool.not_false, Bool.not_true]`. Simplify using `[lamW, lamL, letterOf, symVar]`.
-/
theorem lam_balanced (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) :
    Balanced X.m (X.seg C0 CE1 CE2 j) (lamW C0 CE1 CE2 X j x) (lamL X j x) := by
  refine ⟨fun a c => ?_, fun l => ?_, ?_⟩
  · simp only [lamW, lamL, symVar_inl_fst]
  · have hu := (uTop (X.seg C0 CE1 CE2 j) l).isLt
    have e1 : letterOf X j (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) l))) =
        (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true) :=
      letterOf_eq_odd_letter_true_of_val_eq_two_mul X j _ _ (by simp only [finPos]; omega)
    have e2 : letterOf X j (finPos (2 * segS X.TT j + 1) (2 * ↑(uTop (X.seg C0 CE1 CE2 j) l) + 1)) =
        (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false) :=
      letterOf_E X j _ _ (by simp only [finPos]; omega)
    have s1 : ∀ β : Bool, (symVar C0 CE1 CE2 X j (Sum.inr (l.castSucc, β))).1 =
        (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β) := by
      intro β
      simp [symVar]
    simp only [lamW, lamL, e1, e2, s1, Bool.not_false, Bool.not_true]
  · simp [lamW, lamL, letterOf, symVar]

/- English proof (translation)
Rewrite using `[Finset.sum_filter]`. Unfold `cdeg`. Rewrite using `[← hμ _ _ (lam_balanced C0 CE1 CE2 X j x)]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Unfold `lamW`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sum_fiber (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) (hμ : HomExp C0 CE1 CE2 X j b μ) (x : X.TT × Bool) :
    open Classical in
    ∑ v ∈ Finset.univ.filter (fun v => (symVar C0 CE1 CE2 X j v).1 = x), μ v = cdeg C0 CE1 CE2 X j b x := by
  classical
  rw [Finset.sum_filter]
  unfold cdeg
  rw [← hμ _ _ (lam_balanced C0 CE1 CE2 X j x)]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold lamW
  split_ifs <;> simp

/- English proof (translation)
Introduce `C0 CE1 CE2 X j b _ μ hμ`. Rewrite using `[Nblk]`. Use `Nat.mul_dvd_mul_right ?_ _` and prove the remaining obligations. Establish `hf : ∀ x, ∏ v ∈ Finset.univ.filter (fun v => (symVar C0 CE1 CE2 X j v).1 = x), (μ v).factorial ∣ (cdeg C0 CE1 CE2 X j b x).factorial`. Introduce `x`.

Rewrite using `[← sum_fiber C0 CE1 CE2 X j b μ hμ x]`. Use `Nat.prod_factorial_dvd_factorial_sum _ _` and compare the differences between its conclusion and the goal. Establish `he : expFact μ = ∏ x : X.TT × Bool, ∏ v ∈ Finset.univ.filter (fun v => (symVar C0 CE1 CE2 X j v).1 = x), (μ v).factorial`. Rewrite using `[expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]`. Conclude with `(Finset.prod_fiberwise Finset.univ (fun v => (symVar C0 CE1 CE2 X j v).1) _).symm`.

Rewrite using `[he]`. Conclude with `Finset.prod_dvd_prod_of_dvd _ _ fun x _ => hf x`.
-/
theorem dvdAt : DvdAt := by
  intro C0 CE1 CE2 X j b _ μ hμ
  classical
  rw [Nblk]
  refine Nat.mul_dvd_mul_right ?_ _
  have hf : ∀ x, ∏ v ∈ Finset.univ.filter (fun v => (symVar C0 CE1 CE2 X j v).1 = x), (μ v).factorial ∣
      (cdeg C0 CE1 CE2 X j b x).factorial := by
    intro x
    rw [← sum_fiber C0 CE1 CE2 X j b μ hμ x]
    convert Nat.prod_factorial_dvd_factorial_sum _ _
  have he : expFact μ = ∏ x : X.TT × Bool,
      ∏ v ∈ Finset.univ.filter (fun v => (symVar C0 CE1 CE2 X j v).1 = x), (μ v).factorial := by
    rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
    exact (Finset.prod_fiberwise Finset.univ (fun v => (symVar C0 CE1 CE2 X j v).1) _).symm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun x _ => hf x

end Formalism.MainNotions.ColumnSystems.Pf
