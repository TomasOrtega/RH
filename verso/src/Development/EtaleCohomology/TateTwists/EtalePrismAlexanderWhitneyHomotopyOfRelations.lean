import Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

def leaf_acyc : Prop := ∀ (N k : ℕ) (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 →
  ∃ b : Pr N →₀ ℤ, Pr.Deg (k + 2) b ∧ Pr.d N b = c

def leaf_dbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)

def leaf_bdbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0

def leaf_aw : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N)

def leaf_wa : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N)

/- English proof (translation)
Introduce `z hz`. Simplify using `at hz`.
-/
lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

/- English proof (translation)
Introduce `z hz`. Break down `Finset.mem_union.1 (Finsupp.support_sub hz) with h | h` into its components or cases. Conclude with `ha z h`. Conclude with `hb z h`.
-/
lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

/- English proof (translation)
Introduce `z hz`. Unfold `Pr.bd at hz`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)`. Establish `h2` using `Finsupp.support_smul hi`. Unfold `Pr.push at h2`.

Simplify using `only [Finsupp.lmapDomain_apply] at h2`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support h2)`. Conclude with `hc w hw`.
-/
lemma deg_bd {N k : ℕ} {c : Pr N →₀ ℤ} (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  intro z hz
  unfold Pr.bd at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have h2 := Finsupp.support_smul hi
  unfold Pr.push at h2
  simp only [Finsupp.lmapDomain_apply] at h2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h2)
  exact hc w hw

/- English proof (translation)
Introduce `z hz`. Unfold `Pr.aw at hz`. Take `⟨p, -, hp⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)`. Use `Finsupp.support_single_subset hp` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`.

Substitute `this` using the available equality. Use `p.isLt` as an intermediate fact. Use `show (p : ℕ) + (N - p) = N`. Use linear arithmetic over natural numbers and integers.
-/
lemma deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  intro z hz
  unfold Pr.aw at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (p : ℕ) + (N - p) = N
  omega

/- English proof (translation)
Introduce `z hz`. Unfold `Pr.wa at hz`. Take `⟨p, -, hp⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)`. Use `Finsupp.support_single_subset hp` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`.

Substitute `this` using the available equality. Use `p.isLt` as an intermediate fact. Use `show (N - p) + (p : ℕ) = N`. Use linear arithmetic over natural numbers and integers.
-/
lemma deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  intro z hz
  unfold Pr.wa at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (N - p) + (p : ℕ) = N
  omega

/- English proof (translation)
Unfold `Pr.bd`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, smul_sub]`.
-/
lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  unfold Pr.bd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, smul_sub]

/- English proof (translation)
Simplify using `using bd_sub (0 : Pr N →₀ ℤ) 0`.
-/
lemma bd_zero {N : ℕ} : Pr.bd (0 : Pr N →₀ ℤ) = 0 := by
  simpa using bd_sub (0 : Pr N →₀ ℤ) 0

/- English proof (translation)
Simplify using `[Pr.aw, Pr.wa]`.
-/
lemma aw_zero_eq : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

def Good (N : ℕ) (x : Pr N →₀ ℤ) : Prop :=
  Pr.Deg (N + 1) x ∧ Pr.bd (Pr.aw N - Pr.wa N - Pr.d N x) = 0

/- English proof (translation)
Use `set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef`. Establish `hcdeg : Pr.Deg (N + 1) c` using `deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)`. Establish `hcyc : Pr.d (N + 1) c = 0`. Rewrite using `[hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]`. Conclude with `hx.2`.

Take `⟨b, hbdeg, hb⟩` from `hA (N + 1) N c hcdeg hcyc`. Use `⟨b, ⟨hbdeg, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x`. Rewrite using `[hb, hcdef]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `hB N x`. Rewrite using `[hb, hcdef]`. Normalize the expressions using the abelian group laws.
-/
lemma step (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd) (hAW : leaf_aw) (hWA : leaf_wa)
    (N : ℕ) (x : Pr N →₀ ℤ) (hx : Good N x) :
    ∃ y : Pr (N + 1) →₀ ℤ, Good (N + 1) y ∧ Pr.d (N + 1) y + Pr.bd x = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef
  have hcdeg : Pr.Deg (N + 1) c := deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)
  have hcyc : Pr.d (N + 1) c = 0 := by
    rw [hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]
    exact hx.2
  obtain ⟨b, hbdeg, hb⟩ := hA (N + 1) N c hcdeg hcyc
  refine ⟨b, ⟨hbdeg, ?_⟩, ?_⟩
  · have : Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x := by
      rw [hb, hcdef]; abel
    rw [this]; exact hB N x
  · rw [hb, hcdef]; abel

/- English proof (translation)
Use `⟨deg_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]`.
-/
lemma good_zero : Good 0 0 := by
  refine ⟨deg_zero, ?_⟩
  rw [aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]

end LateralTheory.EtaleFoundations.SteenPf

open LateralTheory.EtaleFoundations.SteenPf in
/- English proof (translation)
Set `seq : ∀ N, {x : Pr N →₀ ℤ // Good N x}` to `fun N => Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩ (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2), (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N`. Use `⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩` and prove the remaining obligations. Use `show Pr.d 0 0 = _`. Rewrite using `[map_zero, aw_zero_eq, sub_self]`. Conclude with `(Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2`.
-/
theorem LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd)
    (hAW : leaf_aw) (hWA : leaf_wa) : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  classical
  let seq : ∀ N, {x : Pr N →₀ ℤ // Good N x} := fun N =>
    Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩
      (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2),
        (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N
  refine ⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩
  · show Pr.d 0 0 = _
    rw [map_zero, aw_zero_eq, sub_self]
  · exact (Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2
