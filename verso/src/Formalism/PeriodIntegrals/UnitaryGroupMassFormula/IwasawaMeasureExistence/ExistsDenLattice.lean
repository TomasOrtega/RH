import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdeleRing

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

abbrev inclV (w : Fin n → E) : Fin n → E ⊗[F] Af := fun i => Formalism.UG.inclE (F := F) Af (w i)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩`.
-/
theorem inclV_mem {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E} (hw : w ∈ L) :
    inclV (F := F) w ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)`.
-/
theorem one_tmul_mem_intAf {c : Af} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

/- English proof (translation)
Establish `hw : w ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL]; trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simpa using L.zero_mem⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨m1, h1, hx⟩` from `hx`. Take `⟨m2, h2, hy⟩` from `hy`. Use `⟨m1 * m2, Nat.mul_pos h1 h2, ?_⟩` and prove the remaining obligations. Establish `: (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm m2 m1]`.

Rewrite using `[this]`. Conclude with `L.add_mem (nsmul_mem hx m2) (nsmul_mem hy m1)`. Consider the case `smul e x _ hx`. Take `⟨m, hm, hx⟩` from `hx`. Take `⟨t, ht, a, ha⟩` from `exists_den e`.

Use `⟨t * m, Nat.mul_pos ht hm, ?_⟩` and prove the remaining obligations. Establish `: (t * m) • (e • x) = a • (m • x)`. Rewrite using `[← algebraMap_smul E a (m • x), ← ha, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.smul_mem a hx`.
-/
theorem exists_nat_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simpa using L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, h1, hx⟩ := hx
    obtain ⟨m2, h2, hy⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos h1 h2, ?_⟩
    have : (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m2 m1]
    rw [this]
    exact L.add_mem (nsmul_mem hx m2) (nsmul_mem hy m1)
  | smul e x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨t, ht, a, ha⟩ := exists_den e
    refine ⟨t * m, Nat.mul_pos ht hm, ?_⟩
    have : (t * m) • (e • x) = a • (m • x) := by
      rw [← algebraMap_smul E a (m • x), ← ha, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, smul_smul]
      congr 1
      push_cast; ring
    rw [this]
    exact L.smul_mem a hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))`. Use `⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩` and prove the remaining obligations. Establish `key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F → (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F` using `F) L := by`. Introduce `j k c hc`. Take `⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p` from `Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))`.

Establish `hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L`. Rewrite using `[hq, mul_comm, mul_smul]`. Conclude with `nsmul_mem (hmL (j, k)) q`. Establish `heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) = (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) • inclV (F` using `F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Rewrite using `[← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']`. Simplify using `only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.

Simplify using `[Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]`. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem _ _ (inclV_mem hw)`. Establish `hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af)` using `by conv_lhs => rw [← Finset.univ_sum_single y]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `h1` using `emb_coord b (y j)`. Simplify using `only [emb] at h1`. Use `conv_lhs => rw [← h1]`. Conclude with `map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _`. Rewrite using `[hy', Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Conclude with `Submodule.sum_mem _ fun k _ => key j k _ (hy j k)`.
-/
theorem exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af, (∀ j, IntC b (y j)) → d • y ∈ lamAf (F := F) L := by
  classical
  choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩
  have key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F →
      (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F := F) L := by
    intro j k c hc
    obtain ⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p := Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))
    have hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L := by
      rw [hq, mul_comm, mul_smul]; exact nsmul_mem (hmL (j, k)) q
    have heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) =
        (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) •
          inclV (F := F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']
        simp only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · simp [Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]
    rw [heq]
    exact Submodule.smul_mem _ _ (inclV_mem hw)
  have hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := emb_coord b (y j)
    simp only [emb] at h1
    conv_lhs => rw [← h1]
    exact map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _
  rw [hy', Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => key j k _ (hy j k)

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L`. Take `⟨p, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := L)`. Take `⟨D, hD, h⟩` from `exists_den_fin (fun q : Fin p × Fin n × ι => b.repr ((s q.1 : Fin n → E) q.2.1) q.2.2)`. Use `⟨D, hD, fun l hl j k => ?_⟩` and prove the remaining obligations.

Establish `hmem : (⟨l, hl⟩ : L) ∈ Submodule.span ℤ (Set.range s)` using `by rw [hs]; trivial`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem`. Establish `hl' : l = ∑ t, c t • (s t : Fin n → E)`. Use `congrArg Subtype.val hc` as an intermediate fact. Simplify `this.symm` using `[Submodule.coe_sum]`.

Establish `: (D : F) * b.repr (l j) k = ∑ t, c t • ((D : F) * b.repr ((s t : Fin n → E) j) k)`. Rewrite using `[hl']`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[← b.coord_apply, map_sum]`. Simplify using `only [map_zsmul, b.coord_apply, Finset.mul_sum, mul_smul_comm, Finsupp.smul_apply]`.

Unfold `IntF`. Rewrite using `[this, map_sum]`. Conclude with `ohat_sum _ fun t _ => by rw [map_zsmul]; exact ohat_zsmul (h (t, j, k)) _`.
-/
theorem exists_den_lattice (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
  classical
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨p, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  obtain ⟨D, hD, h⟩ := exists_den_fin (fun q : Fin p × Fin n × ι => b.repr ((s q.1 : Fin n → E) q.2.1) q.2.2)
  refine ⟨D, hD, fun l hl j k => ?_⟩
  have hmem : (⟨l, hl⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hl' : l = ∑ t, c t • (s t : Fin n → E) := by
    have := congrArg Subtype.val hc
    simpa [Submodule.coe_sum] using this.symm
  have : (D : F) * b.repr (l j) k = ∑ t, c t • ((D : F) * b.repr ((s t : Fin n → E) j) k) := by
    rw [hl']
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [← b.coord_apply, map_sum]
    simp only [map_zsmul, b.coord_apply, Finset.mul_sum, mul_smul_comm, Finsupp.smul_apply]
  unfold IntF
  rw [this, map_sum]
  exact ohat_sum _ fun t _ => by rw [map_zsmul]; exact ohat_zsmul (h (t, j, k)) _

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) Af (l i)}

/- English proof (translation)
Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem x hx`. Introduce `y hy`. Break down `hx with ⟨⟨o, ho⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩` into its components or cases. Take `⟨o', rfl⟩` from `ho`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, l, hl, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨c, hc, o' • l, L.smul_mem o' hl, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← algebraMap_smul E o' (l i)]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `add_mem hy hz`.

Consider the case `neg y _ hy => rw [smul_neg]`. Conclude with `neg_mem hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, l, hl, rfl⟩` from `hy`.

Use `AddSubgroup.subset_closure ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [smul_add]`.

Conclude with `add_mem hy hz`. Consider the case `neg y _ hy => rw [smul_neg]`. Conclude with `neg_mem hy`. Consider the case `zero => intro y _`. Rewrite using `[zero_smul]`.

Conclude with `zero_mem _`. Consider the case `one => intro y hy`. Rewrite using `[one_smul]` and apply the resulting hypothesis. Consider the case `add x x' _ _ hx hx' => intro y hy`. Rewrite using `[add_smul]`.

Conclude with `add_mem (hx y hy) (hx' y hy)`. Consider the case `neg x _ hx => intro y hy`. Rewrite using `[neg_smul]`. Conclude with `neg_mem (hx y hy)`. Consider the case `mul x x' _ _ hx hx' => intro y hy`.

Rewrite using `[mul_smul]`. Conclude with `hx _ (hx' y hy)`.
-/
theorem smul_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    intro y hy
    rcases hx with ⟨⟨o, ho⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩
    · obtain ⟨o', rfl⟩ := ho
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨c, hc, o' • l, L.smul_mem o' hl, ?_⟩
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← algebraMap_smul E o' (l i)]
      | zero => rw [smul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
      | neg y _ hy => rw [smul_neg]; exact neg_mem hy
    · induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
      | neg y _ hy => rw [smul_neg]; exact neg_mem hy
  | zero => intro y _; rw [zero_smul]; exact zero_mem _
  | one => intro y hy; rwa [one_smul]
  | add x x' _ _ hx hx' => intro y hy; rw [add_smul]; exact add_mem (hx y hy) (hx' y hy)
  | neg x _ hx => intro y hy; rw [neg_smul]; exact neg_mem (hx y hy)
  | mul x x' _ _ hx hx' => intro y hy; rw [mul_smul]; exact hx _ (hx' y hy)

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨l, hl⟩, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨1, ohat_one, l, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.TensorProduct.one_def, one_smul]`.

Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul a x _ hx => rw [Subring.smul_def]`. Conclude with `smul_ohatL L a.2 x hx`.
-/
theorem lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨1, ohat_one, l, hl, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => rw [Subring.smul_def]; exact smul_ohatL L a.2 x hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `k` and use `by rw [map_zero]; exact ohat_zero`.
-/
theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af) := fun k => by
  rw [map_zero]; exact ohat_zero

/- English proof (translation)
Introduce `k` and use `by rw [map_neg]; exact ohat_neg (hx k)`.
-/
theorem intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af} (hx : IntC b x) : IntC b (-x) := fun k => by
  rw [map_neg]; exact ohat_neg (hx k)

/- English proof (translation)
Take `⟨D, hD, h⟩` from `exists_den_lattice b L hfg`. Use `⟨D, hD, fun y hy => ?_⟩` and prove the remaining obligations. Set `G : AddSubgroup (Fin n → E ⊗[F] Af)` to `{ carrier := {y | ∀ j, IntC b (D • y j)} add_mem' := fun {y z} hy hz j => by`. Simplify using `only [Set.mem_ofPred_eq, Pi.add_apply, smul_add] at *`. Conclude with `intC_add (hy j) (hz j)`.

Use the proof step `zero_mem' := fun j => by simpa using intC_zero`. Use the proof step `neg_mem' := fun {y} hy j => by`. Simplify using `only [Set.mem_ofPred_eq, Pi.neg_apply, smul_neg] at *`. Conclude with `intC_neg (hy j) }`. Establish `hle : ohatL (F` using `F) L ≤ G := by`.

Unfold `ohatL`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `y ⟨c, hc, l, hl, rfl⟩ j k`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[map_nsmul, coord_tmul_one_mul]`.

Simplify using `only [Formalism.UG.inclE]`. Rewrite using `[coord_incl]`. Simplify using `only [Pi.smul_apply]`. Establish `: D • (c * algebraMap F Af (b.repr (l j) k)) = c * algebraMap F Af ((D : F) * b.repr (l j) k)`. Rewrite using `[nsmul_eq_mul, map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `ohat_mul hc (h l hl j k)`. Conclude with `hle (lamAf_le_ohatL L hy)`.
-/
theorem exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨D, hD, h⟩ := exists_den_lattice b L hfg
  refine ⟨D, hD, fun y hy => ?_⟩
  let G : AddSubgroup (Fin n → E ⊗[F] Af) :=
    { carrier := {y | ∀ j, IntC b (D • y j)}
      add_mem' := fun {y z} hy hz j => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, smul_add] at *
        exact intC_add (hy j) (hz j)
      zero_mem' := fun j => by simpa using intC_zero
      neg_mem' := fun {y} hy j => by
        simp only [Set.mem_ofPred_eq, Pi.neg_apply, smul_neg] at *
        exact intC_neg (hy j) }
  have hle : ohatL (F := F) L ≤ G := by
    unfold ohatL
    rw [AddSubgroup.closure_le]
    rintro y ⟨c, hc, l, hl, rfl⟩ j k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [map_nsmul, coord_tmul_one_mul]
    simp only [Formalism.UG.inclE]
    rw [coord_incl]
    simp only [Pi.smul_apply]
    have : D • (c * algebraMap F Af (b.repr (l j) k)) = c * algebraMap F Af ((D : F) * b.repr (l j) k) := by
      rw [nsmul_eq_mul, map_mul, map_natCast]; ring
    rw [this]
    exact ohat_mul hc (h l hl j k)
  exact hle (lamAf_le_ohatL L hy)

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

/- English proof (translation)
Apply `coord_injective b` to reduce the goal to its premises. Rewrite using `[map_add, coord_emb, coord_emb, coord_emb]`.
-/
theorem emb_add (c c' : ι → B) : emb b (c + c') = emb b c + emb b c' := by
  apply coord_injective b; rw [map_add, coord_emb, coord_emb, coord_emb]

/- English proof (translation)
Apply `coord_injective b` to reduce the goal to its premises. Rewrite using `[map_zero, coord_emb]`.
-/
theorem emb_zero : emb b (0 : ι → B) = 0 := by
  apply coord_injective b; rw [map_zero, coord_emb]

/- English proof (translation)
Apply `coord_injective b` to reduce the goal to its premises. Rewrite using `[map_neg, coord_emb, coord_emb]`.
-/
theorem emb_neg (c : ι → B) : emb b (-c) = -emb b c := by
  apply coord_injective b; rw [map_neg, coord_emb, coord_emb]

/- English proof (translation)
Apply `coord_injective b` to reduce the goal to its premises. Rewrite using `[map_sub, coord_emb, coord_emb, coord_emb]`.
-/
theorem emb_sub (c c' : ι → B) : emb b (c - c') = emb b c - emb b c' := by
  apply coord_injective b; rw [map_sub, coord_emb, coord_emb, coord_emb]

/- English proof (translation)
Apply `coord_injective b` to reduce the goal to its premises. Rewrite using `[map_nsmul, coord_emb, coord_emb]`.
-/
theorem emb_nsmul (N : ℕ) (c : ι → B) : emb b (N • c) = N • emb b c := by
  apply coord_injective b; rw [map_nsmul, coord_emb, coord_emb]

/- English proof (translation)
Establish `: {p | f p = g p} = {p | coord b (f p) = coord b (g p)}`. Use extensionality with `p`. Conclude with `(coord_injective b).eq_iff.symm`. Rewrite using `[this]`. Conclude with `isClosed_eq hf hg`.
-/
theorem isClosed_eqA [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] {X : Type*} [TopologicalSpace X]
    {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = {p | coord b (f p) = coord b (g p)} := by
    ext p; exact (coord_injective b).eq_iff.symm
  rw [this]; exact isClosed_eq hf hg

end General

/- English proof (translation)
The claim follows from `(hx w).mp hw`.
-/
theorem stab_mem {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) {w : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hw : w ∈ I.Lf) : I.fmat x *ᵥ w ∈ I.Lf := (hx w).mp hw

namespace Cpt

variable (I : AutInst)

abbrev ιb : Type := Fin (Module.finrank I.F I.E)

abbrev bs : Module.Basis (ιb I) I.F I.E := Module.finBasis I.F I.E

abbrev Co : Type := Fin I.n → Fin I.n → ιb I → Af I.F

def matOf (P : Co I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun i j => emb (bs I) (P i j)

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx`. Conclude with `hM l hl`. Consider the case `zero => rw [Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]`.

Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem mulVec_mem_Lf (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ l ∈ I.L, M *ᵥ inclV (F := I.F) l ∈ I.Lf) : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx; exact hM l hl
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx

/- English proof (translation)
Set `S : AddSubgroup (Fin I.n → ιb I → Af I.F)` to `{ carrier := {w | (fun j => emb (bs I) (w j)) ∈ I.Lf} add_mem' := fun {w w'} hw hw' => by`. Establish `: (fun j => emb (bs I) ((w + w') j)) = (fun j => emb (bs I) (w j)) + fun j => emb (bs I) (w' j)`. Use function extensionality and compare the values at `j`. Simplify using `[emb_add]`. Use `show (fun j => emb (bs I) ((w + w') j)) ∈ I.Lf`.

Rewrite using `[this]`. Conclude with `I.Lf.add_mem hw hw'`. Use the proof step `zero_mem' := by show (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) ∈ I.Lf`. Establish `: (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) = 0`. Use function extensionality and compare the values at `j`.

Simplify using `[emb_zero]`. Rewrite using `[this]`. Conclude with `I.Lf.zero_mem`. Use the proof step `neg_mem' := fun {w} hw => by`. Establish `: (fun j => emb (bs I) ((-w) j)) = -fun j => emb (bs I) (w j)`.

Use function extensionality and compare the values at `j`. Simplify using `[emb_neg]`. Use `show (fun j => emb (bs I) ((-w) j)) ∈ I.Lf`. Rewrite using `[this]`. Conclude with `I.Lf.neg_mem hw }`.

Establish `hnhds : (S : Set (Fin I.n → ιb I → Af I.F)) ∈ 𝓝 0`. Set `U` to `{w : Fin I.n → ιb I → Af I.F | ∀ j k, algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k ∈ Ohat I.F}`. Establish `hU : IsOpen U`. Establish `: U = ⋂ j, ⋂ k, (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) ⁻¹' Ohat I.F`. Use extensionality with `w`.

Simplify using `[U]`. Rewrite using `[this]`. Use `isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_` and prove the remaining obligations. Establish `hc : Continuous (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k)` using `continuous_const.mul ((continuous_apply k).comp (continuous_apply j))`. Conclude with `hc.isOpen_preimage _ isOpen_Ohat`.

Establish `h0 : (0 : Fin I.n → ιb I → Af I.F) ∈ U` using `fun j k => by simpa using ohat_zero`. Use `Filter.mem_of_superset (hU.mem_nhds h0) fun w hw => ?_` and prove the remaining obligations. Establish `hd0 : (d : I.F) ≠ 0` using `by exact_mod_cast hd.ne'`. Use `hlow (fun j => emb (bs I) (fun k => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k)) (fun j k => by rw [coord_emb]; exact hw j k)` as an intermediate fact. Use `show (fun j => emb (bs I) (w j)) ∈ I.Lf`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, ← emb_nsmul]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hd0, map_one, one_mul]`. Conclude with `AddSubgroup.isClosed_of_isOpen S (S.isOpen_of_mem_nhds hnhds)`.
-/
theorem isClosed_LfC (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsClosed {w : Fin I.n → ιb I → Af I.F | (fun j => emb (bs I) (w j)) ∈ I.Lf} := by
  let S : AddSubgroup (Fin I.n → ιb I → Af I.F) :=
    { carrier := {w | (fun j => emb (bs I) (w j)) ∈ I.Lf}
      add_mem' := fun {w w'} hw hw' => by
        have : (fun j => emb (bs I) ((w + w') j)) = (fun j => emb (bs I) (w j)) + fun j => emb (bs I) (w' j) := by
          funext j; simp [emb_add]
        show (fun j => emb (bs I) ((w + w') j)) ∈ I.Lf
        rw [this]; exact I.Lf.add_mem hw hw'
      zero_mem' := by
        show (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) ∈ I.Lf
        have : (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) = 0 := by
          funext j; simp [emb_zero]
        rw [this]; exact I.Lf.zero_mem
      neg_mem' := fun {w} hw => by
        have : (fun j => emb (bs I) ((-w) j)) = -fun j => emb (bs I) (w j) := by
          funext j; simp [emb_neg]
        show (fun j => emb (bs I) ((-w) j)) ∈ I.Lf
        rw [this]; exact I.Lf.neg_mem hw }
  have hnhds : (S : Set (Fin I.n → ιb I → Af I.F)) ∈ 𝓝 0 := by
    let U := {w : Fin I.n → ιb I → Af I.F | ∀ j k, algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k ∈ Ohat I.F}
    have hU : IsOpen U := by
      have : U = ⋂ j, ⋂ k, (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) ⁻¹' Ohat I.F := by
        ext w; simp [U]
      rw [this]
      refine isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have hc : Continuous (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) :=
        continuous_const.mul ((continuous_apply k).comp (continuous_apply j))
      exact hc.isOpen_preimage _ isOpen_Ohat
    have h0 : (0 : Fin I.n → ιb I → Af I.F) ∈ U := fun j k => by simpa using ohat_zero
    refine Filter.mem_of_superset (hU.mem_nhds h0) fun w hw => ?_
    have hd0 : (d : I.F) ≠ 0 := by exact_mod_cast hd.ne'
    have := hlow (fun j => emb (bs I) (fun k => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k))
      (fun j k => by rw [coord_emb]; exact hw j k)
    show (fun j => emb (bs I) (w j)) ∈ I.Lf
    convert this using 1
    funext j
    rw [Pi.smul_apply, ← emb_nsmul]
    congr 1; funext k
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul,
      mul_inv_cancel₀ hd0, map_one, one_mul]
  exact AddSubgroup.isClosed_of_isOpen S (S.isOpen_of_mem_nhds hnhds)

/- English proof (translation)
Introduce `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `h1`.

Rewrite using `[Pi.single_eq_of_ne hij]`. Conclude with `intC_zero`.
-/
theorem intC_single (D1 : ℕ) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F))) (j : Fin I.n) :
    ∀ i, IntC (bs I) ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) i) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [Pi.single_eq_same]; exact h1
  · rw [Pi.single_eq_of_ne hij]; exact intC_zero

/- English proof (translation)
Establish `hl` using `hlow _ (intC_single I D1 h1 j)`. Establish `hxl` using `stab_mem hx hl`. Use `hup _ hxl i` as an intermediate fact. Establish `e : (I.fmat x *ᵥ (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i = (d * D1) • I.fmat x i j`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply]`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, mul_smul_comm, smul_smul, mul_comm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[e, smul_smul]`. Conclude with `this`.
-/
theorem bound_K (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) (i j : Fin I.n) : IntC (bs I) ((D * (d * D1)) • I.fmat x i j) := by
  have hl := hlow _ (intC_single I D1 h1 j)
  have hxl := stab_mem hx hl
  have := hup _ hxl i
  have e : (I.fmat x *ᵥ (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (d * D1) • I.fmat x i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_smul_comm, smul_smul, mul_comm]
    ring
  rw [e, smul_smul] at this
  exact this

end Cpt

end PI.IwaMeasEx.Wau

end
