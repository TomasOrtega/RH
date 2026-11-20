import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Cont

variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

/- English proof (translation)
Introduce `_` and use `IsLocallyConstant.const _`.
-/
private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

/- English proof (translation)
Introduce `N` and use `by simpa only [map_add] using (hf N).comp₂ (hg N) (· + ·)`.
-/
private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a + g a := fun N => by
  simpa only [map_add] using (hf N).comp₂ (hg N) (· + ·)

/- English proof (translation)
Introduce `N` and use `by simpa only [map_mul] using (hf N).comp₂ (hg N) (· * ·)`.
-/
private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a * g a := fun N => by
  simpa only [map_mul] using (hf N).comp₂ (hg N) (· * ·)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ac_const (0 : R)`. Consider the case `insert i s hi ih => simpa only [Finset.sum_insert hi] using ac_add (hf i) ih`.
-/
private theorem ac_sum {ι : Type} (s : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (0 : R)
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using ac_add (hf i) ih

/- English proof (translation)
Introduce `N` and use `by have hle : Ideal.span {t} ^ N ≤ (Ideal.span {φ t} ^ N).comap φ := by rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow] exact Ideal.mem_span_singleton_self _ exact (hf N).comp (Ideal.quotientMap _ φ hle)`.
-/
private theorem ac_map {S : Type} [CommRing S] (φ : R →+* S) {t : R} {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    AdicCont (Ideal.span {φ t}) fun a => φ (f a) := fun N => by
  have hle : Ideal.span {t} ^ N ≤ (Ideal.span {φ t} ^ N).comap φ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

/- English proof (translation)
Take `⟨N, hN⟩` from `ht`. Use `IsLocallyConstant.desc _ (Ideal.Quotient.mk (Ideal.span {t} ^ N)) (hf N) ?_` and prove the remaining obligations. Rewrite using `[RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN]`. Simplify using the standard rewrite rules.
-/
private theorem ac_nil {t : R} (ht : IsNilpotent t) {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  refine IsLocallyConstant.desc _ (Ideal.Quotient.mk (Ideal.span {t} ^ N)) (hf N) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN]
  simp

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `a`. Establish `: ∀ᶠ b in nhds a, ∀ i j, f b i j = f a i j` using `eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq a`. Conclude with `this.mono fun b hb => Matrix.ext hb`.
-/
private theorem lc_mat {n : ℕ} {f : Γ → Matrix (Fin n) (Fin n) R} (hf : ∀ i j, IsLocallyConstant fun a => f a i j) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have : ∀ᶠ b in nhds a, ∀ i j, f b i j = f a i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq a
  exact this.mono fun b hb => Matrix.ext hb

end Cont

/- English proof (translation)
Establish `e : ∀ c : A, algebraMap A (DD X g) c = DD.C (algebraMap A X c)` using `fun _ => rfl`. Establish `s : ∀ (s : Finset (Fin g)), (∑ j ∈ s, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b)) = ⟨0, fun i => if i ∈ s then algebraMap A X (Z i a b) else 0, 0, 0⟩`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => ext <;> simp`.

Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, ih, e]`. Use extensionality with `j`. Simplify using the standard rewrite rules. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `[hi]`. Simplify using `[h]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[s]`. Simplify using `[DD.epM]`.
-/
private theorem epM_entry {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (Z : Fin g → Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (DD.epM fun j => (Z j).map (algebraMap A X)) a b =
      ∑ j, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b) := by
  have e : ∀ c : A, algebraMap A (DD X g) c = DD.C (algebraMap A X c) := fun _ => rfl
  have s : ∀ (s : Finset (Fin g)), (∑ j ∈ s, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b)) =
      ⟨0, fun i => if i ∈ s then algebraMap A X (Z i a b) else 0, 0, 0⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext <;> simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, ih, e]
      ext j
      · simp
      · by_cases h : j = i
        · subst h; simp [hi]
        · simp [h]
      · simp
      · simp
  rw [s]
  simp [DD.epM]

/- English proof (translation)
Establish `h` using `x.cont i j`. Rewrite `h` using `[PowerSeries.maximalIdeal_eq_span_X]`. Conclude with `ac_map (algebraMap x.A X) h`.
-/
private theorem ρX_cont {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (i j : Fin n) : AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j := by
  have h := x.cont i j
  rw [PowerSeries.maximalIdeal_eq_span_X] at h
  exact ac_map (algebraMap x.A X) h

/- English proof (translation)
Introduce `l _ F n x k X _ _`. Take `⟨h1, h2, -, h4⟩` from `Det.rho1Hom k X`. Establish `c1 : ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j`. Introduce `i j`. Simplify using `only [Kap.ρ1, Matrix.mul_apply, Matrix.add_apply, epM_entry]`.

Use `ac_sum _ fun c => ac_mul (ac_add (ac_const _) (ac_sum _ fun a => ac_mul (ac_const _) ?_)) (ρX_cont x _ c j)` and prove the remaining obligations. Conclude with `ac_map (algebraMap x.A (DD X k.g)) ((k.mem a).2.1 i c)`. Use `⟨⟨by simp [NP.ρX, mat], fun g h => by simp [NP.ρX, mat, Matrix.map_mul], ρX_cont x X⟩, ⟨h1, h2, c1⟩, fun ht => ⟨lc_mat fun i j => ac_nil ht (ρX_cont x X i j), lc_mat fun i j => ac_nil ?_ (c1 i j)⟩, fun v => ⟨(h4 v).1, ?_⟩⟩` and prove the remaining obligations. Conclude with `ht.map (DD.C : X →+* DD X k.g)`. Rewrite using `[NP.wX, NP.wiX, ← Matrix.map_mul]`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Pa.rho_hom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], (x.ρX X 1 = 1 ∧ (∀ g h, x.ρX X (g * h) = x.ρX X g * x.ρX X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j) ∧ (k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j) ∧ (IsNilpotent (algebraMap x.A X x.t) → IsLocallyConstant (x.ρX X) ∧ IsLocallyConstant (k.ρ1 X)) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ x.wX X v * x.wiX X v = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, h2, -, h4⟩ := Det.rho1Hom k X
  have c1 : ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j := by
    intro i j
    simp only [Kap.ρ1, Matrix.mul_apply, Matrix.add_apply, epM_entry]
    refine ac_sum _ fun c => ac_mul (ac_add (ac_const _) (ac_sum _ fun a => ac_mul (ac_const _) ?_)) (ρX_cont x _ c j)
    exact ac_map (algebraMap x.A (DD X k.g)) ((k.mem a).2.1 i c)
  refine ⟨⟨by simp [NP.ρX, mat], fun g h => by simp [NP.ρX, mat, Matrix.map_mul], ρX_cont x X⟩, ⟨h1, h2, c1⟩,
    fun ht => ⟨lc_mat fun i j => ac_nil ht (ρX_cont x X i j), lc_mat fun i j => ac_nil ?_ (c1 i j)⟩,
    fun v => ⟨(h4 v).1, ?_⟩⟩
  · exact ht.map (DD.C : X →+* DD X k.g)
  · rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp
